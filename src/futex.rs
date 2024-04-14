
#![cfg(any(
    target_os = "linux",
    target_os = "android",
    all(target_os = "emscripten", target_feature = "atomics"),
    target_os = "freebsd",
    target_os = "openbsd",
    target_os = "dragonfly",
    target_os = "fuchsia",
))]

use std::sync::atomic::AtomicU32;
use std::time::Duration;
const NSEC_PER_SEC: u64 = 1_000_000_000;
use libc;

/// Wait for a futex_wake operation to wake us.
///
/// Returns directly if the futex doesn't hold the expected value.
///
/// Returns false on timeout, and true in all other cases.
#[cfg(any(target_os = "linux", target_os = "android", target_os = "freebsd"))]
pub fn futex_wait(futex: *const AtomicU32, expected: u32, timeout: Option<Duration>) -> bool {
    use core::ptr::null;
    use core::sync::atomic::Ordering::Relaxed;

    // Calculate the timeout as an absolute timespec.
    //
    // Overflows are rounded up to an infinite timeout (None).
    let timespec = timeout
        .and_then(|d| Timespec::now(libc::CLOCK_MONOTONIC).checked_add_duration(&d))
        .and_then(|t| t.to_timespec());

    loop {
        // No need to wait if the value already changed.
        if unsafe {(*futex).load(Relaxed)} != expected {
            return true;
        }
        let r = unsafe {
            // Use FUTEX_WAIT_BITSET rather than FUTEX_WAIT to be able to give an
                // absolute time rather than a relative time.
            libc::syscall(
                libc::SYS_futex,
                futex as *const AtomicU32,
                libc::FUTEX_WAIT_BITSET | libc::FUTEX_PRIVATE_FLAG,
                expected,
                timespec.as_ref().map_or(null(), |t| t as *const libc::timespec),
                null::<u32>(), // This argument is unused for FUTEX_WAIT_BITSET.
                !0u32,         // A full bitmask, to make it behave like a regular FUTEX_WAIT.
            )
        };
        match (r < 0).then(errno) {
            Some(libc::ETIMEDOUT) => return false,
            Some(libc::EINTR) => continue,
            _ => return true,
        }
    }
}
/// Wake up one thread that's blocked on futex_wait on this futex.
///
/// Returns true if this actually woke up such a thread,
/// or false if no thread was waiting on this futex.
///
/// On some platforms, this always returns false.
#[cfg(any(target_os = "linux", target_os = "android"))]
pub fn futex_wake(futex: *const AtomicU32) -> bool {
    let ptr = futex as *const AtomicU32;
    let op = libc::FUTEX_WAKE | libc::FUTEX_PRIVATE_FLAG;
    unsafe { libc::syscall(libc::SYS_futex, ptr, op, 1) > 0 }
}

pub fn errno() -> i32 {
  unsafe { (*libc::__errno_location()) as i32 }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Timespec {
    tv_sec: i64,
    tv_nsec: Nanoseconds,
}
impl Timespec {
  pub fn now(clock: libc::clockid_t) -> Timespec {
      use std::mem::MaybeUninit;

      let mut t = MaybeUninit::uninit();
      cvt(unsafe { libc::clock_gettime(clock, t.as_mut_ptr()) }).unwrap();
      Timespec::from(unsafe { t.assume_init() })
  }
  pub fn checked_add_duration(&self, other: &Duration) -> Option<Timespec> {
      let mut secs = self.tv_sec.checked_add_unsigned(other.as_secs())?;

      // Nano calculations can't overflow because nanos are <1B which fit
      // in a u32.
      let mut nsec = other.subsec_nanos() + self.tv_nsec.0;
      if nsec >= NSEC_PER_SEC as u32 {
          nsec -= NSEC_PER_SEC as u32;
          secs = secs.checked_add(1)?;
      }
      Some(Timespec::new(secs, nsec.into()))
  }
  pub fn to_timespec(&self) -> Option<libc::timespec> {
      Some(libc::timespec {
          tv_sec: self.tv_sec.try_into().ok()?,
          tv_nsec: self.tv_nsec.0.try_into().ok()?,
      })
  }
  const fn new(tv_sec: i64, tv_nsec: i64) -> Timespec {
        // On Apple OS, dates before epoch are represented differently than on other
        // Unix platforms: e.g. 1/10th of a second before epoch is represented as `seconds=-1`
        // and `nanoseconds=100_000_000` on other platforms, but is `seconds=0` and
        // `nanoseconds=-900_000_000` on Apple OS.
        //
        // To compensate, we first detect this special case by checking if both
        // seconds and nanoseconds are in range, and then correct the value for seconds
        // and nanoseconds to match the common unix representation.
        //
        // Please note that Apple OS nonetheless accepts the standard unix format when
        // setting file times, which makes this compensation round-trippable and generally
        // transparent.
        #[cfg(any(
            target_os = "macos",
            target_os = "ios",
            target_os = "tvos",
            target_os = "watchos"
        ))]
        let (tv_sec, tv_nsec) =
            if (tv_sec <= 0 && tv_sec > i64::MIN) && (tv_nsec < 0 && tv_nsec > -1_000_000_000) {
                (tv_sec - 1, tv_nsec + 1_000_000_000)
            } else {
                (tv_sec, tv_nsec)
            };
        assert!(tv_nsec >= 0 && tv_nsec < NSEC_PER_SEC as i64);
        // SAFETY: The assert above checks tv_nsec is within the valid range
        Timespec { tv_sec, tv_nsec: Nanoseconds(tv_nsec as u32) }
    }
}

pub trait IsMinusOne {
    fn is_minus_one(&self) -> bool;
}

macro_rules! impl_is_minus_one {
    ($($t:ident)*) => ($(impl IsMinusOne for $t {
        fn is_minus_one(&self) -> bool {
            *self == -1
        }
    })*)
}

impl_is_minus_one! { i8 i16 i32 i64 isize }

pub fn cvt<T: IsMinusOne>(t: T) -> std::io::Result<T> {
    if t.is_minus_one() { Err(std::io::Error::last_os_error()) } else { Ok(t) }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
struct Nanoseconds(u32);

impl From<libc::timespec> for Timespec {
    fn from(t: libc::timespec) -> Timespec {
        Timespec::new(t.tv_sec as i64, t.tv_nsec as i64)
    }
}