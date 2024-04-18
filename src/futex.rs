
use std::sync::atomic::AtomicU32;
use std::time::Duration;

use libc;

#[repr(transparent)] #[derive(Debug)]
pub struct Token(AtomicU32);
impl Token {
    pub fn new() -> Self {
        Self(AtomicU32::new(0))
    }
    pub fn load_value(&self) -> u32 {
        self.0.load(core::sync::atomic::Ordering::Relaxed)
    }
}

/// Wait for a futex_wake operation to wake us.
///
/// Returns an actual value if it has observed a mismatch between expected and actual values,
/// otherwise, returns None
///
/// Duration is required, because futex wait without a duration may
/// never be waken up, because of a bug
///
/// https://groups.google.com/g/mechanical-sympathy/c/QbmpZxp6C64?pli=1
///
#[must_use]
#[inline(always)]
pub fn futex_wait(token: &Token, expected: u32, timeout: Duration) -> Option<u32> {
    use core::ptr::null;
    use core::sync::atomic::Ordering;

    let nano_time = timeout.as_nanos();
    assert!(nano_time < 999_999_999, "Invalid time given to futex_wait!");
    let time_speck: libc::timespec = libc::timespec {
        tv_sec: 0,
        tv_nsec: nano_time as i64,
    };

    let item = &token.0;

    let value = item.compare_exchange(expected, expected, Ordering::Relaxed, Ordering::Acquire);
    let value = match value {
        Ok(v) => v,
        Err(real) => return Some(real),
    };
    loop {
        let r = unsafe {
            libc::syscall(
                libc::SYS_futex,
                item,
                libc::FUTEX_PRIVATE_FLAG | libc::FUTEX_WAIT,
                value,
                &time_speck,
                0,
                null::<u32>(),
                0u32,
            )
        };
        if r < 0 {
            match unsafe { *libc::__errno_location() } {
                libc::EAGAIN => return None,
                libc::ETIMEDOUT => return None,
                libc::EINTR => continue,
                err => unreachable!("futex_wait returned unexpected code {}", err),
            }
        }
        return None;
    }
}
/// Wake up one thread that's blocked on futex_wait on this futex.
///
/// Returns true if this actually woke up such a thread,
/// or false if no thread was waiting on this futex.
///
#[inline(always)]
pub fn futex_wake(token: &Token) -> bool {
    let ptr = &token.0;
    use core::sync::atomic::Ordering::AcqRel;
    ptr.fetch_add(1, AcqRel);
    let op = libc::FUTEX_WAKE | libc::FUTEX_PRIVATE_FLAG ;
    unsafe { libc::syscall(libc::SYS_futex, ptr, op, 1) > 0 }
}


#[test] #[ignore]
fn wont_inf_sleep() {
    let ft = Token::new();
    let v = futex_wait(&ft, 0, Duration::from_micros(100));
    println!("{:?}", v);
}