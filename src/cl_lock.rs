use core::{cell::UnsafeCell, mem::{size_of, ManuallyDrop}, ptr::addr_of, simd::Simd, sync::atomic::{fence, AtomicU8, Ordering}};

use crate::utils::publish_changes_on_object;



#[repr(C)] #[repr(align(64))]
pub struct SmallLock<T> {
  data: UnsafeCell<T>,
  lock: AtomicU8
}

#[repr(C)]
union Data<T> {
  data: ManuallyDrop<T>,
  simd: Simd<u64, 8>,
  uninit: ()
}

impl<T> SmallLock<T> {
  pub fn new(data: T) -> Self {
    const {
      assert!(size_of::<T>() <= 64 - 8, "Data can be at most 56 bytes in size");
      assert!(size_of::<Self>() == 64, "Data wont fit in cache line");
    }
    Self { data: UnsafeCell::new(data), lock: AtomicU8::new(0) }
  }
  #[inline(always)]
  pub unsafe fn load_opportunistically(&self) -> T where T: Copy {
    let mut data = Data { uninit: () };
    data.simd = addr_of!(*self).cast::<Simd<u64,8>>().read();
    return ManuallyDrop::into_inner(data.data);
  }
  #[inline(always)]
  pub fn try_lock(&self) -> Option<&mut T> {
    match self.lock.compare_exchange_weak(0, u8::MAX, Ordering::Acquire, Ordering::Relaxed) {
      Ok(_) => {
        return Some(unsafe { &mut*self.data.get() });
      },
      Err(_) => return None,
    };
  }
  #[inline(always)]
  pub fn release(&self) {
    self.lock.store(0, Ordering::Release);
  }
}

unsafe impl<T> Sync for SmallLock<T> {}
impl<T> !Copy for SmallLock<T> {}
impl<T> !Send for SmallLock<T> {}

#[test]
fn banging_it() {

  let lock = SmallLock::new(0usize);

  let limit = 4096*4;

  std::thread::scope(|scope|{
    for _ in 0 .. limit {
      let lock = &lock;
      scope.spawn(move || {
        let data = loop { if let Some(ptr) = lock.try_lock() { break ptr } else { std::thread::yield_now() } };
        *data += 1;
        lock.release();
      });
    }
  });
  let Some(ptr) = lock.try_lock() else { panic!() };
  assert!(*ptr == limit, "data is {}", *ptr);
}