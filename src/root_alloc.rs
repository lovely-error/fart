
use std::{alloc::{alloc, Layout}, sync::atomic::{AtomicU16, Ordering, fence}, cell::UnsafeCell, thread, ptr::{null_mut, addr_of_mut, addr_of, slice_from_raw_parts}, mem::MaybeUninit};

use crate::{cast, utils::PageSource};

pub struct RootAllocator {
  super_page_start: UnsafeCell<*mut [u8;4096]>,
  offset: AtomicU16,
}

impl RootAllocator {
  fn alloc_superpage() -> *mut () {
    let mem = unsafe { alloc(Layout::from_size_align_unchecked(1 << 21, 4096)) };
    mem.cast()
  }
  pub fn new() -> Self {
    Self {
      super_page_start: UnsafeCell::new(Self::alloc_superpage().cast()),
      offset: AtomicU16::new(0) }
  }
  pub fn try_get_block(&self) -> Option<Block4KPtr> {
    let offset = self.offset.fetch_add(1 << 1, Ordering::Relaxed);
    let locked = offset & 1 == 1;
    if locked { return None }
    let index = offset >> 1;
    let did_overshoot = index >= 512;
    if did_overshoot {
      let item = self.offset.fetch_or(1, Ordering::Relaxed);
      let already_locked = item & 1 == 1;
      if already_locked { return None }
      else { // we gotta provide new page
        fence(Ordering::AcqRel); // put after any prior spalloc
        let page = Self::alloc_superpage();
        unsafe { *self.super_page_start.get() = page.cast() };
        self.offset.store(1 << 1, Ordering::Release);
        return Some(Block4KPtr(page.cast()));
      }
    };
    fence(Ordering::Acquire); // we must see that page got allocated
    let ptr = unsafe {(*self.super_page_start.get()).add(index as usize)};
    return Some(Block4KPtr(ptr.cast()));
  }
  pub fn get_block(&self) -> Block4KPtr {
    loop {
      let maybe_page = self.try_get_block();
      if let Some(page) = maybe_page { return page }
    }
  }
}
pub struct Block4KPtr(pub(crate) *mut u8);

// unsafe impl Send for RootAllocator {}
unsafe impl Sync for RootAllocator {}


#[test]
fn alloc_works() {
  // this will eat a lot of ram, fix it if not disposed properly
  const THREAD_COUNT:usize = 4096;
  let ralloc = RootAllocator::new();
  let ptrs: [*mut u8;THREAD_COUNT] = [null_mut(); THREAD_COUNT];
  thread::scope(|s|{
    for i in 0 .. THREAD_COUNT {
      let unique_ref = &ralloc;
      let fuck = addr_of!(ptrs) as u64 ;
      s.spawn(move || {
        let ptr;
        loop {
          if let Some(ptr_) = unique_ref.try_get_block() {
            ptr = ptr_; break;
          };
        }
        let Block4KPtr(v) = ptr;
        for ix in 0 .. 4096 {
          unsafe { *v.cast::<u8>().add(ix) = i as u8; }
        }
        unsafe { *cast!(fuck, *mut u64).add(i) = v as u64 };
      });
    }
  });
  for i in 0 .. THREAD_COUNT {
    let ptr = ptrs[i];
    let sl = unsafe { &*slice_from_raw_parts(ptr, 4096) };
    for s in sl {
        assert!(*s == i as u8, "threads got same memory region");
    }
  }
}

impl PageSource for RootAllocator {
  fn try_drain_page(&mut self) -> Option<Block4KPtr> {
    self.try_get_block()
  }
}