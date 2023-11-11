
use core::sync::atomic::AtomicUsize;
use std::{alloc::{alloc, Layout}, sync::atomic::{AtomicU16, Ordering, fence}, cell::UnsafeCell, thread, ptr::{null_mut, addr_of, slice_from_raw_parts}, mem::size_of};

use crate::{cast, utils::InfailablePageSource};
use libc::{
  self, PROT_READ, PROT_WRITE, MAP_ANONYMOUS, MAP_PRIVATE, MAP_HUGE_2MB, ENOMEM, MAP_FAILED
};
const SMALL_PAGE_SIZE: usize = 4096;
const PAGE_2MB_SIZE: usize = 1 << 21;
const PAGE_2MB_ALIGN: usize = 1 << 21;
const SMALL_PAGE_LIMIT: usize = PAGE_2MB_SIZE / 4096;

pub struct RootAllocator {
  super_page_start: UnsafeCell<*mut [u8;4096]>,
  index: AtomicUsize,
}

impl RootAllocator {
  fn alloc_superpage() -> Option<*mut u8> { unsafe {
    let mut mem = libc::mmap64(
        null_mut(),
        PAGE_2MB_SIZE,
        PROT_READ | PROT_WRITE,
        MAP_ANONYMOUS | MAP_PRIVATE | MAP_HUGE_2MB,
        -1,
        0);
    if mem == MAP_FAILED {
      return None;
    }
    let out = libc::posix_memalign(&mut mem, PAGE_2MB_ALIGN, PAGE_2MB_SIZE);
    if out != 0 {
      return None;
    }
    return Some(mem.cast())
  } }
  pub fn new() -> Self {
    Self {
      super_page_start: UnsafeCell::new(null_mut()),
      index: AtomicUsize::new(SMALL_PAGE_LIMIT << 1)
    }
  }
  #[inline(never)]
  pub fn try_get_page_nonblocking(&self) -> Option<Block4KPtr> {
    let offset = self.index.fetch_add(1 << 1, Ordering::Relaxed);
    let locked = offset & 1 == 1;
    if locked { return None }
    let mut index = offset >> 1;
    let did_overshoot = index >= SMALL_PAGE_LIMIT;
    if did_overshoot {
      let item = self.index.fetch_or(1, Ordering::Relaxed);
      let already_locked = item & 1 == 1;
      if already_locked {
        errno::set_errno(errno::Errno(libc::EWOULDBLOCK));
        return None
      }
      else { // we gotta provide new page
        let page = Self::alloc_superpage()?;
        unsafe { *self.super_page_start.get() = page.cast() };
        self.index.store(1 << 1, Ordering::Release);
        index = 0;
      }
    };
    fence(Ordering::Acquire); // we must see that page got allocated
    let ptr = unsafe { (*self.super_page_start.get()).add(index) };
    return Some(Block4KPtr(ptr.cast()));
  }
  pub fn try_get_page_blocking(&self) -> Option<Block4KPtr> {
    loop {
      if let k@Some(_) = self.try_get_page_nonblocking() {
        return k;
      } else {
        let errno = errno::errno();
        match errno.0 {
          libc::EWOULDBLOCK => continue,
          _ => return None
        }
      }
    }
  }
}
pub struct Block4KPtr(*mut ());
impl Block4KPtr {
  pub fn new(ptr: *mut ()) -> Self {
    assert!(ptr.is_aligned_to(4096), "misaligned ptr given to Block4KPtr");
    return Self(ptr.cast())
  }
  pub fn get_data_ptr(&self) -> *mut u8 {
    self.0 as _
  }
}

// unsafe impl Send for RootAllocator {}
unsafe impl Sync for RootAllocator {}


#[test]
fn alloc_works() {
  // this will eat a lot of ram, fix it if not disposed properly
  const THREAD_COUNT:usize = 4096;
  let ralloc = RootAllocator::new();
  let ptrs: [*mut u32;THREAD_COUNT] = [null_mut(); THREAD_COUNT];
  thread::scope(|s|{
    for i in 0 .. THREAD_COUNT {
      let unique_ref = &ralloc;
      let fuck = addr_of!(ptrs) as u64 ;
      s.spawn(move || {
        let ptr;
        loop {
          if let Some(ptr_) = unique_ref.try_get_page_nonblocking() {
            ptr = ptr_; break;
          };
        }
        let Block4KPtr(v) = ptr;
        for ix in 0 .. (4096 / size_of::<u32>()) {
          unsafe { *v.cast::<u32>().add(ix) = i as u32; }
        }
        unsafe { *cast!(fuck, *mut u64).add(i) = v as u64 };
      });
    }
  });
  for i in 0 .. THREAD_COUNT {
    let ptr = ptrs[i];
    let sl : &[u32] = unsafe { &*slice_from_raw_parts(ptr, 4096 / size_of::<u32>()) };
    for s in sl {
        assert!(*s == i as u32, "threads got same memory region!!!");
    }
  }
}

impl InfailablePageSource for RootAllocator {
  fn get_page(&mut self) -> Block4KPtr {
    self.try_get_page_blocking().unwrap()
  }
}