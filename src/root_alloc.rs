
use core::{mem::{align_of, size_of}, ptr::addr_of_mut, sync::atomic::AtomicUsize};
use std::{cell::UnsafeCell, os::raw::c_int, ptr::null_mut, sync::atomic::Ordering};

use crate::utils::FailablePageSource;
use libc::{
  self, MAP_ANONYMOUS, MAP_HUGETLB, MAP_HUGE_2MB, MAP_POPULATE, MAP_PRIVATE, PROT_READ, PROT_WRITE
};

macro_rules! static_assert {
    ($cond:expr) => {
      const _ : () = if !$cond { std::panic!("Comptime assert failed!") } ;
    };
    ($cond:expr, $msg:expr) => {
      const _ : () = if !$cond { panic!($msg) } ;
    };
}
macro_rules! force_pusblish_stores {
    () => {
      core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::Release);
      #[allow(unused_unsafe)] unsafe { core::arch::x86_64::_mm_sfence() };
      core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::Acquire);
    };
}

const PAGE_2MB_SIZE: usize = 1 << 21;
const PAGE_2MB_ALIGN: usize = 1 << 21;
const SMALL_PAGE_LIMIT: usize = PAGE_2MB_SIZE / 4096;

#[repr(align(2097152))]
struct Superpage([Page4K;SMALL_PAGE_LIMIT]);
static_assert!(align_of::<Superpage>() == PAGE_2MB_ALIGN);
static_assert!(size_of::<Superpage>() == PAGE_2MB_SIZE);

#[repr(align(4096))]
struct Page4K([u8;4096]);

#[derive(Debug, Clone, Copy)]
pub enum AllocationFailure {
  WouldRetry, NoMem
}

pub struct RootAllocator(UnsafeCell<RootAllocatorInner>);
struct RootAllocatorInner {
  super_page: *mut Superpage,
  index: AtomicUsize,
  huge_pages_enabled: bool,
}
unsafe impl Sync for RootAllocator {}
impl RootAllocator {
  fn alloc_superpage(&self) -> Result<*mut Superpage, AllocationFailure> { unsafe {
    let attrs: c_int = if (*self.0.get()).huge_pages_enabled {
      MAP_HUGE_2MB | MAP_HUGETLB
    } else {
      0
    };
    let mut mem = libc::mmap64(
        null_mut(),
        PAGE_2MB_SIZE,
        PROT_READ | PROT_WRITE,
        attrs | MAP_ANONYMOUS | MAP_PRIVATE | MAP_POPULATE,
        -1,
        0);
    if mem == libc::MAP_FAILED {
      let err = match *libc::__errno_location() {
        libc::EPERM |
        libc::ENODEV |
        libc::ENFILE |
        libc::ENOMEM => AllocationFailure::NoMem,
        _ => unreachable!()
      };
      return Err(err);
    }
    let out = libc::posix_memalign(&mut mem, PAGE_2MB_ALIGN, PAGE_2MB_SIZE);
    if out != 0 {
      return Err(AllocationFailure::NoMem);
    }
    return Ok(mem.cast())
  } }
  pub fn new() -> Self {
    let enable_huge = match std::env::var("HUGE_PAGES") {
      Ok(str) if str == "1" => true,
      _ => false,
    };
    Self(
      UnsafeCell::new(RootAllocatorInner {
        super_page: null_mut(),
        index: AtomicUsize::new(SMALL_PAGE_LIMIT << 1),
        huge_pages_enabled: enable_huge
      })
    )
  }
  #[inline(never)]
  pub fn try_get_page_fast_bailout(&self) -> Result<Block4KPtr, AllocationFailure> {
    let this = unsafe{&mut*self.0.get()};
    let offset = this.index.fetch_add(1 << 1, Ordering::Relaxed);
    let locked = offset & 1 == 1;
    if locked { return Err(AllocationFailure::WouldRetry) }
    let mut index = offset >> 1;
    let did_overshoot = index >= SMALL_PAGE_LIMIT;
    if did_overshoot {
      let item = this.index.fetch_or(1, Ordering::Relaxed);
      let already_locked = item & 1 == 1;
      if already_locked {
        return Err(AllocationFailure::WouldRetry);
      }
      else { // we gotta provide new page
        let page = match self.alloc_superpage() {
            Ok(mem) => mem,
            Err(err) => {
              this.index.fetch_and((!0) << 1, Ordering::Relaxed);
              return Err(err);
            },
        };
        this.super_page = page.cast();
        force_pusblish_stores!();
        this.index.store(1 << 1, Ordering::Release);
        index = 0;
      }
    };
    let ptr = unsafe {
      core::ptr::addr_of_mut!((*this.super_page).0[index])
    };
    return Ok(Block4KPtr(ptr.cast()));
  }
  pub fn try_get_page_wait_tolerable(&self) -> Result<Block4KPtr, AllocationFailure> {
    loop {
      match self.try_get_page_fast_bailout() {
        Ok(mem) => return Ok(mem),
        Err(err) => {
          match err {
            AllocationFailure::WouldRetry => continue,
            _ => return Err(err)
          }
        },
      }
    }
  }
  pub fn destroy(&self) { unsafe {
    let inner = &*self.0.get();
    let data = inner.index.compare_exchange(
      0, 0, Ordering::Relaxed, Ordering::Relaxed).unwrap_err();
    let index = data >> 1;
    if index >= SMALL_PAGE_LIMIT { return }
    for i in index  .. SMALL_PAGE_LIMIT {
      let ptr = addr_of_mut!((*inner.super_page).0[i]);
      libc::munmap(ptr.cast(), size_of::<Page4K>());
    }
  } }
}
#[derive(Debug, Clone, Copy)]
pub struct Block4KPtr(*mut u8);
impl Block4KPtr {
  pub fn new(ptr: *mut ()) -> Self {
    assert!(ptr.is_aligned_to(4096), "misaligned ptr given to Block4KPtr");
    return Self(ptr.cast())
  }
  pub fn get_ptr(&self) -> *mut u8 {
    self.0 as _
  }
}

impl FailablePageSource for RootAllocator {
    fn try_drain_page(&self) -> Option<Block4KPtr> {
      match self.try_get_page_wait_tolerable() {
        Ok(mem) => Some(mem),
        Err(err) => match err {
          AllocationFailure::WouldRetry => unreachable!(),
          AllocationFailure::NoMem => return None,
        },
      }
    }
}

#[test]
fn alloc_works() {
  use std::{mem::size_of, ptr::{addr_of, null_mut, slice_from_raw_parts}, thread};
  // this will eat a lot of ram, fix it if not disposed properly
  const THREAD_COUNT:usize = 4096 * 4;
  let ralloc = RootAllocator::new();
  let ptrs: [*mut u32;THREAD_COUNT] = [null_mut(); THREAD_COUNT];

  thread::scope(|s|{
    for i in 0 .. THREAD_COUNT {
      let unique_ref = &ralloc;
      let fuck = addr_of!(ptrs) as u64 ;
      s.spawn(move || {
        let ptr;
        loop {
          if let Ok(ptr_) = unique_ref.try_get_page_wait_tolerable() {
            ptr = ptr_; break;
          };
        }
        let Block4KPtr(v) = ptr;
        for ix in 0 .. (4096 / size_of::<u32>()) {
          unsafe { *v.cast::<u32>().add(ix) = i as u32; }
        }
        unsafe { *(fuck as *mut u64).add(i) = v as u64 };
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

