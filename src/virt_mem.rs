use core::{cell::UnsafeCell, mem::{align_of, offset_of, size_of}, ptr::null_mut, sync::atomic::{AtomicU64, Ordering}};
use libc;

use crate::utils::PageSource;

macro_rules! static_assert {
    ($cond:expr) => {
      const _ : () = if !$cond { std::panic!("Comptime assert failed!") } ;
    };
    ($cond:expr, $msg:expr) => {
      const _ : () = if !$cond { panic!($msg) } ;
    };
}

#[repr(align(4096))] #[allow(dead_code)]
struct Page([u8;4096]);
static_assert!(size_of::<Page>() == 4096);
static_assert!(align_of::<Page>() == 4096);

pub const VIRT_MEM_SIZE: usize = 1024*1024*128;
const PAGE_COUNT: usize = (VIRT_MEM_SIZE / size_of::<Page>()) - 1;
pub const VIRT_MEM_BLOCK_ALIGN: usize = VIRT_MEM_SIZE;

#[repr(C)] #[repr(align(134217728))]
struct PageArray {
  ref_count: AtomicU64,
  pages: [Page; PAGE_COUNT]
}
static_assert!(size_of::<PageArray>() == VIRT_MEM_SIZE);
static_assert!(align_of::<PageArray>() == VIRT_MEM_BLOCK_ALIGN);


pub struct VirtMem(UnsafeCell<VirtMemInner>);
struct VirtMemInner {
  address_space_origin: *mut PageArray,
  current_address: *mut ()
}

impl VirtMem {
  pub fn new() -> Self {
    Self(UnsafeCell::new(VirtMemInner {
      address_space_origin: null_mut(),
      current_address: null_mut()
    }))
  }
  fn inner(&self) -> &mut VirtMemInner {
    unsafe { &mut*self.0.get() }
  }
  fn do_first_init(&self, page: *mut PageArray) {
    let inner = self.inner();
    debug_assert!(inner.address_space_origin.is_null());
    Self::setup_page(page);
    inner.address_space_origin = page;
    inner.current_address = page.map_addr(|a| a + offset_of!(PageArray, pages)).cast()
  }
  fn alloc_space() -> Option<*mut PageArray> {
    let p = 4096usize.next_multiple_of(align_of::<PageArray>());
    let sz = p + size_of::<PageArray>();

    unsafe {
      let ret_val = libc::mmap64(
        null_mut(),
        sz,
        libc::PROT_READ | libc::PROT_WRITE,
        libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_NORESERVE,
        -1,
        0
      );
      if ret_val as isize == -1 {
        let err_code = *libc::__errno_location();
        match err_code {
          libc::ENOMEM |
          libc::ENFILE => return None,
          libc::EAGAIN |
          libc::ETXTBSY |
          libc::EPERM |
          libc::EOVERFLOW |
          libc::ENODEV |
          libc::EINVAL |
          libc::EEXIST |
          libc::EBADF |
          libc::EACCES | _ => unreachable!("Unexpected failure when doing mmap. Error code is {err_code}")
        }
      }
      let aligned_ptr = ret_val.map_addr(|a|a + p).cast::<PageArray>();
      let ret_val = libc::munmap(ret_val, p);
      assert!(ret_val == 0);

      (*aligned_ptr).ref_count = AtomicU64::new(1);
      assert!(aligned_ptr.is_aligned_to(align_of::<PageArray>()));

      return Some(aligned_ptr);
    };
  }
  fn setup_page(page: *mut PageArray) {
    unsafe { (*page).ref_count.store(1, Ordering::Relaxed) };
  }
  fn release_current_page(&self) -> bool {
    let inner = self.inner();
    let rc = unsafe{ &(*inner.address_space_origin).ref_count };
    let prior = rc.fetch_sub(1, Ordering::AcqRel);
    if prior == 1 {
      // reuse
      inner.current_address = inner.address_space_origin.map_addr(|a|a + offset_of!(PageArray, pages)).cast();
      rc.store(1, Ordering::Release);
      return false;
    } else {
      return true;
    }
  }
  pub const MAX_ALLOC_SIZE_IN_BYTES: usize = 4096 * ((1 << 15) - 1);
  pub fn alloc_page_space(&self, page_count: usize) -> Option<VirtMemRange> {
    assert!(page_count > 0);
    assert!(page_count < (1 << 15));
    let inner = self.inner();
    if inner.address_space_origin.is_null() {
      let page = match Self::alloc_space() {
        Some(page) => page,
        None => return None,
      };
      self.do_first_init(page);
    }
    let (cur_addr, next_addr) = loop {
      let cur_addr = inner.current_address as usize;
      let next_addr = cur_addr + ((page_count + 1) * 4096);

      let wont_fit = next_addr > (inner.address_space_origin as usize) + size_of::<PageArray>();
      if wont_fit {
        let need_replace = self.release_current_page();
        if need_replace {
          let new_page = match Self::alloc_space() {
            Some(page) => page,
            None => return None,
          };
          Self::setup_page(new_page);
        }
        continue;
      } else {
        break (cur_addr, next_addr)
      }
    };
    unsafe { (*inner.address_space_origin).ref_count.fetch_add(1, Ordering::AcqRel) };
    let guard_p_addr = next_addr - size_of::<Page>();
    let ret_val = unsafe { libc::mprotect(guard_p_addr as _, 4096, libc::PROT_NONE) };
    assert!(ret_val == 0);
    inner.current_address = next_addr as _;

    let addr = cur_addr as *mut ();
    let page_count = page_count;

    return Some(VirtMemRange { ptr: addr, range: page_count });
  }
  pub fn release_memory(ptr:*mut ()) {
    let origin = ptr.map_addr(|a| a & !(VIRT_MEM_BLOCK_ALIGN - 1));
    let mtd = unsafe{&*origin.cast::<AtomicU64>()};
    let prior = mtd.fetch_sub(1, Ordering::AcqRel);
    if prior == 1 {
      // unmap entire block
      let ret = unsafe { libc::munmap(origin.cast(), VIRT_MEM_SIZE) };
      assert!(ret == 0);
    }
  }
}

pub struct VirtMemRange {
  ptr: *mut (),
  range: usize
}
impl VirtMemRange {
  pub fn fill(self, page_source: &dyn PageSource) -> *mut () {
    let Self { ptr, range } = self;
    let mut count = range;
    let mut remap_addr = ptr as usize;
    assert!(remap_addr % 4096 == 0);
    loop {
      let page = match page_source.try_get_page() {
        Some(page) => page,
        None => unreachable!(),
      };
      unsafe {
        let rmp_raget = page.get_ptr();
        let ret_val = libc::mremap(
          rmp_raget.cast(),
          4096,
          4096,
          libc::MREMAP_FIXED | libc::MREMAP_MAYMOVE, // it shoudnt move
          remap_addr,
        );
        if ret_val as isize == -1 {
          let ret_code = *libc::__errno_location();
          unreachable!("mremap failed with code {ret_code}")
        }
        assert!(ret_val as usize == remap_addr, "Moved the page, but should've not done that!");
      };
      count -= 1;
      if count == 0 { break }
      remap_addr += 4096;
    }

    return ptr;
  }
}

#[test] #[ignore]
fn vmem_basic_check() {
  let ralloc = crate::root_alloc::RootAllocator::new();
  let vmem = VirtMem::new();

  let range = vmem.alloc_page_space(5).unwrap();

  let ptr = range.fill(&ralloc);
  let ptr = ptr.cast::<u8>();

  for i in 0 .. 4096 * 5 {
    unsafe { ptr.add(i).write(u8::MAX) }
  }

  // unsafe { ptr.add(1 + (4096 * 5)).write(u8::MAX) }

  VirtMem::release_memory(ptr.cast());
}