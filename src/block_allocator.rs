use core::{cell::UnsafeCell, mem::{align_of, offset_of, size_of}, ptr::{addr_of_mut, null_mut}, sync::atomic::{AtomicU64, Ordering}};

use crate::{driver_async::PageSink, root_alloc::Block4KPtr, utils::FailablePageSource};

macro_rules! static_assert {
    ($cond:expr) => {
      const _ : () = if !$cond { std::panic!("Comptime assert failed!") } ;
    };
    ($cond:expr, $msg:expr) => {
      const _ : () = if !$cond { panic!($msg) } ;
    };
}

#[repr(align(64))]
struct CLCell([u8;64]);
const CELL_MAX_COUNT: usize = (4096 - 1) / size_of::<CLCell>();
static_assert!(CELL_MAX_COUNT == 63);

#[repr(C)] #[repr(align(64))]
struct Metadata {
  occupation_map: AtomicU64,
  next_page: *mut MBAllocPage,
}
static_assert!(size_of::<Metadata>() <= 64);
static_assert!(align_of::<Metadata>() == 64);
#[repr(C)] #[repr(align(4096))]
struct MBAllocPage {
  mtd: Metadata,
  slots: [CLCell;CELL_MAX_COUNT]
}
static_assert!(size_of::<MBAllocPage>() == 4096);
static_assert!(align_of::<MBAllocPage>() == 4096);
static_assert!(offset_of!(MBAllocPage, slots) == 64);

pub struct MBAlloc(UnsafeCell<MBAllocInner>);

struct MBAllocInner {
  start_page: *mut MBAllocPage,
  current_page: *mut MBAllocPage,
  tail_page: *mut MBAllocPage
}

impl MBAlloc {
  pub fn new() -> Self {
    MBAlloc(UnsafeCell::new(MBAllocInner {
      start_page: null_mut(),
      current_page: null_mut(),
      tail_page: null_mut()
    }))
  }
  fn do_first_init(&self, page: Block4KPtr) {
    let inner = self.inner();
    let ptr = page.get_ptr().cast::<MBAllocPage>();
    Self::setup_page(ptr);
    inner.current_page = ptr;
    inner.start_page = ptr;
    inner.tail_page = ptr;
  }
  fn inner(&self) -> &mut MBAllocInner {
    unsafe { &mut *self.0.get() }
  }
  fn setup_page(page: *mut MBAllocPage) {
    let mtd = unsafe {&mut(*page).mtd};
    mtd.next_page = null_mut();
    mtd.occupation_map.store(0, Ordering::Relaxed);
  }
  pub fn can_allocate(size:usize, alignment:usize) -> bool {
    debug_assert!(alignment.is_power_of_two());
    let size = size + (alignment > size) as usize * alignment;
    size <= 4096 - size_of::<Metadata>()
  }
  pub fn smalloc(&self, size:usize, alignment:usize, page_source: &dyn FailablePageSource) -> Result<RawMemoryPtr, MAllocFailure> { unsafe {
    if !Self::can_allocate(size, alignment) {
      return Err(MAllocFailure::WontFit);
    }

    let inner = self.inner();
    if inner.start_page == null_mut() {
      let page = match page_source.try_drain_page() {
        Some(page) => page,
        None => return Err(MAllocFailure::NoMem),
      };
      self.do_first_init(page)
    }

    let span_count = (size + 63) / 64;
    let span_bitmask = (1u64 << span_count) - 1;

    let mut page = inner.current_page;
    loop {
      let map = (*page).mtd.occupation_map.load(Ordering::Acquire);
      let first_free = map.trailing_ones();
      let mut occup_bm = 0;
      let mut index = 0;
      for i in first_free as _ ..= (63 - span_count) {
        let bm = span_bitmask << i ;
        let found_space = map & bm == 0;
        let aligned_ok = {
          let al = 64 + 64 * i;
          al.next_multiple_of(alignment) == al
        };
        if found_space && aligned_ok {
          occup_bm = bm; index = i; break
        }
      }
      let found_nothing = occup_bm == 0;
      if found_nothing {
        let next_page = (*page).mtd.next_page;
        if next_page.is_null() {
          let fresh_page = match page_source.try_drain_page() {
            Some(page) => page,
            None => {
              inner.current_page = inner.start_page;
              return Err(MAllocFailure::NoMem)
            },
          };
          let fresh_page = fresh_page.get_ptr().cast::<MBAllocPage>();
          Self::setup_page(fresh_page);
          (*inner.tail_page).mtd.next_page = fresh_page;
          inner.tail_page = fresh_page;
          page = fresh_page;
        } else {
          page = next_page;
        }
        // nothing to be found on this page yet.
        // better luck on a next one!
        inner.current_page = page;
        continue;
      }

      let prior = (*page).mtd.occupation_map.fetch_or(occup_bm, Ordering::AcqRel);
      let raced_with_itself = prior & occup_bm != 0;
      if raced_with_itself {
        continue;
      }
      let ptr = (*page).slots.as_mut_ptr().add(index);
      let ptr = RawMemoryPtr::new(ptr.cast(), MemPtrType::Small { block_count: span_count as u16 });
      return Ok(ptr);
    }
  } }
}
#[derive(Debug, Clone, Copy)]
pub enum MAllocFailure {
  NoMem,
  WontFit
}
#[derive(Debug, Clone, Copy)]
enum MemPtrType {
  Small { block_count: u16 },
  Large { page_count: u16 }
}
#[repr(transparent)] #[derive(Debug, Clone, Copy)]
pub struct RawMemoryPtr(u64);
impl RawMemoryPtr {
  fn new(
    ptr: *mut (),
    ty: MemPtrType
  ) -> Self {
    let (size, tag) = match ty {
      MemPtrType::Small { block_count } => (block_count, 0),
      MemPtrType::Large { page_count } => (page_count, 1),
    };
    let mtd = ((size as usize) << 1) | tag;
    let combined = (mtd << 48) | ptr as usize;
    return Self(combined as u64);
  }
  pub fn get_ptr(&self) -> *mut () {
    (self.0 & ((1 << 48) - 1)) as _
  }
  fn get_ptr_type(&self) -> MemPtrType {
    let mtd = self.0 >> 48;
    let tag = mtd & 1;
    let size = (mtd >> 1) as u16;
    if tag == 0 {
      return MemPtrType::Small { block_count: size };
    } else {
      return MemPtrType::Large { page_count: size };
    }
  }
  #[inline(always)]
  pub fn release_memory(self, page_sink: &dyn PageSink) {
    let mut ptr = self.get_ptr();
    match self.get_ptr_type() {
      MemPtrType::Small { block_count } => {
        let index = ((ptr as usize >> 6) & ((1 << 6) - 1)) - 1;
        let mask = ((1 << block_count) - 1) << index;
        let containing_page = ptr.map_addr(|a|a & !((1 << 12) - 1)).cast::<MBAllocPage>();
        unsafe { (*containing_page).mtd.occupation_map.fetch_and(!mask, Ordering::Release) };
      },
      MemPtrType::Large { mut page_count } => {
        loop {
          page_sink.recycle_page(Block4KPtr::new(ptr));
          page_count -= 1;
          if page_count == 0 { break }
          ptr = unsafe { ptr.byte_add(4096) };
        }
      },
    }
  }
}

#[test]
fn basic() {
  use crate::driver_async::PageStorage;
  let raloc = crate::root_alloc::RootAllocator::new();
  let mballoc = MBAlloc::new();

  let smth = mballoc.smalloc(96, 256, &raloc);
  if let Ok(ptr) = smth {
    assert!(ptr.get_ptr().is_aligned_to(256));
    println!("{:?}", ptr.get_ptr_type());
  } else {
    panic!()
  }
  let smth = mballoc.smalloc(4096-size_of::<Metadata>(), 1, &raloc);
  if let Ok(ptr) = smth {
    assert!(ptr.get_ptr().is_aligned_to(1));
    println!("{:?}", ptr.get_ptr_type());
    let store = PageStorage::new();
    ptr.release_memory(&store)
  } else {
    panic!()
  }
  let smth = mballoc.smalloc(4096-size_of::<Metadata>() + 1, 1, &raloc);
  if let Err(MAllocFailure::WontFit) = smth {
    ()
  } else {
    panic!()
  }
  let smth = mballoc.smalloc(4096-size_of::<Metadata>(), 1, &raloc);
  if let Ok(ptr) = smth {
    assert!(ptr.get_ptr().is_aligned_to(1));
    println!("{:?}", ptr.get_ptr_type());
    let store = PageStorage::new();
    ptr.release_memory(&store)
  } else {
    panic!()
  }
}