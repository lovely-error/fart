
use core::sync::atomic::compiler_fence;
use std::{
  sync::{
    atomic::{AtomicU16, Ordering, fence, AtomicU64, AtomicU32, AtomicU8, AtomicBool, },
    mpsc::{Receiver, channel, Sender}
  },
  mem::{
    size_of, MaybeUninit, forget,  transmute, align_of, transmute_copy, ManuallyDrop
  },
  ptr::{addr_of, null_mut, copy_nonoverlapping, addr_of_mut },
  thread::{JoinHandle, self, park, Thread, spawn, current, yield_now},
  cell::UnsafeCell,
  alloc::{alloc, Layout},
  marker::PhantomData, time::{Duration, Instant},  collections::HashMap, os::fd::RawFd, simd::Simd
};

use core_affinity::CoreId;
use polling::{Poller, Source, Event};

use crate::{
  root_alloc::{RootAllocator, Block4KPtr},
  utils::{
    FailablePageSource, MemBlock4Kb, InfailablePageSource },
  loopbuffer::InlineLoopBuffer, ensure
};

use core_affinity;

const SMALL_PAGE_SIZE : usize = 4096;

pub struct RegionMetadata {
  ref_count: AtomicU16
}
#[repr(C)] #[repr(align(4096))]
struct Page {
  metadata: RegionMetadata,
  bytes: MaybeUninit<[u8; SMALL_PAGE_SIZE - size_of::<RegionMetadata>()]>
}
ensure!(size_of::<Page>() == SMALL_PAGE_SIZE);

#[derive(Debug)]
struct AllocatorStateData {
  current_page_start: *mut Page,
  allocation_tail: *mut u8,
}
#[derive(Debug)]
struct SubRegionAllocatorInner {
  data: AllocatorStateData
}
#[derive(Debug)]
pub struct SubRegionAllocator(UnsafeCell<SubRegionAllocatorInner>);
impl SubRegionAllocator {
  pub fn new() -> Self {
    Self(UnsafeCell::new(SubRegionAllocatorInner {
      data: AllocatorStateData { current_page_start: null_mut(), allocation_tail: null_mut() }
    }))
  }
  fn set_new_page(&self, block:Block4KPtr) { unsafe {
    let mem_ptr = block.get_ptr();
    let new_page_ptr = mem_ptr.cast::<Page>();
    {
      let ptr = &mut *new_page_ptr;
      // this has to be born with ref count +1 to not allow for
      // situation when other worker possesing objects within this region
      // consumes this region . this would cause racing
      ptr.metadata.ref_count = AtomicU16::new(1);
    };
    let this = &mut*self.0.get();
    this.data.current_page_start = new_page_ptr;
    this.data.allocation_tail = mem_ptr.cast::<u8>().byte_add(size_of::<RegionMetadata>());
  } }
  // true if still needs page
  fn release_page(
    &self,
  ) -> bool { unsafe {
    let this = &mut*self.0.get();
    let prior_count =
      (*this.data.current_page_start).metadata.ref_count.fetch_sub(1, Ordering::Relaxed);
    if prior_count == 1 {
      // extremely rare situation , when we can reuse current page.
      // there is no need to sync with other threads rws
      // since we dont use anything they have done .
      // their writes wont appear out of nowhere.
      // wont they?
      fence(Ordering::Acquire);
      this.data.allocation_tail =
        this.data.current_page_start.cast::<u8>().byte_add(size_of::<RegionMetadata>());
      return false;
    } else {
      return true;
    }
  } }
  #[inline(never)]
  pub fn alloc_bytes(
    &self,
    byte_size: usize,
    alignment: usize,
    free_page_provider: &mut dyn FnMut() -> Option<Block4KPtr>
  ) -> Option<OpaqueRegionItemRef> { unsafe {
    if byte_size == 0 {
      errno::set_errno(errno::Errno(libc::EINVAL));
      return None
    }
    let reserved_space = size_of::<RegionMetadata>().next_multiple_of(alignment);
    if byte_size >= SMALL_PAGE_SIZE - reserved_space {
      // cant reasonably handle this yet
      errno::set_errno(errno::Errno(libc::EINVAL));
      return None;
    }
    let this = &mut*self.0.get();
    if this.data.current_page_start.is_null() {
      let smth = free_page_provider();
      if smth.is_none() { return None; }
      self.set_new_page(smth.unwrap());
    }
    let addr = this.data.allocation_tail.expose_addr();
    if addr == addr & !(SMALL_PAGE_SIZE - 1) {
      let needs_page = self.release_page();
        if needs_page {
          let smth = free_page_provider();
          if smth.is_none() { return None; }
          self.set_new_page(smth.unwrap());
        }
    }
    'attempt:loop {
      let mut ptr = this.data.allocation_tail;
      ptr = ptr.byte_add(ptr.align_offset(alignment));
      let next_allocation_tail = ptr.byte_add(byte_size);
      let region_end_addr =
        this.data.current_page_start.expose_addr() + SMALL_PAGE_SIZE;
      let next_alloc_addr = next_allocation_tail.expose_addr();
      let doesnt_fit = next_alloc_addr > region_end_addr;
      if doesnt_fit {
        // here we need to release current page (effectively detaching it from this worker)
        // and making current page amenable for consumption by last user of some object,
        // residing within the region backed by current page.
        // all regions have owning worker until they become full, at which point they
        // have to be detached and recycled by last user (worker)
        let need_repage = self.release_page();
        if need_repage {
          let smth = free_page_provider();
          if smth.is_none() { return None; }
          self.set_new_page(smth.unwrap());
          continue 'attempt;
        }
      }
      let _ = (*this.data.current_page_start)
        .metadata.ref_count.fetch_add(1, Ordering::Relaxed);

      this.data.allocation_tail = next_allocation_tail;

      return Some(OpaqueRegionItemRef::new(ptr.cast()));
    }
  }; }
  #[must_use]
  pub fn dispose<T: RegionPtrObject>(&self, object: T) -> Option<Block4KPtr>{ unsafe {
    let rptr = object.get_region_metadata_ptr();
    let i = (*rptr).ref_count.fetch_sub(1, Ordering::Release) ;
    if i == 1 {
      fence(Ordering::Acquire);
      return Some(Block4KPtr::new(rptr.cast::<()>()));
    }
    return None
  } }
  #[inline(never)]
  fn alloc_task_frame(
    &self,
    env_align: usize,
    env_size: usize,
    free_page_provider:&mut dyn FnMut() -> Option<Block4KPtr>
  ) -> Option<TaskFrameRef> { unsafe {
    let frame_size = size_of::<RegionMetadata>().next_multiple_of(env_align) + env_size;
    if frame_size >= SMALL_PAGE_SIZE {
      // cant reasonably handle this yet
      errno::set_errno(errno::Errno(libc::EINVAL));
      return None;
    }
    let this = &mut*self.0.get();
    if this.data.current_page_start.is_null() {
      let smth = free_page_provider();
      if smth.is_none() { return None; }
      self.set_new_page(smth.unwrap());
    }
    let addr = this.data.allocation_tail.expose_addr();
    if addr == addr & !(SMALL_PAGE_SIZE - 1) {
      let needs_page = self.release_page();
        if needs_page {
          let smth = free_page_provider();
          if smth.is_none() { return None; }
          self.set_new_page(smth.unwrap());
        }
    }
    'attempt:loop {
      let tail = this.data.allocation_tail;
      assert!(tail.expose_addr() != 0);
      let mtd_ptr = tail.byte_add(tail.align_offset(align_of::<TaskFrame>()));
      let data_ptr_unal = mtd_ptr.byte_add(size_of::<TaskFrame>());
      let data_ptr_al = data_ptr_unal.byte_add(data_ptr_unal.align_offset(env_align));
      let data_is_overaligned = data_ptr_al != data_ptr_unal;
      let mtd_ptr = if data_is_overaligned {
        let ptr = data_ptr_al.byte_sub(size_of::<TaskFrame>());
        assert!(ptr.expose_addr() >= mtd_ptr.expose_addr());
        ptr
      } else {
        mtd_ptr
      };
      let next_allocation_tail = data_ptr_al.byte_add(env_size);
      let region_end_addr =
        this.data.current_page_start.expose_addr() + SMALL_PAGE_SIZE;
      let next_alloc_addr = next_allocation_tail.expose_addr();
      let doesnt_fit = next_alloc_addr > region_end_addr;
      if doesnt_fit {
        // here we need to release current page (effectively detaching it from this worker)
        // and making current page amenable for consumption by last user of some object,
        // residing within the region backed by current page.
        // all regions have owning worker until they become full, at which point they
        // have to be detached and recycled by last user (worker)
        let need_repage = self.release_page();
        if need_repage {
          let smth = free_page_provider();
          if smth.is_none() { return None; }
          self.set_new_page(smth.unwrap());
          continue 'attempt;
        }
      }
      let _ = (*this.data.current_page_start)
        .metadata.ref_count.fetch_add(1, Ordering::Relaxed);

      this.data.allocation_tail = next_allocation_tail;

      return Some(TaskFrameRef(mtd_ptr));
    }
  } }
}

pub trait RegionPtrObject {
  fn get_region_metadata_ptr(&self) -> *mut RegionMetadata;
}

pub type UninitRegionPtr<T> = RegionItemRef<MaybeUninit<T>>;
pub struct RegionItemRef<T>(OpaqueRegionItemRef, PhantomData<T>);
impl <T> RegionItemRef<MaybeUninit<T>> {
  pub fn init(self, data: T) -> RegionItemRef<T> { unsafe {
    self.0.get_data_ptr().cast::<T>().write(data);
    return transmute(self)
  } }
}
impl <T> RegionItemRef<T> {
  // fn new_null() -> Self { Self(OpaqueRegionItemRef::new_null(), PhantomData) }
  pub fn is_null(&self) -> bool { self.0.is_null() }
  pub fn deref(&self) -> &T {
    unsafe { &*self.0.get_data_ptr().cast::<T>() }
  }
  pub fn deref_mut(&self) -> &mut T {
    unsafe { &mut *self.0.get_data_ptr().cast::<T>() }
  }
  pub fn deref_raw(&self) -> *mut T {
    self.0.get_data_ptr().cast()
  }
}
impl <T> RegionPtrObject for RegionItemRef<T> {
  fn get_region_metadata_ptr(&self) -> *mut RegionMetadata {
    self.0.get_region_origin_ptr().cast()
  }
}
#[derive(Debug, Clone, Copy)]
pub struct OpaqueRegionItemRef(*mut ());
impl OpaqueRegionItemRef {
  pub(crate) fn new(ptr: *mut ()) -> Self {
    Self(ptr)
  }
  pub fn new_null() -> Self {
    OpaqueRegionItemRef(null_mut())
  }
  pub fn is_null(&self) -> bool {
    self.0.is_null()
  }
  pub fn get_data_ptr(&self) -> *mut () {
    self.0 as _
  }
  pub(crate) fn get_region_origin_ptr(&self) -> *mut RegionMetadata {
    (self.0.expose_addr() & !((1 << 12) - 1)) as _
  }
  pub fn bind_type<T>(self) -> RegionItemRef<T> {
    RegionItemRef(self, PhantomData)
  }
}
#[derive(Debug, Clone, Copy)]
struct TaskFrameRef(*mut u8);
impl TaskFrameRef {
    fn get_data_ptr(&self) -> *mut u8 {
      unsafe { self.0.byte_add(size_of::<TaskFrame>()).cast() }
    }
    fn get_frame_ptr(&self) -> *mut TaskFrame {
      self.0.cast()
    }
    fn get_region_mtd(&self) -> *mut RegionMetadata {
      self.0.map_addr(|addr| addr & !(SMALL_PAGE_SIZE - 1)).cast()
    }
}
impl RegionPtrObject for TaskFrameRef {
  fn get_region_metadata_ptr(&self) -> *mut RegionMetadata {
      self.get_region_mtd()
  }
}


struct IOPollingWorker {
  work_group: *mut WorkGroup,
  handle: Option<JoinHandle<()>>,
  out_port: Receiver<IOPollingCallbackData>,
  core_pin_index: CoreId,
  have_to_die: AtomicBool,
  went_to_sleep: AtomicBool
}
impl IOPollingWorker {
  fn start(&mut self) {
    if let None = self.handle {
      let this = unsafe { transmute_copy::<_, u64>(&self) };
      self.handle = Some(spawn(move || {
        let this = unsafe { transmute(this) };
        io_polling_routine(this)
      }))
    }
  }
  fn wakeup(&self) {
    if let Some(handle) = &self.handle {
      handle.thread().unpark();
    } else {
      panic!("cant wakeup uninitialised io worker")
    }
  }
}
struct IOPollingCallbackData {
  task_to_resume: Task,
  target: RawFd,
  readable: bool,
  writeable: bool
}
fn io_polling_routine(this: &mut IOPollingWorker) { unsafe {
  let ok = core_affinity::set_for_current(this.core_pin_index);
  assert!(ok, "failed to pin io thread to core");
  let mut io_pending_tasks = HashMap::<usize, (Task, RawFd)>::new();
  let poller = Poller::new().unwrap();
  let work_source = &mut this.out_port;
  let mut gathered_events = Vec::new();
  let mut batch_for_resume = Vec::new();
  let mut id = 0usize;
  let mut get_id = || { id = id.wrapping_add(1); return id };
  'processing: loop {
    let maybe_some_data = work_source.try_recv();
    match maybe_some_data {
      Ok(data) => {
        let id = get_id();
        io_pending_tasks.insert(id, (data.task_to_resume, data.target));
        let ev = Event {
          key: id,
          readable: data.readable,
          writable: data.writeable
        };
        poller.add(data.target, ev).unwrap();
      },
      Err(err) => {
        match err {
          std::sync::mpsc::TryRecvError::Disconnected => {
            return
          },
          std::sync::mpsc::TryRecvError::Empty => ()
        }
      }
    }
    gathered_events.clear();
    let outcome = poller.wait(&mut gathered_events, Some(Duration::from_millis(100)));
    match outcome {
      Ok(_) => (),
      Err(err) => {
        match err.kind() {
            _ => (), // whatever
        }
      }
    }
    let no_continuations_to_resume = gathered_events.is_empty();
    if no_continuations_to_resume && io_pending_tasks.is_empty() {
      let _ =
        this.went_to_sleep.compare_exchange(false, true, Ordering::Relaxed, Ordering::Relaxed);
      park(); // its okay if this gets unparked at random
      let time_to_die =
        this.have_to_die.compare_exchange(true, true, Ordering::Relaxed, Ordering::Relaxed);
      if time_to_die.is_ok() {
        return;
      }
      let _ =
        this.went_to_sleep.compare_exchange(true, false, Ordering::Relaxed, Ordering::Relaxed);
      continue 'processing;
    }
    for event in &gathered_events {
      let (task, fd) = io_pending_tasks.remove(&event.key).unwrap();
      poller.delete(fd).unwrap();
      batch_for_resume.push(task);
    }
    let no_resume_batch = batch_for_resume.is_empty();
    if !no_resume_batch {
      if let Some(free_worker) = (*this.work_group).worker_set.try_acquire_free_worker_mref() {
        free_worker.start();
        free_worker.with_synced_access(|worker| {
          let inner_ctx = &mut (*worker.inner_context_ptr.assume_init());
          let mut pager = PageRouter(||{
            (*inner_ctx.stale_page_drainer.assume_init()).try_drain_page().unwrap_or(
              worker.get_root_allocator().try_get_page_blocking().unwrap())
          });
          while let Some(task) = batch_for_resume.pop() {
            inner_ctx.workset.enque(task, &mut pager)
          }
        });
        batch_for_resume.clear();
      }
      continue;
    }
  }
} }

struct WorkerSet(UnsafeCell<WorkerSetData>);
struct WorkerSetData {
  workers: Vec<Worker>,
  inline_free_indicies: AtomicU64,
  outline_free_indicies: Option<Vec<AtomicU64>>,
  total_worker_count: u32,
  liveness_count: AtomicU16,
  io_thread: IOPollingWorker // sorry :(
}

impl WorkerSet {
  fn mref_worker_at_index(&self, index: u32) -> &mut Worker { unsafe {
    let this = &mut *self.0.get();
    this.workers.get_unchecked_mut(index as usize)
  } }
  fn set_as_free(&self, worker_index: u32) -> bool {
    let this = unsafe { &mut *self.0.get() };

    let map = if this.total_worker_count > 64 {
      let outlines = this.outline_free_indicies.as_ref().unwrap();
      let ix = (worker_index / 64) - 1;
      let ptr = outlines.get(ix as usize).unwrap();
      ptr
    } else {
      &this.inline_free_indicies
    };
    let index_mask = 1u64 << worker_index;
    let mask = !index_mask ;
    let prior = map.fetch_and(mask, Ordering::Relaxed);
    let all_idle = prior & mask == 0;
    all_idle
  }
  fn try_find_free_worker_index(&self) -> Option<u64> { unsafe {
    let inner = &mut *self.0.get();
    let total_worker_count = inner.total_worker_count;
    let mut limit = total_worker_count;
    let limit_ = if total_worker_count / 64 > 0 { 64 } else { total_worker_count };
    let ix = find_free_index(&inner.inline_free_indicies, limit_);
    if ix.is_some() { return ix }
    if let Some(outline) = &inner.outline_free_indicies {
      limit -= 64;
      let limit_ = if limit > 64 { 64 } else { limit };
      for i in outline {
        let ix = find_free_index(i, limit_);
        if ix.is_some() { return ix }
        limit -= 64;
      }
    }
    return None;
  } }
  fn try_acquire_free_worker_mref(&self) -> Option<&mut Worker> { unsafe {
    let this = &mut *self.0.get();
    let outcome = self.try_find_free_worker_index();
    match outcome {
      Some(index) => {
        let ptr = this.workers.get_unchecked_mut(index as usize);
        return Some(ptr)
      },
      None => return None,
    }
  } }
}
fn find_free_index(map: &AtomicU64, total_worker_count: u32) -> Option<u64> {
  let mut indicies : u64 = 0;
  let outcome = map.compare_exchange(0, 0, Ordering::Relaxed, Ordering::Relaxed);
  match outcome {
    Ok(_) => (),
    Err(real) => indicies = real,
  }
  loop {
    let some_index = indicies.trailing_ones();
    if some_index == total_worker_count { return None }
    let index_mask = 1u64 << some_index;
    let new_val = indicies | index_mask;
    let outcome =
      map.compare_exchange_weak(indicies, new_val, Ordering::Relaxed, Ordering::Relaxed);
    match outcome {
      Ok(_) => {
        return Some(some_index as _);
      },
      Err(real) => {
        indicies = real;
        continue;
      },
    }
  }
}
#[repr(C)] #[derive(Debug)]
struct TaskListPageMtd {
  next_page: *mut TaskListPage,
}
const TASK_LIST_PAGE_PACK_LIMIT : usize = (SMALL_PAGE_SIZE - 1) / size_of::<Simd<u64, 16>>();
const TASK_LIST_PAGE_ITEM_LIMIT : usize = TASK_LIST_PAGE_PACK_LIMIT * 16;
#[repr(C)]
union TaskListPageItemsRepr {
  simd: [Simd<u64, 16>; TASK_LIST_PAGE_PACK_LIMIT],
  array: [Task; TASK_LIST_PAGE_ITEM_LIMIT]
}
#[repr(C)]
struct TaskListPage {
  mtd: TaskListPageMtd,
  items: TaskListPageItemsRepr
}
ensure!(size_of::<TaskListPage>() == SMALL_PAGE_SIZE);
struct TaskList {
  read_ptr: *mut (),
  write_ptr: *mut (),
  tail_page: *mut TaskListPage,
  item_count: usize,
}
impl TaskList {
  fn new() -> Self {
    Self {
      read_ptr: null_mut(),
      write_ptr: null_mut(),
      tail_page: null_mut(),
      item_count: 0,
    }
  }
  fn enque_one(
    &mut self,
    task: Task,
    provider: &mut dyn InfailablePageSource
  ) { unsafe {
    if self.read_ptr.is_null() {
      let page = provider.get_page();
      let ptr = page.get_ptr().cast::<TaskListPage>();
      let loc = addr_of_mut!((*ptr).items).cast::<()>();
      self.read_ptr = loc;
      self.write_ptr = loc;
      self.tail_page = ptr;
    }
    let mut write_ptr = self.write_ptr;
    let no_spare_space = write_ptr == write_ptr.map_addr(|addr|addr & !(SMALL_PAGE_SIZE - 1));
    if no_spare_space {
      let cur_w = write_ptr.byte_sub(SMALL_PAGE_SIZE).cast::<TaskListPage>();
      let next = (*cur_w).mtd.next_page;
      if next.is_null() {
        let new = provider.get_page();
        let ptr = new.get_ptr().cast::<TaskListPage>();
        let mtd = &mut (*ptr).mtd;
        mtd.next_page = null_mut();
        (*self.tail_page).mtd.next_page = ptr;
        self.tail_page = ptr;
        write_ptr = addr_of_mut!((*ptr).items).cast();
      } else {
        write_ptr = addr_of_mut!((*next).items).cast();
      }
    }
    let ptr = write_ptr.cast::<Task>();
    ptr.write(task);
    self.write_ptr = ptr.add(1).cast();
    self.item_count += 1;
  } }
  fn deque_one(
    &mut self
  ) -> Option<(Task, Option<Block4KPtr>)> { unsafe {
    let count = self.item_count;
    if count == 0 { return None; }
    let mut page = None;
    let mut rp = self.read_ptr.cast::<Task>();
    let last_item_on_page = rp == rp.map_addr(|addr|addr & !(SMALL_PAGE_SIZE - 1));
    if last_item_on_page {
      let mtd_ptr = rp.byte_sub(SMALL_PAGE_SIZE).cast::<TaskListPageMtd>();
      let mtd = &mut*mtd_ptr;
      let next = mtd.next_page;
      if next.is_null() {
        return None;
      } else {
        page = Some(Block4KPtr::new(mtd_ptr.cast()));
        rp = addr_of_mut!((*next).items).cast();
      }
    }
    let item = rp.read();
    self.read_ptr = rp.add(1).cast();
    self.item_count -= 1;
    return Some((item, page));
  } }
  fn dequeue_pack(&mut self) -> Option<(Simd<u64, 16>, usize, Option<Block4KPtr>)> { unsafe {
    if self.item_count == 0 { return None;}
    let mut recyc_page = None;
    let mut rp = self.read_ptr;
    let last_item_on_page = rp == rp.map_addr(|addr|addr & !(SMALL_PAGE_SIZE - 1));
    if last_item_on_page {
      let page = rp.byte_sub(SMALL_PAGE_SIZE).cast::<TaskListPage>();
      let mtd = &mut(*page).mtd;
      let next = mtd.next_page;
      if next.is_null() {
        // reuse this page
        let ptr = addr_of_mut!(((*page).items));
        self.read_ptr = ptr.cast();
        self.write_ptr = ptr.cast();
        self.tail_page = page;
        return None;
      } else {
        recyc_page = Some(Block4KPtr::new(page.cast()));
        rp = addr_of_mut!((*next).items).cast();
      }
    }
    let item = rp.cast::<Simd<u64, 16>>().read();
    let new_rp = rp.byte_add(size_of::<Simd<u64, 16>>());
    let reader_got_past_writer =
      new_rp.byte_sub(1).map_addr(|addr|addr & !(SMALL_PAGE_SIZE - 1)) ==
      self.write_ptr.byte_sub(1).map_addr(|addr|addr & !(SMALL_PAGE_SIZE - 1)) &&
      new_rp.expose_addr() > self.write_ptr.expose_addr() ;
    if reader_got_past_writer {
      self.write_ptr = new_rp;
    }
    self.read_ptr = new_rp;
    let count = self.item_count;
    let actual_count = if count >= 16 { 16 } else { count };
    self.item_count = count - actual_count;
    return Some((item, actual_count, recyc_page));
  } }
}
#[test]
fn list_works() {
  let mut alloc = RootAllocator::new();
  let mut list = TaskList::new();
  const LIMIT : usize = 1_000_000;
  for i in 0 .. LIMIT {
    list.enque_one(unsafe { transmute(i) }, &mut alloc)
  }
  let mut got_mem = false;
  for i in 0 .. LIMIT {
    let (item, mem) = list.deque_one().unwrap();
    if let Some(mem) = mem {
      println!("got mem {:?}", mem);
      got_mem = true;
    }
    if i != unsafe { transmute(item) } {
      panic!("fk");
    }
  }
  assert!(got_mem)
}
#[test]
fn list_pack_deque_works() {
  let mut alloc = RootAllocator::new();
  let mut list = TaskList::new();
  for i in 0 .. 32usize * 2 {
    list.enque_one(unsafe { transmute(i) }, &mut alloc);
    let pack = list.dequeue_pack().unwrap();
    assert!(pack.0.to_array()[0] == i as _);
    println!("{:?} {}", pack, i);
  }
}
#[test]
fn list_pack_deque_works2() {
  let mut alloc = RootAllocator::new();
  let mut list = TaskList::new();
  for i in 0 .. 512usize {
    list.enque_one(unsafe { transmute(i) }, &mut alloc)
  }
  for i in 0 .. (512 / 16) {
    let pack = list.dequeue_pack().unwrap();
    println!("{:?} {}", pack, i);
    list.enque_one(unsafe { transmute(11usize) }, &mut alloc);
  }
  println!("delimiter");
  for i in 0 .. 2 {
    let pack = list.dequeue_pack().unwrap();
    assert!(pack.0 == Simd::splat(11));
    println!("{:?} ix {}", pack, i)
  }
}
#[repr(C)]
union ImmidiateTasks {
  simd: Simd<u64, 16>,
  items: [Task;16],
  uninit: ()
}
struct TaskSet {
  immidiate_items: ImmidiateTasks,
  imm_count: u8,
  task_list: TaskList,
}
impl TaskSet {
  fn new() -> Self {
    Self {
      task_list: TaskList::new(),
      immidiate_items: ImmidiateTasks { uninit: () },
      imm_count: 0
    }
  }
  fn item_count(&self) -> usize {
    self.task_list.item_count
  }
  fn enque(&mut self, new_item: Task, ps: &mut dyn InfailablePageSource) {
    self.task_list.enque_one(new_item, ps)
  }
  fn deque_one(&mut self) -> Option<(Task, Option<Block4KPtr>)> {
    let mut mem = None;
    if self.imm_count == 0 {
      if let Some((data, len, mem_)) = self.task_list.dequeue_pack() {
        mem = mem_;
        self.immidiate_items.simd = data;
        self.imm_count = len as _;
      } else {
        return None;
      }
    }
    let count = self.imm_count - 1;
    let task = unsafe { self.immidiate_items.items[count as usize] };
    self.imm_count = count;
    return Some((task, mem));
  }
  fn set_pack(&mut self, pack: Simd<u64,16>, count: usize) {
    self.immidiate_items.simd = pack;
    self.imm_count = count as _;
  }
}


struct WorkerFlags(AtomicU8);
impl WorkerFlags {
  fn new() -> Self {
    Self(AtomicU8::new(0))
  }
  const TERMINATION_BIT: u8 = 1 << 0;
  fn mark_for_termination(&self) {
    let _ = self.0.fetch_or(Self::TERMINATION_BIT, Ordering::Relaxed);
  }
  fn is_marked_for_termination(&self) -> bool {
    let flags = self.0.load(Ordering::Relaxed);
    return flags & Self::TERMINATION_BIT != 0
  }
  const CTX_INIT_BIT: u8 = 1 << 2;
  fn mark_as_initialised(&self) {
    let _ = self.0.fetch_or(Self::CTX_INIT_BIT, Ordering::Relaxed);
  }
  fn is_initialised(&self) -> bool {
    let flags = self.0.load(Ordering::Relaxed);
    return flags & Self::CTX_INIT_BIT != 0
  }
  const FIRST_INIT_BIT: u8 = 1 << 3;
  fn was_started(&self) -> bool {
    let flags = self.0.load(Ordering::SeqCst);
    return flags & Self::FIRST_INIT_BIT != 0;
  }
  const WORK_SUBMITED_BIT: u8 = 1 << 4;
  fn mark_first_work_as_submited(&self) {
    let _ = self.0.fetch_or(Self::WORK_SUBMITED_BIT, Ordering::Relaxed);
  }
  fn is_first_work_submited(&self) -> bool {
    let flags = self.0.load(Ordering::Relaxed);
    return flags & Self::WORK_SUBMITED_BIT != 0
  }
  const TRANSACTION_BEGAN_BIT: u8 = 1 << 5;
  fn mark_transaction_begin(&self) {
    let _ = self.0.fetch_or(Self::TRANSACTION_BEGAN_BIT, Ordering::Relaxed);
  }
  const TRANSACTION_ENDED_BIT:u8 = 1 << 6;
  fn mark_transaction_ended(&self) {
    let _ = self.0.fetch_or(Self::TRANSACTION_ENDED_BIT, Ordering::Relaxed);
  }
  fn has_transaction_began(&self) -> bool {
    let flags = self.0.load(Ordering::Relaxed);
    return flags & Self::TRANSACTION_BEGAN_BIT != 0
  }
  fn has_trunsaction_ended(&self) -> bool {
    let flags = self.0.load(Ordering::Relaxed);
    return flags & Self::TRANSACTION_ENDED_BIT != 0
  }
  fn clear_transaction_bits(&self) {
    let clear_mask = Self::TRANSACTION_BEGAN_BIT | Self::TRANSACTION_ENDED_BIT;
    let _ = self.0.fetch_and(!clear_mask, Ordering::Relaxed);
  }
}

struct Worker {
  runner_handle: Option<JoinHandle<()>>,
  work_group: *mut WorkGroup,
  inner_context_ptr: MaybeUninit<*mut WorkerExportContext>,
  index: u32,
  flags: WorkerFlags,
  core_pin_id: core_affinity::CoreId,
  io_tasks_sink: Sender<IOPollingCallbackData>
}
impl Worker {
  fn get_root_allocator(&self) -> &RootAllocator {
    unsafe{&(*self.work_group).ralloc}
  }
  // false if already occupied
  fn mark_as_free(&self) -> bool {
    unsafe{(*self.work_group).worker_set.set_as_free(self.index)}
  }
  fn wakeup(&self) {
    if let Some(thread) = &self.runner_handle {
      thread.thread().unpark();
    };
  }
  fn start(&mut self) { unsafe {
    let init_bit = WorkerFlags::FIRST_INIT_BIT;
    let prior = self.flags.0.fetch_or(init_bit, Ordering::Relaxed);
    let already_initialised = prior & init_bit != 0 ;
    if already_initialised { return }
    if let None = self.runner_handle {
      let copy = transmute_copy::<_, u64>(&self);
      let thread = thread::spawn(move ||{
        let ptr = transmute::<_, &mut Worker>(copy);
        worker_processing_routine(ptr);
      });
      self.runner_handle = Some(thread);
    }
  } }
  fn with_synced_access(&mut self, action: impl FnOnce(&mut Self)) {
    let was_started = self.flags.was_started();
    assert!(was_started, "cannot acccess context of a worker that was not started");
    while !self.flags.is_initialised() {}
    fence(Ordering::Acquire);
    if self.flags.is_first_work_submited() {
      self.flags.mark_transaction_begin();
      action(self);
      fence(Ordering::Release);
      self.flags.mark_transaction_ended();
      self.wakeup();
    } else {
      action(self);
      fence(Ordering::Release);
      self.flags.mark_first_work_as_submited()
    }
  }
}

struct PageRouter<R, F:FnMut()->R>(F);
impl <F:FnMut()->Option<Block4KPtr>>FailablePageSource for PageRouter<Option<Block4KPtr>, F> {
  fn try_drain_page(&mut self) -> Option<Block4KPtr> {
      self.0()
  }
}
impl <F:FnMut()->Block4KPtr>InfailablePageSource for PageRouter<Block4KPtr, F> {
  fn get_page(&mut self) -> Block4KPtr {
      self.0()
  }
}

struct PageRouter_<const S:usize, I>([*mut dyn FailablePageSource; S], I);
impl <const S:usize> InfailablePageSource for PageRouter_<S, *mut dyn InfailablePageSource> {
  fn get_page(&mut self) -> Block4KPtr {
    for i in self.0 {
      if let Some(block) = unsafe { (*i).try_drain_page() } { return block; }
    }
    unsafe { (*self.1).get_page() }
  }
}
impl <const S:usize> FailablePageSource for PageRouter_<S, ()> {
    fn try_drain_page(&mut self) -> Option<Block4KPtr> {
      for i in self.0 {
        if let block@Some(_) = unsafe { (*i).try_drain_page() } { return block; }
      }
      return None
    }
}
struct FreePageList {
  next_page: *mut FreePageList,
  bytes: [u8; SMALL_PAGE_SIZE - size_of::<*mut FreePageList>()]
}
struct RetiredPageAggregator {
  free_pages: *mut FreePageList
}
impl RetiredPageAggregator {
  fn new() -> Self {
    Self { free_pages: null_mut() }
  }
  fn store_page(&mut self, page:Block4KPtr) { unsafe {
    let page = page.get_ptr().cast::<FreePageList>();
    (*page).next_page = null_mut();
    if !self.free_pages.is_null() {
      (*self.free_pages).next_page = page;
    }
    self.free_pages = page;
  } }
  fn try_get_page(&mut self) -> Option<Block4KPtr> {
    let head = self.free_pages;
    if head.is_null() { return None }
    let next = unsafe { (*head).next_page };
    self.free_pages = next;
    return Some(Block4KPtr::new(head.cast()))
  }
  fn dispose(self) { unsafe {
    let mut page = self.free_pages;
    loop {
      if page.is_null() { return; }
      let next = (*page).next_page;
      let out = libc::munmap(page.cast(), SMALL_PAGE_SIZE);
      assert!(out == 0, "Failed to unmap mem?? 0_o\naddress was {:?}", page);
      page = next;
    }
  } }
}
impl FailablePageSource for RetiredPageAggregator {
  fn try_drain_page(&mut self) -> Option<Block4KPtr> {
      self.try_get_page()
  }
}


struct WorkerExportContext {
  allocator: SubRegionAllocator,
  workset: TaskSet,
  stale_page_drainer: MaybeUninit<*mut dyn FailablePageSource>
}

enum ExecState {
  Fetch, Sleep, Execute, Shutdown
}

const TASK_CACHE_SIZE:usize = 16;

fn worker_processing_routine(worker: &mut Worker) { unsafe {

  let ok = core_affinity::set_for_current(worker.core_pin_id);
  assert!(ok, "failed to pin worker {} to core {:?}", worker.index, worker.core_pin_id);

  let mut exported_context = WorkerExportContext {
    allocator: SubRegionAllocator::new(),
    workset: TaskSet::new(),
    stale_page_drainer: MaybeUninit::uninit()
  };
  // exported_context.workset.outline_tasks.
  let mut retired_aggregator = RetiredPageAggregator::new();
  let mut drainer = PageRouter_([
    addr_of_mut!(retired_aggregator),
  ], ());
  exported_context.stale_page_drainer.write(&mut drainer);
  worker.inner_context_ptr.write(addr_of_mut!(exported_context));
  fence(Ordering::Release); // publish context init to the consumer
  worker.flags.mark_as_initialised();

  while !worker.flags.is_first_work_submited() {}
  fence(Ordering::Acquire);

  let mut current_task : Task = Task::new_null();

  let workset_ = addr_of_mut!(exported_context.workset);
  let mut immidiate_state = ImmidiateState {
    spawned_subtask_count: 0,
    current_task: addr_of!(current_task)
  };
  let mut infailable_page_source = PageRouter_([
    &mut drainer
  ], addr_of_mut!((*worker.work_group).ralloc) as *mut dyn InfailablePageSource);
  let task_context = TaskContext::new(
    addr_of_mut!(exported_context),
    addr_of_mut!(immidiate_state),
    addr_of_mut!(infailable_page_source));
  let worker_set = &mut (*worker.work_group).worker_set;

  let mut exec_total = 0u128;
  let mut exec_runs = 0u128;

  let mut exec_state = ExecState::Fetch;
  'dispatch:loop {
    match exec_state {
      ExecState::Fetch => {
        if let Some((new_task, free_mem)) = (*workset_).deque_one() {
          current_task = new_task;
          if let Some(free_mem) = free_mem {
            retired_aggregator.store_page(free_mem);
          }
          exec_state = ExecState::Execute;
          continue 'dispatch;
        }
        exec_state = ExecState::Sleep;
        continue 'dispatch;
      },
      ExecState::Sleep => {
        let _ = worker.mark_as_free();
        loop {
          if worker.flags.has_transaction_began() {
            while !worker.flags.has_trunsaction_ended() {}
            fence(Ordering::Acquire);
            worker.flags.clear_transaction_bits();
            break;
          }
          if worker.flags.is_marked_for_termination() {
            // clean up
            exec_state = ExecState::Shutdown;
            continue 'dispatch;
          }
          park();
        }
        exec_state = ExecState::Fetch;
        continue 'dispatch;
      },
      ExecState::Shutdown => {
        retired_aggregator.dispose();
        let total_time = Duration::from_nanos((exec_total) as u64);
        println!(
            "Worker {} spent in total {:?}, average {:?} per workitem",
            worker.index, total_time, total_time / (exec_runs as u32));
        return;
      }
      ExecState::Execute => {
        let frame_ptr = current_task.task_frame_ptr.get_frame_ptr();
        let frame = &mut*frame_ptr;
        let continuation = frame.continuation.continuation;
        match continuation {
          ContinuationRepr::Then(thunk) => {
            let pre = Instant::now();
            compiler_fence(Ordering::SeqCst);

            let next = thunk(&task_context);
            fence(Ordering::Release);

            compiler_fence(Ordering::SeqCst);
            let post = pre.elapsed();
            exec_total += post.as_nanos();
            exec_runs += 1;

            frame.continuation = next;
            let produced_subtasks = immidiate_state.spawned_subtask_count != 0;
            if produced_subtasks {
              frame.subtask_count.store(
                immidiate_state.spawned_subtask_count as u32, Ordering::Relaxed);
              task_context.clear_dirty_state();
              // last child awakes parent task
            } else {
              // repush task. we want other tasks to run
              exported_context.workset.enque(
                current_task, &mut infailable_page_source);
            }
            share_work(worker_set, &mut*workset_, &mut retired_aggregator);
            exec_state = ExecState::Fetch;
            continue 'dispatch;
          },
          ContinuationRepr::Done => {
            match &frame.dependent_task {
              Supertask::Thread(awaiting_thread, flag) => {
                (**flag).store(true, Ordering::Relaxed);
                awaiting_thread.unpark();
                if let Some(page) = exported_context.allocator.dispose(current_task.task_frame_ptr) {
                  retired_aggregator.store_page(page)
                }
                exec_state = ExecState::Fetch;
                continue 'dispatch;
              },
              Supertask::Parent(parked_task) => {
                let parked_task = *parked_task;
                let parent_frame = parked_task.get_frame_ptr();
                let remaining_subtasks_count =
                  (*parent_frame).subtask_count.fetch_sub(1, Ordering::Relaxed);
                let last_child = remaining_subtasks_count == 1;
                if last_child {
                  fence(Ordering::Acquire);
                  if let Some(page) = exported_context.allocator.dispose(current_task.task_frame_ptr) {
                    retired_aggregator.store_page(page)
                  }
                  current_task.task_frame_ptr = parked_task;
                  continue 'dispatch;
                } else {
                  if let Some(page) = exported_context.allocator.dispose(current_task.task_frame_ptr) {
                    retired_aggregator.store_page(page)
                  }
                  exec_state = ExecState::Fetch;
                  continue 'dispatch;
                }
              },
              Supertask::None => {
                if let Some(page) = exported_context.allocator.dispose(current_task.task_frame_ptr) {
                  retired_aggregator.store_page(page)
                };
                exec_state = ExecState::Fetch;
                continue 'dispatch;
              },
            }
          },
          ContinuationRepr::AwaitIO(fd, r, w, next) => {
            (*current_task.task_frame_ptr.get_frame_ptr()).continuation = Continuation {
              continuation: ContinuationRepr::Then(next)
            };
            let item = IOPollingCallbackData {
              task_to_resume: current_task,
              target: fd, readable: r, writeable: w
            };
            worker.io_tasks_sink.send(item).unwrap();
            (*(*worker.work_group).worker_set.0.get()).io_thread.wakeup();
            exec_state = ExecState::Fetch;
            continue 'dispatch;
          },
        }
      },
    }
  }


} }

fn share_work(
  worker_set: &mut WorkerSet,
  workset: *mut TaskSet,
  page_sink: &mut RetiredPageAggregator
) { unsafe {
  // todo: use warp scheduling ?
  let local_workset = &mut *workset;
  loop {
    let local_item_count = local_workset.item_count();
    let too_few_tasks = TASK_CACHE_SIZE >= local_item_count;
    if too_few_tasks { return; }
    let maybe_free_worker = worker_set.try_acquire_free_worker_mref();
    match maybe_free_worker {
      Some(subordinate_worker) => {
        let (pack, len, mem) = local_workset.task_list.dequeue_pack().unwrap();
        if let Some(mem) = mem {
          page_sink.store_page(mem)
        }
        subordinate_worker.start();
        subordinate_worker.with_synced_access(|subordinate_worker|{
          let subordinates_inner_ctx =
            &mut (*subordinate_worker.inner_context_ptr.assume_init());
          let dst = &mut subordinates_inner_ctx.workset;
          dst.set_pack(pack, len);
        });
        continue;
      },
      None => {
        return
      }
    }
  }
} }

struct ImmidiateState {
  current_task: *const Task,
  spawned_subtask_count: u32,
}
pub struct TaskContext(UnsafeCell<TaskContextInternals>);
struct TaskContextInternals {
  immidiate_state: *mut ImmidiateState,
  worker_inner_context_ref: *mut WorkerExportContext,
  infailable_page_source: *mut dyn InfailablePageSource,
}
pub trait PageSink {
  fn give_page_for_recycle(&mut self, page: Block4KPtr);
}
pub trait PageManager: FailablePageSource + PageSink {}
impl TaskContext {
  fn new(
    worker_inner_context: *mut WorkerExportContext,
    immidiate_state: *mut ImmidiateState,
    infailable_page_source: *mut dyn InfailablePageSource,
  ) -> Self {
    TaskContext(UnsafeCell::new(TaskContextInternals {
      immidiate_state: immidiate_state,
      worker_inner_context_ref: worker_inner_context,
      infailable_page_source,
    }))
  }
  pub fn acccess_frame_as_raw(&self) -> *mut () { unsafe {
    let this = &mut *self.0.get();
    let data_ptr = (*(*this.immidiate_state).current_task).task_frame_ptr.get_data_ptr();
    return data_ptr.cast();
  } }
  pub fn access_frame_as_uninit<T>(&self) -> &mut MaybeUninit<T> { unsafe {
    return &mut *self.acccess_frame_as_raw().cast::<MaybeUninit<T>>()
  }; }
  pub fn access_frame_as_init<T>(&self) -> &mut ManuallyDrop<T> { unsafe {
    return &mut *self.acccess_frame_as_raw().cast::<ManuallyDrop<T>>()
  }; }
  pub fn consume_frame<T>(&self) -> T {
    unsafe{self.acccess_frame_as_raw().cast::<T>().read()}
  }

  // parents never get ahead of their children in the execution timeline.
  // subtasks are never parentless
  pub fn spawn_subtask<T: Send>(&self, env: T, thunk: Thunk) {
    self.spawn_task_common_impl(
      addr_of!(env).cast::<()>(),
      size_of::<T>(), align_of::<T>(), thunk, false);
    forget(env)
  }
  // parent does not depend on this subtask
  pub fn spawn_detached_task<T: Send>(&self, env: T, thunk: Thunk) {
    self.spawn_task_common_impl(
      addr_of!(env).cast::<()>(),
      size_of::<T>(), align_of::<T>(), thunk, true);
    forget(env)
  }
  #[inline(never)]
  fn spawn_task_common_impl(
    &self,
    env_data:*const (),
    env_size:usize,
    env_align:usize,
    thunk: Thunk,
    detached: bool
  ) { unsafe {
    let this = &mut *self.0.get();
    let immidiate_state_ref = &mut *this.immidiate_state;

    if !detached {
      immidiate_state_ref.spawned_subtask_count += 1;
    }

    let frame_ref = (*this.worker_inner_context_ref).allocator.alloc_task_frame(
      env_align, env_size, &mut || Some((*this.infailable_page_source).get_page())).unwrap();
    let mtd_ptr = frame_ref.get_frame_ptr();
    mtd_ptr.write(TaskFrame {
      dependent_task: if !detached {
        Supertask::Parent((*immidiate_state_ref.current_task).task_frame_ptr)
      } else {
        Supertask::None
      },
      subtask_count: AtomicU32::new(0),
      continuation: Continuation { continuation: ContinuationRepr::Then(thunk) }
    });
    let data_ptr = frame_ref.get_data_ptr();
    copy_nonoverlapping(env_data.cast::<u8>(), data_ptr.cast::<u8>(), env_size);

    let subtask = Task::new(frame_ref);
    let task_set = &mut (*this.worker_inner_context_ref).workset;
    task_set.enque(subtask, &mut*this.infailable_page_source);
  }; }
  fn clear_dirty_state(&self) {
    let this = unsafe { &mut *self.0.get() };
    let imm_ctx = unsafe{&mut *this.immidiate_state};
    imm_ctx.spawned_subtask_count = 0;
  }
}

#[derive(Debug)]
pub struct Continuation {
  continuation: ContinuationRepr
}
#[derive(Clone, Copy, Debug)]
enum ContinuationRepr {
  Done,
  Then(Thunk),
  AwaitIO(RawFd, bool, bool, Thunk),
}
impl Continuation {
  pub fn await_io(
    obj: impl Source,
    watch_readability: bool,
    watch_writeability:bool,
    continuation: Thunk
  ) -> Self {
    let desc = obj.raw();
    Self { continuation:
      ContinuationRepr::AwaitIO(desc, watch_readability, watch_writeability, continuation) }
  }
  pub fn then(continuation: Thunk) -> Self {
    return Self { continuation: ContinuationRepr::Then(continuation) }
  }
  pub fn done() -> Self {
    return Self { continuation: ContinuationRepr::Done }
  }
}
type Thunk = fn (&TaskContext) -> Continuation;

#[derive(Debug)]
enum Supertask {
  Thread(Thread, *const AtomicBool),
  Parent(TaskFrameRef),
  None
}

#[repr(C)] #[derive(Debug)]
struct TaskFrame {
  dependent_task: Supertask,
  subtask_count: AtomicU32,
  continuation: Continuation
}

#[repr(C)] #[repr(align(8))] #[derive(Debug, Clone, Copy)]
struct Task {
  task_frame_ptr: TaskFrameRef
}
impl Task {
  fn new(
    task_frame_ptr: TaskFrameRef,
  ) -> Self {
    Self { task_frame_ptr }
  }
  fn new_null() -> Self {
    Self { task_frame_ptr: TaskFrameRef(null_mut()) }
  }
}
pub struct WorkGroup {
  ralloc: RootAllocator,
  worker_set: WorkerSet,
}
#[derive(Debug)]
pub enum WorkGroupCreationError {
  CoreScarcityError {
    present_core_count:u16,
  },
  RequestedZeroWorkers,
}
impl WorkGroup {
  fn get_core_ids() -> Vec<CoreId> {
    let core_ids = core_affinity::get_core_ids().unwrap_or_else(||{
      panic!("cannot retrieve core indicies")
    });
    let total_core_count = core_ids.len();
    if total_core_count > 64 {
      panic!("fixme: cant handle more then 64 cores at the moment")
    }
    return core_ids
  }
  #[allow(dead_code)]
  fn new_with_thread_count(thread_count:usize)
    -> Result<WorkGroupRef, WorkGroupCreationError> {
      if thread_count == 0 { return Err(WorkGroupCreationError::RequestedZeroWorkers);}
    let core_ids = Self::get_core_ids();
    let total_core_count = core_ids.len();
    if thread_count > total_core_count {
      return Err(WorkGroupCreationError::CoreScarcityError {
        present_core_count: total_core_count as _
      })
    }
    return Ok(Self::new_common_impl(&core_ids[..thread_count]))
  }
  pub fn new() -> WorkGroupRef {
    let core_ids = Self::get_core_ids();
    return Self::new_common_impl(&core_ids[..])
  }
  fn new_common_impl(core_ids: &[core_affinity::CoreId]) -> WorkGroupRef { unsafe {
    let total_core_count = core_ids.len();
    let worker_count = total_core_count;
    type WG = WorkGroup;
    let boxed = alloc(
      Layout::from_size_align_unchecked(size_of::<WG>(), align_of::<WG>()));
    let boxed = boxed.cast::<WG>();
    let (send, recv) = channel();

    let mut workers = Vec::new();
    workers.reserve(worker_count);
    for wix in 0 .. worker_count as u32 {
      let pin = core_ids.get(wix as usize).unwrap().clone();
      let worker = Worker {
        index: wix,
        runner_handle: None,
        work_group: boxed,
        flags: WorkerFlags::new(),
        inner_context_ptr: MaybeUninit::uninit(),
        core_pin_id: pin,
        io_tasks_sink: send.clone()
      };
      workers.push(worker);
    }

    boxed.write(WorkGroup {
      ralloc:RootAllocator::new(),
      worker_set: WorkerSet(UnsafeCell::new(WorkerSetData {
        workers: workers,
        inline_free_indicies: AtomicU64::new(0),
        outline_free_indicies: None,
        total_worker_count: worker_count as u32,
        io_thread: IOPollingWorker {
          work_group: boxed,
          handle: None,
          out_port: recv,
          core_pin_index: core_ids[0],
          have_to_die: AtomicBool::new(false),
          went_to_sleep: AtomicBool::new(false)
        },
        liveness_count: AtomicU16::new(1) // +1 because ref exist
      })),
    });
    (*(*boxed).worker_set.0.get()).io_thread.start();

    return WorkGroupRef(boxed)
  } }
  fn destroy(&self) { unsafe {
    let workeset = &mut *self.worker_set.0.get();
    while workeset.inline_free_indicies.compare_exchange(
      0, 0, Ordering::Relaxed, Ordering::Relaxed).is_err() {
        yield_now()
    }
    let io_worker = &mut workeset.io_thread;
    while io_worker.went_to_sleep.compare_exchange(
      true, true, Ordering::Relaxed, Ordering::Relaxed).is_err() { yield_now() }
    io_worker.have_to_die.store(true, Ordering::Relaxed);
    io_worker.wakeup();
    io_worker.handle.take().unwrap().join().unwrap();
    let total_worker_count = workeset.total_worker_count;
    for ix in 0 .. total_worker_count {
      let wref = self.worker_set.mref_worker_at_index(ix);
      if wref.flags.was_started() {
        wref.flags.mark_for_termination();
        wref.wakeup();
        wref.runner_handle.take().unwrap().join().unwrap()
      }
    }
  } }
}
pub struct WorkGroupRef(*mut WorkGroup);
impl WorkGroupRef {
  pub fn submit_and_await<Env: Send>(&self, capture: Env, operation: Thunk) { unsafe {
    let worker = loop { // todo: make work submission less contended
      if let Some(worker) = (*self.0).worker_set.try_acquire_free_worker_mref() {
        break worker
      };
    };
    worker.start();
    let can_resume = AtomicBool::new(false);
    let requesting_thread = current();
    worker.with_synced_access(|worker|{
      let inner_ctx = &mut *worker.inner_context_ptr.assume_init();
      let mut infailable_page_source = PageRouter(||{
        (*inner_ctx.stale_page_drainer.assume_init()).try_drain_page()
        .unwrap_or(worker.get_root_allocator().try_get_page_blocking().unwrap())
      });
      let ptr = inner_ctx.allocator.alloc_task_frame(
        align_of::<Env>(), size_of::<Env>(), &mut || Some(infailable_page_source.get_page())).unwrap();
      let frame = ptr.get_frame_ptr();
      frame.write(TaskFrame {
        dependent_task: Supertask::Thread(requesting_thread, addr_of!(can_resume)),
        subtask_count: AtomicU32::new(0),
        continuation: Continuation { continuation: ContinuationRepr::Then(operation) }
      });
      let data_ptr = ptr.get_data_ptr();
      copy_nonoverlapping(addr_of!(capture).cast::<u8>(), data_ptr.cast::<u8>(), size_of::<Env>());

      let task = Task::new(ptr);
      inner_ctx.workset.enque(task, &mut infailable_page_source);
    });
    forget(capture);
    loop {
      park();
      if can_resume.load(Ordering::Relaxed) { break }
    }
    return ;
  } }
  pub fn submit<Env: Send>(&self, capture: Env, operation: Thunk) { unsafe {
    let worker = loop { // todo: make work submission less contended
      if let Some(worker) = (*self.0).worker_set.try_acquire_free_worker_mref() {
        break worker
      };
    };
    worker.start();
    worker.with_synced_access(|worker|{
      let inner_ctx = &mut *worker.inner_context_ptr.assume_init();
      let mut infailable_page_source = PageRouter(||{
        (*inner_ctx.stale_page_drainer.assume_init()).try_drain_page()
        .unwrap_or(worker.get_root_allocator().try_get_page_blocking().unwrap())
      });
      let ptr = inner_ctx.allocator.alloc_task_frame(
        align_of::<Env>(), size_of::<Env>(), &mut || Some(infailable_page_source.get_page())).unwrap();
      let frame = ptr.get_frame_ptr();
      frame.write(TaskFrame {
        dependent_task: Supertask::None,
        subtask_count: AtomicU32::new(0),
        continuation: Continuation { continuation: ContinuationRepr::Then(operation) }
      });
      let data_ptr = ptr.get_data_ptr();
      copy_nonoverlapping(addr_of!(capture).cast::<u8>(), data_ptr.cast::<u8>(), size_of::<Env>());

      let task = Task::new(ptr);
      inner_ctx.workset.enque(task, &mut infailable_page_source);
    });
    forget(capture);
    return;
  } }

  pub fn clone_ref(&self) -> Self { unsafe {
    (*(*self.0).worker_set.0.get()).liveness_count.fetch_add(1, Ordering::AcqRel);
    return WorkGroupRef(self.0)
  } }
}
impl Drop for WorkGroupRef {
  fn drop(&mut self) { unsafe {
    let count = (*(*self.0).worker_set.0.get()).liveness_count.fetch_sub(1, Ordering::Relaxed);
    if count == 1 {
      (*self.0).destroy()
    }
  } }
}


#[test]
fn test_trivial_tasking() {
  static mut EVIL_FORMULA : &str = "";
  fn single_print(_: &TaskContext) -> Continuation {
    unsafe { EVIL_FORMULA = "CH3O2"; }
    return Continuation::done();
  }
  let work_group = WorkGroup::new();
  work_group.submit_and_await((), single_print);
  assert!("CH3O2" == unsafe { EVIL_FORMULA });
}


#[test]
fn one_child_one_parent() {

  static mut NAME: &str = "";
  fn parent(ctx: &TaskContext) -> Continuation {
    ctx.spawn_subtask((), child);
    return Continuation::done()
  }
  fn child(_: &TaskContext) -> Continuation {
    unsafe { NAME = "I am Jason";};
    return Continuation::done();
  }

  let work_group = WorkGroup::new();
  work_group.submit_and_await((), parent);

  assert!("I am Jason" == unsafe {NAME});
}

#[test]
fn child_child_check_dead() {
  const LIMIT:u64 = 526;
  struct ParentData { counter: AtomicU64, }
  fn parent(ctx: &TaskContext) -> Continuation {
    let frame = ctx.access_frame_as_init::<ParentData>();
    for _ in 0 .. LIMIT {
      ctx.spawn_subtask(&frame.counter, child);
    }
    return Continuation::then(check)
  }
  fn child(ctx: &TaskContext) -> Continuation {
    let counter = ctx.access_frame_as_init::<&AtomicU64>();
    let _ = counter.fetch_add(1, Ordering::Relaxed);
    return Continuation::done();
  }
  fn check(ctx: &TaskContext) -> Continuation {
    let frame = ctx.access_frame_as_init::<ParentData>();
    let val = frame.counter.load(Ordering::Relaxed);

    assert!(val == LIMIT);

    return Continuation::done()
  }

  let frame = ParentData { counter: AtomicU64::new(0) };
  let work_group = WorkGroup::new_with_thread_count(1).unwrap();
  work_group.submit_and_await(frame, parent);
}

#[test]
fn heavy_spawning() {
  let wg = WorkGroup::new();
  let counter = AtomicU64::new(0);
  const LIMIT : u64 = 1_000_000 ;
  struct Data<'i> { counter_ref: &'i AtomicU64, start_time: Option<Instant> }
  wg.submit_and_await(Data {counter_ref:&counter, start_time:None}, |ctx| {
      let data = ctx.access_frame_as_init::<Data>();
      data.start_time = Some(Instant::now());
      for _ in 0 .. LIMIT {
          let ptr = data.counter_ref;
          ctx.spawn_subtask(ptr, |ctx|{
              let ptr = ctx.access_frame_as_init::<&AtomicU64>();
              ptr.fetch_add(1, Ordering::Relaxed);
              return Continuation::done()
          })
      }
      return Continuation::then(|ctx| {
        let data = ctx.access_frame_as_init::<Data>();
        let el = data.start_time.unwrap().elapsed();
        println!("time spent {:?}", el);
        return Continuation::done();
      })
  });
  let val = counter.load(Ordering::Relaxed);
  // println!("{}", val);
  assert!(val == LIMIT);
}


#[test]
fn subsyncing() {
  const LIMIT : usize = 1_000_000;
  let wg = WorkGroup::new();
  let mut st = Vec::<[usize;16]>::new();
  st.reserve(LIMIT);
  struct Data { start_time: Option<Instant>, items: Vec<[usize;16]> }
  wg.submit_and_await(Data {items: st, start_time:None}, |ctx| {
      let data = ctx.access_frame_as_init::<Data>();
      data.start_time = Some(Instant::now());
      let ptr = data.items.as_mut_ptr();
      for i in 0 .. LIMIT {
          let ptr = unsafe{ptr.add(i)};
          let addr : usize = unsafe { transmute(ptr) };
          ctx.spawn_subtask((addr, i), |ctx|{
              let ptr = ctx.access_frame_as_init::<(usize, usize)>();
              let addr = ptr.0;
              let i = ptr.1;
              let item_ptr : *mut [usize;16] = unsafe { transmute(addr) };
              unsafe {item_ptr.write([i;16])};
              return Continuation::done()
          })
      }
      return Continuation::then(|ctx| {
        let data = ctx.access_frame_as_init::<Data>();
        let el = data.start_time.unwrap().elapsed();
        println!("time spent {:?}", el);
        // unsafe { data.items.set_len(LIMIT) };
        let mut ix : usize = 0;
        let mut iter = data.items.iter();
        while let Some(item) = iter.next() {
          for i in item {
            assert!(*i == ix)
          }
          ix += 1
        }
        return Continuation::done();
      })
  });
}

#[test] #[ignore]
fn alo_fr() {
  let ra = RootAllocator::new();
  let sr = SubRegionAllocator::new();
  let fr = sr.alloc_task_frame(
    128, 1, &mut || ra.try_get_page_blocking()).unwrap();
  let frame = fr.get_frame_ptr();
  let data = fr.get_data_ptr();
  println!("{:#?} {:#?} {:#?}", data, frame, unsafe{&*sr.0.get()});
  unsafe { frame.write(TaskFrame {
    dependent_task: Supertask::None,
    subtask_count: AtomicU32::new(1),
    continuation: Continuation { continuation: ContinuationRepr::Done } }) }
  println!("{:?}", unsafe { &*frame });
}

#[test]
fn subsyncing2() {
  const LIMIT : usize = 1_000_000;
  let wg = WorkGroup::new();
  let mut st = Vec::<[usize;16]>::new();
  st.reserve(LIMIT);
  struct Data { start_time: Option<Instant>, items: Vec<[usize;16]>, counter: AtomicU64 }
  wg.submit_and_await(Data {items: st, start_time:None, counter: AtomicU64::new(0)}, |ctx| {
      let data = ctx.access_frame_as_init::<Data>();
      data.start_time = Some(Instant::now());
      let ptr = data.items.as_mut_ptr();
      for i in 0 .. LIMIT {
          let counter = &data.counter;
          let ptr = unsafe{ptr.add(i)};
          let addr : usize = unsafe { transmute(ptr) };
          ctx.spawn_detached_task((addr, i, counter), |ctx|{
              let ptr = ctx.access_frame_as_init::<(usize, usize, &AtomicU64)>();
              let addr = ptr.0;
              let i = ptr.1;
              let item_ptr : *mut [usize;16] = unsafe { transmute(addr) };
              unsafe {item_ptr.write([i;16])};
              ptr.2.fetch_add(1, Ordering::Release);
              return Continuation::done()
          })
      }
      return Continuation::then(sync_loop)
  });
  fn sync_loop(ctx: &TaskContext) -> Continuation {
    let data = ctx.access_frame_as_init::<Data>();
    if data.counter.load(Ordering::Relaxed) != LIMIT as _ {
      return Continuation::then(sync_loop);
    }
    fence(Ordering::Acquire);
    let el = data.start_time.unwrap().elapsed();
    println!("time spent {:?}", el);
    unsafe { data.items.set_len(LIMIT) };
    let mut ix : usize = 0;
    let mut iter = data.items.iter();
    while let Some(item) = iter.next() {
      for i in item {
        assert!(*i == ix)
      }
      ix += 1
    }
    return Continuation::done();
  }
}