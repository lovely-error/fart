
use std::{sync::{atomic::{AtomicU16, Ordering, fence, AtomicU64, AtomicU32, AtomicU8, AtomicBool, }, mpsc::{Receiver, channel, Sender}}, mem::{size_of, MaybeUninit, forget,  transmute, align_of, transmute_copy, needs_drop, ManuallyDrop}, ptr::{addr_of, null_mut, copy_nonoverlapping, addr_of_mut }, thread::{JoinHandle, self, park, Thread, spawn, current, yield_now}, cell::UnsafeCell, alloc::{alloc, Layout}, marker::PhantomData, time::Duration,  collections::HashMap, os::fd::RawFd, simd::Simd};

use core_affinity::CoreId;
use polling::{Poller, Source, Event};

use crate::{
  root_alloc::{RootAllocator, Block4KPtr},
  utils::{
    FailablePageSource, MemBlock4Kb, InfailablePageSource },
  cast,
  loopbuffer::InlineLoopBuffer, array::Array, ensure
};

use core_affinity;

const PAGE_SIZE : usize = 4096;

struct RegionMetadata {
  ref_count: AtomicU16
}
#[repr(C)] #[repr(align(4096))]
struct Page {
  metadata: RegionMetadata,
  bytes: MaybeUninit<[u8; PAGE_SIZE - size_of::<RegionMetadata>()]>
}
ensure!(size_of::<Page>() == PAGE_SIZE);

pub struct SubRegionAllocator {
  current_page_start: *mut Page,
  allocation_tail: *mut u8,
}

static mut DEALLOCATION_COUNT : AtomicU64 = AtomicU64::new(0);
static mut ALLOCATION_COUNT : AtomicU64 = AtomicU64::new(0);


impl SubRegionAllocator {
  pub fn new() -> Self {
    Self { current_page_start: null_mut(),
           allocation_tail: null_mut(), }
  }
  fn set_new_page(&mut self, page_source:&mut dyn InfailablePageSource) { unsafe {
    let new_page_ptr = page_source.get_page().get_ptr().cast::<Page>();
    {
      let ptr = &mut *new_page_ptr;
      // this has to be born with ref count +1 to not allow for
      // situation when other worker possesing objects within this region
      // consumes this region . this would cause racing
      ptr.metadata.ref_count = AtomicU16::new(1);
    };
    self.current_page_start = new_page_ptr;
    self.allocation_tail = new_page_ptr.cast::<u8>().byte_add(size_of::<RegionMetadata>());
  } }
  pub fn alloc_bytes(
    &mut self,
    byte_size: usize,
    alignment: usize,
    page_source:&mut dyn InfailablePageSource
  ) -> OpaqueRegionItemRef { unsafe {
    ALLOCATION_COUNT.fetch_add(1, Ordering::Relaxed);

    assert!(
      byte_size != 0,
      "region byte allocator was not made to deal with 0 byte allocations");
    let reserved_space = size_of::<RegionMetadata>().next_multiple_of(alignment);
    assert!(
      PAGE_SIZE - reserved_space >= byte_size,
      "objects bigger then");
    if self.current_page_start.is_null() {
      self.set_new_page(page_source)
    }
    loop {
      let mut ptr = self.allocation_tail;
      ptr = ptr.byte_add(ptr.align_offset(alignment));
      let next_allocation_tail = ptr.byte_add(byte_size);
      let region_end_addr = self.current_page_start.expose_addr() + PAGE_SIZE;
      let next_alloc_addr = next_allocation_tail.expose_addr();
      let exceeded_region_capacity = next_alloc_addr >= region_end_addr;
      if exceeded_region_capacity {
        // here we need to release current page (effectively detaching it from this worker)
        // and making current page amenable for consumption by last user of some object,
        // residing within the region backed by current page.
        // all regions have owning worker until they become full, at which point they
        // have to be detached and recycled by last user (worker)
        let prior_count =
          (*self.current_page_start).metadata.ref_count.fetch_sub(1, Ordering::Relaxed);
        if prior_count == 1 { // extremely rare situation , when we can reuse current page
          fence(Ordering::Acquire); // lets see other uses as happened
          self.allocation_tail =
            self.current_page_start.cast::<u8>().byte_add(size_of::<RegionMetadata>());
          continue;
        } else {
          self.set_new_page(page_source);
          continue;
        }
      }
      let _ = (*self.current_page_start).metadata.ref_count.fetch_add(1, Ordering::AcqRel);

      self.allocation_tail = next_allocation_tail;

      return OpaqueRegionItemRef::new(ptr.cast());
    }
  }; }
  #[track_caller]
  pub fn dispose(&mut self, object: OpaqueRegionItemRef) -> Option<Block4KPtr>{ unsafe {
    DEALLOCATION_COUNT.fetch_add(1, Ordering::Relaxed);
    let rptr = object.get_region_origin_ptr();
    let i = (*rptr).ref_count.fetch_sub(1, Ordering::Release) ;
    if i == 1 {
      fence(Ordering::Acquire);
      return Some(Block4KPtr::new(rptr.cast::<()>()));
    }
    return None
  } }
  fn alloc_task_frame(
    &mut self,
    env_align: usize,
    env_size: usize,
    page_source:&mut dyn InfailablePageSource
  ) -> UninitRegionPtr<TaskFrame> {
    let header_size = size_of::<TaskFrame>() ;
    let data_loc = header_size.next_multiple_of(env_align);
    let total_size = data_loc + env_size;

    let frame_allocation_limit = PAGE_SIZE - size_of::<RegionMetadata>();
    if total_size > frame_allocation_limit {
      panic!("Cant allocate this much for single object. Use indirection")
    }
    let region_ref = self.alloc_bytes(
      total_size, align_of::<TaskFrame>(), page_source);

    return RegionItemRef(region_ref, PhantomData);
  }
}

pub trait RegionPtrObject {
  fn destruct(self) -> OpaqueRegionItemRef;
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
  fn is_null(&self) -> bool { self.0.is_null() }
  fn deref(&self) -> &T {
    unsafe { &*self.0.get_data_ptr().cast::<T>() }
  }
  fn deref_mut(&self) -> &mut T {
    unsafe { &mut *self.0.get_data_ptr().cast::<T>() }
  }
  fn deref_raw(&self) -> *mut T {
    self.0.get_data_ptr().cast()
  }
  fn bitcopy(&self) -> Self {
    Self(self.0, PhantomData)
  }
}
impl <T> RegionPtrObject for RegionItemRef<T> {
  fn destruct(self) -> OpaqueRegionItemRef {
    self.0
  }
}
#[derive(Debug, Clone, Copy)]
pub struct OpaqueRegionItemRef(u64);
impl OpaqueRegionItemRef {
  pub fn new_null() -> Self {
    OpaqueRegionItemRef(0)
  }
  pub fn is_null(&self) -> bool {
    self.0 == 0
  }
  pub fn new(
    region_segment_addr: *mut (),
  ) -> Self {
    Self(region_segment_addr.expose_addr() as u64)
  }
  pub fn get_data_ptr(&self) -> *mut () {
    self.0 as _
  }
  fn get_region_origin_ptr(&self) -> *mut RegionMetadata {
    (self.0 & !((1 << 12) - 1)) as _
  }
  pub fn bind_type<T>(self) -> RegionItemRef<T> {
    RegionItemRef(self, PhantomData)
  }
}
// it turns out this causes more harm then good
// impl Drop for SubRegionRef {
//   fn drop(&mut self) {
//       panic!(
//         "The lyfecycle of this object cannot be managed implicitly. It must to be manually disposed into any available SubRegionAllocator")
//   }
// }

pub struct Isolated<T>(RegionItemRef<SyncedMtd>, PhantomData<T>);
impl <T> Isolated<T> {
  pub fn clone_ref(&self) -> Self {
    let meta = self.0.deref();
    meta.ref_count.fetch_add(1, Ordering::AcqRel);
    let copy = Self(RegionItemRef(self.0.0, PhantomData), PhantomData);
    return copy
  }
}
// impl <T> Clone for Isolated<T> {
//   fn clone(&self) -> Self {
//     self.clone_ref()
//   }
// }
#[repr(C)]
struct SyncedMtd {
  ref_count: AtomicU32,
  active_readers_count: AtomicU32,
  align_order: u8,
}
impl SyncedMtd {
  fn ptr_to_data(&self) -> *mut () { unsafe {
    let align = 1 << self.align_order;
    let ptr = transmute::<_, *mut ()>(self).byte_add(size_of::<Self>());
    let ptr = ptr.byte_add(ptr.align_offset(align));
    return ptr
  } }
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
  let mut pending_tasks = HashMap::<usize, (Task, RawFd)>::new();
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
        pending_tasks.insert(id, (data.task_to_resume, data.target));
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
          std::sync::mpsc::TryRecvError::Empty => {

          }
        }
      }
    }
    gathered_events.clear();
    poller.wait(&mut gathered_events, Some(Duration::from_secs(0))).unwrap();
    let no_continuations_to_resume = gathered_events.is_empty();
    if no_continuations_to_resume && pending_tasks.is_empty() {
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
      let (task, fd) = pending_tasks.remove(&event.key).unwrap();
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
              worker.get_root_allocator().get_block())
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


const ASSUMED_NUMBER_OF_CORES_ON_AVERAGE_MODERN_MACHINE : usize = 16;
struct WorkerSet(UnsafeCell<WorkerSetData>);
struct WorkerSetData {
  inline_workers: [MaybeUninit<Worker>; ASSUMED_NUMBER_OF_CORES_ON_AVERAGE_MODERN_MACHINE],
  outline_workers: Option<Array<Worker>>,
  inline_free_indicies: AtomicU64,
  outline_free_indicies: Option<Array<AtomicU64>>,
  total_worker_count: u32,
  liveness_count: AtomicU16,
  io_thread: IOPollingWorker // sorry :(
}

impl WorkerSet {
  fn mref_worker_at_index(&self, index: u32) -> &mut Worker { unsafe {
    let this = &mut *self.0.get();
    let work_count = this.total_worker_count;
    if index >= work_count { panic!("invalid worker index") }
    if index < work_count {
      let ptr = addr_of_mut!(this.inline_workers).cast::<Worker>();
      let worker = &mut *ptr.add(index as usize );
      return worker
    } else {
      if let Some(w) = &this.outline_workers {
        let worker = w.ref_item_at_index(
          index as usize - ASSUMED_NUMBER_OF_CORES_ON_AVERAGE_MODERN_MACHINE).unwrap();
        return &mut *worker;
      };
      panic!()
    };
  }; }
  fn set_as_free(&self, index: u32) -> bool {
    let this = unsafe { &mut *self.0.get() };
    if index >= this.total_worker_count { panic!("invalid worker index") }

    let index_mask = 1u64 << index;
    let mask = !index_mask ;
    let prior = this.inline_free_indicies.fetch_and(mask, Ordering::Relaxed);
    let all_idle = prior & mask == 0;
    all_idle
  }
  fn try_find_free_worker_index(&self) -> Option<u64> { unsafe {
    let total_worker_count = (*self.0.get()).total_worker_count;
    let map = &(*self.0.get()).inline_free_indicies;
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
        map.compare_exchange(indicies, new_val, Ordering::Relaxed, Ordering::Relaxed);
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
  } }
  fn try_acquire_free_worker_mref(&self) -> Option<&mut Worker> { unsafe {
    let this = &mut *self.0.get();
    let outcome = self.try_find_free_worker_index();
    match outcome {
      Some(index) => {
        let ptr = this.inline_workers.as_mut_ptr().add(index as usize);
        let ptr = (*ptr).assume_init_mut();
        return Some(ptr)
      },
      None => return None,
    }
  } }
}
struct TaskSet {
  inline_tasks: InlineLoopBuffer<TASK_CACHE_SIZE, Task>,
  outline_tasks: TaskCombiner,
}
impl TaskSet {
  fn item_count(&self) -> usize {
    let inline = self.inline_tasks.item_count();
    let outline = self.outline_tasks.len();
    return inline + outline as usize;
  }
  fn enque(&mut self, new_item: Task, _: &mut dyn InfailablePageSource) {
    let clone = unsafe { addr_of!(new_item).read() };
    let did_push = self.inline_tasks.push_to_tail(new_item);
    if !(did_push) {
      self.outline_tasks.push(clone)
    } else {
      forget(clone)
    }
  }
  fn deque_one(&mut self) -> Option<Task> {
    let task = self.inline_tasks.pop_from_head();
    return task
  }
  fn deque_pack(&mut self) -> Option<(Simd<u64, 32>, u8)> {
    if let Some(p) = self.outline_tasks.last() {
      self.outline_tasks.drop_last();
      return Some(p);
    } else {
      return None
    };
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

struct RetiredPageAggregator {
  free_pages: *mut MemBlock4Kb
}
impl RetiredPageAggregator {
  fn new() -> Self {
    Self { free_pages: null_mut() }
  }
  fn store_page(&mut self, page:Block4KPtr) {
    let ptr = page.get_ptr().cast::<MemBlock4Kb>();
    unsafe {(*ptr).0 = self.free_pages};
    self.free_pages = ptr;
  }
  fn try_get_page(&mut self) -> Option<Block4KPtr> {
    let head = self.free_pages;
    if head.is_null() { return None }
    let next = unsafe { (*head).0 };
    self.free_pages = next;
    return Some(Block4KPtr::new(head.cast()))
  }
}
impl FailablePageSource for RetiredPageAggregator {
  fn try_drain_page(&mut self) -> Option<Block4KPtr> {
      self.try_get_page()
  }
}
#[repr(C)]
union TaskPack {
  items: std::mem::ManuallyDrop<[Task ; 16]>,
  simd: Simd<u64, 32>
}
ensure!(size_of::<[Task ; 16]>() == size_of::<Simd<u64, 32>>());

struct TaskCombiner {
  data: Vec<TaskPack>,
  len: usize,
  subindex: u8,
}
impl TaskCombiner {
  fn new() -> Self {
    Self { data: Vec::new(), subindex: 0, len: 0 }
  }
  fn last(&mut self) -> Option<(Simd<u64, 32>, u8)> {
    if self.len == 0 {
      return None
    }
    let item = unsafe {self.data.last_mut().unwrap().simd};
    return Some((item, self.subindex));
  }
  fn push(&mut self, task: Task) { unsafe {
    if self.subindex == 16 || self.data.is_empty() {
      self.data.push(MaybeUninit::uninit().assume_init());
      self.subindex = 0;
    }
    self.data.last_mut().unwrap().items[self.subindex as usize] = task;
    self.subindex += 1;
    self.len += 1;
  } }
  fn drop_last(&mut self) {
    if self.len == 0 { return }
    self.len -= self.subindex as usize;
    let _ = self.data.pop();
    if self.data.is_empty() {
      self.subindex = 0;
    } else {
      self.subindex = 16;
    }
  }
  fn len(&self) -> usize {
    self.len
  }
}

struct WorkerExportContext {
  allocator: SubRegionAllocator,
  workset: TaskSet,
  stale_page_drainer: MaybeUninit<*mut dyn FailablePageSource>
}

enum ExecState {
  Fetch, Sleep, Execute
}

const TASK_CACHE_SIZE:usize = 16;

fn worker_processing_routine(worker: &mut Worker) { unsafe {

  let ok = core_affinity::set_for_current(worker.core_pin_id);
  assert!(ok, "failed to pin worker {} to core {:?}", worker.index, worker.core_pin_id);

  let mut exported_context = WorkerExportContext {
    allocator: SubRegionAllocator::new(),
    workset: TaskSet {
      inline_tasks:InlineLoopBuffer::new(),
      outline_tasks: TaskCombiner::new()
    },
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

  let workset_ = addr_of_mut!(exported_context.workset);
  let mut immidiate_state = ImmidiateState {
    spawned_subtask_count: 0,
    current_task: MaybeUninit::uninit()
  };
  let mut infailable_page_source = PageRouter_([
    &mut drainer
  ], addr_of_mut!((*worker.work_group).ralloc) as *mut dyn InfailablePageSource);
  let task_context = TaskContext::new(
    addr_of_mut!(exported_context),
    addr_of_mut!(immidiate_state),
    addr_of_mut!(infailable_page_source),
    addr_of_mut!(retired_aggregator));
  let worker_set = &mut (*worker.work_group).worker_set;

  let mut exec_state = ExecState::Fetch;
  'dispatch:loop {
    match exec_state {
      ExecState::Fetch => {
        if let Some(task) = (*workset_).deque_one() {
          immidiate_state.current_task.write(task);
          exec_state = ExecState::Execute;
          continue 'dispatch;
        }
        if let Some((pack, count)) = (*workset_).deque_pack() {
          exported_context.workset.inline_tasks.insert_pack(pack, count as _);
          exec_state = ExecState::Fetch;
          continue 'dispatch;
        }
        exec_state = ExecState::Sleep;
        continue 'dispatch;
      },
      ExecState::Sleep => {
        let _ = worker.mark_as_free();
        // let rc = &(*(*worker.work_group).worker_set.0.get()).liveness_count;
        // let outcome = rc.compare_exchange(0, 0, Ordering::Relaxed, Ordering::Relaxed);
        // let should_terminate_self = all_idle && outcome.is_ok();
        // if should_terminate_self {
        //   // release resources
        //   return;
        // }
        //
        loop {
          if worker.flags.has_transaction_began() {
            while !worker.flags.has_trunsaction_ended() {}
            fence(Ordering::Acquire);
            worker.flags.clear_transaction_bits();
            break;
          }
          if worker.flags.is_marked_for_termination() {
            // clean up
            return;
          }
          park();
        }
        exec_state = ExecState::Fetch;
        continue 'dispatch;
      },
      ExecState::Execute => {
        let mut continuation = immidiate_state.current_task.assume_init_mut().task_frame_ptr.deref_mut().continuation.continuation;
        'fast_path: loop {
          match continuation {
            ContinuationRepr::Then(thunk) => {
              let next = thunk(&task_context);
              let produced_subtasks = immidiate_state.spawned_subtask_count != 0;
              if produced_subtasks {
                let current_task = immidiate_state.current_task.assume_init_read();
                let frame = current_task.task_frame_ptr.deref_mut();
                frame.resume_task_meta.write(current_task.metadata);
                frame.subtask_count.store(
                  immidiate_state.spawned_subtask_count as u32, Ordering::Relaxed);
                frame.continuation = next;
                share_work(worker_set, &mut*workset_);
                task_context.clear_dirty_state();
                exec_state = ExecState::Fetch;
                continue 'dispatch;
              } else {
                continuation = next.continuation;
                continue 'fast_path
              }
            },
            ContinuationRepr::Done => {
              let current_task = immidiate_state.current_task.assume_init_mut();
              let current_task_frame = current_task.task_frame_ptr.deref();
              match &current_task_frame.dependent_task {
                Supertask::Thread(awaiting_thread, flag) => {
                  (**flag).store(true, Ordering::Relaxed);
                  awaiting_thread.unpark();
                  exported_context.allocator.dispose(
                    immidiate_state.current_task.assume_init_read().task_frame_ptr.0);
                  exec_state = ExecState::Fetch;
                  continue 'dispatch;
                },
                Supertask::Parent(parked_task_ref) => {
                  let parent_task = parked_task_ref.bitcopy();
                  let parent_frame = parent_task.deref_mut();
                  fence(Ordering::Release);
                  let remaining_subtasks_count =
                    parent_frame.subtask_count.fetch_sub(1, Ordering::Relaxed);
                  let last_child = remaining_subtasks_count == 1;
                  if last_child {
                    fence(Ordering::Acquire);
                    exported_context.allocator.dispose(current_task.task_frame_ptr.0);

                    let parent_meta = parent_frame.resume_task_meta.assume_init_read();

                    current_task.metadata = parent_meta;
                    continuation = parent_frame.continuation.continuation;

                    current_task.task_frame_ptr = parent_task;

                    continue 'fast_path;
                  } else {
                    exported_context.allocator.dispose(
                      immidiate_state.current_task.assume_init_read().task_frame_ptr.0);
                    exec_state = ExecState::Fetch;
                    continue 'dispatch;
                  }
                },
                Supertask::None => {
                  exported_context.allocator.dispose(
                    immidiate_state.current_task.assume_init_read().task_frame_ptr.0);
                  exec_state = ExecState::Fetch;
                  continue 'dispatch;
                },
              }
            },
            ContinuationRepr::AwaitIO(fd, r, w, next) => {
              immidiate_state.current_task.assume_init_mut()
              .task_frame_ptr.deref_mut().continuation = Continuation {
                continuation: ContinuationRepr::Then(next)
              };
              let item = IOPollingCallbackData {
                task_to_resume: immidiate_state.current_task.assume_init_read(),
                target: fd, readable: r, writeable: w
              };
              worker.io_tasks_sink.send(item).unwrap();
              (*(*worker.work_group).worker_set.0.get()).io_thread.wakeup();
              exec_state = ExecState::Fetch;
              continue 'dispatch;
            },
          }
        }
      },
    }
  }


} }

fn share_work(
  worker_set: &mut WorkerSet,
  workset: *mut TaskSet,
) { unsafe {
  // todo: use warp scheduling ?
  let local_item_count = (*workset).item_count();
  let have_too_many_tasks = local_item_count > TASK_CACHE_SIZE;
  if have_too_many_tasks {
    let ws = &mut *workset;
    loop {
      let pack = ws.outline_tasks.last();
      match pack {
        Some((pack, count)) => {
          let maybe_free_worker = worker_set.try_acquire_free_worker_mref();
          match maybe_free_worker {
            Some(subordinate_worker) => {
              ws.outline_tasks.drop_last();
              subordinate_worker.start();
              subordinate_worker.with_synced_access(|subordinate_worker|{
                let subordinates_inner_ctx =
                  &mut (*subordinate_worker.inner_context_ptr.assume_init());
                let dst = &mut subordinates_inner_ctx.workset;
                dst.inline_tasks.insert_pack(pack, count)
              });
              continue;
            },
            None => {
              return
            }
          }
        },
        None => {
          return
        },
      }
    }
  }
} }

pub struct Arc<T> { ref_count:AtomicU64, value:T }
pub struct ArcBox<T>(OpaqueRegionItemRef, PhantomData<T>);
impl <T>ArcBox<T> {
  fn as_mut_ptr(&mut self) -> *mut T { unsafe {
    let val = &mut *self.0.get_data_ptr().cast::<Arc<T>>();
    return addr_of_mut!(val.value)
  } }
}
impl <T> AsMut<T> for ArcBox<T> {
  fn as_mut(&mut self) -> &mut T {
    unsafe { &mut*self.as_mut_ptr() }
  }
}
impl <T> AsRef<T> for ArcBox<T> {
  fn as_ref(&self) -> &T { unsafe {
    let val = &*self.0.get_data_ptr().cast::<Arc<T>>();
    return &val.value
  } }
}
pub struct Boxed<T>(OpaqueRegionItemRef, PhantomData<T>);
impl <T> Boxed<T> {
  fn as_mut_ptr(&mut self) -> *mut T { unsafe {
    let val = &mut *self.0.get_data_ptr().cast::<Arc<T>>();
    return addr_of_mut!(val.value)
  } }
}
impl <T> AsMut<T> for Boxed<T> {
  fn as_mut(&mut self) -> &mut T {
    unsafe { &mut*self.as_mut_ptr() }
  }
}
impl <T> AsRef<T> for Boxed<T> {
  fn as_ref(&self) -> &T { unsafe {
    let val = &*self.0.get_data_ptr().cast::<Arc<T>>();
    return &val.value
  } }
}

struct ImmidiateState {
  current_task: MaybeUninit<Task>,
  spawned_subtask_count: u32,
}
pub struct TaskContext(UnsafeCell<TaskContextInternals>);
struct TaskContextInternals {
  immidiate_state: *mut ImmidiateState,
  worker_inner_context_ref: *mut WorkerExportContext,
  infailable_page_source: *mut dyn InfailablePageSource,
  retired_page_aggregator: *mut RetiredPageAggregator
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
    retired_page_aggregator: *mut RetiredPageAggregator
  ) -> Self {
    TaskContext(UnsafeCell::new(TaskContextInternals {
      immidiate_state: immidiate_state,
      worker_inner_context_ref: worker_inner_context,
      infailable_page_source,
      retired_page_aggregator
    }))
  }
  pub fn spawn_synced_data<T:Sync>(&self, data: T) -> Isolated<T> {
    let this = unsafe { &mut *self.0.get() };
    let region = unsafe {
      (*this.worker_inner_context_ref).allocator.alloc_bytes(
        size_of::<(SyncedMtd, T)>(), align_of::<(SyncedMtd, T)>(),
        &mut *this.infailable_page_source) };
    let (mtd, data_) = unsafe{&mut *region.get_data_ptr().cast::<(SyncedMtd, T)>()};
    *mtd = SyncedMtd {
      ref_count:AtomicU32::new(1),
      active_readers_count: AtomicU32::new(0),
      align_order: align_of::<T>().ilog2() as u8
    };
    unsafe {addr_of_mut!(*data_).write(data)};
    return Isolated(region.bind_type(), PhantomData)
  }
  pub fn dispose_synced_data<T>(&self, data: Isolated<T>) {
    let SyncedMtd { ref_count, .. } = data.0.deref();
    let rc = ref_count.fetch_sub(1, Ordering::AcqRel);
    if rc == 1 {
      unsafe{(*(*self.0.get()).worker_inner_context_ref).allocator.dispose(data.0.0)};
    }
  }
  pub fn acccess_frame_as_raw(&self) -> *mut () { unsafe {
    let this = &mut *self.0.get();
    let task = &mut (*this.immidiate_state).current_task;
    let data_offset = task.assume_init_mut().raw_ptr_to_data();
    return data_offset.cast();
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
  // does not need destructor
  pub fn spawn_basic_box<T>(&self, data:T) -> Boxed<T> { unsafe {
    assert!(!needs_drop::<T>(), "detected value with nontrivial destructor");
    if size_of::<T>() == 0 {
      return Boxed(OpaqueRegionItemRef::new_null(), PhantomData)
    }
    let this = &mut *self.0.get();
    let region_ref = (*this.worker_inner_context_ref).allocator.alloc_bytes(
      size_of::<T>(), align_of::<T>(),
      &mut*this.infailable_page_source);
    let loc = region_ref.get_data_ptr();
    loc.cast::<T>().write(data);
    return Boxed(region_ref, PhantomData)
  } }
  pub fn dispose_basic_box<T>(&self, some_box: Boxed<T>) { unsafe {
    let this = &mut *self.0.get();
    if let Some(page) = (*this.worker_inner_context_ref).allocator.dispose(some_box.0) {
      (*this.retired_page_aggregator).store_page(page)
    };

  } }
  pub fn spawn_rc_box<T>(&self, data:T) -> ArcBox<T> { unsafe {
    assert!(needs_drop::<T>(), "value must provide a destructor");
    let this = &mut *self.0.get();
    let region_ref = (*this.worker_inner_context_ref).allocator.alloc_bytes(
      size_of::<Arc<T>>(), align_of::<Arc<T>>(), &mut*this.infailable_page_source);
    let loc = region_ref.get_data_ptr();
    let box_ = loc.cast::<Arc<T>>();
    (*box_).ref_count = AtomicU64::new(1);
    addr_of_mut!((*box_).value).write(data);
    return ArcBox(region_ref, PhantomData)
  }; }
  pub fn dispose_rc_box<T>(&self, some_box: ArcBox<T>) { unsafe {
    let val = &*some_box.0.get_data_ptr().cast::<Arc<T>>();
    let rc = val.ref_count.fetch_sub(1, Ordering::AcqRel);
    if rc == 1 {
      let this = &mut *self.0.get();
      if let Some(page) = (*this.worker_inner_context_ref).allocator.dispose(some_box.0) {
        (*this.retired_page_aggregator).store_page(page)
      }
    }
  } }

  // parents never get ahead of their children in the execution timeline.
  // subtasks are never parentless
  pub fn spawn_subtask<T: Send>(&self, env: T, thunk: Thunk) {
    self.spawn_task_common_impl(
      addr_of!(env).cast::<()>(),
      size_of::<T>(), align_of::<T>(), thunk, false);
    forget(env)
  }
  // parent does not depend on this subtask
  pub fn spawn_detached_task<T:Send>(&self, env: T, thunk: Thunk) {
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
      env_align, env_size, &mut*this.infailable_page_source);
    let frame_ref = frame_ref.init(TaskFrame {
      dependent_task: if !detached {
        let parent_frame: RegionItemRef<TaskFrame> =
          immidiate_state_ref.current_task.assume_init_ref().task_frame_ptr.bitcopy();
        Supertask::Parent(parent_frame)
      } else {
        Supertask::None
      },
      resume_task_meta: MaybeUninit::uninit(),
      subtask_count: AtomicU32::new(0),
      continuation: Continuation { continuation: ContinuationRepr::Then(thunk) }
    });
    let data_ptr = frame_ref.deref_raw().cast::<u8>().byte_add(size_of::<TaskFrame>());
    let data_ptr = data_ptr.byte_add(data_ptr.align_offset(env_align));
    copy_nonoverlapping(env_data.cast::<u8>(), data_ptr.cast::<u8>(), env_size);

    let subtask = Task::new(TaskMetadata { data_align: env_align as u16 }, frame_ref);
    let task_set = &mut (*this.worker_inner_context_ref).workset;
    task_set.enque(subtask, &mut*this.infailable_page_source);
  }; }
  fn clear_dirty_state(&self) {
    let this = unsafe { &mut *self.0.get() };
    let imm_ctx = unsafe{&mut *this.immidiate_state};
    imm_ctx.spawned_subtask_count = 0;
  }
}


pub struct Continuation {
  continuation: ContinuationRepr
}
#[derive(Clone, Copy)]
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


enum Supertask {
  Thread(Thread, *const AtomicBool),
  Parent(RegionItemRef<TaskFrame>),
  None
}

#[repr(C)]
struct TaskFrame {
  dependent_task: Supertask,
  subtask_count: AtomicU32,
  resume_task_meta: MaybeUninit<TaskMetadata>,
  continuation: Continuation
}

#[repr(C)] #[repr(align(8))]
struct TaskMetadata {
  data_align: u16
}
#[repr(C)] #[repr(align(8))]
struct Task {
  metadata: TaskMetadata,
  task_frame_ptr: RegionItemRef<TaskFrame>
}
impl Task {
  fn new(
    metadata: TaskMetadata,
    task_frame_ptr: RegionItemRef<TaskFrame>,
  ) -> Self {
    Self { metadata, task_frame_ptr }
  }
  fn raw_ptr_to_data(&self) -> *mut () { unsafe {
    let align = self.metadata.data_align;
    let ptr = self.task_frame_ptr.deref_raw().cast::<u8>();
    let ptr = ptr.byte_add(size_of::<TaskFrame>());
    let ptr = ptr.byte_add(ptr.align_offset(align as usize));
    return ptr.cast()
  } }
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
  pub fn new_with_thread_count(thread_count:usize)
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
    boxed.write(WorkGroup {
      ralloc:RootAllocator::new(),
      worker_set: WorkerSet(UnsafeCell::new(WorkerSetData {
        inline_workers:MaybeUninit::uninit().assume_init(),
        outline_workers: None,
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

    for wix in 0 .. worker_count as u32 {
      let wref = (*boxed).worker_set.mref_worker_at_index(wix);
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
      cast!(wref, *mut Worker).write(worker);
    }

    return WorkGroupRef(boxed)
  } }
  pub fn destroy(&self) { unsafe {
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
  pub fn submit_and_await<Env>(&self, capture: Env, operation: Thunk) { unsafe {
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
        .unwrap_or(worker.get_root_allocator().get_block())
      });
      let frame_ = inner_ctx.allocator.alloc_task_frame(
        align_of::<Env>(), size_of::<Env>(), &mut infailable_page_source);
      let inited_frame = frame_.init(TaskFrame {
        dependent_task: Supertask::Thread(requesting_thread, addr_of!(can_resume)),
        subtask_count: AtomicU32::new(0),
        resume_task_meta: MaybeUninit::uninit(),
        continuation: Continuation { continuation: ContinuationRepr::Then(operation) }
      });
      let data_ptr = inited_frame.deref_raw().cast::<u8>().byte_add(size_of::<TaskFrame>());
      let data_ptr = data_ptr.byte_add(data_ptr.align_offset(align_of::<Env>()));
      copy_nonoverlapping(addr_of!(capture), data_ptr.cast::<Env>(), 1);

      let task = Task::new(TaskMetadata { data_align: align_of::<Env>() as _ },inited_frame);
      inner_ctx.workset.enque(task, &mut infailable_page_source);
    });
    forget(capture);
    loop {

      park();
      if can_resume.load(Ordering::Relaxed) { break }
    }
    return ;
  } }
  pub fn submit<Env>(&self, capture: Env, operation: Thunk) { unsafe {
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
        .unwrap_or(worker.get_root_allocator().get_block())
      });
      let frame_ = inner_ctx.allocator.alloc_task_frame(
        align_of::<Env>(), size_of::<Env>(), &mut infailable_page_source);
      let inited_frame = frame_.init(TaskFrame {
        dependent_task: Supertask::None,
        subtask_count: AtomicU32::new(0),
        resume_task_meta: MaybeUninit::uninit(),
        continuation: Continuation { continuation: ContinuationRepr::Then(operation) }
      });
      let data_ptr = inited_frame.deref_raw().cast::<u8>().byte_add(size_of::<TaskFrame>());
      let data_ptr = data_ptr.byte_add(data_ptr.align_offset(align_of::<Env>()));
      copy_nonoverlapping(addr_of!(capture), data_ptr.cast::<Env>(), 1);

      let task = Task::new(TaskMetadata { data_align: align_of::<Env>() as _ }, inited_frame );
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
  fn single_print(ctx: &TaskContext) -> Continuation {
    unsafe { EVIL_FORMULA = "CH3O2"; }
    return Continuation::done();
  }
  let work_group = WorkGroup::new();
  work_group.submit_and_await((), single_print);
  assert!("CH3O2" == unsafe { EVIL_FORMULA });
}


#[test]
fn one_shild_one_parent() {

  static mut NAME: &str = "";
  fn parent(ctx: &TaskContext) -> Continuation {
    ctx.spawn_subtask((), child);
    return Continuation::done()
  }
  fn child(ctx: &TaskContext) -> Continuation {
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

  unsafe {
    let relc = ALLOCATION_COUNT.load(Ordering::Relaxed);
    let acqc = DEALLOCATION_COUNT.load(Ordering::Relaxed);
    println!("{} {}", acqc, relc);
    assert!(relc == acqc);
  }
}



#[test] #[ignore]
fn mem_locations() { unsafe {
  let memer = || {
    alloc(Layout::from_size_align_unchecked(1 << 21, 4096))
  };
  let mut highs = 0;
  for _ in 0 .. 16 {
    let mem_addr = memer();
    let k = ((mem_addr as u64) >> 12) >> 32;
    if highs == 0 { highs = k } else {
      assert!(highs == k);
    }
  }
} }


// #[test]
// fn ref_sync() {
//   const LIMIT : usize = 1000;
//   struct Ctx {
//     sync_obj: Option<Isolated<Vec<u32>>>
//   }
//   fn begin(ctx: &TaskContext) -> Continuation {
//     let frame = ctx.access_frame_as_init::<Ctx>();
//     let smth = ctx.spawn_synced_data(Vec::new());
//     frame.sync_obj = Some(smth);
//     for _ in 0 .. LIMIT {
//       let smth_clone = frame.sync_obj.as_ref().unwrap().clone_ref();
//       ctx.spawn_subtask(smth_clone, |ctx|{
//         let frame = ctx.access_frame_as_init::<Isolated<Vec<u32>>>();
//         return Continuation::sync_mut(frame.clone_ref(), |val, ctx| {
//           val.push(u32::MAX);
//           let frame = ctx.access_frame_as_init::<Isolated<Vec<u32>>>();
//           ctx.dispose_synced_data(frame);
//           return Continuation::done();
//         });
//       });
//     }
//     return Continuation::then(sync_on_vec);
//   }
//   fn sync_on_vec(ctx: &TaskContext) -> Continuation {
//     let frame = ctx.access_frame_as_init::<Ctx>();
//     let obj = frame.sync_obj.as_ref().unwrap().clone_ref();
//     return Continuation::sync_ref(obj, |val, _| {
//       let len = val.len();
//       if len == LIMIT { return Continuation::then(end) }
//       return Continuation::then(sync_on_vec);
//     })
//   }
//   fn end(ctx: &TaskContext) -> Continuation {
//     let frame = ctx.access_frame_as_init::<Ctx>();
//     let obj = frame.sync_obj.as_ref().unwrap().clone_ref();
//     return Continuation::sync_ref(obj, |val, ctx|{
//       for i in val {
//         assert!(*i == u32::MAX)
//       }
//       let frame = ctx.access_frame_as_init::<Ctx>();
//       let vec = frame.sync_obj.take().unwrap();
//       ctx.dispose_synced_data(vec);
//       return Continuation::done()
//     });
//   }

//   let exec = WorkGroup::new();
//   exec.submit_and_await(Ctx{sync_obj:None}, begin);

//   unsafe {
//     let relc = ALLOCATION_COUNT.load(Ordering::Relaxed);
//     let acqc = DEALLOCATION_COUNT.load(Ordering::Relaxed);
//     // println!("{} {}", acqc, relc);
//     assert!(relc == acqc);
//   }
// }

#[test]
fn race_on_trivial1() {
  let wg = WorkGroup::new_with_thread_count(6).unwrap();
  let counter = AtomicU64::new(0);
  const LIMIT : u64 = 1_000_000 ;
  wg.submit_and_await(&counter, |ctx| {
      let ptr = ctx.access_frame_as_init::<&AtomicU64>();
      for _ in 0 .. LIMIT {
          let ptr = ptr.clone();
          ctx.spawn_subtask(ptr, |ctx|{
              let ptr = ctx.access_frame_as_init::<&AtomicU64>();
              ptr.fetch_add(1, Ordering::Relaxed);
              return Continuation::done()
          })
      }
      return Continuation::done()
  });
  let val = counter.load(Ordering::Relaxed);
  println!("{}", val);
  // assert!(val == LIMIT);
  // unsafe { println!(
  //     "sent to recycle {} ; taken from recycle {}",
  //     GIVEN_FOR_RECYCLE_COUNT.load(Ordering::Relaxed),
  //     TAKEN_FROM_RECYCLE_COUNT.load(Ordering::Relaxed)) }
}

