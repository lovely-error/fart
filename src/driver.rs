
use std::{sync::{atomic::{AtomicU16, Ordering, fence, AtomicU64, AtomicU32, AtomicU8, AtomicBool, }, mpsc::{Receiver, channel, Sender}}, mem::{size_of, MaybeUninit, forget,  transmute, align_of, transmute_copy, needs_drop, replace, ManuallyDrop}, ptr::{addr_of, null_mut, copy_nonoverlapping, addr_of_mut }, thread::{JoinHandle, self, park, Thread, spawn, current}, cell::UnsafeCell, alloc::{alloc, Layout}, marker::PhantomData, time::Duration,  collections::HashMap, os::fd::RawFd};

use core_affinity::CoreId;
use polling::{Poller, Source, Event};

use crate::{
  root_alloc::{RootAllocator, Block4KPtr},
  utils::{
    ptr_align_dist, with_scoped_consume, bitcopy,
    PageSource, offset_to_higher_multiple },
  cast,
  loopbuffer::{InlineLoopBuffer, LoopBufferTraverser}, array::Array, garbage
};

extern crate core_affinity;

pub struct SubRegionAllocator {
  page_provider: *mut dyn PageSource,
  current_page_start: *mut u8,
  allocation_tail: *mut u8,
  free_list: *mut u8
}

static mut DEALLOCATION_COUNT : AtomicU64 = AtomicU64::new(0);
static mut ALLOCATION_COUNT : AtomicU64 = AtomicU64::new(0);

impl SubRegionAllocator {
  pub fn new(
    page_provider: *mut dyn PageSource
  ) -> Self {
    let mut raw = garbage!(Self);
    raw.page_provider = page_provider;
    raw.free_list = null_mut();
    raw.current_page_start = null_mut();
    return raw;
  }
  pub(crate) fn give_page_for_recycle_impl(&mut self, Block4KPtr(ptr):Block4KPtr) { unsafe {
    *ptr.cast::<*mut u8>() = self.free_list;
    self.free_list = ptr;
  } }
  fn try_take_spare_page(&mut self) -> Option<Block4KPtr> { unsafe {
    if self.free_list == null_mut() { return None }
    let current = self.free_list;
    let next = *self.free_list.cast::<*mut u8>();
    self.free_list = next;
    return Some(Block4KPtr(current))
  } }
  fn set_new_page(&mut self) { unsafe {
    let new_page_ptr;
    let maybe_page = self.drain_spare_page();
    match maybe_page {
      Some(Block4KPtr(ptr)) => new_page_ptr = ptr,
      None => {
        let Block4KPtr(ptr) = (*self.page_provider).try_drain_page().unwrap_or_else(||{
          panic!("infailable page provider failed to give page")
        });
        new_page_ptr = ptr
      }
    }
    self.current_page_start = new_page_ptr;
    {
      let ptr = &mut *new_page_ptr.cast::<RegionMetadata>();
      ptr.ref_count = AtomicU16::new(0);
    };
    self.allocation_tail = new_page_ptr.add(size_of::<RegionMetadata>());
  } }
  #[track_caller]
  pub fn alloc_bytes(
    &mut self,
    byte_size: usize,
    alignment: usize
  ) -> OpaqueRegionItemRef { unsafe {
    ALLOCATION_COUNT.fetch_add(1, Ordering::Relaxed);

    assert!(byte_size != 0);
    let mut reserved_space = size_of::<RegionMetadata>();
    reserved_space += offset_to_higher_multiple(reserved_space as u64, alignment) as usize;
    assert!(
      byte_size <= 4096 - reserved_space,
      "too big allocation, ill fix it when need come");
    if self.current_page_start.is_null() {
      self.set_new_page()
    }
    loop {
      let mut ptr = self.allocation_tail;
      let off = ptr_align_dist(ptr, alignment);
      ptr = ptr.add(off as usize);
      let next_allocation_tail = ptr.add(byte_size);
      if next_allocation_tail as u64 >= (self.current_page_start as u64 + 4096) {
        self.set_new_page(); continue;
      }
      let _ = (*self.current_page_start.cast::<RegionMetadata>())
        .ref_count.fetch_add(1, Ordering::AcqRel);

      self.allocation_tail = next_allocation_tail;
      let dist = ptr as u64 - self.current_page_start as u64;
      assert!(dist <= u16::MAX as u64);

      return OpaqueRegionItemRef::new(self.current_page_start, dist as u16);
    }
  }; }
  #[track_caller]
  pub fn dispose<T: RegionPtrObject>(&mut self, object: T) { unsafe {
    DEALLOCATION_COUNT.fetch_add(1, Ordering::Relaxed);

    let (root,_) = object.destruct().get_components();
    let i = (&*root.cast::<RegionMetadata>()).ref_count.fetch_sub(1, Ordering::AcqRel);
    if i == 1 {
      self.give_page_for_recycle_impl(Block4KPtr(root.cast()));
    }
  } }
  fn drain_spare_page(&mut self) -> Option<Block4KPtr> { unsafe {
    if self.free_list == null_mut() { return None }
    let page = self.free_list;
    let page_after_current = *self.free_list.cast::<*mut u8>();
    self.free_list = page_after_current;
    return Some(Block4KPtr(page))
  } }
  pub fn alloc_object<T>(&mut self) -> UninitRegionPtr<T> {
    let opq = self.alloc_bytes(size_of::<T>(), align_of::<T>());
    return RegionItemRef(opq, PhantomData)
  }
  fn alloc_task_frame(
    &mut self,
    env_align: usize,
    env_size: usize,
    env_data: *const u8,
  ) -> RegionItemRef<TaskFrame> { unsafe {
    let header_size = size_of::<TaskFrame>() as *const u8;
    let offset_to_data = header_size.align_offset(env_align);
    let total_size = size_of::<TaskFrame>() + offset_to_data + env_size;

    let frame_allocation_limit = 4096 - size_of::<RegionMetadata>();
    if total_size >= frame_allocation_limit {
      panic!("FIXME?:Cant allocate this much for a task frame.")
    }
    let region_ref = self.alloc_bytes(total_size, align_of::<TaskFrame>());
    let frame_ptr = region_ref.deref();
    let frame_ref = frame_ptr.cast::<TaskFrame>();
    frame_ref.write(TaskFrame {
      parent_task: Supertask::None,
      subtask_count: AtomicU32::new(0),
      align_order: env_align.ilog2() as u8,
      secondary_data: ExcessData { uninit: () }
    });
    let data_ptr = (*frame_ref).raw_ptr_to_data();
    copy_nonoverlapping(env_data, data_ptr, env_size);

    return region_ref.bind_type()
  } }
}

pub trait RegionPtrObject {
  fn destruct(self) -> OpaqueRegionItemRef;
}

impl PageSource for SubRegionAllocator {
  fn try_drain_page(&mut self) -> Option<Block4KPtr> {
      if let k@Some(_) = self.drain_spare_page() {
        return k
      } else {
        unsafe { (&mut *self.page_provider).try_drain_page() }
      }
  }
}
impl PageSink for SubRegionAllocator {
  fn give_page_for_recycle(&mut self, page: Block4KPtr) {
    self.give_page_for_recycle_impl(page)
  }
}
impl PageManager for SubRegionAllocator {}

pub type UninitRegionPtr<T> = RegionItemRef<MaybeUninit<T>>;
pub struct RegionItemRef<T>(OpaqueRegionItemRef, PhantomData<T>);
impl <T> RegionItemRef<MaybeUninit<T>> {
  pub fn init(self, data: T) -> RegionItemRef<T> { unsafe {
    self.0.deref().cast::<T>().write(data);
    return transmute(self)
  } }
}
impl <T> RegionItemRef<T> {
  fn new_null() -> Self { Self(OpaqueRegionItemRef::new_null(), PhantomData) }
  fn is_null(&self) -> bool { self.0.is_null() }
  fn deref(&self) -> &T {
    unsafe { &*self.0.deref().cast::<T>() }
  }
  fn deref_mut(&self) -> &mut T {
    unsafe { &mut *self.0.deref().cast::<T>() }
  }
}
impl <T> RegionPtrObject for RegionItemRef<T> {
  fn destruct(self) -> OpaqueRegionItemRef {
    self.0
  }
}

pub struct OpaqueRegionItemRef(u64);
impl OpaqueRegionItemRef {
  pub fn new_null() -> Self {
    OpaqueRegionItemRef(0)
  }
  pub fn is_null(&self) -> bool {
    self.0 == 0
  }
  pub fn new(
    region_start_addr: *mut u8,
    byte_offset: u16,
  ) -> Self {
    let ptrint = (region_start_addr as u64) << 16;
    let mtded = ptrint + byte_offset as u64;
    return Self(mtded)
  }
  pub fn get_components(&self) -> (*mut (), u16) {
    let mtd = self.0 & (1u64 << 16) - 1;
    let ptr = (self.0 >> 16) as *mut ();
    return (ptr, mtd as u16);
  }
  pub fn deref(&self) -> *mut u8 {
    let (ptr, off) = self.get_components();
    let spot = unsafe { ptr.cast::<u8>().add(off as usize) };
    return spot
  }
  pub fn bind_type<T>(self) -> RegionItemRef<T> {
    RegionItemRef(self, PhantomData)
  }
}
impl RegionPtrObject for OpaqueRegionItemRef {
  fn destruct(self) -> OpaqueRegionItemRef {
    return self
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
  fn clone_ref(&self) -> Self {
    let meta = self.0.deref();
    meta.ref_count.fetch_add(1, Ordering::AcqRel);
    let copy = unsafe{bitcopy(self)};
    return copy
  }
}
// impl <T> Clone for Isolated<T> {
//   fn clone(&self) -> Self {
//     self.clone_ref()
//   }
// }
struct SyncedMtd {
  ref_count: AtomicU32,
  active_readers_count: AtomicU32,
  align_order: u8,
}
impl SyncedMtd {
  fn ptr_to_data(&self) -> *mut u8 { unsafe {
    let align = 1 << self.align_order;
    let ptr = transmute::<_, *mut u8>(self).add(size_of::<Self>());
    let ptr = ptr.add(ptr.align_offset(align));
    return ptr
  } }
  fn new_for(align: usize) -> Self {
    Self {
      ref_count: AtomicU32::new(1),
      active_readers_count: AtomicU32::new(0),
      align_order: align.checked_ilog2().unwrap() as u8,
    }
  }
}

struct RegionMetadata {
  ref_count: AtomicU16
}

#[test]
fn test_acks_work() { unsafe {
  let mut ralloc = RootAllocator::new();
  let mut sralloc = SubRegionAllocator::new(&mut ralloc);
  let mut boxes: [MaybeUninit<OpaqueRegionItemRef>; 64] = MaybeUninit::uninit().assume_init();
  let boxess = boxes.as_mut_ptr().cast::<OpaqueRegionItemRef>();
  for i in 0 ..64-1 {
    let v = sralloc.alloc_bytes(16, 64);
    let ptr = v.deref();
    *ptr.cast() = u16::MAX;
    boxess.add(i).write(v);
  }
  let above = sralloc.alloc_bytes(16, 64); // must cause page replace
  above.deref().cast::<u16>().write(u16::MAX);
  boxess.add(63).write(above);
  for i in 0 .. 64 {
    let item = boxess.add(i).read();
    let val = *item.deref().cast::<u16>();
    assert!(val == u16::MAX);
    sralloc.dispose(item);
  }
} }

struct IOPollingWorker {
  work_group: *mut WorkGroup,
  handle: Option<JoinHandle<()>>,
  out_port: Receiver<IOPollingCallbackData>,
  core_pin_index: CoreId,
  is_sleeping: AtomicBool,
  have_to_die: AtomicBool
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
    let outcome = self.is_sleeping.compare_exchange(
      true, false, Ordering::Relaxed, Ordering::Relaxed);
    match outcome {
      Ok(_) => {
        if let Some(handle) = &self.handle {
          handle.thread().unpark();
        } else {
          panic!("cant wakeup uninitialised io worker")
        }
      },
      Err(_) => (), // it is already awaken
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
      let outcome = this.is_sleeping.compare_exchange(
        false, true, Ordering::Relaxed, Ordering::Relaxed);
      match outcome {
        Ok(_) => {
          loop {
            park();
            if !this.is_sleeping.load(Ordering::Relaxed) { continue 'processing }
            if this.have_to_die.load(Ordering::Relaxed) { return }
          }
        },
        Err(_) => continue 'processing,
      }
    }
    for event in &gathered_events {
      let (task, fd) = pending_tasks.remove(&event.key).unwrap();
      poller.delete(fd).unwrap();
      batch_for_resume.push(task);
    }
    let no_resume_batch = batch_for_resume.is_empty();
    if !no_resume_batch {
      if let Some(free_worker) = (*this.work_group).worker_set.try_acquire_free_worker_mref() {
        if !free_worker.flags.was_started() { free_worker.start() }
        free_worker.with_synced_access(|worker| {
          let task_set = &mut (*worker.inner_context_ptr.assume_init()).workset;
          while let Some(task) = batch_for_resume.pop() {
            task_set.enque(task)
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
  fn inline_free_indicies(&self) -> &AtomicU64 {
    &unsafe { &*self.0.get() }.inline_free_indicies
  }
  fn total_worker_count(&self) -> u32 {
    unsafe { &*self.0.get() }.total_worker_count
  }
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
        let worker = w.ref_item_at_index(index as usize - 16).unwrap();
        return worker;
      };
      panic!()
    };
  }; }
  fn set_as_free(&self, index: u32) {
    let this = unsafe { &mut *self.0.get() };
    if index >= this.total_worker_count { panic!("invalid worker index") }

    let index_mask = 1u64 << index;
    let mask = !index_mask ;
    // we must see changes to indicies as immidiate thus acqrel
    let _ = this.inline_free_indicies.fetch_and(mask, Ordering::Relaxed);
  }
  // true, if already occupied
  fn set_as_occupied(&self, index: u32) -> bool {
    let this = unsafe { &mut *self.0.get() };
    if index >= this.total_worker_count { panic!("invalid index of worker") }

    let mask = 1u64 << index;
    // we mut see changes to indicies as immidiate or
    // some two wokers might end up aquiring third one and
    // that would be pretty bad
    let old = this.inline_free_indicies.fetch_or(mask, Ordering::Relaxed);
    let already_taken = old & mask != 0;
    return already_taken
  }
  fn try_acquire_free_worker_mref(&self) -> Option<&mut Worker> { unsafe {
    let this = &mut *self.0.get();
    let relevance_mask = u64::MAX << this.total_worker_count;
    let mut indicies = this.inline_free_indicies.load(Ordering::Relaxed);
    loop {
      if indicies | relevance_mask == u64::MAX {
        // nothign to grab in inlines
        if let Some(_) = this.outline_workers {
          todo!()
        }
        return None ;
      };
      let some_index = indicies.trailing_ones();
      let index_mask = 1u64 << some_index;
      indicies = this.inline_free_indicies.fetch_or(index_mask, Ordering::Relaxed);
      let did_acquire = indicies & index_mask == 0;
      if !did_acquire { continue; }

      let ptr = this.inline_workers.as_ptr().add(some_index as usize);
      let ptr = ptr.cast::<Worker>() as *mut _;
      let val = &mut *ptr;
      return Some(val)
    }
  } }
  fn all_workers_are_idle(&self) -> bool { unsafe {
    let this = &mut *self.0.get();
    let lower_are_idle = this.liveness_count.load(Ordering::Relaxed) == 0;
    if lower_are_idle {
      if let Some(_) = this.outline_free_indicies {
        todo!()
      }
    }
    return lower_are_idle
  } }
}

struct TaskSet<const LocalCacheCapacity: usize> {
  inline_tasks: InlineLoopBuffer<LocalCacheCapacity, Task>,
  outline_tasks: Array<Task>,
}
impl <const LocalCacheCapacity: usize> TaskSet<LocalCacheCapacity> {
  fn item_count(&self) -> usize {
    let inline = self.inline_tasks.item_count();
    let outline = self.outline_tasks.item_count();
    return inline + outline;
  }
  fn enque(&mut self, new_item: Task) {
    let clone = unsafe { addr_of!(new_item).read() };
    let did_push = self.inline_tasks.push_to_tail(new_item);
    if !(did_push) {
      self.outline_tasks.push(clone)
    } else {
      forget(clone)
    }
  }
  fn deque(&mut self) -> Option<Task> {
    let task = self.inline_tasks.pop_from_head();
    if let None = task {
      let task = self.outline_tasks.pop();
      return task;
    }
    return task
  }
}


struct WorkerFlags(AtomicU8);
impl WorkerFlags {
  fn new() -> Self {
    Self(AtomicU8::new(0))
  }
  const TERMINATION_BIT: u8 = 1 << 0;
  fn mark_for_termination(&self) {
    let _ = self.0.fetch_or(Self::TERMINATION_BIT, Ordering::SeqCst);
  }
  fn is_marked_for_termination(&self) -> bool {
    let flags = self.0.load(Ordering::SeqCst);
    return flags & Self::TERMINATION_BIT != 0;
  }
  const SUSPEND_BIT: u8 = 1 << 1;
  fn mark_for_suspend(&self) {
    let _ = self.0.fetch_or(Self::SUSPEND_BIT, Ordering::Relaxed);
  }
  fn unmark_for_suspend(&self) {
    let _ = self.0.fetch_and(!Self::SUSPEND_BIT, Ordering::Relaxed);
  }
  fn is_marked_for_suspend(&self) -> bool {
    let flags = self.0.load(Ordering::Relaxed);
    return flags & Self::SUSPEND_BIT != 0
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
  fn mark_as_started(&self) {
    let _ = self.0.fetch_or(Self::FIRST_INIT_BIT, Ordering::Relaxed);
  }
  fn was_started(&self) -> bool {
    let flags = self.0.load(Ordering::Relaxed);
    return flags & Self::FIRST_INIT_BIT != 0;
  }
  const WORK_SUBMITED_BIT: u8 = 1 << 4;
  fn mark_first_work_as_submited(&self) {
    let _ = self.0.fetch_or(Self::WORK_SUBMITED_BIT, Ordering::Relaxed);
  }
  fn unmark_work_as_submited(&self) {
    let _ = self.0.fetch_and(!Self::WORK_SUBMITED_BIT, Ordering::Relaxed);
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
  inner_context_ptr: MaybeUninit<*mut CommonWorkerInnerContext>,
  index: u32,
  flags: WorkerFlags,
  core_pin_id: core_affinity::CoreId,
  io_tasks_sink: Sender<IOPollingCallbackData>
}
impl Worker {
  // false if already occupied
  fn mark_as_occupied(&self) -> bool { unsafe {
    (*self.work_group).worker_set.set_as_occupied(self.index)
  } }
  fn mark_as_free(&self) {
    unsafe{(*self.work_group).worker_set.set_as_free(self.index)}
  }
  fn wakeup(&self) {
    if let Some(thread) = &self.runner_handle {
      thread.thread().unpark();
    };
  }
  fn start(&mut self) { unsafe {
    let init_bit = WorkerFlags::FIRST_INIT_BIT;
    let prior = self.flags.0.fetch_or(init_bit, Ordering::AcqRel);
    if prior & init_bit != 0 {
      panic!("attempt to reinit worker")
    }
    let _ = self.mark_as_occupied();
    if let None = self.runner_handle {
      let copy = transmute_copy::<_, u64>(&self);
      let thread = thread::spawn(move ||{
        let ptr = transmute::<_, &mut Worker>(copy);
        worker_processing_routine(ptr);
      });
      self.runner_handle = Some(thread);
    }
  } }
  fn terminate(&mut self) {
    with_scoped_consume(&mut self.runner_handle, |g| {
      let v = g.consume();
      if let Some(thread) = v {
        let () = thread.join().unwrap();
        g.recover_with(None);
      } else {
        g.recover_with(v)
      };
    });
  }
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

// this thing is created with intention to
// metigate the situation when local objects contain
// too many stale pages. We ask those objects to give away pages
// they dont use and put them to use somewhere else.
struct PageRerouter<const Capacity:usize> {
  subscribed_donors: InlineLoopBuffer<Capacity, *mut dyn PageSource>,
  ralloc: *mut RootAllocator
}
impl <const Capacity:usize> PageRerouter<Capacity> {
  fn new(ralloc: *mut RootAllocator) -> Self {
    Self { subscribed_donors: InlineLoopBuffer::new(), ralloc }
  }
  fn register(&mut self, new_donor: *mut dyn PageSource) {
    let ok = self.subscribed_donors.push_to_tail(new_donor);
    assert!(ok);
  }
  fn get_page(&mut self) -> Block4KPtr { unsafe {
    let mut iter = LoopBufferTraverser::new(&self.subscribed_donors);
    loop {
      let maybe_donor = iter.next();
      if let Some(donor) = maybe_donor {
        let maybe_page = (&mut **donor).try_drain_page();
        if let Some(page) = maybe_page {
          return page
        }
      } else {
        let page = (&mut *self.ralloc).get_block();
        return page
      };
    }
  }; }
}
impl <const Capacity:usize> PageSource for PageRerouter<Capacity> {
  fn try_drain_page(&mut self) -> Option<Block4KPtr> {
      Some(self.get_page())
  }
}


type CommonWorkerInnerContext = WorkerInnerContext<4, TASK_CACHE_SIZE>;
struct WorkerInnerContext<const S0:usize, const S1:usize> {
  page_router: PageRerouter<S0>,
  allocator: SubRegionAllocator,
  workset: TaskSet<S1>,
}

const TASK_CACHE_SIZE:usize = 16;

fn worker_processing_routine(worker: &mut Worker) { unsafe {
  (*(*worker.work_group).worker_set.0.get()).liveness_count.fetch_add(1, Ordering::AcqRel);
  let ok = core_affinity::set_for_current(worker.core_pin_id);
  assert!(ok, "failed to pin worker {} to core {:?}", worker.index, worker.core_pin_id);
  let ralloc = addr_of_mut!((&mut *worker.work_group).ralloc);
  let mut inner_context = {
    let mut ctx: CommonWorkerInnerContext = garbage!();
    let router_ptr = addr_of_mut!(ctx.page_router);
    router_ptr.write(PageRerouter::<4>::new(ralloc));
    addr_of_mut!(ctx.allocator).write(SubRegionAllocator::new(router_ptr));
    addr_of_mut!(ctx.workset).write(TaskSet::<TASK_CACHE_SIZE>{
      inline_tasks:InlineLoopBuffer::new(),
      outline_tasks: Array::new(router_ptr)
    });
    ctx.page_router.register(&mut ctx.workset.outline_tasks);
    ctx
  };
  worker.inner_context_ptr.write(addr_of_mut!(inner_context));
  fence(Ordering::Release); // publish context init to the consumer
  worker.flags.mark_as_initialised();

  while !worker.flags.is_first_work_submited() {}
  fence(Ordering::Acquire);

  let workset_ = addr_of_mut!(inner_context.workset);
  let task_context = TaskContext::new(&mut inner_context);
  let task_context_ref = &mut *task_context.0.get();
  let mut immidiate_state = ImmidiateState {
    spawned_subtask_count: 0,
    parked_task: RegionItemRef::new_null(),
    current_task: garbage!()
  };
  task_context_ref.immidiate_state = addr_of_mut!(immidiate_state);

  'quantum:loop {
    if let Some(task) = (*workset_).deque() {
      immidiate_state.current_task = task;
    } else {
      let rc = &(*(*worker.work_group).worker_set.0.get()).liveness_count;
      let last_alive = rc.fetch_sub(1, Ordering::AcqRel) == 1;
      if last_alive {
        let wg = &mut (*worker.work_group).worker_set;
        let io_worker = &mut (*wg.0.get()).io_thread;
        io_worker.have_to_die.store(true, Ordering::Relaxed);
        io_worker.wakeup();
        let io_handle = replace(&mut io_worker.handle, None);
        if let Some(handle) = io_handle {
          handle.join().unwrap();
        }
        for ix in 0 .. wg.total_worker_count() {
          if worker.index == ix { continue; }
          let other_worker = wg.mref_worker_at_index(ix);
          if other_worker.flags.was_started() {
            other_worker.flags.mark_for_termination();
            other_worker.wakeup();
          }
        }
        return
      }
      let selfkill = suspend(&worker);
      if selfkill {
        return; // goodbye sweet prince
      }
      rc.fetch_add(1, Ordering::AcqRel);
      continue;
    }

    let mut continuation = immidiate_state.current_task.load_continuation();
    'fast_path: loop {
      match continuation.continuation {
        ContinuationRepr::Done => {
          let current_task_frame = immidiate_state.current_task.task_frame_ptr.deref_mut();
          match &current_task_frame.parent_task {
            Supertask::Thread(thread, flag) => {
              (**flag).store(true, Ordering::Relaxed);
              thread.unpark();
            },
            Supertask::Task(task) => {
              let parent_task = task.deref();
              let parent_frame = parent_task.task_frame_ptr.deref();
              let remaining_subtasks_count =
                parent_frame.subtask_count.fetch_sub(1, Ordering::Relaxed);
              let last_child = remaining_subtasks_count == 1;
              if last_child {
                fence(Ordering::Acquire);
                let next_task = bitcopy(parent_task);
                // dispose space taken for parking the parrent task handle
                inner_context.allocator.dispose(bitcopy(task));
                // dispose current task frame
                inner_context.allocator.dispose(immidiate_state.current_task.task_frame_ptr);
                continuation = next_task.load_continuation();
                immidiate_state.current_task = next_task;
                continue 'fast_path;
              }
            },
            Supertask::None => (),
          }
          inner_context.allocator.dispose(immidiate_state.current_task.task_frame_ptr);
          continue 'quantum;
        },
        ContinuationRepr::Then(thunk) => {
          let next = thunk(&task_context);
          let produced_subtasks = immidiate_state.spawned_subtask_count != 0;
          if produced_subtasks {
            immidiate_state.current_task.store_continuation(next);
            fence(Ordering::Release);
            let frame = immidiate_state.current_task.task_frame_ptr.deref_mut();
            frame.subtask_count = AtomicU32::new(immidiate_state.spawned_subtask_count as u32);
            *immidiate_state.parked_task.deref_mut() = immidiate_state.current_task;
            task_context.clear_dirty_state();
            schedule_work(worker, workset_);
            continue 'quantum;
          } else {
            continuation = next;
            continue 'fast_path
          }
        },
        ContinuationRepr::AwaitIO(fd, r, w, next) => {
          immidiate_state.current_task.action.set_fun_ptr(next);
          immidiate_state.current_task.action.mref_flags().set_thunk_type(ThunkType::Then);
          let item = IOPollingCallbackData {
            task_to_resume: immidiate_state.current_task,
            target: fd, readable: r, writeable: w
          };
          worker.io_tasks_sink.send(item).unwrap();
          (*(*worker.work_group).worker_set.0.get()).io_thread.wakeup();
          task_context.clear_dirty_state();
          continue 'quantum;
        },
        ContinuationRepr::Sync(reg_ref, asked_mut, sync_thunk) => {
          let mtd@SyncedMtd {
            ref_count, active_readers_count, ..
          } = reg_ref.deref();
          if asked_mut { // task wants to mustate the iso
            // lets try set a mark that there is an interest to mutate this isolate
            let val = active_readers_count.fetch_or(1 << 31, Ordering::Relaxed);
            let we_got_it = val & (1 << 31) == 0;
            let reader_count = val & ((1 << 31) - 1);
            if we_got_it {
              if reader_count == 0 {
                // nobody reads this and this task have locked it,
                // it is safe to mutate it
                fence(Ordering::Acquire); // syncs on writer
                let data = mtd.ptr_to_data();
                let next = sync_thunk(data.cast(), &task_context);
                let produced_subtasks = immidiate_state.spawned_subtask_count != 0;
                if produced_subtasks {
                  immidiate_state.current_task.store_continuation(next);
                  fence(Ordering::Release);
                  let frame = immidiate_state.current_task.task_frame_ptr.deref_mut();
                  frame.subtask_count = AtomicU32::new(immidiate_state.spawned_subtask_count as u32);
                  *immidiate_state.parked_task.deref_mut() = immidiate_state.current_task;
                  task_context.clear_dirty_state();
                  schedule_work(worker, workset_);
                  continue 'quantum;
                }
                active_readers_count.fetch_and(!(1 << 31), Ordering::Release);
                let rc = ref_count.fetch_sub(1, Ordering::AcqRel);
                if rc == 1 {
                  inner_context.allocator.dispose(reg_ref);
                }
                continuation = next;
                continue 'fast_path;
              }
            }
            let con = Continuation {
              continuation: ContinuationRepr::Sync(reg_ref, asked_mut, sync_thunk) };
            immidiate_state.current_task.store_continuation(con);
            inner_context.workset.outline_tasks.push(immidiate_state.current_task);
            continue 'quantum
          } else { // task wants to read the iso
            let val = active_readers_count.fetch_add(1, Ordering::Relaxed);
            let available_for_reads = val & (1 << 31) == 0;
            if available_for_reads {
              fence(Ordering::Acquire); // syncs on writer
              let data = mtd.ptr_to_data();
              let next = sync_thunk(data.cast(), &task_context);
              let produced_subtasks = immidiate_state.spawned_subtask_count != 0;
              if produced_subtasks {
                immidiate_state.current_task.store_continuation(next);
                fence(Ordering::Release);
                let frame = immidiate_state.current_task.task_frame_ptr.deref_mut();
                frame.subtask_count = AtomicU32::new(immidiate_state.spawned_subtask_count as u32);
                *immidiate_state.parked_task.deref_mut() = immidiate_state.current_task;
                task_context.clear_dirty_state();
                schedule_work(worker, workset_);
                continue 'quantum;
              }
              active_readers_count.fetch_sub(1, Ordering::Release);
              let rc = ref_count.fetch_sub(1, Ordering::AcqRel);
              if rc == 1 {
                inner_context.allocator.dispose(reg_ref);
              }
              continuation = next;
              continue 'fast_path;
            } else {
              // we have to wait until it is available for reads
              let con = Continuation { // rust made me do this :(
                continuation: ContinuationRepr::Sync(reg_ref, asked_mut, sync_thunk) };
              immidiate_state.current_task.store_continuation(con);
              inner_context.workset.outline_tasks.push(immidiate_state.current_task);
              continue 'quantum
            }
          }
        },
      }
    }
  }
} }

fn suspend(worker: &Worker) -> bool {
  worker.mark_as_free(); // other worker looking for available workforce will untoggle this
  let self_kill = loop {
    if worker.flags.is_marked_for_termination() {
      break true
    };
    if worker.flags.has_transaction_began() {
      while !worker.flags.has_trunsaction_ended() {}
      fence(Ordering::Acquire);
      worker.flags.clear_transaction_bits();
      break false;
    }
    park();
  };
  return self_kill
}

fn schedule_work<const C:usize>(
  worker: *mut Worker, workset: *mut TaskSet<C>
) { unsafe {
  let workset = &mut *workset;
  let worker_set = &mut(*(*worker).work_group).worker_set;
  // todo: use task weight metric
  loop {
    let local_item_count = workset.item_count();
    let have_too_many_tasks = local_item_count > TASK_CACHE_SIZE;
    if have_too_many_tasks {
      let maybe_free_worker = worker_set.try_acquire_free_worker_mref();
      match maybe_free_worker {
        Some(subordinate_worker) => {
          if !subordinate_worker.flags.was_started() {
            subordinate_worker.start()
          }
          subordinate_worker.with_synced_access(|subordinate_worker|{
            let src = &mut(&mut *((&mut *worker).inner_context_ptr).assume_init_read()).workset;
            let dest = &mut (*subordinate_worker.inner_context_ptr.assume_init()).workset;
            // todo: make transfers fast
            let mut task_limit = 0;
            loop {
              if let Some(task) = src.deque() {
                dest.enque(task);
                task_limit += 1;
                if task_limit == TASK_CACHE_SIZE { return }
              } else {
                return
              }
            }
          });
          continue;
        },
        None => {
          return
        }
      }
    } else {
      return
    }
  }
} }

pub struct Arc<T> { ref_count:AtomicU64, value:T }
pub struct ArcBox<T>(OpaqueRegionItemRef, PhantomData<T>);
impl <T>ArcBox<T> {
  fn as_mut_ptr(&mut self) -> *mut T { unsafe {
    let val = &mut *self.0.deref().cast::<Arc<T>>();
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
    let val = &*self.0.deref().cast::<Arc<T>>();
    return &val.value
  } }
}
pub struct Boxed<T>(OpaqueRegionItemRef, PhantomData<T>);
impl <T> Boxed<T> {
  fn as_mut_ptr(&mut self) -> *mut T { unsafe {
    let val = &mut *self.0.deref().cast::<Arc<T>>();
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
    let val = &*self.0.deref().cast::<Arc<T>>();
    return &val.value
  } }
}

struct ImmidiateState {
  current_task: Task,
  spawned_subtask_count: u32,
  parked_task: RegionItemRef<Task>,
}
pub struct TaskContext(UnsafeCell<TaskContextInternals>);
struct TaskContextInternals {
  immidiate_state: *mut ImmidiateState,
  worker_inner_context_ref: *mut CommonWorkerInnerContext,
}
pub trait PageSink {
  fn give_page_for_recycle(&mut self, page: Block4KPtr);
}
pub trait PageManager: PageSource + PageSink {}
impl TaskContext {
  fn new(
    worker_inner_context: *mut CommonWorkerInnerContext,
  ) -> Self {
    TaskContext(UnsafeCell::new(TaskContextInternals {
      immidiate_state: null_mut(),
      worker_inner_context_ref: worker_inner_context,
    }))
  }
  pub fn get_page_provider(&self) -> &mut dyn PageManager { unsafe {
    let this = &mut *self.0.get();
    &mut (*this.worker_inner_context_ref).allocator
  } }
  pub fn spawn_synced_data<T:Sync>(&self, data: T) -> Isolated<T> {
    let this = unsafe { &mut *self.0.get() };
    let region = unsafe {
      (*this.worker_inner_context_ref).allocator.alloc_bytes(
        size_of::<(SyncedMtd, T)>(), align_of::<(SyncedMtd, T)>()) };
    let (mtd, data_) = unsafe{&mut *region.deref().cast::<(SyncedMtd, T)>()};
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
      unsafe{(*(*self.0.get()).worker_inner_context_ref).allocator.dispose(data.0)};
    }
  }
  pub fn acccess_frame_as_raw(&self) -> *mut () { unsafe {
    let this = &mut *self.0.get();
    let task = &mut (*this.immidiate_state).current_task;
    let data_offset = task.task_frame_ptr.deref_mut().raw_ptr_to_data();
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
      size_of::<T>(), align_of::<T>());
    let loc = region_ref.deref();
    loc.cast::<T>().write(data);
    return Boxed(region_ref, PhantomData)
  } }
  pub fn dispose_basic_box<T>(&self, some_box: Boxed<T>) { unsafe {
    let this = &mut *self.0.get();
    (*this.worker_inner_context_ref).allocator.dispose(some_box.0)
  } }
  pub fn spawn_rc_box<T>(&self, data:T) -> ArcBox<T> { unsafe {
    assert!(needs_drop::<T>(), "value must provide a destructor");
    let this = &mut *self.0.get();
    let region_ref = (*this.worker_inner_context_ref).allocator.alloc_bytes(
      size_of::<Arc<T>>(), align_of::<Arc<T>>());
    let loc = region_ref.deref();
    let box_ = loc.cast::<Arc<T>>();
    (*box_).ref_count = AtomicU64::new(1);
    addr_of_mut!((*box_).value).write(data);
    return ArcBox(region_ref, PhantomData)
  }; }
  pub fn dispose_rc_box<T>(&self, some_box: ArcBox<T>) { unsafe {
    let val = &*some_box.0.deref().cast::<Arc<T>>();
    let rc = val.ref_count.fetch_sub(1, Ordering::AcqRel);
    if rc == 1 {
      let this = &mut *self.0.get();
      (*this.worker_inner_context_ref).allocator.dispose(some_box.0)
    }
  } }

  // parents never get ahead of their children in the execution timeline.
  // subtasks are never parentless
  pub fn spawn_subtask<T: Send>(&self, env: T, thunk: Thunk) {
    self.spawn_task_common_impl(
      addr_of!(env).cast::<u8>(),
      size_of::<T>(), align_of::<T>(), thunk, false);
    forget(env)
  }
  // parent does not depend on this subtask
  pub fn spawn_detached_task<T:Send>(&self, env: T, thunk: Thunk) {
    self.spawn_task_common_impl(
      addr_of!(env).cast::<u8>(),
      size_of::<T>(), align_of::<T>(), thunk, true);
    forget(env)
  }
  #[inline(never)]
  fn spawn_task_common_impl(
    &self,
    env_data:*const u8, env_size:usize, env_align:usize,
    thunk: Thunk, detached: bool
  ) { unsafe {
    let this = &mut *self.0.get();
    let immidiate_state_ref = &mut *this.immidiate_state;

    if !detached {
      self.idempotently_aquire_parking_lot_for_parent_task();
      immidiate_state_ref.spawned_subtask_count += 1;
    }

    let mut frame_ref = (*this.worker_inner_context_ref).allocator.alloc_task_frame(
      env_align, env_size, env_data);
    if !detached {
      frame_ref.deref_mut().parent_task = if immidiate_state_ref.parked_task.is_null() {
        Supertask::None
      } else {
        Supertask::Task(bitcopy(&immidiate_state_ref.parked_task))
      };
    }
    let subtask = Task {
      action:Action::new(thunk),
      task_frame_ptr: frame_ref
    };
    let task_set = &mut (*this.worker_inner_context_ref).workset;
    task_set.enque(subtask);
  }; }
  fn clear_dirty_state(&self) {
    let this = unsafe { &mut *self.0.get() };
    let imm_ctx = unsafe{&mut *this.immidiate_state};
    imm_ctx.spawned_subtask_count = 0;
    imm_ctx.parked_task = RegionItemRef::new_null();
  }
  fn idempotently_aquire_parking_lot_for_parent_task(&self) { unsafe {
    let this = &mut *self.0.get() ;
    let imm_ctx = &mut *this.immidiate_state;
    if imm_ctx.parked_task.is_null() {
      let srallocator = &mut (*this.worker_inner_context_ref).allocator;
      let slot = srallocator.alloc_bytes(size_of::<Task>(), align_of::<Task>());
      imm_ctx.parked_task = RegionItemRef(slot, PhantomData);
    }
  } }

}

#[repr(u8)] #[derive(Debug, Clone, Copy)]
enum ThunkType {
  Sync, Then, Done, Await
}
struct TaskFlags([u8;2]);
impl TaskFlags {
  fn new() -> Self {
    Self([0;2])
  }
  fn set_thunk_type(&mut self, thunk_type: ThunkType) {
    assert!(thunk_type as u8 <= 0b11);
    self.0[0] = (self.0[0] & !(0b11 << 2)) | ((thunk_type as u8) << 2);
  }
  fn get_thunk_type(&self) -> ThunkType {
    let bitval = (self.0[0] & (0b11 << 2)) >> 2;
    unsafe { transmute(bitval) }
  }
  fn mark_as_dead(&mut self) {
    self.0[0] |= 1 << 1
  }
  fn is_dead(&self) -> bool {
    self.0[0] & (1 << 1) != 0
  }
}

pub struct Continuation {
  continuation: ContinuationRepr
}
enum ContinuationRepr {
  Done,
  Then(Thunk),
  AwaitIO(RawFd, bool, bool, Thunk),
  Sync(RegionItemRef<SyncedMtd>, bool, fn (*mut (), &TaskContext) -> Continuation)
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
  pub fn sync_ref<T>(
    object: Isolated<T>,
    continuation: fn (&T, &TaskContext) -> Self
  ) -> Self {
    let Isolated(reg_ref, _) = object;
    let continuation = unsafe { transmute(continuation) };
    return Self { continuation: ContinuationRepr::Sync(reg_ref, false, continuation) }
  }
  pub fn sync_mut<T>(
    object: Isolated<T>,
    continuation: fn (&mut T, &TaskContext) -> Self
  ) -> Self {
    let Isolated(reg_ref, _) = object;
    let continuation = unsafe { transmute(continuation) };
    return Self { continuation: ContinuationRepr::Sync(reg_ref, true, continuation) }
  }
}
type Thunk = fn (&TaskContext) -> Continuation;
struct Action(UnsafeCell<ActionInternals>);
#[repr(align(8))]
struct ActionInternals([u8;6],TaskFlags);
impl ActionInternals {
  fn new() -> Self {
    return Self([0;6], TaskFlags::new())
  }
}
impl Action {
  fn inject_raw_ptr(&mut self, fun_ptr: *mut ()) { unsafe {
    let ptr = (*self.0.get()).0.as_mut_ptr().cast::<u64>();
    *ptr = fun_ptr as u64 | (*ptr & ((1u64 << 16) - 1) << 48);
  } }
  fn project_raw_ptr(&self) -> *mut () {
    let src = unsafe { &*self.0.get() }.0.as_ptr().cast::<u64>();
    let ptr = unsafe { *src } & ((1 << 48) - 1) ;
    return ptr as _;
  }
  fn new(fun_ptr: Thunk) -> Self {
    let mut new = Self(UnsafeCell::new(ActionInternals::new()));
    new.mref_flags().set_thunk_type(ThunkType::Then);
    new.set_fun_ptr(fun_ptr);
    return new
  }
  fn project_thunk_ptr(&self) -> Thunk {
    unsafe {transmute(self.project_raw_ptr())}
  }
  fn mref_flags(&self) -> &mut TaskFlags {
    unsafe { &mut (*self.0.get()).1 }
  }
  fn set_fun_ptr(&mut self, fun_ptr: Thunk) {
    self.inject_raw_ptr(fun_ptr as _)
  }
  fn project_sync_ptr(&self) -> fn(*mut(),&TaskContext) -> Continuation {
    let ptr = self.project_raw_ptr();
    unsafe { transmute(ptr) }
  }
  fn set_sync_ptr(&mut self, sync_ptr: fn(*mut (), &TaskContext) -> Continuation) {
    self.inject_raw_ptr(sync_ptr as _);
  }
}

fn example(_: &TaskContext) -> Continuation { Continuation::then(example) }
#[test]
fn action_is_not_bullshit() {
  let a = Action::new(example);
  let fptr = a.project_thunk_ptr();
  assert!(fptr as u64 == example as u64)
}

enum Supertask {
  Thread(Thread, *const AtomicBool),
  Task(RegionItemRef<Task>),
  None
}
union ExcessData {
  sync: ManuallyDrop<(RegionItemRef<SyncedMtd>, bool)>,
  io: ManuallyDrop<(RawFd, bool, bool)>,
  uninit: ()
}
struct TaskFrame {
  parent_task: Supertask,
  subtask_count: AtomicU32,
  secondary_data: ExcessData,
  align_order: u8
}
impl TaskFrame {
  fn raw_ptr_to_data(&mut self) -> *mut u8 { unsafe {
    let offset = 1 << self.align_order;
    let ptr = addr_of_mut!(*self).add(1).cast::<u8>();
    let ptr = ptr.add(ptr.align_offset(offset));
    return ptr
  } }
}
struct Task {
  action: Action,
  task_frame_ptr: RegionItemRef<TaskFrame>
}
impl Task {
  fn store_continuation(&mut self, next: Continuation) {
    match next.continuation {
      ContinuationRepr::Done => {
        self.action.mref_flags().set_thunk_type(ThunkType::Done)
      },
      ContinuationRepr::Then(item) => {
        self.action.set_fun_ptr(item);
        self.action.mref_flags().set_thunk_type(ThunkType::Then);
      },
      ContinuationRepr::AwaitIO(fd, r, w, cont) => {
        self.action.set_fun_ptr(cont);
        self.action.mref_flags().set_thunk_type(ThunkType::Await);
        let frame = self.task_frame_ptr.deref_mut();
        frame.secondary_data = ExcessData { io: ManuallyDrop::new((fd, r, w)) };
      },
      ContinuationRepr::Sync(obj, asked_mut, thunk) => {
        self.action.set_sync_ptr(thunk);
        self.action.mref_flags().set_thunk_type(ThunkType::Sync);
        let frame =  self.task_frame_ptr.deref_mut();
        frame.secondary_data = ExcessData { sync: ManuallyDrop::new((obj, asked_mut)) };
      },
    }
  }
  fn load_continuation(&self) -> Continuation {
    match self.action.mref_flags().get_thunk_type() {
      ThunkType::Sync => {
        let ptr = self.action.project_sync_ptr();
        let frame = self.task_frame_ptr.deref();
        let (obj, asked) = unsafe{ManuallyDrop::into_inner(bitcopy(&frame.secondary_data.sync))};
        Continuation { continuation: ContinuationRepr::Sync(obj, asked, ptr) }
      },
      ThunkType::Then => {
        let ptr = self.action.project_thunk_ptr();
        Continuation { continuation: ContinuationRepr::Then(ptr) }
      },
      ThunkType::Done => {
        return Continuation::done()
      },
      ThunkType::Await => {
        let ptr = self.action.project_thunk_ptr();
        let frame = self.task_frame_ptr.deref();
        let (fd, r, w) = unsafe{ManuallyDrop::into_inner(frame.secondary_data.io)};
        Continuation {continuation:ContinuationRepr::AwaitIO(fd, r, w, ptr)}
      }
    }
  }
}
pub struct WorkGroup {
  ralloc: RootAllocator,
  worker_set: WorkerSet,
}
impl WorkGroup {
  pub fn new() -> WorkGroupRef { unsafe {
    let core_ids = core_affinity::get_core_ids().unwrap_or_else(||{
      panic!("cannot retrieve core indicies")
    });
    let total_core_count = core_ids.len();
    if total_core_count > 64 {
      panic!("fixme: write impls for some stuff here and there")
    }
    let (worker_count, io_core_pin) = {
      let last = core_ids.last().unwrap().clone();
      if total_core_count == 1 { (total_core_count, last) }
      else {
        let count = total_core_count - 1;
        (count, last)
      }
    };
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
          core_pin_index: io_core_pin,
          is_sleeping: AtomicBool::new(false),
          have_to_die: AtomicBool::new(false)
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
    let work_set = &self.worker_set;
    let io_worker = &mut (*work_set.0.get()).io_thread;
    io_worker.have_to_die.store(true, Ordering::Relaxed);
    io_worker.wakeup();
    let total_worker_count = work_set.total_worker_count();
    for ix in 0 .. total_worker_count {
      let wref = work_set.mref_worker_at_index(ix);
      wref.flags.mark_for_termination();
      wref.wakeup();
      wref.terminate();
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
    if !worker.flags.was_started() {
      worker.start();
    }
    let can_resume = AtomicBool::new(false);
    let requesting_thread = current();
    worker.with_synced_access(|worker|{
      let inner_ctx = &mut *worker.inner_context_ptr.assume_init();
      let frame_ = inner_ctx.allocator.alloc_task_frame(
        align_of::<Env>(), size_of::<Env>(), addr_of!(capture).cast());
      let frame = frame_.deref_mut();
      frame.parent_task = Supertask::Thread(requesting_thread, addr_of!(can_resume));
      let task = Task { action: Action::new(operation), task_frame_ptr: frame_ };
      inner_ctx.workset.enque(task);
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
    if !worker.flags.was_started() {
      worker.start();
    }
    worker.with_synced_access(|worker|{
      let inner_ctx = &mut *worker.inner_context_ptr.assume_init();
      let frame_ = inner_ctx.allocator.alloc_task_frame(
        align_of::<Env>(), size_of::<Env>(), addr_of!(capture).cast());
      let frame = frame_.deref_mut();
      frame.parent_task = Supertask::None;
      let task = Task { action: Action::new(operation), task_frame_ptr: frame_ };
      inner_ctx.workset.enque(task);
    });
    forget(capture);
    return;
  } }
  pub fn clone_ref(&self) -> Self { unsafe {
    (*(*self.0).worker_set.0.get()).liveness_count.fetch_add(1, Ordering::AcqRel);
    return bitcopy(self)
  } }
}
impl Drop for WorkGroupRef {
  fn drop(&mut self) { unsafe {
    let count = (*(*self.0).worker_set.0.get()).liveness_count.fetch_sub(1, Ordering::AcqRel);
    if count == 1 {
      (*self.0).destroy()
    }
  } }
}


#[test]
fn test_trivial_tasking() {
  static mut evil_formula : &str = "";
  fn single_print(ctx: &TaskContext) -> Continuation {
    unsafe { evil_formula = "CH3O2"; }
    return Continuation::done();
  }
  let work_group = WorkGroup::new();
  work_group.submit_and_await((), single_print);
  assert!("CH3O2" == unsafe { evil_formula });
}


#[test]
fn one_shild_one_parent() {

  static mut name: &str = "";
  fn parent(ctx: &TaskContext) -> Continuation {
    ctx.spawn_subtask((), child);
    return Continuation::done()
  }
  fn child(ctx: &TaskContext) -> Continuation {
    unsafe { name = "I am Jason";};
    return Continuation::done();
  }

  let work_group = WorkGroup::new();
  work_group.submit_and_await((), parent);

  assert!("I am Jason" == unsafe {name});
}

#[test]
fn child_child_check_dead() {
  const Limit:u64 = 4000;
  struct ParentData { counter: AtomicU64, }
  fn parent(ctx: &TaskContext) -> Continuation {
    let frame = ctx.access_frame_as_init::<ParentData>();
    for _ in 0 .. Limit {
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

    assert!(val == Limit);

    return Continuation::done()
  }

  let frame = ParentData { counter: AtomicU64::new(0) };
  let work_group = WorkGroup::new();
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


#[test]
fn ref_sync() {
  const LIMIT : usize = 1;
  struct Ctx {
    sync_obj: Option<Isolated<Vec<u32>>>
  }
  fn begin(ctx: &TaskContext) -> Continuation {
    let frame = ctx.access_frame_as_init::<Ctx>();
    let smth = ctx.spawn_synced_data(Vec::new());
    frame.sync_obj = Some(smth);
    for _ in 0 .. LIMIT {
      let smth_clone = frame.sync_obj.as_ref().unwrap().clone_ref();
      ctx.spawn_subtask(smth_clone, |ctx|{
        let frame = ctx.access_frame_as_init::<Isolated<Vec<u32>>>();
        return Continuation::sync_mut(frame.clone_ref(), |val, ctx| {
          val.push(0);
          let frame = ctx.access_frame_as_init::<Isolated<Vec<u32>>>();
          ctx.dispose_synced_data(unsafe { bitcopy(frame) });
          return Continuation::done();
        });
      });
    }
    return Continuation::then(sync_on_vec);
  }
  fn sync_on_vec(ctx: &TaskContext) -> Continuation {
    let frame = ctx.access_frame_as_init::<Ctx>();
    let obj = frame.sync_obj.as_ref().unwrap().clone_ref();
    return Continuation::sync_ref(obj, |val, _| {
      let len = val.len();
      if len == LIMIT { return Continuation::then(end) }
      return Continuation::then(sync_on_vec);
    })
  }
  fn end(ctx: &TaskContext) -> Continuation {
    let frame = ctx.access_frame_as_init::<Ctx>();
    let obj = frame.sync_obj.as_ref().unwrap().clone_ref();
    return Continuation::sync_ref(obj, |val, ctx|{
      println!("{:#?}", val);
      let frame = ctx.access_frame_as_init::<Ctx>();
      let vec = frame.sync_obj.take().unwrap();
      ctx.dispose_synced_data(vec);
      return Continuation::done()
    });
  }

  let exec = WorkGroup::new();
  exec.submit_and_await(Ctx{sync_obj:None}, begin);

  unsafe {
    let relc = ALLOCATION_COUNT.load(Ordering::Relaxed);
    let acqc = DEALLOCATION_COUNT.load(Ordering::Relaxed);
    println!("{} {}", acqc, relc);
    assert!(relc == acqc);
  }
}