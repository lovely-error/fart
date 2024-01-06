
use core::{sync::atomic::{compiler_fence, AtomicU32}, mem::size_of_val};
use std::{
  sync::{
    atomic::{AtomicU16, Ordering, fence, AtomicU64, AtomicU8, AtomicBool, },
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
    FailablePageSource, InfailablePageSource },
  ensure
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
  pub fn dispose<T: DisposableMemoryObject>(&self, object: T) -> Option<Block4KPtr>{ unsafe {
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
    free_page_provider:&mut dyn FnMut() -> Option<Block4KPtr>,
    frame_type: TaskFrameType,
  ) -> Option<TaskFrameRef> { unsafe {
    let frame_size = size_of::<RegionMetadata>().next_multiple_of(env_align) + env_size;
    if frame_size >= SMALL_PAGE_SIZE {
      // cant reasonably handle this yet
      errno::set_errno(errno::Errno(libc::EINVAL));
      return None;
    }
    let (frame_size, frame_align) = match frame_type {
      TaskFrameType::ThreadResumer =>
        (size_of::<TaskFrame_ThreadResumer>(), align_of::<TaskFrame_ThreadResumer>()),
      TaskFrameType::TaskResumer =>
        (size_of::<TaskFrame_TaskDependent>(), align_of::<TaskFrame_TaskDependent>()),
      TaskFrameType::Independent =>
        (size_of::<TaskFrame_Independent>(), align_of::<TaskFrame_Independent>()),
    };
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
      let mtd_ptr = tail.byte_add(tail.align_offset(frame_align));
      let data_ptr_unal = mtd_ptr.byte_add(frame_size);
      let data_ptr_al = data_ptr_unal.byte_add(data_ptr_unal.align_offset(env_align));
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

      return Some(TaskFrameRef(data_ptr_al));
    }
  } }
}

pub trait DisposableMemoryObject {
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
impl <T> DisposableMemoryObject for RegionItemRef<T> {
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
    fn get_middle_ptr(&self) -> *mut () {
      self.0 as _
    }
    fn get_region_mtd(&self) -> *mut RegionMetadata {
      self.0.map_addr(|addr| (addr - 1) & !(SMALL_PAGE_SIZE - 1)).cast()
    }
}
impl DisposableMemoryObject for TaskFrameRef {
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
  start_state: AtomicU8
}
impl IOPollingWorker {
  fn start(&mut self) {
    let outcome = self.start_state.compare_exchange(
      TriState::Nil as _, TriState::Began as _, Ordering::Relaxed, Ordering::Relaxed);
    match outcome {
      Err(_) => return,
      Ok(_) => unsafe {
        assert!(self.handle.is_none());
        let this = transmute_copy::<_, u64>(&self);
        self.handle = Some(spawn(move || {
          let this = transmute(this);
          io_polling_routine(this)
        }));
        self.start_state.store(TriState::Finished as _, Ordering::Release);
      },
    }
  }
  fn stop(&mut self) {
    if self.start_state.compare_exchange(
      TriState::Nil as _, TriState::Nil as _, Ordering::Relaxed, Ordering::Acquire
    ).is_ok() { return }
    self.handle.take().unwrap().join().unwrap();
  }
  fn wakeup(&self) {
    unsafe { (*(*self.work_group).worker_set.0.get()).active_workers_count.fetch_add(1, Ordering::Relaxed) };
    let started = self.start_state.compare_exchange(
      TriState::Nil as _, TriState::Nil as _, Ordering::Relaxed, Ordering::Relaxed).is_err();
    assert!(started);
    self.handle.as_ref().unwrap().thread().unpark();
  }
}
struct IOPollingCallbackData {
  task_to_resume: Task,
  target: RawFd,
  readable: bool,
  writeable: bool
}
fn io_polling_routine(worker: &mut IOPollingWorker) { unsafe {
  let ok = core_affinity::set_for_current(worker.core_pin_index);
  assert!(ok, "failed to pin io thread to core");
  let mut io_pending_tasks = HashMap::<usize, (Task, RawFd)>::new();
  let poller = Poller::new().unwrap();
  let work_source = &mut worker.out_port;
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
    let outcome = poller.wait(&mut gathered_events, Some(Duration::from_millis(1)));
    match outcome {
      Ok(_) => (),
      Err(err) => {
        match err.kind() {
            std::io::ErrorKind::Interrupted => {
              continue 'processing;
            }
            _ => (), // whatever (fixme)
        }
      }
    }
    let no_continuations_to_resume = gathered_events.is_empty();
    let has_nothing_to_do = no_continuations_to_resume && io_pending_tasks.is_empty();
    if has_nothing_to_do {
      // got to sleep
      (*(*worker.work_group).worker_set.0.get()).active_workers_count.fetch_sub(1, Ordering::Relaxed);
      park(); // its okay if this gets unparked at random
      let time_to_die =
        worker.have_to_die.compare_exchange(true, true, Ordering::Relaxed, Ordering::Relaxed);
      if time_to_die.is_ok() {
        return;
      }
      continue 'processing;
    }
    for event in &gathered_events {
      let (task, fd) = io_pending_tasks.remove(&event.key).unwrap();
      poller.delete(fd).unwrap();
      batch_for_resume.push(task);
    }
    let no_resume_batch = batch_for_resume.is_empty();
    if no_resume_batch { continue }
    if let Some(free_worker) = (*worker.work_group).worker_set.try_acquire_free_worker_mref() {
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
  }
} }
fn blocking_runner_routine(
  runner: &mut BlockingRunner
) { unsafe {
  let ok = core_affinity::set_for_current(runner.core_index);
  if !ok { panic!("failed to pin blocking runner {:?}", runner.core_index) }
  let mut outcome = runner.sink_port.try_iter();
  loop {
    match outcome.next() {
      None => {
        (*(*runner.work_group).worker_set.0.get()).active_workers_count.fetch_sub(1, Ordering::Relaxed);
        park();
        if (*(*runner.work_group).worker_set.0.get()).should_stop.compare_exchange(
          true, true, Ordering::Relaxed, Ordering::Relaxed).is_ok() {
          return;
        }
      },
      Some(item) => {
        let task = item.task;
        let ptr = task.get_ptr();
        let mtd = &mut*ptr.cast::<TaskFrame_GenericView>().sub(1);
        let ContinuationRepr::BlockingCall(fun) = mtd.continuation.continuation else {
          panic!("Expected a blocking operation")
        };
        let handle = CaptureHandle(ptr);
        let next = fun(&handle);
        mtd.continuation = next;
        // lets try to resume this task on idle executor if possible
        let dest = match (*runner.work_group).worker_set.try_acquire_free_worker_mref() {
          Some(worker) => worker,
          None => &mut*item.owning_worker,
        };
        dest.start();
        dest.task_send_port.send(task).unwrap();
        dest.salt.fetch_add(1, Ordering::Release);
        dest.wakeup();
      },
    }
  }
} }
struct BlockingRunner {
  work_group: *mut WorkGroup,
  thread: Option<JoinHandle<()>>,
  sink_port: Receiver<BlockingOperation>,
  send_port: Sender<BlockingOperation>,
  core_index: CoreId,
  start_state: AtomicU8,
}
impl BlockingRunner {
  fn wakeup(&self) {
    unsafe { (*(*self.work_group).worker_set.0.get()).active_workers_count.fetch_add(1, Ordering::Relaxed) };
    while self.start_state.load(Ordering::Relaxed) != TriState::Finished as _ {}
    fence(Ordering::Acquire);
    self.thread.as_ref().unwrap().thread().unpark();
  }
  fn start(&mut self) {
    let outcome = self.start_state.compare_exchange(
      TriState::Nil as _, TriState::Began as _, Ordering::Relaxed, Ordering::Relaxed);
    match outcome {
      Err(_) => return,
      Ok(_) => unsafe {
        let this : u64 = transmute(addr_of_mut!(*self));
        let thread = thread::spawn(move ||{
          let this: &mut Self = transmute(this);
          blocking_runner_routine(this);
        });
        self.thread = Some(thread);
        self.start_state.store(TriState::Finished as _, Ordering::Release);
      },
    }
  }
  fn stop(&mut self) {
    let outcome = self.start_state.compare_exchange(
      TriState::Nil as _, TriState::Nil as _, Ordering::Relaxed, Ordering::Relaxed);
    match outcome {
      Ok(_) => return,
      Err(_) => {
        while self.start_state.load(Ordering::Relaxed) != TriState::Finished as _ {}
        fence(Ordering::Acquire);
        self.thread.take().unwrap().join().unwrap();
      },
    }
  }
}
struct BlockingOperation {
  task: Task,
  owning_worker: *mut Worker
}
struct WorkerSet(UnsafeCell<WorkerSetData>);
struct WorkerSetData {
  workers: Vec<Worker>,
  inline_free_indicies: AtomicU64,
  outline_free_indicies: Option<Vec<AtomicU64>>,
  total_worker_count: u32,
  external_ref_count: AtomicU32, // references to this work group instance
  active_workers_count: AtomicU32,
  io_handling_thread: IOPollingWorker, // sorry :(
  blocking_runners_occupation_map: AtomicU64,
  blocking_runners: Vec<BlockingRunner>,
  should_stop: AtomicBool
}
impl WorkerSet {
  fn try_find_free_blocking_runner(
    &self
  ) -> Option<&mut BlockingRunner> { unsafe {
    let this = &mut *self.0.get();
    let worker_count = this.total_worker_count;
    let limit = if worker_count / 64 > 0 { 64 } else { worker_count } ;
    if let Some(index) = find_free_index(&this.blocking_runners_occupation_map, limit) {
      let ptr = &mut this.blocking_runners[index as usize];
      return Some(ptr);
    } else {
      return None;
    }
  } }
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
  if let Err(real) =  map.compare_exchange(0, 0, Ordering::Relaxed, Ordering::Relaxed) {
    indicies = real
  }
  loop {
    let some_index = indicies.trailing_ones();
    if some_index == total_worker_count { return None }
    let index_mask = 1u64 << some_index;
    let prior = map.fetch_or(index_mask, Ordering::Relaxed);
    let taken = prior & index_mask != 0;
    if taken {
      indicies = prior;
      continue;
    }
    return Some(some_index as _);
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
  #[allow(dead_code)]
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
    let reader_got_past_writer = {
      let on_same_page =
        new_rp.byte_sub(1).map_addr(|addr|addr & !(SMALL_PAGE_SIZE - 1)) ==
        self.write_ptr.byte_sub(1).map_addr(|addr|addr & !(SMALL_PAGE_SIZE - 1));
      let run_ahead = new_rp.expose_addr() > self.write_ptr.expose_addr();

      on_same_page && run_ahead
    };
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
  println!("___DELIMITER___");
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

#[derive(Debug, Clone, Copy)] #[repr(u8)]
enum TriState {
  Nil, Began, Finished
}
#[derive(Debug, Clone, Copy)] #[repr(u8)]
enum SyncState {
  Interest, Ready, Done
}
struct Worker {
  runner_handle: Option<JoinHandle<()>>,
  work_group: *mut WorkGroup,
  inner_context_ptr: MaybeUninit<*mut WorkerExportContext>,
  index: u32,
  core_pin_id: core_affinity::CoreId,
  io_send_port: Sender<IOPollingCallbackData>,
  task_sink_port: Receiver<Task>,
  task_send_port: Sender<Task>,
  salt: AtomicU64,
  start_state: AtomicU8,
  sync_state: AtomicU8
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
  fn was_started(&self) -> bool {
    self.start_state.compare_exchange(
      TriState::Nil as _, TriState::Nil as _, Ordering::Relaxed, Ordering::Acquire).is_err()
  }
  fn start(&mut self) { unsafe {
    let outcome = self.start_state.compare_exchange(
      TriState::Nil as _, TriState::Began as _, Ordering::Relaxed, Ordering::Relaxed);
    match outcome {
      Err(_) => return,
      Ok(_) => {
        let copy = transmute_copy::<_, u64>(&self);
        let thread = thread::spawn(move ||{
          let ptr = transmute::<_, &mut Worker>(copy);
          worker_processing_routine(ptr);
        });
        self.runner_handle = Some(thread);
        self.start_state.store(TriState::Finished as _, Ordering::Release);
      },
    }
  } }
  fn wait_worker_sync_began(&self) {
    while self.sync_state.compare_exchange(
      SyncState::Done as _,
      SyncState::Interest as _,
      Ordering::Relaxed,
      Ordering::Relaxed).is_err() {}
    self.wakeup();
    while self.sync_state.load(Ordering::Relaxed) != SyncState::Ready as _ {}
    fence(Ordering::Acquire);
  }
  fn signal_worker_sync_ended(&self) {
    self.sync_state.store(SyncState::Done as _, Ordering::Release);
  }
  fn with_synced_access(&mut self, action: impl FnOnce(&mut Self)) {
    unsafe { (*(*self.work_group).worker_set.0.get()).active_workers_count.fetch_add(1, Ordering::Relaxed) };
    let was_started = self.was_started();
    assert!(was_started, "cannot acccess context of a worker that was not started");
    self.wait_worker_sync_began();
    action(self);
    self.signal_worker_sync_ended();
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
#[repr(C)]
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

fn worker_processing_routine(worker_: *mut Worker) { unsafe {

  let worker = &mut*worker_;

  let ok = core_affinity::set_for_current(worker.core_pin_id);
  assert!(ok, "failed to pin worker {} to core {:?}", worker.index, worker.core_pin_id);

  let mut exported_context = WorkerExportContext {
    allocator: SubRegionAllocator::new(),
    workset: TaskSet::new(),
    stale_page_drainer: MaybeUninit::uninit()
  };

  let mut retired_pages_aggregator = RetiredPageAggregator::new();
  let mut drainer = PageRouter_([
    addr_of_mut!(retired_pages_aggregator),
  ], ());
  exported_context.stale_page_drainer.write(&mut drainer);
  worker.inner_context_ptr.write(addr_of_mut!(exported_context));

  worker.sync_state.store(SyncState::Ready as _, Ordering::Release);
  while worker.sync_state.load(Ordering::Relaxed) != SyncState::Done as _ {}
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
  let mut sink_port = worker.task_sink_port.try_iter();
  let mut recent_salt = 0;

  #[cfg(feature = "collect_time_metric")]
  let mut exec_total = 0u128;
  #[cfg(feature = "collect_time_metric")]
  let mut exec_runs = 0u128;

  let mut exec_state = ExecState::Fetch;
  'dispatch:loop {
    match exec_state {
      ExecState::Fetch => {
        if let Some((new_task, free_mem)) = (*workset_).deque_one() {
          current_task = new_task;
          if let Some(free_mem) = free_mem {
            retired_pages_aggregator.store_page(free_mem);
          }
          exec_state = ExecState::Execute;
          continue 'dispatch;
        }
        if let Some(task) = sink_port.next() {
          (*workset_).enque(task, &mut infailable_page_source);
          while let Some(task) = sink_port.next() {
            (*workset_).enque(task, &mut infailable_page_source);
          }
          continue 'dispatch;
        }
        exec_state = ExecState::Sleep;
        continue 'dispatch;
      },
      ExecState::Sleep => {
        let _ = (*worker_set.0.get()).active_workers_count.fetch_sub(1, Ordering::Relaxed);
        let _ = worker.mark_as_free();
        // fence(Ordering::SeqCst);
        loop {
          if worker.sync_state.compare_exchange(
            SyncState::Interest as _,
            SyncState::Interest as _,
            Ordering::Relaxed,
            Ordering::Relaxed
          ).is_ok() {
            worker.sync_state.store(SyncState::Ready as _, Ordering::Release);
            while worker.sync_state.load(Ordering::Relaxed) != SyncState::Done as _ {}
            fence(Ordering::Acquire);
            exec_state = ExecState::Fetch;
            continue 'dispatch;
          }
          let done = (*worker_set.0.get()).should_stop.compare_exchange(
            true, true, Ordering::Relaxed, Ordering::Relaxed).is_ok();
          if done {
            exec_state = ExecState::Shutdown;
            continue 'dispatch;
          }
          match worker.salt.compare_exchange(
            recent_salt, recent_salt, Ordering::Relaxed, Ordering::Relaxed
          ) {
            Ok(_) => (),
            Err(real) => {
              fence(Ordering::Acquire);
              recent_salt = real;
              exec_state = ExecState::Fetch;
              continue 'dispatch;
            },
          };
          park();
        }
      },
      ExecState::Shutdown => {
        retired_pages_aggregator.dispose();
        #[cfg(feature = "collect_time_metric")] {
        let total_time = Duration::from_nanos((exec_total) as u64);
        println!(
            "Worker {} spent in total {:?}, average {:?} per workitem",
            worker.index, total_time, total_time / (exec_runs as u32));
        }
        return;
      }
      ExecState::Execute => {
        let frame_ptr = current_task.get_ptr();
        let frame_ref =
          &mut*frame_ptr.cast::<TaskFrame_GenericView>().sub(1);
        let continuation = frame_ref.continuation.continuation;
        match continuation {
          ContinuationRepr::BlockingCall(_) => {
            let smth = (*worker.work_group).worker_set.try_find_free_blocking_runner();
            match smth {
              None => {
                exported_context.workset.enque(current_task, &mut infailable_page_source);
                exec_state = ExecState::Fetch;
                continue 'dispatch;
              },
              Some(runner) => {
                runner.start();
                let op = BlockingOperation {
                  task: current_task,
                  owning_worker: worker_
                };
                runner.send_port.send(op).unwrap();
                runner.wakeup();
                exec_state = ExecState::Fetch;
                continue 'dispatch;
              },
            }
          }
          ContinuationRepr::Then(thunk) => {
            #[cfg(feature = "collect_time_metric")] {
              let pre = Instant::now();
              compiler_fence(Ordering::SeqCst);
            }
            let next = thunk(&task_context);
            fence(Ordering::Release);
            #[cfg(feature = "collect_time_metric")] {
              compiler_fence(Ordering::SeqCst);
              let post = pre.elapsed();
              exec_total += post.as_nanos();
              exec_runs += 1;
            }
            frame_ref.continuation = next;
            let produced_subtasks = immidiate_state.spawned_subtask_count != 0;
            if produced_subtasks {
              frame_ref.subtask_count.store(
                immidiate_state.spawned_subtask_count, Ordering::Relaxed);
              task_context.clear_dirty_state();
              // last child awakes parent task
            } else {
              // repush task. we want other tasks to run
              exported_context.workset.enque(
                current_task, &mut infailable_page_source);
            }
            share_work(worker_set, workset_, &mut retired_pages_aggregator);
            exec_state = ExecState::Fetch;
            continue 'dispatch;
          },
          ContinuationRepr::Done => {
            match current_task.get_frame_type() {
              TaskFrameType::ThreadResumer => {
                let frame_ref = &*frame_ptr.cast::<TaskFrame_ThreadResumer>().sub(1);
                (*frame_ref.wake_flag).store(true, Ordering::Relaxed);
                frame_ref.awaiting_thread.unpark();
                if let Some(page) = exported_context.allocator.dispose(current_task) {
                  retired_pages_aggregator.store_page(page)
                }
                exec_state = ExecState::Fetch;
                continue 'dispatch;
              },
              TaskFrameType::TaskResumer => {
                let frame_ref = &*frame_ptr.cast::<TaskFrame_TaskDependent>().sub(1);
                let parked_task = frame_ref.parent_task;
                if let Some(page) = exported_context.allocator.dispose(current_task) {
                  retired_pages_aggregator.store_page(page)
                }
                let parent_frame = &*parked_task.get_ptr().cast::<TaskFrame_GenericView>().sub(1);
                let remaining_subtasks_count =
                  parent_frame.subtask_count.fetch_sub(1, Ordering::Relaxed);
                let last_child = remaining_subtasks_count == 1;
                if last_child {
                  fence(Ordering::Acquire);
                  current_task = parked_task;
                  continue 'dispatch;
                } else {
                  exec_state = ExecState::Fetch;
                  continue 'dispatch;
                }
              },
              TaskFrameType::Independent => {
                if let Some(page) = exported_context.allocator.dispose(current_task) {
                  retired_pages_aggregator.store_page(page)
                };
                exec_state = ExecState::Fetch;
                continue 'dispatch;
              },
            }
          },
          ContinuationRepr::AwaitIO(fd, r, w, next) => {
            let frame_ref = &mut*current_task.get_ptr().cast::<TaskFrame_GenericView>().sub(1);
            frame_ref.continuation = Continuation {
              continuation: ContinuationRepr::Then(next)
            };
            let item = IOPollingCallbackData {
              task_to_resume: current_task,
              target: fd, readable: r, writeable: w
            };
            worker.io_send_port.send(item).unwrap();
            let io_worker = &mut (*(*worker.work_group).worker_set.0.get()).io_handling_thread;
            io_worker.start();
            io_worker.wakeup();
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
            &mut*subordinate_worker.inner_context_ptr.assume_init();
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
  spawned_subtask_count: u64,
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
pub trait FrameDataProvider {
  fn acccess_frame_as_raw(&self) -> *mut ();
  fn access_frame_as_uninit<T>(&self) -> &mut MaybeUninit<T>;
  fn access_frame_as_init<T>(&self) -> &mut ManuallyDrop<T>;
}

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
  pub fn acccess_capture_as_raw(&self) -> *mut () { unsafe {
    let this = &mut *self.0.get();
    let data_ptr = (*(*this.immidiate_state).current_task).get_ptr();
    return data_ptr.cast();
  } }
  pub fn access_capture_as_uninit<T>(&self) -> &mut MaybeUninit<T> { unsafe {
    return &mut *self.acccess_capture_as_raw().cast::<MaybeUninit<T>>()
  }; }
  pub fn access_capture_as_init<T>(&self) -> &mut ManuallyDrop<T> { unsafe {
    return &mut *self.acccess_capture_as_raw().cast::<ManuallyDrop<T>>()
  }; }

  // parents never get ahead of their children in the execution timeline.
  // subtasks are never parentless
  pub fn spawn_subtask<T: Send>(&self, capture: T, operation: Thunk) {
    self.spawn_task_common_impl(
      addr_of!(capture).cast::<()>(),
      size_of::<T>(), align_of::<T>(), operation, false);
    forget(capture)
  }
  // parent does not depend on this task
  pub fn spawn_detached_task<T: Send>(&self, capture: T, operation: Thunk) {
    self.spawn_task_common_impl(
      addr_of!(capture).cast::<()>(),
      size_of::<T>(), align_of::<T>(), operation, true);
    forget(capture)
  }
  #[inline(never)]
  fn spawn_task_common_impl(
    &self,
    env_data:*const (),
    env_size:usize,
    env_align:usize,
    thunk: Thunk,
    detached: bool,
  ) { unsafe {
    let this = &mut *self.0.get();
    let immidiate_state_ref = &mut *this.immidiate_state;
    if !detached {
      immidiate_state_ref.spawned_subtask_count += 1;
    }
    let frame_type = if detached {
      TaskFrameType::Independent
    } else {
      TaskFrameType::TaskResumer
    };
    let frame_ref = (*this.worker_inner_context_ref).allocator.alloc_task_frame(
      env_align,
      env_size,
      &mut || Some((*this.infailable_page_source).get_page()),
      frame_type
    ).unwrap();
    let middle_ptr = frame_ref.get_middle_ptr();
    if detached {
      let frame_ptr = middle_ptr.cast::<TaskFrame_Independent>().sub(1);
      frame_ptr.write(TaskFrame_Independent {
        continuation: Continuation { continuation: ContinuationRepr::Then(thunk) },
        subtask_count: AtomicU64::new(0)
      })
    } else {
      let frame_ptr = middle_ptr.cast::<TaskFrame_TaskDependent>().sub(1);
      frame_ptr.write(TaskFrame_TaskDependent {
        parent_task: immidiate_state_ref.current_task.read(),
        continuation: Continuation { continuation: ContinuationRepr::Then(thunk) },
        subtask_count: AtomicU64::new(0)
      })
    }
    let data_ptr = middle_ptr;
    copy_nonoverlapping(env_data.cast::<u8>(), data_ptr.cast::<u8>(), env_size);

    let subtask = Task::new(frame_ref, frame_type);
    let task_set = &mut (*this.worker_inner_context_ref).workset;
    task_set.enque(subtask, &mut*this.infailable_page_source);
  }; }
  fn clear_dirty_state(&self) {
    let this = unsafe { &mut *self.0.get() };
    let imm_ctx = unsafe{&mut *this.immidiate_state};
    imm_ctx.spawned_subtask_count = 0;
  }
}
pub struct CaptureHandle(*mut ());
impl CaptureHandle {
  pub fn acccess_capture_as_raw(&self) -> *mut () {
    self.0
  }
  pub fn access_capture_as_uninit<T>(&self) -> &mut MaybeUninit<T> { unsafe {
    return &mut *self.acccess_capture_as_raw().cast::<MaybeUninit<T>>()
  }; }
  pub fn access_capture_as_init<T>(&self) -> &mut ManuallyDrop<T> { unsafe {
    return &mut *self.acccess_capture_as_raw().cast::<ManuallyDrop<T>>()
  }; }
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
  BlockingCall(fn (&CaptureHandle) -> Continuation)
}
impl Continuation {
  pub fn run_blocking(
    operation: fn (&CaptureHandle) -> Continuation
  ) -> Self {
    Self { continuation: ContinuationRepr::BlockingCall(operation) }
  }
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

#[derive(Debug, Clone, Copy)] #[repr(u8)]
enum TaskFrameType {
  ThreadResumer,
  TaskResumer,
  Independent
}

#[repr(C)] #[derive(Debug)] #[allow(non_camel_case_types)]
struct TaskFrame_ThreadResumer {
  awaiting_thread: Thread,
  wake_flag: *const AtomicBool,
  continuation: Continuation,
  subtask_count: AtomicU64,
}
#[repr(C)] #[derive(Debug)] #[allow(non_camel_case_types)]
struct TaskFrame_TaskDependent {
  parent_task: Task,
  continuation: Continuation,
  subtask_count: AtomicU64,
}
#[repr(C)] #[derive(Debug)] #[allow(non_camel_case_types)]
struct TaskFrame_Independent {
  continuation: Continuation,
  subtask_count: AtomicU64,
}
#[repr(C)] #[derive(Debug)] #[allow(non_camel_case_types)]
struct TaskFrame_GenericView {
  continuation: Continuation,
  subtask_count: AtomicU64,
}

#[repr(C)] #[repr(align(8))] #[derive(Debug, Clone, Copy)]
struct Task(u64);
impl Task {
  fn new(
    task_frame_ptr: TaskFrameRef,
    frame_type: TaskFrameType
  ) -> Self {
    let addr = task_frame_ptr.0.expose_addr();
    let num = (addr << 8) + unsafe { transmute::<_,u8>(frame_type) as usize };
    return Self(num as _)
  }
  fn get_frame_type(&self) -> TaskFrameType {
    unsafe { transmute((self.0 & ((1 << 8) - 1)) as u8) }
  }
  fn get_ptr(&self) -> *mut () {
    (self.0 >> 8) as _
  }
  fn new_null() -> Self {
    Self(0)
  }
  fn get_region_metadata_ptr_(&self) -> *mut RegionMetadata {
    self.get_ptr().map_addr(|addr| (addr - 1) & !(SMALL_PAGE_SIZE - 1)).cast()
  }
}
impl DisposableMemoryObject for Task {
  fn get_region_metadata_ptr(&self) -> *mut RegionMetadata {
    self.get_region_metadata_ptr_()
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
    let boxed = alloc(Layout::new::<WG>());
    let boxed = boxed.cast::<WG>();
    let (io_send, io_recv) = channel();

    let mut workers = Vec::new();
    workers.reserve(worker_count);
    let mut blockers = Vec::new();
    blockers.reserve(worker_count);
    for wix in 0 .. worker_count {
      let core_ix = core_ids[wix as usize];
      let (send, recv) = channel();
      let worker = Worker {
        sync_state: AtomicU8::new(SyncState::Done as _),
        salt: AtomicU64::new(0),
        task_send_port: send,
        task_sink_port: recv,
        index: wix as u32,
        runner_handle: None,
        work_group: boxed,
        inner_context_ptr: MaybeUninit::uninit(),
        core_pin_id: core_ix,
        io_send_port: io_send.clone(),
        start_state: AtomicU8::new(TriState::Nil as _)
      };
      workers.push(worker);
      let (send, recv) = channel();
      let blocker = BlockingRunner {
        work_group: boxed,
        core_index: core_ix,
        sink_port: recv,
        send_port: send,
        thread: None,
        start_state: AtomicU8::new(TriState::Nil as _),
      };
      blockers.push(blocker);
    }
    boxed.write(WorkGroup {
      ralloc:RootAllocator::new(),
      worker_set: WorkerSet(UnsafeCell::new(WorkerSetData {
        blocking_runners: blockers,
        blocking_runners_occupation_map: AtomicU64::new(0),
        workers: workers,
        inline_free_indicies: AtomicU64::new(0),
        outline_free_indicies: None,
        total_worker_count: worker_count as u32,
        io_handling_thread: IOPollingWorker {
          work_group: boxed,
          handle: None,
          out_port: io_recv,
          core_pin_index: core_ids[0],
          have_to_die: AtomicBool::new(false),
          start_state: AtomicU8::new(TriState::Nil as _)
        },
        should_stop: AtomicBool::new(false),
        external_ref_count: AtomicU32::new(1), // +1 because ref exist
        active_workers_count: AtomicU32::new(0), // workers have to be started first
      })),
    });

    return WorkGroupRef(boxed)
  } }
  fn destroy(&self) { unsafe {
    let workeset = &mut *self.worker_set.0.get();
    while workeset.active_workers_count.compare_exchange(
      0, 0, Ordering::Relaxed, Ordering::Relaxed
    ).is_err() {
      yield_now()
    }
    workeset.should_stop.store(true, Ordering::Relaxed);
    fence(Ordering::SeqCst);
    let io_worker = &mut workeset.io_handling_thread;
    io_worker.have_to_die.store(true, Ordering::Relaxed);
    io_worker.stop();
    let total_worker_count = workeset.total_worker_count;
    for ix in 0 .. total_worker_count {
      let wref = self.worker_set.mref_worker_at_index(ix);
      if wref.was_started() {
        wref.wakeup();
        wref.runner_handle.take().unwrap().join().unwrap()
      }
    }
    for br in &mut workeset.blocking_runners {
      br.stop();
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
        align_of::<Env>(),
        size_of::<Env>(),
        &mut || Some(infailable_page_source.get_page()),
        TaskFrameType::ThreadResumer
      ).unwrap();
      let middle_ptr = ptr.get_middle_ptr();
      let frame_ptr = middle_ptr.cast::<TaskFrame_ThreadResumer>().sub(1);
      frame_ptr.write(TaskFrame_ThreadResumer {
        awaiting_thread: requesting_thread,
        wake_flag: addr_of!(can_resume),
        continuation: Continuation { continuation: ContinuationRepr::Then(operation) },
        subtask_count: AtomicU64::new(0)
      });
      let data_ptr = middle_ptr;
      copy_nonoverlapping(addr_of!(capture).cast::<u8>(), data_ptr.cast::<u8>(), size_of::<Env>());

      let task = Task::new(ptr, TaskFrameType::ThreadResumer);
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
    worker.with_synced_access(|worker| {
      let inner_ctx = &mut *worker.inner_context_ptr.assume_init();
      let mut infailable_page_source = PageRouter(||{
        (*inner_ctx.stale_page_drainer.assume_init()).try_drain_page()
        .unwrap_or(worker.get_root_allocator().try_get_page_blocking().unwrap())
      });
      let ptr = inner_ctx.allocator.alloc_task_frame(
        align_of::<Env>(),
        size_of::<Env>(),
        &mut || Some(infailable_page_source.get_page()),
        TaskFrameType::Independent
      ).unwrap();
      let middle_ptr = ptr.get_middle_ptr();
      let frame_ptr = middle_ptr.cast::<TaskFrame_Independent>().sub(1);
      frame_ptr.write(TaskFrame_Independent {
        continuation: Continuation { continuation: ContinuationRepr::Then(operation) },
        subtask_count: AtomicU64::new(0)
      });
      let data_ptr = middle_ptr;
      copy_nonoverlapping(addr_of!(capture).cast::<u8>(), data_ptr.cast::<u8>(), size_of::<Env>());

      let task = Task::new(ptr, TaskFrameType::Independent);
      inner_ctx.workset.enque(task, &mut infailable_page_source);
    });
    forget(capture);
    return;
  } }

  pub fn clone_ref(&self) -> Self { unsafe {
    (*(*self.0).worker_set.0.get()).external_ref_count.fetch_add(1, Ordering::AcqRel);
    return WorkGroupRef(self.0)
  } }
}
impl Drop for WorkGroupRef {
  fn drop(&mut self) { unsafe {
    let count = (*(*self.0).worker_set.0.get()).external_ref_count.fetch_sub(1, Ordering::Relaxed);
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
  const LIMIT:u64 = 1_000_000;
  struct ParentData { counter: AtomicU64, }
  fn parent(ctx: &TaskContext) -> Continuation {
    let frame = ctx.access_capture_as_init::<ParentData>();
    for _ in 0 .. LIMIT {
      ctx.spawn_subtask(&frame.counter, child);
    }
    return Continuation::then(check)
  }
  fn child(ctx: &TaskContext) -> Continuation {
    let counter = ctx.access_capture_as_init::<&AtomicU64>();
    let _ = counter.fetch_add(1, Ordering::Relaxed);
    return Continuation::done();
  }
  fn check(ctx: &TaskContext) -> Continuation {
    let frame = ctx.access_capture_as_init::<ParentData>();
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
      let data = ctx.access_capture_as_init::<Data>();
      data.start_time = Some(Instant::now());
      for _ in 0 .. LIMIT {
          let ptr = data.counter_ref;
          ctx.spawn_subtask(ptr, |ctx|{
              let ptr = ctx.access_capture_as_init::<&AtomicU64>();
              ptr.fetch_add(1, Ordering::Relaxed);
              return Continuation::done()
          })
      }
      return Continuation::then(|ctx| {
        let data = ctx.access_capture_as_init::<Data>();
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
      let data = ctx.access_capture_as_init::<Data>();
      data.start_time = Some(Instant::now());
      let ptr = data.items.as_mut_ptr();
      for i in 0 .. LIMIT {
          let ptr = unsafe{ptr.add(i)};
          let addr : usize = unsafe { transmute(ptr) };
          ctx.spawn_subtask((addr, i), |ctx|{
              let ptr = ctx.access_capture_as_init::<(usize, usize)>();
              let addr = ptr.0;
              let i = ptr.1;
              let item_ptr : *mut [usize;16] = unsafe { transmute(addr) };
              unsafe {item_ptr.write([i;16])};
              return Continuation::done()
          })
      }
      return Continuation::then(|ctx| {
        let data = ctx.access_capture_as_init::<Data>();
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


#[test]
fn subsyncing2() {
  const LIMIT : usize = 1_000_000;
  let wg = WorkGroup::new();
  let mut st = Vec::<[usize;16]>::new();
  st.reserve(LIMIT);
  struct Data { start_time: Option<Instant>, items: Vec<[usize;16]>, counter: AtomicU64 }
  wg.submit_and_await(Data {items: st, start_time:None, counter: AtomicU64::new(0)}, |ctx| {
      let data = ctx.access_capture_as_init::<Data>();
      data.start_time = Some(Instant::now());
      let ptr = data.items.as_mut_ptr();
      for i in 0 .. LIMIT {
          let counter = &data.counter;
          let ptr = unsafe{ptr.add(i)};
          let addr : usize = unsafe { transmute(ptr) };
          ctx.spawn_detached_task((addr, i, counter), |ctx|{
              let ptr = ctx.access_capture_as_init::<(usize, usize, &AtomicU64)>();
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
    let data = ctx.access_capture_as_init::<Data>();
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

#[test]
fn blocking_runner() {
  let wg = WorkGroup::new();
  const STR1: &str = "ahoy, maties!";
  const STR2: &str = "yar!";
  wg.submit_and_await(STR1, |_|{
    return Continuation::run_blocking(|cpt|{
      let cpt = cpt.access_capture_as_init::<&str>();
      assert!(*cpt == ManuallyDrop::new(STR1));
      *cpt = ManuallyDrop::new(STR2);
      return Continuation::then(after_blocking);
    });
  });
  fn after_blocking(ctx: &TaskContext) -> Continuation {
    let cpt = ctx.access_capture_as_init::<&str>();
    assert!(*cpt == ManuallyDrop::new(STR2));
    return Continuation::done();
  }
}

