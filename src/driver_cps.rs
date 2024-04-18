
use core::{mem::{offset_of, size_of_val}, simd::{SimdPartialEq, ToBitMask}, sync::atomic::{compiler_fence, AtomicU32}};
use std::{
  alloc::{alloc, Layout}, cell::UnsafeCell, collections::HashMap, marker::PhantomData, mem::{
    align_of, forget, size_of, transmute, transmute_copy, ManuallyDrop, MaybeUninit
  }, os::fd::RawFd, ptr::{addr_of, addr_of_mut, copy_nonoverlapping, null_mut }, simd::Simd, sync::{
    atomic::{fence, AtomicBool, AtomicU16, AtomicU64, AtomicU8, Ordering },
    mpsc::{channel, Receiver, Sender}
  }, thread::{self, current, park, park_timeout, spawn, yield_now, JoinHandle, Thread}, time::{Duration, Instant}
};

use core_affinity::CoreId;
use libc::NFT_SET_ANONYMOUS;
use polling::{Poller, Source, Event};

use crate::{
  static_assert, force_publish_stores_on_location, force_pusblish_stores, hard_mfence, root_alloc::{Block4KPtr, RootAllocator}, utils::FailablePageSource
};
use crate::futex;

use core_affinity;

const SMALL_PAGE_SIZE : usize = 4096;

pub struct RegionMetadata {
  ref_count: AtomicU16
}
#[repr(align(64))]
struct SlabCell([u8;64]);
#[repr(C)] #[repr(align(4096))]
struct SlabPage {
  ref_count: AtomicU32,
  cells: [SlabCell;SLAB_MAX_COUNT]
}
static_assert!(size_of::<SlabPage>() == SMALL_PAGE_SIZE);
const SLAB_MAX_COUNT: usize = (4096 - 1) / size_of::<SlabCell>();
struct WorkerLocalSlabAllocatorInner {
  page_origin_addr: *mut SlabPage,
  free_slab_ptr: *mut u8
}
struct WorkerLocalSlabAllocator(UnsafeCell<WorkerLocalSlabAllocatorInner>);
impl WorkerLocalSlabAllocator {
  fn new() -> Self {
    Self(UnsafeCell::new(WorkerLocalSlabAllocatorInner {
        page_origin_addr: null_mut(),
        free_slab_ptr: null_mut(),
    }))
  }
  fn set_page(&self, page: *mut u8) { unsafe {
    let this = &mut *self.0.get();
    let page = page.cast::<SlabPage>();
    (*page).ref_count.store(1, Ordering::Relaxed);
    this.page_origin_addr = page.cast();
    this.free_slab_ptr = page.byte_add(offset_of!(SlabPage, cells)).cast();
  } }
  fn release_page(&self) -> bool { unsafe {
    let this = &mut *self.0.get() ;
    let prior = (*this.page_origin_addr).ref_count.fetch_sub(1, Ordering::Relaxed);
    if prior == 1 {
      // reusable
      this.free_slab_ptr = addr_of_mut!((*this.page_origin_addr).cells).cast();
      return false;
    } else {
      return true
    }
  } }
  #[inline(never)] #[allow(dead_code)]
  fn alloc_bytes(
    &self,
    size: usize,
    alignment: usize,
    page_source: &mut dyn FailablePageSource
  ) -> Option<OpaqueRegionItemRef> { unsafe {
    if size > SLAB_MAX_COUNT * 64 { panic!("fixme: too big") }
    let this = &mut *self.0.get();
    if this.free_slab_ptr.is_null() {
      let page = match page_source.try_drain_page() {
        Some(page) => page,
        None => return None,
      };
      self.set_page(page.get_ptr())
    }
    loop {
      let ptr_al_off = this.free_slab_ptr.align_offset(alignment);
      let data_ptr = this.free_slab_ptr.byte_add(ptr_al_off);
      let end_ptr = data_ptr.byte_add(size);
      let right_bound = this.page_origin_addr.expose_addr() + 4096;
      let past_boundry = end_ptr.expose_addr() > right_bound;
      if past_boundry {
        // first release current page!
        let needs_new = self.release_page();
        if needs_new {
          let page = page_source.try_drain_page();
          let page = match page {
              Some(page) => page,
              None => {
                this.free_slab_ptr = null_mut();
                return None;
              },
          };
          self.set_page(page.get_ptr().cast());
        }
        continue;
      }
      (*this.page_origin_addr).ref_count.fetch_add(1, Ordering::Relaxed);
      let postfix = end_ptr.byte_add(end_ptr.align_offset(64));
      let exhausted = postfix.expose_addr() == right_bound;
      if exhausted {
        let needs_new = self.release_page();
        if needs_new {
          this.free_slab_ptr = null_mut();
        }
      } else {
        this.free_slab_ptr = postfix;
      }
      let ori = OpaqueRegionItemRef(data_ptr.cast());
      return Some(ori);
    }
  } }
  #[inline(never)]
  fn alloc_task_frame(
    &self,
    env_align: usize,
    env_size: usize,
    page_source: &mut dyn FailablePageSource,
    frame_type: TaskFrameType,
  ) -> Option<(TaskFrameRef, u8)> { unsafe {
    let this = &mut *self.0.get();
    if this.free_slab_ptr.is_null() {
      let page = match page_source.try_drain_page() {
        Some(page) => page,
        None => return None,
      };
      self.set_page(page.get_ptr())
    }
    let frame_size = size_of::<RegionMetadata>().next_multiple_of(env_align) + env_size;
    if frame_size >= SMALL_PAGE_SIZE {
      panic!("fixme: wont fit")
    }
    let (frame_size, frame_align) = match frame_type {
      TaskFrameType::ThreadResumer =>
        (size_of::<TaskFrame_ThreadResumer>(), align_of::<TaskFrame_ThreadResumer>()),
      TaskFrameType::TaskResumer =>
        (size_of::<TaskFrame_TaskResumer>(), align_of::<TaskFrame_TaskResumer>()),
      TaskFrameType::Independent =>
        (size_of::<TaskFrame_Independent>(), align_of::<TaskFrame_Independent>()),
    };
    let task_pivot = frame_size.next_multiple_of(env_align);
    let task_mem_sz = task_pivot + env_size;
    loop {
      let initial_ptr = this.free_slab_ptr;
      let frame_start = initial_ptr.byte_add(initial_ptr.align_offset(frame_align));
      let ptr_past_task = frame_start.byte_add(task_mem_sz);
      let right_bound = this.page_origin_addr.expose_addr() + 4096;
      let past_boundry = ptr_past_task.expose_addr() > right_bound;
      if past_boundry {
        let needs_new = self.release_page();
        if needs_new {
          let page = page_source.try_drain_page();
          let page = match page {
              Some(page) => page,
              None => {
                this.free_slab_ptr = null_mut();
                return None;
              },
          };
          self.set_page(page.get_ptr().cast());
        }
        continue;
      }
      (*this.page_origin_addr).ref_count.fetch_add(1, Ordering::Relaxed);
      let terminal_ptr = ptr_past_task.byte_add(ptr_past_task.align_offset(64));
      let exhausted = terminal_ptr.expose_addr() == right_bound;
      if exhausted {
        let needs_new = self.release_page();
        if needs_new {
          this.free_slab_ptr = null_mut();
        }
      } else {
        this.free_slab_ptr = terminal_ptr;
      }
      let ptr = frame_start.byte_add(task_pivot);
      let delta = terminal_ptr.expose_addr() - (ptr.expose_addr() & !((1 << 6) - 1));
      let slab_span = delta >> 6;
      let tfr = TaskFrameRef(ptr);
      return Some((tfr, slab_span as _));
    }
  } }
  #[must_use]
  pub fn dispose<T: DisposableMemoryObject>(object: T) -> Option<Block4KPtr>{ unsafe {
    let rptr = object.get_region_metadata_ptr();
    let i = (*rptr).ref_count.fetch_sub(1, Ordering::Relaxed) ;
    if i == 1 {
      return Some(Block4KPtr::new(rptr.cast::<()>()));
    } else {
      return None
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
  #[allow(dead_code)]
  fn new(ptr: *mut ()) -> Self {
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
    fn get_page_region_mtd(&self) -> *mut RegionMetadata {
      self.0.map_addr(|addr| (addr - 1) & !(SMALL_PAGE_SIZE - 1)).cast()
    }
    fn get_mtd_ptr<T:TaskFrameMarker>(&self) -> *mut T {
      unsafe { self.0.cast::<T>().sub(1) }
    }
    fn get_data_ptr(&self) -> *mut () {
      self.0.cast()
    }
}
impl DisposableMemoryObject for TaskFrameRef {
  fn get_region_metadata_ptr(&self) -> *mut RegionMetadata {
      self.get_page_region_mtd()
  }
}


struct IOPollingWorker {
  parent: *mut Worker,
  handle: Option<JoinHandle<()>>,
  rx_port: Receiver<IOPollingCallbackData>,
  tx_port: Sender<TaskRef>,
  should_stop: AtomicBool,
}
impl IOPollingWorker {
  fn start(&mut self) { unsafe {
    if let Some(_) = self.handle { return }
     let this = transmute_copy::<_, u64>(&self);
    self.handle = Some(spawn(move || {
      let this = transmute(this);
      io_polling_routine(this)
    }));
  } }
  fn stop(&mut self) {
    if let Some(thread) = self.handle.take() {
      self.should_stop.store(true, Ordering::Relaxed);
      thread.thread().unpark();
      self.handle.take().unwrap().join().unwrap();
    }
  }
  fn wakeup(&self) {
    self.handle.as_ref().unwrap().thread().unpark();
  }
}
struct IOPollingCallbackData {
  task_to_resume: TaskRef,
  target: RawFd,
  readable: bool,
  writeable: bool
}
fn io_polling_routine(worker: &mut IOPollingWorker) { {

  let mut io_pending_tasks = HashMap::<RawFd, TaskRef>::new();
  let poller = Poller::new().unwrap();
  let mut gathered_events = Vec::new();
  let mut batch_for_resume = Vec::new();

  'processing: loop {
    match worker.rx_port.try_recv() {
      Ok(data) => {
        if let None = io_pending_tasks.insert(data.target, data.task_to_resume) {
          let ev = Event {
            key: data.target as usize,
            readable: data.readable,
            writable: data.writeable
          };
          poller.add(data.target, ev).unwrap();
        };
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
      park(); // its okay if this gets unparked at random
      let time_to_die =
        worker.should_stop.compare_exchange(true, true, Ordering::Relaxed, Ordering::Relaxed);
      if time_to_die.is_ok() {
        return;
      }
      continue 'processing;
    }
    for event in &gathered_events {
      let fd = event.key as RawFd;
      let task = io_pending_tasks.remove(&fd).unwrap();
      poller.delete(fd).unwrap();
      batch_for_resume.push(task);
    }
    let no_resume_batch = batch_for_resume.is_empty();
    if no_resume_batch { continue }
    while let Some(task) = batch_for_resume.pop() {
      worker.tx_port.send(task).unwrap();
    }
    let parent = unsafe { &(*worker.parent) };
    parent.wakeup();
    batch_for_resume.clear();
  }
} }
fn blocking_runner_routine(
  runner: &mut BlockingRunner
) { unsafe {
  let mut outcome = runner.rx_port.try_iter();
  loop {
    match outcome.next() {
      None => {
        park();
        if runner.should_stop.load(Ordering::Relaxed) {
          return;
        }
      },
      Some(item) => {
        let task = item.task;
        let mtd = &mut* task.get_mtd_ptr::<TaskFrame_GenericView>();
        let ContinuationRepr::BlockingCall(fun) = mtd.continuation.continuation else {
          panic!("Expected a blocking operation")
        };
        let data_ptr = task.get_data_ptr();
        let handle = BlockingCallCtx(data_ptr);
        let next = fun(&handle);
        mtd.continuation = next;
        runner.tx_port.send(task).unwrap();
        (*runner.parent).wakeup();
      },
    }
  }
} }
struct BlockingRunner {
  parent: *mut Worker,
  thread: Option<JoinHandle<()>>,
  rx_port: Receiver<BlockingOperation>,
  tx_port: Sender<TaskRef>,
  should_stop: AtomicBool,
}
impl BlockingRunner {
  fn wakeup(&self) {
    self.thread.as_ref().unwrap().thread().unpark();
  }
  fn start(&mut self) { unsafe {
    if let Some(_) = self.thread { return }
    let this : u64 = transmute(addr_of_mut!(*self));
    let thread = thread::spawn(move ||{
      let this: &mut Self = transmute(this);
      blocking_runner_routine(this);
    });
    self.thread = Some(thread);
  } }
  fn stop(&mut self) {
    if let Some(thread) = self.thread.take() {
      self.should_stop.store(true, Ordering::Relaxed);
      thread.thread().unpark();
      thread.join().unwrap();
    };
  }
}
struct BlockingOperation {
  task: TaskRef,
}
struct WorkerSet(UnsafeCell<WorkerSetData>);
struct WorkerSetData {
  workers: Vec<Worker>,
  total_worker_count: u32,
  external_ref_count: AtomicU32, // references to this work group instance
  should_stop: AtomicBool,
  availability_map: AvailabilityMap
}
impl WorkerSet {
  fn inner(&self) -> &mut WorkerSetData {
    unsafe {&mut *self.0.get()}
  }
  fn get_worker_at_index(&self, index: usize) -> &mut Worker { unsafe {
    let this = &mut *self.0.get();
    this.workers.get_unchecked_mut(index)
  } }
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
  tasks: [TaskRef; TASK_LIST_PAGE_ITEM_LIMIT],
  array: [u64; TASK_LIST_PAGE_ITEM_LIMIT],
  uninit: ()
}
#[repr(C)]
struct TaskListPage {
  mtd: TaskListPageMtd,
  items: TaskListPageItemsRepr
}
static_assert!(size_of::<TaskListPage>() == SMALL_PAGE_SIZE);
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
  #[must_use]
  fn enque_one(
    &mut self,
    task: TaskRef,
    provider: &mut dyn FailablePageSource
  ) -> bool { unsafe {
    if self.read_ptr.is_null() {
      let page = provider.try_drain_page();
      let page = match page {
        Some(page) => page,
        None => return false,
      };
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
        let new = provider.try_drain_page();
        let new = match new {
          Some(new) => new,
          None => return false,
        };
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
    let ptr = write_ptr.cast::<TaskRef>();
    ptr.write(task);
    self.write_ptr = ptr.add(1).cast();
    self.item_count += 1;
    return true;
  } }
  #[allow(dead_code)]
  fn deque_one(
    &mut self
  ) -> Option<(TaskRef, Option<Block4KPtr>)> { unsafe {
    let count = self.item_count;
    if count == 0 { return None; }
    let mut page = None;
    let mut rp = self.read_ptr.cast::<TaskRef>();
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
  let mut alloc = RootAllocator::new(false);
  let mut list = TaskList::new();
  const LIMIT : usize = 1_000_000;
  for i in 0 .. LIMIT {
    let _ = list.enque_one(unsafe { transmute(i) }, &mut alloc);
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
  let mut alloc = RootAllocator::new(false);
  let mut list = TaskList::new();
  for i in 0 .. 32usize * 2 {
    let _ = list.enque_one(unsafe { transmute(i) }, &mut alloc);
    let pack = list.dequeue_pack().unwrap();
    assert!(pack.0.to_array()[0] == i as _);
    println!("{:?} {}", pack, i);
  }
}
#[test]
fn list_pack_deque_works2() {
  let mut alloc = RootAllocator::new(false);
  let mut list = TaskList::new();
  for i in 0 .. 512usize {
    let _ = list.enque_one(unsafe { transmute(i) }, &mut alloc);
  }
  for i in 0 .. (512 / 16) {
    let pack = list.dequeue_pack().unwrap();
    println!("{:?} {}", pack, i);
    let _ = list.enque_one(unsafe { transmute(11usize) }, &mut alloc);
  }
  println!("___DELIMITER___");
  for i in 0 .. 2 {
    let pack = list.dequeue_pack().unwrap();
    assert!(pack.0 == Simd::splat(11));
    println!("{:?} ix {}", pack, i)
  }
}
#[repr(C)] #[derive(Clone, Copy)]
union ImmidiateTasks {
  simd: Simd<u64, 16>,
  tasks: [TaskRef;16],
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
  #[must_use]
  fn enque(&mut self, new_item: TaskRef, ps: &mut dyn FailablePageSource) -> bool {
    self.task_list.enque_one(new_item, ps)
  }
  fn deque_one(&mut self) -> Option<(TaskRef, Option<Block4KPtr>)> {
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
    let task = unsafe { self.immidiate_items.tasks[count as usize] };
    self.imm_count = count;
    return Some((task, mem));
  }
  fn set_pack(&mut self, pack: Simd<u64,16>, count: usize) {
    self.immidiate_items.simd = pack;
    self.imm_count = count as _;
  }
}

#[derive(Debug)]
struct AvailabilityMap {
  inlines: AtomicU64,
  outlines: Vec<AtomicU64>
}
impl AvailabilityMap {
  fn new(
    max_count: usize,
  ) -> Self {
    let inst = match max_count {
      0 ..= 63 => {
        let indicies = u64::MAX << max_count;
        Self { inlines: AtomicU64::new(indicies), outlines: Vec::new() }
      },
      64 => {
        Self { inlines: AtomicU64::new(0), outlines: Vec::new() }
      },
      _ => {
        let mut v = Vec::new();
        let mut k = max_count - 64;
        loop {
          if k >= 64 {
            v.push(AtomicU64::new(0));
            k -= 64;
            continue;
          } else {
            let indicies = u64::MAX << k;
            v.push(AtomicU64::new(indicies));
            break;
          }
        }
        Self { inlines: AtomicU64::new(0), outlines: v }
      }
    };
    return inst;
  }
  fn mark_as_free(&self, index: usize) {
    let src = if index < 64 {
      &self.inlines
    } else {
      &self.outlines[(index >> 6) - 1]
    };
    let mask = !(1 << (index & ((1 << 6) - 1)));
    let _ = src.fetch_and(mask, Ordering::Relaxed);
  }
  #[allow(dead_code)]
  fn mark_as_taken(&self, index: usize) {
    let src = if index < 64 {
      &self.inlines
    } else {
      &self.outlines[(index >> 6) - 1]
    };
    let mask = 1 << (index & ((1 << 6) - 1));
    let _ = src.fetch_or(mask, Ordering::Relaxed);
  }
  fn try_find_free_index(&self) -> Option<usize> {
    fn pick_index(
      source: &AtomicU64
    ) -> Option<usize> {
      let mut map = source.load(Ordering::Relaxed);
      loop {
        let index = map.trailing_ones();
        if index == 64 { return None }
        let mask = 1u64 << index;
        let prior = source.fetch_or(mask, Ordering::Relaxed);
        let taken = prior & mask != 0;
        if taken { map = prior; continue; }
        return Some(index as _)
      }
    }
    let max = self.outlines.len();
    let mut ix = 0;
    let mut source = &self.inlines;
    loop {
      if let Some(i) = pick_index(source) { return Some(i + (64 * ix)) };
      if ix == max { return None }
      source = &self.outlines[ix];
      ix += 1;
    }
  }
}

#[test]
fn av_map_init() {

  let smth = AvailabilityMap::new(64);
  assert!(smth.inlines.load(Ordering::Relaxed) == 0);
  assert!(smth.outlines.is_empty());

  let smth = AvailabilityMap::new(64 + 1);
  assert!(smth.inlines.load(Ordering::Relaxed) == 0);
  assert!(smth.outlines.len() == 1);
  assert!(smth.outlines[0].load(Ordering::Relaxed) == (!0u64) << 1);
  // println!("{:#?}", smth)

  let smth = AvailabilityMap::new(64 * 2 + 1);
  assert!(smth.inlines.load(Ordering::Relaxed) == 0);
  assert!(smth.outlines.len() == 2);
  assert!(smth.outlines[0].load(Ordering::Relaxed) == 0);
  assert!(smth.outlines[1].load(Ordering::Relaxed) == (!0u64) << 1);
  // println!("{:#?}", smth)
}
#[test]
fn av_map_mark() {
  let smth = AvailabilityMap::new(64 * 2 + 1);
  for i in 0 .. 64 {
    smth.inlines.store(u64::MAX, Ordering::Relaxed);
    smth.mark_as_free(i);
    assert!(smth.inlines.load(Ordering::Relaxed) == u64::MAX & !(1 << i));
  }
  smth.outlines[1].store(u64::MAX, Ordering::Relaxed);
  smth.mark_as_free(64 * 2);
  assert!(smth.outlines[1].load(Ordering::Relaxed) == u64::MAX & !1);
}
#[test]
fn index_finding() {
  let smth = AvailabilityMap::new(64 * 2 + 1);
  let i = smth.try_find_free_index().unwrap();
  assert!(i == 0);

  let smth = AvailabilityMap::new(64 * 2 + 1);
  smth.inlines.store(u64::MAX, Ordering::Relaxed);
  smth.outlines[0].store(u64::MAX, Ordering::Relaxed);
  let i = smth.try_find_free_index().unwrap();
  assert!(i == 128);
  smth.mark_as_free(i);
  assert!(smth.outlines[1].load(Ordering::Relaxed) == u64::MAX << 1);
}
#[test]
fn bangin_it() {
  let thread_count = 64 * 2;
  let smth = AvailabilityMap::new(thread_count);
  let sync = AtomicBool::new(false);
  std::thread::scope(|h|{
    for _ in 0 .. thread_count {
      let sync = &sync;
      let smth = &smth;
      h.spawn(move ||{
        while !sync.load(Ordering::Relaxed) {}
        smth.try_find_free_index();
      });
    }
    sync.store(true, Ordering::Release);
  });
  assert!(smth.inlines.load(Ordering::Relaxed) == u64::MAX);
  for i in smth.outlines {
    assert!(i.load(Ordering::Relaxed) == u64::MAX);
  }
}
#[repr(C)]
union SharePort {
  tasks: ImmidiateTasks,
  free_page: Block4KPtr
}

#[repr(C)]
struct Worker {
  runner_handle: Option<JoinHandle<()>>,
  init_finished: AtomicBool,
  work_group: *mut WorkGroup,
  index: usize,
  core_pin_id: core_affinity::CoreId,
  share_port: SharePort,
  atomic_flags: AtomicU64,
  futex_address: AtomicU32,
}
impl Worker {
  fn advertise_as_available(&self) { unsafe {
    let map = &(*(*self.work_group).worker_set.0.get()).availability_map;
    map.mark_as_free(self.index);
  } }
  fn get_root_allocator(&self) -> &RootAllocator {
    unsafe{&(*self.work_group).ralloc}
  }
  fn wakeup(&self) {
    assert!(self.was_started(), "Cant wake up uinited worker");
    futex::futex_wake(&self.futex_address);
  }
  #[inline]
  fn mark_work_given(&self) {
    let (_, counter) = unsafe{&*addr_of!(self.atomic_flags).cast::<(AtomicU32, AtomicU32)>()};
    counter.fetch_add(1, Ordering::Release);
  }
  fn check_salt(&self, salt:u32) -> u32 {
    let (_,counter) = unsafe{&*addr_of!(self.atomic_flags).cast::<(AtomicU32, AtomicU32)>()};
    match counter.compare_exchange(salt, salt, Ordering::Relaxed, Ordering::Relaxed) {
        Ok(_) => salt,
        Err(real) => real,
    }
  }
  const WAS_STARTED: u64 = 1;
  fn was_started(&self) -> bool {
    match self.atomic_flags.compare_exchange(0, 0, Ordering::Relaxed, Ordering::Acquire) {
        Ok(_) => return false,
        Err(real) => {
          return real & Self::WAS_STARTED != 0;
        },
    }
  }
  const NEED_MEM:u64 = 1 << 1;
  fn mark_need_mem(&self) {
    self.atomic_flags.fetch_or(Self::NEED_MEM, Ordering::Relaxed);
  }
  fn try_volunteer_for_mem_resupply(&self) -> bool {
    let val = self.atomic_flags.fetch_and(!Self::NEED_MEM, Ordering::Relaxed);
    return if val & Self::NEED_MEM == 0 { false }
           else { true };
  }
  fn try_start(&mut self) -> bool { unsafe {
    let prior = self.atomic_flags.fetch_or(Self::WAS_STARTED, Ordering::Relaxed);
    if prior & Self::WAS_STARTED != 0 {
      return true;
    }
    let copy = transmute_copy::<_, u64>(&self);
    let thread = thread::spawn(move ||{
      let ptr = transmute::<_, &mut Worker>(copy);
      worker_processing_routine(ptr);
    });
    self.runner_handle = Some(thread);
    return false;
  } }
}

#[repr(C)]
struct FreePageList {
  next_page: *mut FreePageList,
  bytes: [u8; SMALL_PAGE_SIZE - size_of::<*mut FreePageList>()]
}
struct PageManInner {
  free_pages: *mut FreePageList,
  root_allocator: *const RootAllocator
}
struct PageStorage(UnsafeCell<PageManInner>);
impl PageStorage {
  fn new(
    root_allocator: &RootAllocator
  ) -> Self {
    Self(UnsafeCell::new(PageManInner {
      free_pages: null_mut(),
      root_allocator
    }))
  }
  fn has_mem(&self) -> bool {
    let this = unsafe{&mut*self.0.get()};
    this.free_pages != null_mut()
  }
  fn try_provision_mem(&self) -> bool { unsafe {
    let this = &mut*self.0.get();
    let has_some = this.free_pages != null_mut();
    if !has_some {
      match (*this.root_allocator).try_get_page_wait_tolerable() {
        Ok(mem) => {
          self.store_page(mem);
          return true;
        },
        Err(_) => {
          return false;
        },
      }
    }
    return has_some;
  } }
  fn store_page(&self, page:Block4KPtr) { unsafe {
    let this = &mut*self.0.get();
    let page = page.get_ptr().cast::<FreePageList>();
    (*page).next_page = null_mut();
    if !this.free_pages.is_null() {
      (*this.free_pages).next_page = page;
    }
    this.free_pages = page;
  } }
  fn try_get_page(&self) -> Option<Block4KPtr> {
    let this = unsafe{&mut*self.0.get()};
    let head = this.free_pages;
    if head.is_null() { return None }
    let next = unsafe { (*head).next_page };
    this.free_pages = next;
    return Some(Block4KPtr::new(head.cast()))
  }
  fn dispose_mem(self) { unsafe {
    let this = &mut*self.0.get();
    let mut page = this.free_pages;
    loop {
      if page.is_null() { return; }
      let next = (*page).next_page;
      let out = libc::munmap(page.cast(), SMALL_PAGE_SIZE);
      assert!(out == 0, "Failed to unmap mem?? 0_o\naddress was {:?}", page);
      page = next;
    }
  } }
}
impl FailablePageSource for PageStorage {
  fn try_drain_page(&self) -> Option<Block4KPtr> {
    let a = self.try_get_page();
    if a.is_some() { return a }
    unsafe {
      let b = (*(*self.0.get()).root_allocator).try_get_page_wait_tolerable();
      match b {
        Ok(mem) => return Some(mem),
        Err(_) => return None,
      }
    }
  }
}
impl PageSink for PageStorage {
    fn give_page_for_recycle(&mut self, page: Block4KPtr) {
      self.store_page(page)
    }
}
enum ExecState {
  Fetch, Sleep, Execute, Shutdown
}

const TASK_CACHE_SIZE:usize = 16;

fn worker_processing_routine(worker_: *mut Worker) { unsafe {

  let this_worker = &mut*worker_;
  let workgroup = &*this_worker.work_group;

  let ok = core_affinity::set_for_current(this_worker.core_pin_id);
  assert!(ok, "failed to pin worker {} to core {:?}", this_worker.index, this_worker.core_pin_id);

  let allocator = WorkerLocalSlabAllocator::new();
  let mut task_set = TaskSet::new();
  let mut page_man_ = PageStorage::new(this_worker.get_root_allocator());

  let mut current_task : TaskRef = TaskRef::new_null();

  let mut immidiate_state = ImmidiateState {
    spawned_subtask_count: 0,
    current_task: addr_of!(current_task)
  };

  let task_context = TaskCtx(UnsafeCell::new(TaskContextInternals {
    immidiate_state: addr_of_mut!(immidiate_state),
    page_man: addr_of_mut!(page_man_),
    allocator: addr_of!(allocator),
    task_set: addr_of_mut!(task_set)
  }));

  let mut pending_ops_count = 0;

  let (bc_ftx, bc_frx) = std::sync::mpsc::channel();
  let (bc_btx, bc_brx) = std::sync::mpsc::channel();
  let mut blocking_runner = BlockingRunner {
    parent: worker_,
    thread: None,
    rx_port: bc_frx,
    tx_port: bc_btx,
    should_stop: AtomicBool::new(false),
  };
  let (io_ftx, io_frx) = std::sync::mpsc::channel();
  let (io_btx, io_brx) = std::sync::mpsc::channel();
  let mut io_poller = IOPollingWorker {
    parent: worker_,
    handle: None,
    rx_port: io_frx,
    tx_port: io_btx,
    should_stop: AtomicBool::new(false)
  };

  let mut orphan_task = None;
  let mut salt = 0;


  let mut exec_state = ExecState::Fetch;
  'dispatch:loop {
    match exec_state {
      ExecState::Fetch => {
        if let Some((new_task, free_mem)) = (task_set).deque_one() {
          current_task = new_task;
          if let Some(free_mem) = free_mem {
            page_man_.store_page(free_mem);
          }
          exec_state = ExecState::Execute;
          continue 'dispatch;
        }
        let new_salt = this_worker.check_salt(salt);
        if new_salt != salt {
          let tasks = this_worker.share_port.tasks.simd;
          let count = tasks.simd_eq(Simd::splat(0)).to_bitmask();
          let count = count.count_zeros();
          (task_set).set_pack(tasks, count as usize);
          salt = new_salt;
          exec_state = ExecState::Fetch;
          continue 'dispatch;
        }
        if !page_man_.try_provision_mem() {
          // other workers would give
          this_worker.mark_need_mem();
          exec_state = ExecState::Sleep;
          continue 'dispatch;
        }
        if let Some(orphan) = orphan_task.take() {
          let ok = (task_set).enque(orphan, &mut page_man_);
          assert!(ok);
          exec_state = ExecState::Execute;
          continue 'dispatch;
        };
        if let Ok(new_task) = bc_brx.try_recv() {
          let ok = (task_set).enque(new_task, &mut page_man_);
          assert!(ok);
          pending_ops_count -= 1;
          exec_state = ExecState::Execute;
          continue 'dispatch;
        }
        if let Ok(new_task) = io_brx.try_recv() {
          let ok = (task_set).enque(new_task, &mut page_man_);
          assert!(ok);
          pending_ops_count -= 1;
          exec_state = ExecState::Execute;
          continue 'dispatch;
        }
        this_worker.advertise_as_available();
        exec_state = ExecState::Sleep;
        continue 'dispatch;
      },
      ExecState::Sleep => {
        let time_to_die = (*workgroup.worker_set.0.get()).should_stop.compare_exchange(true, true, Ordering::Relaxed, Ordering::Relaxed).is_ok();
        if time_to_die && pending_ops_count == 0 {
          exec_state = ExecState::Shutdown;
          continue 'dispatch;
        }
        if page_man_.has_mem() {
          give_away_mem(&page_man_, workgroup);
          futex::futex_wait(&this_worker.futex_address, 0, Some(Duration::from_micros(1000)));
        } else {
          futex::futex_wait(&this_worker.futex_address, 0, None);
        }
        exec_state = ExecState::Fetch;
        continue 'dispatch;
      },
      ExecState::Shutdown => {
        page_man_.dispose_mem();
        blocking_runner.stop();
        io_poller.stop();
        return;
      }
      ExecState::Execute => {
        let frame_ref =
          &mut *current_task.get_mtd_ptr::<TaskFrame_GenericView>();
        let continuation = frame_ref.continuation.continuation;
        match continuation {
          ContinuationRepr::BlockingCall(_) => {
            let bop = BlockingOperation {
              task: current_task,
            };
            bc_ftx.send(bop).unwrap();
            blocking_runner.start();
            blocking_runner.wakeup();
            pending_ops_count += 1;
            exec_state = ExecState::Fetch;
            continue 'dispatch;
          }
          ContinuationRepr::Then(thunk) => {
            let next = thunk(&task_context);
            frame_ref.continuation = next;
            let produced_subtasks = immidiate_state.spawned_subtask_count != 0;
            if produced_subtasks {
              frame_ref.subtask_count.store(
                immidiate_state.spawned_subtask_count, Ordering::Relaxed);
              share_work(this_worker, &mut task_set, &mut page_man_);
              task_context.clear_dirty_state();
              // last child awakes parent task
            } else {
              // repush task. we want other tasks to run
              let ok = task_set.enque(current_task, &mut page_man_);
              if !ok {
                // we dont have mem
                // and we must not loose current task
                orphan_task = Some(current_task);
                this_worker.mark_need_mem();
                exec_state = ExecState::Sleep;
                continue 'dispatch;
              }
            }
            exec_state = ExecState::Fetch;
            continue 'dispatch;
          },
          ContinuationRepr::Done => {
            match current_task.get_frame_type() {
              TaskFrameType::ThreadResumer => {
                let frame_ref = &*current_task.get_mtd_ptr::<TaskFrame_ThreadResumer>();
                futex::futex_wake(frame_ref.wake_address);
                exec_state = ExecState::Fetch;
                continue 'dispatch;
              },
              TaskFrameType::TaskResumer => {
                let frame_ref = &*current_task.get_mtd_ptr::<TaskFrame_TaskResumer>();
                let parked_task = frame_ref.parent_task;
                if let Some(page) = WorkerLocalSlabAllocator::dispose(current_task) {
                  page_man_.store_page(page)
                }
                let parent_frame = &*parked_task.get_mtd_ptr::<TaskFrame_GenericView>();
                let remaining_subtasks_count =
                  parent_frame.subtask_count.fetch_sub(1, Ordering::Relaxed);
                let last_child = remaining_subtasks_count == 1;
                if last_child {
                  current_task = parked_task;
                  continue 'dispatch;
                } else {
                  exec_state = ExecState::Fetch;
                  continue 'dispatch;
                }
              },
              TaskFrameType::Independent => {
                if let Some(page) = WorkerLocalSlabAllocator::dispose(current_task) {
                  page_man_.store_page(page)
                };
                exec_state = ExecState::Fetch;
                continue 'dispatch;
              },
            }
          },
          ContinuationRepr::AwaitIO(fd, r, w, next) => {
            let frame_ref = &mut *current_task.get_mtd_ptr::<TaskFrame_GenericView>();
            frame_ref.continuation = Continuation {
              continuation: ContinuationRepr::Then(next)
            };
            let item = IOPollingCallbackData {
              task_to_resume: current_task,
              target: fd, readable: r, writeable: w
            };
            io_ftx.send(item).unwrap();
            io_poller.start();
            io_poller.wakeup();
            pending_ops_count += 1;
            exec_state = ExecState::Fetch;
            continue 'dispatch;
          },
        }
      },
    }
  }

} }

fn share_work(
  src_worker: &mut Worker,
  workset: &mut TaskSet,
  page_sink: &mut dyn PageSink
) { unsafe {
  let local_workset = &mut *workset;
  let all_workers = &mut (*src_worker.work_group).worker_set;
  let av_map = &(*(*src_worker.work_group).worker_set.0.get()).availability_map;
  loop {
    let local_item_count = local_workset.item_count();
    let too_few_tasks = TASK_CACHE_SIZE >= local_item_count;
    if too_few_tasks { return; }

    let Some(index) = av_map.try_find_free_index() else { return };

    let free_worker = all_workers.get_worker_at_index(index);

    let (pack, len, mem) = local_workset.task_list.dequeue_pack().unwrap();
    if let Some(mem) = mem {
      page_sink.give_page_for_recycle(mem)
    }
    let tasks = pack.to_array();
    for i in 0 .. len {
      let task = tasks[i];
      let task = transmute::<_, TaskRef>(task);
      let span = task.get_mtd_ptr::<TaskFrame_GenericView>();
      let size = (*span).slab_span as usize * 64;
      let ptr = task.get_data_ptr().map_addr(|p|p & !((1 << 6) - 1)).cast::<u8>();
      force_publish_stores_on_location!(ptr, size, 64);
    }
    free_worker.share_port.tasks.simd = pack;
    free_worker.mark_work_given();
    free_worker.try_start();
    free_worker.wakeup();
  }
} }

fn give_away_mem(
  page_source: &PageStorage,
  workgroup: &WorkGroup
) {
  assert!(page_source.has_mem());
  let workset = &workgroup.worker_set;
  for ix in 0 .. workset.inner().total_worker_count {
    let worker = workset.get_worker_at_index(ix as _);
    let need_mem = worker.try_volunteer_for_mem_resupply();
    if !need_mem { continue; }
    let page = match page_source.try_get_page() {
      Some(page) => page,
      None => {
        worker.mark_need_mem();
        return;
      },
    };
    worker.share_port.free_page = page;
    worker.wakeup();
  }
}

struct ImmidiateState {
  current_task: *const TaskRef,
  spawned_subtask_count: u32,
}
pub struct TaskCtx(UnsafeCell<TaskContextInternals>);
struct TaskContextInternals {
  immidiate_state: *mut ImmidiateState,
  page_man: *mut PageStorage,
  allocator: *const WorkerLocalSlabAllocator,
  task_set: *mut TaskSet
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

impl TaskCtx {
  pub fn acccess_capture_as_raw(&self) -> *mut () { unsafe {
    let this = &mut *self.0.get();
    let data_ptr = (*(*this.immidiate_state).current_task).get_data_ptr();
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
  #[must_use]
  pub fn spawn_subtask<T: Send>(&self, capture: T, operation: Thunk) -> bool {
    let ok = self.spawn_task_common_impl(
      addr_of!(capture).cast::<()>(),
      size_of::<T>(), align_of::<T>(), operation, false);
    if !ok {
      drop(capture);
      return ok;
    } else {
      forget(capture);
      return ok;
    }
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
  ) -> bool { unsafe {
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
    let pm = &mut*this.page_man;
    let ok = pm.try_provision_mem();
    if !ok { return false }
    let outcome = (*this.allocator).alloc_task_frame(
      env_align,
      env_size,
      pm,
      frame_type
    );
    if outcome.is_none() {
      return false;
    }
    let (frame_ref, slab_span) = outcome.unwrap();
    if detached {
      let frame_ptr = frame_ref.get_mtd_ptr::<TaskFrame_Independent>();
      frame_ptr.write(TaskFrame_Independent {
        continuation: Continuation { continuation: ContinuationRepr::Then(thunk) },
        subtask_count: AtomicU32::new(0),
        slab_span: slab_span
      })
    } else {
      let frame_ptr = frame_ref.get_mtd_ptr::<TaskFrame_TaskResumer>();
      frame_ptr.write(TaskFrame_TaskResumer {
        parent_task: immidiate_state_ref.current_task.read(),
        continuation: Continuation { continuation: ContinuationRepr::Then(thunk) },
        subtask_count: AtomicU32::new(0),
        slab_span: slab_span
      })
    }
    let data_ptr = frame_ref.get_data_ptr();
    copy_nonoverlapping(env_data.cast::<u8>(), data_ptr.cast::<u8>(), env_size);

    let subtask = TaskRef::new(frame_ref, frame_type);
    let task_set = &mut *(*this).task_set;
    let ok = task_set.enque(subtask, pm);
    if !ok {
      if let Some(mem) = WorkerLocalSlabAllocator::dispose(frame_ref) {
        (*this.page_man).store_page(mem)
      };
      return false;
    }
    return true;
  }; }
  fn clear_dirty_state(&self) {
    let this = unsafe { &mut *self.0.get() };
    let imm_ctx = unsafe{&mut *this.immidiate_state};
    imm_ctx.spawned_subtask_count = 0;
  }
}
pub struct BlockingCallCtx(*mut ());
impl BlockingCallCtx {
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
  BlockingCall(fn (&BlockingCallCtx) -> Continuation),
}
impl Continuation {
  pub fn run_blocking(
    operation: fn (&BlockingCallCtx) -> Continuation
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
type Thunk = fn (&TaskCtx) -> Continuation;

#[derive(Debug, Clone, Copy)] #[repr(u8)]
enum TaskFrameType {
  ThreadResumer,
  TaskResumer,
  Independent
}
trait TaskFrameMarker {}
#[repr(C)] #[derive(Debug)] #[allow(non_camel_case_types)]
struct TaskFrame_ThreadResumer {
  wake_address: *const AtomicU32,
  continuation: Continuation,
  slab_span:u8,
  subtask_count: AtomicU32,
}
impl TaskFrameMarker for TaskFrame_ThreadResumer {}
#[repr(C)] #[derive(Debug)] #[allow(non_camel_case_types)]
struct TaskFrame_TaskResumer {
  parent_task: TaskRef,
  continuation: Continuation,
  slab_span:u8,
  subtask_count: AtomicU32,
}
impl TaskFrameMarker for TaskFrame_TaskResumer {}
#[repr(C)] #[derive(Debug)] #[allow(non_camel_case_types)]
struct TaskFrame_Independent {
  continuation: Continuation,
  slab_span:u8,
  subtask_count: AtomicU32,
}
impl TaskFrameMarker for TaskFrame_Independent {}
#[repr(C)] #[derive(Debug)] #[allow(non_camel_case_types)]
struct TaskFrame_GenericView {
  continuation: Continuation,
  slab_span:u8,
  subtask_count: AtomicU32,
}
impl TaskFrameMarker for TaskFrame_GenericView {}

#[repr(C)] #[repr(align(8))] #[derive(Debug, Clone, Copy)]
struct TaskRef(u64);
impl TaskRef {
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
  fn get_data_ptr(&self) -> *mut () {
    (self.0 >> 8) as _
  }
  fn get_mtd_ptr<T:TaskFrameMarker>(&self) -> *mut T {
    unsafe { ((self.0 >> 8) as *mut T).sub(1) }
  }
  fn new_null() -> Self {
    Self(0)
  }
  fn get_region_metadata_ptr_(&self) -> *mut RegionMetadata {
    self.get_data_ptr().map_addr(|addr| (addr - 1) & !(SMALL_PAGE_SIZE - 1)).cast()
  }
}
impl DisposableMemoryObject for TaskRef {
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
  #[inline(always)]
  fn get_core_ids() -> Vec<CoreId> {
    core_affinity::get_core_ids().unwrap_or_else(||{
      panic!("cannot retrieve core indicies")
    })
  }
  #[allow(dead_code)]
  fn new_with_thread_count(
    thread_count:usize
  ) -> WorkGroupRef {
    let core_ids = Self::get_core_ids();
    let total_core_count = core_ids.len();
    assert!(thread_count != 0 || thread_count <= total_core_count);
    let enable_huge = match std::env::var("HUGE_PAGES") {
        Ok(str) if str == "1" => true,
        _ => false,
    };
    return Self::new_common_impl(&core_ids[..thread_count], enable_huge)
  }
  pub fn new() -> WorkGroupRef {
    let () = {
      let res = unsafe { core::arch::x86_64::__cpuid(1) };
      let cl_flush_enabled = (res.edx >> 19) & 1 == 1;
      assert!(cl_flush_enabled, "CPU doesnt have clflush instruction.");
      let cl_size = (res.ebx >> 8 & (1 << 7) - 1) * 8;
      let size_ok = cl_size >= 64;
      assert!(size_ok, "Unexpected cache line size.");
    };
    let core_ids = Self::get_core_ids();
    let enable_huge = match std::env::var("HUGE_PAGES") {
        Ok(str) if str == "1" => true,
        _ => false,
    };
    return Self::new_common_impl(&core_ids[..], enable_huge)
  }
  #[inline(always)]
  fn new_common_impl(
    core_ids: &[core_affinity::CoreId],
    enable_huge: bool
  ) -> WorkGroupRef { unsafe {
    let total_core_count = core_ids.len();
    let worker_count = total_core_count;
    type WG = WorkGroup;
    let boxed = alloc(Layout::new::<WG>());
    let boxed = boxed.cast::<WG>();

    let mut workers = Vec::new();
    workers.reserve(worker_count);
    for wix in 0 .. worker_count {
      let core_ix = core_ids[wix as usize];
      let worker = Worker {
        index: wix,
        runner_handle: None,
        work_group: boxed,
        core_pin_id: core_ix,
        init_finished: AtomicBool::new(false),
        atomic_flags: AtomicU64::new(0),
        share_port: SharePort {
          tasks: ImmidiateTasks { simd: Simd::splat(0) }
        },
        futex_address: AtomicU32::new(0),
      };
      workers.push(worker);
    }
    boxed.write(WorkGroup {
      ralloc:RootAllocator::new(enable_huge),
      worker_set: WorkerSet(UnsafeCell::new(WorkerSetData {
        workers: workers,
        total_worker_count: worker_count as u32,
        should_stop: AtomicBool::new(false),
        external_ref_count: AtomicU32::new(1), // +1 because this ref exist
        availability_map: AvailabilityMap::new(total_core_count),
      })),
    });
    hard_mfence!();
    return WorkGroupRef(boxed)
  } }
}
pub struct WorkGroupRef(*mut WorkGroup);
impl WorkGroupRef {
  fn try_find_free_worker(&self) -> Option<&mut Worker> {
    let w = unsafe { &mut (*(*self.0).worker_set.0.get()) };
    let ix = w.availability_map.try_find_free_index()?;
    let w = (w.workers).get_mut(ix).unwrap();
    return Some(w);
  }
  pub fn submit_and_await<Env: Send>(&self, capture: Env, operation: Thunk) { unsafe {
    let worker = loop {
      if let Some(w) = self.try_find_free_worker() { break w } else { yield_now() }
    };

    let flag = AtomicU32::new(0);

    #[repr(C)] #[repr(align(64))]
    struct Storage<T>(
      [u8;64 - size_of::<TaskFrame_ThreadResumer>()],
      TaskFrame_ThreadResumer,
      T
    );
    let span = size_of::<Storage<Env>>() >> 6;
    let mut data = Storage(
      [0;_],
      TaskFrame_ThreadResumer {
        continuation: Continuation { continuation: ContinuationRepr::Then(operation) },
        slab_span: span as u8,
        subtask_count: AtomicU32::new(0),
        wake_address: addr_of!(flag),
      },
      capture
    );
    let ptr = addr_of_mut!(data.2).cast::<u8>();
    let mut mptr = ptr;
    for _ in 0 .. span {
      core::arch::x86_64::_mm_clflush(mptr);
      mptr = mptr.byte_add(64);
    }
    let task = TaskFrameRef(ptr);
    let task_ref = TaskRef::new(task, TaskFrameType::ThreadResumer);
    worker.share_port.tasks.simd = Simd::splat(0);
    worker.share_port.tasks.tasks[0] = task_ref;
    core::arch::x86_64::_mm_clflush(addr_of!(worker.share_port.tasks.tasks[0]).cast());
    worker.mark_work_given();
    worker.try_start();
    worker.wakeup();
    futex::futex_wait(&flag, 0, None);
    forget(data.2);
  } }

  pub fn clone_ref(&self) -> Self { unsafe {
    (*(*self.0).worker_set.0.get()).external_ref_count.fetch_add(1, Ordering::AcqRel);
    return WorkGroupRef(self.0)
  } }
}
impl Drop for WorkGroupRef {
  fn drop(&mut self) { unsafe {
    let prior = (*(*self.0).worker_set.0.get()).external_ref_count.fetch_sub(1, Ordering::Relaxed);
    if prior == 1 {
      let workeset = &mut *(*self.0).worker_set.0.get();
      workeset.should_stop.store(true, Ordering::Relaxed);
      force_pusblish_stores!();
      let total_worker_count = workeset.total_worker_count;
      for ix in 0 .. total_worker_count {
        let wref = (*self.0).worker_set.get_worker_at_index(ix as _);
        if wref.was_started() {
          wref.wakeup();
          wref.runner_handle.take().unwrap().join().unwrap()
        }
      }
    }
  } }
}


#[test]
fn test_trivial_tasking() {
  static mut EVIL_FORMULA : &str = "";
  fn single_print(_: &TaskCtx) -> Continuation {
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
  fn parent(ctx: &TaskCtx) -> Continuation {
    let ok = ctx.spawn_subtask((), child);
    assert!(ok);
    return Continuation::done()
  }
  fn child(_: &TaskCtx) -> Continuation {
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
  fn parent(ctx: &TaskCtx) -> Continuation {
    let frame = ctx.access_capture_as_init::<ParentData>();
    for _ in 0 .. LIMIT {
      let ok = ctx.spawn_subtask(&frame.counter, child);
      assert!(ok);
    }
    return Continuation::then(check)
  }
  fn child(ctx: &TaskCtx) -> Continuation {
    let counter = ctx.access_capture_as_init::<&AtomicU64>();
    let _ = counter.fetch_add(1, Ordering::Relaxed);
    return Continuation::done();
  }
  fn check(ctx: &TaskCtx) -> Continuation {
    println!("we are here!");
    let frame = ctx.access_capture_as_init::<ParentData>();
    let val = frame.counter.load(Ordering::Relaxed);

    assert!(val == LIMIT);

    return Continuation::done()
  }

  let frame = ParentData { counter: AtomicU64::new(0) };
  let work_group = WorkGroup::new();
  work_group.submit_and_await(frame, parent);
}

#[test]
fn heavy_spawning() {
  let wg = WorkGroup::new() ;
  let counter = AtomicU64::new(0) ;
  const LIMIT : u64 = 1_000_000 ;
  struct Data<'i> { counter_ref: &'i AtomicU64, start_time: Option<Instant> }
  wg.submit_and_await(Data {counter_ref:&counter, start_time:None}, |ctx| {
      let data = ctx.access_capture_as_init::<Data>();
      data.start_time = Some(Instant::now());
      for _ in 0 .. LIMIT {
          let ptr = data.counter_ref;
          let ok = ctx.spawn_subtask(ptr, |ctx|{
              let ptr = ctx.access_capture_as_init::<&AtomicU64>();
              ptr.fetch_add(1, Ordering::Relaxed);
              return Continuation::done()
          });
          assert!(ok);
      }
      return Continuation::then(|ctx| {
        let data = ctx.access_capture_as_init::<Data>();
        let el = data.start_time.unwrap().elapsed();
        println!("time spent {:?}", el);
        return Continuation::done();
      })
  });
  let val = counter.load(Ordering::Relaxed);
  assert!(val == LIMIT);
}


#[test]
fn subsyncing() {
  const LIMIT : usize = 1_000_000;
  let wg = WorkGroup::new_with_thread_count(1);
  let mut st = Vec::<[usize;16]>::new();
  st.reserve(LIMIT);
  struct Data { start_time: Option<Instant>, items: Vec<[usize;16]> }
  wg.submit_and_await(Data {items: st, start_time:None}, |ctx| {
      let data = ctx.access_capture_as_init::<Data>();
      data.start_time = Some(Instant::now());
      let ptr = data.items.as_mut_ptr();
      for i in 0 .. LIMIT {
          let ptr = unsafe{ ptr.add(i) };
          let addr : usize = unsafe { transmute(ptr) };
          let ok = ctx.spawn_subtask((addr, i), |ctx| {
              let ptr = ctx.access_capture_as_init::<(usize, usize)>();
              let addr = ptr.0;
              let i = ptr.1;
              // println!("Subtask {}", i);
              let item_ptr : *mut [usize;16] = unsafe { transmute(addr) };
              unsafe {item_ptr.write([i;16])};
              return Continuation::done()
          });
          assert!(ok);
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
  fn sync_loop(ctx: &TaskCtx) -> Continuation {
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
  fn after_blocking(ctx: &TaskCtx) -> Continuation {
    let cpt = ctx.access_capture_as_init::<&str>();
    assert!(*cpt == ManuallyDrop::new(STR2));
    return Continuation::done();
  }
}
