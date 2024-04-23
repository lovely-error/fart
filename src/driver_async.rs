

use core::{
  any::Any, future::Future, mem::{offset_of, size_of_val}, panic::UnwindSafe, sync::atomic::{fence, AtomicI32, AtomicU32}, task::Poll, time::Duration
};
use std::{
  alloc::Layout, cell::UnsafeCell, mem::{
    align_of, forget, size_of, transmute, MaybeUninit
  }, os::fd::{AsFd, AsRawFd}, ptr::{addr_of, addr_of_mut, null_mut }, simd::Simd, sync::{atomic::{AtomicBool, AtomicU16, AtomicU64, Ordering }, mpsc::{Receiver, Sender}}, thread::{self, spawn, JoinHandle}
};

use crate::{
  block_allocator::MBAlloc, loopbuffer::InlineLoopBuffer, root_alloc::{Block4KPtr, RootAllocator}, utils::PageSource, virt_mem::VirtMem
};
use crate::futex;

macro_rules! hard_mfence {
    () => {
      core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::Release);
      #[allow(unused_unsafe)] unsafe { core::arch::x86_64::_mm_mfence() };
      core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::Acquire);
    };
}


macro_rules! force_pusblish_stores {
    () => {
      core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::Release);
      #[allow(unused_unsafe)] unsafe { core::arch::x86_64::_mm_sfence() };
      core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::Acquire);
    };
}

macro_rules! static_assert {
    ($cond:expr) => {
      const _ : () = if !$cond { std::panic!("Comptime assert failed!") } ;
    };
    ($cond:expr, $msg:expr) => {
      const _ : () = if !$cond { panic!($msg) } ;
    };
}

const SMALL_PAGE_SIZE : usize = 4096;

const MAX_WAIT_TIME: Duration = Duration::from_millis(67);

#[repr(align(64))] #[allow(dead_code)]
struct CLCell([u8;64]);
#[repr(C)] #[repr(align(4096))]
struct SlabPage {
  ref_count: AtomicU32,
  cells: [CLCell;SLAB_MAX_COUNT]
}
static_assert!(size_of::<SlabPage>() == SMALL_PAGE_SIZE);
static_assert!(offset_of!(SlabPage, cells) == 64);
const SLAB_MAX_COUNT: usize = (4096 - 1) / size_of::<CLCell>();
struct TaskAllocatorInner {
  page_origin_addr: *mut SlabPage,
  free_slab_ptr: *mut u8
}
pub struct TaskAllocator(UnsafeCell<TaskAllocatorInner>);
impl TaskAllocator {
  const MAX_ALLOC_SIZE_IN_BYTES: usize = SMALL_PAGE_SIZE - 4;
  fn new() -> Self {
    Self(UnsafeCell::new(TaskAllocatorInner {
      page_origin_addr: null_mut(),
      free_slab_ptr: null_mut(),
    }))
  }
  fn destroy(self) -> Option<Block4KPtr> { unsafe {
    let this = &mut *self.0.get();
    let poa = this.page_origin_addr;
    if poa.is_null() { return None }
    let prior = (*poa).ref_count.fetch_sub(1, Ordering::Release);
    if prior == 1 {
      return Some(Block4KPtr::new(poa.cast()));
    } else {
      return None;
    }
  } }
  fn set_page(&self, page: *mut u8) { unsafe {
    let this = &mut *self.0.get();
    let page = page.cast::<SlabPage>();
    this.page_origin_addr = page.cast();
    this.free_slab_ptr = page.byte_add(core::mem::offset_of!(SlabPage, cells)).cast();
    (*page).ref_count.store(1, Ordering::Release);
  } }
  fn release_page(&self) -> bool { unsafe {
    let this = &mut *self.0.get() ;
    let prior = (*this.page_origin_addr).ref_count.fetch_sub(1, Ordering::AcqRel);
    if prior == 1 {
      // reusable
      this.free_slab_ptr = addr_of_mut!((*this.page_origin_addr).cells).cast();
      (*this.page_origin_addr).ref_count.store(1, Ordering::Release);
      return false;
    } else {
      return true
    }
  } }
  #[inline(never)]
  fn alloc_task_frame(
    &self,
    header_size: u32,
    header_align: u32,
    env_size: u32,
    env_align: u32,
    page_source: &dyn PageSource,
  ) -> Option<*mut ()> { unsafe {
    let this = &mut *self.0.get();
    if this.free_slab_ptr.is_null() {
      let page = match page_source.try_get_page() {
        Some(page) => page,
        None => return None,
      };
      self.set_page(page.get_ptr())
    }
    let frame_size = header_size.next_multiple_of(env_align) + env_size;
    let fits = frame_size as usize <= Self::MAX_ALLOC_SIZE_IN_BYTES;
    debug_assert!(fits);

    loop {
      let initial_addr = this.free_slab_ptr as usize;
      let frame_start = initial_addr.next_multiple_of(header_align as _);
      let addr_past_header = frame_start + header_size as usize;
      let env_start_addr = addr_past_header.next_multiple_of(env_align as _);
      let frame_end = env_start_addr + env_size as usize;

      let right_bound = this.page_origin_addr as usize + 4096;
      let past_boundry = frame_end > right_bound;
      if past_boundry {
        let needs_new = self.release_page();
        if needs_new {
          let page = page_source.try_get_page();
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
      (*this.page_origin_addr).ref_count.fetch_add(1, Ordering::AcqRel);
      let terminal_addr = frame_end.next_multiple_of(64);
      let exhausted = terminal_addr == right_bound;
      if exhausted {
        let needs_new = self.release_page();
        if needs_new {
          this.free_slab_ptr = null_mut();
        }
      } else {
        this.free_slab_ptr = terminal_addr as _;
      }
      let ptr = env_start_addr as _;
      return Some(ptr);
    }
  } }
  #[must_use]
  fn dispose<T: DisposableMemoryObject>(object: T) -> Option<Block4KPtr>{ unsafe {
    let rptr = object.get_region_metadata_ptr();
    let i = (*rptr).ref_count.fetch_sub(1, Ordering::Release) ;
    if i == 1 {
      return Some(Block4KPtr::new(rptr.cast::<()>()));
    } else {
      return None
    }
  } }
}

pub struct RegionMetadata {
  ref_count: AtomicU16
}
pub trait DisposableMemoryObject {
  fn get_region_metadata_ptr(&self) -> *mut RegionMetadata;
}

struct FDWorker {
  parent: *mut Worker,
  handle: Option<JoinHandle<()>>,
  fd_in: std::sync::mpsc::Receiver<TaskRef>,
  fd_out: std::sync::mpsc::Sender<TaskRef>,
  parent_asked_to_stop: AtomicBool,
  ping_fd: i32,
  init_code: AtomicI32,
  salt: futex::Token
}
impl FDWorker {
  #[must_use]
  fn try_start(&mut self) -> Result<(), i32> { unsafe {
    if let Some(_) = self.handle { return Ok(()) }
    let this = addr_of_mut!(*self) as u64;
    let thread = spawn(move || {
      let this = this as *mut FDWorker;
      io_polling_routine(&mut*this)
    });
    loop {
      match self.init_code.compare_exchange(0, 0, Ordering::Relaxed, Ordering::Relaxed) {
        Ok(_) => {
          self.handle = Some(thread);
          return Ok(());
        },
        Err(real) => {
          if real == -1 { continue }
          drop(thread);
          return Err(real);
        },
      };
    }
  } }
  fn stop(&mut self) {
    if let Some(thread) = self.handle.take() {
      match self.parent_asked_to_stop.compare_exchange(false, true, Ordering::AcqRel, Ordering::Relaxed) {
        Ok(_) => (),
        Err(_) => unreachable!(),
      };
      self.wakeup();
      thread.join().unwrap();
    }
  }
  #[inline(always)]
  fn wakeup(&self) {
    let _ = futex::futex_wake(&self.salt);
  }
  #[inline(always)]
  fn ping(&self) { unsafe {
    let fake = 0u64;
    loop {
      let ret_code = libc::write(self.ping_fd, addr_of!(fake).cast(), 8);
      if ret_code == -1 {
        let err_code = *libc::__errno_location();
        match err_code {
          libc::EINTR => {
            continue;
          },
          libc::ENOSPC => {
            continue;
          }
          libc::EPIPE |
          libc::EPERM |
          libc::EIO |
          libc::EINVAL |
          libc::EDQUOT |
          libc::EFBIG |
          libc::EFAULT |
          libc::EBADF |
          libc::EAGAIN | _ => unreachable!()
        }
      }
      break;
    }
    self.wakeup();
  } }
}

fn io_polling_routine(worker: &mut FDWorker) { unsafe {

  let parent = &(*worker.parent);

  let poller = loop {
    let poller = libc::epoll_create(1);
    if poller == -1 {
      match poller {
        libc::ENOMEM => {
          thread::yield_now(); continue;
        }
        libc::EMFILE => {
          worker.init_code.store(libc::EMFILE, Ordering::Relaxed);
          return;
        },
        libc::EINVAL | _ => unreachable!()
      }
    }
    break poller;
  };
  // ping fd
  let mut ping_event = libc::epoll_event { events: libc::EPOLLIN as u32, u64: 0, };
  loop {
    let ret_code = libc::epoll_ctl(poller, libc::EPOLL_CTL_ADD, worker.ping_fd, &mut ping_event);
    if ret_code == -1 {
      match *libc::__errno_location() {
        libc::ENOMEM => {
          thread::yield_now();
          continue;
        },
        libc::ENOSPC => {
          worker.init_code.store(libc::ENOSPC, Ordering::Relaxed);
          return;
        },
        libc::ENOENT |
        libc::ELOOP |
        libc::EINVAL |
        libc::EBADF |
        libc::EFAULT | _ => unreachable!()
      }
    }
    break;
  }
  worker.init_code.store(0, Ordering::Release);

  let mut salt = 0;
  let mut pending_ops = 0usize;
  const MAX_EVENTS: i32 = 256;
  let mut inline_poll_data: MaybeUninit<[libc::epoll_event;MAX_EVENTS as usize]> = MaybeUninit::uninit();
  'main:loop {
    match worker.parent_asked_to_stop.compare_exchange(
      true, true, Ordering::AcqRel, Ordering::Relaxed
    ) {
      Ok(_) => return,
      Err(_) => (),
    }
    match worker.fd_in.try_recv() {
      Ok(task) => {
        let mtd = &mut *task.get_mtd_ptr::<TaskHeader_AnyHeader>();
        let interest = mtd.ext.epoll_interest;
        let mut ep_event = libc::epoll_event {
          events: (
            interest | libc::EPOLLONESHOT // | libc::EPOLLET// | libc::EPOLLWAKEUP
          ) as u32,
          u64: transmute(task),
        };
        let fd = mtd.ext2.fd;
        let outcome = libc::epoll_ctl(poller, libc::EPOLL_CTL_ADD, fd, &mut ep_event);
        mtd.ext.epoll_ret_code = outcome;
        task.publish_header_updates();
        if outcome != 0 {
          while worker.fd_out.send(task).is_err() {}
          continue 'main;
        }
        pending_ops += 1;
        continue;
      },
      Err(_) => {
        if pending_ops == 0 {
          // deep sleep
          if let Some(real) = futex::futex_wait(&worker.salt, salt, MAX_WAIT_TIME) {
            salt = real;
          }
          continue 'main;
        }
      },
    }
    // wait for some things here
    let len = loop {
      let ret_code = libc::epoll_wait(
        poller,
        inline_poll_data.as_mut_ptr().cast(),
        MAX_EVENTS,
        -1
      );
      if ret_code == -1 {
        match *libc::__errno_location() {
          libc::EINTR => {
            continue;
          }
          libc::EINVAL |
          libc::EBADFD |
          libc::EFAULT | _ => unreachable!()
        }
      }
      break ret_code as usize;
    };
    debug_assert!(len != 0);
    pending_ops = pending_ops.saturating_sub(len);
    let ready_items = &inline_poll_data.assume_init_ref()[..len];
    for item in ready_items {
      let item: u64 = item.u64;
      let task: TaskRef = transmute(item);
      while worker.fd_out.send(task).is_err() {}
    }
    parent.wakeup();
  }
} }

fn blocking_runner_routine(
  runner: &mut BlockingRunner
) { unsafe {
  let mut salt = 0;
  loop {
    if runner.should_stop.load(Ordering::Relaxed) { return }
    let task = match runner.rx_port.try_recv() {
      Err(_) => {
        if let Some(new) = futex::futex_wait(&runner.token, salt, MAX_WAIT_TIME) {
          salt = new
        };
        continue;
      },
      Ok(task) => task,
    };
    let poll = task.get_polling_fun();
    let outcome = poll(task.get_data_ptr(), null_mut());
    force_pusblish_stores!();
    match outcome {
      Poll::Ready(()) => unreachable!(),
      Poll::Pending => 'send:loop {
        match runner.tx_port.send(task) {
          Ok(_) => {
            (*runner.parent).wakeup();
            break 'send
          },
          Err(_) => continue 'send,
        }
      },
    }
  }
} }
struct BlockingRunner {
  parent: *mut Worker,
  thread: Option<JoinHandle<()>>,
  tx_port: Sender<TaskRef>,
  rx_port: Receiver<TaskRef>,
  token: futex::Token,
  should_stop: AtomicBool
}
impl BlockingRunner {
  fn ping(&mut self) {
    self.start();
    self.wakeup();
  }
  fn wakeup(&self) {
    futex::futex_wake(&self.token);
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
const REASONABLE_WORKER_DEAULT_COUNT: usize = 16;
struct WorkerSet(UnsafeCell<WorkerSetData>);
struct WorkerSetData {
  inline_workers: InlineLoopBuffer<REASONABLE_WORKER_DEAULT_COUNT, Worker>,
  outline_workers: Vec<Worker>,
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
    if index >= REASONABLE_WORKER_DEAULT_COUNT {
      this.outline_workers.get_unchecked_mut(index)
    } else {
      this.inline_workers.mref_item_at_index(index).unwrap()
    }
  } }
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
#[repr(C)] #[derive(Debug)]
struct TaskListPageMtd {
  next_page: *mut TaskListPage,
}
#[repr(C)] #[repr(align(4096))]
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
  #[allow(dead_code)]
  fn item_count(&self) -> usize {
    self.item_count
  }
  #[must_use]
  fn enque_one(
    &mut self,
    task: TaskRef,
    provider: &dyn PageSource
  ) -> bool { unsafe {
    if self.read_ptr.is_null() {
      let page = provider.try_get_page();
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
    let no_capacity = write_ptr == write_ptr.map_addr(|addr|addr & !(SMALL_PAGE_SIZE - 1));
    if no_capacity {
      let cur_w = write_ptr.byte_sub(SMALL_PAGE_SIZE).cast::<TaskListPage>();
      let next_page = (*cur_w).mtd.next_page;
      if next_page.is_null() {
        let new = provider.try_get_page();
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
        write_ptr = addr_of_mut!((*next_page).items).cast();
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
    let on_boundry = rp == rp.map_addr(|addr|addr & !(SMALL_PAGE_SIZE - 1));
    if on_boundry {
      let cur_rpg = rp.cast::<TaskListPage>().sub(1);
      let next = (*cur_rpg).mtd.next_page;
      if next.is_null() {
        return None;
      } else {
        page = Some(Block4KPtr::new(cur_rpg.cast()));
        rp = addr_of_mut!((*next).items).cast();
      }
    }
    let item = rp.read();
    self.read_ptr = rp.add(1).cast();
    self.item_count -= 1;
    return Some((item, page));
  } }
  fn dequeue_pack(&mut self) -> Option<(TaskPack, usize, Option<Block4KPtr>)> { unsafe {
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
        return None;
      } else {
        recyc_page = Some(Block4KPtr::new(page.cast()));
        rp = addr_of_mut!((*next).items).cast();
      }
    }
    let pack_size = size_of::<TaskPack>();
    let item = rp.cast::<TaskPack>().read();
    let new_rp = rp.byte_add(pack_size);
    let runahead = {
      let rp_addr = new_rp as usize;
      let wp_addr = self.write_ptr as usize;
      let on_same_page =
        (rp_addr - 1) & !(SMALL_PAGE_SIZE - 1) ==
        (wp_addr - 1) & !(SMALL_PAGE_SIZE - 1);
      let rp_runahead = rp_addr > wp_addr;
      on_same_page && rp_runahead
    };
    if runahead {
      self.write_ptr = new_rp;
    }
    self.read_ptr = new_rp;
    let count = self.item_count;
    let actual_count = if count >= 16 { 16 } else { count };
    self.item_count = count - actual_count;
    return Some((item, actual_count, recyc_page));
  } }
  fn remaining_capacity(&self) -> usize {
    if self.read_ptr.is_null() { return 0; }
    let rp = self.write_ptr as usize;
    let rbound = self.tail_page as usize + 4096;
    let delta = rbound - rp;
    let spare_count = delta >> 3;
    return spare_count;
  }
}
#[test]
fn cap_check_works() {
  let mut alloc = RootAllocator::new();
  let mut list = TaskList::new();
  assert!(list.remaining_capacity() == 0);
  let ok = list.enque_one(unsafe { transmute(63u64) }, &mut alloc);
  assert!(ok);
  assert!(list.remaining_capacity() == TASK_LIST_PAGE_ITEM_LIMIT - 1);
  for i in 0 .. TASK_LIST_PAGE_ITEM_LIMIT - 1 {
    let ok = list.enque_one(unsafe { transmute(i) }, &mut alloc);
    assert!(ok);
  }
  assert!(list.remaining_capacity() == 0);
}
#[test]
fn list_works() {
  let mut alloc = RootAllocator::new();
  let mut list = TaskList::new();
  const LIMIT : usize = 1_000_000;
  for i in 0 .. LIMIT {
    let _ = list.enque_one(unsafe { transmute(i) }, &mut alloc);
  }
  let mut got_mem = false;
  for i in 0 .. LIMIT {
    let (item, mem) = list.deque_one().unwrap();
    if let Some(_mem) = mem {
      // println!("got mem {:?}", _mem);
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
    let _ = list.enque_one(unsafe { transmute(i) }, &mut alloc);
    let pack = list.dequeue_pack().unwrap();
    unsafe {assert!(pack.0.simd.to_array()[0] == i as _);}
    // println!("{:?} {}", pack, i);
  }
}
#[test]
fn list_pack_deque_works2() {
  let mut alloc = RootAllocator::new();
  let mut list = TaskList::new();
  for i in 0 .. 512usize {
    let _ = list.enque_one(unsafe { transmute(i) }, &mut alloc);
  }
  for i in 0 .. (512 / 16) {
    let pack = list.dequeue_pack().unwrap();
    if i == 31 { assert!(pack.2.is_some()) }
    // println!("{:?} {}", pack, i);
    let ok = list.enque_one(unsafe { transmute(11usize) }, &mut alloc);
    assert!(ok);
  }
  // println!("___DELIMITER___");
  for _i in 0 .. 2 {
    let pack = list.dequeue_pack().unwrap();
    unsafe {
      assert!(pack.0.simd == Simd::splat(11));
      println!("{:?} ix {}", pack.0.simd, _i)
    }
  }
}


pub(crate) type PackItem = TaskRef;

#[repr(C)] #[derive(Clone, Copy)]
pub(crate) union TaskPack {
  pub simd: Simd<u64, 16>,
  pub(crate) tasks: [PackItem;16],
  pub uninit: ()
}

pub struct TaskSet {
  immidiate_items: InlineLoopBuffer<16, TaskRef>,
  task_list: TaskList,
}
impl TaskSet {
  fn new() -> Self {
    Self {
      task_list: TaskList::new(),
      immidiate_items: InlineLoopBuffer::new(),
    }
  }
  fn insert_pack(&self, pack:TaskPack, len:usize) {
    self.immidiate_items.insert_pack(pack, len);
  }
  fn remaining_capacity(&self) -> usize {
    self.immidiate_items.remaining_capacity() +
    self.task_list.remaining_capacity()
  }
  #[must_use]
  pub fn enque(&mut self, new_item: TaskRef, ps: &dyn PageSource) -> bool {
    let ok = self.task_list.enque_one(new_item, ps);
    if ok {
      return true;
    } else {
      return self.immidiate_items.push_to_tail(new_item);
    }
  }
  fn deque_one(&mut self) -> Option<(TaskRef, Option<Block4KPtr>)> {
    if self.immidiate_items.item_count() == 0 {
      let result = if let Some((pack, len, mem)) = self.task_list.dequeue_pack() {
        self.immidiate_items.insert_pack(pack, len);
        let task = self.immidiate_items.pop_from_head().unwrap();
        Some((task, mem))
      } else { None };
      return result;
    } else {
      let task = self.immidiate_items.pop_from_head().unwrap();
      return Some((task, None));
    }
  }
}

#[derive(Debug)]
struct AvailabilityMap {
  inlines: AtomicU64,
  outlines: Vec<AtomicU64>,
  limit: usize
}
impl AvailabilityMap {
  fn new(
    max_count: usize,
  ) -> Self {
    let mut this = Self {
      inlines: AtomicU64::new(0),
      outlines: Vec::new(),
      limit:max_count
    };
    let mut remainder = max_count;
    let mut source = &this.inlines;
    loop {
      let bitmask = !(u64::MAX << (64 - remainder.min(64)));
      let bitmask = bitmask.reverse_bits();
      source.store(bitmask, Ordering::Relaxed);
      remainder = remainder.saturating_sub(64);
      if remainder == 0 { break }
      this.outlines.push(AtomicU64::new(0));
      source = this.outlines.last().unwrap();
    }

    return this;
  }
  fn mark_as_free(&self, index: usize) {
    let src = if index < 64 {
      &self.inlines
    } else {
      &self.outlines[(index >> 6) - 1]
    };
    let mask = !(1 << (index & ((1 << 6) - 1)));
    let _ = src.fetch_and(mask, Ordering::AcqRel);
  }
  #[allow(dead_code)]
  fn mark_as_taken(&self, index: usize) {
    let src = if index < 64 {
      &self.inlines
    } else {
      &self.outlines[(index >> 6) - 1]
    };
    let mask = 1 << (index & ((1 << 6) - 1));
    let _ = src.fetch_or(mask, Ordering::AcqRel);
  }
  fn try_find_free_index(&self) -> Option<usize> {
    fn pick_index(
      source: &AtomicU64
    ) -> Option<usize> {
      let mut map = source.load(Ordering::Acquire);
      loop {
        let index = map.trailing_ones();
        if index == 64 { return None }
        let mask = 1u64 << index;
        let prior = source.fetch_or(mask, Ordering::AcqRel);
        let taken = prior & mask != 0;
        if taken { map = prior; continue; }
        return Some(index as _)
      }
    }
    let max = (self.limit + 63) / 64;
    debug_assert!(max != 0);
    let mut ix = 0;
    let mut source = &self.inlines;
    loop {
      if let Some(i) = pick_index(source) { return Some(i + (64 * ix)) };
      ix += 1;
      if ix == max { return None }
      source = &self.outlines[ix];
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

#[repr(C)] #[repr(align(64))] #[derive(Debug)]
struct WorkerFlags {
  init_code: AtomicI32,
  flags: AtomicU64,
  futex_token: futex::Token,
}
static_assert!(size_of::<WorkerFlags>() <= 64);
static_assert!(align_of::<WorkerFlags>() == 64);

struct InitToken(*const AtomicU64);
impl InitToken {
  #[inline(always)]
  fn signal_init_release(&self) {
    unsafe { (*self.0).fetch_or(Worker::FIRST_INIT_RELEASE, Ordering::Release) };
  }
}

enum InterworkerMessage {
  Memory(Block4KPtr),
  Pack([PackItem;16], usize)
}

#[repr(C)]
struct Worker {
  atomics: WorkerFlags,
  runner_handle: Option<JoinHandle<()>>,
  tx_port: std::sync::mpsc::Sender<InterworkerMessage>,
  rx_port: std::sync::mpsc::Receiver<InterworkerMessage>,
  work_group: *mut FaRT,
  index: usize,
}
impl Worker {
  const FIRST_INIT_RELEASE: u64 = 1 << 3;
  #[inline(always)]
  fn wait_first_init_release(&self) {
    loop {
      match self.atomics.flags.compare_exchange(0, 0, Ordering::Relaxed, Ordering::Acquire) {
        Ok(_) => unreachable!(),
        Err(v) => {
          let released = v & Self::FIRST_INIT_RELEASE != 0;
          if released { return }
        },
      }
    }
  }
  fn advertise_as_available(&self) { unsafe {
    let map = &(*(*self.work_group).worker_set.0.get()).availability_map;
    map.mark_as_free(self.index);
  } }
  fn get_root_allocator(&self) -> &RootAllocator {
    unsafe{&(*self.work_group).ralloc}
  }
  #[inline(always)]
  fn wakeup(&self) {
    debug_assert!(self.was_started(), "Cant wake up uinited worker");

    futex::futex_wake(&self.atomics.futex_token);
  }
  fn was_started(&self) -> bool {
    self.atomics.flags.compare_exchange(0, 0, Ordering::Relaxed, Ordering::Acquire).is_err()
  }
  const NEED_MEM:u64 = 1 << 1;
  fn mark_need_mem(&self) {
    self.atomics.flags.fetch_or(Self::NEED_MEM, Ordering::AcqRel);
  }
  fn try_volunteer_for_mem_resupply(&self) -> bool {
    let val = self.atomics.flags.fetch_and(!Self::NEED_MEM, Ordering::AcqRel);
    return if val & Self::NEED_MEM == 0 { false }
           else { true };
  }
  const WAS_STARTED: u64 = 1 << 0;
  #[must_use]
  fn try_start_(&mut self) -> Result<InitToken, i32> {
    let token = InitToken(addr_of!(self.atomics.flags));
    let prior = self.atomics.flags.fetch_or(Self::WAS_STARTED, Ordering::AcqRel);
    if prior & Self::WAS_STARTED != 0 {
      return Ok(token);
    }
    let copy = addr_of_mut!(*self) as u64;
    let worker_thread = unsafe {
      std::thread::Builder::new()
      .name(format!("Worker thread {}", self.index))
      .stack_size(16*(1024*1024))
      .spawn_unchecked(move || {
        let ptr = copy as *mut Worker;
        task_processing_routine(ptr)
      }).unwrap()
    };
    loop {
      match self.atomics.init_code.compare_exchange(0, 0, Ordering::Relaxed, Ordering::Relaxed) {
        Ok(_) => break,
        Err(err) => {
          if err == -1 { continue }
          drop(worker_thread);
          self.atomics.flags.fetch_and(!Self::WAS_STARTED, Ordering::Release);
          return Err(err);
        },
      }
    }
    self.runner_handle = Some(worker_thread);
    return Ok(token);
  }
  fn setup_affinity(&self) -> bool { unsafe {

    let index = self.index;
    let segment = index / 8;
    let subindex = index % 8;

    let mut set_mask = MaybeUninit::<libc::cpu_set_t>::zeroed();
    let entries = core::slice::from_raw_parts_mut(set_mask.as_mut_ptr().cast::<u8>(), size_of::<libc::cpu_set_t>());
    entries[segment] |= 1 << subindex;

    let ret_code = libc::sched_setaffinity(0, size_of::<libc::cpu_set_t>(), set_mask.assume_init_ref());
    if ret_code == -1 {
      match *libc::__errno_location() {
        libc::EFAULT |
        libc::ESRCH => unreachable!(),
        err => {
          self.atomics.init_code.store(err, Ordering::Release);
          return false;
        },
      }
    }

    let mut policy = MaybeUninit::<libc::sched_param>::zeroed();
    let ret_val = libc::sched_get_priority_max(libc::SCHED_RR);
    if ret_val == -1 { panic!("Unexpected argument in call to sched_get_priority_max!") }
    policy.assume_init_mut().sched_priority = ret_val / 2;

    let run_with_realtime_priority = match std::env::var("RT_SCHED") {
      Ok(str) if str == "1" => true,
      _ => false,
    };
    if run_with_realtime_priority {
      let ret_code = libc::sched_setscheduler(0, libc::SCHED_RR, policy.as_ptr());
      if ret_code == -1 {
        match *libc::__errno_location() {
          libc::EPERM => {
            self.atomics.init_code.store(libc::EPERM, Ordering::Relaxed);
            return false;
          },
          libc::EFAULT |
          libc::EINVAL |
          libc::ESRCH | _ => unreachable!()
        }
      }
    }

    return true;
  } }
}

pub struct MemRouter(UnsafeCell<MemRouterInner>);
struct MemRouterInner {
  root_allocator: *const RootAllocator,
  page_store: *const PageStorage
}
impl MemRouter {
  fn new(
    root_allocator: &RootAllocator,
    page_store: &PageStorage
  ) -> Self {
    MemRouter(UnsafeCell::new(MemRouterInner {
      root_allocator,
      page_store
    }))
  }
  fn inner(&self) -> &mut MemRouterInner {
    unsafe { &mut *self.0.get() }
  }
  fn try_provision_mem(&self) -> bool { unsafe {
    let inner = self.inner();
    if (*inner.page_store).available_page_count() > 0 {
      return true;
    }
    if let Some(page) = (*inner.root_allocator).try_get_page() {
      (*inner.page_store).store_page(page);
      return true;
    }
    return false;
  } }
  fn available_page_count(&self) -> usize {
    let inner = self.inner();
    unsafe { (*inner.page_store).available_page_count() }
  }
}
impl PageSink for MemRouter {
  fn recycle_page(&self, page: Block4KPtr) {
    unsafe { (*self.inner().page_store).store_page(page) }
  }
}
impl PageSource for MemRouter {
  fn try_get_page(&self) -> Option<Block4KPtr> { unsafe {
    let inner = self.inner();
    if let Some(page) = (*inner.page_store).try_get_page() {
      return Some(page);
    }
    if let Some(page) = (*inner.root_allocator).try_get_page() {
      return Some(page);
    }
    return None;
  } }
}

#[repr(C)]
struct FreePageList {
  next_page: *mut FreePageList,
  bytes: [u8; SMALL_PAGE_SIZE - size_of::<*mut FreePageList>()]
}
struct PageStorageInner {
  free_pages: *mut FreePageList,
  page_count: usize
}
pub struct PageStorage(UnsafeCell<PageStorageInner>);
impl PageStorage {
  pub fn new() -> Self {
    Self(UnsafeCell::new(PageStorageInner {
      free_pages: null_mut(),
      page_count: 0
    }))
  }
  fn available_page_count(&self) -> usize {
    let this = unsafe{&mut*self.0.get()};
    this.page_count
  }
  fn store_page(&self, page:Block4KPtr) { unsafe {
    let this = &mut*self.0.get();
    this.page_count += 1;
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
      debug_assert!(out == 0, "Failed to unmap mem?? 0_o\naddress was {:?}", page);
      page = next;
    }
  } }
}
impl PageSource for PageStorage {
  fn try_get_page(&self) -> Option<Block4KPtr> {
    self.try_get_page()
  }
}
impl PageSink for PageStorage {
    fn recycle_page(&self, page: Block4KPtr) {
      self.store_page(page)
    }
}

enum ExecState {
  Fetch, Sleep, Execute, Shutdown
}
fn task_processing_routine(worker_: *mut Worker) { unsafe {

  let this_worker = &mut*worker_;

  let ok = this_worker.setup_affinity();
  if !ok { return }

  let workgroup = &*this_worker.work_group;

  let allocator = TaskAllocator::new();
  let page_store = PageStorage::new();
  let mballoc = MBAlloc::new();

  let mem_controller = MemRouter::new(
    this_worker.get_root_allocator(),
    &page_store
  );
  let virt_mem = VirtMem::new();
  let mut task_set = TaskSet::new();
  let mut current_task : TaskRef = TaskRef::new_null();

  let (br_tx_in, br_tx_out) = std::sync::mpsc::channel();
  let (br_rx_in, br_rx_out) = std::sync::mpsc::channel();
  let mut blocking_runner = BlockingRunner {
    parent: worker_,
    thread: None,
    tx_port: br_rx_in,
    rx_port: br_tx_out,
    token: futex::Token::new(),
    should_stop: AtomicBool::new(false),
  };
  let (tx_fd_in, rx_fd_in) = std::sync::mpsc::channel();
  let (rx_fd_out, tx_fd_out) = std::sync::mpsc::channel();
  let mut fd_thread = FDWorker {
    parent: worker_,
    handle: None,
    parent_asked_to_stop: AtomicBool::new(false),
    ping_fd: loop {
      let fd = libc::eventfd(0, libc::EFD_NONBLOCK);
      if fd == -1 {
        match *libc::__errno_location() {
          libc::ENOMEM => {
            thread::yield_now();
            continue;
          },
          libc::ENODEV => {
            this_worker.atomics.init_code.store(libc::ENODEV, Ordering::Relaxed);
            return;
          },
          libc::ENFILE => {
            this_worker.atomics.init_code.store(libc::ENFILE, Ordering::Relaxed);
            return;
          },
          libc::EMFILE => {
            this_worker.atomics.init_code.store(libc::EMFILE, Ordering::Relaxed);
            return;
          },
          libc::EINVAL | _ => unreachable!()
        }
      }
      break fd
    },
    init_code: AtomicI32::new(-1),
    salt: futex::Token::new(),
    fd_in: rx_fd_in,
    fd_out: rx_fd_out,
  };

  match fd_thread.try_start() {
    Ok(_) => (),
    Err(err) => {
      this_worker.atomics.init_code.store(err, Ordering::Relaxed);
      return;
    },
  }

  let mut task_context = TaskCtx(UnsafeCell::new(TaskContextInternals {
    allocator: addr_of!(allocator),
    task_set: addr_of_mut!(task_set),
    task_dependency_info: TaskDependency::Unreachable,
    current_task: addr_of!(current_task),
    fd_sink: addr_of!(tx_fd_in),
    mem_router: addr_of!(mem_controller),
    mballoc: addr_of!(mballoc),
    virt_mem: addr_of!(virt_mem)
  }));

  this_worker.atomics.init_code.store(0, Ordering::Release);
  this_worker.wait_first_init_release();
  fence(Ordering::AcqRel);

  let mut pending_ops_count = 0;
  let mut salt = 0;
  let mut exec_state = ExecState::Fetch;

  'dispatch:loop {
    match exec_state {
      ExecState::Fetch => {
        try_transfer_excess(this_worker, &mut task_set, &mem_controller);
        if let Some((new_task, free_mem)) = (task_set).deque_one() {
          current_task = new_task;
          if let Some(free_mem) = free_mem {
            mem_controller.recycle_page(free_mem);
          }
          exec_state = ExecState::Execute;
          continue 'dispatch;
        }
        loop {
          match this_worker.rx_port.try_recv() {
            Ok(msg) => match msg {
              InterworkerMessage::Memory(mem) => {
                mem_controller.recycle_page(mem);
                continue;
              },
              InterworkerMessage::Pack(tasks, len) => {
                let pack = TaskPack { tasks: tasks };
                task_set.insert_pack(pack, len);
                continue 'dispatch;
              },
            },
            Err(_) => break,
          }
        }
        if task_set.remaining_capacity() == 0 {
          if !mem_controller.try_provision_mem() {
            // other workers would give
            this_worker.mark_need_mem();
            exec_state = ExecState::Sleep;
            continue 'dispatch;
          }
          //we have page worth of mem
        }
        fence(Ordering::AcqRel);
        // check what blocking runner has made us
        match br_rx_out.try_recv() {
          Ok(task) => {
            let ok = task_set.enque(task, &mem_controller);
            assert!(ok);
            pending_ops_count -= 1;
            continue 'dispatch;
          },
          Err(_) => (),
        }
        // check if some fds are ready
        if let Ok(task) = tx_fd_out.try_recv() {
          let ok = task_set.enque(task, &mem_controller);
          debug_assert!(ok);
          pending_ops_count -= 1;
          let mut capacity = task_set.remaining_capacity();
          while capacity != 0 && let Ok(task) = tx_fd_out.try_recv() {
            let ok = task_set.enque(task, &mem_controller);
            debug_assert!(ok);
            pending_ops_count -= 1;
            capacity -= 1;
          }
          continue 'dispatch;
        }
        this_worker.advertise_as_available();
        exec_state = ExecState::Sleep;
        continue 'dispatch;
      },
      ExecState::Sleep => {
        let no_pending = pending_ops_count == 0;
        let time_to_die = (*workgroup.worker_set.0.get()).should_stop.compare_exchange(
          true, true, Ordering::Relaxed, Ordering::Relaxed
        ).is_ok();
        if time_to_die && no_pending {
          exec_state = ExecState::Shutdown;
          continue 'dispatch;
        }
        if page_store.available_page_count() > 0 {
          give_away_mem(&page_store, workgroup);
          exec_state = ExecState::Fetch;
          continue 'dispatch;
        }
        if let Some(actual) = futex::futex_wait(&this_worker.atomics.futex_token, salt, MAX_WAIT_TIME) {
          salt = actual;
        }
        exec_state = ExecState::Fetch;
        continue 'dispatch;
      },
      ExecState::Shutdown => {
        if let Some(page) =  allocator.destroy() {
          mem_controller.recycle_page(page)
        };
        page_store.dispose_mem();
        blocking_runner.stop();
        fd_thread.stop();
        return;
      }
      ExecState::Execute => {
        let poller = current_task.get_polling_fun();
        let outcome = poller(current_task.get_data_ptr(), addr_of_mut!(task_context).cast());
        match outcome {
          core::task::Poll::Ready(()) => {
            match current_task.get_header_type() {
              TaskFrameType::ThreadResumer => {
                let frame_ref = current_task.get_mtd_ref::<TaskHeader_ThreadResumer>();
                futex::futex_wake(&(*frame_ref.wake_mtd).flag);
                exec_state = ExecState::Fetch;
                continue 'dispatch;
              },
              TaskFrameType::IndependentTA => {
                if let Some(page) = TaskAllocator::dispose(current_task) {
                  mem_controller.recycle_page(page)
                };
                exec_state = ExecState::Fetch;
                continue 'dispatch;
              },
              TaskFrameType::IndependentVM => {
                let ptr = current_task.get_middle_ptr();
                VirtMem::release_memory(ptr);
                exec_state = ExecState::Fetch;
                continue 'dispatch;
              },
            }
          },
          core::task::Poll::Pending => {
            match task_context.read_task_dependency() {
              TaskDependency::FDWait { need_requeue: want_requeue } => {
                if want_requeue {
                  let ok = task_set.enque(current_task, &mem_controller);
                  debug_assert!(ok);
                } else {
                  pending_ops_count += 1;
                  fd_thread.ping();
                }
                exec_state = ExecState::Fetch;
                continue 'dispatch;
              },
              TaskDependency::RunBlocking => {
                current_task.publish_backing_memory_changes();
                while br_tx_in.send(current_task).is_err() {}
                blocking_runner.ping();
                pending_ops_count += 1;
                exec_state = ExecState::Fetch;
                continue 'dispatch;
              },
              TaskDependency::Reschedule => {
                let ok = task_set.enque(current_task, &mem_controller);
                assert!(ok);
                exec_state = ExecState::Fetch;
                continue 'dispatch;
              },
              TaskDependency::Release => {
                fence(Ordering::SeqCst);
                current_task.release_ownership();
                exec_state = ExecState::Fetch;
                continue 'dispatch;
              },
              TaskDependency::Unreachable => unreachable!(),
            }
          },
        }
      },
    }
  }
} }

fn try_transfer_excess(
  src_worker: &mut Worker,
  workset: &mut TaskSet,
  page_sink: &dyn PageSink
) { unsafe {
  let local_workset = &mut *workset;
  let all_workers = &mut (*src_worker.work_group).worker_set;
  let av_map = &(*(*src_worker.work_group).worker_set.0.get()).availability_map;
  loop {
    let count = local_workset.task_list.item_count();
    let too_few_tasks = 16 >= count;
    if too_few_tasks { return; }

    let Some(index) = av_map.try_find_free_index() else { return };
    let free_worker = all_workers.get_worker_at_index(index);
    let token = match free_worker.try_start_() {
      Ok(tok) => tok,
      Err(_) => {
        // it failed to start
        free_worker.advertise_as_available();
        continue;
      },
    };
    let (pack, len, mem) = local_workset.task_list.dequeue_pack().unwrap();
    if let Some(mem) = mem {
      page_sink.recycle_page(mem)
    }
    let tasks = &pack.tasks;
    for i in 0 .. len {
      tasks[i].publish_backing_memory_changes();
    }
    fence(Ordering::AcqRel);
    while free_worker.tx_port.send(InterworkerMessage::Pack(pack.tasks, len)).is_err() {}
    token.signal_init_release();
    fence(Ordering::AcqRel);
    free_worker.wakeup();
  }
} }

fn give_away_mem(
  page_source: &PageStorage,
  rt: &FaRT
) {
  debug_assert!(page_source.available_page_count() > 0);
  let workset = &rt.worker_set;
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
    let res = worker.tx_port.send(InterworkerMessage::Memory(page));
    assert!(res.is_ok());
    fence(Ordering::AcqRel);
    worker.wakeup();
  }
}


pub trait PageSink {
  fn recycle_page(&self, page: Block4KPtr);
}

pub struct TaskCtx(UnsafeCell<TaskContextInternals>);
pub struct TaskContextInternals {
  pub current_task: *const TaskRef,
  pub mem_router: *const MemRouter,
  pub allocator: *const TaskAllocator,
  pub task_set: *mut TaskSet,
  pub task_dependency_info: TaskDependency,
  pub fd_sink: *const std::sync::mpsc::Sender<TaskRef>,
  pub mballoc: *const MBAlloc,
  pub virt_mem: *const VirtMem
}
impl TaskCtx {
  pub fn inner(&self) -> &mut TaskContextInternals {
    unsafe { &mut*self.0.get() }
  }
  pub fn read_task_dependency(&self) -> TaskDependency {
    self.inner().task_dependency_info
  }
  pub fn write_task_dependency(&self, dep_info: TaskDependency) {
    self.inner().task_dependency_info = dep_info;
  }
  pub fn current_task(&self) -> TaskRef {
    unsafe {*self.inner().current_task}
  }
}
// user code never touches this directly
// and our code should not panic .
// well... std code may
impl UnwindSafe for TaskCtx {}

#[derive(Debug, Clone, Copy, PartialEq)] #[repr(u8)]
enum TaskFrameType {
  ThreadResumer,
  IndependentTA,
  IndependentVM
}
pub(crate) trait ValidTaskHeaderMarker {}

#[repr(u8)]
enum FrameAllocationType {
  FromTaskFrameAllocator, FromVM
}

#[repr(C)] #[repr(align(8))] #[derive(Debug, Clone, Copy)]
pub(crate) struct TaskRef(u64);
impl TaskRef {
  fn new(
    task_frame_ptr: *mut (),
    frame_type: TaskFrameType,
  ) -> Self {

    let fr_type = (unsafe {transmute::<_, u8>(frame_type) as u64}) << 48;
    let addr = task_frame_ptr as usize as u64;
    let comb = fr_type | addr;
    return Self(comb);
  }

  #[inline(always)]
  pub(crate) fn publish_backing_memory_changes(&self) {
    let mut cl_ptr = self.get_middle_ptr().map_addr(|a|a & !((1 << 6) - 1)).cast::<CLCell>();
    let span = (self.get_frame_byte_size() + (64-1)) >> 6;
    for _ in 0 .. span {
      unsafe {
        core::arch::x86_64::_mm_clflush(cl_ptr.cast());
        cl_ptr = cl_ptr.add(1);
      }
    }
  }
  #[inline(always)]
  pub(crate) fn publish_header_updates(&self) {
    let cl_ptr = self.get_middle_ptr().map_addr(|a|a & !((1 << 6) - 1)).cast::<CLCell>();
    unsafe {core::arch::x86_64::_mm_clflush(cl_ptr.cast());}
  }
  #[inline]
  fn get_header_type(&self) -> TaskFrameType {
    unsafe {transmute((self.0 >> 48) as u8)}
  }
  #[inline]
  fn get_middle_ptr(&self) -> *mut () {
    (self.0 & ((1 << 48) - 1)) as _
  }
  #[inline]
  fn get_data_ptr(&self) -> *mut () {
    self.get_middle_ptr()
  }
  #[inline]
  fn get_polling_fun(&self) -> fn (*mut (), *mut()) -> core::task::Poll<()> {
    let mtd = self.get_mtd_ref::<TaskHeader_AnyHeader>();
    mtd.poll_fun
  }
  #[inline]
  fn get_frame_byte_size(&self) -> u32 {
    let mtd = self.get_mtd_ref::<TaskHeader_AnyHeader>();
    mtd.frame_size_data
  }
  #[inline]
  pub(crate) fn get_mtd_ref<T:ValidTaskHeaderMarker>(&self) -> &mut T {
    unsafe { &mut *self.get_data_ptr().cast::<T>().sub(1) }
  }
  #[inline]
  fn get_mtd_ptr<T:ValidTaskHeaderMarker>(&self) -> *mut T {
    unsafe { self.get_data_ptr().cast::<T>().sub(1) }
  }
  #[inline]
  fn new_null() -> Self {
    Self(0)
  }
  #[inline]
  fn get_region_metadata_ptr(&self) -> *mut RegionMetadata {
    self.get_data_ptr().map_addr(|addr| addr & !(SMALL_PAGE_SIZE - 1)).cast()
  }
  #[inline(always)]
  pub fn try_aquire_ownership(&self) -> bool {
    self.get_mtd_ref::<TaskHeader_AnyHeader>().is_owned.compare_exchange(
      false, true, Ordering::AcqRel, Ordering::Relaxed
    ).is_ok()
  }
  #[inline(always)]
  pub fn release_ownership(&self) {
    let ok = self.get_mtd_ref::<TaskHeader_AnyHeader>().is_owned.compare_exchange(
      true, false, Ordering::Release, Ordering::Relaxed
    ).is_ok();
    assert!(ok, "For some reason cant release an owned task");
  }
}
impl DisposableMemoryObject for TaskRef {
  fn get_region_metadata_ptr(&self) -> *mut RegionMetadata {
    Self::get_region_metadata_ptr(self)
  }
}

struct AffinityInfo {
  available_core_count: usize,
  mask: [u8;size_of::<libc::cpu_set_t>()],
}
impl AffinityInfo {
  fn new() -> Result<Self, i32> { unsafe {
    let mut this = AffinityInfo { mask: [0;_], available_core_count: 0 };

    let ret_val = libc::sched_getaffinity(0, size_of::<libc::cpu_set_t>(), this.mask.as_mut_ptr().cast());
    if ret_val == -1 {
      match *libc::__errno_location() {
        libc::EPERM => {
          return Err(libc::EPERM);
        },
        libc::EFAULT |
        libc::EINVAL |
        libc::ESRCH | _ => unreachable!()
      }
    }
    let set = core::slice::from_raw_parts(this.mask.as_ptr(), size_of::<libc::cpu_set_t>());
    for item in set {
      this.available_core_count += item.count_ones() as usize;
    }

    return Ok(this);
  } }
  fn get_index_iter(&self) -> impl Iterator<Item = usize> {
    let mut set = self.mask;
    let mut segment_ix = 0;
    let limit = (self.available_core_count + 63) / 64;
    core::iter::from_fn(move || {
      loop {
        if segment_ix == limit { return None }
        let this_segment_index = segment_ix;
        let segment = set[this_segment_index];
        let index = segment.trailing_zeros();
        if index == 64 {
          segment_ix += 1;
          continue
        }
        set[this_segment_index] ^= 1 << index;
        return Some((segment_ix * 64) + index as usize);
      }
    })
  }
}

pub struct FaRT {
  ralloc: RootAllocator,
  worker_set: WorkerSet,
}
impl FaRT {
  fn check_hardware() {
    let res = unsafe { core::arch::x86_64::__cpuid(1) };
    let cl_flush_enabled = (res.edx >> 19) & 1 == 1;
    assert!(cl_flush_enabled, "CPU doesnt have clflush instruction.");
    let cl_size = (res.ebx >> 8 & (1 << 7) - 1) * 8;
    let size_ok = cl_size >= 64;
    assert!(size_ok, "CPU cache line size is too small.");
  }
  #[allow(dead_code)]
  #[inline(always)]
  pub fn new_with_thread_count(
    worker_count:usize
  ) -> RtRef {
    Self::check_hardware();
    let ai = AffinityInfo::new().unwrap();
    return Self::new_common_impl(worker_count,ai);
  }
  #[inline(always)]
  pub fn new() -> RtRef {
    Self::check_hardware();
    let ai = AffinityInfo::new().unwrap();
    return Self::new_common_impl(ai.available_core_count, ai);
  }
  #[inline(always)]
  fn new_common_impl(
    worker_count:usize,
    affinity_info: AffinityInfo,
  ) -> RtRef { unsafe {
    debug_assert!(worker_count != 0 && worker_count <= affinity_info.available_core_count);

    let worker_count = worker_count;
    let boxed = std::alloc::alloc_zeroed(Layout::new::<FaRT>()).cast::<FaRT>();

    let mut core_ix_iter = affinity_info.get_index_iter();

    let inlines = InlineLoopBuffer::<16, _>::new();
    let mut outlines = Vec::new();
    for i in 0 .. worker_count {
      let (tx, rx) = std::sync::mpsc::channel();
      let cix = core_ix_iter.next().unwrap();
      let worker = Worker {
        index: cix,
        runner_handle: None,
        work_group: boxed,
        atomics: WorkerFlags {
          flags: AtomicU64::new(0),
          init_code: AtomicI32::new(-1),
          futex_token: futex::Token::new(),
        },
        tx_port: tx,
        rx_port: rx,
      };
      if i >= REASONABLE_WORKER_DEAULT_COUNT {
        outlines.push(worker)
      } else {
        let ok = inlines.push_to_tail(worker);
        assert!(ok);
      }
    }
    boxed.write(FaRT {
      ralloc:RootAllocator::new(),
      worker_set: WorkerSet(UnsafeCell::new(WorkerSetData {
        inline_workers: inlines,
        outline_workers: outlines,
        total_worker_count: worker_count as u32,
        should_stop: AtomicBool::new(false),
        external_ref_count: AtomicU32::new(1), // +1 because this ref exist
        availability_map: AvailabilityMap::new(worker_count),
      })),
    });
    hard_mfence!();
    return RtRef(boxed)
  } }
  fn destroy(this: *mut FaRT) { unsafe {

    let workeset = &mut *(*this).worker_set.0.get();
    let ok = workeset.should_stop.compare_exchange(
      false, true, Ordering::AcqRel, Ordering::Relaxed
    ).is_ok();
    debug_assert!(ok);
    force_pusblish_stores!();
    let total_worker_count = workeset.total_worker_count;
    for ix in 0 .. total_worker_count {
      let wref = (*this).worker_set.get_worker_at_index(ix as _);
      if wref.was_started() {
        wref.wakeup();
        wref.runner_handle.take().unwrap().join().unwrap();
      }
    }
    hard_mfence!();
    (*this).ralloc.destroy();
    fence(Ordering::AcqRel);
    std::alloc::dealloc(this.cast::<u8>(), Layout::new::<FaRT>());
  } }
}
#[derive(Debug, Clone, Copy)]
pub struct RunFailure(i32);
pub struct RtRef(*mut FaRT);
impl RtRef {
  fn try_find_free_worker(&self) -> Option<&mut Worker> {
    let w = unsafe { &mut (*(*self.0).worker_set.0.get()) };
    let ix = w.availability_map.try_find_free_index()?;
    let wref = if ix >= REASONABLE_WORKER_DEAULT_COUNT {
      unsafe { w.outline_workers.get_unchecked_mut(ix) }
    } else {
      (w.inline_workers).mref_item_at_index(ix).unwrap()
    };
    return Some(wref);
  }
  #[must_use]
  pub fn run_to_completion<F: Future<Output = ()> + Send>(&self, operation: F) -> Result<(), RunFailure> { unsafe {
    let (worker, token) = loop {
      if let Some(w) = self.try_find_free_worker() {
        match w.try_start_() {
          Ok(token) => break (w, token),
          Err(err) => return Err(RunFailure(err)),
        }
      } else { thread::yield_now() }
    };

    let mut resume_mtd = ResumeMtd {
      flag: futex::Token::new(),
      panic: None,
    };

    #[repr(C)] #[repr(align(64))]
    struct TaskFrame<T>(
      [u8;64 - size_of::<TaskHeader_ThreadResumer>()],
      TaskHeader_ThreadResumer,
      T
    );
    let op_size = size_of_val(&operation);
    let size = size_of::<TaskHeader_ThreadResumer>().next_multiple_of(op_size) + op_size;
    let poll_fun = transmute::<_, SomePollFun>(F::poll as *mut ());
    let mut data = TaskFrame(
      [0;_],
      TaskHeader_ThreadResumer {
        wake_mtd: addr_of_mut!(resume_mtd),
        frame_size_data: size as u32,
        poll_fun: poll_fun,
        ext: Ext { uninit: () },
        ext2: Ext2 { uninit: () },
        is_owned: AtomicBool::new(true)
      },
      operation
    );
    let pivot = addr_of_mut!(data.2).cast::<()>();
    let task_ref = TaskRef::new(pivot, TaskFrameType::ThreadResumer);
    task_ref.publish_backing_memory_changes();
    let mut item = TaskPack {
      simd: Simd::splat(0)
    };
    item.tasks[0] = task_ref;
    while worker.tx_port.send(InterworkerMessage::Pack(item.tasks, 1)).is_err() {};
    fence(Ordering::AcqRel);
    token.signal_init_release();
    worker.wakeup();
    loop {
      if resume_mtd.flag.load_value() != 0 { break }
      let _ = futex::futex_wait(&resume_mtd.flag, 0, MAX_WAIT_TIME);
    }
    fence(Ordering::AcqRel);
    forget(data.2);
    return Ok(());
  } }

  fn clone(&self) -> Self { unsafe {
    (*(*self.0).worker_set.0.get()).external_ref_count.fetch_add(1, Ordering::AcqRel);
    return RtRef(self.0)
  } }
}
impl Clone for RtRef {
    fn clone(&self) -> Self {
      RtRef::clone(self)
    }
}
impl Drop for RtRef {
  fn drop(&mut self) { unsafe {
    let prior = (*(*self.0).worker_set.0.get()).external_ref_count.fetch_sub(1, Ordering::Release);
    if prior == 1 {
      FaRT::destroy(self.0);
    }
  } }
}


macro_rules! get_reverse_offset {
    ($ty:ty, $field:ident) => {
      {
        size_of::<$ty>() -
        std::mem::offset_of!($ty, $field)
      }
    };
}
macro_rules! check_reverse_offset {
    ($t1:ty, $t2:ty, $field:ident) => {
      static_assert!(
        get_reverse_offset!($t1, $field) == get_reverse_offset!($t2, $field)
      );
    };
}
#[repr(C)]
pub(crate) union Ext {
  epoll_interest: i32,
  epoll_ret_code: i32,
  uninit: ()
}
#[repr(C)]
pub(crate) union Ext2 {
  pub(crate) fd: i32,
  uninit: ()
}
#[repr(C)] #[allow(non_camel_case_types, dead_code)]
pub(crate) struct TaskHeader_AnyHeader {
  is_owned: AtomicBool,
  ext2: Ext2,
  frame_size_data: u32,
  ext: Ext,
  poll_fun: fn (*mut (), *mut ()) -> core::task::Poll<()>
}
#[repr(C)]
struct ResumeMtd {
  flag: futex::Token,
  panic: Option<Box<dyn Any + Send + 'static>>
}
#[repr(C)] #[allow(non_camel_case_types)]
struct TaskHeader_ThreadResumer {
  wake_mtd: *mut ResumeMtd,
  is_owned: AtomicBool,
  ext2: Ext2,
  frame_size_data: u32,
  ext: Ext,
  poll_fun: fn (*mut (), *mut ()) -> core::task::Poll<()>
}
check_reverse_offset!(TaskHeader_AnyHeader, TaskHeader_ThreadResumer, poll_fun);
check_reverse_offset!(TaskHeader_AnyHeader, TaskHeader_ThreadResumer, frame_size_data);
check_reverse_offset!(TaskHeader_AnyHeader, TaskHeader_ThreadResumer, ext);
check_reverse_offset!(TaskHeader_AnyHeader, TaskHeader_ThreadResumer, ext2);

#[repr(C)] #[allow(non_camel_case_types)]
struct TaskHeader_Independent {
  is_owned: AtomicBool,
  ext2: Ext2,
  frame_size_data: u32,
  ext: Ext,
  poll_fun: fn (*mut (), *mut ()) -> core::task::Poll<()>
}
check_reverse_offset!(TaskHeader_AnyHeader, TaskHeader_Independent, poll_fun);
check_reverse_offset!(TaskHeader_AnyHeader, TaskHeader_Independent, frame_size_data);
check_reverse_offset!(TaskHeader_AnyHeader, TaskHeader_Independent, ext);
check_reverse_offset!(TaskHeader_AnyHeader, TaskHeader_Independent, ext2);

impl ValidTaskHeaderMarker for TaskHeader_ThreadResumer {}
impl ValidTaskHeaderMarker for TaskHeader_Independent {}
impl ValidTaskHeaderMarker for TaskHeader_AnyHeader {}

#[derive(Clone, Copy)]
pub enum TaskDependency {
  FDWait {
    need_requeue: bool
  },
  RunBlocking,
  Reschedule,
  Release,
  Unreachable
}

type SomePollFun = fn (*mut (), *mut ()) -> Poll<()>;


pub fn launch_detached<F>(operation: F) -> impl Future<Output = ()> where F:Future<Output=()> + Send + 'static {
  let mut oper = MaybeUninit::uninit();
  oper.write(operation);
  let mut task_to_dispatch = None;
  core::future::poll_fn(move |ctx| unsafe {
    let ctx = transmute::<_, &mut TaskCtx>(ctx) ;
    let inner = ctx.inner();
    let pm = &*inner.mem_router;
    let task_set = &mut *(*inner).task_set;
    let free_slot_count = task_set.remaining_capacity();
    if task_to_dispatch.is_none() {
      let size = size_of::<F>();
      let allocated_task = match size {
        ..=TaskAllocator::MAX_ALLOC_SIZE_IN_BYTES => {
          let outcome = (*inner.allocator).alloc_task_frame(
            size_of::<TaskHeader_Independent>() as _,
            align_of::<TaskHeader_Independent>() as _,
            size_of::<F>() as _,
            align_of::<F>() as _,
            pm
          );
          let frame_ref = if let Some(frame) = outcome { frame } else {
            // aint got mem (in the system)
            ctx.write_task_dependency(TaskDependency::Reschedule);
            return Poll::Pending;
          };
          TaskRef::new(frame_ref, TaskFrameType::IndependentTA)
        },
        ..=VirtMem::MAX_ALLOC_SIZE_IN_BYTES => {
          let required_page_count = (size_of::<F>() + 4095) / 4096;
          let available_page_count = (*inner.mem_router).available_page_count();
          if required_page_count > available_page_count {
            // no mem
            // todo: park tasks that need memory instead of
            // rescheduling them
            ctx.write_task_dependency(TaskDependency::Reschedule);
            return Poll::Pending;
          }
          let vm_range = (*inner.virt_mem).alloc_page_space(required_page_count).unwrap();
          let ptr = vm_range.fill(&*inner.mem_router);
          TaskRef::new(ptr, TaskFrameType::IndependentVM)
        },
        _ => todo!("frame size can be at most 128MiB, given was {} bytes", size_of::<F>())
      };
      let subtask = allocated_task;
      subtask.get_data_ptr().cast::<F>().write(oper.assume_init_read());
      let ptr = subtask.get_mtd_ptr::<TaskHeader_Independent>();
      let pfn = transmute::<_, SomePollFun>(F::poll as *mut ());
      let frame_size =
        size_of::<TaskHeader_Independent>()
        .next_multiple_of(align_of::<F>()) + size_of::<F>();
      ptr.write(TaskHeader_Independent {
        frame_size_data: frame_size as u32,
        poll_fun: pfn,
        ext: Ext { uninit: () },
        ext2: Ext2 { uninit: () },
        is_owned: AtomicBool::new(true)
      });
      task_to_dispatch = Some(subtask);
      if free_slot_count == 1 {
        ctx.write_task_dependency(TaskDependency::Reschedule);
        return Poll::Pending;
      }
      let ok = task_set.enque(subtask, pm);
      assert!(ok);
      return Poll::Ready(());
    } else {
      if free_slot_count == 1 {
        ctx.write_task_dependency(TaskDependency::Reschedule);
        return Poll::Pending;
      }
      let ok = task_set.enque(*task_to_dispatch.as_ref().unwrap(), pm);
      assert!(ok);
      return Poll::Ready(());
    }
  })
}

pub fn run_isolated<R>(operation: impl (FnOnce() -> R) + Send) -> impl Future<Output = R> {
  let mut op = Some(operation);
  let mut result = MaybeUninit::uninit();
  let mut ix = 0;
  core::future::poll_fn(move |ctx| unsafe {
    match ix {
      0 => {
        let ctx: &mut TaskCtx = transmute(ctx);
        ctx.write_task_dependency(TaskDependency::RunBlocking);
        ix += 1;
        return Poll::Pending;
      },
      1 => {
        let op = op.take().unwrap();
        let res = op();
        result.write(res);
        ix += 1;
        return Poll::Pending;
      },
      _ => {
        let result = result.assume_init_read();
        return Poll::Ready(result);
      }
    }
  })
}

pub enum FdInterest {
  Read, Write, ReadWrite
}
pub fn wait_on_fd(fd: &dyn AsFd, interest: FdInterest) -> impl Future<Output = ()> {
  let rfd = fd.as_fd().as_raw_fd();
  let mut setup_done = false;
  let mut need_retry = false;
  core::future::poll_fn(move |ctx| unsafe {
    let ctx: &mut TaskCtx = transmute(ctx);
    if !setup_done {
      let interest = match interest {
        FdInterest::Read => libc::POLLIN,
        FdInterest::Write => libc::POLLOUT,
        FdInterest::ReadWrite => libc::POLLIN | libc::POLLOUT,
      };
      let ct = ctx.current_task();
      let mtd = &mut*ct.get_mtd_ptr::<TaskHeader_AnyHeader>();
      mtd.ext2.fd = rfd;
      mtd.ext.epoll_interest = interest as i32 ;
      setup_done = true;

      let ictx = &*ctx.0.get();
      let outcome = (*ictx.fd_sink).send(ct);
      let failed = match outcome {
        Ok(_) => false,
        Err(_) => true,
      };
      need_retry = failed;
      ctx.write_task_dependency(TaskDependency::FDWait {
        need_requeue: need_retry
      });
      return Poll::Pending;
    }
    if need_retry {
      let ct = ctx.current_task();
      let ictx = &*ctx.0.get();
      let outcome = (*ictx.fd_sink).send(ct);
      let failed = match outcome {
        Ok(_) => false,
        Err(_) => true,
      };
      need_retry = failed;
      ctx.write_task_dependency(TaskDependency::FDWait {
        need_requeue: need_retry
      });
      return Poll::Pending;
    }
    return Poll::Ready(());
  })
}

pub fn yield_now() -> impl Future<Output = ()> {
  let mut first = true;
  core::future::poll_fn(move |ctx| unsafe {
    if first {
      first = false;
      let ctx: &mut TaskCtx = transmute(ctx);
      ctx.write_task_dependency(TaskDependency::Reschedule);
      return Poll::Pending;
    } else {
      return Poll::Ready(());
    }
  })
}

#[derive(Debug, Clone, Copy)]
pub enum TimerCreationFailure {
  ResourceExhaustion, InvalidPeriodTime
}
#[derive(Debug, Clone, Copy)]
pub enum TimerPeriodResetFailure {
  InvalidPeriodTime
}

pub struct PeriodicAlarm {
  timer_spec: libc::itimerspec,
  fd: i32,
  is_paused: bool, was_started: bool
}
impl PeriodicAlarm {
  pub fn new_periodic(
    fire_period: Duration
  ) -> Result<Self, TimerCreationFailure> { unsafe {
    const LIMIT: u128 = 999_999_999;
    let ns_time = fire_period.as_nanos();
    let s_time_period = ns_time / LIMIT;
    let ns_time_period =
      if s_time_period == 0 { ns_time }
      else { ns_time - (LIMIT * s_time_period)  };
    if ns_time_period > LIMIT || ns_time_period == 0 {
      return Err(TimerCreationFailure::InvalidPeriodTime);
    }
    let errno_loc = libc::__errno_location();
    let timer_fd = libc::timerfd_create(libc::CLOCK_REALTIME, libc::TFD_NONBLOCK);
    if timer_fd == -1 {
      let err_code = *errno_loc;
      match err_code {
        libc::ENOMEM |
        libc::ENFILE |
        libc::EMFILE => return Err(TimerCreationFailure::ResourceExhaustion),
        libc::ENODEV |
        libc::EPERM |
        libc::EINVAL | _ => unreachable!("createfd_timer unexpectedly failed with errcode {}", err_code)
      }
    }
    let ns_time_period = ns_time_period as i64;
    let s_time_period = s_time_period as i64;
    let timer_spec = libc::itimerspec {
      it_interval: libc::timespec {
        tv_sec: s_time_period,
        tv_nsec: ns_time_period,
      },
      it_value: libc::timespec {
        tv_sec: s_time_period,
        tv_nsec: ns_time_period,
      },
    };

    let timer = Self {
      timer_spec,
      fd: timer_fd,
      is_paused: false,
      was_started: false
    };
    return Ok(timer);
  } }
  pub fn set_new_period(&mut self, new_period: Duration) -> Result<(), TimerPeriodResetFailure>{ unsafe {
    const LIMIT: u128 = 999_999_999;
    let ns_time = new_period.as_nanos();
    let s_time_period = ns_time / LIMIT;
    let ns_time_period =
      if s_time_period == 0 { ns_time }
      else { ns_time - (LIMIT * s_time_period)  };
    if ns_time_period > LIMIT || ns_time_period == 0 {
      return Err(TimerPeriodResetFailure::InvalidPeriodTime);
    }
    let ns_time_period = ns_time_period as i64;
    let s_time_period = s_time_period as i64;
    let new_timer_spec = libc::itimerspec {
      it_interval: libc::timespec {
        tv_sec: s_time_period,
        tv_nsec: ns_time_period,
      },
      it_value: libc::timespec {
        tv_sec: s_time_period,
        tv_nsec: ns_time_period,
      },
    };
    let ret_val = libc::timerfd_settime(self.fd, 0, &new_timer_spec, &mut self.timer_spec);
    assert!(ret_val == 0, "timerfd_settime with code {}", *libc::__errno_location());
    self.timer_spec = new_timer_spec;
    return Ok(());
  } }
  pub fn is_paused(&self) -> bool {
    self.is_paused
  }
  pub fn start(&self) { unsafe {
    let ret_val = libc::timerfd_settime(self.fd, 0, &self.timer_spec, null_mut());
    assert!(ret_val == 0, "timerfd_settime with code {}", *libc::__errno_location());
  } }
  pub fn pause(&self) { unsafe {
    let mut old = self.timer_spec;
    let timer_spec = libc::itimerspec {
      it_interval: libc::timespec {
        tv_sec: 0,
        tv_nsec: 0,
      },
      it_value: libc::timespec {
        tv_sec: 0,
        tv_nsec: 0,
      },
    };
    let ret_val = libc::timerfd_settime(self.fd, 0, &timer_spec, &mut old);
    assert!(ret_val == 0);
  } }
  pub fn resume(&self) {
    let mut crap = MaybeUninit::<libc::itimerspec>::uninit();
    let ret_val = unsafe {
      libc::timerfd_settime(self.fd, 0, &self.timer_spec, crap.as_mut_ptr())
    };
    assert!(ret_val == 0);
  }
  pub fn cancel(self) { unsafe {
    loop {
      let ret_val = libc::close(self.fd) ;
      if ret_val != 0 {
        let err_code = *libc::__errno_location();
        match err_code {
          libc::EINTR => continue,
          _ => unreachable!("close failed unexpectedly with error code {}", err_code)
        }
      }
      break;
    }
  } }
}
impl Drop for PeriodicAlarm {
    fn drop(&mut self) { unsafe {
      loop {
        let ret_val = libc::close(self.fd) ;
        if ret_val != 0 {
          let err_code = *libc::__errno_location();
          match err_code {
            libc::EINTR => continue,
            _ => unreachable!("close failed unexpectedly with error code {}", err_code)
          }
        }
        break;
      }
    } }
}
impl AsFd for PeriodicAlarm {
  fn as_fd(&self) -> std::os::unix::prelude::BorrowedFd<'_> {
    unsafe { std::os::unix::prelude::BorrowedFd::borrow_raw(self.fd) }
  }
}


#[test]
fn t() {

  let rt = FaRT::new();

  rt.run_to_completion(async {
    println!("Hello!");

    let limit = 1_000_000;

    let atomic = AtomicU64::new(0);

    for _ in 0 .. limit {
      let atomic = addr_of!(atomic) as u64;
      launch_detached(async move {
        let atomic = unsafe{&*(atomic as *const AtomicU64)};
        atomic.fetch_add(1, Ordering::Relaxed);
      }).await;
    }
    loop {
      let val = atomic.load(Ordering::Relaxed);
      if val != limit {
        yield_now().await;
      } else { break }
    }

    // println!("{}", atomic.load(Ordering::Relaxed));
    assert!(atomic.load(Ordering::Relaxed) == limit);

    let mut val = 0;
    run_isolated(|| {
      for i in 0 .. 13 {
        val += i;
      }
    }).await;
    let t = (0 .. 13).reduce(core::ops::Add::add).unwrap();
    assert!(t == val);

    println!("Goodbye!");
  }).unwrap();
}
static mut DC: usize = 0;
struct D;
impl Drop for D {
  fn drop(&mut self) {
    unsafe { DC += 1; }
  }
}
#[test] #[ignore]
fn autodestruction() {
  let rt = FaRT::new();
  let item = D;
  rt.run_to_completion(async move {
    drop(item);
    println!("just dropped your shit");
  }).unwrap();
  assert!(unsafe { DC } == 1);
}

#[test]
fn large_frame_alloc() {
  use std::{fs::File, io::Read} ;
  let rt = FaRT::new();
  rt.run_to_completion(async {
    launch_detached(async {
      let mut f = File::open("/dev/urandom").unwrap();
      let mut b = [0u8;4096];
      let count = f.read(&mut b).unwrap();
      println!("read {} bytes\n{:#?}", count, b);

    }).await;
  }).unwrap();
}

#[test]
fn sock() {

  let rt = FaRT::new();
  rt.run_to_completion(async {

    let socket = std::net::TcpListener::bind("localhost:19193").unwrap();
    socket.set_nonblocking(true).unwrap();

    loop {
      wait_on_fd(&socket, FdInterest::Read).await;
      match socket.accept() {
        Ok((stream, _)) => {
          launch_detached(process_incoming(stream)).await;
        },
        Err(err) => {
          println!("{}", err);
          return;
        },
      };
    }
  }).unwrap();

  async fn process_incoming(stream: std::net::TcpStream) {
    let stream = stream;
    stream.set_nonblocking(true).unwrap();

    wait_on_fd(&stream, FdInterest::Read).await;


    println!("Pise4ka!")
  }
}


#[test] #[ignore]
fn timer_test() {
  let rt = FaRT::new();
  rt.run_to_completion(async {
    let mut alarm = PeriodicAlarm::new_periodic(Duration::from_secs(2)).unwrap();
    alarm.start();
    alarm.pause();
    alarm.resume();
    let start = std::time::Instant::now();
    println!("began waiting on the thing");
    wait_on_fd(&alarm, FdInterest::Read).await;
    println!("waiting finished. Spent {:?}", start.elapsed());
    alarm.set_new_period(Duration::from_secs(5)).unwrap();
    wait_on_fd(&alarm, FdInterest::Read).await;
    println!("waiting finished. Spent {:?}", start.elapsed());
  }).unwrap();
}