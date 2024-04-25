use core::{cell::UnsafeCell, mem::{size_of, transmute, MaybeUninit}, ptr::{addr_of, addr_of_mut, null_mut}, sync::atomic::{fence, AtomicBool, AtomicU32, AtomicU64, AtomicUsize, Ordering}, time::Duration};

use crate::{driver_async::TaskRef, futex, root_alloc::{Block4KPtr, RootAllocator}, utils::{publish_changes_on_memory, PageSource}};

macro_rules! static_assert {
    ($cond:expr) => {
      const _ : () = if !$cond { std::panic!("Comptime assert failed!") } ;
    };
    ($cond:expr, $msg:expr) => {
      const _ : () = if !$cond { panic!($msg) } ;
    };
}

const MAP_LEN: usize = 4;

#[repr(C)]
struct Metadata {
  submit_map: MaybeUninit<[AtomicU64;MAP_LEN]>,
  ready_map: MaybeUninit<[AtomicU64;MAP_LEN]>,
  next_page: AtomicUsize,
}
const FDS_MAX: usize = (4096 - size_of::<Metadata>()) / (size_of::<TaskRef>() * 2);
#[repr(C)] #[repr(align(4096))]
struct FDPage {
  submit_map: MaybeUninit<[AtomicU64;MAP_LEN]>,
  submit_fds: [TaskRef;FDS_MAX],
  ready_map: MaybeUninit<[AtomicU64;MAP_LEN]>,
  ready_fds: MaybeUninit<[TaskRef;FDS_MAX]>,
  next_page: AtomicUsize,
}
static_assert!(size_of::<FDPage>() == 4096);

const FIRST_INVALID_IX: usize = 64 - ((8*8*MAP_LEN) - FDS_MAX);

pub(crate) struct FDTable(UnsafeCell<FDReactorInner>);
struct FDReactorInner {
  first_page: AtomicU64,
}
impl FDTable {
  pub(crate)fn new() -> Self {
    Self(UnsafeCell::new(FDReactorInner {
      first_page: AtomicU64::new(0),
    }))
  }
  fn inner(&self) -> &mut FDReactorInner {
    unsafe { &mut *self.0.get() }
  }
  fn is_uninit(&self) -> bool {
    let inner = self.inner();
    inner.first_page.load(Ordering::Relaxed) == 0
  }
  #[inline(always)]
  fn setup_page(page: &Block4KPtr) {
    let ptr = page.get_ptr().cast::<Metadata>();
    unsafe { ptr.write(Metadata {
      submit_map: MaybeUninit::zeroed(),
      ready_map: MaybeUninit::zeroed(),
      next_page: AtomicUsize::new(0)
    }); }
  }
  #[inline(always)]
  fn do_first_init(&self, page: Block4KPtr) {
    Self::setup_page(&page);
    let ptr = page.get_ptr();
    self.inner().first_page.store(ptr as _, Ordering::Release);
  }
  #[inline(always)]
  fn get_page_ptr(&self) -> *mut FDPage {
    self.inner().first_page.load(Ordering::Acquire) as _
  }
  #[must_use]
  pub(crate) fn tx_try_put(&self, task: TaskRef, page_source: &dyn PageSource) -> bool {
    self.tx_try_put_impl(task, page_source, false)
  }
  pub(crate) fn tx_try_get(&self) -> Option<TaskRef> {
    let item = self.get_page_ptr();
    if item.is_null() { return None; }
    let mut ptr = item as *mut FDPage;
    let mut segment_map_ref = unsafe {
      (*ptr).ready_map.assume_init_ref()
    };
    let (ix, six) = 'free_slot_search: loop {
      'map_traverse:for i in 0 .. MAP_LEN {
        let segment = &segment_map_ref[i];
        let map = segment.load(Ordering::Acquire);
        let index = map.trailing_zeros();
        let reached_map_end =
          i == (MAP_LEN - 1) && (index as usize == FIRST_INVALID_IX);
        if reached_map_end { break 'map_traverse }
        let reached_segment_end = index == 64;
        if reached_segment_end { continue 'map_traverse }

        break 'free_slot_search (index as usize, i);
      }
      let next = unsafe { (*ptr).next_page.load(Ordering::Acquire) };
      if next == 0 { return None };
      ptr = next as _;
      segment_map_ref = unsafe { (*ptr).ready_map.assume_init_ref() };
      continue 'free_slot_search;
    };
    unsafe {
      let addr = addr_of_mut!((*ptr).ready_fds.assume_init_mut()[(six * 64) + ix]);
      let val = addr.read();
      let mask = 1 << ix;
      let prior = segment_map_ref[six].fetch_and(!mask, Ordering::Release);

      let taken_value = prior & mask != 0;
      debug_assert!(taken_value, "Taken garbage!");

      return Some(val);
    }
  }
  pub(crate)fn rx_try_get(&self) -> Option<TaskRef> {

    let mut ptr = self.get_page_ptr();
    if ptr.is_null() { return None; }
    let mut segment_map_ref = unsafe {
      (*ptr).submit_map.assume_init_ref()
    };
    let (ix, six) = 'free_slot_search: loop {
      'map_traverse:for i in 0 .. MAP_LEN {
        let segment = &segment_map_ref[i];
        let map = segment.load(Ordering::Acquire);
        let index = map.trailing_zeros();
        let reached_map_end =
          i == (MAP_LEN - 1) && (index as usize == FIRST_INVALID_IX);
        if reached_map_end { break 'map_traverse }
        let reached_segment_end = index == 64;
        if reached_segment_end { continue 'map_traverse }

        break 'free_slot_search (index as usize, i);
      }
      let next = unsafe { (*ptr).next_page.load(Ordering::Acquire) };
      if next == 0 { return None };
      ptr = next as _;
      segment_map_ref = unsafe { (*ptr).submit_map.assume_init_ref() };
      continue 'free_slot_search;
    };
    unsafe {
      let addr = addr_of_mut!((*ptr).submit_fds[(six * 64) + ix]);
      let fd = addr.read();
      let mask = 1 << ix;
      let prior = segment_map_ref[six].fetch_and(!mask, Ordering::Release);
      let taken_value = prior & mask != 0;
      debug_assert!(taken_value, "Taken garbage!");

      return Some(fd);
    }
  }
  // reciever end wishing to publish awaited fd wont ever find itself in a need to find mem
  // or observe thit object as uninit
  pub(crate) fn rx_put_ready(&self, task:TaskRef) {
    let ptr = self.get_page_ptr();
    debug_assert!(!ptr.is_null());
    let mut ptr = self.get_page_ptr();
    let mut segment_map_ref = unsafe {
      (*ptr).ready_map.assume_init_ref()
    };
    let (ix, six) = 'free_slot_search: loop {
      'map_traverse:for i in 0 .. MAP_LEN {
        let segment = &segment_map_ref[i];
        let map = segment.load(Ordering::Acquire);
        let index = map.trailing_ones();
        let reached_map_end =
          i == (MAP_LEN - 1) && (index as usize == FIRST_INVALID_IX);
        if reached_map_end { break 'map_traverse }
        let reached_segment_end = index == 64;
        if reached_segment_end { continue 'map_traverse }
        break 'free_slot_search (index as usize, i);
      }
      let next = unsafe { (*ptr).next_page.load(Ordering::Acquire) };
      assert!(next != 0);
      ptr = next as _;
      segment_map_ref = unsafe { (*ptr).ready_map.assume_init_ref() };
      continue 'free_slot_search;
    };
    unsafe {
      let index = (six * 64) + ix;
      let addr = addr_of_mut!((*ptr).ready_fds.assume_init_mut()[index]);
      addr.write(task);
      let mask = 1 << ix;
      let prior = segment_map_ref[six].fetch_or(mask, Ordering::Release);
      let untaken = mask & prior == 0;
      debug_assert!(untaken, "Impossible index collision happened!");
    }
  }
}
impl FDTable {
  #[inline(always)]
  pub(crate) fn tx_try_put_impl(
    &self,
    task: TaskRef,
    page_source: &dyn PageSource,
    in_test_mode:bool
  ) -> bool {
    if self.is_uninit() {
      let page = match page_source.try_get_page() {
        Some(page) => page,
        None => return false,
      };
      Self::setup_page(&page);
      self.do_first_init(page);
    }
    let mut ptr = self.get_page_ptr();
    let mut segment_map_ref = unsafe {
      (*ptr).submit_map.assume_init_ref()
    };
    let (ix, six) = 'free_slot_search: loop {
      'map_traverse:for i in 0 .. MAP_LEN {
        let segment = &segment_map_ref[i];
        let map = segment.load(Ordering::Acquire);
        let index = map.trailing_ones();
        let reached_map_end =
          i == (MAP_LEN - 1) && (index as usize == FIRST_INVALID_IX);
        if reached_map_end { break 'map_traverse }
        let reached_segment_end = index == 64;
        if reached_segment_end { continue 'map_traverse }
        break 'free_slot_search (index as usize, i);
      }
      let next = unsafe { (*ptr).next_page.load(Ordering::Acquire) };
      let next = if next == 0 {
        let page = match page_source.try_get_page() {
          Some(page) => page,
          None => return false,
        };
        Self::setup_page(&page);
        let next = page.get_ptr();
        unsafe { (*ptr).next_page.store(next as usize, Ordering::Release) };
        next.cast::<FDPage>()
      } else {
        next as _
      };
      ptr = next;
      segment_map_ref = unsafe { (*ptr).submit_map.assume_init_ref() };
      continue 'free_slot_search;
    };
    unsafe {
      let index = (six * 64) + ix;
      let addr = addr_of_mut!((*ptr).submit_fds[index]);
      addr.write(task);
      if !in_test_mode {
        task.publish_backing_memory_changes();
      }
      let mask = 1 << ix;
      let prior = segment_map_ref[six].fetch_or(mask, Ordering::Release);

      let untaken = prior & mask == 0;
      debug_assert!(untaken, "Impossible index collision happened!")
    }
    return true;
  }
}

#[test]
fn tx_rx_inout() {
  let mut s = RootAllocator::new();
  let r = FDTable::new();
  for i in 0 .. FDS_MAX {
    let ok = r.tx_try_put_impl(unsafe {transmute(i)}, &mut s, true);
    assert!(ok);
  }
  let p = unsafe {&*r.get_page_ptr()};
  assert!(p.next_page.load(Ordering::Relaxed) == 0);
  let sm = unsafe {p.submit_map.assume_init_ref()};
  for i in &sm[..(MAP_LEN - 1)] {
    assert!(u64::MAX == i.load(Ordering::Relaxed));
  }
  let span = 8*8*MAP_LEN - FDS_MAX;
  let correct_last = !(((1 << span) - 1) << (64 - span));
  assert!(sm[MAP_LEN - 1].load(Ordering::Relaxed) == correct_last);
  let ok = r.tx_try_put_impl(unsafe {transmute(FDS_MAX + 1)}, &mut s, true);
  assert!(ok);
  assert!(p.next_page.load(Ordering::Relaxed) != 0);
  for i in 0 .. FDS_MAX  {
    let v = r.rx_try_get().unwrap();
    assert!(i == unsafe { transmute(v) } );
  }
  let v = r.rx_try_get().unwrap();
  assert!(unsafe {transmute::<_, usize>(v)} == FDS_MAX + 1);
  for i in &sm[..MAP_LEN] {
    assert!(0 == i.load(Ordering::Relaxed));
  }
}

#[test]
fn tx_rx_tx() {
  let mut s = RootAllocator::new();
  let r = FDTable::new();
  let limit = FDS_MAX * 4;
  for i in 0 .. limit {
    let ok = r.tx_try_put_impl(unsafe {transmute(i)}, &mut s, true);
    assert!(ok);
  }
  for _ in 0 .. limit {
    let fd = r.rx_try_get().unwrap();
    r.rx_put_ready(fd)
  }
  for i in 0 .. limit {
    let ok = r.tx_try_get().unwrap();
    assert!(i == unsafe {transmute::<_, usize>(ok)})
  }
}

unsafe impl Sync for FDTable {}

#[test]
fn to_production_check() {

  struct Env {
    fd_table: FDTable,
    alloc: RootAllocator
  }
  let env = Env {
    fd_table: FDTable::new(),
    alloc: RootAllocator::new()
  };

  let env_addr1 = addr_of!(env) as u64;
  const LIMIT: usize = 4096*4;

  let tx = std::thread::spawn(move || {
    let env = unsafe{ &*(env_addr1 as *const Env) };
    let mut ix = 0u64;
    loop {
      let ok = env.fd_table.tx_try_put_impl(unsafe{transmute(ix)}, &env.alloc, true);
      assert!(ok);
      ix += 1;
      if ix == LIMIT as _ { return }
    }
  });
  tx.join().unwrap();
  let mut vec = Vec::<u64>::new();
  vec.reserve(LIMIT);
  for _ in 0 .. LIMIT {
    let smth = env.fd_table.rx_try_get().unwrap();
    let v = unsafe{transmute(smth)};
    vec.push(v);
  }
  vec.sort();
  for i in 0 .. LIMIT {
    assert!(i == vec[i] as usize)
  }
}

#[test] #[ignore = "BECAUSE IT DOESNT FUCKING WORK"]
fn threaded_prod_cons_check_few_times_more() {
  let total_count = 64*2;
  let mut fail_count = 0;
  for _ in 0 .. total_count {
    std::panic::set_hook(Box::new(|_|{}));
    let result = std::panic::catch_unwind(|| {
      threaded_prod_cons_check_()
    });
    match result {
      Ok(_) => (),
      Err(_) => {
        fail_count += 1;
      },
    }
  }
  let per = (fail_count as f32 / total_count as f32) * 100.0;
  println!(
    "Failed {} times in {} runs, {}% failure rate",
    fail_count, total_count, per
  );
  assert!(
    fail_count == 0
  );
}


#[test] #[ignore]
fn threaded_prod_cons_check_() {

  struct Env {
    tx_salt: futex::Token,
    rx_salt: futex::Token,
    fd_table: FDTable,
    alloc: RootAllocator,
    kill_rx_side: AtomicBool
  }
  let env = Env {
    tx_salt: futex::Token::new(),
    rx_salt: futex::Token::new(),
    fd_table: FDTable::new(),
    alloc: RootAllocator::new(),
    kill_rx_side: AtomicBool::new(false)
  };

  let env_addr2 = addr_of!(env) as u64;

  const LIMIT: usize = FDS_MAX;
  const SHOULD_LOG:bool = false;

  let rx = std::thread::spawn(move ||{
    let env = unsafe{ &*(env_addr2 as *const Env) };
    let mut salt = 0;
    loop {
      if env.kill_rx_side.load(Ordering::Relaxed) { break; }
      if let Some(actual) = futex::futex_wait(&env.rx_salt, salt, Duration::from_micros(100)) {
        salt = actual;
        if SHOULD_LOG {
          println!("Consumer found stale value");
        }
      }
      fence(Ordering::AcqRel);
      let smth = env.fd_table.rx_try_get();
      match smth {
        Some(item) => {
          let n:u64 = unsafe{transmute(item)};
          if SHOULD_LOG {
            println!("Consumer got {}", n);
          }
          fence(Ordering::AcqRel);
          env.fd_table.rx_put_ready(item);
          fence(Ordering::AcqRel);
          futex::futex_wake(&env.tx_salt);
          if SHOULD_LOG {
            println!("Consumer put {}", n);
          }
        },
        None => {
          if SHOULD_LOG {
            println!("Consumer got nothing");
          }
        },
      }
      if SHOULD_LOG {
        println!("Consumer awoken producer");
      }
    }
    if SHOULD_LOG {
      println!("Consumer has exited");
    }
  });
  let mut items = Vec::<u64>::new();
  items.reserve(LIMIT);
  let mut salt = 0;
  let mut ix = 0u64;
  let mut count = 0;
  use std::fmt::Write;
  let mut log = String::new();
  fence(Ordering::AcqRel);
  loop {
    let ok = env.fd_table.tx_try_put_impl(unsafe{ transmute(ix) }, &env.alloc, true);
    assert!(ok);
    ix += 1;
    if SHOULD_LOG {
      writeln!(&mut log, "{}: Producer put {}", ix, ix).unwrap();
    }
    fence(Ordering::AcqRel);
    let awoken = futex::futex_wake(&env.rx_salt);
    if awoken && SHOULD_LOG {
      writeln!(&mut log, "{}: Producer awoken consumer", ix).unwrap();
    } else {
      writeln!(&mut log, "{}: Producer HAS NOT awaken consumer", ix).unwrap();
    }
    if let Some(actual) = futex::futex_wait(&env.tx_salt, salt, Duration::from_micros(100)) {
      salt = actual;
      if SHOULD_LOG {
        println!("{}: Producer found stale value", ix);
      }
    }
    fence(Ordering::AcqRel);
    let item = env.fd_table.tx_try_get();
    match item {
      Some(item) => {
        let v = unsafe{ transmute(item) };
        if SHOULD_LOG {
          writeln!(&mut log, "{}: Producer awoken. Got {}", ix, v).unwrap();
        }
        items.push(v);
        count += 1;
        if count == LIMIT as _ { break; }
      },
      None => {
        if SHOULD_LOG {
          writeln!(&mut log, "{}: Producer awoken, Got nothing!", ix).unwrap();
        }
      },
    }
  }

  fence(Ordering::AcqRel);
  if SHOULD_LOG {
    println!("---\n{}", log);
  }

  env.kill_rx_side.store(true, Ordering::Release);
  rx.join().unwrap();

  items.sort();
  // println!("{:#?}", items);

  let len = items.len();
  let items_lost = LIMIT - len;
  assert!(items_lost == 0, "Lost items {}", items_lost);
  for i in 0 .. LIMIT {
    let item = items[i];
    assert!(item == i as u64, "Mismatch {} {}", i, item)
  }

  if SHOULD_LOG {
    println!("---\n{}", log);
    println!("DONE!");
  }
}

