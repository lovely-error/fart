use core::{cell::UnsafeCell, future::Future, marker::PhantomData, mem::{align_of, needs_drop, size_of, transmute, ManuallyDrop, MaybeUninit}, ptr::addr_of, sync::atomic::{fence, AtomicU32, AtomicU64, AtomicUsize, Ordering}, task::Poll};

use crate::{block_allocator::RawMemoryPtr, cl_lock::SmallLock, driver_async::{TaskCtx, TaskDependency, TaskRef}, launch_detached, FaRT};

#[repr(C)]
union Heads {
  both: ManuallyDrop<AtomicUsize>,
  either: ManuallyDrop<(AtomicU32, AtomicU32)>
}

#[repr(C)]
struct Metadata {
  heads: Heads,
  parked_task: AtomicU64,
  rc_count: AtomicU64,
}

pub struct PipeIn<T>(UnsafeCell<PipeInInner>, PhantomData<T>);
struct PipeInInner {
  ptr: RawMemoryPtr,
  end_index: u32,
}
#[derive(Debug, Clone, Copy)]
pub enum SendFailure {
  RecieverDisconnected
}
impl<T> PipeIn<T> {
  fn inner(&self) -> &mut PipeInInner {
    unsafe { &mut *self.0.get() }
  }
  fn backing_store_ref(&self) -> (&SmallLock<Metadata>, *mut ()) {
    let ptr = self.inner().ptr.get_ptr();
    let data_ptr = ptr.map_addr(|a| (a + size_of::<SmallLock<Metadata>>()).next_multiple_of(align_of::<T>()));
    let mtd_ptr = data_ptr.map_addr(|a| a - size_of::<SmallLock<Metadata>>()).cast::<SmallLock<Metadata>>();
    return (unsafe{&*mtd_ptr}, data_ptr);
  }
  pub fn drop(self) -> impl Future<Output = ()> {
    let inner = self.inner();
    let capacity = inner.end_index;
    let mref = inner.ptr;
    let (mtd, ptr) = self.backing_store_ref();
    let data_ptr = ptr as u64;
    let mtd_ptr = addr_of!(*mtd) as u64;
    core::future::poll_fn(move |ctx| unsafe {
      let lock = &*(mtd_ptr as *const SmallLock<Metadata>);
      let data_ptr = data_ptr as *mut ();
      let ctx: &mut TaskCtx = transmute(ctx);
      let mtd = match lock.try_lock() {
        Some(mtd) => mtd,
        None => return Poll::Ready(()),
      };
      let prior = mtd.rc_count.fetch_sub(1, Ordering::Relaxed);
      if prior == 1 {
        let heads = mtd.heads.both.load(Ordering::Relaxed);
        let wix = (heads & ((1 << 32) - 1)) as u32;
        let mut rix = (heads >> 32) as u32;
        let need_drop = wix != rix;
        if needs_drop::<T>() && need_drop {
          loop {
            let ptr = data_ptr.map_addr(|a| a + size_of::<T>() * rix as usize).cast::<T>();
            ptr.drop_in_place();
            rix += 1;
            if rix == capacity { rix = 0 }
            if rix == wix { break }
          }
        }
        fence(Ordering::AcqRel);
        mref.release_memory(&*ctx.inner().mem_router);
        return Poll::Ready(());
      } else {
        lock.release();
        return Poll::Ready(());
      }
    })
  }
  pub fn put(&self, item: T) -> impl Future<Output = Result<(), SendFailure>> {
    let end_index = self.inner().end_index;
    let mut item_ = MaybeUninit::<T>::uninit();
    item_.write(item);
    let (mtd, data) = self.backing_store_ref();
    let data_ptr = data as u64;
    let mtd = addr_of!(*mtd) as u64;
    let mut parked_consumer: Option<TaskRef> = None;
    let mut can_resume_immidiately = false;
    core::future::poll_fn(move |ctx| unsafe {
      let lock = &*(mtd as *const SmallLock<Metadata>);
      let data = data_ptr as *mut T;
      let ctx: &mut TaskCtx = transmute(ctx);
      if let Some(parked_consumer_) = parked_consumer {
        let owned = parked_consumer_.try_aquire_ownership();
        if owned {
          let inner = ctx.inner();
          let ok = (*inner.task_set).enque(parked_consumer_, &*inner.mem_router);
          if ok {
            // we have dealt with the orphaned consumer
            parked_consumer = None;
            if can_resume_immidiately {
              // its okay to just fallthrough
              ()
            } else {
              // we cant resume right away, because the only way we got here
              // is through observing that pipe is full.
              // wait for consumer to unclutter the pipe
              ctx.write_task_dependency(TaskDependency::Reschedule);
              return Poll::Pending;
            }
          } else {
            // we did not enhomed our orphan so retry doing it
            ctx.write_task_dependency(TaskDependency::Reschedule);
            return Poll::Pending;
          }
        } else {
          // we havent not had parked task owned. retry
          ctx.write_task_dependency(TaskDependency::Reschedule);
          return Poll::Pending;
        }
      }
      let current_task = ctx.current_task();
      let Some(mtd) = lock.try_lock() else {
        let inner = ctx.inner();
        let _ = (*inner.task_set).enque(current_task, &*inner.mem_router);
        ctx.write_task_dependency(TaskDependency::Reschedule);
        return Poll::Pending;
      };
      let rc = mtd.rc_count.load(Ordering::Relaxed);
      if rc == 1 {
        item_.assume_init_drop();
        return Poll::Ready(Err(SendFailure::RecieverDisconnected));
      }
      let ixs = mtd.heads.both.load(Ordering::Acquire);
      let old_wix = (ixs & ((1 << 32) - 1)) as u32;
      let rix = (ixs >> 32) as u32;
      let next_wix = old_wix + 1;
      let next_wix = next_wix * ((next_wix != end_index) as u32);
      let full = next_wix == rix ;
      fence(Ordering::SeqCst);
      if full {
        current_task.publish_backing_memory_changes();
        let prior = mtd.parked_task.swap(transmute(current_task), Ordering::AcqRel);
        // we've parked ourselves
        let consumer_parked = prior != transmute(current_task) && prior != 0;
        if consumer_parked {
          let consumer_task = transmute::<_, TaskRef>(prior);
          let got_owned = consumer_task.try_aquire_ownership();
          if got_owned {
            let inner = ctx.inner();
            let ok = (*inner.task_set).enque(consumer_task, &*inner.mem_router);
            if ok {
              // we enqueed consumer . it will unclutter the pipe
              ctx.write_task_dependency(TaskDependency::Release);
              lock.release();
              return Poll::Pending;
            } else {
              // failed to enq consumer. retry
              can_resume_immidiately = false;
              parked_consumer = Some(consumer_task);
              ctx.write_task_dependency(TaskDependency::Reschedule);
              lock.release();
              return Poll::Pending;
            }
          } else {
            // we failed to own consumer. retry owning it later
            can_resume_immidiately = false;
            parked_consumer = Some(consumer_task);
            ctx.write_task_dependency(TaskDependency::Reschedule);
            lock.release();
            return Poll::Pending;
          }
        } else {
          // conumer will resume this producer
          ctx.write_task_dependency(TaskDependency::Release);
          lock.release();
          return Poll::Pending;
        }
      }
      fence(Ordering::AcqRel);
      debug_assert!(next_wix < end_index);
      debug_assert!(old_wix < end_index);

      let slot = data.cast::<T>().map_addr(|a| a + (size_of::<T>() * old_wix as usize));
      slot.write(item_.assume_init_read());
      mtd.heads.either.0.store(next_wix as u32, Ordering::Release);

      // resume consumer
      let prior = mtd.parked_task.swap(0, Ordering::AcqRel);
      let consumer_parked = prior != transmute(current_task) && prior != 0;
      if consumer_parked {
        let consumer_task = transmute::<_, TaskRef>(prior);
        let got_owned = consumer_task.try_aquire_ownership();
        if got_owned {
          let inner = ctx.inner();
          let ok = (*inner.task_set).enque(consumer_task, &*inner.mem_router);
          if ok {
            // we enqueed consumer . it will unclutter the pipe.
            // its okay to fallthrough
            ()
          } else {
            // failed to enq consumer. retry
            can_resume_immidiately = false;
            parked_consumer = Some(consumer_task);
            ctx.write_task_dependency(TaskDependency::Reschedule);
            lock.release();
            return Poll::Pending;
          }
        } else {
          // we failed to own consumer. retry owning it later
          can_resume_immidiately = false;
          parked_consumer = Some(consumer_task);
          ctx.write_task_dependency(TaskDependency::Reschedule);
          lock.release();
          return Poll::Pending;
        }
      }

      lock.release();
      return Poll::Ready(Ok(()));
    })
  }
  // fn try_send(&self, item: T) -> impl Future<Output = Result<(), SendFailure<T>>> {

  // }
}
unsafe impl<T> Send for PipeIn<T> {}
unsafe impl<T> Sync for PipeIn<T> {}

#[derive(Debug, Clone, Copy)]
pub enum RecieveFailure {
  SenderDisconnected
}
pub struct PipeOut<T>(UnsafeCell<PipeOutInner>, PhantomData<T>);
struct PipeOutInner {
  ptr: RawMemoryPtr,
  end_index: u32,
}
impl<T> PipeOut<T> {
  fn inner(&self) -> &mut PipeOutInner {
    unsafe { &mut*self.0.get() }
  }
  fn backing_store_ref(&self) -> (&SmallLock<Metadata>, *mut ()) {
    let ptr = self.inner().ptr.get_ptr();
    let data_ptr = ptr.map_addr(|a| (a + size_of::<SmallLock<Metadata>>()).next_multiple_of(align_of::<T>()));
    let mtd_ptr = data_ptr.map_addr(|a| a - size_of::<SmallLock<Metadata>>()).cast::<SmallLock<Metadata>>();
    return (unsafe{&*mtd_ptr}, data_ptr);
  }
  pub fn drop(self) -> impl Future<Output = ()> {
    let capacity = self.inner().end_index;
    let mref = self.inner().ptr;
    let (mtd, data_ptr) = self.backing_store_ref();
    let data_ptr = data_ptr as u64;
    let mtd_ptr = addr_of!(*mtd) as u64;
    core::future::poll_fn(move |ctx| unsafe {
      let lock = &*(mtd_ptr as *const SmallLock<Metadata>);
      let data_ptr = data_ptr as *mut ();
      let ctx: &mut TaskCtx = transmute(ctx);
      let mtd = match lock.try_lock() {
        Some(mtd) => mtd,
        None => return Poll::Ready(()),
      };
      let prior = mtd.rc_count.fetch_sub(1, Ordering::Relaxed);
      if prior == 1 {
        let heads = mtd.heads.both.load(Ordering::Relaxed);
        let wix = (heads & ((1 << 32) - 1)) as u32;
        let mut rix = (heads >> 32) as u32;
        let need_drop = wix != rix;
        if needs_drop::<T>() && need_drop {
          loop {
            let ptr = data_ptr.map_addr(|a| a + size_of::<T>() * rix as usize).cast::<T>();
            ptr.drop_in_place();
            rix += 1;
            if rix == capacity { rix = 0 }
            if rix == wix { break }
          }
        }
        fence(Ordering::AcqRel);
        mref.release_memory(&*ctx.inner().mem_router);
        return Poll::Ready(());
      } else {
        lock.release();
        return Poll::Ready(());
      }
    })
  }
  pub fn get(&self) -> impl Future<Output = Result<T, RecieveFailure>> {
    let inner_self = self.inner();
    let end_index = inner_self.end_index;
    let (mtd, data_ptr) = self.backing_store_ref();
    let data_ptr = data_ptr as u64;
    let mtd_ptr = addr_of!(*mtd) as u64;
    let mut parked_producer: Option<TaskRef> = None;
    core::future::poll_fn(move |ctx| unsafe {
      let data = data_ptr as *mut T;
      let lock = &*(mtd_ptr as *const SmallLock<Metadata>);
      let ctx: &mut TaskCtx = transmute(ctx);
      if let Some(parked) = parked_producer {
        let owned = parked.try_aquire_ownership();
        if owned {
          let inner = ctx.inner();
          let ok = (*inner.task_set).enque(parked, &*inner.mem_router);
          if ok {
            parked_producer = None;
            // cant resume right away
            ctx.write_task_dependency(TaskDependency::Reschedule);
            return Poll::Pending;
          } else {
            // we did not enhomed our orphan so retry doing it
            ctx.write_task_dependency(TaskDependency::Reschedule);
            return Poll::Pending;
          }
        } else {
          // we havent not had parked task owned. retry
          ctx.write_task_dependency(TaskDependency::Reschedule);
          return Poll::Pending;
        }
      }
      let current_task = ctx.current_task();
      let Some(mtd) = lock.try_lock() else {
        let inner = ctx.inner();
        let _ = (*inner.task_set).enque(current_task, &*inner.mem_router);
        ctx.write_task_dependency(TaskDependency::Reschedule);
        return Poll::Pending;
      };
      let ixs = mtd.heads.both.load(Ordering::Acquire);
      let wix = (ixs & ((1 << 32) - 1)) as u32;
      let old_rix = (ixs >> 32) as u32;
      let next_rix = old_rix + 1;
      let real_rix = next_rix * ((next_rix != end_index) as u32);
      let empty = wix == real_rix ;
      fence(Ordering::SeqCst);
      if empty {
        let rc = mtd.rc_count.load(Ordering::Relaxed);
        if rc == 1 {
          lock.release();
          return Poll::Ready(Err(RecieveFailure::SenderDisconnected));
        }
        current_task.publish_backing_memory_changes();
        let prior = mtd.parked_task.swap(transmute(current_task), Ordering::AcqRel);
        let producer_parked = prior != transmute(current_task) && prior != 0;
        if producer_parked {
          let prod: TaskRef = transmute(prior);
          if prod.try_aquire_ownership() {
            // resume the producer
            let inner = ctx.inner();
            let ok = (*inner.task_set).enque(prod, &*inner.mem_router);
            if !ok {
              // this task is responsible for resuming producer. need retry
              parked_producer = Some(prod);
              ctx.write_task_dependency(TaskDependency::Reschedule);
              lock.release();
              return Poll::Pending;
            } else {
              // we can release ourselve
              ctx.write_task_dependency(TaskDependency::Release);
              lock.release();
              return Poll::Pending;
            }
          } else {
            // failed to own producer. need retry
            parked_producer = Some(prod);
            ctx.write_task_dependency(TaskDependency::Reschedule);
            lock.release();
            return Poll::Pending;
          }
        } else {
          // we've parked our selves and waiting for producer to resume us!
          ctx.write_task_dependency(TaskDependency::Release);
          lock.release();
          return Poll::Pending;
        }
      }
      fence(Ordering::AcqRel);
      debug_assert!(real_rix < end_index);
      // its okay to recompute these . read index wouldnt change in next attempt
      let result = data.map_addr(|a| a + (size_of::<T>() * real_rix as usize)).read();
      mtd.heads.either.1.store(real_rix as u32, Ordering::Release);
      lock.release();
      return Poll::Ready(Ok(result));
    })
  }
}
unsafe impl<T> Send for PipeOut<T> {}
unsafe impl<T> Sync for PipeOut<T> {}



#[derive(Debug)]
pub enum PipeCreationFailure {
  InvalidCapacity
}

pub fn pipe<T>(capacity: u32) -> impl Future<Output = Result<(PipeIn<T>, PipeOut<T>), PipeCreationFailure>> {
  core::future::poll_fn(move |ctx| unsafe {
    if capacity == 0 { return Poll::Ready(Err(PipeCreationFailure::InvalidCapacity)) }

    let ctx: &mut TaskCtx = transmute(ctx);
    let inner = ctx.inner();
    // we cant have <3 because of how indexing works
    let capacity = capacity.max(3);
    type Mtd = SmallLock<Metadata>;
    let size = size_of::<Mtd>().next_multiple_of(
      align_of::<T>()
    ) + (size_of::<T>() * capacity as usize);
    let mptr = match (*inner.mballoc).smalloc(size, align_of::<Mtd>(), &*inner.mem_router) {
      Ok(mptr) => mptr,
      Err(err) => {
        todo!("{:?}", err)
      },
    };
    let ptr = mptr.get_ptr().map_addr(|a| (a + size_of::<Mtd>()).next_multiple_of(align_of::<T>()));
    let mtd = ptr.map_addr(|a| a - size_of::<Mtd>()).cast::<Mtd>();
    mtd.write(SmallLock::new(Metadata {
      heads: Heads { either: ManuallyDrop::new((AtomicU32::new(0), AtomicU32::new(capacity-1))) },
      parked_task: AtomicU64::new(0),
      rc_count: AtomicU64::new(2),
    }));

    let pin = PipeIn(UnsafeCell::new(PipeInInner {
      ptr: mptr,
      end_index: capacity,
    }), PhantomData);
    let pout = PipeOut(UnsafeCell::new(PipeOutInner {
      ptr: mptr,
      end_index: capacity,
    }), PhantomData);

    return Poll::Ready(Ok((pin,pout)));
  })
}



#[test]
fn basic_squezing_through_pipes() {
  let rt = FaRT::new_with_thread_count(1);
  rt.run_to_completion(async {

    let (tx, rx) = pipe::<u32>(1).await.unwrap();

    let limit = 1024;

    launch_detached(async move {
      let rx = rx;
      for i in 1 .. limit+1 {
        let v = rx.get().await;
        match v {
          Ok(val) => assert!(val == i),
          Err(err) => panic!("{:?}", err),
        }
      }
      rx.drop().await;
    }).await;

    for i in 1 .. limit + 1 {
      let _ = tx.put(i).await.unwrap();
    }

    tx.drop().await;

  }).unwrap();
}


#[test] #[ignore = "it races"]
fn not_so_basic_squezing_through_pipes() {
  let rt = FaRT::new_with_thread_count(2);
  rt.run_to_completion(async {

    let limit = 1024;
    let mut pipes = Vec::new();

    for i in 0 .. limit {
      let (tx, rx) = pipe::<usize>(1).await.unwrap();
      launch_detached(async move {
        let rx = rx;
        let mut items = Vec::new();
        for _ in 0 .. limit {
          let v = rx.get().await;
          match v {
            Ok(val) => {
              items.push(val)
            },
            Err(err) => panic!("Reciever panicked {:?}", err),
          }
        }
        rx.drop().await;
        items.sort();
        for k in 0 .. limit {
          let got = items[k];
          if got != k {
            println!("item mismatch in pipe {}. expected {}, got {}", i, k, got);
            break;
          }
        }
      }).await;
      pipes.push(tx);
    }

    for i in 0 .. limit {
      for pipe in &pipes {
        match pipe.put(i).await {
          Ok(_) => (),
          Err(err) => println!("Oops! {:?}", err),
        };
      }
    }

    for pipe in pipes {
      pipe.drop().await;
    }

  }).unwrap();
}


