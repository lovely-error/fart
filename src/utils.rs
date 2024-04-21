use core::{arch, ptr::null};
use std::{iter::zip, mem::{align_of, size_of, MaybeUninit, transmute, ManuallyDrop, size_of_val, align_of_val}, ptr::{drop_in_place, copy_nonoverlapping, addr_of, null_mut, Alignment}, cell::UnsafeCell, str::FromStr, time::{SystemTime, Duration}, alloc::{alloc, Layout}, sync::Arc, any::Any};

use crate::root_alloc::Block4KPtr;


macro_rules! static_assert {
    ($cond:expr) => {
      const _ : () = if !$cond { std::panic!("Comptime assert failed!") } ;
    };
    ($cond:expr, $msg:expr) => {
      const _ : () = if !$cond { panic!($msg) } ;
    };
}

pub struct RestoreGuard<T>(UnsafeCell<(*mut T, bool)>);
impl <T> RestoreGuard<T> {
  pub fn consume(&self) -> T { unsafe {
    let this = &mut *self.0.get();
    assert!(!this.1);
    let value = this.0.read() ;
    this.1 = true;
    return value;
  } }
  pub fn recover_with(&self, new_value: T) { unsafe {
    let this = &mut *self.0.get();
    if !this.1 { drop_in_place(this.0) }
    this.0.write(new_value);
    this.1 = false;
  } }
}
pub fn with_scoped_consume<T, K>(
  source: &mut T, action: impl FnOnce(&RestoreGuard<T>) -> K
) -> K {
  let guard = RestoreGuard(UnsafeCell::new((source, false)));
  let result = action(&guard);
  let this = unsafe { &*guard.0.get() };
  assert!(!this.1, "Consumed value was not restored");
  return result;
}

struct Box<T>(T);
#[test]
fn quick_sanity_check(){
  let str = "Hello, ya loving rust too??";
  let mut val = Box(String::from_str(str).unwrap());
  with_scoped_consume(&mut val.0, |val|{
    let v = val.consume();
    assert!(v == String::from_str(str).unwrap());
    val.recover_with(String::from_str("yeah..").unwrap());
  });
  assert!(val.0 == String::from_str("yeah..").unwrap())
}


pub trait FailablePageSource {
  fn try_drain_page(&self) -> Option<Block4KPtr>;
}

#[repr(C)]
union Bitcaster<I, O> {
  in_: ManuallyDrop<I>,
  out_: ManuallyDrop<O>
}

pub fn bitcast<T, R>(val: T) -> R {
  let in_ = Bitcaster {in_:ManuallyDrop::new(val)};
  let out = unsafe { ManuallyDrop::into_inner(in_.out_) };
  return out
}

#[test]
fn bitcasting() {
  let val = [0u8; 4];
  let casted = bitcast::<_, [u8;3]>(val);
  assert!(casted == [0u8;3]);
}
#[repr(align(4096))]
pub(crate) struct MemBlock4Kb(pub(crate)*mut MemBlock4Kb, pub(crate)[u8;4088]);


#[inline(always)]
pub(crate)
fn publish_changes_on_memory(
  start_address: *const (),
  bytes: usize
) {
  let span = bytes.next_multiple_of(64) >> 6;
  let mut addr = start_address as usize;
  for _ in 0 .. span {
    unsafe {
      core::arch::x86_64::_mm_clflush(addr as _);
      addr += 64;
    }
  }
}
#[inline(always)]
pub(crate)
fn publish_changes_on_object<T>(
  address: *const T,
) {
  publish_changes_on_memory(address.cast(), size_of::<T>())
}