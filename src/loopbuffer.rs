

use core::mem::align_of;
use std::{
  mem::{MaybeUninit, size_of, forget},
  cell::UnsafeCell, ptr::{addr_of_mut, copy_nonoverlapping, addr_of}, simd::Simd
};

use crate::driver_async::{PackItem, TaskPack};

// non-thread safe, bounded queue.
// pushes and pops do not invalidate refs to this object.
#[repr(C)] #[repr(align(128))] #[allow(non_upper_case_globals)]
struct InlineLoopBufferStorageRepr<const Capacity:usize, T>([MaybeUninit<T>;Capacity]);

#[allow(non_upper_case_globals)]
pub struct InlineLoopBuffer<const Capacity:usize, T>(
  UnsafeCell<InlineLoopBufferInner<Capacity, T>>);
#[repr(C)] #[allow(non_upper_case_globals)]
struct InlineLoopBufferInner<const Capacity:usize, T> {
  items: InlineLoopBufferStorageRepr<Capacity, T>,
  write_index: usize,
  read_index: usize,
  item_count: usize,
}

trait InlineLoopBufferDataAccessorImpl {
  fn get_internals(&mut self)
    -> (*mut u8, &mut usize, &mut usize, &mut usize);
}
#[allow(non_upper_case_globals)]
impl <const Capacity:usize, T>
  InlineLoopBufferDataAccessorImpl
  for InlineLoopBufferInner<Capacity, T> {

  fn get_internals(&mut self)
    -> (*mut u8, &mut usize, &mut usize, &mut usize) {

    (
      addr_of_mut!(self.items).cast(),
      &mut self.write_index,
      &mut self.read_index,
      &mut self.item_count
    )
  }
}
#[allow(non_upper_case_globals)]
impl <const Capacity:usize, T> InlineLoopBuffer<Capacity, T> {
  pub fn new() -> Self { unsafe {
    Self(UnsafeCell::new(
      InlineLoopBufferInner {
        items: MaybeUninit::uninit().assume_init(),
        write_index: 0,
        read_index: 0,
        item_count: 0 }))
  } }
  pub fn insert_pack(&self, pack: TaskPack, len: usize) { unsafe {
    assert!(Capacity * size_of::<PackItem>() >= size_of::<TaskPack>());
    assert!(align_of::<Self>() >= align_of::<TaskPack>());
    assert!(self.item_count() == 0);
    let this = &mut *self.0.get();
    this.read_index = 0;
    this.write_index = if len == 16 { 0 } else { len };
    this.item_count = len ;
    let ptr = this.items.0.as_mut_ptr().cast::<Simd<u64, 16>>();
    ptr.write(pack.simd);
  } }
  // true if pushing was successful
  pub fn push_to_tail(&self, new_item: T) -> bool { unsafe {
    let this = &mut *self.0.get();
    let result = InlineLoopBuffer_push_impl(
      this, addr_of!(new_item).cast(), size_of::<T>(), Capacity);
    forget(new_item);
    return result
  } }
  pub fn pop_from_head(&self) -> Option<T> { unsafe {
    let this = &mut *self.0.get();
    let mut result = MaybeUninit::<T>::uninit();
    let ok = InlineLoopBuffer_pop_from_head_impl(
      this, size_of::<T>(), Capacity, result.as_mut_ptr().cast());
    if ok { return Some(result.assume_init()) }
    return None
  }; }
  pub fn pop_from_tail(&self) -> Option<T> { unsafe {
    let this = &mut *self.0.get();
    let mut result = MaybeUninit::<T>::uninit();
    let ok = InlineLoopBuffer_pop_from_tail_impl(
      this, size_of::<T>(), Capacity, result.as_mut_ptr().cast());
    if ok { return Some(result.assume_init()) }
    return None
  } }
  pub fn item_count(&self) -> usize {
    unsafe { (&*self.0.get()).item_count }
  }
  pub fn remaining_capacity(&self) -> usize {
    Capacity - self.item_count()
  }
  pub fn mref_item_at_index(&self, index: usize) -> Option<&mut T> { unsafe {
    let this = &mut*self.0.get();
    if index >= this.item_count { return None }
    let mut index_ = this.read_index + index;
    if index_ >= Capacity {
      index_ = index_ - Capacity
    }
    let item_ref = this.items.0[index_].assume_init_mut();
    return Some(item_ref)
  }; }
}

#[allow(non_snake_case)]
#[inline(never)]
fn InlineLoopBuffer_push_impl(
  object: &mut dyn InlineLoopBufferDataAccessorImpl,
  new_item_addr: *const u8,
  item_byte_size: usize,
  max_capacity: usize,
) -> bool { unsafe {
  let (storage_ptr, write_index, _, item_count) = object.get_internals();
  if *item_count == max_capacity { return false };
  let slot_ptr = storage_ptr.byte_add(*write_index * item_byte_size);
  copy_nonoverlapping(new_item_addr, slot_ptr, item_byte_size);
  let mut new_index = *write_index + 1;
  if new_index == max_capacity { new_index = 0 }
  *write_index = new_index;
  *item_count += 1;
  return true
}; }

#[allow(non_snake_case)]
#[inline(never)]
fn InlineLoopBuffer_pop_from_head_impl(
  object: &mut dyn InlineLoopBufferDataAccessorImpl,
  item_byte_size: usize,
  max_capacity: usize,
  result_loc: *mut ()
) -> bool { unsafe {
  let (storage_ptr, _, read_index, item_count) = object.get_internals();
  if *item_count == 0 { return false }
  let slot_ptr = storage_ptr.byte_add(*read_index * item_byte_size);
  copy_nonoverlapping(slot_ptr.cast::<u8>(), result_loc.cast::<u8>(), item_byte_size);
  let mut new_read_index = *read_index + 1;
  if new_read_index == max_capacity { new_read_index = 0 };
  *read_index = new_read_index;
  *item_count -= 1;
  return true
} }

#[allow(non_snake_case)]
#[inline(never)]
fn InlineLoopBuffer_pop_from_tail_impl(
  object: &mut dyn InlineLoopBufferDataAccessorImpl,
  item_byte_size: usize,
  max_capacity: usize,
  result_loc: *mut ()
) -> bool { unsafe {
  let (storage_ptr, write_index, _, item_count) = object.get_internals();
  if *item_count == 0 { return false }
  let index = if *write_index == 0 { max_capacity } else {*write_index} - 1;
  let slot_ptr = storage_ptr.byte_add(index * item_byte_size);
  copy_nonoverlapping(slot_ptr.cast::<u8>(), result_loc.cast::<u8>(), item_byte_size);
  *write_index = index;
  *item_count -= 1;
  return true
} }

#[test]
fn idexing_works() {
  let buf = InlineLoopBuffer::<5, u8>::new();
  for i in 0 .. 5 {
    let ok = buf.push_to_tail(i);
    assert!(ok)
  }
  let v = buf.pop_from_head().unwrap();
  assert!(v == 0);
  let v = buf.pop_from_head().unwrap();
  assert!(v == 1);
  let ok = buf.push_to_tail(5);
  assert!(ok);
  let ok = buf.push_to_tail(6);
  assert!(ok);
  assert!(buf.item_count() == 5);
  for i in 0 .. 5 {
    let v = buf.mref_item_at_index(i).unwrap();
    assert!(*v == (i + 2) as u8)
  }
}

#[test]
fn inout_items() {
  const ITEM_COUNT: usize = 255;
  let items = InlineLoopBuffer::<ITEM_COUNT, usize>::new();
  for i in 0 .. ITEM_COUNT {
    let did_push = items.push_to_tail(i);
    assert!(did_push);
  }
  let did_push = items.push_to_tail(usize::MAX);
  assert!(!did_push);
  for i in 0 .. ITEM_COUNT {
    let val = items.pop_from_head();
    if let Some(k) = val {
      assert!(k == i)
    } else { panic!() }
  }
  let pop = items.pop_from_head();
  if let Some(_) = pop { panic!() }
}

#[test]
fn poping_from_tail() {
  let buf = InlineLoopBuffer::<2, u64>::new();
  let ok = buf.push_to_tail(0);
  assert!(ok);
  let ok = buf.push_to_tail(1);
  assert!(ok);
  let ok = buf.push_to_tail(2);
  assert!(!ok);
  let tail_item = buf.pop_from_tail().unwrap();
  assert!(tail_item == 1);
  let ok = buf.push_to_tail(2);
  assert!(ok);
  let zero = buf.pop_from_head().unwrap();
  assert!(zero == 0);
  let two = buf.pop_from_head().unwrap();
  assert!(two == 2)
}

pub trait SomeInlineLoopBuffer {
  type Item ;
  fn push_to_tail(&self, new_item: Self::Item) -> bool;
  fn pop_from_head(&self) -> Option<Self::Item>;
  fn pop_from_tail(&self) -> Option<Self::Item>;
  fn item_count(&self) -> usize;
  fn mref_item_at_index(&self, index: usize) -> Option<&mut Self::Item>;
}
#[allow(non_upper_case_globals)]
impl <const Cap:usize, T>  SomeInlineLoopBuffer for InlineLoopBuffer<Cap, T> {
  type Item = T;
  fn item_count(&self) -> usize { self.item_count()}
  fn mref_item_at_index(&self, index: usize) -> Option<&mut Self::Item> {
      self.mref_item_at_index(index)
  }
  fn pop_from_head(&self) -> Option<Self::Item> {
      self.pop_from_head()
  }
  fn pop_from_tail(&self) -> Option<Self::Item> {
      self.pop_from_tail()
  }
  fn push_to_tail(&self, new_item: Self::Item) -> bool {
      self.push_to_tail(new_item)
  }
}
#[allow(unused)]
pub struct LoopBufferTraverser<'i, T> {
  source: &'i dyn SomeInlineLoopBuffer<Item = T>,
  current_index: usize
}
#[allow(unused)] #[allow(non_upper_case_globals)]
impl <'i, T> LoopBufferTraverser<'i, T> {
  pub fn new<const Cap:usize>(source: &'i InlineLoopBuffer<Cap, T>) -> Self {
    Self {
      source: source as &(dyn SomeInlineLoopBuffer<Item = T>),
      current_index: 0 }
  }
  pub fn next(&mut self) -> Option<&mut T> {
    if self.current_index == self.source.item_count() { return None }
    let item = self.source.mref_item_at_index(self.current_index);
    self.current_index += 1;
    return item
  }
}

#[test]
fn empty() {
  let buf = InlineLoopBuffer::<10, u8>::new();
  let mut iter = LoopBufferTraverser::new(&buf);
  if let Some(_) = iter.next() { panic!() };
}

#[test]
fn iter_over_loop() {
  let buf = InlineLoopBuffer::<10, u8>::new();
  for i in 0 .. 10 {
    let ok = buf.push_to_tail(i);
    assert!(ok);
  }
  let mut iter = LoopBufferTraverser::new(&buf);
  for _ in 0 .. 10 {
    *iter.next().unwrap() = u8::MAX;
  }
  let mut iter = LoopBufferTraverser::new(&buf);
  for _ in 0 .. 10 {
    let val = *iter.next().unwrap();
    assert!(val == u8::MAX)
  }
}

#[test]
fn iter_over_loop2() {

  const LIMIT : usize = 1000;
  let buf = InlineLoopBuffer::<LIMIT, usize>::new();

  for i in 0 .. LIMIT {
    let ok = buf.push_to_tail(i);
    assert!(ok);
  }
  for i in 0 .. LIMIT {
    let v = buf.pop_from_head();
    if v.is_none() { panic!() }
    assert!(v.unwrap() == i)
  }
}

#[test]
fn indexiing_trivial() {
  const LIMIT : usize = 1000;
  let buf = InlineLoopBuffer::<LIMIT, usize>::new();

  for i in 0 .. LIMIT {
    buf.push_to_tail(i);
  }
  for i in 0 .. LIMIT {
    let item = buf.mref_item_at_index(i).unwrap();
    assert!(*item == i);
  }
}