use std::{mem::{MaybeUninit, size_of, forget}, cell::UnsafeCell, ptr::{addr_of_mut, copy_nonoverlapping, addr_of}};



// non-thread safe, bounded queue.
// pushes and pops do not invalidate refs to this object.
pub struct InlineLoopBuffer<const Capacity:usize, T>(
  UnsafeCell<InlineLoopBufferData<Capacity, T>>);
struct InlineLoopBufferData<const Capacity:usize, T> {
  items: [MaybeUninit<T>; Capacity],
  write_index: usize,
  read_index: usize,
  item_count: usize,
}
trait InlineLoopBufferDataAccessorImpl {
  fn get_internals(&mut self)
    -> (*mut u8, &mut usize, &mut usize, &mut usize);
}

impl <const Capacity:usize, T>
  InlineLoopBufferDataAccessorImpl
  for InlineLoopBufferData<Capacity, T> {

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

impl <const Capacity:usize, T> InlineLoopBuffer<Capacity, T> {
  pub fn new() -> Self { unsafe {
    Self(UnsafeCell::new(
      InlineLoopBufferData {
        items: MaybeUninit::uninit().assume_init(),
        write_index: 0,
        read_index: 0,
        item_count: 0 }))
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
    let mut result = MaybeUninit::<(T, bool)>::uninit();
    let result_mref = &mut *result.as_mut_ptr();
    let result_addr = addr_of_mut!(result_mref.0);
    InlineLoopBuffer_pop_from_head_impl(
      this, size_of::<T>(), Capacity, (result_addr.cast(), &mut result_mref.1));
    let (value, did_write) = result.assume_init();
    if did_write { return Some(value) }
    return None
  }; }
  pub fn pop_from_tail(&self) -> Option<T> { unsafe {
    let this = &mut *self.0.get();
    let mut result = MaybeUninit::<T>::uninit();
    let mut ok = false;
    InlineLoopBuffer_pop_from_tail_impl(
      this, size_of::<T>(), Capacity,
      (result.as_mut_ptr().cast(), &mut ok));
    if ok { return Some(result.assume_init()) }
    return None
  } }
  pub fn item_count(&self) -> usize {
    unsafe { (&*self.0.get()).item_count }
  }
  pub fn mref_item_at_index(&self, index: usize) -> Option<&mut T> { unsafe {
    let this = &mut*self.0.get();
    if index >= this.item_count { return None }
    let mut index_ = this.read_index + index;
    if index_ >= Capacity {
      index_ = index - (Capacity - this.read_index) }
    let item_ref = (&mut*this.items.as_mut_ptr().add(index_)).assume_init_mut();
    return Some(item_ref)
  }; }
}

#[inline(never)]
fn InlineLoopBuffer_push_impl(
  object: &mut dyn InlineLoopBufferDataAccessorImpl,
  new_item_addr: *const u8,
  item_byte_size: usize,
  max_capacity: usize,
) -> bool { unsafe {
  let (storage_ptr, write_index, _, item_count) = object.get_internals();
  if *item_count == max_capacity { return false };
  let slot_ptr = storage_ptr.add(*write_index * item_byte_size);
  copy_nonoverlapping(new_item_addr, slot_ptr, item_byte_size);
  let mut new_index = *write_index + 1;
  if new_index == max_capacity { new_index = 0 }
  *write_index = new_index;
  *item_count += 1;
  return true
}; }

#[inline(never)]
fn InlineLoopBuffer_pop_from_head_impl(
  object: &mut dyn InlineLoopBufferDataAccessorImpl,
  item_byte_size: usize,
  max_capacity: usize,
  result_loc: (*mut u8, &mut bool)
) { unsafe {
  let (storage_ptr, _, read_index, item_count) = object.get_internals();
  if *item_count == 0 { *result_loc.1 = false; return }
  let slot_ptr = storage_ptr.add(*read_index * item_byte_size);
  copy_nonoverlapping(slot_ptr, result_loc.0, item_byte_size);
  let mut new_read_index = *read_index + 1;
  if new_read_index == max_capacity { new_read_index = 0 };
  *read_index = new_read_index;
  *item_count -= 1;
  *result_loc.1 = true;
} }

#[inline(never)]
fn InlineLoopBuffer_pop_from_tail_impl(
  object: &mut dyn InlineLoopBufferDataAccessorImpl,
  item_byte_size: usize,
  max_capacity: usize,
  result_loc: (*mut u8, &mut bool)
) { unsafe {
  let (storage_ptr, write_index, _, item_count) = object.get_internals();
  if *item_count == 0 { *result_loc.1 = false; return }
  let index = if *write_index == 0 { max_capacity } else {*write_index} - 1;
  let slot_ptr = storage_ptr.add(index * item_byte_size);
  copy_nonoverlapping(slot_ptr, result_loc.0, item_byte_size);
  *write_index = index;
  *item_count -= 1;
  *result_loc.1 = true;
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

pub struct LoopBufferTraverser<'i, T> {
  source: &'i dyn SomeInlineLoopBuffer<Item = T>,
  current_index: usize
}
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