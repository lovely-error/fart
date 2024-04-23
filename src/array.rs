

use std::{marker::PhantomData, ptr::{null_mut, copy_nonoverlapping}, mem::{size_of, MaybeUninit, forget}, cell::UnsafeCell};
use crate::{root_alloc::Block4KPtr, utils::PageSource};


// this datatype is monomorphisation-aware.
// instead of letting rustc copy-paste identical code around,
// the major functionalities of interface methods are factored out
// into a standalone implementations that never get inlined.
//
// this may sacrifise some speed but the advantage is that i-caches
// are operating without being polluted by dull duplicates.
// I deem this chose as acceptable for a currency type.

// Lyfecycle protocol:
// this badly needs a propper destructor

// Interface: todo
pub struct Array<T>(
  UnsafeCell<ArrayInternals>,
  PhantomData<T>);

#[allow(unused)]
impl <T> Array<T> {
  pub fn new() -> Self {
    Self(UnsafeCell::new(ArrayInternals::new()), PhantomData)
  }
  pub fn ref_item_at_index(&self, index: usize) -> Option<*mut T> {
    let this = self.project_internals();
    if index >= this.item_count || this.item_count == 0 { return None; };
    let ptr = Array_ref_item_at_index_impl(this, size_of::<T>(), index);
    return Some(ptr.cast::<T>())
  }
  #[must_use]
  pub fn push(&self, new_item: T, page_source: &mut dyn PageSource) -> bool {
    let this = self.project_internals();
    let ok = Array_push_impl(this, core::ptr::addr_of!(new_item).cast(), size_of::<T>(), page_source);
    if !ok { return false }
    forget(new_item);
    return true;
  }
  pub fn pop(&/*mut*/ self) -> Option<T> {
    let this = self.project_internals();
    if this.item_count == 0 { return None };
    let mut val = MaybeUninit::<T>::uninit();
    let item_size = size_of::<T>();
    let mtd_slot_count = this.slots_occupied_by_mtd(item_size) as u64;
    Array_pop_impl(
      this,
      item_size,
      val.as_mut_ptr().cast(),
      mtd_slot_count);
    return Some(unsafe { val.assume_init() })
  }
  pub fn item_count(&self) -> usize {
    let this = self.project_internals();
    return this.item_count
  }
  pub fn reset(&self) {
    let this = self.project_internals();
    this.access_head = this.head_page;
    this.put_access_head_to_first_element(size_of::<T>());
    this.item_count = 0;
  }
}

struct ArrayInternals {
  head_page: *mut u8,
  tail_page: *mut u8,
  access_head: *mut u8,
  item_count: usize,
}
impl ArrayInternals {
  #[allow(unused)]
  fn new() -> Self {
    Self { head_page: null_mut(),
           tail_page: null_mut(),
           access_head: null_mut(),
           item_count: 0,}
  }
  fn put_access_head_to_first_element(&mut self, item_size: usize) { unsafe {
    let off = self.slots_occupied_by_mtd(item_size);
    self.access_head = self.access_head.byte_add(off * item_size) ;
  } }
  fn do_late_init(&mut self, item_size: usize, page_source: &mut dyn PageSource) -> bool { unsafe {
    assert!(self.head_page == null_mut());
    let page = match page_source.try_get_page() {
      Some(page) => page,
      None => {
        return false;
      },
    };
    let ptr = page.get_ptr();
    self.head_page = ptr;
    self.tail_page = ptr;
    let mtd = &mut *ptr.cast::<PageMetadata>();
    *mtd = PageMetadata {next_page:null_mut(), previous_page:null_mut()};
    self.access_head = ptr;
    self.put_access_head_to_first_element(item_size);
    return true;
  } }
  fn expand_storage(&mut self, item_size: usize, page_source: &mut dyn PageSource) -> bool { unsafe {
    let page = match page_source.try_get_page() {
      Some(page) => page,
      None => return false,
    };
    let ptr = page.get_ptr();
    let mtd = &mut *ptr.cast::<PageMetadata>();
    *mtd = PageMetadata {next_page:null_mut(), previous_page:self.tail_page};
    (&mut *self.tail_page.cast::<PageMetadata>()).next_page = ptr;
    self.tail_page = ptr;
    self.access_head = ptr;
    self.put_access_head_to_first_element(item_size);
    return true;
  } }
  fn slots_occupied_by_mtd(&self, item_size: usize) -> usize {
    let mut off = size_of::<PageMetadata>() / item_size;
    if off * item_size < size_of::<PageMetadata>() { off += 1 };
    return off
  }
}

struct PageMetadata {
  next_page: *mut u8,
  previous_page: *mut u8
}

trait ProjectableInternals<'i> {
  fn project_internals(&'i self) -> &'i mut ArrayInternals;
}
impl <'k,T> ProjectableInternals<'k> for Array<T>  {
  fn project_internals(&'k self) -> &'k mut ArrayInternals {
    unsafe { &mut *self.0.get() }
  }
}

#[inline(never)]
#[allow(non_snake_case, unused)]
fn Array_ref_item_at_index_impl(
  object: &mut ArrayInternals,
  item_size: usize,
  index: usize,
) -> *mut u8 { unsafe {
  assert!(index < object.item_count && object.item_count != 0);
  let slots_for_mtd = object.slots_occupied_by_mtd(item_size);
  let slot_count = (4096 / item_size) - slots_for_mtd;
  let chase_count = index / slot_count;
  let mut containing_page = object.head_page;
  let mut chase_count_m = chase_count;
  loop {
    if chase_count_m == 0 { break; }
    containing_page = (*containing_page.cast::<PageMetadata>()).next_page;
    chase_count_m -= 1;
  };
  let real_index = index - (slot_count * chase_count);
  let offset = (slots_for_mtd * item_size) + (real_index * item_size);
  let ptr = containing_page.byte_add(offset);
  return ptr;
}; }
#[inline(never)]
#[allow(non_snake_case)]
fn Array_push_impl(
  object: &mut ArrayInternals,
  new_item_source_loc: *const u8,
  item_size: usize,
  page_source: &mut dyn PageSource,
) -> bool { unsafe {
  if object.head_page == null_mut() {
    let ok = object.do_late_init(item_size, page_source);
    if !ok {
      return false;
    }
  }
  copy_nonoverlapping(new_item_source_loc, object.access_head.cast::<u8>(), item_size);
  object.access_head = object.access_head.byte_add(item_size);
  let at_the_edge =
    (object.access_head as u64 & !((1 << 12) - 1)) == object.access_head as u64;
  if at_the_edge {
    let head = object.access_head.byte_sub(4096);
    let mtd = &*head.cast::<PageMetadata>();
    let next_page = mtd.next_page;
    let has_next = next_page != null_mut();
    if has_next {
      object.access_head = next_page;
      object.put_access_head_to_first_element(item_size);
    } else {
      let ok = object.expand_storage(item_size, page_source);
      if !ok {
        return false;
      }
    }
  }
  object.item_count += 1;
  return true;
} }

#[inline(never)]
#[allow(non_snake_case)]
fn Array_pop_impl(
  object: &mut ArrayInternals,
  item_size: usize,
  result_write_back_loc: *mut u8,
  mtd_slot_count: u64,
) { unsafe {
  assert!(object.item_count != 0);
  let adjusted_mtd_offset = item_size as u64 * mtd_slot_count;
  let offset_head = object.access_head as u64 - adjusted_mtd_offset;
  let at_the_edge = (offset_head & !((1 << 12) - 1)) == offset_head;
  if at_the_edge {
    let mtd = &*(offset_head as *mut PageMetadata);
    let pp = mtd.previous_page;
    if pp != null_mut() {
      let mut ptr = pp.byte_add(adjusted_mtd_offset as usize);
      let item_count_per_page = 4096 / item_size;
      let item_count_adjusted_for_metadata =
        item_count_per_page - mtd_slot_count as usize;
      let byte_offset_to_one_past_last_item =
        item_count_adjusted_for_metadata * item_size;
      ptr = ptr.byte_add(byte_offset_to_one_past_last_item);
      object.access_head = ptr;
    }
  }
  let item_ptr = object.access_head.byte_sub(item_size);
  copy_nonoverlapping(item_ptr.cast::<u8>(), result_write_back_loc.cast(), item_size);
  object.access_head = item_ptr;
  object.item_count -= 1;
} }



#[test]
fn pushespops_repsect_boundries() {
  let mut ralloc = crate::root_alloc::RootAllocator::new();
  type Item = u32;
  let arr = Array::<Item>::new();
  let limit = 4096 / size_of::<Item>();
  let mut mtd_adj = size_of::<PageMetadata>() / size_of::<Item>();
  if mtd_adj * size_of::<Item>() < size_of::<PageMetadata>() {mtd_adj += 1}
  for i in 0 .. limit - mtd_adj  {
    let _ = arr.push(i as Item, &mut ralloc);
  }
  let mut vec = Vec::new();
  for _ in 0 .. limit - mtd_adj  {
    if let Some(v) = arr.pop() {
      vec.push(v);
    } else { panic!() }
  }
  vec.reverse();
  for i in 0 .. limit - mtd_adj {
    let item = *vec.get(i).unwrap();
    assert!(item == i as u32);
  }
}

#[test]
fn weirdly_sized_pushespops_repsect_boundries() {
  use core::ptr::addr_of;
  let mut ralloc = crate::root_alloc::RootAllocator::new();
  type Item = [u8;3];
  let arr = Array::<Item>::new();
  let page_capacity = 4096 / size_of::<Item>();
  let mut mtd_adj = size_of::<PageMetadata>() / size_of::<Item>();
  if mtd_adj * size_of::<Item>() < size_of::<PageMetadata>() {mtd_adj += 1}
  let limit = (page_capacity - mtd_adj + 1) * 2;
  for i in 0 .. limit {
    let mut v = [0u8;3];
    unsafe {
      copy_nonoverlapping(addr_of!(i).cast::<u8>(), core::ptr::addr_of_mut!(v).cast::<u8>(), 3)
    };
    let _ = arr.push(v, &mut ralloc);
  }
  let mut vec = Vec::new();
  for _ in 0 .. limit  {
    if let Some(v) = arr.pop() {
      vec.push(v);
    } else { panic!() }
  }
  vec.reverse();
  for i in 0 .. limit {
    let item = *vec.get(i).unwrap();
    let mut m = 0u32;
    unsafe {
      copy_nonoverlapping(addr_of!(item).cast::<u8>(), core::ptr::addr_of_mut!(m).cast::<u8>(), 3)
    }
    assert!(m == i as u32);
  }
}

#[test]
fn indexing_works() {
  let mut ralloc = crate::root_alloc::RootAllocator::new();
  let arr = Array::<u32>::new();
  for i in 0 .. 4096 {
    let _ = arr.push(i, &mut ralloc);
  }
  for i in 0 ..4096 {
    let k = arr.ref_item_at_index(i);
    if let Some(n) = k {
      assert!(unsafe{*n} == i as u32);
    } else { panic!() };
  }
}

impl <T> PageSource for Array<T> {
  fn try_get_page(&self) -> Option<Block4KPtr> { unsafe {
    let ArrayInternals { access_head, tail_page, .. } = &mut *self.0.get();
    let page_start_addr = (*access_head as usize) & !((1 << 12) - 1);
    let head_on_last_page = page_start_addr == *tail_page as _;
    if head_on_last_page { return None } // nothing to give away

    let last_page = *tail_page;
    let last_mtd = &*last_page.cast::<PageMetadata>();
    let page_before_last = last_mtd.previous_page;
    let only_one_page = page_before_last == null_mut();
    if only_one_page { return None } // dont rob the thing of last possesions

    let pre_last_mtd = &mut*page_before_last.cast::<PageMetadata>();
    pre_last_mtd.next_page = null_mut();
    *tail_page = page_before_last;

    return Some(Block4KPtr::new(last_page.cast()))
  }; }
}

#[test]
fn draining_works() { unsafe {
  let mut ralloc = crate::root_alloc::RootAllocator::new();
  let arr = Array::<u64>::new();
  for i in 0 .. 512 {
    let _ = arr.push(i, &mut ralloc);
  }
  for _ in 0 .. 512 {
    let _ = arr.pop();
  }
  let ptr = arr.try_get_page().unwrap().get_ptr().cast::<u8>();
  ptr.write_bytes(u8::MAX, 4096);
  for i in 0 .. 512 {
    let _ = arr.push(i, &mut ralloc);
  }
  for i in 0 .. 512 {
    let item = arr.pop().unwrap();
    assert!(511 - i == item)
  }
  for i in 0 .. 4096 {
    assert!(*ptr.byte_add(i).cast::<u8>() == u8::MAX)
  }
} }

#[test]
fn draining_on_empty() {
  let mut ralloc = crate::root_alloc::RootAllocator::new();
  let arr = Array::<u64>::new();

  let smth = arr.try_get_page();
  if let Some(_) = smth { panic!() }

  let _ = arr.push(1, &mut ralloc);
  if let Some(_) = arr.try_get_page(){ panic!()};
}

#[test]
fn inout_lots() {
  let mut ralloc = crate::root_alloc::RootAllocator::new();
  let arr = Array::new();
  const LIMIT : usize = 1_000_000;
  for i in 0 .. LIMIT {
    let _ = arr.push(i, &mut ralloc);
  }
  let mut res = Vec::new();
  for _ in 0 .. LIMIT {
    res.push(arr.pop().unwrap());
  }
  res.sort();
  for i in 0 .. LIMIT {
    assert!(i == res[i])
  }
}