use std::{marker::PhantomData, ptr::{null_mut, copy_nonoverlapping, addr_of, addr_of_mut}, mem::{size_of, MaybeUninit, forget}, cell::UnsafeCell};

use crate::{root_alloc::{RootAllocator, Block4KPtr}, cast, utils::PageSource};


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

impl <T> Array<T> {
  pub fn new(ralloc: *mut dyn PageSource) -> Self {
    Self(UnsafeCell::new(ArrayInternals::new(ralloc)), PhantomData)
  }
  pub fn ref_item_at_index(&self, index: usize) -> Option<&mut T> {
    let this = self.project_internals();
    if index >= this.item_count || this.item_count == 0 { return None; };
    let mut result = null_mut();
    Array_ref_item_at_index_impl(this, size_of::<T>(), index, &mut result);
    return Some(cast!(result, &mut T))
  }
  pub fn push(&self, new_item: T) {
    let this = self.project_internals();
    Array_push_impl(this, addr_of!(new_item).cast(), size_of::<T>());
    forget(new_item);
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
      val.as_mut_ptr().cast::<u8>(),
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
  mem_block_provider: *mut dyn PageSource,
  head_page: *mut u8,
  tail_page: *mut u8,
  access_head: *mut u8,
  item_count: usize,
}
impl ArrayInternals {
  fn new(page_provider: *mut dyn PageSource) -> Self {
    Self { mem_block_provider: page_provider,
           head_page: null_mut(),
           tail_page: null_mut(),
           access_head: null_mut(),
           item_count: 0,}
  }
  fn put_access_head_to_first_element(&mut self, item_size: usize) { unsafe {
    let off = self.slots_occupied_by_mtd(item_size);
    self.access_head = self.access_head.add(off * item_size) ;
  } }
  fn do_late_init(&mut self, item_size: usize) { unsafe {
    assert!(self.head_page == null_mut());
    let page;
    loop {
      if let Some(v) = (*self.mem_block_provider).try_drain_page() {
        page = v; break
      };
    }
    let Block4KPtr(ptr) = page;
    self.head_page = ptr;
    self.tail_page = ptr;
    let mtd = &mut *ptr.cast::<PageMetadata>();
    *mtd = PageMetadata {next_page:null_mut(), previous_page:null_mut()};
    self.access_head = ptr;
    self.put_access_head_to_first_element(item_size);
  } }
  fn expand_storage(&mut self, item_size: usize) { unsafe {
    let page;
    loop {
      if let Some(v) = (*self.mem_block_provider).try_drain_page() {
        page = v; break
      };
    }
    let Block4KPtr(ptr) = page;
    let mtd = &mut *ptr.cast::<PageMetadata>();
    *mtd = PageMetadata {next_page:null_mut(), previous_page:self.tail_page};
    (&mut *self.tail_page.cast::<PageMetadata>()).next_page = ptr;
    self.tail_page = ptr;
    self.access_head = ptr;
    self.put_access_head_to_first_element(item_size);
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
fn Array_ref_item_at_index_impl(
  object: &mut ArrayInternals,
  item_size: usize,
  index: usize,
  write_back_loc: &mut *mut u8,
) { unsafe {
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
  let ptr = containing_page.add(offset);
  *write_back_loc = ptr;
}; }
#[inline(never)]
fn Array_push_impl(
  object: &mut ArrayInternals,
  new_item_source_loc: *const u8,
  item_size: usize
) { unsafe {
  if object.head_page == null_mut() { object.do_late_init(item_size) }
  copy_nonoverlapping(new_item_source_loc, object.access_head, item_size);
  object.access_head = object.access_head.add(item_size);
  let at_the_edge =
    (object.access_head as u64 & !((1 << 12) - 1)) == object.access_head as u64;
  if at_the_edge {
    let head = object.access_head.sub(4096);
    let mtd = &*head.cast::<PageMetadata>();
    let next_page = mtd.next_page;
    let has_next = next_page != null_mut();
    if has_next {
      object.access_head = next_page;
      object.put_access_head_to_first_element(item_size);
    } else {
      object.expand_storage(item_size)
    }
  }
  object.item_count += 1;
} }

#[inline(never)]
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
    let mtd = &*(offset_head as *mut ()).cast::<PageMetadata>();
    let pp = mtd.previous_page;
    if pp != null_mut() {
      let mut ptr = pp.add(adjusted_mtd_offset as usize);
      let item_count_per_page = 4096 / item_size;
      let item_count_adjusted_for_metadata =
        item_count_per_page - mtd_slot_count as usize;
      let byte_offset_to_one_past_last_item =
        item_count_adjusted_for_metadata * item_size;
      ptr = ptr.add(byte_offset_to_one_past_last_item);
      object.access_head = ptr;
    }
  }
  let item_ptr = object.access_head.sub(item_size);
  copy_nonoverlapping(item_ptr, result_write_back_loc, item_size);
  object.access_head = item_ptr;
  object.item_count -= 1;
} }



#[test]
fn pushespops_repsect_boundries() {
  let mut ralloc = RootAllocator::new();
  type Item = u32;
  let arr = Array::<Item>::new(&mut ralloc);
  let limit = 4096 / size_of::<Item>();
  let mut mtd_adj = size_of::<PageMetadata>() / size_of::<Item>();
  if mtd_adj * size_of::<Item>() < size_of::<PageMetadata>() {mtd_adj += 1}
  for i in 0 .. limit - mtd_adj  {
    arr.push(i as Item);
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
  let mut ralloc = RootAllocator::new();
  type Item = [u8;3];
  let arr = Array::<Item>::new(&mut ralloc);
  let page_capacity = 4096 / size_of::<Item>();
  let mut mtd_adj = size_of::<PageMetadata>() / size_of::<Item>();
  if mtd_adj * size_of::<Item>() < size_of::<PageMetadata>() {mtd_adj += 1}
  let limit = (page_capacity - mtd_adj + 1) * 2;
  for i in 0 .. limit {
    let mut v = [0u8;3];
    unsafe {
      copy_nonoverlapping(cast!(&i, *const u8), cast!(&mut v, *mut u8) , 3)
    };
    arr.push(v);
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
      copy_nonoverlapping(cast!(&item, *const u8), cast!(&mut m, *mut u8), 3)
    }
    assert!(m == i as u32);
  }
}

#[test]
fn indexing_works() {
  let mut ralloc = RootAllocator::new();
  let arr = Array::<u32>::new(&mut ralloc);
  for i in 0 .. 4096 {
    arr.push(i)
  }
  for i in 0 ..4096 {
    let k = arr.ref_item_at_index(i);
    if let Some(n) = k {
      assert!(*n == i as u32);
    } else { panic!() };
  }
}

impl <T> PageSource for Array<T> {
  fn try_drain_page(&mut self) -> Option<Block4KPtr> { unsafe {
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

    return Some(Block4KPtr(last_page))
  }; }
}

#[test]
fn draining_works() { unsafe {
  let mut ralloc = RootAllocator::new();
  let mut arr = Array::<u64>::new(addr_of_mut!(ralloc));
  for i in 0 .. 512 {
    arr.push(i);
  }
  for _ in 0 .. 512 {
    let _ = arr.pop();
  }
  let Block4KPtr(ptr) = arr.try_drain_page().unwrap();
  ptr.write_bytes(u8::MAX, 4096);
  for i in 0 .. 512 {
    arr.push(i)
  }
  for i in 0 .. 512 {
    let item = arr.pop().unwrap();
    assert!(511 - i == item)
  }
  for i in 0 .. 4096 {
    assert!(*ptr.add(i) == u8::MAX)
  }
} }

#[test]
fn draining_on_empty() {
  let mut ralloc = RootAllocator::new();
  let mut arr = Array::<u64>::new(addr_of_mut!(ralloc));

  let smth = arr.try_drain_page();
  if let Some(_) = smth { panic!() }

  arr.push(1);
  if let Some(_) = arr.try_drain_page(){ panic!()};
}