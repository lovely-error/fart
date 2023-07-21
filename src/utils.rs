use std::{iter::zip, mem::{align_of, size_of, MaybeUninit, transmute, ManuallyDrop, size_of_val, align_of_val}, ptr::{drop_in_place, copy_nonoverlapping, addr_of, null_mut}, cell::UnsafeCell, str::FromStr, time::{SystemTime, Duration}, alloc::{alloc, Layout}, sync::Arc, any::Any};

use crate::root_alloc::Block4KPtr;


#[macro_export]
macro_rules! cast {
    ($Val:expr, $Ty:ty) => {
      {
        use core::mem::transmute;
        unsafe { transmute::<_, $Ty>($Val) }
      }
    };
}

pub fn high_order_pow2(number: u64) -> u64 {
  if number == 0 { return 0 }
  if number == 1 { return 1 }
  64u64 - (number - 1).leading_zeros() as u64
}
#[test]
fn valid_order_count() {
  let nums = [
    0, 1, 3, 5, 7, 11, 13, 17, 23];
  let orders = [
    0, 1, 2, 3, 3, 4, 4, 5, 5];
  for (n, o) in zip(nums, orders) {
    assert!(high_order_pow2(n) == o);
  }
}

#[test]
fn ex () {
  println!("{}", high_order_pow2(0))
}

pub fn ptr_align_dist<T>(ptr: *const T, align: usize) -> u64 {
  let ptrint = ptr as u64;
  let order = high_order_pow2(align as u64);
  let mul = ptrint >> order;
  let mut result = mul << order;
  if (result as u64) < ptrint { result += align as u64 };
  return result - ptrint;
}

pub fn offset_to_higher_multiple(addr: u64, align: usize) -> u64 {
  assert!(align.is_power_of_two());
  let order = high_order_pow2(align as u64);
  let mul = addr >> order;
  let mut result = mul << order;
  if (result as u64) < addr { result += align as u64 };
  return result - addr;
}

#[test]
fn offseter_check() {
  let i = [
    3, 5, 6, 7, 8, 11, 12, 13, 16
  ];
  let m = [
    2, 4, 4, 4, 4, 4,  4,  2,  32
  ];
  let o = [
    1, 3, 2, 1, 0, 1,  0,  1,  16
  ];
  assert!(i.len() == m.len() && o.len() == i.len());
  for n in 0 .. i.len() {
    let i = i[n];
    let m = m[n];
    let k = offset_to_higher_multiple(i, m);
    assert!(k == o[n])
    // println!("{} {} {}", i, m ,k)
  }
}

#[test]
fn bool_to_int() {
  assert!(1u8 == unsafe { transmute(true) });
  assert!(0u8 == unsafe { transmute(false) })
}

#[test]
fn test_align_works() {
  let ptr = (8 * 7) as *mut u8;
  let m = ptr.align_offset(32);
  let k = ptr_align_dist(ptr, 32);
  println!("{} {}",m, k);
}

pub fn measure_exec_time(action: impl FnOnce()) -> Duration {
  let begin = SystemTime::now();
  action();
  let diff = begin.elapsed().unwrap();
  return diff
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
#[test]
fn no_double_free () {}

#[test]
fn guard_guards() {}

#[macro_export]
macro_rules! garbage {
    () => {
      {unsafe { MaybeUninit::uninit().assume_init() }}
    };
    ($ty:ty) => {
      {
        use std::mem::MaybeUninit;
        unsafe { MaybeUninit::<$ty>::uninit().assume_init() }
      }
    }
}


pub unsafe fn bitcopy<T>(val: &T) -> T {
  transmute::<_, *const T>(val).read()
}


// #[macro_export]
// macro_rules! unborrowcheck {
//   ($expr:expr, $Ty:ty) => {
//     {
//       use std::mem::transmute;
//       let copied_mref = transmute::<_, u64>($expr);
//       move || { &mut *transmute::<_, *mut $Ty>(copied_mref) }
//     }
//   };
// }


pub trait PageSource {
  fn try_drain_page(&mut self) -> Option<Block4KPtr>;
}

#[test]
fn fat_ptr_to_object() {
  let size = size_of::<*mut dyn PageSource>();
  assert!(size == 16)
  // println!("{}", size)
}


#[test]
fn speed() {
  for _ in 0 .. 30 {
    let mut v = garbage!() ;
    let time = measure_exec_time(|| {
      v = offset_to_higher_multiple(8 * 23, 32)
    });
    println!("{v} {}", time.as_nanos());
    let mut v = garbage!() ;
    let time = measure_exec_time(|| {
      v = ((8 * 3) as *mut u8).align_offset(32);
    });
    println!("{v} {}\n", time.as_nanos())
  }
}

#[test]
fn no_aslr() {
  let alloc = unsafe { alloc(Layout::from_size_align_unchecked(1 << 21, 4096)) };
  println!("{} {}", alloc as u64, (alloc as u64 >> 12) > u32::MAX as u64)
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

#[test]
fn size_of_counter() {
  println!("{}", size_of::<Arc<String>>())
}

pub fn aligned_for<T>(ptr: *const u8) -> bool {
  let align = align_of::<T>();
  assert!(align.is_power_of_two());
  let ptr = ptr as u64;
  let tr = ptr.trailing_zeros();
  let align_order = align.trailing_zeros();
  let ok = tr >= align_order;
  return ok
}

pub fn stride_of<T>() -> usize {
  let mut stride = size_of::<T>();
  stride += offset_to_higher_multiple(
    stride as u64, align_of::<T>()) as usize;
  return stride
}

#[test] #[ignore]
fn striding () {
  struct Eww(u64, u64, u64, u32, u32, u32, u16);
  println!("{} {}", size_of::<Eww>(), stride_of::<Eww>());
}


trait ExposesTraversableContiguosMemory {
  type Item;
  fn next_contiguos_block(&mut self) -> Option<&mut [Self::Item]>;
}

pub trait SomeDebug: Any + std::fmt::Debug + Clone {}
type __ = Box<dyn SomeDebug>;

#[test] #[ignore]
fn what_the () {
  async fn async_ () {
    let str = async_2().await;
    let id = what().await.type_id();
    println!("{} {:?}", str, id)
  }
  async fn async_2 () -> String {
    return String::from_str("???").unwrap()
  }
  async fn what() -> impl Any {
    return 0u64
  }
  let thing = async_();
  println!("{}", size_of_val(&thing));
}
