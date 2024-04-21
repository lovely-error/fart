#![feature(strict_provenance)]
#![feature(ptr_alignment_type)]
#![feature(generic_arg_infer)]
#![feature(let_chains)]
#![feature(thread_spawn_unchecked)]
#![feature(pointer_is_aligned_to)]
#![feature(portable_simd)]
#![feature(negative_impls)]
#![feature(inline_const)]

#[cfg(not(target_os = "linux"))]
  compile_error!(
    "It only works on linux"
  );
#[cfg(not(target_endian = "little"))]
  compile_error!(
    "It only works on little endian"
  );
#[cfg(not(target_has_atomic = "64"))]
  compile_error!(
    "This software needs atomics"
  );
#[cfg(not(target_pointer_width = "64"))]
  compile_error!(
    "Only 64 bit arches are supported"
  );
#[cfg(not(target_arch= "x86_64"))]
  compile_error!(
    "Only x86_64 is supported at this point, sorry"
  );



mod root_alloc;
#[allow(unused)]
mod utils;
mod loopbuffer;
mod array;
#[allow(dead_code)]
mod futex;

mod driver_async;

pub use driver_async::{
  launch_detached,
  run_isolated,
  wait_on_fd,
  yield_now,
  FaRT,
  RtRef,
};

mod pipe;
mod block_allocator;

// #[allow(unused_imports)]
mod fd_table;

mod cl_lock;