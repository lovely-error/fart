#![feature(pointer_is_aligned)]
#![feature(strict_provenance)]
#![feature(inline_const)]
#![feature(const_for)]
#![feature(const_trait_impl)]
#![feature(const_mut_refs)]
#![feature(ptr_alignment_type)]
#![feature(portable_simd)]
#![feature(offset_of)]
#![feature(generic_arg_infer)]

#[allow(unused_imports)]
pub mod driver;
#[allow(unused_imports)]
mod root_alloc;
#[allow(unused)]
mod utils;
#[allow(unused_imports)]
#[allow(non_upper_case_globals)]
mod loopbuffer;
#[allow(unused_imports)]
mod array;
mod futex;