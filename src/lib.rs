#![feature(pointer_is_aligned)]
#![feature(strict_provenance)]
#![feature(inline_const)]
#![feature(const_for)]
#![feature(const_trait_impl)]
#![feature(const_mut_refs)]
#![feature(ptr_alignment_type)]
#![feature(portable_simd)]

pub mod driver;
mod root_alloc;
mod utils;
mod loopbuffer;
mod array;
