#![feature(pointer_is_aligned)]
#![feature(pointer_byte_offsets)]
#![feature(strict_provenance)]

#![feature(const_maybe_uninit_zeroed)]
#![feature(inline_const)]
#![feature(const_for)]
#![feature(const_trait_impl)]
#![feature(const_mut_refs)]
#![feature(ptr_alignment_type)]

pub mod driver;
mod root_alloc;
mod utils;
mod loopbuffer;
mod array;
