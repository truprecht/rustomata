#![feature(result_map_or_else)]
extern crate integeriser;
extern crate log_domain;
#[macro_use]
extern crate nom;
extern crate num_traits;
extern crate rand;
extern crate serde;
extern crate time;
#[macro_use]
extern crate serde_derive;
extern crate fnv;
extern crate search;
extern crate unique_heap;
extern crate vecmultimap;
extern crate rustomata_util;

pub mod cfg;
pub mod mcfg;
pub mod pmcfg;
pub mod lcfrs;
pub mod dyck;
pub mod factorizable;
mod util;