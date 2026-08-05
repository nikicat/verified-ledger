module Repro_decreases
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let rec count_up (n i: usize)
    : Prims.Tot usize (decreases (if i <=. n <: bool then n -! i <: usize else mk_usize 0)) =
  if i >=. n then mk_usize 0 else mk_usize 1 +! (count_up n (i +! mk_usize 1 <: usize) <: usize)
