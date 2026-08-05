module Repro_checked_models
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let saturating_ish_add (x y: u64) : u64 =
  Core_models.Option.impl__unwrap_or #u64
    (Core_models.Num.impl_u64__checked_add x y <: Core_models.Option.t_Option u64)
    Core_models.Num.impl_u64__MAX
