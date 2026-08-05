module Verified_ledger_helpers
(* Models for u64::checked_add / checked_sub, missing from proof-libs'
   Core_models.Num at hax rev 54c34967 (Num cannot depend on Option there
   without a dependency cycle). The generated Verified_ledger.fst is
   redirected here by verify.sh. Semantics mirror Rust exactly. *)
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Rust_primitives

let checked_add_u64 (x y: u64) : Core_models.Option.t_Option u64 =
  if x <=. (Core_models.Num.impl_u64__MAX -! y <: u64)
  then Core_models.Option.Option_Some (x +! y) <: Core_models.Option.t_Option u64
  else Core_models.Option.Option_None <: Core_models.Option.t_Option u64

let checked_sub_u64 (x y: u64) : Core_models.Option.t_Option u64 =
  if y <=. x
  then Core_models.Option.Option_Some (x -! y) <: Core_models.Option.t_Option u64
  else Core_models.Option.Option_None <: Core_models.Option.t_Option u64
