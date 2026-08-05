module Verified_ledger
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Ledger = {
  f_balances:Alloc.Vec.t_Vec u64 Alloc.Alloc.t_Global;
  f_total:u128
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core_models.Fmt.t_Debug t_Ledger

unfold
let impl = impl'

let impl_1: Core_models.Clone.t_Clone t_Ledger =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core_models.Marker.t_StructuralPartialEq t_Ledger

unfold
let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core_models.Cmp.t_PartialEq t_Ledger t_Ledger

unfold
let impl_3 = impl_3'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Core_models.Cmp.t_Eq t_Ledger

unfold
let impl_4 = impl_4'

type t_LedgerError =
  | LedgerError_NoSuchAccount : t_LedgerError
  | LedgerError_InsufficientFunds : t_LedgerError
  | LedgerError_BalanceOverflow : t_LedgerError

let t_LedgerError_cast_to_repr (x: t_LedgerError) : isize =
  match x <: t_LedgerError with
  | LedgerError_NoSuchAccount  -> mk_isize 0
  | LedgerError_InsufficientFunds  -> mk_isize 1
  | LedgerError_BalanceOverflow  -> mk_isize 2

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core_models.Fmt.t_Debug t_LedgerError

unfold
let impl_5 = impl_5'

let impl_6: Core_models.Clone.t_Clone t_LedgerError =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': Core_models.Marker.t_Copy t_LedgerError

unfold
let impl_7 = impl_7'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_8': Core_models.Marker.t_StructuralPartialEq t_LedgerError

unfold
let impl_8 = impl_8'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_9': Core_models.Cmp.t_PartialEq t_LedgerError t_LedgerError

unfold
let impl_9 = impl_9'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_10': Core_models.Cmp.t_Eq t_LedgerError

unfold
let impl_10 = impl_10'

let balance_of (l: t_Ledger) (account: usize) : Core_models.Option.t_Option u64 =
  if account <. (Alloc.Vec.impl_1__len #u64 #Alloc.Alloc.t_Global l.f_balances <: usize)
  then Core_models.Option.Option_Some l.f_balances.[ account ] <: Core_models.Option.t_Option u64
  else Core_models.Option.Option_None <: Core_models.Option.t_Option u64

/// Spec helper and ordinary function: sum of balances from index `i` on,
/// widened to u128 so it cannot overflow (2^64 accounts x u64::MAX < 2^128).
/// Recursive on purpose: it extracts to a structurally-recursive F*
/// function that induction proofs can unfold.
let rec sum_from (balances: t_Slice u64) (i: usize)
    : Prims.Pure u128
      Prims.l_True
      (ensures
        fun result ->
          let result:u128 = result in
          result <=.
          ((if i <=. (Core_models.Slice.impl__len #u64 balances <: usize) <: bool
              then cast ((Core_models.Slice.impl__len #u64 balances <: usize) -! i <: usize) <: u128
              else mk_u128 0) *!
            (cast (Core_models.Num.impl_u64__MAX <: u64) <: u128)
            <:
            u128))
      (decreases
        (Rust_primitives.Hax.Int.from_machine (if
                i <=. (Core_models.Slice.impl__len #u64 balances <: usize) <: bool
              then (Core_models.Slice.impl__len #u64 balances <: usize) -! i <: usize
              else mk_usize 0)
          <:
          Hax_lib.Int.t_Int)) =
  if i >=. (Core_models.Slice.impl__len #u64 balances <: usize)
  then mk_u128 0
  else
    (cast (balances.[ i ] <: u64) <: u128) +! (sum_from balances (i +! mk_usize 1 <: usize) <: u128)

let sum_balances (balances: t_Slice u64) : u128 = sum_from balances (mk_usize 0)

module FSeq = FStar.Seq

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
(* sum of an all-zero sequence is zero *)
let rec lemma_sum_create_zero (n: usize) (i: usize)
  : Lemma (ensures v (sum_from (FSeq.create (v n) (mk_u64 0)) i) == 0)
          (decreases (if v i <= v n then v n - v i else 0))
  = if v i < v n then lemma_sum_create_zero n (i +! mk_usize 1) else ()
#pop-options

/// A fresh ledger: `accounts` accounts, all balances zero.
let new_ledger (accounts: usize)
    : Prims.Pure t_Ledger
      Prims.l_True
      (ensures
        fun l ->
          let l:t_Ledger = l in
          (sum_balances (Alloc.Vec.impl_1__as_slice l.f_balances <: t_Slice u64) <: u128) =.
          l.f_total &&
          l.f_total =. mk_u128 0) =
  let _:Prims.unit = lemma_sum_create_zero accounts (mk_usize 0) in
  { f_balances = Alloc.Vec.from_elem #u64 (mk_u64 0) accounts; f_total = mk_u128 0 } <: t_Ledger

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
(* updating one slot: sum(upd) + old == sum + new (suffix containing k) *)
let rec lemma_sum_upd (s: t_Slice u64) (k: usize) (x: u64) (i: usize)
  : Lemma (requires v k < FSeq.length s)
          (ensures (let s' : t_Slice u64 = FSeq.upd s (v k) x in
                    (v i <= v k ==>
                       v (sum_from s' i) + v (FSeq.index s (v k))
                    == v (sum_from s i) + v x) /\
                    (v i > v k ==> v (sum_from s' i) == v (sum_from s i))))
          (decreases (if v i <= FSeq.length s then FSeq.length s - v i else 0))
  = if v i >= FSeq.length s then ()
    else lemma_sum_upd s k x (i +! mk_usize 1)

(* to_vec builds `append empty s`; bridge it back to `s` *)
let lemma_append_empty (s: t_Slice u64)
  : Lemma (FSeq.append (FSeq.empty #u64) s == s)
          [SMTPat (FSeq.append (FSeq.empty #u64) s)]
  = FSeq.lemma_eq_elim (FSeq.append (FSeq.empty #u64) s) s
#pop-options

/// Create `amount` new tokens in `to`\'s balance.
let mint (l: t_Ledger) (to: usize) (amount: u64)
    : Prims.Pure (t_Ledger & Core_models.Result.t_Result Prims.unit t_LedgerError)
      (requires
        (sum_balances (Alloc.Vec.impl_1__as_slice l.f_balances <: t_Slice u64) <: u128) =. l.f_total
      )
      (ensures
        fun temp_0_ ->
          let (l2: t_Ledger), (r: Core_models.Result.t_Result Prims.unit t_LedgerError) = temp_0_ in
          (sum_balances (Alloc.Vec.impl_1__as_slice l2.f_balances <: t_Slice u64) <: u128) =.
          l2.f_total &&
          (match r <: Core_models.Result.t_Result Prims.unit t_LedgerError with
            | Core_models.Result.Result_Ok () ->
              l2.f_total =. (l.f_total +! (cast (amount <: u64) <: u128) <: u128)
            | Core_models.Result.Result_Err _ -> l2 =. l)) =
  if to >=. (Alloc.Vec.impl_1__len #u64 #Alloc.Alloc.t_Global l.f_balances <: usize)
  then
    l,
    (Core_models.Result.Result_Err (LedgerError_NoSuchAccount <: t_LedgerError)
      <:
      Core_models.Result.t_Result Prims.unit t_LedgerError)
    <:
    (t_Ledger & Core_models.Result.t_Result Prims.unit t_LedgerError)
  else
    match
      Core_models.Num.impl_u64__checked_add (l.f_balances.[ to ] <: u64) amount
      <:
      Core_models.Option.t_Option u64
    with
    | Core_models.Option.Option_None  ->
      l,
      (Core_models.Result.Result_Err (LedgerError_BalanceOverflow <: t_LedgerError)
        <:
        Core_models.Result.t_Result Prims.unit t_LedgerError)
      <:
      (t_Ledger & Core_models.Result.t_Result Prims.unit t_LedgerError)
    | Core_models.Option.Option_Some v_new ->
      let _:Prims.unit =
        lemma_sum_upd (Alloc.Vec.impl_1__as_slice l.f_balances) to v_new (mk_usize 0)
      in
      let l2:t_Ledger = l in
      let l2:t_Ledger =
        {
          l2 with
          f_balances
          =
          Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice
                    l2.f_balances
                  <:
                  t_Slice u64)
                to
                v_new
              <:
              t_Slice u64)
        }
        <:
        t_Ledger
      in
      let l2:t_Ledger =
        { l2 with f_total = l2.f_total +! (cast (amount <: u64) <: u128) } <: t_Ledger
      in
      l2,
      (Core_models.Result.Result_Ok (() <: Prims.unit)
        <:
        Core_models.Result.t_Result Prims.unit t_LedgerError)
      <:
      (t_Ledger & Core_models.Result.t_Result Prims.unit t_LedgerError)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
(* one element never exceeds a sum over a suffix containing it *)
let rec lemma_elem_le_sum (s: t_Slice u64) (k: usize) (i: usize)
  : Lemma (requires v k < FSeq.length s /\ v i <= v k)
          (ensures v (FSeq.index s (v k)) <= v (sum_from s i))
          (decreases (FSeq.length s - v i))
  = if v i < v k then lemma_elem_le_sum s k (i +! mk_usize 1) else ()
#pop-options

/// Destroy `amount` tokens from `from`\'s balance.
let burn (l: t_Ledger) (from: usize) (amount: u64)
    : Prims.Pure (t_Ledger & Core_models.Result.t_Result Prims.unit t_LedgerError)
      (requires
        (sum_balances (Alloc.Vec.impl_1__as_slice l.f_balances <: t_Slice u64) <: u128) =. l.f_total
      )
      (ensures
        fun temp_0_ ->
          let (l2: t_Ledger), (r: Core_models.Result.t_Result Prims.unit t_LedgerError) = temp_0_ in
          (sum_balances (Alloc.Vec.impl_1__as_slice l2.f_balances <: t_Slice u64) <: u128) =.
          l2.f_total &&
          (match r <: Core_models.Result.t_Result Prims.unit t_LedgerError with
            | Core_models.Result.Result_Ok () ->
              (l2.f_total +! (cast (amount <: u64) <: u128) <: u128) =. l.f_total
            | Core_models.Result.Result_Err _ -> l2 =. l)) =
  if from >=. (Alloc.Vec.impl_1__len #u64 #Alloc.Alloc.t_Global l.f_balances <: usize)
  then
    l,
    (Core_models.Result.Result_Err (LedgerError_NoSuchAccount <: t_LedgerError)
      <:
      Core_models.Result.t_Result Prims.unit t_LedgerError)
    <:
    (t_Ledger & Core_models.Result.t_Result Prims.unit t_LedgerError)
  else
    match
      Core_models.Num.impl_u64__checked_sub (l.f_balances.[ from ] <: u64) amount
      <:
      Core_models.Option.t_Option u64
    with
    | Core_models.Option.Option_None  ->
      l,
      (Core_models.Result.Result_Err (LedgerError_InsufficientFunds <: t_LedgerError)
        <:
        Core_models.Result.t_Result Prims.unit t_LedgerError)
      <:
      (t_Ledger & Core_models.Result.t_Result Prims.unit t_LedgerError)
    | Core_models.Option.Option_Some v_new ->
      let _:Prims.unit =
        lemma_elem_le_sum (Alloc.Vec.impl_1__as_slice l.f_balances) from (mk_usize 0)
      in
      let _:Prims.unit =
        lemma_sum_upd (Alloc.Vec.impl_1__as_slice l.f_balances) from v_new (mk_usize 0)
      in
      let old_total:u128 = l.f_total in
      let l2:t_Ledger = l in
      let l2:t_Ledger =
        {
          l2 with
          f_balances
          =
          Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (Alloc.Vec.impl_1__as_slice
                    l2.f_balances
                  <:
                  t_Slice u64)
                from
                v_new
              <:
              t_Slice u64)
        }
        <:
        t_Ledger
      in
      let l2:t_Ledger =
        { l2 with f_total = l2.f_total -! (cast (amount <: u64) <: u128) } <: t_Ledger
      in
      let _:Prims.unit =
        Hax_lib.v_assert ((sum_balances (Alloc.Vec.impl_1__as_slice l2.f_balances <: t_Slice u64)
              <:
              u128) =.
            l2.f_total
            <:
            bool)
      in
      let _:Prims.unit =
        Hax_lib.v_assert ((l2.f_total +! (cast (amount <: u64) <: u128) <: u128) =. old_total
            <:
            bool)
      in
      l2,
      (Core_models.Result.Result_Ok (() <: Prims.unit)
        <:
        Core_models.Result.t_Result Prims.unit t_LedgerError)
      <:
      (t_Ledger & Core_models.Result.t_Result Prims.unit t_LedgerError)

/// Move `amount` from `from` to `to`. `from == to` is a no-op that still
/// validates the account and the balance.
let transfer (l: t_Ledger) (from to: usize) (amount: u64)
    : Prims.Pure (t_Ledger & Core_models.Result.t_Result Prims.unit t_LedgerError)
      (requires
        (sum_balances (Alloc.Vec.impl_1__as_slice l.f_balances <: t_Slice u64) <: u128) =. l.f_total
      )
      (ensures
        fun temp_0_ ->
          let (l2: t_Ledger), (r: Core_models.Result.t_Result Prims.unit t_LedgerError) = temp_0_ in
          (sum_balances (Alloc.Vec.impl_1__as_slice l2.f_balances <: t_Slice u64) <: u128) =.
          l2.f_total &&
          l2.f_total =. l.f_total &&
          (match r <: Core_models.Result.t_Result Prims.unit t_LedgerError with
            | Core_models.Result.Result_Ok () -> true
            | Core_models.Result.Result_Err _ -> l2 =. l)) =
  if
    from >=. (Alloc.Vec.impl_1__len #u64 #Alloc.Alloc.t_Global l.f_balances <: usize) ||
    to >=. (Alloc.Vec.impl_1__len #u64 #Alloc.Alloc.t_Global l.f_balances <: usize)
  then
    l,
    (Core_models.Result.Result_Err (LedgerError_NoSuchAccount <: t_LedgerError)
      <:
      Core_models.Result.t_Result Prims.unit t_LedgerError)
    <:
    (t_Ledger & Core_models.Result.t_Result Prims.unit t_LedgerError)
  else
    match
      Core_models.Num.impl_u64__checked_sub (l.f_balances.[ from ] <: u64) amount
      <:
      Core_models.Option.t_Option u64
    with
    | Core_models.Option.Option_None  ->
      l,
      (Core_models.Result.Result_Err (LedgerError_InsufficientFunds <: t_LedgerError)
        <:
        Core_models.Result.t_Result Prims.unit t_LedgerError)
      <:
      (t_Ledger & Core_models.Result.t_Result Prims.unit t_LedgerError)
    | Core_models.Option.Option_Some new_src ->
      if from =. to
      then
        l,
        (Core_models.Result.Result_Ok (() <: Prims.unit)
          <:
          Core_models.Result.t_Result Prims.unit t_LedgerError)
        <:
        (t_Ledger & Core_models.Result.t_Result Prims.unit t_LedgerError)
      else
        match
          Core_models.Num.impl_u64__checked_add (l.f_balances.[ to ] <: u64) amount
          <:
          Core_models.Option.t_Option u64
        with
        | Core_models.Option.Option_None  ->
          l,
          (Core_models.Result.Result_Err (LedgerError_BalanceOverflow <: t_LedgerError)
            <:
            Core_models.Result.t_Result Prims.unit t_LedgerError)
          <:
          (t_Ledger & Core_models.Result.t_Result Prims.unit t_LedgerError)
        | Core_models.Option.Option_Some new_dst ->
          let _:Prims.unit =
            lemma_sum_upd (Alloc.Vec.impl_1__as_slice l.f_balances) from new_src (mk_usize 0)
          in
          let _:Prims.unit =
            lemma_sum_upd (FSeq.upd (Alloc.Vec.impl_1__as_slice l.f_balances) (v from) new_src)
              to
              new_dst
              (mk_usize 0)
          in
          let l2:t_Ledger = l in
          let l2:t_Ledger =
            {
              l2 with
              f_balances
              =
              Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (
                      Alloc.Vec.impl_1__as_slice l2.f_balances <: t_Slice u64)
                    from
                    new_src
                  <:
                  t_Slice u64)
            }
            <:
            t_Ledger
          in
          let l2:t_Ledger =
            {
              l2 with
              f_balances
              =
              Alloc.Slice.impl__to_vec (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (
                      Alloc.Vec.impl_1__as_slice l2.f_balances <: t_Slice u64)
                    to
                    new_dst
                  <:
                  t_Slice u64)
            }
            <:
            t_Ledger
          in
          l2,
          (Core_models.Result.Result_Ok (() <: Prims.unit)
            <:
            Core_models.Result.t_Result Prims.unit t_LedgerError)
          <:
          (t_Ledger & Core_models.Result.t_Result Prims.unit t_LedgerError)
