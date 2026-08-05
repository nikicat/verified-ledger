/-!
# Conservation proofs for the extracted ledger

Proves, over the Aeneas-extracted model in `VerifiedLedger.lean`, the
contracts stated as `hax_lib::ensures` in `src/lib.rs`:

  * every operation returns `ok` (no panic / overflow / OOB is reachable),
  * conservation: `sum(balances) == total` is preserved by every operation,
  * supply moves only by mint/burn amounts; transfers never change it,
  * atomicity: on `Err` the returned ledger equals the input.

`lsum` is the pure mathematical sum the proofs reason with; `sum_from_spec`
bridges it to the extracted (monadic, u128) `sum_from`.
-/

namespace verified_ledger
open Aeneas Aeneas.Std Aeneas.Std.WP Result

/-! ## Pure model -/

def lsum (bs : List Std.U64) : Nat := (bs.map (·.val)).sum

/-- The ledger invariant: the balances really do sum to `total`. -/
def conserved (l : Ledger) : Prop := lsum l.balances.val = l.total.val

/-! ## Sum lemmas (structural induction) -/

theorem lsum_nil : lsum [] = 0 := rfl

theorem lsum_cons (b : Std.U64) (t : List Std.U64) :
    lsum (b :: t) = b.val + lsum t := by simp [lsum]

/-- every balance is at most u64::MAX, so the sum is bounded by len * MAX -/
theorem lsum_le (bs : List Std.U64) : lsum bs ≤ bs.length * Std.U64.max := by
  induction bs with
  | nil => simp [lsum]
  | cons b t ih =>
    have hb : b.val ≤ Std.U64.max := by scalar_tac
    simp only [lsum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- one element never exceeds the whole sum -/
theorem getElem_le_lsum (bs : List Std.U64) (i : Nat) (h : i < bs.length) :
    bs[i].val ≤ lsum bs := by
  induction bs generalizing i with
  | nil => simp at h
  | cons b t ih =>
    cases i with
    | zero => simp [lsum_cons]
    | succ j =>
      have := ih j (by simpa using h)
      simp only [List.getElem_cons_succ, lsum_cons]
      omega

/-- updating one slot: sum(set) + old = sum + new -/
theorem lsum_set (bs : List Std.U64) (i : Nat) (x : Std.U64) (h : i < bs.length) :
    lsum (bs.set i x) + bs[i].val = lsum bs + x.val := by
  induction bs generalizing i with
  | nil => simp at h
  | cons b t ih =>
    cases i with
    | zero => simp [lsum_cons]; omega
    | succ j =>
      have := ih j (by simpa using h)
      simp only [List.set_cons_succ, lsum_cons, List.getElem_cons_succ]
      omega

theorem usize_max_le_u64_max : Std.Usize.max ≤ Std.U64.max := by
  cases System.Platform.numBits_eq <;>
    simp_all [Std.Usize.max, Std.U64.max, Std.Usize.numBits, Std.U64.numBits] <;>
    omega

theorem lsum_replicate_zero (n : Nat) : lsum (List.replicate n 0#u64) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, lsum_cons, ih]

/-- peeling one element off a dropped suffix -/
theorem lsum_drop_succ (bs : List Std.U64) (i : Nat) (h : i < bs.length) :
    lsum (bs.drop i) = bs[i].val + lsum (bs.drop (i + 1)) := by
  induction bs generalizing i with
  | nil => simp at h
  | cons b t ih =>
    cases i with
    | zero => simp [lsum_cons]
    | succ j =>
      have := ih j (by simpa using h)
      simpa [lsum_cons] using this

/-! ## Bridge: the extracted monadic sum computes `lsum` -/

theorem sum_from_spec (s : Slice Std.U64) (i : Std.Usize) :
    ∃ v, sum_from s i = ok v ∧ v.val = lsum (s.val.drop i.val) := by
  have hlen : s.val.length ≤ Std.Usize.max := s.property
  induction hn : s.val.length - i.val using Nat.strong_induction_on generalizing i with
  | _ n ih =>
  rw [sum_from.eq_def]
  dsimp only
  split
  · -- i ≥ length: empty suffix, sum 0
    rename_i hge
    refine ⟨0#u128, rfl, ?_⟩
    have : s.val.drop i.val = [] := List.drop_eq_nil_of_le (by scalar_tac)
    simp [this, lsum_nil]
  · -- read s[i], recurse on i+1
    rename_i hlt
    have hi : i.val < s.val.length := by scalar_tac
    have ⟨x, hx, hxv⟩ := spec_imp_exists (Slice.index_usize_spec s i hi)
    have ⟨i4, hi4, hi4v⟩ := spec_imp_exists (Std.Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    have ⟨v5, hv5, hv5v⟩ := ih (s.val.length - (i.val + 1)) (by scalar_tac) i4 (by scalar_tac)
    -- the final u128 addition cannot overflow
    have hxb : x.val ≤ Std.U64.max := by scalar_tac
    have hsum : lsum (s.val.drop i4.val) ≤ s.val.length * Std.U64.max := by
      have := lsum_le (s.val.drop i4.val)
      have : (s.val.drop i4.val).length ≤ s.val.length := by simp
      calc lsum (s.val.drop i4.val)
          ≤ (s.val.drop i4.val).length * Std.U64.max := lsum_le _
        _ ≤ s.val.length * Std.U64.max := by
            apply Nat.mul_le_mul_right; simp
    have hcast : (UScalar.cast .U128 x).val = x.val := by
      simp [UScalar.cast_val_eq]; scalar_tac
    have hnoof : (UScalar.cast .U128 x).val + v5.val ≤ Std.U128.max := by
      rw [hcast, hv5v]
      have h1 : lsum (s.val.drop i4.val) ≤ Std.U64.max * Std.U64.max :=
        calc lsum (s.val.drop i4.val)
            ≤ s.val.length * Std.U64.max := hsum
          _ ≤ Std.U64.max * Std.U64.max :=
              Nat.mul_le_mul_right _ (le_trans hlen usize_max_le_u64_max)
      have h2 : Std.U64.max * Std.U64.max + Std.U64.max ≤ Std.U128.max := by
        scalar_tac
      omega
    have ⟨z, hz, hzv⟩ := spec_imp_exists (Std.U128.add_spec hnoof)
    have h1v : (1#usize).val = 1 := by scalar_tac
    refine ⟨z, ?_, ?_⟩
    · simp [hx, ← hxv, hi4, hv5, hz, lift]
    · rw [hzv, hcast, hv5v, hi4v, h1v, lsum_drop_succ s.val i.val hi, hxv]

theorem sum_balances_spec (s : Slice Std.U64) :
    ∃ v, sum_balances s = ok v ∧ v.val = lsum s.val := by
  have ⟨v, h1, h2⟩ := sum_from_spec s 0#usize
  exact ⟨v, h1, by simpa using h2⟩

/-! ## The operation contracts -/

theorem new_ledger_spec (n : Std.Usize) :
    ∃ l, new_ledger n = ok l ∧ conserved l ∧ l.total.val = 0 := by
  unfold new_ledger
  have ⟨v, hv, hvv⟩ := spec_imp_exists
    (alloc.vec.from_elem_spec core.clone.CloneU64 0#u64 n (by rfl))
  refine ⟨⟨v, 0#u128⟩, by simp [hv], ?_, by simp⟩
  simp [conserved, hvv, lsum_replicate_zero]

theorem mint_spec (l : Ledger) (to1 : Std.Usize) (amount : Std.U64)
    (hc : conserved l) :
    ∃ l2 r, mint l to1 amount = ok (l2, r) ∧ conserved l2 ∧
      (∀ u, r = core.result.Result.Ok u →
        l2.total.val = l.total.val + amount.val) ∧
      (∀ e, r = core.result.Result.Err e → l2 = l) := by
  unfold mint
  dsimp only
  split
  · -- account out of range: error, unchanged
    exact ⟨l, core.result.Result.Err LedgerError.NoSuchAccount, rfl, hc,
           by simp, by simp⟩
  · rename_i hin
    have hi : to1.val < l.balances.val.length := by scalar_tac
    have ⟨x, hx, hxv⟩ :=
      spec_imp_exists (alloc.vec.Vec.index_usize_spec l.balances to1 hi)
    have hca := Std.U64.checked_add_bv_spec x amount
    cases hcae : Std.U64.checked_add x amount with
    | none =>
      -- balance would overflow: error, unchanged
      refine ⟨l, core.result.Result.Err LedgerError.BalanceOverflow, ?_, hc,
              by simp, by simp⟩
      simp [alloc.vec.Vec.index_slice_index, hx, ← hxv, hcae, lift]
    | some new =>
      rw [hcae] at hca
      have ⟨hnoof, hnv, _⟩ := hca
      have ⟨p, hp, hpv⟩ :=
        spec_imp_exists (alloc.vec.Vec.index_mut_usize_spec l.balances to1 hi)
      obtain ⟨pe, pback⟩ := p
      obtain ⟨hpe, hpback⟩ := hpv
      have hcst : (UScalar.cast .U128 amount).val = amount.val := by
        simp [UScalar.cast_val_eq]; scalar_tac
      -- the u128 total addition cannot overflow: total = lsum <= MAX^2
      have hbound : l.total.val + (UScalar.cast .U128 amount).val ≤ Std.U128.max := by
        rw [hcst]
        have h1 : lsum l.balances.val ≤ Std.U64.max * Std.U64.max :=
          calc lsum l.balances.val
              ≤ l.balances.val.length * Std.U64.max := lsum_le _
            _ ≤ Std.U64.max * Std.U64.max :=
                Nat.mul_le_mul_right _
                  (le_trans l.balances.property usize_max_le_u64_max)
        have h2 : Std.U64.max * Std.U64.max + Std.U64.max ≤ Std.U128.max := by
          scalar_tac
        have hamt : amount.val ≤ Std.U64.max := by scalar_tac
        rw [conserved] at hc
        omega
      have ⟨t2, ht2, ht2v⟩ := spec_imp_exists (Std.U128.add_spec hbound)
      refine ⟨⟨pback new, t2⟩, core.result.Result.Ok (), ?_, ?_, ?_, by simp⟩
      · simp [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index,
              hx, ← hxv, hcae, lift, hp, ht2]
      · -- conservation of the new state
        rw [conserved, hpback]
        simp only [alloc.vec.Vec.set_val_eq]
        have hset := lsum_set l.balances.val to1.val new hi
        rw [← hxv] at hset
        rw [hcst] at ht2v
        rw [conserved] at hc
        omega
      · intro u _
        simp [ht2v, hcst]

theorem burn_spec (l : Ledger) (from1 : Std.Usize) (amount : Std.U64)
    (hc : conserved l) :
    ∃ l2 r, burn l from1 amount = ok (l2, r) ∧ conserved l2 ∧
      (∀ u, r = core.result.Result.Ok u →
        l2.total.val = l.total.val - amount.val ∧ amount.val ≤ l.total.val) ∧
      (∀ e, r = core.result.Result.Err e → l2 = l) := by
  unfold burn
  dsimp only
  split
  · exact ⟨l, core.result.Result.Err LedgerError.NoSuchAccount, rfl, hc,
           by simp, by simp⟩
  · rename_i hin
    have hi : from1.val < l.balances.val.length := by scalar_tac
    have ⟨x, hx, hxv⟩ :=
      spec_imp_exists (alloc.vec.Vec.index_usize_spec l.balances from1 hi)
    have hcs := Std.U64.checked_sub_bv_spec x amount
    cases hcse : Std.U64.checked_sub x amount with
    | none =>
      refine ⟨l, core.result.Result.Err LedgerError.InsufficientFunds, ?_, hc,
              by simp, by simp⟩
      simp [alloc.vec.Vec.index_slice_index, hx, hcse, lift]
    | some new =>
      rw [hcse] at hcs
      have ⟨hle, hnv, _⟩ := hcs
      have ⟨p, hp, hpv⟩ :=
        spec_imp_exists (alloc.vec.Vec.index_mut_usize_spec l.balances from1 hi)
      obtain ⟨pe, pback⟩ := p
      obtain ⟨hpe, hpback⟩ := hpv
      have hcst : (UScalar.cast .U128 amount).val = amount.val := by
        simp [UScalar.cast_val_eq]; scalar_tac
      -- conservation makes the u128 subtraction safe: amount <= x <= sum = total
      have hxle : x.val ≤ lsum l.balances.val := by
        rw [hxv]; exact getElem_le_lsum _ _ hi
      have hsub : (UScalar.cast .U128 amount).val ≤ l.total.val := by
        rw [hcst]; rw [conserved] at hc; omega
      have ⟨t2, ht2, ht2v⟩ := spec_imp_exists (Std.U128.sub_spec hsub)
      refine ⟨⟨pback new, t2⟩, core.result.Result.Ok (), ?_, ?_, ?_, by simp⟩
      · simp [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index,
              hx, hcse, lift, hp, ht2]
      · rw [conserved, hpback]
        simp only [alloc.vec.Vec.set_val_eq]
        have hset := lsum_set l.balances.val from1.val new hi
        rw [← hxv] at hset
        rw [hcst] at ht2v
        rw [conserved] at hc
        omega
      · intro u _
        rw [hcst] at ht2v hsub
        exact ⟨ht2v.1, hsub⟩

theorem transfer_spec (l : Ledger) (from1 to1 : Std.Usize) (amount : Std.U64)
    (hc : conserved l) :
    ∃ l2 r, transfer l from1 to1 amount = ok (l2, r) ∧ conserved l2 ∧
      l2.total = l.total ∧
      (∀ e, r = core.result.Result.Err e → l2 = l) := by
  unfold transfer
  dsimp only
  split
  · exact ⟨l, core.result.Result.Err LedgerError.NoSuchAccount, rfl, hc, rfl,
           by simp⟩
  · rename_i hin1
    split
    · exact ⟨l, core.result.Result.Err LedgerError.NoSuchAccount, rfl, hc, rfl,
             by simp⟩
    · rename_i hin2
      have hif : from1.val < l.balances.val.length := by scalar_tac
      have hit : to1.val < l.balances.val.length := by scalar_tac
      have ⟨x, hx, hxv⟩ :=
        spec_imp_exists (alloc.vec.Vec.index_usize_spec l.balances from1 hif)
      have hcs := Std.U64.checked_sub_bv_spec x amount
      cases hcse : Std.U64.checked_sub x amount with
      | none =>
        refine ⟨l, core.result.Result.Err LedgerError.InsufficientFunds, ?_, hc,
                rfl, by simp⟩
        simp [alloc.vec.Vec.index_slice_index, hx, hcse, lift]
      | some new_src =>
        rw [hcse] at hcs
        have ⟨hle, hnsv, _⟩ := hcs
        split
        · -- self-transfer: validated no-op
          rename_i heq
          subst heq
          refine ⟨l, core.result.Result.Ok (), ?_, hc, rfl, by simp⟩
          simp [alloc.vec.Vec.index_slice_index, hx, hcse, lift]
        · rename_i hne
          have ⟨y, hy, hyv⟩ :=
            spec_imp_exists (alloc.vec.Vec.index_usize_spec l.balances to1 hit)
          have hca := Std.U64.checked_add_bv_spec y amount
          cases hcae : Std.U64.checked_add y amount with
          | none =>
            refine ⟨l, core.result.Result.Err LedgerError.BalanceOverflow, ?_, hc,
                    rfl, by simp⟩
            simp [alloc.vec.Vec.index_slice_index, hx, hcse, lift, hne, hy, hcae]
          | some new_dst =>
            rw [hcae] at hca
            have ⟨hnoof, hndv, _⟩ := hca
            have ⟨p, hp, hpv⟩ :=
              spec_imp_exists (alloc.vec.Vec.index_mut_usize_spec l.balances from1 hif)
            obtain ⟨pe, pback⟩ := p
            obtain ⟨hpe, hpback⟩ := hpv
            have hit2 : to1.val < (alloc.vec.Vec.set l.balances from1 new_src).val.length := by
              simp only [alloc.vec.Vec.set_val_eq]
              simpa using hit
            have ⟨q, hq, hqv⟩ :=
              spec_imp_exists (alloc.vec.Vec.index_mut_usize_spec
                (alloc.vec.Vec.set l.balances from1 new_src) to1 hit2)
            obtain ⟨qe, qback⟩ := q
            obtain ⟨hqe, hqback⟩ := hqv
            refine ⟨⟨qback new_dst, l.total⟩, core.result.Result.Ok (), ?_, ?_, rfl,
                    by simp⟩
            · simp [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index,
                    hx, hcse, lift, hne, hy, hcae, hp, hpback, hq]
            · -- conservation: -amount at from, +amount at to, sum unchanged
              rw [conserved, hqback]
              simp only [alloc.vec.Vec.set_val_eq]
              have hset1 := lsum_set l.balances.val from1.val new_src hif
              rw [← hxv] at hset1
              have hne' : from1.val ≠ to1.val := fun h => hne (by scalar_tac)
              have hgel : (l.balances.val.set from1.val new_src)[to1.val]'(by simpa using hit) =
                  l.balances.val[to1.val]'hit := by
                exact List.getElem_set_ne (by omega) _
              have hset2 := lsum_set (l.balances.val.set from1.val new_src) to1.val new_dst
                (by simpa using hit)
              rw [hgel, ← hyv] at hset2
              rw [conserved] at hc
              omega

/-! ## Bridging to the extracted hax contracts, literally

The `hax_lib::ensures` closures from src/lib.rs were extracted as Lean
functions (`__1.ensures` = mint's contract). These theorems close the
loop: the operation's result makes its own extracted contract evaluate
to `ok true`. -/

theorem partialEqVecU64_refl (v : alloc.vec.Vec Std.U64) :
    alloc.vec.partial_eq.PartialEqVec.eq core.cmp.PartialEqU64 v v = ok true := by
  unfold alloc.vec.partial_eq.PartialEqVec.eq
  rw [if_pos rfl]
  generalize v.val = bs
  induction bs with
  | nil => rfl
  | cons b t ih => simpa [List.allM] using ih

theorem ledger_eq_refl (l : Ledger) :
    Ledger.Insts.CoreCmpPartialEqLedger.eq l l = ok true := by
  unfold Ledger.Insts.CoreCmpPartialEqLedger.eq
  rw [if_pos rfl]
  exact partialEqVecU64_refl l.balances

theorem mint_meets_contract (l : Ledger) (to1 : Std.Usize) (amount : Std.U64)
    (hc : conserved l) :
    ∃ p, mint l to1 amount = ok p ∧ __1.ensures l to1 amount p = ok true := by
  obtain ⟨l2, r, hm, hc2, hok, herr⟩ := mint_spec l to1 amount hc
  refine ⟨(l2, r), hm, ?_⟩
  unfold __1.ensures
  dsimp only
  have ⟨sv, hsv, hsvv⟩ := sum_balances_spec (alloc.vec.Vec.deref l2.balances)
  have hsv_eq : sv = l2.total := by
    apply UScalar.eq_of_val_eq
    rw [hsvv]; rw [conserved] at hc2
    simpa [alloc.vec.Vec.deref] using hc2
  cases r with
  | Ok u =>
    have htot := hok u rfl
    have hcst : (UScalar.cast .U128 amount).val = amount.val := by
      simp [UScalar.cast_val_eq]; scalar_tac
    have hb : l.total.val + (UScalar.cast .U128 amount).val ≤ Std.U128.max := by
      rw [hcst]
      have h2 : l2.total.val ≤ Std.U128.max := by scalar_tac
      omega
    have ⟨z, hz, hzv⟩ := spec_imp_exists (Std.U128.add_spec hb)
    have hz_eq : l2.total = z := by
      apply UScalar.eq_of_val_eq
      rw [hzv, hcst, htot]
    simp [hsv, hsv_eq, hz, lift, hz_eq]
  | Err e =>
    have hl : l2 = l := herr e rfl
    subst hl
    simp [hsv, hsv_eq, lift, ledger_eq_refl]

theorem new_ledger_meets_contract (n : Std.Usize) :
    ∃ l, new_ledger n = ok l ∧ anon.ensures n l = ok true := by
  obtain ⟨l, hn, hc, ht⟩ := new_ledger_spec n
  refine ⟨l, hn, ?_⟩
  unfold anon.ensures
  dsimp only
  have ⟨sv, hsv, hsvv⟩ := sum_balances_spec (alloc.vec.Vec.deref l.balances)
  have hsv_eq : sv = l.total := by
    apply UScalar.eq_of_val_eq
    rw [hsvv]; rw [conserved] at hc
    simpa [alloc.vec.Vec.deref] using hc
  have ht0 : l.total = 0#u128 := by
    apply UScalar.eq_of_val_eq; simpa using ht
  simp [hsv, hsv_eq, ht0]

theorem burn_meets_contract (l : Ledger) (from1 : Std.Usize) (amount : Std.U64)
    (hc : conserved l) :
    ∃ p, burn l from1 amount = ok p ∧ __2.ensures l from1 amount p = ok true := by
  obtain ⟨l2, r, hm, hc2, hok, herr⟩ := burn_spec l from1 amount hc
  refine ⟨(l2, r), hm, ?_⟩
  unfold __2.ensures
  dsimp only
  have ⟨sv, hsv, hsvv⟩ := sum_balances_spec (alloc.vec.Vec.deref l2.balances)
  have hsv_eq : sv = l2.total := by
    apply UScalar.eq_of_val_eq
    rw [hsvv]; rw [conserved] at hc2
    simpa [alloc.vec.Vec.deref] using hc2
  cases r with
  | Ok u =>
    obtain ⟨htot, hle⟩ := hok u rfl
    have hcst : (UScalar.cast .U128 amount).val = amount.val := by
      simp [UScalar.cast_val_eq]; scalar_tac
    have hb : (UScalar.cast .U128 amount).val ≤ l.total.val := by
      rw [hcst]; exact hle
    have ⟨z, hz, hzv⟩ := spec_imp_exists (Std.U128.sub_spec hb)
    have hz_eq : l2.total = z := by
      apply UScalar.eq_of_val_eq
      rw [hzv.1, hcst, htot]
    simp [hsv, hsv_eq, hz, lift, hz_eq]
  | Err e =>
    have hl : l2 = l := herr e rfl
    subst hl
    simp [hsv, hsv_eq, lift, ledger_eq_refl]

theorem transfer_meets_contract (l : Ledger) (from1 to1 : Std.Usize)
    (amount : Std.U64) (hc : conserved l) :
    ∃ p, transfer l from1 to1 amount = ok p ∧
      __3.ensures l from1 to1 amount p = ok true := by
  obtain ⟨l2, r, hm, hc2, htot, herr⟩ := transfer_spec l from1 to1 amount hc
  refine ⟨(l2, r), hm, ?_⟩
  unfold __3.ensures
  dsimp only
  have ⟨sv, hsv, hsvv⟩ := sum_balances_spec (alloc.vec.Vec.deref l2.balances)
  have hsv_eq : sv = l2.total := by
    apply UScalar.eq_of_val_eq
    rw [hsvv]; rw [conserved] at hc2
    simpa [alloc.vec.Vec.deref] using hc2
  cases r with
  | Ok u =>
    simp [hsv, hsv_eq, htot]
  | Err e =>
    have hl : l2 = l := herr e rfl
    subst hl
    simp [hsv, hsv_eq, htot, ledger_eq_refl]

end verified_ledger
