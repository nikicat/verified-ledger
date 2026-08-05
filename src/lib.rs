//! A token ledger with conservation of value.
//!
//! Fixed set of accounts (indices), u64 balances, u128 total supply.
//! The invariant that must hold after every operation, successful or not:
//! `sum_balances(balances) == total` (conservation).
//!
//! Operations are total functions: no preconditions a caller could
//! violate — bad inputs return `Err` and the ledger comes back unchanged
//! (atomicity). The API is functional (consume the ledger, return it),
//! the style hax extracts best; atomicity becomes a statement about the
//! returned value instead of a story about mutation.

// for `.to_int()` in the `decreases` measure; that attribute is erased
// outside hax, hence unused in a plain cargo build.
#[allow(unused_imports)]
use hax_lib::ToInt;

/// Spec helper and ordinary function: sum of balances from index `i` on,
/// widened to u128 so it cannot overflow (2^64 accounts x u64::MAX < 2^128).
/// Recursive on purpose: it extracts to a structurally-recursive F*
/// function that induction proofs can unfold.
#[hax_lib::decreases((if i <= balances.len() { balances.len() - i } else { 0 }).to_int())]
#[hax_lib::ensures(|result| result
    <= (if i <= balances.len() { (balances.len() - i) as u128 } else { 0 })
        * (u64::MAX as u128))]
pub fn sum_from(balances: &[u64], i: usize) -> u128 {
    if i >= balances.len() {
        0
    } else {
        balances[i] as u128 + sum_from(balances, i + 1)
    }
}

pub fn sum_balances(balances: &[u64]) -> u128 {
    sum_from(balances, 0)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ledger {
    pub balances: Vec<u64>,
    pub total: u128,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LedgerError {
    NoSuchAccount,
    InsufficientFunds,
    BalanceOverflow,
}

use LedgerError::*;

#[hax_lib::fstar::before(r#"
module FSeq = FStar.Seq

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
(* sum of an all-zero sequence is zero *)
let rec lemma_sum_create_zero (n: usize) (i: usize)
  : Lemma (ensures v (sum_from (FSeq.create (v n) (mk_u64 0)) i) == 0)
          (decreases (if v i <= v n then v n - v i else 0))
  = if v i < v n then lemma_sum_create_zero n (i +! mk_usize 1) else ()
#pop-options
"#)]
/// A fresh ledger: `accounts` accounts, all balances zero.
#[hax_lib::ensures(|l| sum_balances(&l.balances) == l.total && l.total == 0)]
pub fn new_ledger(accounts: usize) -> Ledger {
    hax_lib::fstar!("lemma_sum_create_zero $accounts (mk_usize 0)");
    Ledger { balances: vec![0; accounts], total: 0 }
}

pub fn balance_of(l: &Ledger, account: usize) -> Option<u64> {
    if account < l.balances.len() { Some(l.balances[account]) } else { None }
}

#[hax_lib::fstar::before(r#"
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
"#)]
/// Create `amount` new tokens in `to`'s balance.
#[hax_lib::ensures(|(l2, r)| sum_balances(&l2.balances) == l2.total
    && match r {
        Ok(()) => l2.total == l.total + amount as u128,
        Err(_) => l2 == l,                // atomicity: failure changes nothing
    })]
#[hax_lib::requires(sum_balances(&l.balances) == l.total)]
pub fn mint(l: Ledger, to: usize, amount: u64) -> (Ledger, Result<(), LedgerError>) {
    if to >= l.balances.len() {
        return (l, Err(NoSuchAccount));
    }
    match l.balances[to].checked_add(amount) {
        None => (l, Err(BalanceOverflow)),
        Some(new) => {
            hax_lib::fstar!("lemma_sum_upd (Alloc.Vec.impl_1__as_slice ${l}.f_balances) $to $new (mk_usize 0)");
            let mut l2 = l;
            l2.balances[to] = new;
            l2.total += amount as u128; // cannot overflow: total == sum, and sums fit
            (l2, Ok(()))
        }
    }
}

#[hax_lib::fstar::before(r#"
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
(* one element never exceeds a sum over a suffix containing it *)
let rec lemma_elem_le_sum (s: t_Slice u64) (k: usize) (i: usize)
  : Lemma (requires v k < FSeq.length s /\ v i <= v k)
          (ensures v (FSeq.index s (v k)) <= v (sum_from s i))
          (decreases (FSeq.length s - v i))
  = if v i < v k then lemma_elem_le_sum s k (i +! mk_usize 1) else ()
#pop-options
"#)]
/// Destroy `amount` tokens from `from`'s balance.
#[hax_lib::ensures(|(l2, r)| sum_balances(&l2.balances) == l2.total
    && match r {
        Ok(()) => l2.total + amount as u128 == l.total,
        Err(_) => l2 == l,
    })]
#[hax_lib::requires(sum_balances(&l.balances) == l.total)]
pub fn burn(l: Ledger, from: usize, amount: u64) -> (Ledger, Result<(), LedgerError>) {
    if from >= l.balances.len() {
        return (l, Err(NoSuchAccount));
    }
    match l.balances[from].checked_sub(amount) {
        None => (l, Err(InsufficientFunds)),
        Some(new) => {
            hax_lib::fstar!("lemma_elem_le_sum (Alloc.Vec.impl_1__as_slice ${l}.f_balances) $from (mk_usize 0)");
            hax_lib::fstar!("lemma_sum_upd (Alloc.Vec.impl_1__as_slice ${l}.f_balances) $from $new (mk_usize 0)");
            let old_total = l.total;
            let mut l2 = l;
            l2.balances[from] = new;
            l2.total -= amount as u128;
            hax_lib::assert!(sum_balances(&l2.balances) == l2.total);
            hax_lib::assert!(l2.total + amount as u128 == old_total);
            (l2, Ok(()))
        }
    }
}

/// Move `amount` from `from` to `to`. `from == to` is a no-op that still
/// validates the account and the balance.
#[hax_lib::ensures(|(l2, r)| sum_balances(&l2.balances) == l2.total
    && l2.total == l.total                    // transfers never change supply
    && match r {
        Ok(()) => true,
        Err(_) => l2 == l,
    })]
#[hax_lib::requires(sum_balances(&l.balances) == l.total)]
pub fn transfer(
    l: Ledger,
    from: usize,
    to: usize,
    amount: u64,
) -> (Ledger, Result<(), LedgerError>) {
    if from >= l.balances.len() || to >= l.balances.len() {
        return (l, Err(NoSuchAccount));
    }
    match l.balances[from].checked_sub(amount) {
        None => (l, Err(InsufficientFunds)),
        Some(new_src) => {
            if from == to {
                // classic landmine: with from == to, "dst + amount" both
                // double-counts and can spuriously overflow — explicit no-op
                return (l, Ok(()));
            }
            match l.balances[to].checked_add(amount) {
                None => (l, Err(BalanceOverflow)),
                Some(new_dst) => {
                    hax_lib::fstar!("lemma_sum_upd (Alloc.Vec.impl_1__as_slice ${l}.f_balances) $from $new_src (mk_usize 0)");
                    hax_lib::fstar!("lemma_sum_upd (FSeq.upd (Alloc.Vec.impl_1__as_slice ${l}.f_balances) (v $from) $new_src) $to $new_dst (mk_usize 0)");
                    let mut l2 = l;
                    l2.balances[from] = new_src;
                    l2.balances[to] = new_dst;
                    (l2, Ok(()))
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn conserved(l: &Ledger) -> bool {
        sum_balances(&l.balances) == l.total
    }

    #[test]
    fn mint_transfer_burn() {
        let l = new_ledger(3);
        let (l, r) = mint(l, 0, 1000);
        assert_eq!(r, Ok(()));
        let (l, r) = transfer(l, 0, 1, 300);
        assert_eq!(r, Ok(()));
        let (l, r) = burn(l, 1, 100);
        assert_eq!(r, Ok(()));
        assert_eq!(balance_of(&l, 0), Some(700));
        assert_eq!(balance_of(&l, 1), Some(200));
        assert_eq!(l.total, 900);
        assert!(conserved(&l));
    }

    #[test]
    fn self_transfer_conserves() {
        let (l, _) = mint(new_ledger(2), 0, 500);
        let (l, r) = transfer(l, 0, 0, 200);
        assert_eq!(r, Ok(()));
        assert_eq!(balance_of(&l, 0), Some(500));
        assert!(conserved(&l));
    }

    #[test]
    fn failures_change_nothing() {
        let (l, _) = mint(new_ledger(2), 0, 500);
        let snapshot = l.clone();
        let (l, r) = transfer(l, 0, 1, 501);
        assert_eq!(r, Err(InsufficientFunds));
        assert_eq!(l, snapshot);
        let (l, r) = transfer(l, 0, 9, 1);
        assert_eq!(r, Err(NoSuchAccount));
        assert_eq!(l, snapshot);
        let (l, _) = mint(l, 1, u64::MAX);
        let snapshot = l.clone();
        let (l, r) = transfer(l, 0, 1, 1);
        assert_eq!(r, Err(BalanceOverflow));
        assert_eq!(l, snapshot);
    }

    #[test]
    fn pseudo_random_op_storm_conserves() {
        // deterministic LCG; every op on every step must conserve
        let mut x: u64 = 42;
        let mut step = || { x = x.wrapping_mul(6364136223846793005).wrapping_add(1); x };
        let mut l = new_ledger(8);
        for _ in 0..10_000 {
            let (a, b, amt) = (step() as usize % 8, step() as usize % 8, step() % 1000);
            l = match step() % 3 {
                0 => mint(l, a, amt).0,
                1 => burn(l, a, amt).0,
                _ => transfer(l, a, b, amt).0,
            };
            assert!(conserved(&l));
        }
    }
}
