# verified-ledger — a Rust token ledger with machine-checked money conservation

[![verify](https://github.com/nikicat/verified-ledger/actions/workflows/verify.yml/badge.svg)](https://github.com/nikicat/verified-ledger/actions/workflows/verify.yml)

A ~130-line token ledger (mint / burn / transfer over `u64` balances and a
`u128` total supply) written in ordinary Rust, whose safety properties are
**proved for all inputs** rather than tested on some: money is never created
or destroyed, failed operations change nothing, and no arithmetic can
overflow or panic.

The proof is not a separate model of the code — it is run against the code.
[hax](https://github.com/cryspen/hax) extracts `src/lib.rs` to F\*, and
F\*/Z3 discharges the contracts written as attributes in that same Rust
source. `./verify.sh` does the whole thing; CI runs it on every push.

**This is a proof of concept, not a crate to depend on.** It exists to find
out what verifying smart-contract-style invariants (conservation of value,
atomicity, panic-freedom) with **hax + F\*** actually costs on ordinary Rust
— where it is pleasant, where the toolchain still has holes (two filed
upstream, see below). Useful if you are evaluating hax, F\*, or Aeneas/Lean;
not useful as a ledger.

## The contract, in the source

```rust
#[hax_lib::requires(sum_balances(&l.balances) == l.total)]
#[hax_lib::ensures(|(l2, r)| sum_balances(&l2.balances) == l2.total
    && match r {
        Ok(())  => l2.total == l.total + amount as u128,
        Err(_)  => l2 == l,               // atomicity: failure changes nothing
    })]
pub fn mint(l: Ledger, to: usize, amount: u64) -> (Ledger, Result<(), LedgerError>) {
    ...
}
```

That `ensures` holds for every account count, every balance vector, and every
`amount` — checked by Z3, not by examples.

## What is verified

Contracts on `new_ledger`, `mint`, `burn`, `transfer` in `src/lib.rs`,
discharged for **all** inputs satisfying the stated `requires`
(conservation of the input ledger — the type-state invariant):

* **conservation** — `sum_balances(balances) == total` in every returned
  ledger, on every path;
* **supply movement** — mint: `total' = total + amount`; burn:
  `total' + amount = total`; transfer: `total' = total`;
* **atomicity** — on any `Err` the returned ledger equals the input;
* **panic-freedom** — every arithmetic op and index in bodies *and specs*
  is proven in-range (`Prims.Pure` is total).

## Pipeline

```
src/lib.rs        plain Rust
                  + hax_lib::requires/ensures   (the contracts you audit)
                  + hax_lib::decreases          (termination measure)
                  + hax_lib::fstar::before      (4 induction lemmas, verbatim F*,
                                                 split per-op next to consumers)
      │ cargo hax into fstar        (rustc driver + OCaml engine)
      ▼
proofs/fstar/extraction/Verified_ledger.fst     generated — do not edit
      │ patch_extraction.py         (1 toolchain-gap patch, documented there)
      ▼
fstar.exe + Z3 against hax proof-libs           ALL contracts discharged
```

Run it: `./verify.sh` (tests → extraction → F\* check, ~2 min once the
toolchain is in place). `.github/workflows/verify.yml` is the executable
install recipe: pinned hax revision, pinned F\*, no local state.

## How the proofs are organised

The proof hints are four ~5-line induction lemmas defined in three small
`fstar::before` blocks next to their consumers, and — deliberately —
applied **explicitly**: each operation's body invokes the lemmas it needs
by name via `hax_lib::fstar!` statements at the exact point they justify
(e.g. burn calls `lemma_elem_le_sum` then `lemma_sum_upd` right before
mutating). No invisible SMT-pattern instantiation for domain facts; the
proof dataflow is readable in the Rust source. The one exception is
`lemma_append_empty`, kept as an `[SMTPat]` rewrite rule: it normalizes
an extraction artifact (`to_vec` extracts as `append empty s`), and
calling it explicitly would hard-code extraction-internal spellings into
every body. All four lemmas are load-bearing. `fstar::before` accepts
only string literals (`include_str!` is rejected), so the F\* text cannot
yet live in a standalone file; that's an upstreamable feature gap.

A pleasing detail survives from the Lean port: `burn`'s in-body u128
subtraction is provable only *because of* the conservation `requires` —
`amount ≤ balance ≤ sum = total`. The invariant pays for its own
maintenance.

## Toolchain

* hax @ 54c34967: `cargo-hax` + `hax-driver` (cargo, nightly-2025-11-08),
  **OCaml engine** (opam switch, OCaml 5.x; needs `hax-export-json-schemas`
  + `hax-engine-names-extract` from cargo in PATH when building), proof-libs
  from the same checkout. `HAX_HOME` points `verify.sh` at it.
* F\* **v2025.10.06** (hax's pin — newer F\* dropped `FStar.Mul`), bundled
  Z3. `FSTAR_BIN` points `verify.sh` at its `bin`.

## Notes and honest caveats

* `patch_extraction.py` papers over one gap at this hax revision:
  missing `checked_add/sub` u64 models in proof-libs (supplied in
  `proofs/fstar/extraction/Verified_ledger_helpers.fst`), an
  upstreamable fix ([hax#2120](https://github.com/cryspen/hax/issues/2120)).
* The `decreases` measure is written `(...).to_int()` so it extracts as a
  `nat`; a machine-int measure is not well-founded in F\*
  ([hax#2121](https://github.com/cryspen/hax/issues/2121)).
* `burn`'s supply clause is stated additively (`total' + amount = total`)
  because a machine subtraction in an `ensures` must be well-formed for
  arbitrary results — a lesson in writing contracts over machine ints.
* Trusted base: hax extraction fidelity, proof-libs models, F\*+Z3.
* The earlier **Lean/Aeneas pipeline** (charon → aeneas → Lean, kernel-
  checked proofs incl. literal extracted-contract fidelity) is archived:
  `verify-lean.sh` + `proofs/lean/`. Its `Proofs.lean` matches the
  pre-F\*-port revision of `src/lib.rs`; expect proof maintenance if
  re-extracting. Both pipelines proved the same conservation story —
  F\* with ~20 lines of lemmas + SMT, Lean with ~300 lines of explicit
  kernel-checked proof.

## Upstream

`upstream/` holds the minimized repros and the write-ups filed against hax
from this work: the two issues above, plus a proposal for a CI lane that
must *discharge* extracted contracts instead of snapshotting extraction
output.

## License

Apache-2.0 — see [LICENSE](LICENSE).
