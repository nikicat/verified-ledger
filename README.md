# verified-ledger

A token ledger in ordinary Rust whose money-conservation contracts are
**machine-verified via hax's F\* backend** — statements *and* proof hints
all live in the Rust source:

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

Run it: `./verify.sh` (tests → extraction → F\* check, ~2 min).

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
only string literals (`include_str!` is rejected), so the F* text cannot
yet live in a standalone file; that's an upstreamable feature gap.

A pleasing detail survives from the Lean port: `burn`'s in-body u128
subtraction is provable only *because of* the conservation `requires` —
`amount ≤ balance ≤ sum = total`. The invariant pays for its own
maintenance.

## Toolchain

* hax @ 54c34967, all components from the `~/src/hax` checkout:
  `cargo-hax` + `hax-driver` (cargo, nightly-2025-11-08), **OCaml engine**
  (opam switch, OCaml 5.5.0; needs `hax-export-json-schemas` +
  `hax-engine-names-extract` from cargo in PATH when building),
  proof-libs from the same checkout.
* F\* **v2025.10.06** (hax's pin — newer F\* dropped `FStar.Mul`) at
  `~/.local/opt/fstar-2025.10.06`, bundled Z3.

## Notes and honest caveats

* `patch_extraction.py` papers over one gap at this hax revision:
  missing `checked_add/sub` u64 models in proof-libs (supplied in
  `proofs/fstar/extraction/Verified_ledger_helpers.fst`), an
  upstreamable fix (issue #2120).
* The `decreases` measure is written `(...).to_int()` so it extracts as a
  `nat`; a machine-int measure is not well-founded in F\* (issue #2121).
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
