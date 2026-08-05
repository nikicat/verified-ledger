# CI: add a verification lane that must *discharge* extracted contracts, not just snapshot them

## Observation

The test suite pins extraction *output* (snapshots) and CI verifies
downstream crypto (Bertie, libcrux). Neither exercises the
contract-verification surface: no lane runs `fstar.exe` over extracted
programs whose `requires`/`ensures` must actually be discharged.

Crypto-style code doesn't hit that surface — it rarely uses checked
arithmetic under a contract, `decreases` over machine ints, or
`ensures` over derived-eq types. As a result, at 54c34967 (with snapshot
CI green) a small contract-bearing crate fails verification twice over:

* missing `checked_add`/`checked_sub` models (issue: #2120),
* `decreases` over machine ints unprovable without a `v` coercion
  (issue: #2121).

Both would have been caught at introduction time by any must-discharge
test.

## Proposal

A `tests/verify/` lane (or an `examples/`-style entry, which CI already
knows how to build): a handful of small crates with real contracts,
extracted and then checked with F\* against proof-libs in CI. Failure of
`fstar.exe` fails the job.

Seed content we can contribute:

* the two minimized repro crates from the issues above (once fixed, they
  become regression tests);
* a ~130-line token ledger with conservation/atomicity contracts and
  four in-source lemmas (`fstar::before` + explicit `fstar!` lemma
  calls) that exercises: checked arithmetic under `ensures`, recursion +
  `decreases`, `Vec` update under a sum invariant, `requires`-carrying
  state invariants. It currently verifies end to end against proof-libs
  (with the two workarounds above) in ~60 s.

If maintainers are open to this, we'll prepare the PR (crates + a
workflow job pinning F\* to the flake's version).
