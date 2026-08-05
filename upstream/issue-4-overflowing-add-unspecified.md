# proof-libs: `overflowing_add_*` is an uninterpreted `val`, so the new `checked_add` models are unprovable

Thanks for #2124 — it does unblock the module cycle, and
`Core_models.Num.impl_u64__checked_add` now resolves. But the model it
resolves to carries no specification, so it cannot be used in a proof.

`Core_models.Bundle.impl_9__checked_add` is defined via
`impl_9__overflowing_add`, which forwards to
`Rust_primitives.Arithmetic.overflowing_add_u64`. That symbol is declared
`val` in `Rust_primitives.Arithmetic.fsti` and there is no `.fst` realizing
it, so Z3 knows nothing about its result.

Its sibling `overflowing_sub_u64` **is** defined a few lines below, which is
why `checked_sub` works and `checked_add` does not.

## Repro (hax @ 984ca92e, F\* v2025.10.06)

No hax invocation needed — this is proof-libs only:

```fstar
module Probe
open Rust_primitives

let sub_ok (x y: u64) : Lemma
  (requires v y <= v x)
  (ensures Core_models.Num.impl_u64__checked_sub x y
           == Core_models.Option.Option_Some (x -! y))
  = ()

let add_ok (x y: u64) : Lemma
  (requires v x + v y <= maxint U64)
  (ensures Core_models.Num.impl_u64__checked_add x y
           == Core_models.Option.Option_Some (x +! y))
  = ()
```

```
fstar.exe --include proof-libs/fstar/rust_primitives \
          --include proof-libs/fstar/core \
          --include hax-lib/proofs/fstar/extraction Probe.fst
```

```
* Error 19 at Probe.fst(16,4-16,6):
  - Could not prove post-condition
```

`sub_ok` passes, `add_ok` fails. The inverse direction fails too — from
`impl_u64__checked_add x y == Option_Some r` one cannot derive
`v r == v x + v y` — so the model is unusable in either direction.

## Scope

In `Rust_primitives.Arithmetic.fsti`, of the add/sub overflowing families:

| family | status |
| --- | --- |
| `overflowing_sub_u{8,16,32,64,128,size}` | defined `let` |
| `overflowing_add_*` (all 12, signed and unsigned) | uninterpreted `val` |
| `overflowing_sub_i{8,16,32,64,128,size}` | uninterpreted `val` |

So after #2124 the affected `checked_*` models are `checked_add` on every
integer type and `checked_sub` on the signed ones.

## Suggested fix

Give `overflowing_add_*` the definition its `sub` counterpart already has:

```fstar
let overflowing_add_u64 (x y: u64): u64 & bool
  = let sum = v x + v y in
    let carry = sum > maxint U64 in
    let out = if carry then sum - pow2 64 else sum in
    (mk_u64 out, carry)
```

We applied exactly this locally and both lemmas above discharge.

## Why it matters to us

We verify a small contract-bearing crate (a token ledger: conservation of
supply, atomicity on failure, panic-freedom) end to end with the F\* backend.
Against `984ca92e` unpatched, the split is exactly along this line:

| operation | primitive used | result |
| --- | --- | --- |
| `burn` | `checked_sub` | verifies |
| `mint` | `checked_add` | fails |
| `transfer` | both | fails |

(F\* aborts a module at the first error, so `mint`'s failure masks
`transfer`'s; removing `mint` surfaces it.)

With the five-line definition above in place, the entire crate verifies with
**no post-extraction patching at all** — the local `checked_add`/`checked_sub`
helper module and call-site rewrite we have been carrying since #2120 can be
deleted outright.
