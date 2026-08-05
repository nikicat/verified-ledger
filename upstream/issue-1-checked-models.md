# core-models: missing `checked_add`/`checked_sub` — F\* backend emits `Core_models.Num.impl_u64__checked_add`

While verifying a small contract-bearing crate (a token ledger) end to end
with the F\* backend, extraction of ordinary `u64::checked_add`/`checked_sub`
calls produces references to models that don't exist in proof-libs.

## Repro (hax @ 54c34967, F\* v2025.10.06)

```rust
pub fn saturating_ish_add(x: u64, y: u64) -> u64 {
    x.checked_add(y).unwrap_or(u64::MAX)
}
```

```
cargo hax into fstar
fstar.exe --include proof-libs/fstar/rust_primitives --include proof-libs/fstar/core \
  --include hax-lib/proofs/fstar/extraction Repro.fst
```

```
* Error 72 at Repro.fst(8,21-8,42):
  - Identifier impl_u64__checked_add not found in module Core_models.Num
  - Hint: Did you mean impl_u64__unchecked_add?
```

## Analysis

`Core_models.Num` has the `unchecked_*`/`overflowing_*` families but no
`checked_*`. Adding them at the F\* level inside `Core_models.Num` is not
possible as-is: their signature needs `Core_models.Option.t_Option`, but
`Option` includes `Bundle`, which depends on `Num` — a dependency cycle
(we hit it). The natural home appears to be the `core-models` Rust crate,
where both backends would inherit the models — same work-stream as #2088
(`checked_pow`/`overflowing_pow`).

## Workaround we ship today

A local helper module plus a call-site rewrite in our pipeline:

```fstar
let checked_add_u64 (x y: u64) : Core_models.Option.t_Option u64 =
  if x <=. (Core_models.Num.impl_u64__MAX -! y <: u64)
  then Core_models.Option.Option_Some (x +! y)
  else Core_models.Option.Option_None

let checked_sub_u64 (x y: u64) : Core_models.Option.t_Option u64 =
  if y <=. x
  then Core_models.Option.Option_Some (x -! y)
  else Core_models.Option.Option_None
```

Both verify, and downstream contract proofs (conservation of a ledger)
go through against them.

Happy to turn this into a PR adding `checked_add`/`checked_sub` (and the
other widths) to the `core-models` Rust crate if that's the right place —
guidance on placement welcome.
