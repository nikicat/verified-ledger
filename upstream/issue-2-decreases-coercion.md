# F\* backend: `#[hax_lib::decreases]` over machine ints extracts without `v` coercion — termination unprovable

A recursive function with a machine-int termination measure cannot be
proven terminating in F\*, because the extracted `decreases` clause
compares `int_t` values with the *datatype subterm* ordering rather than
numerically.

## Repro (hax @ 54c34967, F\* v2025.10.06)

```rust
#[hax_lib::decreases(if i <= n { n - i } else { 0 })]
pub fn count_up(n: usize, i: usize) -> usize {
    if i >= n { 0 } else { 1 + count_up(n, i + 1) }
}
```

Extracts to:

```fstar
let rec count_up (n i: usize) : Prims.Tot usize
  (decreases (if i <=. n <: bool then n -! i <: usize else mk_usize 0)) = ...
```

```
* Error 19 at Repro_decreases.fst(8,60-8,86):
  - Could not prove termination of this recursive call
```

Z3 reports `incomplete quantifiers` immediately (not a resource limit).

## Root cause

`Rust_primitives.Integers.int_t` is a datatype
(`type int_t t = | MkInt: range_t t -> int_t t`), so F\*'s well-founded
`<<` on the measure falls back to datatype subterm ordering, which never
relates two distinct `MkInt` values. The measure needs the `v` coercion
to `nat`.

## Demonstrated fix

Patching the generated clause to

```fstar
(decreases Rust_primitives.Integers.v (if i <=. n ... else mk_usize 0))
```

makes the same definition verify (we carry exactly this patch in our
pipeline). Suggested fix: the F\* printer wraps integer-typed `decreases`
payloads in `v (...)` (tuple measures member-wise).

Precedent: the Lean backend had the analogous machine-int termination
issue, fixed in #1882.

Happy to attempt an engine PR with guidance on where the decreases
payload is printed.
