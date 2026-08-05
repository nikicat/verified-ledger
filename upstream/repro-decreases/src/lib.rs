//! Repro: #[hax_lib::decreases] over machine ints extracts a measure of
//! type usize; int_t is a datatype (MkInt), so F*'s well-founded ordering
//! compares subterms, not values -> termination unprovable.
//! Hand-wrapping the extracted measure in `v` fixes it.
#[hax_lib::decreases(if i <= n { n - i } else { 0 })]
pub fn count_up(n: usize, i: usize) -> usize {
    if i >= n { 0 } else { 1 + count_up(n, i + 1) }
}
