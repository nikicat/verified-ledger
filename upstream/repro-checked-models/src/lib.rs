//! Repro: extraction references Core_models.Num.impl_u64__checked_add,
//! which does not exist in proof-libs (only unchecked_* variants do).
pub fn saturating_ish_add(x: u64, y: u64) -> u64 {
    x.checked_add(y).unwrap_or(u64::MAX)
}
