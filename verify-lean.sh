#!/bin/sh -e
# ARCHIVED: the Lean/Aeneas verification pipeline (superseded by verify.sh,
# which uses hax's F* backend as the primary path).
#
# NOTE: proofs/lean/Proofs.lean was proven against the pre-F*-port revision
# of src/lib.rs (before the decreases/requires attributes and the additive
# burn ensures). Re-extracting now will shift the __N.ensures item numbering
# and shapes; the semantic theorems still describe the same operations, but
# expect proof maintenance before this pipeline is green again.

AENEAS_HOME="${AENEAS_HOME:-$HOME/.local/opt/aeneas}"
export PATH="$AENEAS_HOME:$HOME/.cargo/bin:$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")"

cargo test --quiet
cargo hax into lean >/dev/null 2>&1 || true
test -f proofs/lean/llbc/verified_ledger.llbc
"$AENEAS_HOME/aeneas" -backend lean -dest proofs/lean \
    proofs/lean/llbc/verified_ledger.llbc
sed -i 's/^def _\.future/def anon.future/; s/^def _\.ensures/def anon.ensures/; s/def _ : Unit/def anon : Unit/; s/^import Aeneas$/import Aeneas\nset_option linter.style.nameCheck false/' \
    proofs/lean/VerifiedLedger.lean
LEANDIR="$AENEAS_HOME/backends/lean"
{ cat proofs/lean/VerifiedLedger.lean
  grep -v "^import" proofs/lean/Proofs.lean
} > "$LEANDIR/Combined.lean"
( cd "$LEANDIR" && lake env lean Combined.lean )
echo "VERIFIED (Lean): conservation + atomicity for new_ledger/mint/burn/transfer"
