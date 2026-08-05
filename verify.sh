#!/bin/sh -e
# Primary verification pipeline: hax F* backend + Z3.
#
#   src/lib.rs  (contracts + F* lemmas, all in the Rust source)
#     --cargo hax into fstar-->  proofs/fstar/extraction/Verified_ledger.fst
#     --patch_extraction.py-->   (1 toolchain-gap patch, see that file)
#     --fstar.exe + Z3-->        all contracts discharged
#
# Toolchain: cargo-hax + hax-driver (cargo, git 54c34967), hax OCaml engine
# (opam, built from ~/src/hax), F* v2025.10.06 (hax's pin), proof-libs from
# the ~/src/hax checkout. The earlier Lean/Aeneas pipeline is archived in
# verify-lean.sh.

HAX_HOME="${HAX_HOME:-$HOME/src/hax}"
FSTAR_BIN="${FSTAR_BIN:-$HOME/.local/opt/fstar-2025.10.06/fstar/bin}"
export PATH="$FSTAR_BIN:$HOME/.cargo/bin:$PATH"
command -v hax-engine >/dev/null 2>&1 || eval "$(opam env)"
cd "$(dirname "$0")"

#echo "== 1/3 rust tests"
#cargo test --quiet

echo "== 2/3 hax: rust -> F*"
cargo hax into fstar
python3 proofs/fstar/patch_extraction.py

echo "== 3/3 F* + Z3: discharge all contracts"
HL="$HAX_HOME/proof-libs/fstar"
cd proofs/fstar/extraction
if fstar.exe \
  --include "$HL/rust_primitives" --include "$HL/core" \
  --include "$HAX_HOME/hax-lib/proofs/fstar/extraction" --include . \
  --cache_dir .cache --cache_checked_modules --z3rlimit_factor 8 \
  ${QUERY_STATS:+--query_stats} \
  Verified_ledger.fst > fstar.log 2>&1
then
  echo "VERIFIED (F*): conservation + supply deltas + atomicity for new_ledger/mint/burn/transfer"
else
  sh ../explain_failure.sh
  exit 1
fi
