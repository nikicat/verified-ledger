#!/bin/sh
# Turn a failed F* run (fstar.log in extraction/) into a readable report.
# Called by verify.sh; expects to run inside proofs/fstar/extraction.

grep -A2 "^\* Error" fstar.log | head -12

LINE=$(grep "^\* Error" fstar.log | grep -oE "\(([0-9]+)" | head -1 | tr -d "(")
FN=$(awk -v n="${LINE:-0}" 'NR>n{exit} /^let /{name=($2=="rec")?$3:$2} END{print name}' Verified_ledger.fst)
RS=$(grep -n "fn $FN" ../../../src/lib.rs | head -1 | cut -d: -f1)

cat <<MSG

x VERIFICATION FAILED in \`$FN\` (src/lib.rs:${RS:-?})
  The contract of \`$FN\` no longer holds for all inputs.
  To localize which clause broke:
    1. cargo test -- a concrete counterexample is the fastest signal
       (the conservation storm test catches most contract bugs);
    2. bisect the contract: add hax_lib::assert!(<one clause>); lines in
       the body before the return -- each extracts to an individually
       located F* assert, so the first failing one names the clause;
    3. full solver stats: QUERY_STATS=1 ./verify.sh
  Full F* output: proofs/fstar/extraction/fstar.log
MSG
