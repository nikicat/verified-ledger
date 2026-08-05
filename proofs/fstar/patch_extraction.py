#!/usr/bin/env python3
"""Post-extraction patch on the generated Verified_ledger.fst.

One gap between hax@54c34967's F* backend and its proof-libs: calls u64
checked_add/checked_sub models that proof-libs lacks (Core_models.Num
cannot depend on Option without a cycle) — redirected to
Verified_ledger_helpers.
"""
import pathlib

p = pathlib.Path(__file__).parent / "extraction" / "Verified_ledger.fst"
s = p.read_text()

s = s.replace("Core_models.Num.impl_u64__checked_add",
              "Verified_ledger_helpers.checked_add_u64")
s = s.replace("Core_models.Num.impl_u64__checked_sub",
              "Verified_ledger_helpers.checked_sub_u64")

p.write_text(s)
print("extraction patched")
