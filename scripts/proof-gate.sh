#!/usr/bin/env bash
# Proof gate: no escape hatches in the proofs, every statement is ascribed
# (Check.lean compiles), and only the standard axioms are used.
set -euo pipefail
cd "$(dirname "$0")/../domain"

bad='sorry|axiom|native_decide|unsafe|implemented_by|@\[extern|opaque'
if grep -nE "$bad" Ledger/Proofs.lean Ledger/Statements.lean Ledger/Defs.lean; then
  echo "proof-gate: FAIL (forbidden construct above)"; exit 1
fi

lake build Ledger >/dev/null
out=$(lake env lean Ledger/Check.lean)   # fails if any `example` does not typecheck
echo "$out"
n=$(echo "$out" | grep -c "axioms\|does not depend")
[ "$n" -ge 7 ] || { echo "proof-gate: FAIL (expected >=7 axiom reports, got $n)"; exit 1; }
if echo "$out" | grep "depends on axioms" | sed 's/.*\[//; s/\]//' | tr ',' '\n' \
   | sed 's/ //g' | grep -vxE 'propext|Classical.choice|Quot.sound|'; then
  echo "proof-gate: FAIL (non-standard axiom above)"; exit 1
fi
echo "proof-gate: PASS"
