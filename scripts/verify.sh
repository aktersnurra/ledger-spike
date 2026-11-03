#!/usr/bin/env bash
# One command from a clean clone (needs elan and an OCaml 5 switch with dune + alcotest):
#   scripts/verify.sh
# Lean build + proof gate, generator rejection tests, drift check, OCaml build,
# unit tests, and seeded differential tests against the Lean oracle.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"

echo "== lean: proofs + gate";        scripts/proof-gate.sh
echo "== generator: reject tests";    scripts/test-reject.sh
echo "== drift check";                scripts/check-gen.sh
echo "== lean: oracle";               (cd domain && lake build oracle >/dev/null)
echo "== ocaml: build + tests"
dune build 2>&1
LEDGER_ORACLE="$root/domain/.lake/build/bin/oracle" dune test --force 2>&1
echo "verify: PASS"
