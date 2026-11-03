#!/usr/bin/env bash
# The generator must refuse anything outside its subset (nonzero exit + message),
# and must not leave generated output behind.
set -uo pipefail
cd "$(dirname "$0")/../domain"
lake build emit Reject >/dev/null || exit 1
fail=0
for d in natSub intDiv firstAmount maxAmt propUse optUse; do
  tmp=$(mktemp -d)
  if msg=$(lake exe emit "$tmp" --module Reject.Bad --root "Reject.$d" 2>&1); then
    echo "FAIL: Reject.$d was accepted"; fail=1
  elif [ -e "$tmp/ledger_gen.ml" ]; then
    echo "FAIL: Reject.$d errored but wrote output"; fail=1
  else
    echo "ok  : Reject.$d rejected -> $(echo "$msg" | head -1 | cut -c1-150)"
  fi
  rm -rf "$tmp"
done
exit $fail
