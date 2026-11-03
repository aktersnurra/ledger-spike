#!/usr/bin/env bash
# Regenerate gen/ from the Lean source. Never hand-edit gen/.
set -euo pipefail
cd "$(dirname "$0")/../domain"
# emit imports Ledger.Defs only at run time, so lake does not know to rebuild it:
# build the library explicitly or the generator reads a stale .olean.
lake build Ledger emit >/dev/null
lake exe emit "${1:-../gen}"
