#!/usr/bin/env bash
# Regenerate gen/ from the Lean source. Never hand-edit gen/.
set -euo pipefail
cd "$(dirname "$0")/../domain"
lake build emit >/dev/null
lake exe emit "${1:-../gen}"
