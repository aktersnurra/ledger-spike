#!/usr/bin/env bash
# Drift check: regenerate into a temp dir and diff against the checked-in gen/.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
"$root/scripts/gen.sh" "$tmp" >/dev/null
if diff -ru "$root/gen" "$tmp" --exclude=dune; then
  echo "check-gen: PASS (gen/ matches Lean source)"
else
  echo "check-gen: FAIL -- gen/ differs from what Emit.lean produces." >&2
  echo "Run scripts/gen.sh and commit; never hand-edit gen/." >&2
  exit 1
fi
