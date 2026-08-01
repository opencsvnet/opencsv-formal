#!/usr/bin/env bash
# Axiom audit gate for the OpenCSV Lean development.
#
#   scripts/axiom-audit.sh           verify the audit matches axiom-audit.txt
#   scripts/axiom-audit.sh --write   regenerate the baseline (review the diff first!)
#
# The build prints `#print axioms` results for every headline theorem; this
# script normalizes them into one line per theorem and diffs against the
# checked-in baseline. CI runs the check mode: any NEW assumption (or a
# theorem silently gaining one) fails the build unless a human accepts the
# change by regenerating the baseline in the same commit.
set -euo pipefail
cd "$(dirname "$0")/.."

LAKE="${LAKE:-$(command -v lake || echo "$HOME/.elan/bin/lake")}"

AUDIT=$("$LAKE" build 2>&1 | sed -E 's/^info: [^ ]+ //' | grep -v 'ℹ\|Build completed' | awk '
  /^'\''/ { if (e != "") print e; e = $0; next }
  { e = e " " $0 }
  END { if (e != "") print e }' | sed -E 's/ +/ /g; s/\], /],/g' | LC_ALL=C sort)

if [[ "${1:-}" == "--write" ]]; then
  printf '%s\n' "$AUDIT" > axiom-audit.txt
  echo "wrote axiom-audit.txt"
else
  if ! diff <(printf '%s\n' "$AUDIT") axiom-audit.txt; then
    echo >&2 "AXIOM AUDIT CHANGED — the assumption set of the development changed."
    echo >&2 "If this is intentional, review the diff and regenerate with:"
    echo >&2 "  scripts/axiom-audit.sh --write"
    exit 1
  fi
  echo "axiom audit matches baseline ($(wc -l < axiom-audit.txt) theorems)"
fi
