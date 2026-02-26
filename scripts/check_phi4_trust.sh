#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

TMP_REPORT="$(mktemp /tmp/phi4_trust_report_XXXXXX)"
TMP_DEF_SORRY="$(mktemp /tmp/phi4_def_sorry_XXXXXX)"
trap 'rm -f "$TMP_REPORT" "$TMP_DEF_SORRY"' EXIT

# 1) Explicit axiom declarations are forbidden.
if rg -n "^\s*axiom\b" Phi4 --glob '*.lean' >"$TMP_REPORT"; then
  echo "[FAIL] Explicit axiom declarations found in Phi4/**/*.lean:" >&2
  cat "$TMP_REPORT" >&2
  exit 1
fi

echo "[OK] No explicit axiom declarations in Phi4/**/*.lean"

# 2) No def/abbrev-level sorry placeholders.
awk '
FNR==1{decl=""}
{
  if ($0 ~ /^[[:space:]]*(theorem|lemma|def|abbrev|instance|example)[[:space:]]/) decl=$0
  if ($0 ~ /^[[:space:]]*sorry([[:space:]]|$)/) {
    if (decl ~ /^[[:space:]]*(def|abbrev)[[:space:]]/) {
      printf "%s:%d:%s\n", FILENAME, FNR, decl
    }
  }
}
' $(find Phi4 -name '*.lean' | sort) >"$TMP_DEF_SORRY"

if [[ -s "$TMP_DEF_SORRY" ]]; then
  echo "[FAIL] def/abbrev declarations using theorem placeholder sorry found:" >&2
  cat "$TMP_DEF_SORRY" >&2
  exit 1
fi

echo "[OK] No def/abbrev := by sorry placeholders"

# 3) Theorem-level sorry is allowed by project policy; report current inventory.
grep -RIn "^[[:space:]]*sorry\\b" Phi4 --include='*.lean' >"$TMP_REPORT" || true
CORE_COUNT="$(grep -v '/Scratch/' "$TMP_REPORT" | wc -l | tr -d ' ')"
SCRATCH_COUNT="$(grep '/Scratch/' "$TMP_REPORT" | wc -l | tr -d ' ')"
TOTAL_COUNT="$(wc -l < "$TMP_REPORT" | tr -d ' ')"

if [[ "$TOTAL_COUNT" -eq 0 ]]; then
  echo "[OK] No theorem-level sorry occurrences"
else
  echo "[INFO] Theorem-level sorry count (core): $CORE_COUNT"
  echo "[INFO] Theorem-level sorry count (scratch): $SCRATCH_COUNT"
  echo "[INFO] Current core sorry locations:"
  grep -v '/Scratch/' "$TMP_REPORT" || true
fi
