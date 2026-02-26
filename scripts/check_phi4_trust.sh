#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/phi4_trust.XXXXXX")"
TMP_REPORT="$TMP_DIR/trust_report.txt"
TMP_DEF_SORRY="$TMP_DIR/def_sorry.txt"
TMP_AXIOMS_LEAN="$TMP_DIR/axioms_check.lean"
TMP_AXIOMS_OUT="$TMP_DIR/axioms_out.txt"
trap 'rm -rf "$TMP_DIR"' EXIT

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

# 4) Trusted endpoints must not depend on sorryAx.
TRUSTED_THEOREMS=(
  phi4_satisfies_OS_of_interfaces
  phi4_satisfies_OS_of_bundle
  phi4_wightman_exists_of_interfaces
  phi4_wightman_exists_of_bundle
  phi4_os4_weak_coupling_eventually_small
  phi4_os4_weak_coupling_eventually_small_of_bundle
)

{
  echo "import Phi4.ModelBundle"
  for theorem in "${TRUSTED_THEOREMS[@]}"; do
    echo "#print axioms ${theorem}"
  done
} > "$TMP_AXIOMS_LEAN"

if ! lake env lean "$TMP_AXIOMS_LEAN" > "$TMP_AXIOMS_OUT" 2>&1; then
  echo "[FAIL] Unable to evaluate theorem axiom dependencies:" >&2
  cat "$TMP_AXIOMS_OUT" >&2
  exit 1
fi

collect_axiom_block() {
  local theorem="$1"
  awk -v theorem="$theorem" '
    BEGIN { capture = 0; out = "" }
    {
      if (index($0, sprintf("%c%s%c depends on axioms:", 39, theorem, 39)) == 1) {
        capture = 1
        out = $0
        next
      }
      if (capture && index($0, sprintf("%c", 39)) == 1 && index($0, " depends on axioms:") > 0) {
        capture = 0
      }
      if (capture) {
        out = out " " $0
      }
    }
    END {
      if (out != "") {
        print out
      }
    }
  ' "$TMP_AXIOMS_OUT"
}

for theorem in "${TRUSTED_THEOREMS[@]}"; do
  block="$(collect_axiom_block "$theorem")"
  if [[ -z "$block" ]]; then
    echo "[FAIL] Missing axiom report for theorem '${theorem}'." >&2
    cat "$TMP_AXIOMS_OUT" >&2
    exit 1
  fi
  if [[ "$block" == *"sorryAx"* ]]; then
    echo "[FAIL] Trusted theorem '${theorem}' depends on sorryAx." >&2
    echo "$block" >&2
    exit 1
  fi
done

echo "[OK] Trusted interface/bundle endpoints are free of sorryAx dependencies"
