#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

# 1) Project-local trust scan (recursive).
if rg -n "\bsorry\b|\bsorryAx\b|^axiom\b" Phi4 --glob '*.lean' >/tmp/phi4_trust_report.txt; then
  echo "[FAIL] Found forbidden trust markers in Phi4/**/*.lean:" >&2
  cat /tmp/phi4_trust_report.txt >&2
  exit 1
fi

echo "[OK] No sorry/sorryAx/axiom in Phi4/**/*.lean"

# 2) Axiom dependency check for key reconstruction outputs.
TMP_BASE="$(mktemp /tmp/phi4_axiom_check_XXXXXX)"
TMP_LEAN="${TMP_BASE}.lean"
TMP_OUT="${TMP_BASE}.out"

cat > "$TMP_LEAN" <<'LEAN'
import Phi4.Reconstruction
#print axioms phi4_wightman_exists
#print axioms phi4_selfadjoint_fields
#print axioms phi4_locality
#print axioms phi4_lorentz_covariance
#print axioms phi4_unique_vacuum
LEAN

if ! lake env lean "$TMP_LEAN" >"$TMP_OUT" 2>&1; then
  echo "[FAIL] Axiom audit failed to run:" >&2
  cat "$TMP_OUT" >&2
  exit 1
fi

if rg -n "sorryAx" "$TMP_OUT" >/dev/null; then
  echo "[FAIL] sorryAx detected in audited theorem dependencies:" >&2
  cat "$TMP_OUT" >&2
  exit 1
fi

echo "[OK] No sorryAx in audited reconstruction theorems"
