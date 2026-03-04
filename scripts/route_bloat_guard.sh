#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

# Baselines captured after bloat-reduction refactor (2026-03-04):
# - class .*Model count: 58
# - theorem .*_nonempty_of_ count: 67
# - interactionWeightModel_nonempty_of_* count: 8
# - interactionIntegrabilityModel_nonempty_of_* count: 2
# - gap_phi4_linear_growth variant count in Reconstruction/Part1Core.lean: 3
# - Interaction/Part2 top-level theorem count: 8
# - Reconstruction/Part2 top-level theorem count: 1
# - Reconstruction/Part2 *_explicit* theorem count: 0
# - ModelBundle top-level theorem count: 0
# - Reconstruction/Part3 top-level theorem count: 5
# - Reconstruction/Part3 phi4_wightman_exists* theorem count: 4
# - InfiniteVolumeLimit/Part1 top-level theorem count: 24
# - InfiniteVolumeLimit/Part1 schwingerTwo_* theorem count: 1
# - InfiniteVolumeLimit/Part1 infinite_volume_schwinger_exists_*_of_* theorem count: 4
# - InfiniteVolumeLimit/Part2 top-level theorem count: 11
# - InfiniteVolumeLimit/Part3 top-level theorem count: 16
# - CorrelationInequalities top-level theorem count: 56
MAX_MODEL_CLASSES=58
MAX_NONEMPTY_CONSTRUCTORS=67
MAX_WEIGHT_ROUTES=8
MAX_INTEGRABILITY_ROUTES=2
MAX_LINEAR_GROWTH_ROUTES=3
MAX_INTERACTION_PART2_THEOREMS=8
MAX_RECON_PART2_THEOREMS=1
MAX_RECON_PART2_EXPLICIT_ROUTES=0
MAX_MODELBUNDLE_THEOREMS=0
MAX_RECON_PART3_THEOREMS=5
MAX_RECON_PART3_WIGHTMAN_ROUTES=4
MAX_IVL_PART1_THEOREMS=24
MAX_IVL_PART1_SCHWINGERTWO_ROUTES=1
MAX_IVL_PART1_EXISTS_ROUTES=4
MAX_IVL_PART2_THEOREMS=11
MAX_IVL_PART3_THEOREMS=16
MAX_CORRELATION_THEOREMS=56

model_classes="$( (rg -n '^class .*Model' Phi4 --glob '*.lean' || true) | wc -l | tr -d ' ' )"
nonempty_ctors="$( (rg -n '^theorem[[:space:]]+.*_nonempty_of_' Phi4 --glob '*.lean' || true) | wc -l | tr -d ' ' )"
weight_routes="$( (rg -n '^theorem[[:space:]]+interactionWeightModel_nonempty_of_' Phi4/Interaction --glob '*.lean' || true) | wc -l | tr -d ' ' )"
integrability_routes="$( (rg -n '^theorem[[:space:]]+interactionIntegrabilityModel_nonempty_of_' Phi4/Interaction --glob '*.lean' || true) | wc -l | tr -d ' ' )"
linear_growth_routes="$( (rg -n '^theorem[[:space:]]+gap_phi4_linear_growth(_of_[A-Za-z0-9_]+)?' Phi4/Reconstruction/Part1Core.lean || true) | wc -l | tr -d ' ' )"
interaction_part2_theorem_count="$(rg -n '^theorem[[:space:]]' Phi4/Interaction/Part2.lean | wc -l | tr -d ' ')"
part2_theorem_count="$(rg -n '^theorem[[:space:]]' Phi4/Reconstruction/Part2.lean | wc -l | tr -d ' ')"
part2_explicit_routes="$( (rg -n '^theorem[[:space:]]+.*_explicit(_|$)' Phi4/Reconstruction/Part2.lean || true) | wc -l | tr -d ' ' )"
modelbundle_theorem_count="$( (rg -n '^theorem[[:space:]]' Phi4/ModelBundle.lean || true) | wc -l | tr -d ' ' )"
ivl_part1_theorem_count="$(rg -n '^theorem[[:space:]]' Phi4/InfiniteVolumeLimit/Part1.lean | wc -l | tr -d ' ')"
ivl_part1_schwingerTwo_routes="$( (rg -n '^theorem[[:space:]]+schwingerTwo_' Phi4/InfiniteVolumeLimit/Part1.lean || true) | wc -l | tr -d ' ' )"
ivl_part1_exists_routes="$( (rg -n '^theorem[[:space:]]+infinite_volume_schwinger_exists_.*_of_' Phi4/InfiniteVolumeLimit/Part1.lean || true) | wc -l | tr -d ' ' )"
ivl_part2_theorem_count="$(rg -n '^theorem[[:space:]]' Phi4/InfiniteVolumeLimit/Part2.lean | wc -l | tr -d ' ')"
ivl_part3_theorem_count="$(rg -n '^theorem[[:space:]]' Phi4/InfiniteVolumeLimit/Part3.lean | wc -l | tr -d ' ')"
correlation_theorem_count="$(rg -n '^theorem[[:space:]]' Phi4/CorrelationInequalities.lean | wc -l | tr -d ' ')"
part3_theorem_names="$(
  awk '
  /^[[:space:]]*theorem([[:space:]]|$)/{
    line=$0
    sub(/^[[:space:]]*theorem[[:space:]]*/, "", line)
    if (line != "" && line !~ /^--/) {
      split(line, a, /[^A-Za-z0-9_\047]/)
      if (a[1] != "") print a[1]
      pend=0
    } else {
      pend=1
    }
    next
  }
  pend==1{
    line=$0
    if (line ~ /^[[:space:]]*$/) next
    if (line ~ /^[[:space:]]*\/-/) next
    sub(/^[[:space:]]*/, "", line)
    split(line, a, /[^A-Za-z0-9_\047]/)
    if (a[1] != "") print a[1]
    pend=0
  }' Phi4/Reconstruction/Part3.lean
)"
part3_theorem_count="$(printf '%s\n' "$part3_theorem_names" | sed '/^$/d' | wc -l | tr -d ' ')"
part3_wightman_routes="$(printf '%s\n' "$part3_theorem_names" | (rg '^phi4_wightman_exists' || true) | wc -l | tr -d ' ')"

echo "[route_bloat_guard] class .*Model: $model_classes (max $MAX_MODEL_CLASSES)"
echo "[route_bloat_guard] _nonempty_of_ constructors: $nonempty_ctors (max $MAX_NONEMPTY_CONSTRUCTORS)"
echo "[route_bloat_guard] interactionWeightModel routes: $weight_routes (max $MAX_WEIGHT_ROUTES)"
echo "[route_bloat_guard] interactionIntegrabilityModel routes: $integrability_routes (max $MAX_INTEGRABILITY_ROUTES)"
echo "[route_bloat_guard] gap_phi4_linear_growth routes: $linear_growth_routes (max $MAX_LINEAR_GROWTH_ROUTES)"
echo "[route_bloat_guard] Interaction.Part2 theorem count: $interaction_part2_theorem_count (max $MAX_INTERACTION_PART2_THEOREMS)"
echo "[route_bloat_guard] Reconstruction.Part2 theorem count: $part2_theorem_count (max $MAX_RECON_PART2_THEOREMS)"
echo "[route_bloat_guard] Reconstruction.Part2 *_explicit* theorem count: $part2_explicit_routes (max $MAX_RECON_PART2_EXPLICIT_ROUTES)"
echo "[route_bloat_guard] ModelBundle theorem count: $modelbundle_theorem_count (max $MAX_MODELBUNDLE_THEOREMS)"
echo "[route_bloat_guard] InfiniteVolumeLimit.Part1 theorem count: $ivl_part1_theorem_count (max $MAX_IVL_PART1_THEOREMS)"
echo "[route_bloat_guard] InfiniteVolumeLimit.Part1 schwingerTwo_* routes: $ivl_part1_schwingerTwo_routes (max $MAX_IVL_PART1_SCHWINGERTWO_ROUTES)"
echo "[route_bloat_guard] InfiniteVolumeLimit.Part1 infinite_volume_schwinger_exists_*_of_* routes: $ivl_part1_exists_routes (max $MAX_IVL_PART1_EXISTS_ROUTES)"
echo "[route_bloat_guard] InfiniteVolumeLimit.Part2 theorem count: $ivl_part2_theorem_count (max $MAX_IVL_PART2_THEOREMS)"
echo "[route_bloat_guard] InfiniteVolumeLimit.Part3 theorem count: $ivl_part3_theorem_count (max $MAX_IVL_PART3_THEOREMS)"
echo "[route_bloat_guard] CorrelationInequalities theorem count: $correlation_theorem_count (max $MAX_CORRELATION_THEOREMS)"
echo "[route_bloat_guard] Reconstruction.Part3 theorem count: $part3_theorem_count (max $MAX_RECON_PART3_THEOREMS)"
echo "[route_bloat_guard] Reconstruction.Part3 phi4_wightman_exists* routes: $part3_wightman_routes (max $MAX_RECON_PART3_WIGHTMAN_ROUTES)"

fail=0
if (( model_classes > MAX_MODEL_CLASSES )); then
  echo "[FAIL] Model-class count exceeded baseline." >&2
  fail=1
fi
if (( nonempty_ctors > MAX_NONEMPTY_CONSTRUCTORS )); then
  echo "[FAIL] _nonempty_of_ constructor count exceeded baseline." >&2
  fail=1
fi
if (( weight_routes > MAX_WEIGHT_ROUTES )); then
  echo "[FAIL] interactionWeightModel route count exceeded baseline." >&2
  fail=1
fi
if (( integrability_routes > MAX_INTEGRABILITY_ROUTES )); then
  echo "[FAIL] interactionIntegrabilityModel route count exceeded baseline." >&2
  fail=1
fi
if (( linear_growth_routes > MAX_LINEAR_GROWTH_ROUTES )); then
  echo "[FAIL] gap_phi4_linear_growth route count exceeded baseline." >&2
  fail=1
fi
if (( interaction_part2_theorem_count > MAX_INTERACTION_PART2_THEOREMS )); then
  echo "[FAIL] Interaction.Part2 theorem count exceeded baseline." >&2
  fail=1
fi
if (( part2_theorem_count > MAX_RECON_PART2_THEOREMS )); then
  echo "[FAIL] Reconstruction.Part2 theorem count exceeded baseline." >&2
  fail=1
fi
if (( part2_explicit_routes > MAX_RECON_PART2_EXPLICIT_ROUTES )); then
  echo "[FAIL] Reconstruction.Part2 explicit-route count exceeded baseline." >&2
  fail=1
fi
if (( modelbundle_theorem_count > MAX_MODELBUNDLE_THEOREMS )); then
  echo "[FAIL] ModelBundle theorem count exceeded baseline." >&2
  fail=1
fi
if (( ivl_part1_theorem_count > MAX_IVL_PART1_THEOREMS )); then
  echo "[FAIL] InfiniteVolumeLimit.Part1 theorem count exceeded baseline." >&2
  fail=1
fi
if (( ivl_part1_schwingerTwo_routes > MAX_IVL_PART1_SCHWINGERTWO_ROUTES )); then
  echo "[FAIL] InfiniteVolumeLimit.Part1 schwingerTwo route count exceeded baseline." >&2
  fail=1
fi
if (( ivl_part1_exists_routes > MAX_IVL_PART1_EXISTS_ROUTES )); then
  echo "[FAIL] InfiniteVolumeLimit.Part1 existence-route count exceeded baseline." >&2
  fail=1
fi
if (( ivl_part2_theorem_count > MAX_IVL_PART2_THEOREMS )); then
  echo "[FAIL] InfiniteVolumeLimit.Part2 theorem count exceeded baseline." >&2
  fail=1
fi
if (( ivl_part3_theorem_count > MAX_IVL_PART3_THEOREMS )); then
  echo "[FAIL] InfiniteVolumeLimit.Part3 theorem count exceeded baseline." >&2
  fail=1
fi
if (( correlation_theorem_count > MAX_CORRELATION_THEOREMS )); then
  echo "[FAIL] CorrelationInequalities theorem count exceeded baseline." >&2
  fail=1
fi
if (( part3_theorem_count > MAX_RECON_PART3_THEOREMS )); then
  echo "[FAIL] Reconstruction.Part3 theorem count exceeded baseline." >&2
  fail=1
fi
if (( part3_wightman_routes > MAX_RECON_PART3_WIGHTMAN_ROUTES )); then
  echo "[FAIL] Reconstruction.Part3 phi4_wightman_exists route count exceeded baseline." >&2
  fail=1
fi

if (( fail != 0 )); then
  exit 1
fi

echo "[route_bloat_guard] OK"
