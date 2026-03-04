#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "[weekly_gate] Running trust audit (timeout 1200s)..."
timeout 1200 scripts/check_phi4_trust.sh

echo "[weekly_gate] Building core frontier modules..."
lake build Phi4.Interaction Phi4.FiniteVolumeMeasure Phi4.InfiniteVolumeLimit Phi4.Regularity Phi4.OSAxioms Phi4.Reconstruction

echo "[weekly_gate] Running route-bloat guard..."
scripts/route_bloat_guard.sh

echo "[weekly_gate] Scanning upstream blockers..."
scripts/upstream_blockers_scan.sh >/dev/null
scripts/upstream_blockers_status.sh stats

echo "[weekly_gate] Completed."
