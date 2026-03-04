#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "[quick_gate] Building core frontier modules..."
lake build Phi4.Interaction Phi4.FiniteVolumeMeasure Phi4.InfiniteVolumeLimit Phi4.Regularity Phi4.OSAxioms Phi4.Reconstruction

echo "[quick_gate] Running route-bloat guard..."
scripts/route_bloat_guard.sh

echo "[quick_gate] Completed."
