#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

emit_path=""
if [[ "${1:-}" == "--emit" ]]; then
  if [[ -z "${2:-}" ]]; then
    echo "[nonempty_route_inventory] --emit requires a path" >&2
    exit 1
  fi
  emit_path="$2"
fi

if [[ ! -f docs/frontier_obligations/frontier.tsv ]]; then
  echo "[nonempty_route_inventory] Missing docs/frontier_obligations/frontier.tsv" >&2
  echo "[nonempty_route_inventory] Run: scripts/frontier_report.sh --emit docs/frontier_obligations/frontier.tsv" >&2
  exit 1
fi

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/phi4_nonempty_inventory.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT
TMP_OUT="$TMP_DIR/nonempty_inventory.tsv"

classify() {
  local name="$1"
  local callers="$2"
  if (( callers > 0 )); then
    printf "CONTENTFUL\n"
    return
  fi
  if [[ "$name" =~ _nonempty_of_data$ ]] \
    || [[ "$name" =~ _nonempty_of_models$ ]] \
    || [[ "$name" =~ _nonempty_of_submodel_nonempty$ ]] \
    || [[ "$name" =~ _nonempty_of_lattice$ ]] \
    || [[ "$name" =~ _nonempty_of_latticeTwo$ ]]; then
    printf "PLUMBING\n"
    return
  fi
  printf "CONTENTFUL\n"
}

{
  printf "name\tfile\tline\tcallers\tclassification\n"
  awk -F'\t' 'NR > 1 && $1 == "nonempty_constructor" {print $2 "\t" $3 "\t" $4}' \
    docs/frontier_obligations/frontier.tsv | \
  while IFS=$'\t' read -r name file line; do
    callers="$(rg -n "\\b${name}\\b" Phi4 --glob '*.lean' | awk -F: -v f="$file" -v l="$line" '!( $1 == f && $2 == l ) { c++ } END { print c + 0 }')"
    classification="$(classify "$name" "$callers")"
    printf "%s\t%s\t%s\t%s\t%s\n" "$name" "$file" "$line" "$callers" "$classification"
  done | sort -t$'\t' -k5,5 -k4,4n -k1,1
} > "$TMP_OUT"

if [[ -n "$emit_path" ]]; then
  mkdir -p "$(dirname "$emit_path")"
  cp "$TMP_OUT" "$emit_path"
  echo "[nonempty_route_inventory] wrote: $emit_path"
fi

total="$(awk 'NR>1{c++} END{print c+0}' "$TMP_OUT")"
plumbing="$(awk -F'\t' 'NR>1 && $5=="PLUMBING"{c++} END{print c+0}' "$TMP_OUT")"
contentful="$(awk -F'\t' 'NR>1 && $5=="CONTENTFUL"{c++} END{print c+0}' "$TMP_OUT")"
zero_callers="$(awk -F'\t' 'NR>1 && $4==0{c++} END{print c+0}' "$TMP_OUT")"

echo "[nonempty_route_inventory] total routes: $total"
echo "[nonempty_route_inventory] zero-caller routes: $zero_callers"
echo "[nonempty_route_inventory] classified PLUMBING: $plumbing"
echo "[nonempty_route_inventory] classified CONTENTFUL: $contentful"
echo "[nonempty_route_inventory] top zero-caller PLUMBING routes:"
awk -F'\t' 'NR>1 && $4==0 && $5=="PLUMBING" {print "  " $1 " (" $2 ":" $3 ")"}' "$TMP_OUT" | sed -n '1,20p'
