#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SCAN_SCRIPT="$ROOT_DIR/scripts/upstream_blockers_scan.sh"
QUEUE_FILE="$ROOT_DIR/docs/upstream_blockers/generated/declaration_queue.tsv"
OSR_DIR="$ROOT_DIR/.lake/packages/OSReconstruction/OSReconstruction"
PROMPT_DIR="$ROOT_DIR/docs/upstream_blockers/generated/prompts"

usage() {
  cat <<'USAGE'
Usage:
  scripts/upstream_blockers_prompt.sh <file> <kind> <name> [output_file]

Example:
  scripts/upstream_blockers_prompt.sh \
    "Wightman/Reconstruction/WickRotation/OSToWightman.lean" \
    theorem full_analytic_continuation
USAGE
}

if [[ $# -lt 3 ]]; then
  usage
  exit 1
fi

file="$1"
kind="$2"
name="$3"
output_file="${4:-}"

"$SCAN_SCRIPT" >/dev/null

if [[ ! -f "$QUEUE_FILE" ]]; then
  echo "[FAIL] Missing queue file: $QUEUE_FILE" >&2
  exit 1
fi

row="$(awk -F'\t' -v file="$file" -v kind="$kind" -v name="$name" '
  $4 == file && $5 == kind && $6 == name {
    printf "%s\037%s\037%s\037%s\037%s\037%s\037%s\037%s\037%s\037%s\037%s\n",
      $1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11
    exit
  }
' "$QUEUE_FILE")"

if [[ -z "$row" ]]; then
  echo "[FAIL] Declaration not found in queue: file=$file kind=$kind name=$name" >&2
  exit 1
fi

IFS=$'\037' read -r score status owner row_file row_kind row_name decl_line sorry_count reverse_importers last_update note <<< "$row"

src_file="$OSR_DIR/$row_file"
if [[ ! -f "$src_file" ]]; then
  echo "[FAIL] Source file not found: $src_file" >&2
  exit 1
fi

module="${row_file%.lean}"
module="OSReconstruction.${module//\//.}"

decl_snippet="$(awk -v start="$decl_line" '
  NR < start { next }
  NR >= start {
    print
    if ($0 ~ /:= *by([[:space:]]|$)/) exit
    if ($0 ~ /^[[:space:]]*by([[:space:]]|$)/) exit
    if ($0 ~ /:= *sorry([[:space:]]|$)/) exit
    if (NR >= start + 60) exit
  }
' "$src_file")"

if [[ -z "$decl_snippet" ]]; then
  decl_snippet="<unable to extract declaration snippet>"
fi

mkdir -p "$PROMPT_DIR"
if [[ -z "$output_file" ]]; then
  safe_file="${row_file//\//__}"
  safe_file="${safe_file//./_}"
  safe_name="${row_name//\//__}"
  output_file="$PROMPT_DIR/${safe_file}__${row_kind}__${safe_name}.txt"
fi

cat > "$output_file" <<EOF_PROMPT
You are assisting with a focused coding/proof blocker.

Task:
- Primary goal: Close upstream blocker ${row_kind}:${row_name} without placeholders.
- Current blocker: Declaration currently contains 'sorry' (score=${score}, status=${status}, sorry_count=${sorry_count}, reverse_importers=${reverse_importers}).

Repository context:
- Language/toolchain: Lean 4 + Mathlib
- File(s): ${src_file}
- Target declaration: ${row_kind} ${row_name}

Current local context:
- Relevant hypotheses/locals:

a) Declaration snippet (from ${row_file}:${decl_line})
${decl_snippet}

b) Build target
- lake build ${module}

What already failed:
1) <ATTEMPT_1 + error/result>
2) <ATTEMPT_2 + error/result>

Constraints:
- No axioms/placeholders/weakened theorem statements.
- Keep existing architecture and imports unless necessary.
- Prefer reusable infrastructure lemmas over brittle one-off hacks.

Request:
1) Propose 2-3 concrete solution paths, ranked by feasibility.
2) For the top path, give exact code-level steps.
3) Point out likely type mismatches or missing bridge lemmas.
4) If statement looks false/underdetermined, provide a minimal counterexample strategy or corrected intermediate lemma.
5) Keep output actionable and concise.
EOF_PROMPT

echo "[OK] Prompt written: $output_file"
