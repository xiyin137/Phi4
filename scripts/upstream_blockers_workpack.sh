#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SCAN_SCRIPT="$ROOT_DIR/scripts/upstream_blockers_scan.sh"
PROMPT_SCRIPT="$ROOT_DIR/scripts/upstream_blockers_prompt.sh"
QUEUE_FILE="$ROOT_DIR/docs/upstream_blockers/generated/declaration_queue.tsv"
OUT_FILE="$ROOT_DIR/docs/upstream_blockers/generated/workpack.md"
PROMPT_DIR="$ROOT_DIR/docs/upstream_blockers/generated/prompts"

usage() {
  cat <<'USAGE'
Usage:
  scripts/upstream_blockers_workpack.sh [count] [status]

Defaults:
  count  = 10
  status = open

Examples:
  scripts/upstream_blockers_workpack.sh
  scripts/upstream_blockers_workpack.sh 15 open
  scripts/upstream_blockers_workpack.sh 8 in_progress
USAGE
}

count="${1:-10}"
status_filter="${2:-open}"

case "$status_filter" in
  open|in_progress|blocked|done|all) ;;
  *)
    echo "[FAIL] Invalid status filter: $status_filter" >&2
    usage
    exit 1
    ;;
esac

if ! [[ "$count" =~ ^[0-9]+$ ]] || [[ "$count" -le 0 ]]; then
  echo "[FAIL] count must be a positive integer" >&2
  usage
  exit 1
fi

"$SCAN_SCRIPT" >/dev/null

if [[ ! -f "$QUEUE_FILE" ]]; then
  echo "[FAIL] Missing queue file: $QUEUE_FILE" >&2
  exit 1
fi

mkdir -p "$(dirname "$OUT_FILE")" "$PROMPT_DIR"

selected="$(mktemp "${TMPDIR:-/tmp}/workpack_selected.XXXXXX")"
trap 'rm -f "$selected"' EXIT

awk -F'\t' -v want="$status_filter" '
  want == "all" || $2 == want { print }
' "$QUEUE_FILE" | sed -n "1,${count}p" > "$selected"

selected_count="$(awk 'END { print NR + 0 }' "$selected")"
date_now="$(date +%F)"

{
  echo "# Upstream Blocker Workpack"
  echo
  echo "_Generated: ${date_now}_"
  echo
  printf -- '- Requested count: `%s`\n' "$count"
  printf -- '- Status filter: `%s`\n' "$status_filter"
  printf -- '- Included declarations: `%s`\n' "$selected_count"
  echo
  echo "| Rank | Score | Status | File | Declaration | Sorry Count | Reverse Importers | Owner |"
  echo "|---:|---:|---|---|---|---:|---:|---|"

  rank=0
  while IFS=$'\037' read -r score status owner file kind name decl_line sorry_count reverse_importers last_update note; do
    rank=$((rank + 1))
    owner_disp="${owner:--}"
    printf '| %d | %s | %s | `%s` | `%s:%s` | %s | %s | %s |\n' \
      "$rank" "$score" "$status" "$file" "$kind" "$name" "$sorry_count" "$reverse_importers" "$owner_disp"
  done < <(awk -F'\t' '
    {
      printf "%s\037%s\037%s\037%s\037%s\037%s\037%s\037%s\037%s\037%s\037%s\n",
        $1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11
    }
  ' "$selected")

  echo
  echo "## Action Blocks"

  rank=0
  while IFS=$'\037' read -r score status owner file kind name decl_line sorry_count reverse_importers last_update note; do
    rank=$((rank + 1))
    module="${file%.lean}"
    module="OSReconstruction.${module//\//.}"

    safe_file="${file//\//__}"
    safe_file="${safe_file//./_}"
    safe_name="${name//\//__}"
    prompt_file="$PROMPT_DIR/${safe_file}__${kind}__${safe_name}.txt"

    "$PROMPT_SCRIPT" "$file" "$kind" "$name" "$prompt_file" >/dev/null

    echo "### ${rank}. ${kind}:${name}"
    printf -- '- File: `%s:%s`\n' "$file" "$decl_line"
    printf -- '- Queue: score=`%s`, status=`%s`, sorry_count=`%s`, reverse_importers=`%s`\n' \
      "$score" "$status" "$sorry_count" "$reverse_importers"
    printf -- '- Build target: `lake build %s`\n' "$module"
    printf -- '- Claim command: `scripts/upstream_blockers_status.sh set "%s" %s "%s" in_progress <owner>`\n' \
      "$file" "$kind" "$name"
    printf -- '- Prompt file: `%s`\n' "$prompt_file"
    if [[ -n "$note" ]]; then
      echo "- Note: ${note}"
    fi
    echo
  done < <(awk -F'\t' '
    {
      printf "%s\037%s\037%s\037%s\037%s\037%s\037%s\037%s\037%s\037%s\037%s\n",
        $1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11
    }
  ' "$selected")
} > "$OUT_FILE"

echo "[OK] Workpack written: $OUT_FILE"
