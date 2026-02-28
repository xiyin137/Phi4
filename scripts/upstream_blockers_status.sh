#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SCAN_SCRIPT="$ROOT_DIR/scripts/upstream_blockers_scan.sh"
STATUS_FILE="$ROOT_DIR/docs/upstream_blockers/status.tsv"
QUEUE_FILE="$ROOT_DIR/docs/upstream_blockers/generated/declaration_queue.tsv"

valid_status() {
  case "$1" in
    open|in_progress|blocked|done) return 0 ;;
    *) return 1 ;;
  esac
}

usage() {
  cat <<'EOF'
Usage:
  scripts/upstream_blockers_status.sh list [status] [limit]
  scripts/upstream_blockers_status.sh stats
  scripts/upstream_blockers_status.sh set <file> <kind> <name> <status> [owner|-] [note...|-]
  scripts/upstream_blockers_status.sh claim-next <owner> [count]

Examples:
  scripts/upstream_blockers_status.sh list open 15
  scripts/upstream_blockers_status.sh set "Wightman/WightmanAxioms.lean" def wickRotatePoint in_progress codex
  scripts/upstream_blockers_status.sh set "vNA/KMS.lean" theorem modular_state_is_kms blocked codex "needs bridge lemma"
  scripts/upstream_blockers_status.sh claim-next codex 2
EOF
}

ensure_generated() {
  "$SCAN_SCRIPT" >/dev/null
}

set_one_status() {
  local file="$1"
  local kind="$2"
  local name="$3"
  local new_status="$4"
  local owner_set="$5"
  local owner="$6"
  local note_set="$7"
  local note="$8"
  local date_now
  date_now="$(date +%F)"

  local tmp
  tmp="$(mktemp "${TMPDIR:-/tmp}/upstream_blocker_status.XXXXXX")"

  set +e
  awk -F'\t' -v OFS='\t' \
      -v file="$file" -v kind="$kind" -v name="$name" \
      -v newStatus="$new_status" -v dateNow="$date_now" \
      -v ownerSet="$owner_set" -v owner="$owner" \
      -v noteSet="$note_set" -v note="$note" '
  NR == 1 {
    print
    next
  }
  {
    if ($1 == file && $2 == kind && $3 == name) {
      found = 1
      $4 = newStatus
      $6 = dateNow
      if (ownerSet == 1) {
        $5 = owner
      }
      if (noteSet == 1) {
        $7 = note
      }
    }
    print
  }
  END {
    if (!found) {
      exit 2
    }
  }
  ' "$STATUS_FILE" >"$tmp"
  local rc=$?
  set -e

  if [[ $rc -ne 0 ]]; then
    rm -f "$tmp"
    if [[ $rc -eq 2 ]]; then
      echo "[FAIL] Declaration not found in status file:" >&2
      echo "       file=$file kind=$kind name=$name" >&2
      return 2
    fi
    echo "[FAIL] Unable to update status file." >&2
    return "$rc"
  fi

  mv "$tmp" "$STATUS_FILE"
}

cmd_list() {
  local filter_status="${1:-all}"
  local limit="${2:-20}"

  if [[ "$filter_status" != "all" ]] && ! valid_status "$filter_status"; then
    echo "[FAIL] Invalid status '$filter_status' for list." >&2
    exit 1
  fi
  if ! [[ "$limit" =~ ^[0-9]+$ ]] || [[ "$limit" -le 0 ]]; then
    echo "[FAIL] Limit must be a positive integer." >&2
    exit 1
  fi

  ensure_generated

  printf "score\tstatus\tfile\tkind\tname\tsorry_count\treverse_importers\towner\n"
  awk -F'\t' -v want="$filter_status" '
    want == "all" || $2 == want {
      owner = ($3 == "" ? "-" : $3)
      printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n", $1, $2, $4, $5, $6, $8, $9, owner
    }
  ' "$QUEUE_FILE" | sed -n "1,${limit}p"
}

cmd_stats() {
  ensure_generated
  awk -F'\t' '
    NR == 1 { next }
    { c[$4]++ }
    END {
      printf "open=%d in_progress=%d blocked=%d done=%d\n",
        c["open"] + 0, c["in_progress"] + 0, c["blocked"] + 0, c["done"] + 0
    }
  ' "$STATUS_FILE"
}

cmd_set() {
  if [[ $# -lt 4 ]]; then
    usage
    exit 1
  fi
  local file="$1"
  local kind="$2"
  local name="$3"
  local new_status="$4"
  shift 4

  if ! valid_status "$new_status"; then
    echo "[FAIL] Invalid status '$new_status'." >&2
    exit 1
  fi

  ensure_generated

  local owner_set=0
  local owner=""
  local note_set=0
  local note=""

  if [[ $# -ge 1 ]]; then
    owner_set=1
    owner="$1"
    shift
    if [[ "$owner" == "-" ]]; then
      owner=""
    fi
  fi
  if [[ $# -ge 1 ]]; then
    note_set=1
    note="$*"
    if [[ "$note" == "-" ]]; then
      note=""
    fi
  fi

  set_one_status "$file" "$kind" "$name" "$new_status" "$owner_set" "$owner" "$note_set" "$note"
  ensure_generated
  echo "[OK] Updated: $file $kind $name -> $new_status"
}

cmd_claim_next() {
  if [[ $# -lt 1 ]]; then
    usage
    exit 1
  fi

  local owner="$1"
  local count="${2:-1}"
  if ! [[ "$count" =~ ^[0-9]+$ ]] || [[ "$count" -le 0 ]]; then
    echo "[FAIL] count must be a positive integer." >&2
    exit 1
  fi

  ensure_generated

  local picked
  picked="$(mktemp "${TMPDIR:-/tmp}/upstream_blockers_claim.XXXXXX")"
  awk -F'\t' '$2 == "open" { print $4 "\t" $5 "\t" $6 }' "$QUEUE_FILE" | sed -n "1,${count}p" > "$picked"

  if [[ ! -s "$picked" ]]; then
    rm -f "$picked"
    echo "[INFO] No open declarations available to claim."
    exit 0
  fi

  while IFS=$'\t' read -r file kind name; do
    set_one_status "$file" "$kind" "$name" "in_progress" "1" "$owner" "0" ""
    echo "[OK] Claimed: $file $kind $name"
  done < "$picked"
  rm -f "$picked"

  ensure_generated
}

main() {
  if [[ $# -lt 1 ]]; then
    usage
    exit 1
  fi

  local cmd="$1"
  shift

  case "$cmd" in
    list) cmd_list "$@" ;;
    stats) cmd_stats "$@" ;;
    set) cmd_set "$@" ;;
    claim-next) cmd_claim_next "$@" ;;
    -h|--help|help) usage ;;
    *)
      echo "[FAIL] Unknown command: $cmd" >&2
      usage
      exit 1
      ;;
  esac
}

main "$@"
