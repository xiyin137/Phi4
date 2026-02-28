#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TODO_FILE="${TODO_FILE:-$ROOT_DIR/TODO.md}"
BEGIN_MARK="<!-- BEGIN_UPSTREAM_BLOCKERS -->"
END_MARK="<!-- END_UPSTREAM_BLOCKERS -->"

"$ROOT_DIR/scripts/upstream_blockers_scan.sh"

TODO_BLOCK="$ROOT_DIR/docs/upstream_blockers/generated/todo_inventory.md"
if [[ ! -f "$TODO_BLOCK" ]]; then
  echo "[FAIL] Generated TODO block not found: $TODO_BLOCK" >&2
  exit 1
fi

if ! grep -q "^${BEGIN_MARK}$" "$TODO_FILE"; then
  TMP_INSERT="$(mktemp "${TMPDIR:-/tmp}/todo_insert.XXXXXX")"
  if grep -q "^## Upstream Blocking Proof Inventory" "$TODO_FILE"; then
    awk -v begin="$BEGIN_MARK" -v end="$END_MARK" '
    BEGIN { inserted = 0; skipping = 0 }
    /^## Upstream Blocking Proof Inventory/ && inserted == 0 {
      print "## Upstream Blocking Proof Inventory (auto-generated)"
      print ""
      print begin
      print end
      inserted = 1
      skipping = 1
      next
    }
    skipping == 1 && /^## / {
      skipping = 0
    }
    skipping == 0 {
      print
    }
    END {
      if (inserted == 0) {
        print ""
        print "## Upstream Blocking Proof Inventory (auto-generated)"
        print ""
        print begin
        print end
      }
    }
    ' "$TODO_FILE" > "$TMP_INSERT"
  else
    awk -v begin="$BEGIN_MARK" -v end="$END_MARK" '
    BEGIN { inserted = 0 }
    /^## Risk Register$/ && inserted == 0 {
      print "## Upstream Blocking Proof Inventory (auto-generated)"
      print ""
      print begin
      print end
      print ""
      inserted = 1
    }
    { print }
    END {
      if (inserted == 0) {
        print ""
        print "## Upstream Blocking Proof Inventory (auto-generated)"
        print ""
        print begin
        print end
      }
    }
    ' "$TODO_FILE" > "$TMP_INSERT"
  fi
  mv "$TMP_INSERT" "$TODO_FILE"
fi

TMP_OUT="$(mktemp "${TMPDIR:-/tmp}/todo_sync.XXXXXX")"
awk -v begin="$BEGIN_MARK" -v end="$END_MARK" -v block="$TODO_BLOCK" '
$0 == begin {
  print
  while ((getline line < block) > 0) {
    print line
  }
  inblock = 1
  next
}
$0 == end {
  inblock = 0
  print
  next
}
!inblock {
  print
}
' "$TODO_FILE" > "$TMP_OUT"

mv "$TMP_OUT" "$TODO_FILE"

echo "[OK] TODO blocker inventory synced: $TODO_FILE"
