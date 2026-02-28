#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OSR_DIR="${OSR_DIR:-$ROOT_DIR/.lake/packages/OSReconstruction/OSReconstruction}"
OUT_DIR="${OUT_DIR:-$ROOT_DIR/docs/upstream_blockers/generated}"
STATUS_FILE="${STATUS_FILE:-$ROOT_DIR/docs/upstream_blockers/status.tsv}"

if [[ ! -d "$OSR_DIR" ]]; then
  echo "[FAIL] OSReconstruction source directory not found: $OSR_DIR" >&2
  exit 1
fi

mkdir -p "$OUT_DIR" "$(dirname "$STATUS_FILE")"

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/upstream_blockers.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

ALL_FILES="$TMP_DIR/all_lean_files.txt"
find "$OSR_DIR" -name '*.lean' | sort > "$ALL_FILES"

if [[ ! -s "$ALL_FILES" ]]; then
  echo "[FAIL] No Lean files found under: $OSR_DIR" >&2
  exit 1
fi

TOKENS="$OUT_DIR/sorry_tokens.tsv"
DECLS="$OUT_DIR/declarations.tsv"
FILE_STATS="$OUT_DIR/file_stats.tsv"
PRIORITY="$OUT_DIR/file_priority.tsv"
QUEUE="$OUT_DIR/declaration_queue.tsv"
TODO_BLOCK="$OUT_DIR/todo_inventory.md"
PRIORITY_MD="$OUT_DIR/priority.md"
NEXT_MD="$OUT_DIR/next_open.md"
SUMMARY_MD="$OUT_DIR/summary.md"

xargs awk -v root="$OSR_DIR/" '
BEGIN { OFS = "\t" }
FNR == 1 { declKind = ""; declName = ""; declLine = 0; blockDepth = 0 }
{
  raw = $0
  code = ""
  scan = raw

  # Strip line comments and nested block comments before token matching.
  while (length(scan) > 0) {
    if (blockDepth > 0) {
      openPos = index(scan, "/-")
      closePos = index(scan, "-/")
      if (closePos == 0) {
        scan = ""
      } else if (openPos > 0 && openPos < closePos) {
        blockDepth++
        scan = substr(scan, openPos + 2)
      } else {
        blockDepth--
        scan = substr(scan, closePos + 2)
      }
    } else {
      linePos = index(scan, "--")
      openPos = index(scan, "/-")
      if (linePos > 0 && (openPos == 0 || linePos < openPos)) {
        code = code substr(scan, 1, linePos - 1)
        scan = ""
      } else if (openPos > 0) {
        code = code substr(scan, 1, openPos - 1)
        blockDepth++
        scan = substr(scan, openPos + 2)
      } else {
        code = code scan
        scan = ""
      }
    }
  }

  work = code
  sub(/^[[:space:]]*/, "", work)
  if (work != "") {
    # Drop leading attribute annotations like @[simp] (possibly repeated).
    while (substr(work, 1, 2) == "@[") {
      closeAttr = index(work, "]")
      if (closeAttr == 0) {
        break
      }
      work = substr(work, closeAttr + 1)
      sub(/^[[:space:]]*/, "", work)
    }

    tokCount = split(work, tok, /[[:space:]]+/)
    declIdx = 0
    for (i = 1; i <= tokCount; i++) {
      if (tok[i] == "theorem" || tok[i] == "lemma" || tok[i] == "def" ||
          tok[i] == "abbrev" || tok[i] == "instance" || tok[i] == "example") {
        declIdx = i
        break
      }
    }

    if (declIdx > 0) {
      kind = tok[declIdx]
      name = "__anonymous__"
      if (declIdx < tokCount) {
        cand = tok[declIdx + 1]
        if (cand !~ /^[:(]/ && cand != "where") {
          name = cand
          sub(/[:()].*$/, "", name)
          if (name == "") {
            name = "__anonymous__"
          }
        }
      }
      declKind = kind
      declName = name
      declLine = FNR
    }
  }

  probe = code
  while (match(probe, /sorry/)) {
    pos = RSTART
    before = (pos == 1) ? " " : substr(probe, pos - 1, 1)
    afterPos = pos + 5
    after = (afterPos > length(probe)) ? " " : substr(probe, afterPos, 1)
    if (before !~ /[A-Za-z0-9_]/ && after !~ /[A-Za-z0-9_]/) {
      file = FILENAME
      sub("^" root, "", file)
      kind = declKind
      name = declName
      dline = declLine
      if (kind == "" || name == "") {
        kind = "unknown"
        name = "__unknown__"
        dline = 0
      }
      print file, FNR, kind, name, dline
    }
    probe = substr(probe, pos + 5)
  }
}
' < "$ALL_FILES" > "$TOKENS"

awk -F'\t' '
BEGIN { OFS = "\t" }
{
  key = $1 FS $3 FS $4 FS $5
  count[key]++
}
END {
  for (k in count) {
    split(k, a, FS)
    print count[k], a[1], a[2], a[3], a[4]
  }
}
' "$TOKENS" | sort -t $'\t' -k2,2 -k3,3 -k4,4 > "$DECLS"

awk -F'\t' '
BEGIN { OFS = "\t" }
{
  file = $2
  tokens[file] += ($1 + 0)
  decls[file] += 1
  if (($1 + 0) > 1) {
    multi[file] += 1
  }
}
END {
  for (f in decls) {
    print f, tokens[f] + 0, decls[f] + 0, multi[f] + 0
  }
}
' "$DECLS" | sort -t $'\t' -k1,1 > "$FILE_STATS"

FILE_MODULES="$TMP_DIR/file_modules.tsv"
awk -F'\t' '
BEGIN { OFS = "\t" }
{
  file = $1
  module = file
  sub(/\.lean$/, "", module)
  gsub(/\//, ".", module)
  module = "OSReconstruction." module
  print file, module
}
' "$FILE_STATS" > "$FILE_MODULES"

REVERSE_IMPORTS="$TMP_DIR/reverse_importers.tsv"
xargs awk -v modules="$FILE_MODULES" '
BEGIN {
  FS = "[[:space:]]+"
  while ((getline < modules) > 0) {
    blocker[$2] = 1
  }
}
$1 == "import" && $2 ~ /^OSReconstruction\./ {
  imported = $2
  if (imported in blocker) {
    key = imported SUBSEP FILENAME
    if (!(key in seen)) {
      seen[key] = 1
      rev[imported]++
    }
  }
}
END {
  for (m in blocker) {
    printf "%s\t%d\n", m, rev[m] + 0
  }
}
' < "$ALL_FILES" | sort -t $'\t' -k1,1 > "$REVERSE_IMPORTS"

FILE_REVERSE="$TMP_DIR/file_reverse.tsv"
awk -F'\t' '
BEGIN { OFS = "\t" }
NR == FNR {
  rev[$1] = $2 + 0
  next
}
{
  print $1, $2, rev[$2] + 0
}
' "$REVERSE_IMPORTS" "$FILE_MODULES" > "$FILE_REVERSE"

awk -F'\t' '
BEGIN { OFS = "\t" }
NR == FNR {
  module[$1] = $2
  rev[$1] = $3 + 0
  next
}
{
  file = $1
  tokenCount = $2 + 0
  declCount = $3 + 0
  multiDecls = $4 + 0
  reverseImporters = rev[file] + 0
  score = (50 * reverseImporters) + (10 * declCount) + (5 * multiDecls) + tokenCount
  print score, reverseImporters, tokenCount, declCount, multiDecls, file, module[file]
}
' "$FILE_REVERSE" "$FILE_STATS" | sort -t $'\t' -k1,1nr -k6,6 > "$PRIORITY"

if [[ -s "$STATUS_FILE" ]]; then
  :
else
  printf "file\tkind\tname\tstatus\towner\tlast_update\tnote\n" > "$STATUS_FILE"
fi

NEW_STATUS="$TMP_DIR/status_new.tsv"
awk -F'\t' '
BEGIN { OFS = "\t" }
NR == FNR {
  if ($1 == "file" || $1 ~ /^#/ || NF < 4) {
    next
  }
  key = $1 FS $2 FS $3
  status[key] = $4
  owner[key] = $5
  updated[key] = $6
  note[key] = $7
  next
}
{
  key = $2 FS $3 FS $4
  if (!(key in seen)) {
    seen[key] = 1
    s = (key in status && status[key] != "") ? status[key] : "open"
    o = (key in owner) ? owner[key] : ""
    u = (key in updated) ? updated[key] : ""
    n = (key in note) ? note[key] : ""
    print $2, $3, $4, s, o, u, n
  }
}
' "$STATUS_FILE" "$DECLS" | sort -t $'\t' -k1,1 -k2,2 -k3,3 > "$NEW_STATUS"

{
  printf "file\tkind\tname\tstatus\towner\tlast_update\tnote\n"
  cat "$NEW_STATUS"
} > "$STATUS_FILE"

QUEUE_UNSORTED="$TMP_DIR/queue_unsorted.tsv"
awk -F'\t' '
BEGIN { OFS = "\t" }
NR == FNR {
  fileScore[$6] = $1 + 0
  fileRev[$6] = $2 + 0
  next
}
NR > FNR && FILENAME ~ /status\.tsv$/ {
  if ($1 == "file" || NF < 4) {
    next
  }
  key = $1 FS $2 FS $3
  status[key] = $4
  owner[key] = $5
  updated[key] = $6
  note[key] = $7
  next
}
{
  sorryCount = $1 + 0
  file = $2
  kind = $3
  name = $4
  declLine = $5 + 0
  key = file FS kind FS name
  s = (key in status && status[key] != "") ? status[key] : "open"
  o = (key in owner) ? owner[key] : ""
  u = (key in updated) ? updated[key] : ""
  n = (key in note) ? note[key] : ""
  score = fileScore[file] + (3 * (sorryCount - 1))
  print score, s, o, file, kind, name, declLine, sorryCount, fileRev[file] + 0, u, n
}
' "$PRIORITY" "$STATUS_FILE" "$DECLS" > "$QUEUE_UNSORTED"

sort -t $'\t' -k1,1nr -k2,2 -k4,4 -k6,6 "$QUEUE_UNSORTED" > "$QUEUE"

TOKEN_TOTAL="$(awk 'END { print NR + 0 }' "$TOKENS")"
DECL_TOTAL="$(awk 'END { print NR + 0 }' "$DECLS")"
FILE_TOTAL="$(awk 'END { print NR + 0 }' "$FILE_STATS")"

OPEN_TOTAL="$(awk -F'\t' '$2 == "open" { c++ } END { print c + 0 }' "$QUEUE")"
IN_PROGRESS_TOTAL="$(awk -F'\t' '$2 == "in_progress" { c++ } END { print c + 0 }' "$QUEUE")"
BLOCKED_TOTAL="$(awk -F'\t' '$2 == "blocked" { c++ } END { print c + 0 }' "$QUEUE")"
DONE_TOTAL="$(awk -F'\t' '$2 == "done" { c++ } END { print c + 0 }' "$QUEUE")"

GEN_DATE="$(date +%F)"

awk -F'\t' -v tokenTotal="$TOKEN_TOTAL" -v declTotal="$DECL_TOTAL" -v fileTotal="$FILE_TOTAL" \
    -v openTotal="$OPEN_TOTAL" -v inProgressTotal="$IN_PROGRESS_TOTAL" \
    -v blockedTotal="$BLOCKED_TOTAL" -v doneTotal="$DONE_TOTAL" \
    -v generatedOn="$GEN_DATE" '
BEGIN {
  print "_Generated: " generatedOn "_"
  print ""
  print "Generated from `.lake/packages/OSReconstruction/OSReconstruction/**/*.lean` by mapping each `sorry` token to its enclosing declaration."
  print ""
  print "- Total `sorry` tokens: `" tokenTotal "`."
  print "- Unique blocking declarations: `" declTotal "` across `" fileTotal "` files."
  print "- Queue status counts: `open=" openTotal "`, `in_progress=" inProgressTotal "`, `blocked=" blockedTotal "`, `done=" doneTotal "`."
  print "- Entries marked `(xN)` contain multiple `sorry` tokens in one declaration."
  print ""
  print "Top file priorities (score/reverse-importers/declarations/tokens):"
}
NR <= 10 {
  printf "- `%s`: `%d / %d / %d / %d`\n", $6, $1, $2, $4, $3
}
' "$PRIORITY" > "$TODO_BLOCK"

printf "\n" >> "$TODO_BLOCK"

awk -F'\t' '
BEGIN { OFS = "\t" }
NR == FNR {
  score[$6] = $1 + 0
  rev[$6] = $2 + 0
  tok[$6] = $3 + 0
  dec[$6] = $4 + 0
  next
}
{
  file = $2
  if (file != prev) {
    if (sectionCount > 0) {
      print ""
    }
    printf "### `%s` (priority `%d`, reverse importers `%d`, declarations `%d`, sorry tokens `%d`)\n", file, score[file], rev[file], dec[file], tok[file]
    sectionCount++
    prev = file
  }
  if (($1 + 0) > 1) {
    printf "- `%s:%s` (x%d)\n", $3, $4, $1
  } else {
    printf "- `%s:%s`\n", $3, $4
  }
}
' "$PRIORITY" "$DECLS" >> "$TODO_BLOCK"

{
  echo "# Upstream Blocking Proof Priority Queue"
  echo
  echo "_Generated: ${GEN_DATE}_"
  echo
  echo "| Score | Reverse Importers | Declarations | Sorry Tokens | Multi-sorry Decls | File |"
  echo "|---:|---:|---:|---:|---:|---|"
  awk -F'\t' '{ printf "| %d | %d | %d | %d | %d | `%s` |\n", $1, $2, $4, $3, $5, $6 }' "$PRIORITY"
} > "$PRIORITY_MD"

{
  echo "# Next Open Blocking Declarations"
  echo
  echo "_Generated: ${GEN_DATE}_"
  echo
  echo "| Score | Status | File | Declaration | Sorry Count | Reverse Importers | Owner |"
  echo "|---:|---|---|---|---:|---:|---|"
  awk -F'\t' '$2 != "done" { printf "| %d | %s | `%s` | `%s:%s` | %d | %d | %s |\n", $1, $2, $4, $5, $6, $8, $9, ($3 == "" ? "-" : $3) }' "$QUEUE" | sed -n '1,60p'
} > "$NEXT_MD"

{
  echo "# Upstream Blocking Proof Summary"
  echo
  echo "_Generated: ${GEN_DATE}_"
  echo
  echo "- Source tree: $OSR_DIR"
  echo "- Total sorry tokens: $TOKEN_TOTAL"
  echo "- Unique blocking declarations: $DECL_TOTAL"
  echo "- Files with blockers: $FILE_TOTAL"
  echo "- Queue status: open=$OPEN_TOTAL, in_progress=$IN_PROGRESS_TOTAL, blocked=$BLOCKED_TOTAL, done=$DONE_TOTAL"
  echo "- Status file: $STATUS_FILE"
  echo "- Priority queue: $PRIORITY_MD"
  echo "- Declaration queue: $QUEUE"
} > "$SUMMARY_MD"

echo "[OK] Upstream blocker inventory generated:"
echo "  - $SUMMARY_MD"
echo "  - $TODO_BLOCK"
echo "  - $PRIORITY_MD"
echo "  - $NEXT_MD"
echo "  - $STATUS_FILE"
