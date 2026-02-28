# Upstream Blocking Proof Workflow

This directory contains infrastructure for systematically unlocking upstream
`OSReconstruction` blocking proofs.

This workflow is secondary to the primary local goal: the Glimm-Jaffe `φ⁴₂`
pipeline (`InfiniteVolume → OS axioms → Wightman reconstruction`) in `Phi4/`.
Use it as dependency-risk management, not as the main project work queue.

## Commands

```bash
# 1) Recompute blocker inventory + queues
scripts/upstream_blockers_scan.sh

# 2) Recompute inventory and sync TODO section
scripts/sync_upstream_blockers_todo.sh

# 3) Operate queue statuses (list / claim / set / stats)
scripts/upstream_blockers_status.sh list open 20
scripts/upstream_blockers_status.sh claim-next codex 2
scripts/upstream_blockers_status.sh set "vNA/KMS.lean" theorem modular_state_is_kms blocked codex "needs bridge lemma"
scripts/upstream_blockers_status.sh stats

# 4) Generate declaration prompt template (Gemini-ready)
scripts/upstream_blockers_prompt.sh "Wightman/Reconstruction/WickRotation/OSToWightman.lean" theorem full_analytic_continuation

# 5) Generate top-N execution workpack (+ prompt files)
scripts/upstream_blockers_workpack.sh 10 open
```

## Generated Outputs

The scan script writes to `docs/upstream_blockers/generated/`:

- `summary.md`: high-level counts and paths.
- `todo_inventory.md`: full markdown block used in `TODO.md`.
- `priority.md`: file-level priority table.
- `next_open.md`: declaration-level queue (excluding `done`).
- `workpack.md`: top-N actionable packet (queue rows + build targets + claim commands).
- `sorry_tokens.tsv`: raw per-`sorry` occurrences.
- `declarations.tsv`: unique declaration blockers with multiplicity.
- `file_stats.tsv`: blocker counts per file.
- `file_priority.tsv`: file-level scoring + reverse importer fanout.
- `declaration_queue.tsv`: declaration queue with status and score.
- `prompts/*.txt`: declaration-specific Gemini consultation prompt templates.

## Status Tracking

Persistent status is stored in:

- `docs/upstream_blockers/status.tsv`

Columns:

- `file`
- `kind`
- `name`
- `status` (`open`, `in_progress`, `blocked`, `done`)
- `owner`
- `last_update` (`YYYY-MM-DD`)
- `note`

`upstream_blockers_scan.sh` refreshes this file against current blockers,
preserving existing status metadata for unchanged declarations.

`upstream_blockers_status.sh` is the supported way to mutate statuses, owners,
and notes while keeping generated queues synchronized.
It automatically updates `last_update` on `set` and `claim-next`.

## Scoring Heuristic

`file_priority.tsv` uses:

- `reverse_importers`: number of files importing the blocker file's module
  (direct fanout in `OSReconstruction`).
- `decl_count`: number of blocked declarations in the file.
- `multi_sorry_decls`: declarations containing multiple `sorry` tokens.
- `token_count`: total `sorry` tokens in the file.

Score:

```text
score = 50 * reverse_importers + 10 * decl_count + 5 * multi_sorry_decls + token_count
```

`declaration_queue.tsv` derives declaration score from file score, with a small
bonus for declarations containing repeated `sorry` tokens.
