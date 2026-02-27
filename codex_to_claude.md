# Codex -> Claude: Next Proof Workpack

Date: 2026-02-27
Repo: `/Users/xiyin/Phi4`

## Primary Goal (Authoritative)

Formalize Glimm-Jaffe `phi^4_2` in Lean with canonical continuum objects:

1. infinite-volume Schwinger construction,
2. OS axioms (OS0-OS4, weak-coupling OS4 explicit),
3. reconstruction to Wightman.

## Architecture Constraints (Non-Negotiable)

- Continuum definitions are canonical.
- Lattice interfaces are optional proof-transport bridges only.
- No axioms/placeholders/weakened theorem statements.
- A simplified definition is a wrong definition.
- Prefer reusable infrastructure lemmas over brittle wrappers.

## Already Merged (for context)

The previous blocker tasks are now merged on `main`:

- `CorrelationFourPointModel` now has `schwinger_four_monotone`.
- Instance exists:
  `schwingerNMonotoneModel_four_of_correlationFourPoint`.
- Added:
  `infinite_volume_schwinger_exists_four_of_models`,
  `infinite_volume_schwinger_exists_four_of_lattice_models`.
- Lattice iSup two-point convergence theorems now use shifted `(n+1)` sequences
  and no longer require `LatticeGriffithsFirstModel`.

## Current Blocking Direction

Infrastructure is now broad enough. The blocker is proving/constructing concrete
assumption instances, especially 4-point monotonicity data, and then consuming
that to reduce frontier assumptions.

## Requested Work (Proof Tasks)

### Task 1: Constructive source for `schwinger_four_monotone`

Target file:
- `Phi4/CorrelationInequalities.lean` (or scratch first)

Target outcome:
- Provide a mathematically sound derivation path for the new field
  `schwinger_four_monotone`.
- Preferred endpoint is one of:
  1. a theorem that supplies the field from explicit lattice approximation-order
     data (then usable via `correlationFourPointModel_nonempty_of_data`), or
  2. a theorem from continuum assumptions that are strictly weaker/more explicit
     than introducing the field directly.

Constraint:
- Do not claim derivation from GKS-II + Lebowitz sandwich alone.

### Task 2: Concrete instance package for 4-point channel

Target file:
- `Phi4/CorrelationInequalities.lean`

Target outcome:
- Build a reusable constructor theorem (or a minimal class split if needed)
  that makes constructing `CorrelationFourPointModel` instances practical in
  downstream modules, with the new monotonicity requirement explicit and clear.
- If class split is proposed, keep compatibility instance and avoid API breakage.

### Task 3: Push one frontier toward closure

Target file:
- `Phi4/InfiniteVolumeLimit.lean` (preferred) or `Phi4/Regularity.lean`

Target outcome:
- Use the existing generic convergence/existence infrastructure to reduce one
  honest frontier dependency surface (not via workaround).
- Preferred candidates:
  1. strengthen construction path around `gap_infiniteVolumeSchwingerModel_nonempty`,
  2. or reduce assumptions in a currently frontier-adjacent theorem by proving a
     reusable bridge lemma.

## Acceptance Criteria

1. Build succeeds:
   - `lake build Phi4.CorrelationInequalities Phi4.InfiniteVolumeLimit Phi4.Reconstruction Phi4.ModelBundle`
2. Trust checks pass:
   - `scripts/check_phi4_trust.sh`
3. No new theorem-level `sorry`, no new `axiom`.
4. Any new assumptions are explicit, named, and auditable.

## Reporting Back

For each task, report:

1. what was attempted,
2. what was proved/added,
3. what failed and exact blocker,
4. exact declaration names and file locations,
5. compile/check results.
