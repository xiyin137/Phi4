# Codex -> Claude: Proof Construction Workpack

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
- Prefer reusable infrastructure lemmas over one-off wrappers.

## Current Blocking Direction

We now have generic monotonicity infrastructure in place:

- `SchwingerNMonotoneModel` in `Phi4/CorrelationInequalities.lean`
- `LatticeSchwingerNMonotoneModel` in `Phi4/CorrelationInequalities.lean`
- generic `k`-point convergence/existence paths in `Phi4/InfiniteVolumeLimit.lean`:
  - `schwingerN_tendsto_iSup_of_models`
  - `schwingerN_limit_exists_if_exhaustion_of_models`
  - `infinite_volume_schwinger_exists_k_of_models`
  - `infinite_volume_schwinger_exists_k_of_lattice_models`

The blocker is no longer infrastructure shape; it is constructing concrete
`k > 2` monotonicity instances/proofs and using them to unlock higher-arity
infinite-volume existence.

## Requested Work (Proof Tasks)

### Task 1: Constructive `k=4` monotonicity bridge instance

Target file:
- `Phi4/CorrelationInequalities.lean`

Target outcome:
- Provide a concrete theorem/instance path to obtain
  `SchwingerNMonotoneModel params 4` from auditable assumptions that match the
  current architecture (continuum target, lattice bridge optional).

Preferred shape:
- Either build a concrete `Nonempty (LatticeSchwingerNMonotoneModel params 4)`
  from explicit approximation-order data, then infer
  `SchwingerNMonotoneModel params 4`, or
- build `SchwingerNMonotoneModel params 4` directly from continuum assumptions
  if available.

### Task 2: Use `k=4` monotonicity in IV existence endpoint

Target file:
- `Phi4/InfiniteVolumeLimit.lean`

Target outcome:
- Add a concrete `k=4` infinite-volume existence theorem in interface-sequence form,
  using existing generic infrastructure:
  - expected style:
    `∃ S, Tendsto (fun n => if h : 0 < n then schwingerN ... 4 ... else 0) atTop (nhds S)`

The theorem should route through generic lemmas, not duplicate old two-point proofs.

### Task 3: Reduce lattice assumptions where unnecessary

Target file:
- `Phi4/InfiniteVolumeLimit.lean`

Target outcome:
- Audit lattice-specific two-point convergence signatures and drop any redundant
  assumptions that are no longer needed due to the generic monotonicity framework.
- Specifically check whether `LatticeGriffithsFirstModel` is still required in
  lattice `if`-exhaustion convergence paths, or whether monotonicity+uniform-bound
  routes suffice.

## Acceptance Criteria

1. Build succeeds:
   - `lake build Phi4.CorrelationInequalities Phi4.InfiniteVolumeLimit Phi4.Reconstruction Phi4.ModelBundle`
2. Trust checks pass:
   - `scripts/check_phi4_trust.sh`
3. No new theorem-level `sorry`, no new `axiom`.
4. Documentation/comments make continuum-vs-lattice role explicit where edited.

## Reporting Back

For each task, report:

1. what was attempted,
2. what was proved/added,
3. what failed and exact blocker,
4. exact declaration names and file locations,
5. compile/check results.
