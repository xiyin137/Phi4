# CLAUDE-to-Codex Systematic Remediation Tracker

Date: 2026-02-27

This tracker converts `claude_to_codex.md` into an execution matrix.
Each line item is actionable, testable, and tied to concrete files/modules.

## Status Legend

- `done`: implemented and verified
- `in_progress`: active implementation
- `planned`: queued with explicit next action
- `blocked`: requires upstream closure or prior work package completion

## Global Issues (Sections 1, 13, 14, 17, 18, 19)

| ID | Issue from `claude_to_codex.md` | Action | Status |
|---|---|---|---|
| CTC-G-01 | Core sorry count reported as `9` is stale | Keep trust audit as source of truth; sync docs in follow-up updates | done |
| CTC-G-02 | Trust guarantees must be continuously enforced | Run `scripts/check_phi4_trust.sh` before each commit | done |
| CTC-G-03 | Upstream OSReconstruction risk is high (`os_to_wightman_full`) | Isolate upstream bridge from core reconstruction logic | done |
| CTC-G-04 | Avoid wrapper-only churn and assumption smuggling | Enforce anti-pattern checks in code review and commit criteria | in_progress |
| CTC-G-05 | Start-of-session operating checklist needed | Follow section-19 checklist as default per cycle | done |

## Architecture/Boundary Issues (Sections 2, 3, 4, 8, 10)

| ID | Issue | Action | Status |
|---|---|---|---|
| CTC-A-01 | Core reconstruction mixed with upstream adapter | Split adapter into `Phi4/ReconstructionUpstream.lean` | done |
| CTC-A-02 | Need reusable infrastructure, not one-off theorem wrappers | Add reusable localized combinatorial lemmas for graph bounds | done |
| CTC-A-03 | Keep model-class surface from expanding | No new model classes unless mathematically distinct obligation | done |
| CTC-A-04 | Preserve compatibility split/recombine pattern | Continue `_of_submodels`/`nonempty_of_data` architecture when grounding; reduced Regularity/Wick interfaces from `InfiniteVolumeLimitModel` to Schwinger+measure subinterfaces, decoupled `ReconstructionLinearGrowthModel` and fixed-parameter Wightman interface endpoints from unnecessary Schwinger package assumptions, trimmed `phi4_satisfies_OS` to OS-core assumptions, split measure-vs-moment data (`InfiniteVolumeMeasureModel` vs `InfiniteVolumeMomentModel`), and made `MeasureOS3Model` purely measure-level | in_progress |

## Work Package Issues (Sections 5 and 9)

### WP1: Interaction Integrability (critical blocker)

| ID | Issue | Action | Status |
|---|---|---|---|
| CTC-WP1-01 | Missing localized graph bound infrastructure | Add `Phi4/FeynmanGraphs/LocalizedBounds.lean` with occupancy/factorial combinatorics | done |
| CTC-WP1-02 | `exp_interaction_Lp` not grounded | Build from semibounded Wick-4 + localized graph bounds + tail/layer-cake chain; weighted occupancy bounds + AE-lower-bound-to-`MemLp` + cutoff-sequence-lower-bound constructors (including eventually-in-`n` AE, variable `Bₙ` with eventual uniform control, and Borel-Cantelli bridges from summable bad-event tails / summable majorants / geometric tails / exponential tails) for weight/integrability models landed | in_progress |

### WP2: Covariance/Boundary/RP grounding

| ID | Issue | Action | Status |
|---|---|---|---|
| CTC-WP2-01 | `FreeCovarianceKernelModel` not constructively instantiated | Develop CLM-to-kernel bridge from existing free-field kernel machinery; constructor scaffolds landed (`freeCovarianceKernelModel_nonempty_of_data`, `freeCovarianceKernelModel_nonempty_of_two_point_kernel`) and reusable free-kernel Bessel/off-diagonal bounds exported in `FreeField.lean` (`freeCovKernel_eq_besselK0` and `K₁` comparison consequences) | in_progress |
| CTC-WP2-02 | Boundary comparison models remain interface-level | Ground `C_D ≤ C ≤ C_N` path in `CovarianceOperators.lean`; constructor scaffolds landed for boundary kernel/comparison/regularity/covariance models, with reusable off-diagonal free-kernel positivity/`K₁` comparison lemmas added | in_progress |

### WP3: Correlation + lattice bridge

| ID | Issue | Action | Status |
|---|---|---|---|
| CTC-WP3-01 | Lattice Griffiths/FKG assumptions remain ungrounded | Develop lattice-to-continuum constructive instances using existing approximation bridges; constructor scaffolds landed for lattice/core correlation interfaces | in_progress |

### WP4: Multiple reflections + infinite volume

| ID | Issue | Action | Status |
|---|---|---|---|
| CTC-WP4-01 | Chessboard / uniform bound still interface-level | Port only non-tautological scratch results and extend with reusable lemmas | planned |
| CTC-WP4-02 | `gap_infiniteVolumeSchwingerModel_nonempty` depends on upstream interfaces | Close via grounded WP1/WP2/WP3 estimates | blocked |

### WP5/WP6: Regularity/OS/Reconstruction closure

| ID | Issue | Action | Status |
|---|---|---|---|
| CTC-WP5-01 | OS1 and E2 packaging still interface-level | Ground once WP1–WP4 dependencies close | blocked |
| CTC-WP6-01 | `WightmanReconstructionModel` upstream theorem path is not axiom-clean | Keep as explicit final interface; do not discharge with `os_to_wightman_full` | done |

## Scratch/Porting Issues (Section 15)

| ID | Issue | Action | Status |
|---|---|---|---|
| CTC-S-01 | Scratch contains candidate lemmas for porting | Port only proofs that materially reduce downstream blocker surface | in_progress |
| CTC-S-02 | Avoid tautological "∃ C" ports | Require new ports to provide reusable/nontrivial bounds or bridge lemmas | done |

## Active Execution Order

1. Execute `CTC-WP1-02`: start `exp_interaction_Lp` closure chain from semibounded Wick-4 plus localized occupancy bounds.
2. Continue `CTC-WP2-01` by proving a concrete CLM-to-kernel bridge lemma (constructor already in place).
3. Continue `CTC-WP3-01` by constructing first lattice GKS-I / monotonicity instances against approximation data.
4. Continue `CTC-S-01` by porting only non-tautological scratch lemmas that reduce WP1/WP2/WP3 blockers.
5. Re-run trust/build/gap checks before each commit.

## Verification Commands

```bash
lake build Phi4
scripts/check_phi4_trust.sh
grep -RIn "^[[:space:]]*sorry\\b" Phi4 --include='*.lean' | grep -v Scratch
rg -n "^class .*Model" Phi4 --glob '*.lean'
```
