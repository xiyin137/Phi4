# Phi4 Audit Notes

Date: 2026-03-10

## Main vs Simplified Branch Review

The `simplified` branch was reviewed before any salvage back to `main`.

### Safe material imported into `main`

1. clearer documentation for `limsup`-based staging definitions,
2. explicit bridge lemmas from `limsup` definitions to ordinary limits under convergence,
3. explicit theorem-level frontier statements for several model-only obligations,
4. corrected status documentation and roadmap framing.

### Material intentionally not imported

The branch also deleted substantive proved mathematics, so it was not suitable
for direct merge. In particular:

1. `Phi4/FeynmanGraphs/LocalizedBounds.lean` was removed even though it contains
   real combinatorial/localized-bound infrastructure,
2. parts of `Phi4/InfiniteVolumeLimit/Part2.lean` and `Part3.lean` with genuine
   cumulant/positivity lemmas were removed,
3. parts of `Phi4/Interaction/Part1Tail.lean` were dropped even though they
   contain real tail/moment infrastructure.

## Current Honest Status

- theorem-level `sorry` in core modules: `21`
- legacy `class/structure .*Model`: `13`
- canonical `gap_*` theorem frontiers: `45`
- `axiom`: `0`
- `def/abbrev := by sorry`: `0`

## Audit Conclusion

`main` is now more honest than it was before the branch comparison, because the
open mathematics is no longer presented as “zero sorry therefore nearly done”.

Recent local cleanup also deleted dead OS/reconstruction bundle classes and the
unused `Phi4ModelBundle` file. The latest pass also removed the internal
infinite-volume recombination classes and dead correlation bridge classes, so
the remaining model-class surface is smaller and closer to the actual live
dependency graph. The current slice also removed `MultipleReflectionModel` from
the infinite-volume limit arguments and surfaced the chessboard estimate itself
as the explicit frontier `gap_hasChessboardEstimate`. More recently, several
WP1 analytic-input obligations were surfaced explicitly in
`Interaction/AnalyticInputs.lean`, which increased the visible frontier count
without changing the no-axiom / no-`def := by sorry` trust boundary.

The latest proof-focused pass also closed `gap_interaction_sq_integrable` and
added quantitative shell infrastructure in `WickProduct.lean`, including:

1. `wickPower_four_step_decomposition`,
2. `rawFieldEval_sub_sq_expectation`,
3. `rawFieldEval_sub_fourth_expectation`.

This means the main WP1 shell-rate blocker is no longer stuck on quartic-Wick
algebra or basic Gaussian moment identities. The remaining obstruction is the
actual covariance-shell analysis behind
`gap_wickPowerStandardSeqShellUpper_spatial_sq_rate`, together with the
Nelson-side leaf frontiers in `Interaction/NelsonBound.lean`.

The latest Nelson-focused pass refined the theorem surface further:

1. `gap_interactionCutoffSubUniformApprox_tendsto_ae` is closed,
2. `gap_interactionCutoffSubUniformApprox_L2` is closed,
3. the remaining hypercontractive Nelson leaf is now attached to
   `gap_finiteWickCylinder_even_moment_comparison` in
   [WickProduct.lean](/Users/xiyin/Phi4/Phi4/WickProduct.lean:722),
4. `gap_interactionCutoffSubUniformApprox_even_moment_comparison` is now a
   derived theorem for the canonical uniform approximant sequence,
5. `gap_interactionCutoff_sub_even_moment_comparison` is derived from the
   canonical approximant sequence rather than from an over-broad generic route.

This is a theorem-surface improvement, not just refactoring. The remaining
Nelson mathematics is now concentrated in:

1. covariance growth,
2. finite Wick-cylinder hypercontractivity, and
3. reference-shell `L²` decay.

The FreeField side was also made more honest:

1. `gap_covariance_eq_kernel` remains the flat-space CLM existence frontier,
2. `gap_uvMollifier_covariance_eq_freeCovKernel` isolates the narrower
   mollifier-family covariance bridge actually used by WP1,
3. `gap_uvMollifier_freeCovKernel_log_growth` isolates the kernel-side
   logarithmic growth estimate.

The project is therefore in a cleaner state than before, but the local proof
that `phi^4_2` satisfies the OS axioms is still not complete. The OS file is
still an assembly layer with explicit OS0/OS2/E2/E3 hypotheses, and the
dominant remaining blockers are the WP1 analytic leafs, the regularity
theorems, and local OS3 reflection positivity.

## Refactor Update

The old monolithic `Interaction/AnalyticInputs.lean` has now been split into:

1. `Interaction/UVInfra.lean`
2. `Interaction/ShellEstimates.lean`
3. `Interaction/NelsonBound.lean`
4. `Interaction/AnalyticInputs.lean` as the thin endpoint orchestrator

This split is build-verified and follows actual proof-program boundaries rather
than arbitrary file size reduction.

The refactor also surfaced two definition-level corrections:

1. `uvMollifier` is now normalized to unit mass in `FreeField.lean`, which is
   necessary for an honest delta-approximation interpretation,
2. `gap_covariance_eq_kernel` now states existence of a flat-space CLM witness
   instead of the false statement that the already-defined harmonic-oscillator
   `freeCovarianceCLM` equals the flat kernel.

But the repository is still not close to completion:

1. several major frontiers are now explicit theorem-level gaps,
2. several OS-side obligations are explicit hypotheses but not yet named local frontiers,
3. WP1 remains the controlling analytic blocker.
