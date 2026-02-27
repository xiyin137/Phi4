/- 
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Reconstruction
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightman

/-!
# Upstream OS→Wightman Adapter

This module isolates the adapter from the abstract local reconstruction
interface (`WightmanReconstructionModel`) to the upstream
`os_to_wightman_full` theorem from `OSReconstruction`.
-/

noncomputable section

open MeasureTheory Reconstruction

/-- Canonical OS→Wightman reconstruction rule from the upstream
    `os_to_wightman_full` theorem. -/
theorem wightman_reconstruction_of_os_to_wightman (_params : Phi4Params)
    :
    ∀ (OS : OsterwalderSchraderAxioms 1),
      OSLinearGrowthCondition 1 OS →
        ∃ (Wfn : WightmanFunctions 1),
          IsWickRotationPair OS.S Wfn.W := by
  intro OS hlg
  exact os_to_wightman_full OS hlg

/-- Package the upstream OS→Wightman theorem as a
    `WightmanReconstructionModel`. -/
theorem wightmanReconstructionModel_nonempty_of_os_to_wightman
    (params : Phi4Params) :
    Nonempty (WightmanReconstructionModel params) := by
  exact wightmanReconstructionModel_nonempty_of_data params
    (wightman_reconstruction_of_os_to_wightman params)
