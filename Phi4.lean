/-
# Phi4 — The φ⁴₂ Quantum Field Theory in Lean 4

This project formalizes the construction of the φ⁴ quantum field theory in 2 Euclidean
dimensions and verifies that it satisfies the Osterwalder-Schrader axioms (and hence,
via the OS reconstruction theorem, the Wightman axioms).

The construction follows Glimm and Jaffe, *Quantum Physics: A Functional Integral
Point of View*, Part II (Chapters 7-12) and Chapter 19.

## Dependencies

- **gaussian-field**: Free Gaussian measure on nuclear Fréchet spaces, Schwartz space
  nuclearity, spectral CLM construction
- **OSreconstruction**: Osterwalder-Schrader axioms, Wightman axioms, reconstruction
  theorem, analytic continuation

## Architecture

```
FreeField ← Defs                           (free Gaussian field dφ_C)
Combinatorics.PerfectMatchings ← Defs      (perfect matching / pairing infrastructure)
GreenFunction.PeriodicKernel ← FreeField   (periodic image-sum kernel infrastructure)
CovarianceOperators ← FreeField            (Dirichlet/Neumann BC, inequalities)
WickProduct ← CovarianceOperators          (:φⁿ: Wick ordering)
FeynmanGraphs ← WickProduct                (Feynman diagram expansion)
             ← Combinatorics.PerfectMatchings
Interaction ← WickProduct                  (V_Λ = λ∫:φ⁴:, e^{-V} ∈ Lᵖ)
FiniteVolumeMeasure ← Interaction          (dμ_Λ = Z⁻¹ e^{-V} dφ_C)
CorrelationInequalities ← FiniteVolume     (GKS, FKG, Lebowitz)
ReflectionPositivity ← FiniteVolume        (OS axiom E2)
MultipleReflections ← ReflectionPositivity (chessboard bounds)
InfiniteVolumeLimit ← MultipleReflections  (monotone + bounded → convergent)
                     ← CorrelationInequalities
Regularity ← InfiniteVolumeLimit           (IBP, OS1 bound)
OSAxioms ← Regularity                      (OS0-OS3 verified)
Reconstruction ← OSAxioms                  (OS → Wightman via reconstruction)
```
-/

import Phi4.Defs
import Phi4.LatticeApproximation
import Phi4.Combinatorics.PerfectMatchings
import Phi4.GreenFunction.PeriodicKernel
import Phi4.FreeField
import Phi4.CovarianceOperators
import Phi4.WickProduct
import Phi4.FeynmanGraphs
import Phi4.Interaction
import Phi4.FiniteVolumeMeasure
import Phi4.CorrelationInequalities
import Phi4.ReflectionPositivity
import Phi4.MultipleReflections
import Phi4.InfiniteVolumeLimit
import Phi4.Regularity
import Phi4.OSAxioms
import Phi4.Reconstruction
