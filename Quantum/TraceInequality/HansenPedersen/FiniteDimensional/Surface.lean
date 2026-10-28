/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.ConvexBridge
import Quantum.TraceInequality.HansenPedersen.FiniteDimensional.BlockExtensionLimit
import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.Surface

/-!
# Finite-dimensional Hansen-Pedersen surface theorems

This file exposes the public fixed-Hilbert-space and `AllH` forms of the
finite-dimensional bridge.  The proof payload is split across the matrix model,
transport, compression, monotonicity, and convexity modules; this file only
assembles their core theorems into the surface API.

## Main results

* `matrixMonotoneImpliesOperatorMonotone`: fixed-space monotonicity bridge.
* `matrixConvexImpliesOperatorMidpointConvex`: fixed-space midpoint convexity
  bridge.
* `matrixMonotoneConvexImpliesAllHOperator`: bundled global surface result.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1, Proposition 5.1.5.
-/

namespace HansenPedersen

universe u

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

section NormalCFC514

/-- Fixed-Hilbert-space monotonicity bridge in Proposition 5.1.5.  Matrix
monotonicity on every finite-dimensional matrix algebra implies operator
monotonicity on the ambient Hilbert space.
Local API: one-line wrapper; terminology from Hiai–Yanagi, Proposition 5.1.5. -/
theorem matrixMonotoneImpliesOperatorMonotone :
    MatrixMonotoneImpliesOperatorMonotone (ℋ := ℋ) := by
  exact BlockExtensionInternal.matrixMonotoneImpliesOperatorMonotone_core (ℋ := ℋ)

omit [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Global `AllH` wrapper for the monotonicity half of Proposition 5.1.5.  It
applies the fixed-space bridge independently to each Hilbert space.
Source: Hiai–Yanagi, Proposition 5.1.5. -/
theorem matrixMonotoneImpliesAllHOperatorMonotone :
    MatrixMonotoneImpliesAllHOperatorMonotone.{u} := by
  intro J f hJ hfJ hmat K _ _ _ _ _
  exact matrixMonotoneImpliesOperatorMonotone (ℋ := K) hJ hfJ hmat

omit [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Bundled global surface theorem for Proposition 5.1.5.  It returns both the
monotonicity bridge and the midpoint-convexity bridge in their `AllH` forms.
Source: Hiai–Yanagi, Proposition 5.1.5. -/
theorem matrixMonotoneConvexImpliesAllHOperator :
    MatrixMonotoneImpliesAllHOperatorMonotone.{u} ∧
      MatrixConvexImpliesAllHOperatorMidpointConvex.{u} := by
  exact ⟨matrixMonotoneImpliesAllHOperatorMonotone,
    matrixConvexImpliesAllHOperatorMidpointConvex⟩

end NormalCFC514

end HansenPedersen
