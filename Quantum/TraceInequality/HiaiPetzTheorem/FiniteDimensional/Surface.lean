/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.ConvexBridge

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

/-- Fixed-Hilbert-space convexity bridge in Proposition 5.1.5.  Matrix operator
convexity on every finite-dimensional matrix algebra implies operator midpoint
convexity on the ambient Hilbert space.
Source: Hiai–Yanagi, Proposition 5.1.5. -/
theorem matrixConvexImpliesOperatorMidpointConvex :
    MatrixConvexImpliesOperatorMidpointConvex (ℋ := ℋ) := by
  exact BlockExtensionInternal.matrixConvexImpliesOperatorMidpointConvex_core (ℋ := ℋ)

omit [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Global `AllH` wrapper for the convexity half of Proposition 5.1.5.  It
applies the fixed-space midpoint-convexity bridge independently to each Hilbert
space.
Source: Hiai–Yanagi, Proposition 5.1.5. -/
theorem matrixConvexImpliesAllHOperatorMidpointConvex :
    MatrixConvexImpliesAllHOperatorMidpointConvex.{u} := by
  intro J f hJ hfJ hmat K _ _ _ _ _
  exact matrixConvexImpliesOperatorMidpointConvex (ℋ := K) hJ hfJ hmat

end NormalCFC514

end HansenPedersen
