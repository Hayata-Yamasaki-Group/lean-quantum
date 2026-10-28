/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Reduction.Map

namespace HiaiPetz
open scoped MatrixOrder ComplexOrder
open scoped Matrix.Norms.L2Operator
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

/-- The endomorphism of the output-support Euclidean subspace induced by the image `Φ 1` of the
identity. This is the Euclidean-space avatar of the corner-restricted `Φ 1`, used to establish the
strict positivity of the reduced map. -/
noncomputable def outputSupportUnitToEuclideanEnd {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) :
    outputSupportEuclideanSubspace Φ →ₗ[ℂ] outputSupportEuclideanSubspace Φ :=
  outputCornerToEuclideanEndLinearEquiv Φ
    ⟨Φ (1 : Mₙ n), map_mem_outputCorner Φ hPos 1⟩

/-- Evaluating the reduced map at `X` gives the corner model's matrix representation of the corner
element `⟨Φ X, _⟩`. -/
@[simp] theorem outputSupportReducedMap_apply {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (X : Mₙ n) :
    outputSupportReducedMap Φ hPos X =
      (outputSupportMatrixCornerModel Φ).toMat
        ⟨Φ X, map_mem_outputCorner Φ hPos X⟩ := by
  rfl

end HiaiPetz
