/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.OutputSupportDPI.SupportCorners
import Quantum.TraceInequality.HansenPedersen.Model.MatrixCorner
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.OutputSupportDPI.CornerModels

/-!
# Output-support corner models

This module contains the orthonormal Euclidean corner model and Hilbert--Schmidt
transport API for the output-support stage of Hiai--Petz 6.2.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace
  instOutputSupportHSOpCStarAlgebra
  instOutputSupportHSOpStarRing
  instOutputSupportHSOpComplexAlgebra
  instOutputSupportHSOpNormedAlgebra
  instOutputSupportHSOpPartialOrder
  instOutputSupportHSOpStarOrderedRing
  instOutputSupportHSOpNonnegSpectrumClass
  instOutputSupportHSOpComplexCFC
  instOutputSupportHSOpRealCFC
  outputSupportBridgeMatrixNormedAddCommGroup
  outputSupportBridgeMatrixNormedSpace
  outputSupportBridgeMatrixInnerProductSpace
  outputSupportBridgeMatrixCompleteSpace
  outputSupportBridgeMatrixFiniteDimensional

noncomputable section

/-! ### Matrix Corner Models and Hilbert-Schmidt Transport -/

noncomputable abbrev outputSupportEuclideanEndToContinuousLinearEquiv {n m : ℕ} (Φ : HSMap n m) :
    (outputSupportEuclideanSubspace Φ →ₗ[ℂ] outputSupportEuclideanSubspace Φ) ≃ₗ[ℂ]
      (outputSupportEuclideanSubspace Φ →L[ℂ] outputSupportEuclideanSubspace Φ) :=
  _root_.HiaiPetz.outputSupportEuclideanEndToContinuousLinearEquiv Φ

/-- The finite-dimensional continuous-linear upgrade preserves composition. -/
theorem outputSupportEuclideanEndToContinuousLinearEquiv_mul {n m : ℕ} (Φ : HSMap n m)
    (T S : outputSupportEuclideanSubspace Φ →ₗ[ℂ] outputSupportEuclideanSubspace Φ) :
    outputSupportEuclideanEndToContinuousLinearEquiv Φ (T * S) =
      outputSupportEuclideanEndToContinuousLinearEquiv Φ T *
        outputSupportEuclideanEndToContinuousLinearEquiv Φ S := by
  rfl

noncomputable abbrev outputCornerToEuclideanContinuousLinearEquiv {n m : ℕ} (Φ : HSMap n m) :
    matrixCornerSubmodule (outputSupportProj Φ) ≃ₗ[ℂ]
      (outputSupportEuclideanSubspace Φ →L[ℂ] outputSupportEuclideanSubspace Φ) :=
  _root_.HiaiPetz.outputCornerToEuclideanContinuousLinearEquiv Φ

/-- The output-corner continuous-linear coordinate map preserves multiplication. -/
theorem outputCornerToEuclideanContinuousLinearEquiv_mul {n m : ℕ} (Φ : HSMap n m)
    (X Y : matrixCornerSubmodule (outputSupportProj Φ)) :
    outputCornerToEuclideanContinuousLinearEquiv Φ
      ⟨X.1 * Y.1, outputCorner_mul_mem Φ X Y⟩ =
      outputCornerToEuclideanContinuousLinearEquiv Φ X *
        outputCornerToEuclideanContinuousLinearEquiv Φ Y := by
  exact _root_.HiaiPetz.outputCornerToEuclideanContinuousLinearEquiv_mul Φ X Y

end

end Quantum.TraceInequality.Loewner.HiaiPetz
