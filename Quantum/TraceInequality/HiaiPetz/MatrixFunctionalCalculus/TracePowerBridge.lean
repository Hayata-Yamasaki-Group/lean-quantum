/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Quantum.TraceInequality.HiaiPetz.Basic
import Quantum.TraceInequality.HiaiPetz.Core.Basic
import Quantum.TraceInequality.HiaiPetz.Core.MatrixType
import Mathlib.LinearAlgebra.Lagrange

/-!
# Provider-independent trace-power bridges

This module contains the functional-calculus identities identifying the
J-operator trace functionals with the Lieb and inverse trace-power functionals.
It deliberately contains no Hiai--Petz 6.2 implication or provider package.
-/

namespace HiaiPetz

open Matrix Unitary
open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

/-- The matrix CFC of a self-adjoint matrix is self-adjoint. -/
theorem matrixCfcR_isSelfAdjoint
    {n : ℕ} (f : ℝ → ℝ) {A : Mₙ n} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (HansenPedersen.matrixCfcR f A) := by
  let φ : Mₙ n ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hφA : IsSelfAdjoint (φ A) := by
    have h1 : φ (star A) = φ A := congrArg φ hA
    simpa [map_star] using h1
  have hSelfEuclid :
      IsSelfAdjoint
        (HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f (φ A)) := by
    simp [HansenPedersen.cfcR]
  have hBack :
      φ.symm (star (HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f (φ A))) =
        φ.symm (HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f (φ A)) := by
    exact congrArg φ.symm hSelfEuclid.star_eq
  change
    star ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm
      (HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A))) =
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm
      (HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A))
  simpa [φ, HansenPedersen.matrixCfcR, map_star] using hBack

end HiaiPetz
