/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.TraceFunctionMonotonicity.Sandwiched.PowerTrace
import Quantum.TraceInequality.TraceFunctionMonotonicity.PowerTrace
import Quantum.TraceInequality.HiaiPetz.PowerTraceRetained
import Quantum.TraceInequality.HansenPedersen.LaterConsequences
import Quantum.TraceInequality.LaterConsequencesRetained
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule

/-!
# Basic transport lemmas for matrix real powers

This file contains the elementary bridge from finite matrices to continuous
linear maps on Euclidean space. It transports matrix nonnegativity, real scalar
multiplication, and positive-definite spectral information through
`Matrix.toEuclideanCLM`, preparing later files to reuse operator functional
calculus results for `matrixPower`.

## Main results

* `toEuclideanCLM_nonneg_of_matrix_nonneg`: nonnegative matrices become
  nonnegative Euclidean continuous linear maps.
* `toEuclideanCLM_spectrum_Ici_of_matrix_nonneg`: spectral nonnegativity after
  transport.
* `toEuclideanCLM_real_smul`: compatibility with real scalar multiplication.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Chapter 6 matrix functional calculus.
-/

namespace HiaiPetz

open scoped ComplexOrder MatrixOrder

noncomputable section MatrixScopedInstances

/-- If `n` is nonzero, the Euclidean space on `Fin n` is nontrivial. This
supplies the operator-level nontriviality needed by transported CFC theorems. -/
theorem euclideanNontrivial_of_fin_ne_zero {n : ℕ} (hn : n ≠ 0) :
    Nontrivial (EuclideanSpace ℂ (Fin n)) := by
  classical
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  refine ⟨0, EuclideanSpace.single i (1 : ℂ), ?_⟩
  intro h
  have hsingle : EuclideanSpace.single i (1 : ℂ) = 0 := h.symm
  exact one_ne_zero (EuclideanSpace.single_eq_zero_iff.mp hsingle)

/-- A nonnegative matrix is sent by `Matrix.toEuclideanCLM` to a nonnegative
continuous linear map on Euclidean space. -/
theorem toEuclideanCLM_nonneg_of_matrix_nonneg {n : ℕ} {A : Mₙ n}
    (hA : 0 ≤ A) :
    0 ≤ (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A := by
  let φ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hpsd : A.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hA
  have hlin : ((φ A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
      EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)).IsPositive := by
    simpa [φ, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
      (Matrix.isPositive_toEuclideanLin_iff (A := A)).2 hpsd
  exact (ContinuousLinearMap.nonneg_iff_isPositive (φ A)).2 hlin

-- CLM order instances are needed for spectrum positivity.
/-- The real spectrum of the Euclidean CLM associated to a nonnegative matrix
is contained in `[0, ∞)`. -/
theorem toEuclideanCLM_spectrum_Ici_of_matrix_nonneg {n : ℕ} {A : Mₙ n}
    (hA : 0 ≤ A) :
    spectrum ℝ ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A) ⊆ Set.Ici (0 : ℝ) := by
  intro x hx
  exact spectrum_nonneg_of_nonneg
    (𝕜 := ℝ)
    (A := EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (a := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A)
    (toEuclideanCLM_nonneg_of_matrix_nonneg hA) hx

-- Real scalar action on CLM is inferred through complex scalar towers.
/-- `Matrix.toEuclideanCLM` commutes with real scalar multiplication, viewed
through the complex scalar tower. -/
theorem toEuclideanCLM_real_smul {n : ℕ} (a : ℝ) (A : Mₙ n) :
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) (a • A) =
      a • (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A := by
  let φ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  change φ ((a : ℂ) • A) = (a : ℂ) • φ A
  exact map_smul φ ((a : ℂ)) A

end MatrixScopedInstances

end HiaiPetz
