/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Quantum.TraceInequality.HiaiPetz.MatrixPosDef

/-!
# Positive definite matrix transport

Finite-dimensional lower-bound facts for positive definite matrices and their
transport through positive Hilbert--Schmidt maps.  The proofs reduce strict
positivity to a scalar spectral lower bound and then use positivity of the map
plus strict positivity of `Φ 1`.

## Main results

* `Matrix.PosDef.exists_pos_algebraMap_le`: a positive definite matrix dominates
  a positive scalar multiple of the identity.
* `Matrix.PosDef.image_of_isPositiveMap`: a positive map sends positive definite
  inputs to positive definite outputs when `Φ 1` is positive definite.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Section 6.1.
-/

namespace HiaiPetz

open Matrix Unitary
open scoped MatrixOrder ComplexOrder
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- A PSD matrix plus `ε•1` (`ε>0`) is positive definite. -/
theorem matrixPosDef_add_pos_smul_one_of_nonneg {n : ℕ} {A : Mₙ n}
    (hA : 0 ≤ A) {ε : ℝ} (hε : 0 < ε) :
    Matrix.PosDef (A + (ε : ℂ) • (1 : Mₙ n)) := by
  have hApsd : A.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hA
  have hεone_real : ((ε : ℝ) • (1 : Mₙ n)).PosDef :=
    Matrix.PosDef.smul (Matrix.PosDef.one (R := ℂ) (n := Fin n)) hε
  have hεone : ((ε : ℂ) • (1 : Mₙ n)).PosDef := by
    simpa using hεone_real
  exact Matrix.PosDef.posSemidef_add hApsd hεone

/-- The real spectrum of the Euclidean continuous linear map associated to a
positive-definite matrix is contained in `(0, ∞)`. -/
theorem toEuclideanCLM_spectrum_Ioi_of_matrix_posDef {n : ℕ} {C : Mₙ n}
    (hC : Matrix.PosDef C) :
    spectrum ℝ ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) C) ⊆ Set.Ioi (0 : ℝ) := by
  let φ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  let T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) := φ C
  have hTunit : IsUnit T := by
    simpa [T, φ] using IsUnit.map φ hC.isUnit
  have hTnonneg : 0 ≤ T := by
    have hpos : (T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).IsPositive := by
      change ((φ C : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
        EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)).IsPositive
      simpa [φ, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
        (Matrix.isPositive_toEuclideanLin_iff (A := C)).2 hC.posSemidef
    exact (ContinuousLinearMap.nonneg_iff_isPositive T).2 hpos
  have hTstrict : IsStrictlyPositive T := hTunit.isStrictlyPositive hTnonneg
  intro x hx
  exact hTstrict.spectrum_pos hx

end MatrixScopedInstances

end HiaiPetz

namespace HiaiPetz.MatrixPosDef

section

open HiaiPetz Matrix Unitary
open scoped MatrixOrder ComplexOrder CStarAlgebra

/-- The image block `jArg (Φ A) (Φ B)` is self-adjoint when `Φ` is positive and `A, B` are
positive definite. -/
theorem imageJArg_isSelfAdjoint
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    IsSelfAdjoint (jArg (Φ A) (Φ B)) := by
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  simpa [hsAdjoint] using jArg_isSelfAdjoint (A := Φ A) (B := Φ B) hΦA.1 hΦB

end

end HiaiPetz.MatrixPosDef

namespace HiaiPetz.MatrixPosDef

section

open HiaiPetz Matrix Unitary
open scoped MatrixOrder ComplexOrder CStarAlgebra

/-- The zero matrix on a space of positive dimension `n+1` is not positive
definite: the standard basis vector `e₀` witnesses a vanishing quadratic form. -/
theorem not_matrixPosDef_zero_succ (n : ℕ) :
    ¬ Matrix.PosDef (0 : Mₙ (Nat.succ n)) := by
  intro hzero
  let x : Fin (Nat.succ n) → ℂ := Pi.single 0 (1 : ℂ)
  have hx : x ≠ 0 := by
    intro hx0
    have hx00 := congrArg (fun v => v 0) hx0
    simp [x] at hx00
  have hpos0 := hzero.re_dotProduct_pos hx
  simp [x] at hpos0

end

end HiaiPetz.MatrixPosDef
