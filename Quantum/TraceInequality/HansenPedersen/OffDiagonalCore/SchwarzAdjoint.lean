/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.MatrixPosDef
import Quantum.TraceInequality.HiaiPetz.MatrixPosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Provider-independent Schwarz-adjoint matrix facts

The matrix square-root and Hilbert--Schmidt adjoint facts used by shared
trace-monotonicity consumers independently of the selected proof provider.
-/

namespace HiaiPetz

open Matrix Unitary
open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra

/-- Positive square root of a matrix when it is nonnegative, and zero
otherwise; the nonnegative branch is defined by Hermitian functional calculus. -/
noncomputable def matrixSqrtPos {n : ℕ} (A : Mₙ n) : Mₙ n := by
  classical
  exact if hA : 0 ≤ A then
    let hApsd : A.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hA
    Matrix.IsHermitian.cfc hApsd.1 (fun x : ℝ => Real.sqrt x)
  else 0
/-- On a nonnegative matrix, `matrixSqrtPos` is exactly the Hermitian functional
calculus square root. -/
theorem matrixSqrtPos_eq_of_nonneg {n : ℕ} {A : Mₙ n} (hA : 0 ≤ A) :
    matrixSqrtPos A =
      Matrix.IsHermitian.cfc ((Matrix.nonneg_iff_posSemidef).mp hA).1
        (fun x : ℝ => Real.sqrt x) := by
  classical
  simp [matrixSqrtPos, hA]
/-- The positive square root of a nonnegative matrix is positive semidefinite. -/
theorem matrixSqrtPos_posSemidef_of_nonneg {n : ℕ} {A : Mₙ n}
    (hA : 0 ≤ A) :
    (matrixSqrtPos A).PosSemidef := by
  classical
  let hApsd : A.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hA
  rw [matrixSqrtPos_eq_of_nonneg hA]
  change (((Unitary.conjStarAlgAut ℂ (Mₙ n)) hApsd.1.eigenvectorUnitary)
      (Matrix.diagonal
        (RCLike.ofReal ∘ (fun x : ℝ => Real.sqrt x) ∘ hApsd.1.eigenvalues))).PosSemidef
  simp [Matrix.IsUnit.posSemidef_star_right_conjugate_iff isUnit_coe,
    Matrix.posSemidef_diagonal_iff,
    Real.sqrt_nonneg]
/-- The positive square root of a nonnegative matrix squares back to the
original matrix. -/
theorem matrixSqrtPos_mul_self_of_nonneg {n : ℕ} {A : Mₙ n}
    (hA : 0 ≤ A) :
    matrixSqrtPos A * matrixSqrtPos A = A := by
  classical
  let hApsd : A.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hA
  let U : Mₙ n := ↑hApsd.1.eigenvectorUnitary
  let D : Mₙ n := Matrix.diagonal (fun i => (Real.sqrt (hApsd.1.eigenvalues i) : ℂ))
  have hU : star U * U = 1 := by
    simp [U]
  calc
    matrixSqrtPos A * matrixSqrtPos A
        = (U * D * star U) * (U * D * star U) := by
            rw [matrixSqrtPos_eq_of_nonneg hA]
            rfl
    _ = U * D * (star U * U) * D * star U := by
          simp [Matrix.mul_assoc]
    _ = U * D * D * star U := by
          simp [hU, Matrix.mul_assoc]
    _ = U * (D * D) * star U := by
          simp [Matrix.mul_assoc]
    _ = U *
          Matrix.diagonal
            (fun i => ((Real.sqrt (hApsd.1.eigenvalues i) : ℂ) *
              (Real.sqrt (hApsd.1.eigenvalues i) : ℂ))) *
          star U := by
            rw [Matrix.diagonal_mul_diagonal]
    _ = U * Matrix.diagonal (fun i => (hApsd.1.eigenvalues i : ℂ)) * star U := by
          congr 2
          ext i j
          by_cases hij : i = j
          · subst hij
            simp [Matrix.diagonal]
            simpa [sq] using congrArg Complex.ofReal (Real.sq_sqrt (hApsd.eigenvalues_nonneg i))
          · simp [Matrix.diagonal, hij]
    _ = A := by
          simpa [U, Function.comp_def] using hApsd.1.spectral_theorem.symm
/-- The Schwarz condition for the Hilbert-Schmidt adjoint implies that the
adjoint map preserves nonnegativity. -/
theorem hsAdjoint_nonneg_of_schwarz
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l))
    (hSch : HSAdjointSchwarz Φ)
    {X : Mₙ (Nat.succ l)} (hX : 0 ≤ X) :
    0 ≤ (hsAdjoint Φ) X := by
  have hXpsd : X.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hX
  let Y : Mₙ (Nat.succ l) := matrixSqrtPos X
  have hYpsd : Y.PosSemidef := by
    simpa [Y] using matrixSqrtPos_posSemidef_of_nonneg hX
  have hYsa : IsSelfAdjoint Y := by
    simpa [Matrix.IsHermitian, IsSelfAdjoint] using hYpsd.1
  have hYsq : Matrix.conjTranspose Y * Y = X := by
    have hmul : Y * Y = X := by
      simpa [Y] using matrixSqrtPos_mul_self_of_nonneg hX
    calc
      Matrix.conjTranspose Y * Y = Y * Y := by
        simpa [Matrix.star_eq_conjTranspose] using congrArg (fun M => M * Y) hYsa.star_eq
      _ = X := hmul
  calc
    0 ≤ Matrix.conjTranspose ((hsAdjoint Φ) Y) * ((hsAdjoint Φ) Y) := by
      exact Matrix.PosSemidef.nonneg (Matrix.posSemidef_conjTranspose_mul_self ((hsAdjoint Φ) Y))
    _ ≤ (hsAdjoint Φ) (Matrix.conjTranspose Y * Y) := hSch Y
    _ = (hsAdjoint Φ) X := by rw [hYsq]

/-- Positive part of a Hermitian matrix, defined by functional calculus with
`x ↦ max x 0`. -/
noncomputable def hermitianPosPartMatrix {n : ℕ} {X : Mₙ n}
    (hX : X.IsHermitian) : Mₙ n :=
  hX.cfc (fun x : ℝ => max x 0)

/-- Negative part of a Hermitian matrix, defined by functional calculus with
`x ↦ max (-x) 0`. -/
noncomputable def hermitianNegPartMatrix {n : ℕ} {X : Mₙ n}
    (hX : X.IsHermitian) : Mₙ n :=
  hX.cfc (fun x : ℝ => max (-x) 0)

/-- The positive part of a Hermitian matrix is positive semidefinite. -/
theorem hermitianPosPartMatrix_posSemidef {n : ℕ} {X : Mₙ n}
    (hX : X.IsHermitian) : (hermitianPosPartMatrix hX).PosSemidef := by
  dsimp [hermitianPosPartMatrix]
  rw [Matrix.IsHermitian.cfc]
  refine
    (Matrix.IsUnit.posSemidef_star_right_conjugate_iff
      (hU := Unitary.isUnit_coe (U := hX.eigenvectorUnitary))).2 ?_
  simp [Matrix.posSemidef_diagonal_iff]

/-- The negative part of a Hermitian matrix is positive semidefinite. -/
theorem hermitianNegPartMatrix_posSemidef {n : ℕ} {X : Mₙ n}
    (hX : X.IsHermitian) : (hermitianNegPartMatrix hX).PosSemidef := by
  dsimp [hermitianNegPartMatrix]
  rw [Matrix.IsHermitian.cfc]
  refine
    (Matrix.IsUnit.posSemidef_star_right_conjugate_iff
      (hU := Unitary.isUnit_coe (U := hX.eigenvectorUnitary))).2 ?_
  simp [Matrix.posSemidef_diagonal_iff]

/-- A Hermitian matrix decomposes as its positive part minus its negative
part. -/
theorem hermitian_sub_posPartMatrix_negPartMatrix {n : ℕ} {X : Mₙ n}
    (hX : X.IsHermitian) :
    X = hermitianPosPartMatrix hX - hermitianNegPartMatrix hX := by
  have hspec := hX.spectral_theorem
  calc
    X =
        Unitary.conjStarAlgAut ℂ _ hX.eigenvectorUnitary
          (Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues)) := hspec
    _ = hX.cfc (fun x : ℝ => max x 0) - hX.cfc (fun x : ℝ => max (-x) 0) := by
      rw [Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc, ← map_sub]
      congr 1
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.diagonal_apply_eq, Function.comp_apply, Complex.coe_algebraMap,
          Matrix.sub_apply]
        exact_mod_cast (max_zero_sub_eq_self (hX.eigenvalues i)).symm
      · simp [Matrix.diagonal, hij]

/-- Under the Schwarz condition, the Hilbert-Schmidt adjoint sends
self-adjoint matrices to self-adjoint matrices. -/
theorem hsAdjoint_map_isSelfAdjoint_of_schwarz
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l))
    (hSch : HSAdjointSchwarz Φ)
    {X : Mₙ (Nat.succ l)} (hX : IsSelfAdjoint X) :
    IsSelfAdjoint ((hsAdjoint Φ) X) := by
  have hXH : X.IsHermitian := by
    simpa [Matrix.IsHermitian, IsSelfAdjoint] using hX
  let pos : Mₙ (Nat.succ l) := hermitianPosPartMatrix hXH
  let neg : Mₙ (Nat.succ l) := hermitianNegPartMatrix hXH
  have hpos_psd : pos.PosSemidef := by
    dsimp [pos]
    exact hermitianPosPartMatrix_posSemidef hXH
  have hneg_psd : neg.PosSemidef := by
    dsimp [neg]
    exact hermitianNegPartMatrix_posSemidef hXH
  have hdecomp : X = pos - neg := by
    dsimp [pos, neg]
    exact hermitian_sub_posPartMatrix_negPartMatrix hXH
  have hΦpos_nonneg : 0 ≤ (hsAdjoint Φ) pos := by
    exact hsAdjoint_nonneg_of_schwarz (Φ := Φ) hSch <|
      Matrix.nonneg_iff_posSemidef.mpr hpos_psd
  have hΦneg_nonneg : 0 ≤ (hsAdjoint Φ) neg := by
    exact hsAdjoint_nonneg_of_schwarz (Φ := Φ) hSch <|
      Matrix.nonneg_iff_posSemidef.mpr hneg_psd
  have hΦpos_sa : IsSelfAdjoint ((hsAdjoint Φ) pos) := by
    simpa [Matrix.IsHermitian, IsSelfAdjoint] using
      (Matrix.nonneg_iff_posSemidef.mp hΦpos_nonneg).1
  have hΦneg_sa : IsSelfAdjoint ((hsAdjoint Φ) neg) := by
    simpa [Matrix.IsHermitian, IsSelfAdjoint] using
      (Matrix.nonneg_iff_posSemidef.mp hΦneg_nonneg).1
  rw [hdecomp, (hsAdjoint Φ).map_sub, sub_eq_add_neg]
  simpa [sub_eq_add_neg] using hΦpos_sa.add hΦneg_sa.neg

/-- Under the Schwarz condition, the Hilbert-Schmidt adjoint commutes with
conjugate transpose. -/
theorem hsAdjoint_map_conjTranspose_of_schwarz
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l))
    (hSch : HSAdjointSchwarz Φ)
    (U : Mₙ (Nat.succ l)) :
    (hsAdjoint Φ) (Matrix.conjTranspose U) =
      Matrix.conjTranspose ((hsAdjoint Φ) U) := by
  let H : Mₙ (Nat.succ l) := ((1 / 2 : ℂ)) • (U + Matrix.conjTranspose U)
  let K : Mₙ (Nat.succ l) := ((-(Complex.I) / 2 : ℂ)) • (U - Matrix.conjTranspose U)
  have hH : IsSelfAdjoint H := by
    change Matrix.conjTranspose H = H
    ext i j
    simp [H]
    ring_nf
  have hK : IsSelfAdjoint K := by
    change Matrix.conjTranspose K = K
    ext i j
    simp [K]
    ring_nf
  have hHU : (hsAdjoint Φ) H = Matrix.conjTranspose ((hsAdjoint Φ) H) := by
    simpa [Matrix.star_eq_conjTranspose] using
      (hsAdjoint_map_isSelfAdjoint_of_schwarz (Φ := Φ) hSch hH).star_eq.symm
  have hKU : (hsAdjoint Φ) K = Matrix.conjTranspose ((hsAdjoint Φ) K) := by
    simpa [Matrix.star_eq_conjTranspose] using
      (hsAdjoint_map_isSelfAdjoint_of_schwarz (Φ := Φ) hSch hK).star_eq.symm
  have hdecomp : U = H + Complex.I • K := by
    have hdecomp' : H + Complex.I • K = U := by
      have hcoef : (Complex.I : ℂ) * (-(Complex.I) / 2 : ℂ) = (1 / 2 : ℂ) := by
        field_simp
        norm_num
      calc
      H + Complex.I • K
          = ((1 / 2 : ℂ)) • (U + Matrix.conjTranspose U) +
              (((Complex.I : ℂ) * (-(Complex.I) / 2 : ℂ)) •
                (U - Matrix.conjTranspose U)) := by
                  simp [H, K, smul_smul]
      _ = ((1 / 2 : ℂ)) • (U + Matrix.conjTranspose U) +
            ((1 / 2 : ℂ)) • (U - Matrix.conjTranspose U) := by
              rw [hcoef]
      _ = U := by
            calc
              ((1 / 2 : ℂ)) • (U + Matrix.conjTranspose U) +
                  ((1 / 2 : ℂ)) • (U - Matrix.conjTranspose U)
                  = (((1 / 2 : ℂ) + (1 / 2 : ℂ)) • U) +
                      (((1 / 2 : ℂ) + (-(1 / 2 : ℂ))) • Matrix.conjTranspose U) := by
                          ext i j
                          simp [sub_eq_add_neg, add_smul, add_comm]
                          ring_nf
              _ = U := by norm_num
    exact hdecomp'.symm
  have hdecomp_star : Matrix.conjTranspose U = H - Complex.I • K := by
    have hHct : Matrix.conjTranspose H = H := by
      simpa [Matrix.star_eq_conjTranspose] using hH.star_eq
    have hKct : Matrix.conjTranspose K = K := by
      simpa [Matrix.star_eq_conjTranspose] using hK.star_eq
    calc
      Matrix.conjTranspose U = Matrix.conjTranspose (H + Complex.I • K) := by
        simp [hdecomp]
      _ = Matrix.conjTranspose H + Matrix.conjTranspose (Complex.I • K) := by
        simp
      _ = H - Complex.I • K := by
        simp [hHct, hKct, sub_eq_add_neg]
  calc
    (hsAdjoint Φ) (Matrix.conjTranspose U)
        = (hsAdjoint Φ) H - Complex.I • ((hsAdjoint Φ) K) := by
            rw [hdecomp_star, (hsAdjoint Φ).map_sub,
              (hsAdjoint Φ).map_smul, (hsAdjoint Φ).map_smul]
    _ = Matrix.conjTranspose ((hsAdjoint Φ) H + Complex.I • ((hsAdjoint Φ) K)) := by
          rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, ← hHU, ← hKU]
          simp [sub_eq_add_neg]
    _ = Matrix.conjTranspose ((hsAdjoint Φ) U) := by
          have hcoef' : (Complex.I : ℂ) * (-(Complex.I) / 2 : ℂ) = (1 / 2 : ℂ) := by
            field_simp
            norm_num
          rw [hdecomp]
          ext i j
          simp

/-- Schwarz inequality in the form with `U * U†`, obtained from the defining
Schwarz condition by conjugate-transpose compatibility. -/
theorem hsAdjointSchwarz_mul_conjTranspose
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l))
    (hSch : HSAdjointSchwarz Φ)
    (U : Mₙ (Nat.succ l)) :
    ((hsAdjoint Φ) U) * Matrix.conjTranspose ((hsAdjoint Φ) U) ≤
      (hsAdjoint Φ) (U * Matrix.conjTranspose U) := by
  have hsch := hSch (Matrix.conjTranspose U)
  let X : Mₙ (Nat.succ k) := (hsAdjoint Φ) (Matrix.conjTranspose U)
  have hmap : X = Matrix.conjTranspose ((hsAdjoint Φ) U) :=
    hsAdjoint_map_conjTranspose_of_schwarz (Φ := Φ) hSch U
  change star X * X ≤ (hsAdjoint Φ)
    (Matrix.conjTranspose (Matrix.conjTranspose U) * Matrix.conjTranspose U) at hsch
  rw [hmap] at hsch
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_mul] using hsch
end HiaiPetz

namespace HiaiPetz.OffDiagonalCore

section

open HiaiPetz Matrix Unitary
open scoped MatrixOrder ComplexOrder CStarAlgebra

/-- Positive definiteness is preserved by the positive square-root
construction. -/
theorem matrixPosDef_sqrt {n : ℕ} {A : Mₙ n} :
    Matrix.PosDef A → Matrix.PosDef (matrixSqrtPos A) := by
  intro hA
  let S : Mₙ n := matrixSqrtPos A
  have hS_psd : S.PosSemidef := matrixSqrtPos_posSemidef_of_nonneg (Matrix.PosDef.nonneg hA)
  have hS_unit : IsUnit S := by
    rw [Matrix.isUnit_iff_isUnit_det]
    refine isUnit_iff_ne_zero.mpr ?_
    have hprod : ∀ i : Fin n,
        Real.sqrt (hA.1.eigenvalues i) ≠ 0 := by
      intro i
      exact Real.sqrt_ne_zero'.2 (hA.eigenvalues_pos i)
    simpa [S, matrixSqrtPos_eq_of_nonneg (Matrix.PosDef.nonneg hA), Matrix.IsHermitian.cfc,
      -Unitary.conjStarAlgAut_apply, Finset.prod_ne_zero_iff] using hprod
  exact hS_psd.posDef_iff_isUnit.mpr hS_unit

end

end HiaiPetz.OffDiagonalCore

namespace HiaiPetz.OffDiagonalCore

section

open HiaiPetz Matrix Unitary
open scoped MatrixOrder ComplexOrder CStarAlgebra

/-- Positive-definite version of `matrixSqrtPos_mul_self_of_nonneg`. -/
theorem matrixSqrtPos_mul_self {n : ℕ} {A : Mₙ n}
    (hA : Matrix.PosDef A) :
    matrixSqrtPos A * matrixSqrtPos A = A := by
  exact matrixSqrtPos_mul_self_of_nonneg (Matrix.PosDef.nonneg hA)

end

end HiaiPetz.OffDiagonalCore
