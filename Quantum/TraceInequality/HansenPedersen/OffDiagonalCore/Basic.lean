/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.BlockSumBase
import Quantum.TraceInequality.HiaiPetz.MatrixPosDef
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.StandardRectangle.Main
import
Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.StandardRectangle.DirectToInverse
import Quantum.TraceInequality.HansenPedersen.LaterConsequences
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Quantum.TraceInequality.HansenPedersen.OffDiagonalCore.SchwarzAdjoint
import Quantum.TraceInequality.HansenPedersen.SharedVocabulary
import Quantum.TraceInequality.HiaiPetz.HilbertSchmidt.QuadraticForm
import Quantum.TraceInequality.HansenPedersen.AmbientSubmodule.JOperatorInequalities
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.Basic
import Quantum.TraceInequality.HiaiPetz.Core.JOperatorPositivity

/-!
# Off-diagonal core basics

Positive-definite matrix square-root facts and the strict-output contraction
estimates used by the off-diagonal block construction.

## Main results

* `matrixSqrtPos` and `matrixInvSqrtPos`: positive square-root and inverse
  square-root operators for positive definite matrices.
* `hsAdjoint_nonneg_of_schwarz` and `hsAdjointSchwarz_mul_conjTranspose`:
  consequences of the Schwarz condition for the Hilbert-Schmidt adjoint.
* `StrictlyPositive.contraction_contractive`: the contraction estimate that
  drives the strict-output off-diagonal construction.

## References

* Hiai, Schur complement and Schwarz-map estimates used in the strict
  data-processing/off-diagonal reduction.
-/

namespace HiaiPetz

open Matrix Unitary
open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra


/-- Inverse of the positive square root used for strict positive matrices. -/
noncomputable def matrixInvSqrtPos {n : ℕ} (A : Mₙ n) : Mₙ n :=
  (matrixSqrtPos A)⁻¹

/-- For a positive definite matrix, the square root multiplied by its inverse
square root is the identity. -/
theorem matrixSqrtPos_mul_matrixInvSqrtPos {n : ℕ} {A : Mₙ n}
    (hA : Matrix.PosDef A) :
    matrixSqrtPos A * matrixInvSqrtPos A = 1 := by
  rcases (HiaiPetz.OffDiagonalCore.matrixPosDef_sqrt hA).isUnit with ⟨u, hu⟩
  have hu' : matrixSqrtPos A = (u : Mₙ n) := by
    simpa using hu.symm
  have huinv' : matrixInvSqrtPos A = (↑u⁻¹ : Mₙ n) := by
    rw [matrixInvSqrtPos, hu']
    simp
  rw [hu', huinv']
  exact Units.mul_inv u

/-- For a positive definite matrix, the inverse square root multiplied by the
square root is the identity. -/
theorem matrixInvSqrtPos_mul_matrixSqrtPos {n : ℕ} {A : Mₙ n}
    (hA : Matrix.PosDef A) :
    matrixInvSqrtPos A * matrixSqrtPos A = 1 := by
  rcases (HiaiPetz.OffDiagonalCore.matrixPosDef_sqrt hA).isUnit with ⟨u, hu⟩
  have hu' : matrixSqrtPos A = (u : Mₙ n) := by
    simpa using hu.symm
  have huinv' : matrixInvSqrtPos A = (↑u⁻¹ : Mₙ n) := by
    rw [matrixInvSqrtPos, hu']
    simp
  rw [hu', huinv']
  exact Units.inv_mul u

/-- The inverse square root of a positive definite matrix is positive
definite. -/
theorem matrixInvSqrtPos_posDef {n : ℕ} {A : Mₙ n}
    (hA : Matrix.PosDef A) :
    Matrix.PosDef (matrixInvSqrtPos A) := by
  simpa [matrixInvSqrtPos] using
    (posInv_posDef (B := matrixSqrtPos A) (HiaiPetz.OffDiagonalCore.matrixPosDef_sqrt hA))

/-- The square of the inverse square root is the positive inverse of the
matrix. -/
theorem matrixInvSqrtPos_mul_self {n : ℕ} {A : Mₙ n}
    (hA : Matrix.PosDef A) :
    matrixInvSqrtPos A * matrixInvSqrtPos A = A⁻¹ := by
  rcases (HiaiPetz.OffDiagonalCore.matrixPosDef_sqrt hA).isUnit with ⟨u, hu⟩
  have hu' : matrixSqrtPos A = (u : Mₙ n) := by
    simpa using hu.symm
  have hsqrtmul : matrixSqrtPos A * matrixSqrtPos A = A := by
    exact matrixSqrtPos_mul_self_of_nonneg (Matrix.PosDef.nonneg hA)
  have hsqrtmul' : ((↑u : Mₙ n) * (↑u : Mₙ n)) = A := by
    simpa [hu'] using hsqrtmul
  have hmulinv :
      (((u⁻¹ : Units (Mₙ n)) : Mₙ n) * ((u⁻¹ : Units (Mₙ n)) : Mₙ n)) =
        Ring.inverse ((↑u : Mₙ n) * (↑u : Mₙ n)) := by
    calc
      (((u⁻¹ : Units (Mₙ n)) : Mₙ n) * ((u⁻¹ : Units (Mₙ n)) : Mₙ n))
          = (((u * u)⁻¹ : Units (Mₙ n)) : Mₙ n) := by
              simp
      _ = Ring.inverse ((↑u : Mₙ n) * (↑u : Mₙ n)) := by
            symm
            simpa using Ring.inverse_unit (u * u)
  calc
    matrixInvSqrtPos A * matrixInvSqrtPos A
        = (((u⁻¹ : Units (Mₙ n)) : Mₙ n) * (u⁻¹ : Units (Mₙ n))) := by
            simp [matrixInvSqrtPos, hu']
    _ = Ring.inverse ((↑u : Mₙ n) * (↑u : Mₙ n)) := by
          exact hmulinv
    _ = Ring.inverse A := by
          simpa using congrArg Ring.inverse hsqrtmul'
    _ = A⁻¹ := by
          simp [Matrix.nonsing_inv_eq_ringInverse]

/-- Strict-output contraction associated to a positive map `Φ` and a positive
definite base point `B`, normalized by the square roots of `B` and `Φ B`. -/
noncomputable def StrictlyPositive.contraction
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {B : Mₙ (Nat.succ k)}
    (_hPos : IsPositiveMap Φ) (_hB : Matrix.PosDef B) (_hΦ1 : Matrix.PosDef (Φ 1)) :
    HSMap (Nat.succ l) (Nat.succ k) :=
  (rightMul (matrixSqrtPos B)).comp
    ((hsAdjoint Φ).comp (rightMul (matrixInvSqrtPos (Φ B))))

private theorem StrictlyPositive.contraction_apply
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ) (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ l)) :
    StrictlyPositive.contraction Φ hPos hB hΦ1 X =
      ((hsAdjoint Φ) (X * matrixInvSqrtPos (Φ B))) * matrixSqrtPos B := by
  rfl

/-- Applying the strict-output contraction after right multiplication by
`sqrt (Φ B)` removes the inverse-square-root normalization. -/
theorem StrictlyPositive.contraction_apply_sqrtShift
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ) (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ l)) :
    StrictlyPositive.contraction Φ hPos hB hΦ1 (rightMul (matrixSqrtPos (Φ B)) X) =
      ((hsAdjoint Φ) X) * matrixSqrtPos B := by
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  simp [StrictlyPositive.contraction_apply, rightMul_apply, Matrix.mul_assoc,
    matrixSqrtPos_mul_matrixInvSqrtPos hΦB]

/-- If `B` is positive definite and `D` is nonnegative, then the real part of
`tr (B D)` is nonnegative. -/
theorem re_trace_mul_nonneg_of_posDef_nonneg {n : ℕ} {B D : Mₙ n}
    (hB : Matrix.PosDef B) (hD : 0 ≤ D) :
    0 ≤ Complex.re (Matrix.trace (B * D)) := by
  have hD_psd : D.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hD
  have hconj_psd :
      (matrixSqrtPos B * D * Matrix.conjTranspose (matrixSqrtPos B)).PosSemidef := by
    exact Matrix.PosSemidef.mul_mul_conjTranspose_same hD_psd (matrixSqrtPos B)
  have htrace_nonneg :
      0 ≤ Matrix.trace (matrixSqrtPos B * D * Matrix.conjTranspose (matrixSqrtPos B)) :=
    Matrix.PosSemidef.trace_nonneg hconj_psd
  have hsqrt_star : Matrix.conjTranspose (matrixSqrtPos B) = matrixSqrtPos B := by
    exact (HiaiPetz.OffDiagonalCore.matrixPosDef_sqrt hB).isHermitian
  have htrace_eq :
      Matrix.trace (matrixSqrtPos B * D * Matrix.conjTranspose (matrixSqrtPos B)) =
        Matrix.trace (B * D) := by
    rw [hsqrt_star]
    calc
      Matrix.trace ((matrixSqrtPos B * D) * matrixSqrtPos B)
          = Matrix.trace (matrixSqrtPos B * (matrixSqrtPos B * D)) := by
              rw [Matrix.trace_mul_comm]
      _ = Matrix.trace ((matrixSqrtPos B * matrixSqrtPos B) * D) := by
            simp [Matrix.mul_assoc]
      _ = Matrix.trace (B * D) := by
            rw [HiaiPetz.OffDiagonalCore.matrixSqrtPos_mul_self hB]
  have htrace_nonneg' : 0 ≤ Matrix.trace (B * D) := by
    simpa [htrace_eq] using htrace_nonneg
  exact (RCLike.nonneg_iff.mp htrace_nonneg').1

/-- Quadratic-form estimate for the strict-output contraction; the normalized
image has Hilbert-Schmidt square norm bounded by that of the input. -/
theorem StrictlyPositive.contraction_qform_le
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ) (hSch : HSAdjointSchwarz Φ)
    (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ l)) :
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
            StrictlyPositive.contraction Φ hPos hB hΦ1 X)) ≤
      Complex.re (Matrix.trace (Matrix.conjTranspose X * X)) := by
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  let Y : Mₙ (Nat.succ l) := rightMul (matrixInvSqrtPos (Φ B)) X
  let Z : Mₙ (Nat.succ k) := (hsAdjoint Φ) Y
  have hlhs :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
              StrictlyPositive.contraction Φ hPos hB hΦ1 X)) =
        Complex.re (Matrix.trace ((Matrix.conjTranspose Z * Z) * B)) := by
    have hsqrtB_sa : IsSelfAdjoint (matrixSqrtPos B) :=
      (HiaiPetz.OffDiagonalCore.matrixPosDef_sqrt hB).1
    calc
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
              StrictlyPositive.contraction Φ hPos hB hΦ1 X))
          = Complex.re
              (Matrix.trace
                (Matrix.conjTranspose (rightMul (matrixSqrtPos B) Z) *
                  rightMul (matrixSqrtPos B) Z)) := by
                    rw [StrictlyPositive.contraction_apply]
                    simp [Y, Z, rightMul_apply, Matrix.mul_assoc]
      _ = Complex.re
            (Matrix.trace ((Matrix.conjTranspose Z * rightMul (matrixSqrtPos B) Z) *
              matrixSqrtPos B)) := by
                symm
                exact hsQForm_shift_rightMul_testMatrix (B := matrixSqrtPos B) (X := Z)
                  (Y := rightMul (matrixSqrtPos B) Z) hsqrtB_sa
      _ = Complex.re (Matrix.trace ((Matrix.conjTranspose Z * Z) * B)) := by
            simp [rightMul_apply, Matrix.mul_assoc,
              HiaiPetz.OffDiagonalCore.matrixSqrtPos_mul_self hB]
  have hschY :
      Matrix.conjTranspose Z * Z ≤ hsAdjoint Φ (Matrix.conjTranspose Y * Y) := by
    simpa [Y, Z] using hSch Y
  have hdiff_nonneg :
      0 ≤ hsAdjoint Φ (Matrix.conjTranspose Y * Y) - Matrix.conjTranspose Z * Z := by
    exact sub_nonneg.mpr hschY
  have htrace_le :
      Complex.re (Matrix.trace ((Matrix.conjTranspose Z * Z) * B)) ≤
        Complex.re (Matrix.trace (B * hsAdjoint Φ (Matrix.conjTranspose Y * Y))) := by
    have hnonneg :
        0 ≤ Complex.re
          (Matrix.trace
            (B * (hsAdjoint Φ (Matrix.conjTranspose Y * Y) - Matrix.conjTranspose Z * Z))) :=
      re_trace_mul_nonneg_of_posDef_nonneg hB hdiff_nonneg
    have hsplit :
        Complex.re
            (Matrix.trace
              (B * (hsAdjoint Φ (Matrix.conjTranspose Y * Y) - Matrix.conjTranspose Z * Z))) =
          Complex.re (Matrix.trace (B * hsAdjoint Φ (Matrix.conjTranspose Y * Y))) -
            Complex.re (Matrix.trace (B * (Matrix.conjTranspose Z * Z))) := by
      rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    rw [hsplit] at hnonneg
    calc
      Complex.re (Matrix.trace ((Matrix.conjTranspose Z * Z) * B))
          = Complex.re (Matrix.trace (B * (Matrix.conjTranspose Z * Z))) := by
              rw [Matrix.trace_mul_comm]
      _ ≤ Complex.re (Matrix.trace (B * hsAdjoint Φ (Matrix.conjTranspose Y * Y))) := by
            exact sub_nonneg.mp hnonneg
  have hrhs :
      Complex.re (Matrix.trace (B * hsAdjoint Φ (Matrix.conjTranspose Y * Y))) =
        Complex.re (Matrix.trace (Matrix.conjTranspose X * X)) := by
    have hΦB_sa : IsSelfAdjoint (Φ B) := hΦB.1
    have hsqrtΦ_sa : IsSelfAdjoint (matrixSqrtPos (Φ B)) :=
      (HiaiPetz.OffDiagonalCore.matrixPosDef_sqrt hΦB).1
    calc
      Complex.re (Matrix.trace (B * hsAdjoint Φ (Matrix.conjTranspose Y * Y)))
          = Complex.re (Matrix.trace ((Φ B) * (Matrix.conjTranspose Y * Y))) := by
              exact ProofNet.re_trace_mul_hsAdjoint_eq Φ hB.1 hΦB_sa
      _ = Complex.re (Matrix.trace ((Matrix.conjTranspose Y * Y) * (Φ B))) := by
            rw [Matrix.trace_mul_comm]
      _ = Complex.re
            (Matrix.trace
              (Matrix.conjTranspose (rightMul (matrixSqrtPos (Φ B)) Y) *
                rightMul (matrixSqrtPos (Φ B)) Y)) := by
                  have hshift :=
                    hsQForm_shift_rightMul_testMatrix (B := matrixSqrtPos (Φ B))
                      (X := Y) (Y := rightMul (matrixSqrtPos (Φ B)) Y) hsqrtΦ_sa
                  simpa [rightMul_apply, Matrix.mul_assoc,
                    HiaiPetz.OffDiagonalCore.matrixSqrtPos_mul_self hΦB] using hshift
      _ = Complex.re (Matrix.trace (Matrix.conjTranspose X * X)) := by
            have hYS : rightMul (matrixSqrtPos (Φ B)) Y = X := by
              ext i j
              simp [Y, rightMul_apply, Matrix.mul_assoc, matrixInvSqrtPos_mul_matrixSqrtPos hΦB]
            rw [hYS]
  rw [hlhs]
  linarith [htrace_le, hrhs]

/-- The strict-output contraction is norm-contracting in Hilbert-Schmidt norm. -/
theorem StrictlyPositive.contraction_contractive
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ) (hSch : HSAdjointSchwarz Φ)
    (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ l)) :
    ‖StrictlyPositive.contraction Φ hPos hB hΦ1 X‖ ≤ ‖X‖ := by
  have hsq :
      ‖StrictlyPositive.contraction Φ hPos hB hΦ1 X‖ ^ 2 ≤ ‖X‖ ^ 2 := by
    calc
      ‖StrictlyPositive.contraction Φ hPos hB hΦ1 X‖ ^ 2
          = Complex.re (inner ℂ (StrictlyPositive.contraction Φ hPos hB hΦ1 X)
              (StrictlyPositive.contraction Φ hPos hB hΦ1 X)) := by
                simpa using
                  (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)
                    (x := StrictlyPositive.contraction Φ hPos hB hΦ1 X))
      _ = Complex.re
            (Matrix.trace
              (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
                StrictlyPositive.contraction Φ hPos hB hΦ1 X)) := by
                  change Complex.re
                      (Matrix.trace
                        (StrictlyPositive.contraction Φ hPos hB hΦ1 X *
                          Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X))) =
                    Complex.re
                      (Matrix.trace
                        (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
                          StrictlyPositive.contraction Φ hPos hB hΦ1 X))
                  rw [Matrix.trace_mul_comm]
      _ ≤ Complex.re (Matrix.trace (Matrix.conjTranspose X * X)) :=
            StrictlyPositive.contraction_qform_le Φ hPos hSch hB hΦ1 X
      _ = Complex.re (inner ℂ X X) := by
            change Complex.re (Matrix.trace (Matrix.conjTranspose X * X)) =
              Complex.re (Matrix.trace (X * Matrix.conjTranspose X))
            rw [Matrix.trace_mul_comm]
      _ = ‖X‖ ^ 2 := by
            simpa using
              (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (x := X)).symm
  have hnorm : ‖StrictlyPositive.contraction Φ hPos hB hΦ1 X‖ ≤ ‖X‖ := by
    nlinarith [hsq, norm_nonneg (StrictlyPositive.contraction Φ hPos hB hΦ1 X), norm_nonneg X]
  simpa using hnorm


end HiaiPetz
