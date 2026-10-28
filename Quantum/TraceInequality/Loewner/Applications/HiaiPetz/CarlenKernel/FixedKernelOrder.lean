/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Quantum.TraceInequality.HiaiPetz.CarlenKernel.MatrixFactor

/-!
# Carlen fixed-kernel DPI: fixed-kernel order stage

This module contains the fixed-kernel DPI stage of Carlen 2022: the
Hilbert--Schmidt operator structure, fixed inverse-form kernels, quadratic-form
order, positive multiplier inputs, contraction flips, and inverse-form DPI
aggregation.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped Matrix.Norms.Frobenius MatrixOrder CStarAlgebra ComplexOrder

/-! ### Hilbert--Schmidt Operator Structure -/
attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

/-- The Hilbert--Schmidt operator algebra `HSOp n` is a C⋆-algebra. -/
noncomputable local instance instCarlenKernelHSOpCStarAlgebra {n : ℕ} :
    CStarAlgebra (HSOp n) :=
  @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace (Mₙ n)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (instMatrixCompleteSpace (n := n))

/-- `HSOp n` is a star ring, with the operator adjoint as the star operation. -/
noncomputable local instance instCarlenKernelHSOpStarRing {n : ℕ} : StarRing (HSOp n) :=
  (instCarlenKernelHSOpCStarAlgebra (n := n)).toNonUnitalCStarAlgebra.toStarRing

/-- `HSOp n` carries the Löwner partial order inherited from the matrix inner product. -/
noncomputable local instance instCarlenKernelHSOpPartialOrder {n : ℕ} :
    PartialOrder (HSOp n) :=
  @ContinuousLinearMap.instLoewnerPartialOrder ℂ (Mₙ n) inferInstance
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))

/-- The Löwner order makes `HSOp n` a star-ordered ring. -/
noncomputable local instance instCarlenKernelHSOpStarOrderedRing {n : ℕ} :
    @StarOrderedRing (HSOp n) inferInstance (instCarlenKernelHSOpPartialOrder (n := n))
      (instCarlenKernelHSOpStarRing (n := n)) :=
  @ContinuousLinearMap.instStarOrderedRing (Mₙ n)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (instMatrixCompleteSpace (n := n))

/-- Nonnegative elements of `HSOp n` have nonnegative real spectrum. -/
noncomputable local instance instCarlenKernelHSOpNonnegSpectrumClass {n : ℕ} :
    NonnegSpectrumClass ℝ (HSOp n) :=
  @CStarAlgebra.instNonnegSpectrumClass (HSOp n)
    (instCarlenKernelHSOpCStarAlgebra (n := n))
    (instCarlenKernelHSOpPartialOrder (n := n))
    (instCarlenKernelHSOpStarOrderedRing (n := n))

noncomputable section

/-! ### Carlen Fixed-Kernel Definitions -/
/--
Inverse-form of Carlen's fixed Hiai--Petz kernel:
`t • L_{A^{-1}} + R_{B^{-1}}`.
-/
noncomputable def jKuboKernelInvForm {n : ℕ} (t : ℝ) (A B : Mₙ n) : HSOp n :=
  (t : ℂ) • leftMul (posInv A) + rightMul (posInv B)

/--
Carlen's fixed Hiai--Petz kernel, represented by the inverse form used in the
data-processing proof.
-/
noncomputable def jKuboKernel {n : ℕ} (t : ℝ) (A B : Mₙ n) : HSOp n :=
  Ring.inverse (jKuboKernelInvForm t A B)

/-- The theorem-facing kernel is definitionally the ring inverse of its inverse form. -/
theorem jKuboKernel_eq_inverse_invForm {n : ℕ} (t : ℝ) (A B : Mₙ n) :
    jKuboKernel t A B = Ring.inverse (jKuboKernelInvForm t A B) := rfl

/--
If the inverse-form kernel is a unit, then inverting the fixed kernel recovers
that inverse form.
-/
theorem jKuboKernel_inverse_eq_invForm_of_isUnit {n : ℕ} (t : ℝ) (A B : Mₙ n)
    (hu : IsUnit (jKuboKernelInvForm t A B)) :
    Ring.inverse (jKuboKernel t A B) = jKuboKernelInvForm t A B := by
  rcases hu with ⟨u, hu_eq⟩
  rw [jKuboKernel, ← hu_eq, Ring.inverse_unit]
  simp

/-- The fixed kernel inverse formula, named for the Carlen fixed-kernel DPI step. -/
theorem jKuboKernel_inv_eq {n : ℕ} (t : ℝ) (A B : Mₙ n)
    (hu : IsUnit (jKuboKernelInvForm t A B)) :
    Ring.inverse (jKuboKernel t A B) = jKuboKernelInvForm t A B :=
  jKuboKernel_inverse_eq_invForm_of_isUnit t A B hu

/-! ### Multiplication Operators and Norm Gates -/
/-- Left multiplication acts by ordinary matrix multiplication. -/
@[simp]
theorem leftMul_apply {n : ℕ} (A X : Mₙ n) :
    leftMul A X = A * X := rfl

/-- Right multiplication acts by ordinary matrix multiplication. -/
@[simp]
theorem rightMul_apply {n : ℕ} (B X : Mₙ n) :
    rightMul B X = X * B := rfl

/-- Left multiplication by a self-adjoint matrix is self-adjoint on Hilbert--Schmidt space. -/
theorem leftMul_isSelfAdjoint_of_matrix_isSelfAdjoint {n : ℕ} {A : Mₙ n}
    (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (leftMul A) := by
  refine @LinearMap.IsSymmetric.isSelfAdjoint ℂ (Mₙ n) inferInstance
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (instMatrixCompleteSpace (n := n))
    (A := leftMul A) ?_
  intro X Y
  calc
    @inner ℂ (Mₙ n) inferInstance ((leftMul A) X) Y
        = Matrix.trace (Y * Matrix.conjTranspose (A * X)) := rfl
    _ = Matrix.trace (Y * (Matrix.conjTranspose X * Matrix.conjTranspose A)) := by
          rw [Matrix.conjTranspose_mul]
    _ = Matrix.trace ((Y * Matrix.conjTranspose X) * Matrix.conjTranspose A) := by
          rw [Matrix.mul_assoc]
    _ = Matrix.trace (Matrix.conjTranspose A * (Y * Matrix.conjTranspose X)) := by
          rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (A * (Y * Matrix.conjTranspose X)) := by
          rw [hA.isHermitian.eq]
    _ = Matrix.trace ((A * Y) * Matrix.conjTranspose X) := by
          rw [Matrix.mul_assoc]
    _ = @inner ℂ (Mₙ n) inferInstance X ((leftMul A) Y) := rfl

/-- Right multiplication by a self-adjoint matrix is self-adjoint on Hilbert--Schmidt space. -/
theorem rightMul_isSelfAdjoint_of_matrix_isSelfAdjoint {n : ℕ} {B : Mₙ n}
    (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (rightMul B) := by
  refine @LinearMap.IsSymmetric.isSelfAdjoint ℂ (Mₙ n) inferInstance
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (instMatrixCompleteSpace (n := n))
    (A := rightMul B) ?_
  intro X Y
  calc
    @inner ℂ (Mₙ n) inferInstance ((rightMul B) X) Y
        = Matrix.trace (Y * Matrix.conjTranspose (X * B)) := rfl
    _ = Matrix.trace (Y * (Matrix.conjTranspose B * Matrix.conjTranspose X)) := by
          rw [Matrix.conjTranspose_mul]
    _ = Matrix.trace ((Y * Matrix.conjTranspose B) * Matrix.conjTranspose X) := by
          rw [Matrix.mul_assoc]
    _ = Matrix.trace ((Y * B) * Matrix.conjTranspose X) := by
          rw [hB.isHermitian.eq]
    _ = @inner ℂ (Mₙ n) inferInstance X ((rightMul B) Y) := rfl

/-- The inverse-form fixed kernel is self-adjoint under theorem-facing positivity. -/
theorem jKuboKernelInvForm_isSelfAdjoint_of_matrixPosDef {n : ℕ}
    {t : ℝ} {A B : Mₙ n}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    IsSelfAdjoint (jKuboKernelInvForm t A B) := by
  have hAinv : IsSelfAdjoint (posInv A) :=
    (matrixPosDef_posInv_posDef hA).isHermitian.isSelfAdjoint
  have hBinv : IsSelfAdjoint (posInv B) :=
    (matrixPosDef_posInv_posDef hB).isHermitian.isSelfAdjoint
  have hleft :
      (leftMul (posInv A)).toLinearMap.IsSymmetric :=
    @IsSelfAdjoint.isSymmetric ℂ (Mₙ n) inferInstance
      (_root_.HiaiPetz.instMatrixNormedAddCommGroup (n := n))
      (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
      (_root_.HiaiPetz.instMatrixCompleteSpace (n := n))
      (A := leftMul (posInv A))
      (leftMul_isSelfAdjoint_of_matrix_isSelfAdjoint hAinv)
  have hleft_scaled :
      ((t : ℂ) • leftMul (posInv A)).toLinearMap.IsSymmetric :=
    @LinearMap.IsSymmetric.smul ℂ (Mₙ n) inferInstance
      inferInstance
      (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
      (c := (t : ℂ)) (by simp)
      (T := (leftMul (posInv A)).toLinearMap) hleft
  have hright :
      (rightMul (posInv B)).toLinearMap.IsSymmetric :=
    @IsSelfAdjoint.isSymmetric ℂ (Mₙ n) inferInstance
      (_root_.HiaiPetz.instMatrixNormedAddCommGroup (n := n))
      (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
      (_root_.HiaiPetz.instMatrixCompleteSpace (n := n))
      (A := rightMul (posInv B))
      (rightMul_isSelfAdjoint_of_matrix_isSelfAdjoint hBinv)
  refine @LinearMap.IsSymmetric.isSelfAdjoint ℂ (Mₙ n) inferInstance
    (_root_.HiaiPetz.instMatrixNormedAddCommGroup (n := n))
    (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
    (_root_.HiaiPetz.instMatrixCompleteSpace (n := n))
    (A := jKuboKernelInvForm t A B) ?_
  simpa [jKuboKernelInvForm] using
    (@LinearMap.IsSymmetric.add ℂ (Mₙ n) inferInstance
      inferInstance
      (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
      (T := ((t : ℂ) • leftMul (posInv A)).toLinearMap)
      (S := (rightMul (posInv B)).toLinearMap)
      hleft_scaled hright)

/-- Operator norm of a Hilbert--Schmidt map with the explicit matrix Hilbert instances. -/
noncomputable def hsMapNorm {n m : ℕ} (V : HSMap n m) : ℝ :=
  @ContinuousLinearMap.opNorm ℂ ℂ (Mₙ n) (Mₙ m)
    inferInstance
    inferInstance
    inferInstance
    inferInstance
    (instMatrixNormedSpace (n := n))
    (instMatrixNormedSpace (n := m))
    (RingHom.id ℂ)
    V

/-! ### Hilbert--Schmidt Quadratic-Form Order -/
/-- Nonnegative Hilbert--Schmidt quadratic forms are closed under addition. -/
theorem HSNonneg_add {n : ℕ} {S T : HSOp n} (hS : HSNonneg S) (hT : HSNonneg T) :
    HSNonneg (S + T) := by
  intro X
  have h := add_nonneg (hS X) (hT X)
  simpa [HSNonneg, ContinuousLinearMap.add_apply, Matrix.mul_add, Matrix.trace_add,
    Complex.add_re] using h

/-- Nonnegative real scalar multiples preserve Hilbert--Schmidt nonnegativity. -/
theorem HSNonneg_smul_of_nonneg {n : ℕ} {T : HSOp n} {a : ℝ} (ha : 0 ≤ a)
    (hT : HSNonneg T) : HSNonneg ((a : ℂ) • T) := by
  intro X
  have h := mul_nonneg ha (hT X)
  change 0 ≤ Complex.re (Matrix.trace (Matrix.conjTranspose X * (((a : ℂ) • T) X)))
  rw [ContinuousLinearMap.smul_apply]
  rw [Matrix.mul_smul]
  rw [Matrix.trace_smul]
  simpa [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] using h

/-- Hilbert--Schmidt quadratic-form order is closed under addition. -/
theorem HSLE_add {n : ℕ} {S₁ T₁ S₂ T₂ : HSOp n}
    (h₁ : HSLE S₁ T₁) (h₂ : HSLE S₂ T₂) :
    HSLE (S₁ + S₂) (T₁ + T₂) := by
  have hdiff : ((T₁ + T₂) - (S₁ + S₂) : HSOp n) = (T₁ - S₁) + (T₂ - S₂) := by
    abel_nf
  rw [HSLE, hdiff]
  exact HSNonneg_add h₁ h₂

/-- Hilbert--Schmidt quadratic-form order is closed under nonnegative real scaling. -/
theorem HSLE_smul_of_nonneg {n : ℕ} {S T : HSOp n} {a : ℝ} (ha : 0 ≤ a)
    (h : HSLE S T) : HSLE ((a : ℂ) • S) ((a : ℂ) • T) := by
  have hdiff : ((a : ℂ) • T - (a : ℂ) • S : HSOp n) = (a : ℂ) • (T - S) := by
    module
  rw [HSLE, hdiff]
  exact HSNonneg_smul_of_nonneg ha h

/--
The standard Loewner order on Hilbert--Schmidt operators implies the
theorem-facing quadratic-form order `HSLE`.
-/
theorem HSLE_of_le {n : ℕ} {S T : HSOp n} (h : S ≤ T) : HSLE S T := by
  rw [HSLE]
  intro X
  change @ContinuousLinearMap.IsPositive ℂ (Mₙ n) inferInstance
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n)) (T - S) at h
  have hq :=
    @ContinuousLinearMap.IsPositive.re_inner_nonneg_right ℂ (Mₙ n) inferInstance
      (instMatrixNormedAddCommGroup (n := n)) (instMatrixInnerProductSpace (n := n))
      (T - S) h X
  change 0 ≤ Complex.re (Matrix.trace (((T - S) X) * Matrix.conjTranspose X)) at hq
  rw [Matrix.trace_mul_comm] at hq
  change 0 ≤ Complex.re (Matrix.trace (Matrix.conjTranspose X * ((T - S) X)))
  exact hq

/--
For self-adjoint differences, the theorem-facing quadratic-form order `HSLE`
returns to the standard Loewner order on Hilbert--Schmidt operators.
-/
theorem le_of_HSLE_of_isSelfAdjoint {n : ℕ} {S T : HSOp n} (h : HSLE S T)
    (hsa : IsSelfAdjoint (T - S)) : S ≤ T := by
  let U : HSOp n := T - S
  change @ContinuousLinearMap.IsPositive ℂ (Mₙ n) inferInstance
    (_root_.HiaiPetz.instMatrixNormedAddCommGroup (n := n))
    (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n)) U
  rw [@ContinuousLinearMap.isPositive_def' ℂ (Mₙ n) inferInstance
    (_root_.HiaiPetz.instMatrixNormedAddCommGroup (n := n))
    (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
    (_root_.HiaiPetz.instMatrixCompleteSpace (n := n))]
  constructor
  · exact (show IsSelfAdjoint U from by simpa [U] using hsa)
  · intro X
    have hinner : inner ℂ (U X) X = inner ℂ X (U X) := by
      have h0 :=
        @ContinuousLinearMap.adjoint_inner_right ℂ (Mₙ n) (Mₙ n) inferInstance
          (_root_.HiaiPetz.instMatrixNormedAddCommGroup (n := n))
          (_root_.HiaiPetz.instMatrixNormedAddCommGroup (n := n))
          (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
          (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
          (_root_.HiaiPetz.instMatrixCompleteSpace (n := n))
          (_root_.HiaiPetz.instMatrixCompleteSpace (n := n))
          U X X
      have hadj :
          (@ContinuousLinearMap.adjoint ℂ (Mₙ n) (Mₙ n) inferInstance
            (_root_.HiaiPetz.instMatrixNormedAddCommGroup (n := n))
            (_root_.HiaiPetz.instMatrixNormedAddCommGroup (n := n))
            (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
            (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
            (_root_.HiaiPetz.instMatrixCompleteSpace (n := n))
            (_root_.HiaiPetz.instMatrixCompleteSpace (n := n)) U) = U :=
        @IsSelfAdjoint.adjoint_eq ℂ (Mₙ n) inferInstance
          (_root_.HiaiPetz.instMatrixNormedAddCommGroup (n := n))
          (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
          (_root_.HiaiPetz.instMatrixCompleteSpace (n := n)) U
          (show IsSelfAdjoint U from by simpa [U] using hsa)
      rw [hadj] at h0
      exact h0.symm
    have hxinner : 0 ≤ RCLike.re (inner ℂ X (U X)) := by
      have hx := h X
      change 0 ≤ Complex.re (Matrix.trace (Matrix.conjTranspose X * ((T - S) X))) at hx
      change 0 ≤ Complex.re (Matrix.trace (U X * Matrix.conjTranspose X))
      rwa [Matrix.trace_mul_comm]
    change 0 ≤ RCLike.re (inner ℂ (U X) X)
    rw [hinner]
    exact hxinner

/-! ### Positive Multipliers and Kernel Spectra -/
/-- A positive semidefinite matrix has nonnegative real trace. -/
theorem re_trace_nonneg_of_posSemidef {n : ℕ} {M : Mₙ n} (hM : M.PosSemidef) :
    0 ≤ Complex.re (Matrix.trace M) := by
  have htrace := hM.trace_nonneg
  exact (Complex.nonneg_iff.mp htrace).1


/-- Positive semidefinite matrix left multiplication is nonnegative on Hilbert--Schmidt space. -/
theorem leftMul_HSNonneg_of_matrix_posSemidef {n : ℕ} {C : Mₙ n}
    (hC : C.PosSemidef) :
    HSNonneg (leftMul C) := by
  intro X
  obtain ⟨Y, hY⟩ := matrixPosSemidef_eq_conjTranspose_mul_self hC
  change 0 ≤ Complex.re (Matrix.trace (Matrix.conjTranspose X * (C * X)))
  rw [hY]
  have htrace :
      Matrix.trace (Matrix.conjTranspose X * ((Matrix.conjTranspose Y * Y) * X)) =
        Matrix.trace (Matrix.conjTranspose (Y * X) * (Y * X)) := by
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [htrace]
  exact re_trace_nonneg_of_posSemidef (Matrix.posSemidef_conjTranspose_mul_self (Y * X))

/-- Positive semidefinite matrix right multiplication is nonnegative on Hilbert--Schmidt space. -/
theorem rightMul_HSNonneg_of_matrix_posSemidef {n : ℕ} {C : Mₙ n}
    (hC : C.PosSemidef) :
    HSNonneg (rightMul C) := by
  intro X
  obtain ⟨Y, hY⟩ := matrixPosSemidef_eq_conjTranspose_mul_self hC
  change 0 ≤ Complex.re (Matrix.trace (Matrix.conjTranspose X * (X * C)))
  rw [hY]
  have htrace :
      Matrix.trace (Matrix.conjTranspose X * (X * (Matrix.conjTranspose Y * Y))) =
        Matrix.trace
          (Matrix.conjTranspose (X * Matrix.conjTranspose Y) *
            (X * Matrix.conjTranspose Y)) := by
    calc
      Matrix.trace (Matrix.conjTranspose X * (X * (Matrix.conjTranspose Y * Y)))
          = Matrix.trace ((Matrix.conjTranspose X * X) * Matrix.conjTranspose Y * Y) := by
              simp [Matrix.mul_assoc]
      _ = Matrix.trace (Y * ((Matrix.conjTranspose X * X) * Matrix.conjTranspose Y)) := by
              rw [Matrix.trace_mul_cycle]
              rw [Matrix.mul_assoc]
      _ = Matrix.trace
            (Matrix.conjTranspose (X * Matrix.conjTranspose Y) *
              (X * Matrix.conjTranspose Y)) := by
              simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
                Matrix.mul_assoc]
  rw [htrace]
  exact re_trace_nonneg_of_posSemidef
    (Matrix.posSemidef_conjTranspose_mul_self (X * Matrix.conjTranspose Y))

/-- Positive semidefinite matrix left multiplication is nonnegative in Loewner order. -/
theorem leftMul_nonneg_of_matrix_posSemidef {n : ℕ} {C : Mₙ n}
    (hC : C.PosSemidef) :
    0 ≤ (leftMul C : HSOp n) := by
  refine le_of_HSLE_of_isSelfAdjoint (S := 0) (T := leftMul C) ?_ ?_
  · have h0 : HSNonneg ((leftMul C : HSOp n) - 0) :=
      (sub_zero (leftMul C : HSOp n)).symm ▸ leftMul_HSNonneg_of_matrix_posSemidef hC
    exact h0
  · have hsa : IsSelfAdjoint ((leftMul C : HSOp n) - 0) :=
      (sub_zero (leftMul C : HSOp n)).symm ▸
        leftMul_isSelfAdjoint_of_matrix_isSelfAdjoint hC.isHermitian.isSelfAdjoint
    exact hsa

/-- Positive semidefinite matrix right multiplication is nonnegative in Loewner order. -/
theorem rightMul_nonneg_of_matrix_posSemidef {n : ℕ} {C : Mₙ n}
    (hC : C.PosSemidef) :
    0 ≤ (rightMul C : HSOp n) := by
  refine le_of_HSLE_of_isSelfAdjoint (S := 0) (T := rightMul C) ?_ ?_
  · have h0 : HSNonneg ((rightMul C : HSOp n) - 0) :=
      (sub_zero (rightMul C : HSOp n)).symm ▸ rightMul_HSNonneg_of_matrix_posSemidef hC
    exact h0
  · have hsa : IsSelfAdjoint ((rightMul C : HSOp n) - 0) :=
      (sub_zero (rightMul C : HSOp n)).symm ▸
        rightMul_isSelfAdjoint_of_matrix_isSelfAdjoint hC.isHermitian.isSelfAdjoint
    exact hsa

/-- Nonnegative real scaling preserves nonnegativity of left multiplication. -/
theorem leftMul_smul_nonneg_of_matrix_posSemidef {n : ℕ} {t : ℝ} {C : Mₙ n}
    (ht : 0 ≤ t) (hC : C.PosSemidef) :
    0 ≤ ((t : ℂ) • (leftMul C : HSOp n)) := by
  have hHS : HSNonneg ((t : ℂ) • (leftMul C : HSOp n)) :=
    HSNonneg_smul_of_nonneg ht (leftMul_HSNonneg_of_matrix_posSemidef hC)
  refine le_of_HSLE_of_isSelfAdjoint (S := 0)
    (T := ((t : ℂ) • (leftMul C : HSOp n))) ?_ ?_
  · have h0 : HSNonneg ((t : ℂ) • (leftMul C : HSOp n) - 0) :=
      (sub_zero ((t : ℂ) • (leftMul C : HSOp n))).symm ▸ hHS
    exact h0
  · have hleft :
        (leftMul C).toLinearMap.IsSymmetric :=
      @IsSelfAdjoint.isSymmetric ℂ (Mₙ n) inferInstance
        (_root_.HiaiPetz.instMatrixNormedAddCommGroup (n := n))
        (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
        (_root_.HiaiPetz.instMatrixCompleteSpace (n := n))
        (A := leftMul C)
        (leftMul_isSelfAdjoint_of_matrix_isSelfAdjoint hC.isHermitian.isSelfAdjoint)
    have hscaled :
        ((t : ℂ) • (leftMul C : HSOp n)).toLinearMap.IsSymmetric :=
      @LinearMap.IsSymmetric.smul ℂ (Mₙ n) inferInstance
        inferInstance
        (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
        (c := (t : ℂ)) (by simp)
        (T := (leftMul C).toLinearMap) hleft
    have hsa :=
      (@LinearMap.IsSymmetric.isSelfAdjoint ℂ (Mₙ n) inferInstance
        (_root_.HiaiPetz.instMatrixNormedAddCommGroup (n := n))
        (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
        (_root_.HiaiPetz.instMatrixCompleteSpace (n := n))
        (A := ((t : ℂ) • (leftMul C : HSOp n)))
        hscaled)
    exact (sub_zero ((t : ℂ) • (leftMul C : HSOp n))).symm ▸ hsa

/-- Nonnegative real scaling preserves nonnegativity of right multiplication. -/
theorem rightMul_smul_nonneg_of_matrix_posSemidef {n : ℕ} {t : ℝ} {C : Mₙ n}
    (ht : 0 ≤ t) (hC : C.PosSemidef) :
    0 ≤ ((t : ℂ) • (rightMul C : HSOp n)) := by
  have hHS : HSNonneg ((t : ℂ) • (rightMul C : HSOp n)) :=
    HSNonneg_smul_of_nonneg ht (rightMul_HSNonneg_of_matrix_posSemidef hC)
  refine le_of_HSLE_of_isSelfAdjoint (S := 0)
    (T := ((t : ℂ) • (rightMul C : HSOp n))) ?_ ?_
  · have h0 : HSNonneg ((t : ℂ) • (rightMul C : HSOp n) - 0) :=
      (sub_zero ((t : ℂ) • (rightMul C : HSOp n))).symm ▸ hHS
    exact h0
  · have hright :
        (rightMul C).toLinearMap.IsSymmetric :=
      @IsSelfAdjoint.isSymmetric ℂ (Mₙ n) inferInstance
        (_root_.HiaiPetz.instMatrixNormedAddCommGroup (n := n))
        (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
        (_root_.HiaiPetz.instMatrixCompleteSpace (n := n))
        (A := rightMul C)
        (rightMul_isSelfAdjoint_of_matrix_isSelfAdjoint hC.isHermitian.isSelfAdjoint)
    have hscaled :
        ((t : ℂ) • (rightMul C : HSOp n)).toLinearMap.IsSymmetric :=
      @LinearMap.IsSymmetric.smul ℂ (Mₙ n) inferInstance
        inferInstance
        (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
        (c := (t : ℂ)) (by simp)
        (T := (rightMul C).toLinearMap) hright
    have hsa :=
      (@LinearMap.IsSymmetric.isSelfAdjoint ℂ (Mₙ n) inferInstance
        (_root_.HiaiPetz.instMatrixNormedAddCommGroup (n := n))
        (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
        (_root_.HiaiPetz.instMatrixCompleteSpace (n := n))
        (A := ((t : ℂ) • (rightMul C : HSOp n)))
        hscaled)
    exact (sub_zero ((t : ℂ) • (rightMul C : HSOp n))).symm ▸ hsa

/-- Invertible matrix left multiplication is a unit on Hilbert--Schmidt space. -/
theorem leftMul_isUnit_of_matrix_isUnit {n : ℕ} {C : Mₙ n} (hC : IsUnit C) :
    IsUnit (leftMul C : HSOp n) := by
  rcases hC with ⟨u, rfl⟩
  refine ⟨{
    val := leftMul (u : Mₙ n)
    inv := leftMul ((↑u⁻¹ : Mₙ n))
    val_inv := ?_
    inv_val := ?_ }, rfl⟩
  · apply ContinuousLinearMap.ext
    intro X
    simp
  · apply ContinuousLinearMap.ext
    intro X
    simp

/-- Invertible matrix right multiplication is a unit on Hilbert--Schmidt space. -/
theorem rightMul_isUnit_of_matrix_isUnit {n : ℕ} {C : Mₙ n} (hC : IsUnit C) :
    IsUnit (rightMul C : HSOp n) := by
  rcases hC with ⟨u, rfl⟩
  refine ⟨{
    val := rightMul (u : Mₙ n)
    inv := rightMul ((↑u⁻¹ : Mₙ n))
    val_inv := ?_
    inv_val := ?_ }, rfl⟩
  · apply ContinuousLinearMap.ext
    intro X
    simp [Matrix.mul_assoc]
  · apply ContinuousLinearMap.ext
    intro X
    simp [Matrix.mul_assoc]

/-- Positive definite matrix left multiplication is strictly positive on Hilbert--Schmidt space. -/
theorem leftMul_isStrictlyPositive_of_matrix_posDef {n : ℕ} {C : Mₙ n}
    (hC : C.PosDef) :
    IsStrictlyPositive (leftMul C : HSOp n) :=
  (leftMul_isUnit_of_matrix_isUnit hC.isUnit).isStrictlyPositive
    (leftMul_nonneg_of_matrix_posSemidef hC.posSemidef)

/-- Positive definite matrix right multiplication is strictly positive on Hilbert--Schmidt space. -/
theorem rightMul_isStrictlyPositive_of_matrix_posDef {n : ℕ} {C : Mₙ n}
    (hC : C.PosDef) :
    IsStrictlyPositive (rightMul C : HSOp n) :=
  (rightMul_isUnit_of_matrix_isUnit hC.isUnit).isStrictlyPositive
    (rightMul_nonneg_of_matrix_posSemidef hC.posSemidef)

/-- Left and right multiplication commute on Hilbert--Schmidt space. -/
theorem leftMul_commute_rightMul {n : ℕ} (A B : Mₙ n) :
    Commute (leftMul A : HSOp n) (rightMul B : HSOp n) := by
  rw [commute_iff_eq]
  ext X i j
  simp [ContinuousLinearMap.mul_apply, Matrix.mul_assoc]

/-- `jArg A B` is the product `R_{B⁻¹} L_A`. -/
theorem jArg_eq_rightMul_mul_leftMul {n : ℕ} (A B : Mₙ n) :
    jArg A B = (rightMul (posInv B) : HSOp n) * leftMul A := by
  rfl

/-- The Hiai--Petz CFC argument is strictly positive for positive-definite inputs. -/
theorem jArg_isStrictlyPositive_of_matrixPosDef {n : ℕ} {A B : Mₙ n}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    IsStrictlyPositive (jArg A B) := by
  have hright : IsStrictlyPositive (rightMul (posInv B) : HSOp n) :=
    rightMul_isStrictlyPositive_of_matrix_posDef (matrixPosDef_posInv_posDef hB)
  have hleft : IsStrictlyPositive (leftMul A : HSOp n) :=
    leftMul_isStrictlyPositive_of_matrix_posDef (matrixPosDef_posDef hA)
  have hcomm : Commute (rightMul (posInv B) : HSOp n) (leftMul A) :=
    (leftMul_commute_rightMul A (posInv B)).symm
  have hprod : IsStrictlyPositive ((rightMul (posInv B) : HSOp n) * leftMul A) :=
    (@IsStrictlyPositive.commute_iff (HSOp n)
      inferInstance
      (instCarlenKernelHSOpPartialOrder (n := n))
      (instCarlenKernelHSOpStarRing (n := n))
      (instCarlenKernelHSOpStarOrderedRing (n := n))
      inferInstance
      inferInstance
      inferInstance
      (instCarlenKernelHSOpNonnegSpectrumClass (n := n))
      (rightMul (posInv B) : HSOp n) (leftMul A) hright hleft).mp hcomm
  simpa [jArg_eq_rightMul_mul_leftMul A B] using hprod

/-- The Hiai--Petz CFC argument is self-adjoint for positive-definite inputs. -/
theorem jArg_isSelfAdjoint_of_matrixPosDef {n : ℕ} {A B : Mₙ n}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    IsSelfAdjoint (jArg A B) := by
  rw [jArg_eq_rightMul_mul_leftMul]
  have hBinv : IsSelfAdjoint (posInv B) :=
    (matrixPosDef_posInv_posDef hB).isHermitian.isSelfAdjoint
  have hright :
      (rightMul (posInv B)).toLinearMap.IsSymmetric :=
    @IsSelfAdjoint.isSymmetric ℂ (Mₙ n) inferInstance
      (_root_.HiaiPetz.instMatrixNormedAddCommGroup (n := n))
      (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
      (_root_.HiaiPetz.instMatrixCompleteSpace (n := n))
      (A := rightMul (posInv B))
      (rightMul_isSelfAdjoint_of_matrix_isSelfAdjoint hBinv)
  have hleft :
      (leftMul A).toLinearMap.IsSymmetric :=
    @IsSelfAdjoint.isSymmetric ℂ (Mₙ n) inferInstance
      (_root_.HiaiPetz.instMatrixNormedAddCommGroup (n := n))
      (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
      (_root_.HiaiPetz.instMatrixCompleteSpace (n := n))
      (A := leftMul A)
      (leftMul_isSelfAdjoint_of_matrix_isSelfAdjoint hA.1)
  have hcomm :
      Commute (rightMul (posInv B)).toLinearMap (leftMul A).toLinearMap := by
    rw [commute_iff_eq]
    ext X i j
    simp [Matrix.mul_assoc]
  have hsymm :
      (((rightMul (posInv B) : HSOp n) * leftMul A).toLinearMap).IsSymmetric := by
    simpa using LinearMap.IsSymmetric.mul_of_commute hright hleft hcomm
  exact
    @LinearMap.IsSymmetric.isSelfAdjoint ℂ (Mₙ n) inferInstance
      (_root_.HiaiPetz.instMatrixNormedAddCommGroup (n := n))
      (_root_.HiaiPetz.instMatrixInnerProductSpace (n := n))
      (_root_.HiaiPetz.instMatrixCompleteSpace (n := n))
      (A := ((rightMul (posInv B) : HSOp n) * leftMul A : HSOp n)) hsymm

/-- The Hiai--Petz CFC argument has positive real spectrum for positive-definite inputs. -/
theorem jArg_spectrum_subset_Ioi_of_matrixPosDef {n : ℕ} {A B : Mₙ n}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    spectrum ℝ (jArg A B) ⊆ Set.Ioi (0 : ℝ) := by
  intro x hx
  exact
    @IsStrictlyPositive.spectrum_pos (HSOp n) ℝ
      inferInstance
      (instCarlenKernelHSOpPartialOrder (n := n))
      inferInstance
      inferInstance
      inferInstance
      (instCarlenKernelHSOpNonnegSpectrumClass (n := n))
      (jArg A B)
      (jArg_isStrictlyPositive_of_matrixPosDef hA hB) x hx

/-- The Hiai--Petz CFC argument has nonnegative real spectrum for positive-definite inputs. -/
theorem jArg_spectrum_subset_Ici_of_matrixPosDef {n : ℕ} {A B : Mₙ n}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    spectrum ℝ (jArg A B) ⊆ Set.Ici (0 : ℝ) := by
  intro x hx
  exact le_of_lt (by
    simpa [Set.mem_Ioi] using (jArg_spectrum_subset_Ioi_of_matrixPosDef hA hB hx))

/-- The inverse-form fixed kernel is strictly positive under theorem-facing positivity. -/
theorem jKuboKernelInvForm_isStrictlyPositive_of_matrixPosDef {n : ℕ}
    {t : ℝ} {A B : Mₙ n} (ht : 0 ≤ t)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    IsStrictlyPositive (jKuboKernelInvForm t A B) := by
  have hleft : 0 ≤ ((t : ℂ) • (leftMul (posInv A) : HSOp n)) :=
    leftMul_smul_nonneg_of_matrix_posSemidef ht
      (matrixPosDef_posInv_posDef hA).posSemidef
  have hright : IsStrictlyPositive (rightMul (posInv B) : HSOp n) :=
    rightMul_isStrictlyPositive_of_matrix_posDef (matrixPosDef_posInv_posDef hB)
  simpa [jKuboKernelInvForm] using
    @IsStrictlyPositive.nonneg_add (HSOp n)
      (instCarlenKernelHSOpCStarAlgebra (n := n))
      (instCarlenKernelHSOpPartialOrder (n := n))
      (instCarlenKernelHSOpStarOrderedRing (n := n))
      ((t : ℂ) • (leftMul (posInv A) : HSOp n))
      (rightMul (posInv B) : HSOp n) hleft hright

/-- The inverse-form fixed kernel has positive real spectrum under theorem-facing positivity. -/
theorem jKuboKernelInvForm_spectrum_subset_Ioi_of_matrixPosDef {n : ℕ}
    {t : ℝ} {A B : Mₙ n} (ht : 0 ≤ t)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    spectrum ℝ (jKuboKernelInvForm t A B) ⊆ Set.Ioi (0 : ℝ) := by
  intro x hx
  exact
    @IsStrictlyPositive.spectrum_pos (HSOp n) ℝ
      inferInstance
      (instCarlenKernelHSOpPartialOrder (n := n))
      inferInstance
      inferInstance
      inferInstance
      (instCarlenKernelHSOpNonnegSpectrumClass (n := n))
      (jKuboKernelInvForm t A B)
      (jKuboKernelInvForm_isStrictlyPositive_of_matrixPosDef ht hA hB) x hx

/-- The inverse-form fixed kernel is a unit under theorem-facing positivity. -/
theorem jKuboKernelInvForm_isUnit_of_matrixPosDef {n : ℕ}
    {t : ℝ} {A B : Mₙ n} (ht : 0 ≤ t)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    IsUnit (jKuboKernelInvForm t A B) :=
  (jKuboKernelInvForm_isStrictlyPositive_of_matrixPosDef ht hA hB).isUnit

/-! ### Carlen Contraction Flip Primitives -/
/--
The elementary C⋆-algebra contraction flip used by Carlen's finite-dimensional
kernel flip: `x * x⋆ ≤ 1` implies `x⋆ * x ≤ 1`.
-/
theorem cstar_star_mul_self_le_one_of_mul_star_self_le_one {A : Type*}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (x : A)
    (h : x * star x ≤ 1) :
    star x * x ≤ 1 := by
  have hnorm₁ : ‖x * star x‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg (x * star x)
      (mul_star_self_nonneg x)).2 h
  have hnorm₂ : ‖star x * x‖ ≤ 1 := by
    rw [CStarRing.norm_star_mul_self]
    rwa [CStarRing.norm_self_mul_star] at hnorm₁
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg (star x * x)
    (star_mul_self_nonneg x)).1 hnorm₂

/--
Rectangular contraction flip for bounded maps between Hilbert spaces.  This is
the Hilbert-space version needed for Carlen's finite-dimensional flip: from
`V† V ≤ 1` on the source space one gets `V V† ≤ 1` on the target space.
-/
theorem clm_self_comp_adjoint_le_one_of_adjoint_comp_self_le_one
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V : E →L[ℂ] F) (h : (ContinuousLinearMap.adjoint V) ∘L V ≤ 1) :
    V ∘L (ContinuousLinearMap.adjoint V) ≤ 1 := by
  have hpos_adj_comp : 0 ≤ (ContinuousLinearMap.adjoint V) ∘L V :=
    (ContinuousLinearMap.nonneg_iff_isPositive
      ((ContinuousLinearMap.adjoint V) ∘L V)).2
      (ContinuousLinearMap.isPositive_adjoint_comp_self V)
  have hnorm_adj_comp : ‖(ContinuousLinearMap.adjoint V) ∘L V‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg ((ContinuousLinearMap.adjoint V) ∘L V)
      hpos_adj_comp).2 h
  have hnormV : ‖V‖ ≤ 1 := by
    have hsquare : ‖V‖ * ‖V‖ ≤ 1 := by
      simpa [ContinuousLinearMap.norm_adjoint_comp_self] using hnorm_adj_comp
    nlinarith [norm_nonneg V]
  have hnorm_self_comp : ‖V ∘L (ContinuousLinearMap.adjoint V)‖ ≤ 1 := by
    have hcomp : ‖V ∘L (ContinuousLinearMap.adjoint V)‖ ≤
        ‖V‖ * ‖ContinuousLinearMap.adjoint V‖ :=
      V.opNorm_comp_le (ContinuousLinearMap.adjoint V)
    have hadj_norm : ‖ContinuousLinearMap.adjoint V‖ = ‖V‖ :=
      ContinuousLinearMap.adjointAux_norm V
    calc
      ‖V ∘L (ContinuousLinearMap.adjoint V)‖ ≤
          ‖V‖ * ‖ContinuousLinearMap.adjoint V‖ := hcomp
      _ = ‖V‖ * ‖V‖ := by rw [hadj_norm]
      _ ≤ 1 := by nlinarith [norm_nonneg V, hnormV]
  have hpos_self_comp : 0 ≤ V ∘L (ContinuousLinearMap.adjoint V) :=
    (ContinuousLinearMap.nonneg_iff_isPositive
      (V ∘L (ContinuousLinearMap.adjoint V))).2
      (ContinuousLinearMap.isPositive_self_comp_adjoint V)
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg
    (V ∘L (ContinuousLinearMap.adjoint V))
    hpos_self_comp).1 hnorm_self_comp

/-! ### Inverse-Form DPI Aggregation -/
/--
Conjugating the inverse-form fixed kernel by a Hilbert--Schmidt map expands into
the sum of the conjugated left and right inverse terms.
-/
theorem jKuboKernelInvForm_comp_expand {n m : ℕ} (Φ : HSMap n m)
    (t : ℝ) (A B : Mₙ m) :
    ((hsAdjoint Φ).comp ((jKuboKernelInvForm t A B).comp Φ)) =
      (t : ℂ) • ((hsAdjoint Φ).comp ((leftMul (posInv A)).comp Φ)) +
        ((hsAdjoint Φ).comp ((rightMul (posInv B)).comp Φ)) := by
  simp only [jKuboKernelInvForm, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.smul_comp]
  apply ContinuousLinearMap.ext
  intro X
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]
  change (hsAdjoint Φ)
      ((((t : ℂ) • ((leftMul (posInv A)).comp Φ)) X) +
        ((rightMul (posInv B)).comp Φ) X) = _
  rw [map_add, ContinuousLinearMap.smul_apply, map_smul]
  rfl

/--
If the two inverse terms are ordered after conjugation by `Φ`, then the full
inverse-form fixed kernel is ordered as well.
-/
theorem jKuboKernelInvForm_dpi_of_inverse_terms {n m : ℕ} (Φ : HSMap n m)
    {t : ℝ} (ht : 0 ≤ t) {A B : Mₙ n} {A' B' : Mₙ m}
    (hleft : HSLE ((hsAdjoint Φ).comp ((leftMul (posInv A')).comp Φ))
      (leftMul (posInv A)))
    (hright : HSLE ((hsAdjoint Φ).comp ((rightMul (posInv B')).comp Φ))
      (rightMul (posInv B))) :
    HSLE ((hsAdjoint Φ).comp ((jKuboKernelInvForm t A' B').comp Φ))
      (jKuboKernelInvForm t A B) := by
  let S :=
    (t : ℂ) • ((hsAdjoint Φ).comp ((leftMul (posInv A')).comp Φ)) +
      ((hsAdjoint Φ).comp ((rightMul (posInv B')).comp Φ))
  have hsum : HSLE S (jKuboKernelInvForm t A B) := by
    simpa only [S, jKuboKernelInvForm] using
      (HSLE_add (HSLE_smul_of_nonneg ht hleft) hright)
  have hexpand := jKuboKernelInvForm_comp_expand Φ t A' B'
  exact hexpand.symm ▸ hsum

end

end Quantum.TraceInequality.Loewner.HiaiPetz
