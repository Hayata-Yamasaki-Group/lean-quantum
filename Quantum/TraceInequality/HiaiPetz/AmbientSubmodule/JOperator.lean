/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.Basic
import Quantum.TraceInequality.HiaiPetz.Core.JOperatorPositivity

/-!
# Positive-definite `J`-operator algebra

Private support lemmas and public consequences for positive-definite
`jArg`, `jOperator`, and their inverses.

## Main results

* `spectrum_jArg_subset_Ioi`: the real spectrum of a positive-definite
  `jArg` lies in the positive half-line.
* `jOperator_isUnit_of_posDef` and
  `ringInverse_jOperator_eq_jOperatorInv_of_posDef`: invertibility of
  `jOperator` when the scalar function is positive on `(0, ∞)`.
* `jOperator_nonneg_of_posDef`: positivity of `jOperator` for positive scalar
  functions.

## References

* Hiai, `J`-operator calculus for positive definite matrices in the
  operator convexity/monotonicity framework.
-/

namespace HiaiPetz

open scoped MatrixOrder

open scoped ComplexOrder

noncomputable section MatrixScopedInstances

attribute [local instance] instMatrixNormedAddCommGroupScoped
attribute [local instance] instMatrixNormedSpaceScoped
attribute [local instance] instMatrixInnerProductSpaceScoped
attribute [local instance] instMatrixCompleteSpaceScoped
attribute [local instance] instWithLpMatrixPairInnerProductSpace
attribute [local instance] instWithLpMatrixPairNormedSpace
attribute [local instance] instWithLpMatrixPairCompleteSpace

private theorem jArg_isUnit {n : ℕ} {A B : Mₙ n}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    IsUnit (jArg A B) := by
  have hLeft : IsUnit (leftMul A) :=
    leftMul_isUnit_of_isUnit (n := n) (Matrix.PosDef.isUnit hA)
  have hRight : IsUnit (rightMul (B⁻¹)) := by
    rcases Matrix.PosDef.isUnit hB with ⟨u, rfl⟩
    simpa using rightMul_isUnit_of_isUnit (n := n) ((u⁻¹).isUnit)
  simpa [jArg] using hRight.mul hLeft

private theorem jArg_isStrictlyPositive {n : ℕ} {A B : Mₙ n}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    IsStrictlyPositive (jArg A B) := by
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  exact (jArg_isUnit hA hB).isStrictlyPositive
    (jArg_nonneg (A := A) (B := B) (Matrix.PosDef.nonneg hA) hB)

/-- If `A` and `B` are positive definite, the real spectrum of `jArg A B` is
contained in the open positive half-line. -/
theorem spectrum_jArg_subset_Ioi {n : ℕ} {A B : Mₙ n}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    spectrum ℝ (jArg A B) ⊆ Set.Ioi (0 : ℝ) := by
  intro x hx
  exact jArg_isStrictlyPositive hA hB |>.spectrum_pos hx

/-- Positive definite inputs make `jArg A B` a strictly positive
Hilbert-Schmidt operator. -/
theorem jArg_isStrictlyPositive_of_posDef {n : ℕ} {A B : Mₙ n}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    IsStrictlyPositive (jArg A B) :=
  jArg_isStrictlyPositive hA hB

theorem jArg_mul_rightMul {n : ℕ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    jArg A B * rightMul B = leftMul A := by
  rcases Matrix.PosDef.isUnit hB with ⟨u, rfl⟩
  ext X
  simp [jArg, leftMul_apply, rightMul_apply, mul_assoc]

theorem rightMul_mul_jArg {n : ℕ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    rightMul B * jArg A B = leftMul A := by
  rcases Matrix.PosDef.isUnit hB with ⟨u, rfl⟩
  ext X
  simp [jArg, leftMul_apply, rightMul_apply, mul_assoc]

theorem hsTrace_rightMul_shift {n : ℕ} (X Y B : Mₙ n) :
    Matrix.trace (Matrix.conjTranspose X * (rightMul B Y)) =
      Matrix.trace ((Matrix.conjTranspose X * Y) * B) := by
  simp [rightMul_apply, Matrix.mul_assoc]

private theorem hsTrace_jOperator_of_posDef {n : ℕ} {f : ℝ → ℝ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) (X Y : Mₙ n) :
    Matrix.trace (Matrix.conjTranspose X * (jOperator f A B Y)) =
      Matrix.trace
        ((Matrix.conjTranspose X *
            (hsCfcR f (jArg A B) Y)) * B) := by
  have hcomm :
      Commute (hsCfcR f (jArg A B)) (rightMul B) :=
    by
      have hcomm0 : Commute (jArg A B) (rightMul B) := by
        change jArg A B * rightMul B = rightMul B * jArg A B
        rw [jArg_mul_rightMul hB, rightMul_mul_jArg hB]
      exact hcomm0.cfc_real f
  rw [jOperator, (Commute.eq hcomm)]
  simpa using
    hsTrace_rightMul_shift X (hsCfcR f (jArg A B) Y) B

/-- Trace-pairing formula for `jOperator`: its Hilbert-Schmidt quadratic form
is expressed using `hsCfcR f (jArg A B)` and right multiplication by `B`. -/
theorem hsQForm_jOperator_of_posDef {n : ℕ} {f : ℝ → ℝ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) (X Y : Mₙ n) :
    Complex.re (Matrix.trace (Matrix.conjTranspose X * (jOperator f A B Y))) =
      Complex.re
        (Matrix.trace
          ((Matrix.conjTranspose X *
              (hsCfcR f (jArg A B) Y)) * B)) := by
  rw [hsTrace_jOperator_of_posDef hB X Y]

/-- The positive inverse of a two-block diagonal positive definite matrix is
the two-block diagonal matrix of the positive inverses. -/
theorem twoBlockDiag_inv {n : ℕ} {B₁ B₂ : Mₙ n}
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    ((twoBlockDiag B₁ B₂)⁻¹) = twoBlockDiag (B₁⁻¹) (B₂⁻¹) := by
  let e : Fin (2 * n) ≃ Fin n ⊕ Fin n :=
    (finCongr (by simp [two_mul])).trans finSumFinEquiv.symm
  have hB1u : IsUnit B₁ := Matrix.PosDef.isUnit hB₁
  have hB2u : IsUnit B₂ := Matrix.PosDef.isUnit hB₂
  have hEq : IsUnit B₁ ↔ IsUnit B₂ := ⟨fun _ => hB2u, fun _ => hB1u⟩
  have hbase :
      (Matrix.reindexAlgEquiv ℂ ℂ e) (twoBlockDiag B₁ B₂) =
        Matrix.fromBlocks B₁ 0 0 B₂ := by
    simpa [Matrix.reindexAlgEquiv_apply, reindexToBlockEquiv, e, twoBlockDiag] using
      (LinearEquiv.apply_symm_apply (reindexToBlockEquiv n) (Matrix.fromBlocks B₁ 0 0 B₂))
  have hrhs :
      (Matrix.reindexAlgEquiv ℂ ℂ e) (twoBlockDiag (B₁⁻¹) (B₂⁻¹)) =
        Matrix.fromBlocks B₁⁻¹ 0 0 B₂⁻¹ := by
    simpa [Matrix.reindexAlgEquiv_apply, reindexToBlockEquiv, e, twoBlockDiag] using
      (LinearEquiv.apply_symm_apply (reindexToBlockEquiv n)
        (Matrix.fromBlocks B₁⁻¹ 0 0 B₂⁻¹))
  apply (reindexToBlockEquiv n).injective
  change (Matrix.reindexAlgEquiv ℂ ℂ e) ((twoBlockDiag B₁ B₂)⁻¹) =
    (Matrix.reindexAlgEquiv ℂ ℂ e) (twoBlockDiag (B₁⁻¹) (B₂⁻¹))
  calc
    (Matrix.reindexAlgEquiv ℂ ℂ e) ((twoBlockDiag B₁ B₂)⁻¹)
        = ((Matrix.reindexAlgEquiv ℂ ℂ e) (twoBlockDiag B₁ B₂))⁻¹ := by
            simp
    _ = (Matrix.fromBlocks B₁ 0 0 B₂)⁻¹ := by rw [hbase]
    _ = Matrix.fromBlocks B₁⁻¹ 0 0 B₂⁻¹ := by
          simpa using Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff B₁ (0 : Mₙ n) B₂ hEq
    _ = (Matrix.reindexAlgEquiv ℂ ℂ e) (twoBlockDiag (B₁⁻¹) (B₂⁻¹)) := hrhs.symm

end MatrixScopedInstances

end HiaiPetz
