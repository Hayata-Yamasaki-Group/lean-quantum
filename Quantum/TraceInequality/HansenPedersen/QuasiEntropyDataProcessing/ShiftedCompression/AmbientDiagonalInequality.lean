/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.ShiftedCompression.AmbientDiagonalOperators
-- The imported module names above are indivisible tokens longer than the style limit.
set_option linter.style.longLine false

/-!
# Ambient diagonal compression inequalities

Quadratic-form comparisons for the ambient first compression operator: the operator-Schwarz
bound `ambientFirst_qform_le_imageJArg`, the resulting spectrum containment in the half-open
ray, and the shifted functional calculus `ambientShiftedFirstCFC` built on that operator.
-/

namespace HiaiPetz
open Matrix Unitary
open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances
open scoped HiaiPetz.RectangularOperatorInstances
noncomputable section MatrixScopedInstances

/-- The `jArg (Φ A) (Φ B)` quadratic form at `X` equals the left-multiplication form
`Re (tr (Y⋆ · ((Φ A) Y)))` with `Y = X · matrixInvSqrtPos (Φ B)`. -/
theorem image_jArg_qform_eq_imageMul_qform
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (_hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ l)) :
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((jArg (Φ A) (Φ B)) X))) =
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose (X * matrixInvSqrtPos (Φ B)) *
            ((Φ A) * (X * matrixInvSqrtPos (Φ B))))) := by
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  let U : Mₙ (Nat.succ l) := X * matrixInvSqrtPos (Φ B)
  have hsqrt_star : Matrix.conjTranspose (matrixSqrtPos (Φ B)) = matrixSqrtPos (Φ B) := by
    exact (HiaiPetz.OffDiagonalCore.matrixPosDef_sqrt hΦB).isHermitian
  have hinv_eq :
      (Φ B)⁻¹ = matrixInvSqrtPos (Φ B) * matrixInvSqrtPos (Φ B) := by
    simpa using (matrixInvSqrtPos_mul_self hΦB).symm
  have hsqrt_inv :
      matrixSqrtPos (Φ B) * (Φ B)⁻¹ = matrixInvSqrtPos (Φ B) := by
    calc
      matrixSqrtPos (Φ B) * (Φ B)⁻¹
          = matrixSqrtPos (Φ B) *
              (matrixInvSqrtPos (Φ B) * matrixInvSqrtPos (Φ B)) := by
                rw [hinv_eq]
      _ = (matrixSqrtPos (Φ B) * matrixInvSqrtPos (Φ B)) * matrixInvSqrtPos (Φ B) := by
            simp [Matrix.mul_assoc]
      _ = matrixInvSqrtPos (Φ B) := by
            simp [matrixSqrtPos_mul_matrixInvSqrtPos hΦB]
  have hX : U * matrixSqrtPos (Φ B) = X := by
    simp [U, Matrix.mul_assoc, matrixInvSqrtPos_mul_matrixSqrtPos hΦB]
  calc
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((jArg (Φ A) (Φ B)) X)))
      = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (U * matrixSqrtPos (Φ B)) *
              ((jArg (Φ A) (Φ B)) (U * matrixSqrtPos (Φ B))))) := by
              simp [hX]
    _ = Complex.re
          (Matrix.trace
            (((matrixSqrtPos (Φ B) * Matrix.conjTranspose U) * (Φ A) * U) *
              matrixInvSqrtPos (Φ B))) := by
              simp [U, jArg_apply, Matrix.mul_assoc, hsqrt_star, hsqrt_inv]
    _ = Complex.re
          (Matrix.trace
            (matrixInvSqrtPos (Φ B) *
              ((matrixSqrtPos (Φ B) * Matrix.conjTranspose U) * (Φ A) * U))) := by
              rw [Matrix.trace_mul_comm]
    _ = Complex.re
          (Matrix.trace
            ((((matrixInvSqrtPos (Φ B) * matrixSqrtPos (Φ B)) * Matrix.conjTranspose U) *
              (Φ A)) * U)) := by
              simp [Matrix.mul_assoc]
    _ = Complex.re
          (Matrix.trace (Matrix.conjTranspose U * ((Φ A) * U))) := by
              simp [Matrix.mul_assoc, matrixInvSqrtPos_mul_matrixSqrtPos hΦB]
    _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (X * matrixInvSqrtPos (Φ B)) *
              ((Φ A) * (X * matrixInvSqrtPos (Φ B))))) := by
              simp [U]

/-- The `ambientFirstOperator` quadratic form at `X` is bounded above by `Re (tr (A (Z Z⋆)))`,
where `Z = Φ⋆ (X · matrixInvSqrtPos (Φ B))`. -/
theorem StrictlyPositive.ambientFirstOperator_qform_le_hsAdjointImageMul_qform
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ l)) :
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1) X))) ≤
      Complex.re
          (Matrix.trace
            (A *
              (((hsAdjoint Φ) (X * matrixInvSqrtPos (Φ B))) *
                Matrix.conjTranspose ((hsAdjoint Φ) (X * matrixInvSqrtPos (Φ B)))))) := by
  have hq :=
    StrictlyPositive.ambientFirstOperator_qform_eq_hsAdjointImage_qform
      (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X
  rw [hq]
  let U : Mₙ (Nat.succ l) := X * matrixInvSqrtPos (Φ B)
  let Z : Mₙ (Nat.succ k) := (hsAdjoint Φ) U
  rw [Matrix.trace_mul_comm]
  simp [Matrix.mul_assoc]

/-- Operator-Schwarz comparison: the `ambientFirstOperator` quadratic form is dominated by the
image block `jArg (Φ A) (Φ B)` quadratic form, using the Schwarz property of `Φ⋆`. -/
theorem StrictlyPositive.ambientFirst_qform_le_imageJArg
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ l)) :
    Complex.re
      (Matrix.trace
        (Matrix.conjTranspose X *
          ((StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1) X)))
      ≤
    Complex.re
      (Matrix.trace
        (Matrix.conjTranspose X *
          ((jArg (Φ A) (Φ B)) X))) := by
  let U : Mₙ (Nat.succ l) := X * matrixInvSqrtPos (Φ B)
  let Z : Mₙ (Nat.succ k) := (hsAdjoint Φ) U
  have hschU :
      Z * Matrix.conjTranspose Z ≤
        (hsAdjoint Φ) (U * Matrix.conjTranspose U) := by
    simpa [U, Z] using hsAdjointSchwarz_mul_conjTranspose (Φ := Φ) hSch U
  have htrace_nonneg :
      0 ≤
        Complex.re
          (Matrix.trace
            (A * ((hsAdjoint Φ) (U * Matrix.conjTranspose U) -
              Z * Matrix.conjTranspose Z))) := by
    exact re_trace_mul_nonneg_of_posDef_nonneg hA (sub_nonneg.mpr hschU)
  have htrace_split :
      Complex.re
          (Matrix.trace
            (A * ((hsAdjoint Φ) (U * Matrix.conjTranspose U) -
              Z * Matrix.conjTranspose Z))) =
        Complex.re (Matrix.trace (A * ((hsAdjoint Φ) (U * Matrix.conjTranspose U)))) -
          Complex.re (Matrix.trace (A * (Z * Matrix.conjTranspose Z))) := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  have htrace_le :
      Complex.re (Matrix.trace (A * (Z * Matrix.conjTranspose Z))) ≤
        Complex.re (Matrix.trace (A * ((hsAdjoint Φ) (U * Matrix.conjTranspose U)))) := by
    rw [htrace_split] at htrace_nonneg
    exact sub_nonneg.mp htrace_nonneg
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  have hrhs :
      Complex.re (Matrix.trace (A * ((hsAdjoint Φ) (U * Matrix.conjTranspose U)))) =
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((jArg (Φ A) (Φ B)) X))) := by
    calc
      Complex.re (Matrix.trace (A * ((hsAdjoint Φ) (U * Matrix.conjTranspose U))))
          = Complex.re (Matrix.trace ((Φ A) * (U * Matrix.conjTranspose U))) := by
              exact ProofNet.re_trace_mul_hsAdjoint_eq Φ hA.1 hΦA.1
      _ = Complex.re
            (Matrix.trace
              (Matrix.conjTranspose U * ((Φ A) * U))) := by
              calc
                Complex.re (Matrix.trace ((Φ A) * (U * Matrix.conjTranspose U)))
                    = Complex.re
                        (Matrix.trace
                          ((U * Matrix.conjTranspose U) * (Φ A))) := by
                            rw [Matrix.trace_mul_comm]
                _ = Complex.re
                      (Matrix.trace
                        (U * (Matrix.conjTranspose U * (Φ A)))) := by
                          simp [Matrix.mul_assoc]
                _ = Complex.re
                      (Matrix.trace
                        ((Matrix.conjTranspose U * (Φ A)) * U)) := by
                          rw [Matrix.trace_mul_comm]
                _ = Complex.re
                      (Matrix.trace
                        (Matrix.conjTranspose U * ((Φ A) * U))) := by
                          simp [Matrix.mul_assoc]
      _ = Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X *
                ((jArg (Φ A) (Φ B)) X))) := by
              symm
              exact image_jArg_qform_eq_imageMul_qform
                (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1 X
  calc
    Complex.re
      (Matrix.trace
        (Matrix.conjTranspose X *
          ((StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1) X)))
        ≤ Complex.re (Matrix.trace (A * (Z * Matrix.conjTranspose Z))) := by
            simpa [U, Z] using
              StrictlyPositive.ambientFirstOperator_qform_le_hsAdjointImageMul_qform
                (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X
    _ ≤ Complex.re (Matrix.trace (A * ((hsAdjoint Φ) (U * Matrix.conjTranspose U)))) := htrace_le
    _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((jArg (Φ A) (Φ B)) X))) := hrhs

/-- The spectrum of `ambientFirstOperator` lies in the half-open ray `halfOpenRay ⊤`, since the
operator is nonnegative. -/
theorem StrictlyPositive.spectrum_ambientFirstOperator_subset_halfOpenRay
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
  spectrum ℝ (StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1) ⊆
      HansenPedersen.halfOpenRay ⊤ := by
  letI : NormedAddCommGroup (Mₙ (Nat.succ l)) := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI : NormedSpace ℂ (Mₙ (Nat.succ l)) := instMatrixNormedSpace (n := Nat.succ l)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ l)) := instMatrixInnerProductSpace (n := Nat.succ l)
  letI : CompleteSpace (Mₙ (Nat.succ l)) := instMatrixCompleteSpace (n := Nat.succ l)
  letI : NormedAddCommGroup (Mₙ (Nat.succ k)) := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI : NormedSpace ℂ (Mₙ (Nat.succ k)) := instMatrixNormedSpace (n := Nat.succ k)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ k)) := instMatrixInnerProductSpace (n := Nat.succ k)
  letI : CompleteSpace (Mₙ (Nat.succ k)) := instMatrixCompleteSpace (n := Nat.succ k)
  have hnonneg : 0 ≤ StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1 := by
    refine @le_of_quadratic_form_nonneg (Mₙ (Nat.succ l))
      (instMatrixNormedAddCommGroup (n := Nat.succ l))
      (instMatrixInnerProductSpace (n := Nat.succ l))
      (instMatrixCompleteSpace (n := Nat.succ l))
      0 (StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1) ?_ ?_
    · simpa [sub_eq_add_neg, hsAdjoint] using
        StrictlyPositive.ambientFirstOperator_isSelfAdjoint
          (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1
    · intro X
      simpa [hsQForm_real_eq_inner_real] using
        StrictlyPositive.ambientFirstOperator_trace_nonneg
          (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1 X
  exact @HansenPedersen.spectrum_subset_halfOpenRay_top_of_nonneg (Mₙ (Nat.succ l))
    (instMatrixNormedAddCommGroup (n := Nat.succ l))
    (instMatrixInnerProductSpace (n := Nat.succ l))
    (instMatrixCompleteSpace (n := Nat.succ l))
    (A := StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1)
    hnonneg

/-- The spectrum of `ambientSecondOperator` lies in the half-open ray `halfOpenRay ⊤`, since the
operator is nonnegative. -/
theorem StrictlyPositive.spectrum_ambientSecondOperator_subset_halfOpenRay
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    spectrum ℝ (StrictlyPositive.ambientSecondOperator Φ A B hPos hB hΦ1) ⊆
      HansenPedersen.halfOpenRay ⊤ :=
  letI : NormedAddCommGroup (Mₙ (Nat.succ k)) := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI : NormedSpace ℂ (Mₙ (Nat.succ k)) := instMatrixNormedSpace (n := Nat.succ k)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ k)) := instMatrixInnerProductSpace (n := Nat.succ k)
  letI : CompleteSpace (Mₙ (Nat.succ k)) := instMatrixCompleteSpace (n := Nat.succ k)
  letI : NormedAddCommGroup (Mₙ (Nat.succ l)) := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI : NormedSpace ℂ (Mₙ (Nat.succ l)) := instMatrixNormedSpace (n := Nat.succ l)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ l)) := instMatrixInnerProductSpace (n := Nat.succ l)
  letI : CompleteSpace (Mₙ (Nat.succ l)) := instMatrixCompleteSpace (n := Nat.succ l)
  have hnonneg : 0 ≤ StrictlyPositive.ambientSecondOperator Φ A B hPos hB hΦ1 := by
    refine @le_of_quadratic_form_nonneg (Mₙ (Nat.succ k))
      (instMatrixNormedAddCommGroup (n := Nat.succ k))
      (instMatrixInnerProductSpace (n := Nat.succ k))
      (instMatrixCompleteSpace (n := Nat.succ k))
      0 (StrictlyPositive.ambientSecondOperator Φ A B hPos hB hΦ1) ?_ ?_
    · simpa [sub_eq_add_neg, hsAdjoint] using
        StrictlyPositive.ambientSecondOperator_isSelfAdjoint
          (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1
    · intro X
      simpa [hsQForm_real_eq_inner_real] using
        StrictlyPositive.ambientSecondOperator_trace_nonneg
          (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1 X
  @HansenPedersen.spectrum_subset_halfOpenRay_top_of_nonneg (Mₙ (Nat.succ k))
    (instMatrixNormedAddCommGroup (n := Nat.succ k))
    (instMatrixInnerProductSpace (n := Nat.succ k))
    (instMatrixCompleteSpace (n := Nat.succ k))
    (A := StrictlyPositive.ambientSecondOperator Φ A B hPos hB hΦ1)
    hnonneg

/-- The negated `p`-shift of `f : ℝ → ℝ`: `fun t ↦ -(f (t + p))`. -/
def StrictlyPositive.shiftedNegFn (f : ℝ → ℝ) (p : ℝ) : ℝ → ℝ :=
  fun t : ℝ ↦ -(f (t + p))

/-- The shifted functional calculus of `ambientFirstOperator`: the real CFC of the negated shift
`shiftedNegFn f p` applied to the codomain compression operator. -/
noncomputable def StrictlyPositive.ambientShiftedFirstCFC
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (p : ℝ) : HSOp (Nat.succ l) :=
  hsCfcR (StrictlyPositive.shiftedNegFn f p)
    (StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1)

end MatrixScopedInstances

end HiaiPetz
