/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.ShiftedCompression

/-!
# Residual equivalence of the strict-output direct and inverse inequalities

This module closes the strict-output (`StrictlyPositive`) branch of the
Hiai–Petz data-processing theorem by proving that the direct and inverse
`J`-operator inequalities are equivalent. Each direction rewrites a compressed
kernel back to its standard quadratic form, passes through the compression /
core / ring-core operator reformulations, and bridges the two sides via the
rectangular inverse-ring reduction. The dimension cases `n, m = 0` are handled
by the zero-boundary lemmas, and the `succ/succ` case by the core bridges.

## Main results

* `StrictlyPositive.inverse_implies_direct`: the inverse `J`-operator
  inequality implies the direct one.
* `StrictlyPositive.direct_implies_inverse`: the converse implication.
* `strictlyPositiveDirect_of_matrixMonotoneCondition`: the direct inequality
  follows from the matrix-monotonicity condition on `f`.
* `QuasiEntropyDataProcessing.strictlyPositiveInverseInequality_iff_directInequality`:
  the two strict-output inequalities are equivalent.

## References

* Hiai, Theorem 6.2, output-nondegenerate cases of conditions (ii) and (iii).
-/

namespace HiaiPetz

open Matrix Unitary
open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances
private noncomputable def inverseKernelDiff
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k)) :
    HSOp (Nat.succ k) :=
  let TA : HSOp (Nat.succ k) := jOperatorInv f A B
  let TΦ : HSOp (Nat.succ k) := (hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ)
  TA - TΦ

private theorem inverseKernelDiff_isSelfAdjoint
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hB : Matrix.PosDef B) (hΦB : Matrix.PosDef (Φ B)) :
    IsSelfAdjoint (inverseKernelDiff f Φ A B) := by
  have hsource :
      IsSelfAdjoint
        (show HSOp (Nat.succ k) from
          (hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ)) := by
    have hadj := hsAdjoint_directRectOp
      (V := Φ) (TA := jOperatorInv f (Φ A) (Φ B))
      (jOperatorInv_isSelfAdjoint hΦB)
    simpa only [hsAdjoint] using hadj
  simpa [inverseKernelDiff] using (jOperatorInv_isSelfAdjoint hB).sub hsource

private theorem rewrite_inverse_to_standard_qform
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    (∀ X : Mₙ (Nat.succ k),
      0 ≤
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((inverseKernelDiff f Φ A B) X)))) →
    StrictlyPositive.InverseStandard f Φ A B := by
  intro hInv X
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  specialize hInv X
  rw [inverseKernelDiff] at hInv
  rw [hsQForm_sub, ← hsQForm_standard_jOperatorInv_of_posDef hB X X] at hInv
  have hcomp :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              (((hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ)) X))) =
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (Φ X) *
              ((jOperatorInv f (Φ A) (Φ B)) (Φ X)))) := by
    simpa using hsQForm_hsAdjoint_comp Φ (jOperatorInv f (Φ A) (Φ B)) X
  have hInv' :
      0 ≤
        (((rightMul (B⁻¹)) X)ᴴ * (hsCfcR (fun x ↦ (f x)⁻¹) (jArg A B)) X).trace.re -
          ((Φ X)ᴴ * (jOperatorInv f (Φ A) (Φ B)) (Φ X)).trace.re := by
    have hInv_le :
        (Xᴴ *
              (ContinuousLinearMap.comp (hsAdjoint Φ)
                (ContinuousLinearMap.comp (jOperatorInv f (Φ A) (Φ B)) Φ)) X).trace.re ≤
          (((rightMul (B⁻¹)) X)ᴴ * (hsCfcR (fun x ↦ (f x)⁻¹) (jArg A B)) X).trace.re := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hInv
    have hInv_le' :
        ((Φ X)ᴴ * (jOperatorInv f (Φ A) (Φ B)) (Φ X)).trace.re ≤
          (((rightMul (B⁻¹)) X)ᴴ * (hsCfcR (fun x ↦ (f x)⁻¹) (jArg A B)) X).trace.re := by
      exact hcomp.symm.le.trans hInv_le
    linarith
  rw [hsQForm_jOperatorInv_of_posDef (f := f) (A := Φ A) (B := Φ B) hΦB (Φ X) (Φ X)] at hInv'
  simpa [StrictlyPositive.inverseStandardQForm] using hInv'

private noncomputable def directKernelDiff
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k)) :
    HSOp (Nat.succ l) :=
  let TΦ : HSOp (Nat.succ l) := jOperator f (Φ A) (Φ B)
  let TA : HSOp (Nat.succ l) := Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))
  TΦ - TA

private theorem directKernelDiff_isSelfAdjoint
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hB : Matrix.PosDef B) (hΦB : Matrix.PosDef (Φ B)) :
    IsSelfAdjoint (directKernelDiff f Φ A B) := by
  have hsource :
      IsSelfAdjoint
        (show HSOp (Nat.succ l) from
          Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))) := by
    have hadj := hsAdjoint_directRectOp
      (V := hsAdjoint Φ) (TA := jOperator f A B) (jOperator_isSelfAdjoint hB)
    rw [isSelfAdjoint_iff]
    change ContinuousLinearMap.adjoint
      (Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))) =
        Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))
    simpa [directRectOp, hsAdjoint] using hadj
  simpa [directKernelDiff] using (jOperator_isSelfAdjoint hΦB).sub hsource

private theorem rewrite_direct_to_standard_qform
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    (∀ X : Mₙ (Nat.succ l),
      0 ≤
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((directKernelDiff f Φ A B) X)))) →
    StrictlyPositive.DirectStandard f Φ A B := by
  intro hDir X
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  specialize hDir X
  rw [directKernelDiff] at hDir
  rw [hsQForm_sub,
    hsQForm_jOperator_of_posDef (f := f) (A := Φ A) (B := Φ B) hΦB X X] at hDir
  have hcomp :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))) X))) =
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose ((hsAdjoint Φ) X) *
              ((jOperator f A B) ((hsAdjoint Φ) X)))) := by
    simpa using hsQForm_comp_hsAdjoint Φ (jOperator f A B) X
  have hstd :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))) X))) =
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (rightMul B ((hsAdjoint Φ) X)) *
              (hsCfcR f (jArg A B) ((hsAdjoint Φ) X)))) := by
    calc
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))) X)))
          =
            Complex.re
              (Matrix.trace
                (Matrix.conjTranspose ((hsAdjoint Φ) X) *
                  ((jOperator f A B) ((hsAdjoint Φ) X)))) := hcomp
      _ =
            Complex.re
              (Matrix.trace
                (Matrix.conjTranspose (rightMul B ((hsAdjoint Φ) X)) *
                  (hsCfcR f (jArg A B) ((hsAdjoint Φ) X)))) := by
            symm
            simpa using
              hsQForm_standard_jOperator_of_posDef hB ((hsAdjoint Φ) X) ((hsAdjoint Φ) X)
  have hDir_le :
      (Xᴴ * (ContinuousLinearMap.comp Φ
            (ContinuousLinearMap.comp (jOperator f A B) (hsAdjoint Φ))) X).trace.re ≤
        (Xᴴ * (hsCfcR f (jArg (Φ A) (Φ B))) X * Φ B).trace.re := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hDir
  have hDir_le' :
      (((rightMul B) ((hsAdjoint Φ) X))ᴴ * (hsCfcR f (jArg A B)) ((hsAdjoint Φ) X)).trace.re ≤
        (Xᴴ * (hsCfcR f (jArg (Φ A) (Φ B))) X * Φ B).trace.re := by
    exact hstd.symm.le.trans hDir_le
  have hDir' :
      0 ≤
        (Xᴴ * (hsCfcR f (jArg (Φ A) (Φ B))) X * Φ B).trace.re -
          (((rightMul B) ((hsAdjoint Φ) X))ᴴ *
              (hsCfcR f (jArg A B)) ((hsAdjoint Φ) X)).trace.re := by
    exact sub_nonneg.mpr hDir_le'
  simpa [StrictlyPositive.directStandardQForm]
    using hDir'

-- Residual compression keeps a large strict-output operator family in the declaration head.
-- The same declaration synthesizes both domain and codomain matrix Hilbert-space instances.
private def ResidualCompressionGoal
    (f : ℝ → ℝ) {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l))
    {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ) (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ 1)) : Prop :=
  StrictlyPositive.DirectCompressionOperatorNonneg f Φ A B hPos hB hΦ1

private def ShiftedAmbientFirstMonotoneGoal
    (f : ℝ → ℝ) {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l))
    {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ) (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ 1))
    (p : ℝ) (X : Mₙ (Nat.succ l)) : Prop :=
  StrictlyPositive.ShiftedAmbientFirstMonotoneQForm
    f Φ A B hPos hB hΦ1 p X

private theorem residual_compression (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hI : QuasiEntropyDataProcessing.MatrixMonotoneCondition f)
    (hPos : IsPositiveMap Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (hdiagCore :
      StrictlyPositive.ShiftedAmbientDiagCoreAt f Φ A B hPos hSch hA hB hΦ1) :
    ResidualCompressionGoal (A := A) (B := B) f Φ hPos hB hΦ1 :=
by
  letI : NormedAddCommGroup (Mₙ (Nat.succ l)) := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI : NormedSpace ℂ (Mₙ (Nat.succ l)) := instMatrixNormedSpace (n := Nat.succ l)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ l)) := instMatrixInnerProductSpace (n := Nat.succ l)
  letI : CompleteSpace (Mₙ (Nat.succ l)) := instMatrixCompleteSpace (n := Nat.succ l)
  letI : NormedAddCommGroup (Mₙ (Nat.succ k)) := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI : NormedSpace ℂ (Mₙ (Nat.succ k)) := instMatrixNormedSpace (n := Nat.succ k)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ k)) := instMatrixInnerProductSpace (n := Nat.succ k)
  letI : CompleteSpace (Mₙ (Nat.succ k)) := instMatrixCompleteSpace (n := Nat.succ k)
  have hST :
      StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1 ≤
        jArg (Φ A) (Φ B) := by
    let S : HSOp (Nat.succ l) :=
      StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1
    let T : HSOp (Nat.succ l) :=
      jArg (Φ A) (Φ B)
    have hSsa :
        IsSelfAdjoint (StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1) := by
      simpa [hsAdjoint] using
        StrictlyPositive.ambientFirstOperator_isSelfAdjoint
          (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1
    have hTsa : IsSelfAdjoint (jArg (Φ A) (Φ B)) := by
      simpa [hsAdjoint] using
        HiaiPetz.MatrixPosDef.imageJArg_isSelfAdjoint
          (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1
    have hST' : S ≤ T := by
      refine @le_of_quadratic_form_nonneg (Mₙ (Nat.succ l))
        (instMatrixNormedAddCommGroup (n := Nat.succ l))
        (instMatrixInnerProductSpace (n := Nat.succ l))
        (instMatrixCompleteSpace (n := Nat.succ l))
        S T ?_ ?_
      · exact hTsa.sub (by simpa [S] using hSsa)
      · intro ξ
        rw [show RCLike.re (inner ℂ ((T - S) ξ) ξ) =
            Complex.re (inner ℂ (T ξ) ξ) - Complex.re (inner ℂ (S ξ) ξ) by
              simp [ContinuousLinearMap.sub_apply, Complex.sub_re]]
        rw [← HiaiPetz.HilbertSchmidt.hsQForm_real_eq_inner_real_of_fun (T := fun Y => S Y) ξ]
        rw [← HiaiPetz.HilbertSchmidt.hsQForm_real_eq_inner_real_of_fun (T := fun Y => T Y) ξ]
        linarith [StrictlyPositive.ambientFirst_qform_le_imageJArg
          (Φ := Φ) (A := A) (B := B) hPos hSch hA hB hΦ1 ξ]
    simpa [S, T] using hST'
  have hshiftorder :
      ∀ {p : ℝ}, 0 < p →
        StrictlyPositive.ShiftedAmbientFirstOrderLE
          f Φ A B hPos hB hΦ1 p := by
    intro p hp
    exact
      StrictlyPositive.shiftedAmbientFirstOrderLE_of_le
        (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B)
        hI hPos hA hB hΦ1 hST hp
  have hmono :
      ∀ {p : ℝ}, 0 < p →
        ∀ X : Mₙ (Nat.succ l),
          ShiftedAmbientFirstMonotoneGoal
            (A := A) (B := B) f Φ hPos hB hΦ1 p X := by
    intro p hp X
    simpa [ShiftedAmbientFirstMonotoneGoal] using
      (StrictlyPositive.shiftedAmbientFirstMonotoneQForm_of_le
        (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B)
        hI hPos hA hB hΦ1 hST hp X)
  exact
    (by
      simpa [ResidualCompressionGoal] using
        (StrictlyPositive.directCompression_from_diagCoreAt_of_mono
      (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B)
      hPos hSch hA hB hΦ1 hdiagCore hmono))

-- This wrapper is now down to kernel-to-standard glue; the remaining cost is theorem-head whnf.
private theorem recover_direct_qform_from_standard (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.DirectStandard f Φ A B →
    ∀ X : Mₙ (Nat.succ l),
      0 ≤
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((directKernelDiff f Φ A B) X))) := by
  letI : NormedAddCommGroup (Mₙ (Nat.succ l)) := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI : NormedSpace ℂ (Mₙ (Nat.succ l)) := instMatrixNormedSpace (n := Nat.succ l)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ l)) := instMatrixInnerProductSpace (n := Nat.succ l)
  letI : CompleteSpace (Mₙ (Nat.succ l)) := instMatrixCompleteSpace (n := Nat.succ l)
  letI : NormedAddCommGroup (Mₙ (Nat.succ k)) := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI : NormedSpace ℂ (Mₙ (Nat.succ k)) := instMatrixNormedSpace (n := Nat.succ k)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ k)) := instMatrixInnerProductSpace (n := Nat.succ k)
  letI : CompleteSpace (Mₙ (Nat.succ k)) := instMatrixCompleteSpace (n := Nat.succ k)
  intro hDir X
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  have hDir' :
      0 ≤
        (Xᴴ * (hsCfcR f (jArg (Φ A) (Φ B))) X * Φ B).trace.re -
          (((rightMul B) ((hsAdjoint Φ) X))ᴴ *
              (hsCfcR f (jArg A B)) ((hsAdjoint Φ) X)).trace.re := by
    simpa [StrictlyPositive.directStandardQForm]
      using hDir X
  have hstd :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))) X))) =
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (rightMul B ((hsAdjoint Φ) X)) *
              (hsCfcR f (jArg A B) ((hsAdjoint Φ) X)))) := by
    calc
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))) X)))
          =
            Complex.re
              (Matrix.trace
                (Matrix.conjTranspose ((hsAdjoint Φ) X) *
                  ((jOperator f A B) ((hsAdjoint Φ) X)))) := by
            simpa using hsQForm_comp_hsAdjoint Φ (jOperator f A B) X
      _ =
            Complex.re
              (Matrix.trace
                (Matrix.conjTranspose (rightMul B ((hsAdjoint Φ) X)) *
                  (hsCfcR f (jArg A B) ((hsAdjoint Φ) X)))) := by
            symm
            simpa using
              hsQForm_standard_jOperator_of_posDef hB ((hsAdjoint Φ) X) ((hsAdjoint Φ) X)
  have hDir_le' :
      (((rightMul B) ((hsAdjoint Φ) X))ᴴ * (hsCfcR f (jArg A B)) ((hsAdjoint Φ) X)).trace.re ≤
        (Xᴴ * (hsCfcR f (jArg (Φ A) (Φ B))) X * Φ B).trace.re := by
    exact sub_nonneg.mp hDir'
  have hDir_le :
      (Xᴴ * (ContinuousLinearMap.comp Φ
            (ContinuousLinearMap.comp (jOperator f A B) (hsAdjoint Φ))) X).trace.re ≤
        (Xᴴ * (hsCfcR f (jArg (Φ A) (Φ B))) X * Φ B).trace.re := by
    exact hstd.trans_le hDir_le'
  rw [directKernelDiff, hsQForm_sub,
    hsQForm_jOperator_of_posDef (f := f) (A := Φ A) (B := Φ B) hΦB X X]
  exact sub_nonneg.mpr hDir_le

private theorem recover_direct_from_standard (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.DirectStandard f Φ A B →
    (show HSOp (Nat.succ l) from
      Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))) ≤
      (jOperator f (Φ A) (Φ B)) := by
  intro hDir
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  have hquad :=
    recover_direct_qform_from_standard (f := f) Φ (A := A) (B := B) hPos hB hΦ1 hDir
  refine @le_of_quadratic_form_nonneg (Mₙ (Nat.succ l))
    (instMatrixNormedAddCommGroup (n := Nat.succ l))
    (instMatrixInnerProductSpace (n := Nat.succ l))
    (instMatrixCompleteSpace (n := Nat.succ l)) _ _ ?_ ?_
  · simpa [directKernelDiff] using
      directKernelDiff_isSelfAdjoint (f := f) Φ (A := A) (B := B) hB hΦB
  · intro X
    have hx := hquad X
    change 0 ≤ Complex.re (inner ℂ ((directKernelDiff f Φ A B) X) X)
    rw [← hsQForm_real_eq_inner_real (directKernelDiff f Φ A B) X]
    exact hx

-- The inverse-to-direct core bridge expands the standard and compression forms simultaneously.
-- This bridge still needs a modest instance budget for paired matrix Hilbert-space operators.
private theorem inverse_implies_direct_core (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    (show HSOp (Nat.succ k) from
      (hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ)) ≤
      (jOperatorInv f A B) →
    (show HSOp (Nat.succ l) from
      Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))) ≤
      (jOperator f (Φ A) (Φ B)) := by
  intro hInv
  have hInv' := rewrite_inverse_to_standard_qform
    (f := f) Φ (A := A) (B := B) hPos hB hΦ1
    (by
      intro X
      have hq := hsQForm_le_of_le hInv X
      rw [inverseKernelDiff, hsQForm_sub]
      exact sub_nonneg.mpr hq)
  have hInvOp :
      StrictlyPositive.InverseCompressionOperatorNonneg f Φ A B hPos hB hΦ1 :=
    (StrictlyPositive.inverseStandard_iff_operatorNonneg
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).mp hInv'
  have hInvCore :
      StrictlyPositive.InverseCoreOperatorNonneg f Φ A B hPos hB hΦ1 :=
    (StrictlyPositive.inverseCompressionOperatorNonneg_iff_coreOperatorNonneg
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).mp hInvOp
  have hDirCore :
      StrictlyPositive.DirectCoreOperatorNonneg f Φ A B hPos hB hΦ1 := by
    have hInvRingCore :
        StrictlyPositive.InverseRingCoreOperatorNonneg f Φ A B hPos hB hΦ1 :=
      (StrictlyPositive.inverseCoreOperatorNonneg_iff_ringCoreOperatorNonneg
        (f := f) (hf := hf) (hpos := hpos) (Φ := Φ) (A := A) (B := B)
        hPos hA hB hΦ1).mp hInvCore
    have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
    have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
    have hTA0 : 0 ≤ StrictlyPositive.sourceJOp f Φ A B := by
      exact HiaiPetz.AmbientSubmodule.cfcR_jArg_nonneg (f := f) (n := Nat.succ k) (hpos := hpos)
        hA hB
    have hTΦ0 : 0 ≤ StrictlyPositive.imageJOp f Φ A B := by
      exact HiaiPetz.AmbientSubmodule.cfcR_jArg_nonneg (f := f) (n := Nat.succ l) (hpos := hpos)
        hΦA hΦB
    have hTAu : IsUnit (StrictlyPositive.sourceJOp f Φ A B) := by
      exact cfcR_jArg_isUnit (f := f) (n := Nat.succ k) (hf := hf) (hpos := hpos) hA hB
    have hTΦu : IsUnit (StrictlyPositive.imageJOp f Φ A B) := by
      exact cfcR_image_jArg_isUnit
        (f := f) (k := k) (l := l) (hf := hf) (hpos := hpos) (Φ := Φ) hPos hA hB hΦ1
    have hrect :
        StrictlyPositive.InverseCompressedLE f Φ A B hPos hB hΦ1 :=
      (StrictlyPositive.inverseRingCoreOperatorNonneg_iff_le_concrete
        (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).mp hInvRingCore
    exact
      (StrictlyPositive.directCoreOperatorNonneg_iff_le_concrete
        (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).mpr <|
        inverseRingCore_to_directCore_rect
          (StrictlyPositive.contraction (Φ := Φ) hPos hB hΦ1) hTA0 hTΦ0 hTAu hTΦu hrect
  have hDirOp :
      StrictlyPositive.DirectCompressionOperatorNonneg f Φ A B hPos hB hΦ1 :=
    (StrictlyPositive.directCompressionOperatorNonneg_iff_coreOperatorNonneg
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).mpr hDirCore
  exact recover_direct_from_standard (f := f) Φ (A := A) (B := B) hPos hB hΦ1
    ((StrictlyPositive.directStandard_iff_operatorNonneg
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).mpr hDirOp)

/-- Strict-output monotonicity, inverse ⇒ direct direction: for a positive map `Φ` and
positive-definite `A`, `B`, the compressed inverse `J`-operator inequality
`Φ* ∘ jOperatorInv f (Φ A) (Φ B) ∘ Φ ≤ jOperatorInv f A B` implies the direct one
`Φ ∘ jOperator f A B ∘ Φ* ≤ jOperator f (Φ A) (Φ B)`. All dimensions `n, m` are covered,
reducing to the `succ/succ` core bridge. -/
theorem StrictlyPositive.inverse_implies_direct (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    {n m : ℕ} (Φ : HSMap n m) {A B : Mₙ n}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) :
    (show HSOp n from
      (hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ)) ≤
      (jOperatorInv f A B) →
    (show HSOp m from Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))) ≤
      (jOperator f (Φ A) (Φ B)) := by
  cases n with
  | zero =>
      cases m with
      | zero =>
          intro hInv
          exact HiaiPetz.Core.direct_zeroCodomain (f := f) Φ
      | succ l =>
          exact False.elim (not_matrixPosDef_image_one_zeroDomain_succ Φ hΦ1)
  | succ k =>
      cases m with
      | zero =>
          intro hInv
          exact HiaiPetz.Core.direct_zeroCodomain (f := f) Φ
      | succ l =>
          intro hInv
          exact inverse_implies_direct_core
            (f := f) (hf := hf) (hpos := hpos)
            (k := k) (l := l) Φ (A := A) (B := B) hPos hA hB hΦ1 hInv

private theorem recover_inverse_from_standard (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.InverseStandard f Φ A B →
    (show HSOp (Nat.succ k) from
      (hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ)) ≤
      (jOperatorInv f A B) := by
  intro hInv
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  have hquad : ∀ X : Mₙ (Nat.succ k), 0 ≤
      Complex.re (Matrix.trace (Matrix.conjTranspose X * inverseKernelDiff f Φ A B X)) := by
    intro X
    have hInv' :
      0 ≤
        (((rightMul (B⁻¹)) X)ᴴ * (hsCfcR (fun x ↦ (f x)⁻¹) (jArg A B)) X).trace.re -
          (((Φ X)ᴴ * (hsCfcR (fun x ↦ (f x)⁻¹) (jArg (Φ A) (Φ B)) (Φ X))) *
              ((Φ B)⁻¹)).trace.re := by
      simpa [StrictlyPositive.inverseStandardQForm]
        using hInv X
    have hcomp :
      (Xᴴ *
            (ContinuousLinearMap.comp (hsAdjoint Φ)
              (ContinuousLinearMap.comp (jOperatorInv f (Φ A) (Φ B)) Φ)) X).trace.re =
        ((Φ X)ᴴ * (jOperatorInv f (Φ A) (Φ B)) (Φ X)).trace.re := by
      simpa using hsQForm_hsAdjoint_comp Φ (jOperatorInv f (Φ A) (Φ B)) X
    have hphi :
      ((Φ X)ᴴ * (jOperatorInv f (Φ A) (Φ B)) (Φ X)).trace.re =
        (((Φ X)ᴴ * (hsCfcR (fun x ↦ (f x)⁻¹) (jArg (Φ A) (Φ B)) (Φ X))) *
            ((Φ B)⁻¹)).trace.re := by
      simpa using hsQForm_jOperatorInv_of_posDef
        (f := f) (A := Φ A) (B := Φ B) hΦB (Φ X) (Φ X)
    have hInv_le' :
      (((Φ X)ᴴ * (hsCfcR (fun x ↦ (f x)⁻¹) (jArg (Φ A) (Φ B)) (Φ X))) * ((Φ
        B)⁻¹)).trace.re ≤
        (((rightMul (B⁻¹)) X)ᴴ * (hsCfcR (fun x ↦ (f x)⁻¹) (jArg A B)) X).trace.re := by
      exact sub_nonneg.mp hInv'
    have hInv_le :
      (Xᴴ *
            (ContinuousLinearMap.comp (hsAdjoint Φ)
              (ContinuousLinearMap.comp (jOperatorInv f (Φ A) (Φ B)) Φ)) X).trace.re ≤
        (((rightMul (B⁻¹)) X)ᴴ * (hsCfcR (fun x ↦ (f x)⁻¹) (jArg A B)) X).trace.re := by
      exact hcomp.trans_le (hphi.trans_le hInv_le')
    rw [inverseKernelDiff, hsQForm_sub, ← hsQForm_standard_jOperatorInv_of_posDef hB X X]
    exact sub_nonneg.mpr hInv_le
  refine @le_of_quadratic_form_nonneg (Mₙ (Nat.succ k))
    (instMatrixNormedAddCommGroup (n := Nat.succ k))
    (instMatrixInnerProductSpace (n := Nat.succ k))
    (instMatrixCompleteSpace (n := Nat.succ k)) _ _ ?_ ?_
  · simpa [inverseKernelDiff] using
      inverseKernelDiff_isSelfAdjoint (f := f) Φ (A := A) (B := B) hB hΦB
  · intro X
    have hx := hquad X
    change 0 ≤ Complex.re (inner ℂ ((inverseKernelDiff f Φ A B) X) X)
    rw [← hsQForm_real_eq_inner_real (inverseKernelDiff f Φ A B) X]
    exact hx

private def DirectMainLE
    (f : ℝ → ℝ) {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l))
    (A B : Mₙ (Nat.succ k)) : Prop :=
  (show HSOp (Nat.succ l) from
    Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))) ≤
    (jOperator f (Φ A) (Φ B))

private def InverseMainLE
    (f : ℝ → ℝ) {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l))
    (A B : Mₙ (Nat.succ k)) : Prop :=
  (show HSOp (Nat.succ k) from
    (hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ)) ≤
    (jOperatorInv f A B)

-- The direct-to-inverse core bridge expands the rectangular inverse-ring reduction.
-- The proof still synthesizes both strict-output matrix Hilbert-space layers repeatedly.
private theorem directCore_to_inverseRingCore_main
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.DirectCoreOperatorNonneg f Φ A B hPos hB hΦ1 →
    StrictlyPositive.InverseRingCoreOperatorNonneg f Φ A B hPos hB hΦ1 := by
  intro hDirCore
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction (Φ := Φ) hPos hB hΦ1
  let TA : HSOp (Nat.succ k) := StrictlyPositive.sourceJOp f Φ A B
  let TΦ : HSOp (Nat.succ l) := StrictlyPositive.imageJOp f Φ A B
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  have hTA0 : 0 ≤ TA := by
    exact HiaiPetz.AmbientSubmodule.cfcR_jArg_nonneg (f := f) (n := Nat.succ k) (hpos := hpos) hA hB
  have hTΦ0 : 0 ≤ TΦ := by
    exact HiaiPetz.AmbientSubmodule.cfcR_jArg_nonneg (f := f) (n := Nat.succ l) (hpos := hpos)
      hΦA hΦB
  have hTAu : IsUnit TA := by
    exact cfcR_jArg_isUnit (f := f) (n := Nat.succ k) (hf := hf) (hpos := hpos) hA hB
  have hTΦu : IsUnit TΦ := by
    exact cfcR_image_jArg_isUnit
      (f := f) (k := k) (l := l) (hf := hf) (hpos := hpos) (Φ := Φ) hPos hA hB hΦ1
  have hdir :
      StrictlyPositive.DirectCompressedLE f Φ A B hPos hB hΦ1 :=
    (StrictlyPositive.directCoreOperatorNonneg_iff_le_concrete
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).mp hDirCore
  have hTA_sa : IsSelfAdjoint TA := IsSelfAdjoint.of_nonneg hTA0
  have hTΦ_sa : IsSelfAdjoint TΦ := IsSelfAdjoint.of_nonneg hTΦ0
  have hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ) :=
    hsSpectrumIoi_of_nonneg_isUnit hTA0 hTAu
  have hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ) :=
    hsSpectrumIoi_of_nonneg_isUnit hTΦ0 hTΦu
  have hUUstar :
      invUUStarRectUUstarExpr V TA TΦ := by
    exact invUUStarRectUUstar_le_one_of_directRectLE_of_nonneg
      (V := V) hTA0 hTΦ0 hTAu hTΦu hdir
  have hfinal :
      InverseRectLE V TA TΦ :=
    inverseRectLE_of_invUUStarCoreRectUUstar_le_one
      (V := V) hTA_sa hTΦ_sa hσTA hσTΦ hUUstar
  exact
    (StrictlyPositive.inverseRingCoreOperatorNonneg_iff_le_concrete
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).mpr <|
      hfinal

-- The main direct-to-inverse wrapper unfolds both public Loewner-order forms and the inverse core.
-- This wrapper reuses the strict-output core bridge and keeps the instance budget local.
private theorem direct_implies_inverse_core (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    DirectMainLE f Φ A B →
    InverseMainLE f Φ A B := by
  intro hDir
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction (Φ := Φ) hPos hB hΦ1
  let TA : HSOp (Nat.succ k) := StrictlyPositive.sourceJOp f Φ A B
  let TΦ : HSOp (Nat.succ l) := StrictlyPositive.imageJOp f Φ A B
  have hDir' := rewrite_direct_to_standard_qform
    (f := f) Φ (A := A) (B := B) hPos hB hΦ1
    (by
      intro X
      have hDirLE :
          (show HSOp (Nat.succ l) from
            Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))) ≤
            jOperator f (Φ A) (Φ B) := by
        simpa [DirectMainLE] using hDir
      have hq := hsQForm_le_of_le hDirLE X
      rw [directKernelDiff, hsQForm_sub]
      exact sub_nonneg.mpr hq)
  have hDirOp :
      StrictlyPositive.DirectCompressionOperatorNonneg f Φ A B hPos hB hΦ1 :=
    (StrictlyPositive.directStandard_iff_operatorNonneg
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).mp hDir'
  have hDirCore :
      StrictlyPositive.DirectCoreOperatorNonneg f Φ A B hPos hB hΦ1 :=
    (StrictlyPositive.directCompressionOperatorNonneg_iff_coreOperatorNonneg
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).mp hDirOp
  have hInvOp :
      StrictlyPositive.InverseCompressionOperatorNonneg f Φ A B hPos hB hΦ1 := by
    have hInvRingCore :
        StrictlyPositive.InverseRingCoreOperatorNonneg f Φ A B hPos hB hΦ1 :=
      directCore_to_inverseRingCore_main
        (f := f) (hf := hf) (hpos := hpos)
        (k := k) (l := l) (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1 hDirCore
    have hInvCore :
        StrictlyPositive.InverseCoreOperatorNonneg f Φ A B hPos hB hΦ1 :=
      (StrictlyPositive.inverseCoreOperatorNonneg_iff_ringCoreOperatorNonneg
        (f := f) (hf := hf) (hpos := hpos) (Φ := Φ) (A := A) (B := B)
        hPos hA hB hΦ1).mpr hInvRingCore
    exact
      (StrictlyPositive.inverseCompressionOperatorNonneg_iff_coreOperatorNonneg
        (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).mpr hInvCore
  exact recover_inverse_from_standard (f := f) Φ (A := A) (B := B) hPos hB hΦ1
    ((StrictlyPositive.inverseStandard_iff_operatorNonneg
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).mpr hInvOp)

/-- Strict-output monotonicity, direct ⇒ inverse direction: for a positive map `Φ` and
positive-definite `A`, `B`, the direct `J`-operator inequality
`Φ ∘ jOperator f A B ∘ Φ* ≤ jOperator f (Φ A) (Φ B)` implies the compressed inverse one
`Φ* ∘ jOperatorInv f (Φ A) (Φ B) ∘ Φ ≤ jOperatorInv f A B`. All dimensions `n, m` are
covered, reducing to the `succ/succ` core bridge. -/
theorem StrictlyPositive.direct_implies_inverse (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    {n m : ℕ} (Φ : HSMap n m) {A B : Mₙ n}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) :
    (show HSOp m from Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))) ≤
      (jOperator f (Φ A) (Φ B)) →
    (show HSOp n from
      (hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ)) ≤
      (jOperatorInv f A B) := by
  cases n with
  | zero =>
      cases m with
      | zero =>
          intro hDir
          exact StrictlyPositive.inverse_zeroCodomain (f := f) (hf := hf) (hpos := hpos) Φ hA hB
      | succ l =>
          exact False.elim (not_matrixPosDef_image_one_zeroDomain_succ Φ hΦ1)
  | succ k =>
      cases m with
      | zero =>
          intro _hDir
          exact StrictlyPositive.inverse_zeroCodomain (f := f) (hf := hf) (hpos := hpos) Φ hA hB
      | succ l =>
          intro hDir
          exact direct_implies_inverse_core
            (f := f) (hf := hf) (hpos := hpos)
            (k := k) (l := l) Φ (A := A) (B := B) hPos hA hB hΦ1 hDir

private theorem strictlyPositiveDirectCompression_of_matrixMonotoneCondition (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hI : QuasiEntropyDataProcessing.MatrixMonotoneCondition f)
    (hPos : IsPositiveMap Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.DirectStandard f Φ A B := by
  have hfirstCore :
      StrictlyPositive.ShiftedAmbientDiagCoreAt f Φ A B hPos hSch hA hB hΦ1 := by
    exact shiftedAmbientDiagCoreAt_of_matrixMonotoneCondition
      (f := f) hf hpos (Φ := Φ) (A := A) (B := B) hI hPos hSch hA hB hΦ1
  have hcompOp :=
    residual_compression
      (f := f) (k := k) (l := l) Φ (A := A) (B := B) hf hI hPos hSch hA hB hΦ1 hfirstCore
  exact (StrictlyPositive.directStandard_iff_operatorNonneg
    (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).mpr hcompOp

private theorem strictlyPositiveDirectSucc_of_matrixMonotoneCondition (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hI : QuasiEntropyDataProcessing.MatrixMonotoneCondition f)
    (hPos : IsPositiveMap Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    (show HSOp (Nat.succ l) from
      Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))) ≤
      (jOperator f (Φ A) (Φ B)) := by
  exact recover_direct_from_standard
    (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1
    (strictlyPositiveDirectCompression_of_matrixMonotoneCondition
      (f := f) (k := k) (l := l) Φ (A := A) (B := B) hf hpos hI hPos hSch hA hB hΦ1)

/-- From the matrix-monotonicity condition on `f`, the direct strict-output `J`-operator
inequality `Φ ∘ jOperator f A B ∘ Φ* ≤ jOperator f (Φ A) (Φ B)` holds for every positive
map `Φ` satisfying the Hilbert–Schmidt adjoint Schwarz inequality `HSAdjointSchwarz Φ`, with
`A`, `B` positive definite. All dimensions `n, m` are covered. -/
theorem strictlyPositiveDirect_of_matrixMonotoneCondition (f : ℝ → ℝ)
    {n m : ℕ} (Φ : HSMap n m) {A B : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hI : QuasiEntropyDataProcessing.MatrixMonotoneCondition f)
    (hPos : IsPositiveMap Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) :
    (show HSOp m from Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))) ≤
      (jOperator f (Φ A) (Φ B)) := by
  cases n with
  | zero =>
      cases m with
      | zero =>
          exact HiaiPetz.Core.direct_zeroCodomain (f := f) Φ
      | succ l =>
          exact False.elim (not_matrixPosDef_image_one_zeroDomain_succ Φ hΦ1)
  | succ k =>
      cases m with
      | zero =>
          exact HiaiPetz.Core.direct_zeroCodomain (f := f) Φ
      | succ l =>
          exact strictlyPositiveDirectSucc_of_matrixMonotoneCondition
            (f := f) (k := k) (l := l) Φ (A := A) (B := B)
            hf hpos hI hPos hSch hA hB hΦ1

/-- The strict-output inverse and direct inequalities are equivalent.
Source: Hiai, Theorem 6.2, output-nondegenerate cases of conditions (ii) and (iii). -/
theorem QuasiEntropyDataProcessing.strictlyPositiveInverseInequality_iff_directInequality
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    QuasiEntropyDataProcessing.StrictlyPositiveInverseInequality f ↔
      QuasiEntropyDataProcessing.StrictlyPositiveDirectInequality f := by
  constructor
  · intro hII n m Φ A B hPos hTr hSch hA hB hΦ1
    exact StrictlyPositive.inverse_implies_direct (f := f) (hf := hf) (hpos := hpos)
      (n := n) (m := m) Φ (A := A) (B := B) hPos hA hB hΦ1
      (hII Φ (A := A) (B := B) hPos hTr hSch hA hB hΦ1)
  · intro hIII n m Φ A B hPos hTr hSch hA hB hΦ1
    exact StrictlyPositive.direct_implies_inverse (f := f) (hf := hf) (hpos := hpos)
      (n := n) (m := m) Φ (A := A) (B := B) hPos hA hB hΦ1
      (hIII Φ (A := A) (B := B) hPos hTr hSch hA hB hΦ1)

end MatrixScopedInstances

end HiaiPetz
