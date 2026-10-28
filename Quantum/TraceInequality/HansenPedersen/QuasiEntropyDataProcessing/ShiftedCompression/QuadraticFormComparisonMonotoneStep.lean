/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.ShiftedCompression.QuadraticFormComparisonDiagCore
import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
-- The imported module names above are indivisible tokens longer than the style limit.
set_option linter.style.longLine false

/-!
# Shifted compression monotone steps
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

namespace StrictlyPositive

/-- The `p`-shifted first-operator monotone step at `X`: the real trace quadratic form of the
ambient shifted first CFC `ambientShiftedFirstPosCFC f Φ A B … p` is bounded by that of the
shifted codomain CFC `shiftedCodomainCFC f Φ A B p`. -/
def ShiftedAmbientFirstMonotoneStep
    (f : ℝ → ℝ)
    (_hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (_hI : QuasiEntropyDataProcessing.MatrixMonotoneCondition f)
    (hPos : IsPositiveMap Φ)
    (_hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (_hfirst_le :
      StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1 ≤
        jArg (Φ A) (Φ B))
    {p : ℝ} (_hp : 0 < p)
    (X : Mₙ (Nat.succ l)) :=
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.ambientShiftedFirstPosCFC f Φ A B hPos hB hΦ1 p) X))) ≤
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.shiftedCodomainCFC f Φ A B p) X)))

/-- Quadratic-form predicate at `X`: the real trace quadratic form of
`ambientShiftedFirstPosCFC f Φ A B … p` is `≤` that of `shiftedCodomainCFC f Φ A B p`. The
`ShiftedAmbientFirstMonotoneStep` inequality packaged as a reusable `Prop`. -/
def ShiftedAmbientFirstMonotoneQForm
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (p : ℝ)
    (X : Mₙ (Nat.succ l)) : Prop :=
  Complex.re
      (Matrix.trace
        (Matrix.conjTranspose X *
          ((StrictlyPositive.ambientShiftedFirstPosCFC f Φ A B hPos hB hΦ1 p) X))) ≤
    Complex.re
      (Matrix.trace
        (Matrix.conjTranspose X *
          ((StrictlyPositive.shiftedCodomainCFC f Φ A B p) X)))

/-- Operator-order predicate: `ambientShiftedFirstPosCFC f Φ A B … p ≤ shiftedCodomainCFC
  f Φ A B p`
as self-adjoint operators in `HSOp (l+1)`. The operator-level form underlying the quadratic-form
monotone step. -/
def ShiftedAmbientFirstOrderLE
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (p : ℝ) : Prop :=
  StrictlyPositive.ambientShiftedFirstPosCFC f Φ A B hPos hB hΦ1 p ≤
    StrictlyPositive.shiftedCodomainCFC f Φ A B p

end StrictlyPositive

/-- From the unshifted operator inequality `ambientFirstOperator Φ A B … ≤ jArg (Φ A) (Φ B)`,
operator monotonicity of the shift lifts the comparison to `ShiftedAmbientFirstOrderLE f Φ A B
  … p`
for every `p > 0`. -/
theorem StrictlyPositive.shiftedAmbientFirstOrderLE_of_le
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hI : QuasiEntropyDataProcessing.MatrixMonotoneCondition f)
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (hfirst_le :
      StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1 ≤
        jArg (Φ A) (Φ B))
    {p : ℝ} (hp : 0 < p) :
    StrictlyPositive.ShiftedAmbientFirstOrderLE f Φ A B hPos hB hΦ1 p := by
  letI : NormedAddCommGroup (Mₙ (Nat.succ l)) := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI : NormedSpace ℂ (Mₙ (Nat.succ l)) := instMatrixNormedSpace (n := Nat.succ l)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ l)) := instMatrixInnerProductSpace (n := Nat.succ l)
  letI : CompleteSpace (Mₙ (Nat.succ l)) := instMatrixCompleteSpace (n := Nat.succ l)
  have hmono :=
    shiftedAllHOperatorMonotone_of_matrixMonotoneCondition
      (f := f) hf hI hp
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  have hfirst_sa :
      IsSelfAdjoint (StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1) := by
    simpa [hsAdjoint] using
      StrictlyPositive.ambientFirstOperator_isSelfAdjoint
        (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1
  have himage_sa : IsSelfAdjoint (jArg (Φ A) (Φ B)) := by
    simpa [hsAdjoint] using jArg_isSelfAdjoint (A := Φ A) (B := Φ B) hΦA.1 hΦB
  have hσfirst :
      spectrum ℝ (StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1) ⊆
        HansenPedersen.halfOpenRay ⊤ := by
    exact StrictlyPositive.spectrum_ambientFirstOperator_subset_halfOpenRay
      (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1
  have hσimage :
      spectrum ℝ (jArg (Φ A) (Φ B)) ⊆ HansenPedersen.halfOpenRay ⊤ := by
    exact spectrum_jArg_subset_halfOpenRay_top hΦA hΦB
  exact
    @hmono (Mₙ (Nat.succ l))
      (instMatrixNormedAddCommGroup (n := Nat.succ l))
      (instMatrixInnerProductSpace (n := Nat.succ l))
      (instMatrixCompleteSpace (n := Nat.succ l))
      (inferInstance : ContinuousFunctionalCalculus ℝ (HSOp (Nat.succ l)) IsSelfAdjoint)
      inferInstance
      (StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1)
      (jArg (Φ A) (Φ B))
      hfirst_sa himage_sa hσfirst hσimage hfirst_le

/-- Specializes `ShiftedAmbientFirstOrderLE` to the quadratic form at `X`, yielding the monotone
step `ShiftedAmbientFirstMonotoneStep f … X` under the same hypotheses. -/
theorem StrictlyPositive.shiftedAmbientFirstMonotoneStep_of_le
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hI : QuasiEntropyDataProcessing.MatrixMonotoneCondition f)
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (hfirst_le :
      StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1 ≤
        jArg (Φ A) (Φ B))
    {p : ℝ} (hp : 0 < p)
    (X : Mₙ (Nat.succ l)) :
    StrictlyPositive.ShiftedAmbientFirstMonotoneStep
      f hf Φ (A := A) (B := B) hI hPos hA hB hΦ1 hfirst_le hp X := by
  letI : NormedAddCommGroup (Mₙ (Nat.succ l)) := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI : NormedSpace ℂ (Mₙ (Nat.succ l)) := instMatrixNormedSpace (n := Nat.succ l)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ l)) := instMatrixInnerProductSpace (n := Nat.succ l)
  letI : CompleteSpace (Mₙ (Nat.succ l)) := instMatrixCompleteSpace (n := Nat.succ l)
  have hshiftorder :=
    StrictlyPositive.shiftedAmbientFirstOrderLE_of_le
      (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B)
      hI hPos hA hB hΦ1 hfirst_le hp
  have hshiftorder0 :
      ∀ X : Mₙ (Nat.succ l),
        ↑(Complex.re
            (inner ℂ
              ((StrictlyPositive.shiftedCodomainCFC f Φ A B p -
                  StrictlyPositive.ambientShiftedFirstPosCFC f Φ A B hPos hB hΦ1 p) X)
              X)) =
          inner ℂ
            ((StrictlyPositive.shiftedCodomainCFC f Φ A B p -
                StrictlyPositive.ambientShiftedFirstPosCFC f Φ A B hPos hB hΦ1 p) X)
            X ∧
        0 ≤
          Complex.re
            (inner ℂ
              ((StrictlyPositive.shiftedCodomainCFC f Φ A B p -
                  StrictlyPositive.ambientShiftedFirstPosCFC f Φ A B hPos hB hΦ1 p) X)
              X) := by
    simpa [StrictlyPositive.ShiftedAmbientFirstOrderLE,
      ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff_complex,
      ContinuousLinearMap.sub_apply, inner_sub_left, Complex.sub_re,
      sub_nonneg] using hshiftorder
  have hshiftorder' :
      ∀ X : Mₙ (Nat.succ l),
        0 ≤
          Complex.re
            (inner ℂ
              ((StrictlyPositive.shiftedCodomainCFC f Φ A B p -
                  StrictlyPositive.ambientShiftedFirstPosCFC f Φ A B hPos hB hΦ1 p) X)
              X) := by
    intro X
    exact (hshiftorder0 X).2
  have hnonneg :
      0 ≤
        Complex.re
          (inner ℂ
            ((StrictlyPositive.shiftedCodomainCFC f Φ A B p -
                StrictlyPositive.ambientShiftedFirstPosCFC f Φ A B hPos hB hΦ1 p) X)
            X) :=
    hshiftorder' X
  have hinner :
      Complex.re
          (inner ℂ
            ((StrictlyPositive.ambientShiftedFirstPosCFC f Φ A B hPos hB hΦ1 p) X)
            X) ≤
        Complex.re
          (inner ℂ ((StrictlyPositive.shiftedCodomainCFC f Φ A B p) X) X) := by
    have hrew :
        Complex.re
            (inner ℂ
              ((StrictlyPositive.shiftedCodomainCFC f Φ A B p -
                  StrictlyPositive.ambientShiftedFirstPosCFC f Φ A B hPos hB hΦ1 p) X)
              X) =
          Complex.re
              (inner ℂ ((StrictlyPositive.shiftedCodomainCFC f Φ A B p) X) X) -
            Complex.re
              (inner ℂ
                ((StrictlyPositive.ambientShiftedFirstPosCFC f Φ A B hPos hB hΦ1 p) X)
                X) := by
      simp [ContinuousLinearMap.sub_apply, Complex.sub_re]
    rw [hrew] at hnonneg
    linarith
  simpa [StrictlyPositive.ShiftedAmbientFirstMonotoneStep,
    HiaiPetz.HilbertSchmidt.hsQForm_real_eq_inner_real_of_fun] using hinner

/-- Restates the monotone step as the quadratic-form predicate
`ShiftedAmbientFirstMonotoneQForm f Φ A B … p X`, discharged by
`shiftedAmbientFirstMonotoneStep_of_le`. -/
theorem StrictlyPositive.shiftedAmbientFirstMonotoneQForm_of_le
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hI : QuasiEntropyDataProcessing.MatrixMonotoneCondition f)
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (hfirst_le :
      StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1 ≤
        jArg (Φ A) (Φ B))
    {p : ℝ} (hp : 0 < p)
    (X : Mₙ (Nat.succ l)) :
    StrictlyPositive.ShiftedAmbientFirstMonotoneQForm
      f Φ A B hPos hB hΦ1 p X := by
  exact
    StrictlyPositive.shiftedAmbientFirstMonotoneStep_of_le
      (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B)
      hI hPos hA hB hΦ1 hfirst_le hp X

/-- Under the diagonal-core hypothesis `ShiftedAmbientDiagCoreAt` and the first-operator inequality
`ambientFirstOperator ≤ jArg (Φ A) (Φ B)`, the `p`-shifted scalar gap—the codomain
  quadratic form
minus the contracted domain quadratic form—is nonnegative for every `p > 0`. -/
theorem StrictlyPositive.shiftedScalarGap_nonneg_of_diagCoreAt_and_le
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hI : QuasiEntropyDataProcessing.MatrixMonotoneCondition f)
    (hPos : IsPositiveMap Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (hdiagCore : StrictlyPositive.ShiftedAmbientDiagCoreAt f Φ A B hPos hSch hA hB hΦ1)
    (hfirst_le :
      StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1 ≤
        jArg (Φ A) (Φ B))
    {p : ℝ} (hp : 0 < p)
    (X : Mₙ (Nat.succ l)) :
    0 ≤
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.shiftedCodomainCFC f Φ A B p) X))) -
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
            ((StrictlyPositive.shiftedDomainCFC f Φ A B p)
              (StrictlyPositive.contraction Φ hPos hB hΦ1 X)))) := by
  have hdiag :=
    StrictlyPositive.shiftedAmbientFirst_qform_le_neg_shiftedDomain_qform_of_diagCoreAt
      (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B)
      hPos hSch hA hB hΦ1 hdiagCore hp X
  have hlhs :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.shiftedAmbientFirstLhs f Φ A B hPos hB hΦ1 p) X))) =
        -Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.ambientShiftedFirstPosCFC f Φ A B hPos hB hΦ1 p) X))) := by
    exact StrictlyPositive.shiftedAmbientFirstLhs_qform_eq_neg_shiftedAmbientFirst_qform
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X
  have hmono :=
    StrictlyPositive.shiftedAmbientFirstMonotoneStep_of_le
      (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B)
      hI hPos hA hB hΦ1 hfirst_le hp X
  rw [hlhs] at hdiag
  change
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.ambientShiftedFirstPosCFC f Φ A B hPos hB hΦ1 p) X))) ≤
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.shiftedCodomainCFC f Φ A B p) X))) at hmono
  linarith

/-- Same nonnegativity of the `p`-shifted scalar gap as
`shiftedScalarGap_nonneg_of_diagCoreAt_and_le`, but obtained from the diagonal-core hypothesis
together with a supplied monotone quadratic-form hypothesis `hmono` in place of the operator
inequality. -/
theorem StrictlyPositive.shiftedScalarGap_nonneg_of_diagCoreAt_and_mono
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (hdiagCore : StrictlyPositive.ShiftedAmbientDiagCoreAt f Φ A B hPos hSch hA hB hΦ1)
    (hmono :
      ∀ {p : ℝ}, 0 < p →
        ∀ X : Mₙ (Nat.succ l),
          StrictlyPositive.ShiftedAmbientFirstMonotoneQForm
            f Φ A B hPos hB hΦ1 p X)
    {p : ℝ} (hp : 0 < p)
    (X : Mₙ (Nat.succ l)) :
    0 ≤
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.shiftedCodomainCFC f Φ A B p) X))) -
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
            ((StrictlyPositive.shiftedDomainCFC f Φ A B p)
              (StrictlyPositive.contraction Φ hPos hB hΦ1 X)))) := by
  have hdiag :=
    StrictlyPositive.shiftedAmbientFirst_qform_le_neg_shiftedDomain_qform_of_diagCoreAt
      (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B)
      hPos hSch hA hB hΦ1 hdiagCore hp X
  have hlhs :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.shiftedAmbientFirstLhs f Φ A B hPos hB hΦ1 p) X))) =
        -Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.ambientShiftedFirstPosCFC f Φ A B hPos hB hΦ1 p) X))) := by
    exact StrictlyPositive.shiftedAmbientFirstLhs_qform_eq_neg_shiftedAmbientFirst_qform
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X
  have hmonoX := hmono hp X
  rw [hlhs] at hdiag
  have hdom_le_ambient :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
              ((StrictlyPositive.shiftedDomainCFC f Φ A B p)
                (StrictlyPositive.contraction Φ hPos hB hΦ1 X)))) ≤
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.ambientShiftedFirstPosCFC f Φ A B hPos hB hΦ1 p) X))) := by
    linarith
  have hdom_le_cod :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
              ((StrictlyPositive.shiftedDomainCFC f Φ A B p)
                (StrictlyPositive.contraction Φ hPos hB hΦ1 X)))) ≤
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.shiftedCodomainCFC f Φ A B p) X))) :=
    le_trans hdom_le_ambient hmonoX
  exact sub_nonneg.mpr hdom_le_cod


end MatrixScopedInstances

end HiaiPetz
