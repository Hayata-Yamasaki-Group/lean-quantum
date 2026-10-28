/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.ShiftedCompression.QuadraticFormComparisonMonotoneStep
import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
-- The imported module names above are indivisible tokens longer than the style limit.
set_option linter.style.longLine false

/-!
# Shifted compression limiting comparison
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

/-- As `p → 0⁺` (within `Set.Ioi 0`), the `p`-shifted scalar gap—the codomain quadratic form
`⟪X, shiftedCodomainCFC f Φ A B p X⟫` minus the contracted domain quadratic
  form—converges to the
unshifted gap built from the functional calculi `hsCfcR f (jArg (Φ A) (Φ B))` and
`hsCfcR f (jArg A B)`. -/
theorem tendsto_shiftedDirectCore_scalar_qform
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ l)) :
    Filter.Tendsto
      (fun p : ℝ =>
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.shiftedCodomainCFC f Φ A B p) X))) -
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
              ((StrictlyPositive.shiftedDomainCFC f Φ A B p)
                (StrictlyPositive.contraction Φ hPos hB hΦ1 X)))))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds
        (Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((hsCfcR f (jArg (Φ A) (Φ B))) X))) -
          Complex.re
            (Matrix.trace
              (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
                ((hsCfcR f (jArg A B))
                  (StrictlyPositive.contraction Φ hPos hB hΦ1 X)))))) := by
  /- Step 1: Record positivity of the images Φ A and Φ B. -/
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  /- Step 2: Show the codomain-side quadratic form converges to its p → 0⁺ CFC value. -/
  have hcod :
      Filter.Tendsto
        (fun p : ℝ =>
          Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X *
                ((StrictlyPositive.shiftedCodomainCFC f Φ A B p) X))))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds
          (Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X *
                ((hsCfcR f (jArg (Φ A) (Φ B))) X))))) := by
    letI := instMatrixNormedAddCommGroup (n := Nat.succ l)
    letI := instMatrixNormedSpace (n := Nat.succ l)
    letI := instMatrixInnerProductSpace (n := Nat.succ l)
    letI := instMatrixCompleteSpace (n := Nat.succ l)
    convert
      (shifted_cfc_inner_tendsto_Ioi
        (f := f)
        (K := Mₙ (Nat.succ l))
        (A := jArg (Φ A) (Φ B))
        (hA := by simpa [hsAdjoint] using jArg_isSelfAdjoint (A := Φ A) (B := Φ B) hΦA.1 hΦB)
        (hσA := spectrum_jArg_subset_Ioi_of_posDef hΦA hΦB)
        hf X) using 1
    · ext p
      calc
        Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X *
                ((StrictlyPositive.shiftedCodomainCFC f Φ A B p) X))) =
            Complex.re
              (inner ℂ ((StrictlyPositive.shiftedCodomainCFC f Φ A B p) X) X) := by
              simpa using
                (HiaiPetz.HilbertSchmidt.hsQForm_real_eq_inner_real_of_fun
                  (T := StrictlyPositive.shiftedCodomainCFC f Φ A B p) X)
        _ = Complex.re (inner ℂ X ((StrictlyPositive.shiftedCodomainCFC f Φ A B p) X)) := by
              simpa using
                (@inner_re_symm ℂ _ _
                  ((instMatrixNormedAddCommGroup (n := Nat.succ l)).toSeminormedAddCommGroup)
                  (instMatrixInnerProductSpace (n := Nat.succ l)) X
                  ((StrictlyPositive.shiftedCodomainCFC f Φ A B p) X)).symm
    · exact congrArg nhds <| by
        calc
          Complex.re
              (Matrix.trace
                (Matrix.conjTranspose X *
                  ((hsCfcR f (jArg (Φ A) (Φ B))) X))) =
              Complex.re (inner ℂ ((hsCfcR f (jArg (Φ A) (Φ B))) X) X) := by
                simpa using
                  (HiaiPetz.HilbertSchmidt.hsQForm_real_eq_inner_real_of_fun
                    (T := hsCfcR f (jArg (Φ A) (Φ B))) X)
          _ = Complex.re (inner ℂ X ((hsCfcR f (jArg (Φ A) (Φ B))) X)) := by
                simpa using
                  (@inner_re_symm ℂ _ _
                    ((instMatrixNormedAddCommGroup
                        (n := Nat.succ l)).toSeminormedAddCommGroup)
                    (instMatrixInnerProductSpace (n := Nat.succ l)) X ((hsCfcR f (jArg (Φ A) (Φ
                      B))) X)).symm
  /- Step 3: Show the contracted domain-side quadratic form converges likewise. -/
  have hdom :
      Filter.Tendsto
        (fun p : ℝ =>
          Complex.re
            (Matrix.trace
              (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
                ((StrictlyPositive.shiftedDomainCFC f Φ A B p)
                  (StrictlyPositive.contraction Φ hPos hB hΦ1 X)))))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds
          (Complex.re
            (Matrix.trace
              (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
                ((hsCfcR f (jArg A B))
                  (StrictlyPositive.contraction Φ hPos hB hΦ1 X)))))) := by
    letI := instMatrixNormedAddCommGroup (n := Nat.succ k)
    letI := instMatrixNormedSpace (n := Nat.succ k)
    letI := instMatrixInnerProductSpace (n := Nat.succ k)
    letI := instMatrixCompleteSpace (n := Nat.succ k)
    convert
      (shifted_cfc_inner_tendsto_Ioi
        (f := f)
        (K := Mₙ (Nat.succ k))
        (A := jArg A B)
        (hA := by simpa [hsAdjoint] using jArg_isSelfAdjoint (A := A) (B := B) hA.1 hB)
        (hσA := spectrum_jArg_subset_Ioi_of_posDef hA hB)
        hf (StrictlyPositive.contraction Φ hPos hB hΦ1 X)) using 1
    · ext p
      calc
        Complex.re
            (Matrix.trace
              (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
                ((StrictlyPositive.shiftedDomainCFC f Φ A B p)
                  (StrictlyPositive.contraction Φ hPos hB hΦ1 X)))) =
            Complex.re
              (inner ℂ
                ((StrictlyPositive.shiftedDomainCFC f Φ A B p)
                  (StrictlyPositive.contraction Φ hPos hB hΦ1 X))
                (StrictlyPositive.contraction Φ hPos hB hΦ1 X)) := by
              simpa using
                (HiaiPetz.HilbertSchmidt.hsQForm_real_eq_inner_real_of_fun
                  (T := StrictlyPositive.shiftedDomainCFC f Φ A B p)
                  (X := StrictlyPositive.contraction Φ hPos hB hΦ1 X))
        _ = Complex.re
              (inner ℂ (StrictlyPositive.contraction Φ hPos hB hΦ1 X)
                ((StrictlyPositive.shiftedDomainCFC f Φ A B p)
                  (StrictlyPositive.contraction Φ hPos hB hΦ1 X))) := by
              simpa using
                (@inner_re_symm ℂ _ _
                  ((instMatrixNormedAddCommGroup).toSeminormedAddCommGroup)
                  (instMatrixInnerProductSpace)
                  (StrictlyPositive.contraction Φ hPos hB hΦ1 X)
                  ((StrictlyPositive.shiftedDomainCFC f Φ A B p)
                    (StrictlyPositive.contraction Φ hPos hB hΦ1 X))).symm
    · exact congrArg nhds <| by
        calc
          Complex.re
              (Matrix.trace
                (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
                  ((hsCfcR f (jArg A B)) (StrictlyPositive.contraction Φ hPos hB hΦ1 X)))) =
              Complex.re
                (inner ℂ ((hsCfcR f (jArg A B)) (StrictlyPositive.contraction Φ hPos hB hΦ1 X))
                  (StrictlyPositive.contraction Φ hPos hB hΦ1 X)) := by
                simpa using
                  (HiaiPetz.HilbertSchmidt.hsQForm_real_eq_inner_real_of_fun
                    (T := hsCfcR f (jArg A B))
                    (X := StrictlyPositive.contraction Φ hPos hB hΦ1 X))
          _ = Complex.re
                (inner ℂ (StrictlyPositive.contraction Φ hPos hB hΦ1 X)
                  ((hsCfcR f (jArg A B)) (StrictlyPositive.contraction Φ hPos hB hΦ1 X))) := by
                simpa using
                  (@inner_re_symm ℂ _ _
                    ((instMatrixNormedAddCommGroup).toSeminormedAddCommGroup)
                    (instMatrixInnerProductSpace)
                    (StrictlyPositive.contraction Φ hPos hB hΦ1 X)
                    ((hsCfcR f (jArg A B)) (StrictlyPositive.contraction Φ hPos hB hΦ1 X))).symm
  /- Step 4: Subtract the two convergent forms to obtain the limit of their difference. -/
  exact hcod.sub hdom

/-- Passes the `p > 0` scalar-gap nonnegativity to the `p → 0⁺` limit, proving
`DirectCoreOperatorNonneg f Φ A B …` from the diagonal-core hypothesis and the first-operator
inequality `ambientFirstOperator ≤ jArg (Φ A) (Φ B)`. -/
theorem StrictlyPositive.directCore_nonneg_from_diagCoreAt_of_le
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)} :
    ∀ (_hI : QuasiEntropyDataProcessing.MatrixMonotoneCondition f)
      (hPos : IsPositiveMap Φ)
      (hSch : HSAdjointSchwarz Φ)
      (hA : Matrix.PosDef A)
      (hB : Matrix.PosDef B)
      (hΦ1 : Matrix.PosDef (Φ 1))
      (_hdiagCore :
        StrictlyPositive.ShiftedAmbientDiagCoreAt f Φ A B hPos hSch hA hB hΦ1)
      (_hfirst_le :
        StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1 ≤
          jArg (Φ A) (Φ B)),
        StrictlyPositive.DirectCoreOperatorNonneg f Φ A B hPos hB hΦ1 := by
  intro hI hPos hSch hA hB hΦ1 hdiagCore hfirst_le X
  /- Step 1: Define the scalar gap between the codomain and domain quadratic forms in p. -/
  let gap : ℝ → ℝ := fun p : ℝ =>
    Complex.re
      (Matrix.trace
        (Matrix.conjTranspose X *
          ((StrictlyPositive.shiftedCodomainCFC f Φ A B p) X))) -
    Complex.re
      (Matrix.trace
        (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
          ((StrictlyPositive.shiftedDomainCFC f Φ A B p)
            (StrictlyPositive.contraction Φ hPos hB hΦ1 X))))
  /- Step 2: Make the gap nonnegative for every p > 0 via the diagonal-core hypothesis. -/
  have hgap :
      ∀ᶠ p : ℝ in nhdsWithin 0 (Set.Ioi (0 : ℝ)), gap p ∈ Set.Ici (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact StrictlyPositive.shiftedScalarGap_nonneg_of_diagCoreAt_and_le
      (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B)
      hI hPos hSch hA hB hΦ1 hdiagCore hfirst_le hp X
  /- Step 3: Pass nonnegativity to the p → 0⁺ limit using closedness of [0, ∞). -/
  let limitVal : ℝ :=
    Complex.re
      (Matrix.trace
        (Matrix.conjTranspose X *
          ((hsCfcR f (jArg (Φ A) (Φ B))) X))) -
    Complex.re
      (Matrix.trace
        (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
          ((hsCfcR f (jArg A B))
            (StrictlyPositive.contraction Φ hPos hB hΦ1 X))))
  have htendsto :=
    tendsto_shiftedDirectCore_scalar_qform
      (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B)
      hPos hA hB hΦ1 X
  have hlimit_mem : limitVal ∈ Set.Ici (0 : ℝ) := by
    exact IsClosed.mem_of_tendsto isClosed_Ici
      (by simpa [gap, limitVal] using htendsto)
      hgap
  have hgap0 : 0 ≤ limitVal := hlimit_mem
  /- Step 4: Identify the direct-core operator quadratic form with that limit value and conclude. -/
  have hcomp :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              (((hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)).comp
                  ((hsCfcR f (jArg A B)).comp (StrictlyPositive.contraction Φ hPos hB hΦ1)))
                    X))) =
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
              ((hsCfcR f (jArg A B)) (StrictlyPositive.contraction Φ hPos hB hΦ1 X)))) := by
    simpa using
      hsQForm_hsAdjoint_comp
        (StrictlyPositive.contraction Φ hPos hB hΦ1)
        (hsCfcR f (jArg A B))
        X
  have hqform :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.directCoreOperator f Φ A B hPos hB hΦ1) X))) =
        limitVal := by
    calc
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.directCoreOperator f Φ A B hPos hB hΦ1) X)))
        =
          Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X *
                ((hsCfcR f (jArg (Φ A) (Φ B))) X))) -
          Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X *
                (((hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)).comp
                    ((hsCfcR f (jArg A B)).comp
                      (StrictlyPositive.contraction Φ hPos hB hΦ1))) X))) := by
              let TΦ : HSOp (Nat.succ l) := hsCfcR f (jArg (Φ A) (Φ B))
              let TV : HSOp (Nat.succ l) :=
                (hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)).comp
                  ((hsCfcR f (jArg A B)).comp (StrictlyPositive.contraction Φ hPos hB hΦ1))
              change
                Complex.re
                    (Matrix.trace
                      (Matrix.conjTranspose X * ((TΦ - TV) X))) =
                  Complex.re
                    (Matrix.trace
                      (Matrix.conjTranspose X * (TΦ X))) -
                    Complex.re
                      (Matrix.trace
                        (Matrix.conjTranspose X * (TV X)))
              simp [ContinuousLinearMap.sub_apply, Matrix.mul_sub, Matrix.trace_sub,
                Complex.sub_re, TΦ, TV]
      _ =
          Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X *
                ((hsCfcR f (jArg (Φ A) (Φ B))) X))) -
          Complex.re
            (Matrix.trace
              (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
                ((hsCfcR f (jArg A B)) (StrictlyPositive.contraction Φ hPos hB hΦ1 X)))) := by
              rw [hcomp]
      _ = limitVal := rfl
  rw [hqform]
  exact hgap0

/-- Transfers `directCore_nonneg_from_diagCoreAt_of_le` across the core/compression equivalence
`directCompressionOperatorNonneg_iff_coreOperatorNonneg` to conclude
`DirectCompressionOperatorNonneg f Φ A B …`. -/
theorem StrictlyPositive.directCompression_from_diagCoreAt_of_le
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)} :
    ∀ (_hI : QuasiEntropyDataProcessing.MatrixMonotoneCondition f)
      (hPos : IsPositiveMap Φ)
      (hSch : HSAdjointSchwarz Φ)
      (hA : Matrix.PosDef A)
      (hB : Matrix.PosDef B)
      (hΦ1 : Matrix.PosDef (Φ 1))
      (_hdiagCore :
        StrictlyPositive.ShiftedAmbientDiagCoreAt f Φ A B hPos hSch hA hB hΦ1)
      (_hfirst_le :
        StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1 ≤
          jArg (Φ A) (Φ B)),
        StrictlyPositive.DirectCompressionOperatorNonneg f Φ A B hPos hB hΦ1 := by
  intro hI hPos hSch hA hB hΦ1 hdiagCore hfirst_le
  exact
    (StrictlyPositive.directCompressionOperatorNonneg_iff_coreOperatorNonneg
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).mpr <|
      StrictlyPositive.directCore_nonneg_from_diagCoreAt_of_le
        (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B)
        hI hPos hSch hA hB hΦ1 hdiagCore hfirst_le

/-- Variant of `directCore_nonneg_from_diagCoreAt_of_le` deriving
`DirectCoreOperatorNonneg f Φ A B …` from the diagonal-core hypothesis together with a supplied
monotone quadratic-form hypothesis in
place of the first-operator inequality. -/
theorem StrictlyPositive.directCore_nonneg_from_diagCoreAt_of_mono
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)} :
    ∀ (hPos : IsPositiveMap Φ)
      (hSch : HSAdjointSchwarz Φ)
      (hA : Matrix.PosDef A)
      (hB : Matrix.PosDef B)
      (hΦ1 : Matrix.PosDef (Φ 1))
      (_hdiagCore :
        StrictlyPositive.ShiftedAmbientDiagCoreAt f Φ A B hPos hSch hA hB hΦ1)
      (_hmono :
        ∀ {p : ℝ}, 0 < p →
          ∀ X : Mₙ (Nat.succ l),
            StrictlyPositive.ShiftedAmbientFirstMonotoneQForm
              f Φ A B hPos hB hΦ1 p X),
        StrictlyPositive.DirectCoreOperatorNonneg f Φ A B hPos hB hΦ1 := by
  intro hPos hSch hA hB hΦ1 hdiagCore hmono X
  /- Step 1: Define the scalar gap between the codomain and domain quadratic forms in p. -/
  let gap : ℝ → ℝ := fun p : ℝ =>
    Complex.re
      (Matrix.trace
        (Matrix.conjTranspose X *
          ((StrictlyPositive.shiftedCodomainCFC f Φ A B p) X))) -
    Complex.re
      (Matrix.trace
        (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
          ((StrictlyPositive.shiftedDomainCFC f Φ A B p)
            (StrictlyPositive.contraction Φ hPos hB hΦ1 X))))
  /- Step 2: Make the gap nonnegative for every p > 0 via the diagonal-core hypothesis. -/
  have hgap :
      ∀ᶠ p : ℝ in nhdsWithin 0 (Set.Ioi (0 : ℝ)), gap p ∈ Set.Ici (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact StrictlyPositive.shiftedScalarGap_nonneg_of_diagCoreAt_and_mono
      (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B)
      hPos hSch hA hB hΦ1 hdiagCore hmono hp X
  /- Step 3: Pass nonnegativity to the p → 0⁺ limit using closedness of [0, ∞). -/
  let limitVal : ℝ :=
    Complex.re
      (Matrix.trace
        (Matrix.conjTranspose X *
          ((hsCfcR f (jArg (Φ A) (Φ B))) X))) -
    Complex.re
      (Matrix.trace
        (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
          ((hsCfcR f (jArg A B))
            (StrictlyPositive.contraction Φ hPos hB hΦ1 X))))
  have htendsto :=
    tendsto_shiftedDirectCore_scalar_qform
      (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B)
      hPos hA hB hΦ1 X
  have hlimit_mem : limitVal ∈ Set.Ici (0 : ℝ) := by
    exact IsClosed.mem_of_tendsto isClosed_Ici
      (by simpa [gap, limitVal] using htendsto)
      hgap
  have hgap0 : 0 ≤ limitVal := hlimit_mem
  /- Step 4: Identify the direct-core operator quadratic form with that limit value and conclude. -/
  have hcomp :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              (((hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)).comp
                  ((hsCfcR f (jArg A B)).comp (StrictlyPositive.contraction Φ hPos hB hΦ1)))
                    X))) =
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
              ((hsCfcR f (jArg A B)) (StrictlyPositive.contraction Φ hPos hB hΦ1 X)))) := by
    simpa using
      hsQForm_hsAdjoint_comp
        (StrictlyPositive.contraction Φ hPos hB hΦ1)
        (hsCfcR f (jArg A B))
        X
  have hqform :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.directCoreOperator f Φ A B hPos hB hΦ1) X))) =
        limitVal := by
    calc
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.directCoreOperator f Φ A B hPos hB hΦ1) X)))
        =
          Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X *
                ((hsCfcR f (jArg (Φ A) (Φ B))) X))) -
          Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X *
                (((hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)).comp
                    ((hsCfcR f (jArg A B)).comp
                      (StrictlyPositive.contraction Φ hPos hB hΦ1))) X))) := by
              let TΦ : HSOp (Nat.succ l) := hsCfcR f (jArg (Φ A) (Φ B))
              let TV : HSOp (Nat.succ l) :=
                (hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)).comp
                  ((hsCfcR f (jArg A B)).comp (StrictlyPositive.contraction Φ hPos hB hΦ1))
              change
                Complex.re
                    (Matrix.trace
                      (Matrix.conjTranspose X * ((TΦ - TV) X))) =
                  Complex.re
                    (Matrix.trace
                      (Matrix.conjTranspose X * (TΦ X))) -
                    Complex.re
                      (Matrix.trace
                        (Matrix.conjTranspose X * (TV X)))
              simp [ContinuousLinearMap.sub_apply, Matrix.mul_sub, Matrix.trace_sub,
                Complex.sub_re, TΦ, TV]
      _ =
          Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X *
                ((hsCfcR f (jArg (Φ A) (Φ B))) X))) -
          Complex.re
            (Matrix.trace
              (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
                ((hsCfcR f (jArg A B)) (StrictlyPositive.contraction Φ hPos hB hΦ1 X)))) := by
              rw [hcomp]
      _ = limitVal := rfl
  rw [hqform]
  exact hgap0

/-- Transfers `directCore_nonneg_from_diagCoreAt_of_mono` across the core/compression equivalence
`directCompressionOperatorNonneg_iff_coreOperatorNonneg` to conclude
`DirectCompressionOperatorNonneg f Φ A B …`. -/
theorem StrictlyPositive.directCompression_from_diagCoreAt_of_mono
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)} :
    ∀ (hPos : IsPositiveMap Φ)
      (hSch : HSAdjointSchwarz Φ)
      (hA : Matrix.PosDef A)
      (hB : Matrix.PosDef B)
      (hΦ1 : Matrix.PosDef (Φ 1))
      (_hdiagCore :
        StrictlyPositive.ShiftedAmbientDiagCoreAt f Φ A B hPos hSch hA hB hΦ1)
      (_hmono :
        ∀ {p : ℝ}, 0 < p →
          ∀ X : Mₙ (Nat.succ l),
            StrictlyPositive.ShiftedAmbientFirstMonotoneQForm
              f Φ A B hPos hB hΦ1 p X),
        StrictlyPositive.DirectCompressionOperatorNonneg f Φ A B hPos hB hΦ1 := by
  intro hPos hSch hA hB hΦ1 hdiagCore hmono
  exact
    (StrictlyPositive.directCompressionOperatorNonneg_iff_coreOperatorNonneg
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).mpr <|
      StrictlyPositive.directCore_nonneg_from_diagCoreAt_of_mono
        (f := f) (hf := hf) (Φ := Φ) (A := A) (B := B)
        hPos hSch hA hB hΦ1 hdiagCore hmono


end MatrixScopedInstances

end HiaiPetz
