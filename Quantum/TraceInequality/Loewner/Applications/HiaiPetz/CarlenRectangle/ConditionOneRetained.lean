/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.BochnerDPIRetained
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.ConditionOne
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.ConditionsRetained

/-!
# Carlen rectangle condition I stage

This module contains the theorem-facing Carlen rectangle declarations moved
from the aggregate rectangle file.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

universe u

open MeasureTheory

open scoped Matrix.Norms.Frobenius MatrixOrder CStarAlgebra ComplexOrder

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace
  instCarlenRectangleHSOpCStarAlgebra
  instCarlenRectangleHSOpPartialOrder
  instCarlenRectangleHSOpStarRing
  instCarlenRectangleHSOpStarOrderedRing
  instCarlenRectangleComplexCFC
  instCarlenRectangleRealCFC
  instCarlenRectangleHSOpNonnegSpectrumClass
  instCarlenRectangleHSOpSMulZeroClass
  instCarlenRectangleHSOpIsBoundedSMul
  instCarlenRectangleHSOpContinuousSMul
  instCarlenRectangleHSOpRealAlgebra
  instCarlenRectangleHSOpRealRealTower

noncomputable section

/--
Loewner-native condition I gives the strict direct DPI for Carlen's
two-variable operator `G_f`.
-/
theorem gOperator_dpi_of_loewnerConditionI
    {n m : ℕ} (Ψ : HSMap n m) {f : ℝ → ℝ} {X Y : Mₙ m}
    (hf : LoewnerConditionI f)
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y)
    (hΨX : MatrixPosDef (hsAdjoint Ψ X))
    (hΨY : MatrixPosDef (hsAdjoint Ψ Y))
    (hpos : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 < f x) :
    HSLE
      ((hsAdjoint Ψ).comp ((gOperator f X Y).comp Ψ))
      (gOperator f (hsAdjoint Ψ X) (hsAdjoint Ψ Y)) := by
  rcases loewnerConditionI_to_positiveRayKuboAndoRep hf with
    ⟨f₀, hagree, ⟨rep⟩⟩
  have hpos₀ : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 < f₀ x := by
    intro x hx
    rw [hagree hx]
    exact hpos hx
  have hbase :
      HSLE
        ((hsAdjoint Ψ).comp ((gOperator f₀ X Y).comp Ψ))
        (gOperator f₀ (hsAdjoint Ψ X) (hsAdjoint Ψ Y)) :=
    gOperator_dpi_of_positiveRayKuboAndoRep Ψ rep hΨ hX hY hΨX hΨY hpos₀
  have hXY : gOperator f₀ X Y = gOperator f X Y :=
    gOperator_congr_on_positive hagree hX hY
  have hΨXY :
      gOperator f₀ (hsAdjoint Ψ X) (hsAdjoint Ψ Y) =
        gOperator f (hsAdjoint Ψ X) (hsAdjoint Ψ Y) :=
    gOperator_congr_on_positive hagree hΨX hΨY
  simpa [hXY, hΨXY] using hbase

/--
Condition (1) implies condition (3).  Positivity on the positive ray supplies
the endpoint extension needed for the Loewner-native Kubo--Ando entry theorem,
and the resulting Loewner condition gives the direct `G_f` DPI.
-/
theorem condition1_to_condition3_of_functionHypothesis
    {f : ℝ → ℝ}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (h1 : CarlenOpMontICondition1 f) :
    CarlenOpMontICondition3 f := by
  have hnonneg : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 ≤ f x := by
    intro x hx
    exact le_of_lt (hf.2 hx)
  have hLoewner : LoewnerConditionI f :=
    closedPositive_extension_of_operatorMonotoneOnPositive_nonneg h1 hnonneg
  intro n m Ψ X Y hΨ hX hY hΨX hΨY
  exact gOperator_dpi_of_loewnerConditionI Ψ hLoewner hΨ hX hY hΨX hΨY hf.2

/--
Loewner-native condition I gives the strict direct DPI in the unital
two-positive Carlen formulation.
-/
theorem jOperator_dpi_of_loewnerConditionI
    {n m : ℕ} (Ψ : HSMap n m) {f : ℝ → ℝ} {A B : Mₙ m}
    (hf : LoewnerConditionI f)
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B))
    (hpos : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 < f x) :
    HSLE
      ((hsAdjoint Ψ).comp ((jOperator f A B).comp Ψ))
      (jOperator f (hsAdjoint Ψ A) (hsAdjoint Ψ B)) := by
  rcases loewnerConditionI_to_positiveRayKuboAndoRep hf with
    ⟨f₀, hagree, ⟨rep⟩⟩
  have hpos₀ : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 < f₀ x := by
    intro x hx
    rw [hagree hx]
    exact hpos hx
  have hbase :
      HSLE
        ((hsAdjoint Ψ).comp ((jOperator f₀ A B).comp Ψ))
        (jOperator f₀ (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
    jOperator_dpi_of_positiveRayKuboAndoRep Ψ rep hΨ hA hB hΨA hΨB hpos₀
  have hAB : jOperator f₀ A B = jOperator f A B :=
    jOperator_congr_on_positive hagree hA hB
  have hΨAB :
      jOperator f₀ (hsAdjoint Ψ A) (hsAdjoint Ψ B) =
      jOperator f (hsAdjoint Ψ A) (hsAdjoint Ψ B) :=
    jOperator_congr_on_positive hagree hΨA hΨB
  simpa [hAB, hΨAB] using hbase

/--
Operator monotonicity on the positive ray gives the direct Hiai--Petz
data-processing inequality for `J_f`.
-/
theorem jOperator_dpi_of_operatorMonotoneOnPositive
    {n m : ℕ} (Ψ : HSMap n m) {f : ℝ → ℝ} {A B : Mₙ m}
    (hf : OperatorMonotoneOnPositive.{u} f)
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B))
    (hpos : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 < f x) :
    HSLE
      ((hsAdjoint Ψ).comp ((jOperator f A B).comp Ψ))
      (jOperator f (hsAdjoint Ψ A) (hsAdjoint Ψ B)) := by
  have hnonneg : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 ≤ f x := by
    intro x hx
    exact le_of_lt (hpos hx)
  have hLoewner : LoewnerConditionI f :=
    closedPositive_extension_of_operatorMonotoneOnPositive_nonneg hf hnonneg
  exact jOperator_dpi_of_loewnerConditionI Ψ hLoewner hΨ hA hB hΨA hΨB hpos

/--
Operator monotonicity gives the inverse Hiai--Petz data-processing inequality
for `J_f` by applying the rectangular direct-to-inverse transfer to the direct
inequality.
-/
theorem jOperator_inverse_dpi_of_operatorMonotoneOnPositive
    {n m : ℕ} (Ψ : HSMap n m) {f : ℝ → ℝ} {A B : Mₙ m}
    (hfcont : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hf : OperatorMonotoneOnPositive.{u} f)
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B))
    (hpos : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 < f x) :
    HSLE
      (Ψ.comp
        ((Ring.inverse (jOperator f (hsAdjoint Ψ A) (hsAdjoint Ψ B))).comp
          (hsAdjoint Ψ)))
      (Ring.inverse (jOperator f A B)) := by
  let TA : HSOp m := jOperator f A B
  let TΦ : HSOp n := jOperator f (hsAdjoint Ψ A) (hsAdjoint Ψ B)
  have hfHyp : CarlenOpMontIFunctionHypothesis f := ⟨hfcont, hpos⟩
  have hTA_sa : IsSelfAdjoint TA := by
    simpa [TA] using jOperator_isSelfAdjoint_of_carlenFunctionHypothesis hfHyp hA hB
  have hTΦ_sa : IsSelfAdjoint TΦ := by
    simpa [TΦ] using
      jOperator_isSelfAdjoint_of_carlenFunctionHypothesis hfHyp hΨA hΨB
  have hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ) := by
    simpa [TA] using jOperator_spectrum_subset_Ioi_of_carlenFunctionHypothesis hfHyp hA hB
  have hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ) := by
    simpa [TΦ] using
      jOperator_spectrum_subset_Ioi_of_carlenFunctionHypothesis hfHyp hΨA hΨB
  have hdirect :
      HSLE (carlenRectDirectOp Ψ TA) TΦ := by
    simpa [carlenRectDirectOp, TA, TΦ] using
      jOperator_dpi_of_operatorMonotoneOnPositive
        Ψ hf hΨ hA hB hΨA hΨB hpos
  have hinv : HSLE (carlenRectInverseOp Ψ TΦ) (Ring.inverse TA) :=
    carlenRectangle_direct_to_inverse Ψ hTA_sa hTΦ_sa hσTA hσTΦ hdirect
  simpa [carlenRectInverseOp, TA, TΦ] using hinv

/--
The theorem-facing strict Hiai--Petz DPI package for `J_f`: direct DPI, strict
positivity and invertibility of both endpoint operators, and the inverse DPI.
-/
theorem jOperator_strict_direct_inverse_dpi_of_operatorMonotoneOnPositive
    {n m : ℕ} (Ψ : HSMap n m) {f : ℝ → ℝ} {A B : Mₙ m}
    (hfcont : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hf : OperatorMonotoneOnPositive.{u} f)
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B))
    (hpos : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 < f x) :
    HSLE
        ((hsAdjoint Ψ).comp ((jOperator f A B).comp Ψ))
        (jOperator f (hsAdjoint Ψ A) (hsAdjoint Ψ B)) ∧
      IsStrictlyPositive (jOperator f A B) ∧
      IsStrictlyPositive (jOperator f (hsAdjoint Ψ A) (hsAdjoint Ψ B)) ∧
      IsUnit (jOperator f A B) ∧
      IsUnit (jOperator f (hsAdjoint Ψ A) (hsAdjoint Ψ B)) ∧
      HSLE
        (Ψ.comp
          ((Ring.inverse (jOperator f (hsAdjoint Ψ A) (hsAdjoint Ψ B))).comp
            (hsAdjoint Ψ)))
        (Ring.inverse (jOperator f A B)) := by
  have hfHyp : CarlenOpMontIFunctionHypothesis f := ⟨hfcont, hpos⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jOperator_dpi_of_operatorMonotoneOnPositive
      Ψ hf hΨ hA hB hΨA hΨB hpos
  · exact jOperator_isStrictlyPositive_of_carlenFunctionHypothesis hfHyp hA hB
  · exact jOperator_isStrictlyPositive_of_carlenFunctionHypothesis hfHyp hΨA hΨB
  · exact jOperator_isUnit_of_carlenFunctionHypothesis hfHyp hA hB
  · exact jOperator_isUnit_of_carlenFunctionHypothesis hfHyp hΨA hΨB
  · exact jOperator_inverse_dpi_of_operatorMonotoneOnPositive
      Ψ hfcont hf hΨ hA hB hΨA hΨB hpos

/--
Hiai--Petz `ConditionI`, together with Carlen's continuity and positivity
hypotheses, gives the theorem-facing strict `J_f` DPI package for a unital
two-positive Hilbert--Schmidt map.
-/
theorem jOperator_strict_direct_inverse_dpi_of_conditionI
    {n m : ℕ} (Ψ : HSMap n m) {f : ℝ → ℝ} {A B : Mₙ m}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hI : ConditionI f)
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B)) :
    HSLE
        ((hsAdjoint Ψ).comp ((jOperator f A B).comp Ψ))
        (jOperator f (hsAdjoint Ψ A) (hsAdjoint Ψ B)) ∧
      IsStrictlyPositive (jOperator f A B) ∧
      IsStrictlyPositive (jOperator f (hsAdjoint Ψ A) (hsAdjoint Ψ B)) ∧
      IsUnit (jOperator f A B) ∧
      IsUnit (jOperator f (hsAdjoint Ψ A) (hsAdjoint Ψ B)) ∧
      HSLE
        (Ψ.comp
          ((Ring.inverse (jOperator f (hsAdjoint Ψ A) (hsAdjoint Ψ B))).comp
            (hsAdjoint Ψ)))
        (Ring.inverse (jOperator f A B)) :=
  jOperator_strict_direct_inverse_dpi_of_operatorMonotoneOnPositive.{0}
    Ψ hf.1 (conditionI_to_operatorMonotoneOnPositive.{0} hI)
    hΨ hA hB hΨA hΨB hf.2

end

end Quantum.TraceInequality.Loewner.HiaiPetz
