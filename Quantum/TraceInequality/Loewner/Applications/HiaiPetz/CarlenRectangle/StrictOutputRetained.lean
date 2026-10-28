/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.ConditionOne
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.ConditionOneRetained
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.RectangleOrderRetained
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.StrictOutput
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.CFCTransportRetained
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.RankOneBridgeRetained

/-!
# Carlen rectangle strict-output stage

This module contains the theorem-facing Carlen rectangle declarations moved
from the aggregate rectangle file.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

universe u

open MeasureTheory

open scoped Matrix.Norms.Frobenius MatrixOrder CStarAlgebra ComplexOrder FinMatrixCStar

attribute [local instance]
  _root_.HiaiPetz.instMatrixNormedAddCommGroup
  _root_.HiaiPetz.instMatrixNormedSpace
  _root_.HiaiPetz.instMatrixInnerProductSpace
  _root_.HiaiPetz.instMatrixCompleteSpace
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

/-! ### Strict-output bridges and condition II/III equivalence -/
/--
The strengthened two-positive adjoint input supplies exactly the residual
pointwise inverse-form fixed-kernel input needed by the Schwarz-output bridge.
-/
theorem pointwiseInvKernelInput_of_hsAdjoint_twoPositive {n m : ℕ}
    (Φ : HSMap n m) {A B : Mₙ n}
    (htrace : _root_.HiaiPetz.TracePreserving Φ)
    (hadj_twoPositive : IsTwoPositiveMap (hsAdjoint Φ))
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΦA : MatrixPosDef (Φ A)) (hΦB : MatrixPosDef (Φ B)) :
    ∀ {t : ℝ}, 0 ≤ t →
      HSLE
        ((hsAdjoint Φ).comp ((jKuboKernelInvForm t (Φ A) (Φ B)).comp Φ))
        (jKuboKernelInvForm t A B) := by
  intro t ht
  have hΦ_twoPositive : IsTwoPositiveMap Φ := by
    simpa [hsAdjoint_hsAdjoint] using
      (isTwoPositiveMap_hsAdjoint_of_isTwoPositiveMap hadj_twoPositive)
  exact jKuboKernelInvForm_dpi_of_liebRuskai_terms Φ ht htrace hΦ_twoPositive
    (matrixPosDef_posDef hA) (matrixPosDef_posDef hB)
    (matrixPosDef_posDef hΦA) (matrixPosDef_posDef hΦB)

/--
If the Hilbert--Schmidt adjoint has the two-positivity input required by the
unital convention, and the output endpoints are already positive definite, then
Hiai--Petz `ConditionI` gives both strict-output inequalities in the named
`J_f` notation.
-/
theorem strict_output_direct_inverse_dpi_of_conditionI_hsAdjoint_twoPositive_outputs
    {n m : ℕ} (Φ : HSMap n m) {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hI : ConditionI f)
    (htrace : _root_.HiaiPetz.TracePreserving Φ)
    (hadj_twoPositive : IsTwoPositiveMap (hsAdjoint Φ))
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΦA : MatrixPosDef (Φ A)) (hΦB : MatrixPosDef (Φ B)) :
    HSLE
        (Φ.comp ((jOperator f A B).comp (hsAdjoint Φ)))
        (jOperator f (Φ A) (Φ B)) ∧
      HSLE
        ((hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ))
        (jOperatorInv f A B) := by
  let Ψ : HSMap m n := hsAdjoint Φ
  have hΨ : IsUnitalTwoPositiveMap Ψ := by
    refine ⟨?_, ?_⟩
    · simpa [Ψ] using isUnitalMap_hsAdjoint_of_tracePreserving htrace
    · simpa [Ψ] using hadj_twoPositive
  have hΨA : MatrixPosDef (hsAdjoint Ψ A) := by
    simpa [Ψ, hsAdjoint_hsAdjoint] using hΦA
  have hΨB : MatrixPosDef (hsAdjoint Ψ B) := by
    simpa [Ψ, hsAdjoint_hsAdjoint] using hΦB
  rcases jOperator_strict_direct_inverse_dpi_of_conditionI
      Ψ hf hI hΨ hA hB hΨA hΨB with
    ⟨hdirect, _hstrictAB, _hstrictΦ, _hunitAB, _hunitΦ, hinverse⟩
  have hJΦ :
      jOperatorInv f (Φ A) (Φ B) =
        Ring.inverse (jOperator f (Φ A) (Φ B)) :=
    jOperatorInv_eq_ringInverse_of_carlenFunctionHypothesis hf hΦA hΦB
  have hJAB :
      jOperatorInv f A B = Ring.inverse (jOperator f A B) :=
    jOperatorInv_eq_ringInverse_of_carlenFunctionHypothesis hf hA hB
  refine ⟨?_, ?_⟩
  · simpa [Ψ, hsAdjoint_hsAdjoint] using hdirect
  · simpa [Ψ, hsAdjoint_hsAdjoint, hJΦ, hJAB] using hinverse

/--
If the Hilbert--Schmidt adjoint has the two-positivity input required by the
unital convention, then the original strict-output positivity assumptions
already supply the positive-definite output endpoints.
-/
theorem strict_output_direct_inverse_dpi_of_conditionI_hsAdjoint_twoPositive
    {n m : ℕ} (Φ : HSMap n m) {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hI : ConditionI f)
    (hpos : IsPositiveMap Φ)
    (htrace : _root_.HiaiPetz.TracePreserving Φ)
    (hadj_twoPositive : IsTwoPositiveMap (hsAdjoint Φ))
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    HSLE
        (Φ.comp ((jOperator f A B).comp (hsAdjoint Φ)))
        (jOperator f (Φ A) (Φ B)) ∧
      HSLE
        ((hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ))
        (jOperatorInv f A B) := by
  have hΦA : MatrixPosDef (Φ A) :=
    isPositiveMap_matrixPosDef_of_map_one_matrixPosDef Φ hpos hΦ1 hA
  have hΦB : MatrixPosDef (Φ B) :=
    isPositiveMap_matrixPosDef_of_map_one_matrixPosDef Φ hpos hΦ1 hB
  exact strict_output_direct_inverse_dpi_of_conditionI_hsAdjoint_twoPositive_outputs
    Φ hf hI htrace hadj_twoPositive hA hB hΦA hΦB

/--
Carlen's strict-domain `opmontI` conditions are equivalent for functions that are
continuous and positive on the positive half-line.
-/
theorem carlenOpMontI_conditions_equivalent
    {f : ℝ → ℝ}
    (hf : CarlenOpMontIFunctionHypothesis f) :
    (CarlenOpMontICondition1.{u} f ↔ CarlenOpMontICondition2 f) ∧
      (CarlenOpMontICondition2 f ↔ CarlenOpMontICondition3 f) ∧
      (CarlenOpMontICondition3 f ↔ CarlenOpMontICondition4 f) := by
  have h13 : CarlenOpMontICondition1.{u} f → CarlenOpMontICondition3 f :=
    condition1_to_condition3_of_functionHypothesis hf
  have h23 : CarlenOpMontICondition2 f ↔ CarlenOpMontICondition3 f :=
    carlenOpMontICondition2_iff_condition3_of_functionHypothesis hf
  have h24 : CarlenOpMontICondition2 f → CarlenOpMontICondition4 f :=
    condition2_to_condition4_of_carlenFunction hf
  have h41 : CarlenOpMontICondition4 f → CarlenOpMontICondition1.{u} f :=
    condition4_to_condition1 hf
  refine ⟨?_, h23, ?_⟩
  · exact
      ⟨fun h1 => h23.mpr (h13 h1),
        fun h2 => h41 (h24 h2)⟩
  · exact
      ⟨fun h3 => h24 (h23.mpr h3),
        fun h4 => h13 (h41 h4)⟩
end

end Quantum.TraceInequality.Loewner.HiaiPetz
