/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.OutputSupportDPI.ReducedMap
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.JointConcavityToMonotone.ConvexityUpgrade
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.JointConcavityToMonotone.MidpointTransport
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.SharedStageCompatibility
-- The imported module names above are indivisible tokens longer than the style limit.
set_option linter.style.longLine false

/-!
# Hiai--Petz 6.2 output-support strict-output lift

This module contains the general and book-facing output-support conditions,
their strict-output lift through the canonical reduced map, and the final
Hiai--Petz 6.2 output-support wrappers.
-/
namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace
  instOutputSupportHSOpCStarAlgebra
  instOutputSupportHSOpStarRing
  instOutputSupportHSOpComplexAlgebra
  instOutputSupportHSOpNormedAlgebra
  instOutputSupportHSOpPartialOrder
  instOutputSupportHSOpStarOrderedRing
  instOutputSupportHSOpNonnegSpectrumClass
  instOutputSupportHSOpComplexCFC
  instOutputSupportHSOpRealCFC
  outputSupportBridgeMatrixNormedAddCommGroup
  outputSupportBridgeMatrixNormedSpace
  outputSupportBridgeMatrixInnerProductSpace
  outputSupportBridgeMatrixCompleteSpace
  outputSupportBridgeMatrixFiniteDimensional

noncomputable section

/-! ### General and Book Conditions via the Canonical Reduction -/

/-- Proof-facing general `(ii)` phrased via the canonical output-support reduction of `Φ`. -/
def ConditionII_general (f : ℝ → ℝ) {n m : ℕ} (Φ : HSMap n m) : Prop :=
  ∀ {A B : Mₙ n},
    (hPos : IsPositiveMap Φ) →
    _root_.HiaiPetz.TracePreserving Φ →
    HSAdjointSchwarz Φ →
    MatrixPosDef A →
    MatrixPosDef B →
    let Ψ := outputSupportReducedHSMap Φ hPos
    HSLE
      ((hsAdjoint Ψ).comp ((jOperatorInv f (Ψ A) (Ψ B)).comp Ψ))
      (jOperatorInv f A B)

/-- Proof-facing general `(iii)` phrased via the canonical output-support reduction of `Φ`. -/
def ConditionIII_general (f : ℝ → ℝ) {n m : ℕ} (Φ : HSMap n m) : Prop :=
  ∀ {A B : Mₙ n},
    (hPos : IsPositiveMap Φ) →
    _root_.HiaiPetz.TracePreserving Φ →
    HSAdjointSchwarz Φ →
    MatrixPosDef A →
    MatrixPosDef B →
    let Ψ := outputSupportReducedHSMap Φ hPos
    HSLE
      (Ψ.comp ((jOperator f A B).comp (hsAdjoint Ψ)))
      (jOperator f (Ψ A) (Ψ B))

def ConditionII_reduced (f : ℝ → ℝ) : Prop :=
  ConditionII_strict f

def ConditionIII_reduced (f : ℝ → ℝ) : Prop :=
  ConditionIII_strict f

/-- Proof-facing general inverse inequality, quantified over all maps. -/
def ConditionII (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m), ConditionII_general f Φ

/-- Proof-facing general direct inequality, quantified over all maps. -/
def ConditionIII (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m), ConditionIII_general f Φ

/-- Book-facing general `(ii)` through the canonical support-corner reduced map. -/
def ConditionII_book (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m),
    ∀ {A B : Mₙ n},
      (hPos : IsPositiveMap Φ) →
      _root_.HiaiPetz.TracePreserving Φ →
      HSAdjointSchwarz Φ →
      MatrixPosDef A →
      MatrixPosDef B →
      let Ψ := outputSupportReducedHSMap Φ hPos
      HSLE
        ((hsAdjoint Ψ).comp ((jOperatorInv f (Ψ A) (Ψ B)).comp Ψ))
        (jOperatorInv f A B)

/-- Book-facing general `(iii)` through the canonical support-corner reduced map. -/
def ConditionIII_book (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m),
    ∀ {A B : Mₙ n},
      (hPos : IsPositiveMap Φ) →
      _root_.HiaiPetz.TracePreserving Φ →
      HSAdjointSchwarz Φ →
      MatrixPosDef A →
      MatrixPosDef B →
      let Ψ := outputSupportReducedHSMap Φ hPos
      HSLE
        (Ψ.comp ((jOperator f A B).comp (hsAdjoint Ψ)))
        (jOperator f (Ψ A) (Ψ B))

/-- The canonical support-corner reduced formulation of general `(ii)` is a re-expression of
the proof-facing canonical reduced-map representative. -/
theorem ConditionII_book_iff_ConditionII (f : ℝ → ℝ) :
    ConditionII_book f ↔ ConditionII f := by
  constructor
  · intro hII
    change ∀ {n m : ℕ} (Φ : HSMap n m), ConditionII_general f Φ
    intro n m Φ A B hPos hTrace hSch hA hB
    simpa [ConditionII_general, outputSupportReducedHSMap] using
      (hII Φ (A := A) (B := B) hPos hTrace hSch hA hB)
  · intro hII
    change ∀ {n m : ℕ} (Φ : HSMap n m),
      ∀ {A B : Mₙ n},
        (hPos : IsPositiveMap Φ) →
        _root_.HiaiPetz.TracePreserving Φ →
        HSAdjointSchwarz Φ →
        MatrixPosDef A →
        MatrixPosDef B →
        let Ψ := outputSupportReducedHSMap Φ hPos
        HSLE
          ((hsAdjoint Ψ).comp ((jOperatorInv f (Ψ A) (Ψ B)).comp Ψ))
          (jOperatorInv f A B)
    intro n m Φ
    dsimp
    intro A B hPos hTrace hSch hA hB
    simpa [ConditionII_general, outputSupportReducedHSMap] using
      (hII Φ (A := A) (B := B) hPos hTrace hSch hA hB)

/-- The canonical support-corner reduced formulation of general `(iii)` is a re-expression of
the proof-facing canonical reduced-map representative. -/
theorem ConditionIII_book_iff_ConditionIII (f : ℝ → ℝ) :
    ConditionIII_book f ↔ ConditionIII f := by
  constructor
  · intro hIII
    change ∀ {n m : ℕ} (Φ : HSMap n m), ConditionIII_general f Φ
    intro n m Φ A B hPos hTrace hSch hA hB
    simpa [ConditionIII_general, outputSupportReducedHSMap] using
      (hIII Φ (A := A) (B := B) hPos hTrace hSch hA hB)
  · intro hIII
    change ∀ {n m : ℕ} (Φ : HSMap n m),
      ∀ {A B : Mₙ n},
        (hPos : IsPositiveMap Φ) →
        _root_.HiaiPetz.TracePreserving Φ →
        HSAdjointSchwarz Φ →
        MatrixPosDef A →
        MatrixPosDef B →
        let Ψ := outputSupportReducedHSMap Φ hPos
        HSLE
          (Ψ.comp ((jOperator f A B).comp (hsAdjoint Ψ)))
          (jOperator f (Ψ A) (Ψ B))
    intro n m Φ
    dsimp
    intro A B hPos hTrace hSch hA hB
    simpa [ConditionIII_general, outputSupportReducedHSMap] using
      (hIII Φ (A := A) (B := B) hPos hTrace hSch hA hB)

/-! ### Strict-Output Lift of Hiai-Petz Conditions -/

/-- Pointwise strict-output bridge: inverse Hiai--Petz DPI implies direct DPI. -/
theorem strictOutputInverse_implies_direct_of_carlenFunctionHypothesis
    {f : ℝ → ℝ} (hf : CarlenOpMontIFunctionHypothesis f)
    {n m : ℕ} (Φ : HSMap n m) {A B : Mₙ n}
    (hpos : IsPositiveMap Φ) (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    HSLE
        ((hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ))
        (jOperatorInv f A B) →
      HSLE
        (Φ.comp ((jOperator f A B).comp (hsAdjoint Φ)))
        (jOperator f (Φ A) (Φ B)) := by
  intro hinverse
  have hΦA : MatrixPosDef (Φ A) :=
    isPositiveMap_matrixPosDef_of_map_one_matrixPosDef Φ hpos hΦ1 hA
  have hΦB : MatrixPosDef (Φ B) :=
    isPositiveMap_matrixPosDef_of_map_one_matrixPosDef Φ hpos hΦ1 hB
  let TA : HSOp n := jOperator f A B
  let TΦ : HSOp m := jOperator f (Φ A) (Φ B)
  have hTA_sa : IsSelfAdjoint TA := by
    simpa [TA] using jOperator_isSelfAdjoint_of_carlenFunctionHypothesis hf hA hB
  have hTΦ_sa : IsSelfAdjoint TΦ := by
    simpa [TΦ] using jOperator_isSelfAdjoint_of_carlenFunctionHypothesis hf hΦA hΦB
  have hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ) := by
    simpa [TA] using jOperator_spectrum_subset_Ioi_of_carlenFunctionHypothesis hf hA hB
  have hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ) := by
    simpa [TΦ] using jOperator_spectrum_subset_Ioi_of_carlenFunctionHypothesis hf hΦA hΦB
  have hJΦ :
      jOperatorInv f (Φ A) (Φ B) =
        Ring.inverse (jOperator f (Φ A) (Φ B)) :=
    jOperatorInv_eq_ringInverse_of_carlenFunctionHypothesis hf hΦA hΦB
  have hJAB :
      jOperatorInv f A B = Ring.inverse (jOperator f A B) :=
    jOperatorInv_eq_ringInverse_of_carlenFunctionHypothesis hf hA hB
  have hinverseRing :
      HSLE (carlenRectInverseOp (hsAdjoint Φ) TΦ) (Ring.inverse TA) := by
    simpa [carlenRectInverseOp, TA, TΦ, hJΦ, hJAB, hsAdjoint_hsAdjoint] using hinverse
  have hdirect :
      HSLE (carlenRectDirectOp (hsAdjoint Φ) TA) TΦ :=
    carlenRectangle_inverse_to_direct (hsAdjoint Φ) hTA_sa hTΦ_sa hσTA hσTΦ hinverseRing
  simpa [carlenRectDirectOp, TA, TΦ, hsAdjoint_hsAdjoint] using hdirect

/-- Pointwise strict-output bridge: direct Hiai--Petz DPI implies inverse DPI. -/
theorem strictOutputDirect_implies_inverse_of_carlenFunctionHypothesis
    {f : ℝ → ℝ} (hf : CarlenOpMontIFunctionHypothesis f)
    {n m : ℕ} (Φ : HSMap n m) {A B : Mₙ n}
    (hpos : IsPositiveMap Φ) (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    HSLE
        (Φ.comp ((jOperator f A B).comp (hsAdjoint Φ)))
        (jOperator f (Φ A) (Φ B)) →
      HSLE
        ((hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ))
        (jOperatorInv f A B) := by
  intro hdirect
  have hΦA : MatrixPosDef (Φ A) :=
    isPositiveMap_matrixPosDef_of_map_one_matrixPosDef Φ hpos hΦ1 hA
  have hΦB : MatrixPosDef (Φ B) :=
    isPositiveMap_matrixPosDef_of_map_one_matrixPosDef Φ hpos hΦ1 hB
  let TA : HSOp n := jOperator f A B
  let TΦ : HSOp m := jOperator f (Φ A) (Φ B)
  have hTA_sa : IsSelfAdjoint TA := by
    simpa [TA] using jOperator_isSelfAdjoint_of_carlenFunctionHypothesis hf hA hB
  have hTΦ_sa : IsSelfAdjoint TΦ := by
    simpa [TΦ] using jOperator_isSelfAdjoint_of_carlenFunctionHypothesis hf hΦA hΦB
  have hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ) := by
    simpa [TA] using jOperator_spectrum_subset_Ioi_of_carlenFunctionHypothesis hf hA hB
  have hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ) := by
    simpa [TΦ] using jOperator_spectrum_subset_Ioi_of_carlenFunctionHypothesis hf hΦA hΦB
  have hdirectRect :
      HSLE (carlenRectDirectOp (hsAdjoint Φ) TA) TΦ := by
    simpa [carlenRectDirectOp, TA, TΦ, hsAdjoint_hsAdjoint] using hdirect
  have hinverseRing :
      HSLE (carlenRectInverseOp (hsAdjoint Φ) TΦ) (Ring.inverse TA) :=
    carlenRectangle_direct_to_inverse (hsAdjoint Φ) hTA_sa hTΦ_sa hσTA hσTΦ hdirectRect
  have hJΦ :
      jOperatorInv f (Φ A) (Φ B) =
        Ring.inverse (jOperator f (Φ A) (Φ B)) :=
    jOperatorInv_eq_ringInverse_of_carlenFunctionHypothesis hf hΦA hΦB
  have hJAB :
      jOperatorInv f A B = Ring.inverse (jOperator f A B) :=
    jOperatorInv_eq_ringInverse_of_carlenFunctionHypothesis hf hA hB
  simpa [carlenRectInverseOp, TA, TΦ, hJΦ, hJAB, hsAdjoint_hsAdjoint]
    using hinverseRing

/-- General output-support inverse and direct conditions are equivalent after reduction. -/
theorem conditionII_general_iff_conditionIII_general (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hposf : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    {n m : ℕ} (Φ : HSMap n m) :
    ConditionII_general f Φ ↔ ConditionIII_general f Φ := by
  have hfCarlen : CarlenOpMontIFunctionHypothesis f := by
    exact ⟨hf, fun {x} hx => hposf x hx⟩
  constructor
  · intro hII A B hPos hTrace hSch hA hB
    have hReady := outputSupportReducedHSMap_ready Φ hPos hTrace hSch
    exact strictOutputInverse_implies_direct_of_carlenFunctionHypothesis
      (f := f) hfCarlen (outputSupportReducedHSMap Φ hPos)
      hReady.positive hA hB hReady.outputPosDef
      (hII hPos hTrace hSch hA hB)
  · intro hIII A B hPos hTrace hSch hA hB
    have hReady := outputSupportReducedHSMap_ready Φ hPos hTrace hSch
    exact strictOutputDirect_implies_inverse_of_carlenFunctionHypothesis
      (f := f) hfCarlen (outputSupportReducedHSMap Φ hPos)
      hReady.positive hA hB hReady.outputPosDef
      (hIII hPos hTrace hSch hA hB)

/-- Condition I implies the proof-facing general direct inequality by applying the completed
strict-output theorem to the canonical reduced map. -/
theorem conditionI_implies_conditionIII_general (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hposf : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hI : ConditionI f) {n m : ℕ} (Φ : HSMap n m) :
    ConditionIII_general f Φ := by
  intro A B hPos hTrace hSch hA hB
  have hfCarlen : CarlenOpMontIFunctionHypothesis f := by
    exact ⟨hf, fun {x} hx => hposf x hx⟩
  have hReady := outputSupportReducedHSMap_ready Φ hPos hTrace hSch
  have hStrict :
      ConditionIII_strict f ∧ ConditionII_strict f :=
    conditionI_to_conditionIII_and_conditionII_strict hfCarlen hI
  exact hStrict.1
    (outputSupportReducedHSMap Φ hPos)
    hReady.positive hReady.tracePreserving hReady.adjointSchwarz hA hB hReady.outputPosDef

/-! ### Full-Support Trivialization and Transport -/

private noncomputable def oneCornerLinearEquiv (m : ℕ) :
    Mₙ m ≃ₗ[ℂ] matrixCornerSubmodule (1 : Mₙ m) where
  toFun := fun X => ⟨X, by simp⟩
  invFun := fun X => X.1
  left_inv := by
    intro X
    rfl
  right_inv := by
    intro X
    ext
    rfl
  map_add' := by
    intro X Y
    rfl
  map_smul' := by
    intro a X
    rfl

private noncomputable def fullSupportToMatLinearEquiv {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    Mₙ m ≃ₗ[ℂ] Mₙ (outputSupportMatrixCornerModel Φ).dim := by
  let hCorner : matrixCornerSubmodule (1 : Mₙ m) = matrixCornerSubmodule (outputSupportProj Φ) := by
    simp [outputSupportProj_eq_one_of_posDef Φ hΦ1]
  exact (oneCornerLinearEquiv m).trans
    ((LinearEquiv.ofEq _ _ hCorner).trans (outputSupportMatrixCornerModel Φ).toMat)

@[simp] private theorem fullSupportToMatLinearEquiv_apply {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) (X : Mₙ m) :
    fullSupportToMatLinearEquiv Φ hΦ1 X =
      (outputSupportMatrixCornerModel Φ).toMat
        ⟨X, by
          simp [outputSupportProj_eq_one_of_posDef Φ hΦ1]⟩ := by
  rfl

private noncomputable def fullSupportToMatLinearIsometryEquiv {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    Mₙ m ≃ₗᵢ[ℂ] Mₙ (outputSupportMatrixCornerModel Φ).dim :=
  (fullSupportToMatLinearEquiv Φ hΦ1).isometryOfInner (by
    intro X Y
    simpa [fullSupportToMatLinearEquiv_apply] using
      MatrixCornerModel.inner_toMat_eq (outputSupportMatrixCornerModel Φ)
        ⟨X, by
          simp [outputSupportProj_eq_one_of_posDef Φ hΦ1]⟩
        ⟨Y, by
          simp [outputSupportProj_eq_one_of_posDef Φ hΦ1]⟩)

@[simp] private theorem fullSupportToMat_map_mul {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) (X Y : Mₙ m) :
    fullSupportToMatLinearEquiv Φ hΦ1 (X * Y) =
      fullSupportToMatLinearEquiv Φ hΦ1 X * fullSupportToMatLinearEquiv Φ hΦ1 Y := by
  simpa [fullSupportToMatLinearEquiv_apply] using
    (outputSupportMatrixCornerModel Φ).map_mul
      ⟨X, by simp [outputSupportProj_eq_one_of_posDef Φ hΦ1]⟩
      ⟨Y, by simp [outputSupportProj_eq_one_of_posDef Φ hΦ1]⟩

@[simp] private theorem fullSupportToMat_map_star {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) (X : Mₙ m) :
    fullSupportToMatLinearEquiv Φ hΦ1 (star X) =
      star (fullSupportToMatLinearEquiv Φ hΦ1 X) := by
  simpa [fullSupportToMatLinearEquiv_apply] using
    (outputSupportMatrixCornerModel Φ).preservesAdjoint
      ⟨X, by simp [outputSupportProj_eq_one_of_posDef Φ hΦ1]⟩

@[simp] private theorem fullSupportToMat_map_one {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    fullSupportToMatLinearEquiv Φ hΦ1 (1 : Mₙ m) = 1 := by
  simpa [fullSupportToMatLinearEquiv_apply, outputSupportProj_eq_one_of_posDef Φ hΦ1] using
    (outputSupportMatrixCornerModel Φ).map_proj

private noncomputable abbrev fullSupportToMat {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    Mₙ m ≃ₗ[ℂ] Mₙ (outputSupportMatrixCornerModel Φ).dim :=
  fullSupportToMatLinearEquiv Φ hΦ1

private noncomputable abbrev fullSupportIso {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    Mₙ m ≃ₗᵢ[ℂ] Mₙ (outputSupportMatrixCornerModel Φ).dim :=
  fullSupportToMatLinearIsometryEquiv Φ hΦ1

@[simp] private theorem fullSupportToMat_symm_apply {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n)))
    (Y : Mₙ (outputSupportMatrixCornerModel Φ).dim) :
    (outputSupportMatrixCornerModel Φ).toMat.symm Y =
      ⟨(fullSupportToMatLinearEquiv Φ hΦ1).symm Y, by
        simp [outputSupportProj_eq_one_of_posDef Φ hΦ1]⟩ := by
  apply (outputSupportMatrixCornerModel Φ).toMat.injective
  calc
    (outputSupportMatrixCornerModel Φ).toMat
        ((outputSupportMatrixCornerModel Φ).toMat.symm Y) = Y := by
          simp
    _ = (outputSupportMatrixCornerModel Φ).toMat
          ⟨(fullSupportToMatLinearEquiv Φ hΦ1).symm Y, by
            simp [outputSupportProj_eq_one_of_posDef Φ hΦ1]⟩ := by
          exact (LinearEquiv.apply_symm_apply (fullSupportToMat Φ hΦ1) Y).symm

@[simp] private theorem fullSupportToMat_symm_apply_val {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n)))
    (Y : Mₙ (outputSupportMatrixCornerModel Φ).dim) :
    ((outputSupportMatrixCornerModel Φ).toMat.symm Y).1 =
      (fullSupportToMatLinearEquiv Φ hΦ1).symm Y := by
  simpa using congrArg Subtype.val (fullSupportToMat_symm_apply Φ hΦ1 Y)

private theorem fullSupportToMat_map_posInv {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) {B : Mₙ m} (hB : MatrixPosDef B) :
  fullSupportToMatLinearEquiv Φ hΦ1 (posInv B) =
      posInv (fullSupportToMatLinearEquiv Φ hΦ1 B) := by
  rcases matrixPosDef_isUnit hB with ⟨u, rfl⟩
  let Fu : Units (Mₙ (outputSupportMatrixCornerModel Φ).dim) := by
    refine
      { val := fullSupportToMatLinearEquiv Φ hΦ1 (u : Mₙ m)
        inv := fullSupportToMatLinearEquiv Φ hΦ1 (((u⁻¹ : Units (Mₙ m)) : Mₙ m))
        val_inv := ?_
        inv_val := ?_ }
    · simpa [fullSupportToMat_map_one Φ hΦ1] using
        (fullSupportToMat_map_mul Φ hΦ1
          (u : Mₙ m) (((u⁻¹ : Units (Mₙ m)) : Mₙ m))).symm
    · simpa [fullSupportToMat_map_one Φ hΦ1] using
        (fullSupportToMat_map_mul Φ hΦ1
          (((u⁻¹ : Units (Mₙ m)) : Mₙ m)) (u : Mₙ m)).symm
  change fullSupportToMatLinearEquiv Φ hΦ1 (((u : Mₙ m)⁻¹)) =
    (fullSupportToMatLinearEquiv Φ hΦ1 (u : Mₙ m))⁻¹
  rw [show ((u : Mₙ m)⁻¹) = (((u⁻¹ : Units (Mₙ m)) : Mₙ m)) by simp]
  rw [show (fullSupportToMatLinearEquiv Φ hΦ1 (u : Mₙ m))⁻¹ =
      (((Fu : Units (Mₙ (outputSupportMatrixCornerModel Φ).dim)) :
          Mₙ (outputSupportMatrixCornerModel Φ).dim)⁻¹) by simp [Fu]]
  rw [show ((((Fu : Units (Mₙ (outputSupportMatrixCornerModel Φ).dim)) :
      Mₙ (outputSupportMatrixCornerModel Φ).dim))⁻¹) =
      (((Fu⁻¹ : Units (Mₙ (outputSupportMatrixCornerModel Φ).dim)) :
          Mₙ (outputSupportMatrixCornerModel Φ).dim)) by simp]
  rfl

private theorem jArg_isStrictlyPositive_local {n : ℕ} {A B : Mₙ n}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    IsStrictlyPositive (jArg A B) :=
  jArg_isStrictlyPositive_of_matrixPosDef hA hB

private theorem spectrum_jArg_subset_Ioi_local {n : ℕ} {A B : Mₙ n}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    spectrum ℝ (jArg A B) ⊆ Set.Ioi (0 : ℝ) :=
  jArg_spectrum_subset_Ioi_of_matrixPosDef hA hB

private noncomputable def conjHSOp {m k : ℕ} (e : Mₙ m ≃ₗᵢ[ℂ] Mₙ k) (T : HSOp m) :
    HSOp k :=
  e.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.comp e.symm.toContinuousLinearMap)

@[simp] private theorem conjHSOp_apply {m k : ℕ} (e : Mₙ m ≃ₗᵢ[ℂ] Mₙ k)
    (T : HSOp m) (X : Mₙ k) :
    conjHSOp e T X = e (T (e.symm X)) := rfl

private theorem conjHSOp_mul {m k : ℕ} (e : Mₙ m ≃ₗᵢ[ℂ] Mₙ k) (S T : HSOp m) :
    conjHSOp e (S * T) = conjHSOp e S * conjHSOp e T := by
  ext X
  simp [conjHSOp_apply]

private theorem conjHSOp_map_sub {m k : ℕ} (e : Mₙ m ≃ₗᵢ[ℂ] Mₙ k) (S T : HSOp m) :
    conjHSOp e (S - T) = conjHSOp e S - conjHSOp e T := by
  ext X i j
  simpa using congrArg (fun Y : Mₙ k => Y i j) (e.map_sub (S (e.symm X)) (T (e.symm X)))

private noncomputable def fullSupportConjLeftMulTarget {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) (A : Mₙ m) :
    HSOp (outputSupportMatrixCornerModel Φ).dim :=
  conjHSOp (fullSupportIso Φ hΦ1) (leftMul A)

private theorem fullSupportToMat_conj_leftMul {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) (A : Mₙ m) :
    fullSupportConjLeftMulTarget Φ hΦ1 A =
      leftMul (fullSupportToMat Φ hΦ1 A) := by
  ext X i j
  simpa [fullSupportConjLeftMulTarget, conjHSOp] using
    congrArg (fun M : Mₙ (outputSupportMatrixCornerModel Φ).dim => M i j)
      (fullSupportToMat_map_mul Φ hΦ1 A
        ((fullSupportToMat Φ hΦ1).symm X))

private noncomputable def fullSupportConjRightMulTarget {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) (B : Mₙ m) :
    HSOp (outputSupportMatrixCornerModel Φ).dim :=
  conjHSOp (fullSupportIso Φ hΦ1) (rightMul B)

private theorem fullSupportToMat_conj_rightMul {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) (B : Mₙ m) :
    fullSupportConjRightMulTarget Φ hΦ1 B =
      rightMul (fullSupportToMat Φ hΦ1 B) := by
  ext X i j
  simpa [fullSupportConjRightMulTarget, conjHSOp] using
    congrArg (fun M : Mₙ (outputSupportMatrixCornerModel Φ).dim => M i j)
      (fullSupportToMat_map_mul Φ hΦ1
        ((fullSupportToMat Φ hΦ1).symm X) B)

private noncomputable def fullSupportConjJArgTarget {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) (A B : Mₙ m) :
    HSOp (outputSupportMatrixCornerModel Φ).dim :=
  conjHSOp (fullSupportIso Φ hΦ1) (jArg A B)

private theorem fullSupportToMat_conj_jArg {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) {A B : Mₙ m}
    (hB : MatrixPosDef B) :
    fullSupportConjJArgTarget Φ hΦ1 A B =
      jArg (fullSupportToMat Φ hΦ1 A)
        (fullSupportToMat Φ hΦ1 B) := by
  rw [fullSupportConjJArgTarget]
  change conjHSOp (fullSupportIso Φ hΦ1)
      ((rightMul (posInv B)) * leftMul A) =
    (rightMul (posInv (fullSupportToMat Φ hΦ1 B))) *
      leftMul (fullSupportToMat Φ hΦ1 A)
  rw [conjHSOp_mul]
  change fullSupportConjRightMulTarget Φ hΦ1 (posInv B) *
      fullSupportConjLeftMulTarget Φ hΦ1 A =
    (rightMul (posInv (fullSupportToMat Φ hΦ1 B))) *
      leftMul (fullSupportToMat Φ hΦ1 A)
  rw [fullSupportToMat_conj_rightMul, fullSupportToMat_conj_leftMul,
    fullSupportToMat_map_posInv Φ hΦ1 hB]

private noncomputable def fullSupportConjJOperatorTarget {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) (f : ℝ → ℝ) (A B : Mₙ m) :
    HSOp (outputSupportMatrixCornerModel Φ).dim :=
  conjHSOp (fullSupportIso Φ hΦ1) (jOperator f A B)

private theorem fullSupportToMat_conj_jOperator {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) {A B : Mₙ m}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    fullSupportConjJOperatorTarget Φ hΦ1 f A B =
      jOperator f (fullSupportToMat Φ hΦ1 A)
        (fullSupportToMat Φ hΦ1 B) := by
  letI : NormedAddCommGroup (Mₙ m) := outputSupportBridgeMatrixNormedAddCommGroup (n := m)
  letI : NormedSpace ℂ (Mₙ m) := outputSupportBridgeMatrixNormedSpace (n := m)
  letI : InnerProductSpace ℂ (Mₙ m) := outputSupportBridgeMatrixInnerProductSpace (n := m)
  letI : CompleteSpace (Mₙ m) := outputSupportBridgeMatrixCompleteSpace (n := m)
  letI : FiniteDimensional ℂ (Mₙ m) := outputSupportBridgeMatrixFiniteDimensional (n := m)
  let k := (outputSupportMatrixCornerModel Φ).dim
  letI : NormedAddCommGroup (Mₙ k) := outputSupportBridgeMatrixNormedAddCommGroup (n := k)
  letI : NormedSpace ℂ (Mₙ k) := outputSupportBridgeMatrixNormedSpace (n := k)
  letI : InnerProductSpace ℂ (Mₙ k) := outputSupportBridgeMatrixInnerProductSpace (n := k)
  letI : CompleteSpace (Mₙ k) := outputSupportBridgeMatrixCompleteSpace (n := k)
  letI : FiniteDimensional ℂ (Mₙ k) := outputSupportBridgeMatrixFiniteDimensional (n := k)
  letI : NormedAddCommGroup (Mₙ (outputSupportMatrixCornerModel Φ).dim) :=
    outputSupportBridgeMatrixNormedAddCommGroup (n := (outputSupportMatrixCornerModel Φ).dim)
  letI : NormedSpace ℂ (Mₙ (outputSupportMatrixCornerModel Φ).dim) :=
    outputSupportBridgeMatrixNormedSpace (n := (outputSupportMatrixCornerModel Φ).dim)
  letI : InnerProductSpace ℂ (Mₙ (outputSupportMatrixCornerModel Φ).dim) :=
    outputSupportBridgeMatrixInnerProductSpace (n := (outputSupportMatrixCornerModel Φ).dim)
  letI : CompleteSpace (Mₙ (outputSupportMatrixCornerModel Φ).dim) :=
    outputSupportBridgeMatrixCompleteSpace (n := (outputSupportMatrixCornerModel Φ).dim)
  letI : FiniteDimensional ℂ (Mₙ (outputSupportMatrixCornerModel Φ).dim) :=
    outputSupportBridgeMatrixFiniteDimensional (n := (outputSupportMatrixCornerModel Φ).dim)
  let eIso : Mₙ m ≃ₗᵢ[ℂ] Mₙ k := fullSupportIso Φ hΦ1
  let Φ₀ : HSOp m ≃⋆ₐ[ℂ] HSOp k :=
    @LinearIsometryEquiv.conjStarAlgEquiv ℂ
      (inferInstance : RCLike ℂ)
      (Mₙ m)
      (outputSupportBridgeMatrixNormedAddCommGroup (n := m))
      (outputSupportBridgeMatrixInnerProductSpace (n := m))
      (outputSupportBridgeMatrixCompleteSpace (n := m))
      (Mₙ k)
      (outputSupportBridgeMatrixNormedAddCommGroup (n := k))
      (outputSupportBridgeMatrixInnerProductSpace (n := k))
      (outputSupportBridgeMatrixCompleteSpace (n := k))
      eIso
  let Φop : HSOp m →⋆ₐ[ℂ] HSOp k :=
    { Φ₀.toAlgEquiv.toAlgHom with
      map_star' := by
        intro T
        simpa [Φ₀] using Φ₀.map_star' T }
  have hsrc : IsSelfAdjoint (jArg A B) := by
    simpa using jArg_isSelfAdjoint_of_matrixPosDef hA hB
  have hcont :
      ContinuousOn f (spectrum ℝ (jArg A B)) := by
    exact hf.mono (spectrum_jArg_subset_Ioi_local hA hB)
  have hφa :
      IsSelfAdjoint (Φop (jArg A B)) := by
    have hEq : Φop (star (jArg A B)) = Φop (jArg A B) := congrArg Φop hsrc
    simpa [map_star] using hEq
  have hφ :
      Continuous Φop := by
    simpa [Φ₀, Φop, LinearIsometryEquiv.conjStarAlgEquiv_apply,
      ContinuousLinearEquiv.conjContinuousAlgEquiv_apply, ContinuousLinearMap.comp_assoc] using
      eIso.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous_toFun
  have hmap :
      Φ₀ (hsCfcR f (jArg A B)) = hsCfcR f (Φ₀ (jArg A B)) := by
    simpa [Φop] using
      (StarAlgHomClass.map_cfc (φ := Φop) (f := f) (a := jArg A B)
        (hf := hcont)
        (hφ := hφ)
        (ha := hsrc) (hφa := hφa))
  have hright :
      Φ₀ (rightMul B) = rightMul (fullSupportToMat Φ hΦ1 B) := by
    simpa [Φ₀, fullSupportConjRightMulTarget, conjHSOp,
      LinearIsometryEquiv.conjStarAlgEquiv_apply] using
      fullSupportToMat_conj_rightMul Φ hΦ1 B
  calc
    Φ₀ (jOperator f A B)
        = Φ₀ (hsCfcR f (jArg A B)) *
            rightMul (fullSupportToMat Φ hΦ1 B) := by
              rw [jOperator]
              calc
                Φ₀ (hsCfcR f (jArg A B) * rightMul B)
                    = Φ₀ (hsCfcR f (jArg A B)) * Φ₀ (rightMul B) := by
                        simp
                _ = Φ₀ (hsCfcR f (jArg A B)) *
                      rightMul (fullSupportToMat Φ hΦ1 B) := by
                        rw [hright]
    _ = hsCfcR f (Φ₀ (jArg A B)) * rightMul (fullSupportToMat Φ hΦ1 B) := by
            rw [hmap]
    _ = jOperator f (fullSupportToMat Φ hΦ1 A)
          (fullSupportToMat Φ hΦ1 B) := by
            rw [show Φ₀ (jArg A B) =
                jArg (fullSupportToMat Φ hΦ1 A) (fullSupportToMat Φ hΦ1 B) by
                  simpa [Φ₀] using fullSupportToMat_conj_jArg Φ hΦ1 hB]
            rfl

private theorem outputSupportReducedMap_eq_fullSupportToMat {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    outputSupportReducedMap Φ hPos =
      (fullSupportIso Φ hΦ1).toContinuousLinearMap.comp Φ := by
  ext X
  rw [outputSupportReducedMap_eq_of_posDef (hΦ1 := hΦ1)]
  rfl

private theorem outputSupportReducedMap_hsAdjoint_eq_fullSupportToMat {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    hsAdjoint (outputSupportReducedMap Φ hPos) =
      (hsAdjoint Φ).comp (fullSupportIso Φ hΦ1).symm.toContinuousLinearMap := by
  ext Y
  rw [outputSupportReducedMap_hsAdjoint_apply]
  rw [fullSupportToMat_symm_apply_val (Φ := Φ) (hΦ1 := hΦ1)]
  rfl

private noncomputable def outputSupportReducedMapDirectConjTarget {n m : ℕ}
    (Φ : HSMap n m) (_hPos : IsPositiveMap Φ) (f : ℝ → ℝ) (A B : Mₙ n)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    HSOp (outputSupportMatrixCornerModel Φ).dim :=
  conjHSOp (fullSupportIso Φ hΦ1)
    (Φ.comp ((jOperator f A B).comp (hsAdjoint Φ)))

private theorem outputSupportReducedMap_direct_conj {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (f : ℝ → ℝ) {A B : Mₙ n}
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    (outputSupportReducedMap Φ hPos).comp
        ((jOperator f A B).comp (hsAdjoint (outputSupportReducedMap Φ hPos))) =
      outputSupportReducedMapDirectConjTarget Φ hPos f A B hΦ1 := by
  ext Y i j
  rw [outputSupportReducedMap_hsAdjoint_eq_fullSupportToMat (Φ := Φ) (hPos := hPos) (hΦ1 := hΦ1)]
  rw [outputSupportReducedMap_eq_fullSupportToMat (Φ := Φ) (hPos := hPos) (hΦ1 := hΦ1)]
  rfl

private noncomputable def outputSupportReducedMapJOperatorConjTarget {n m : ℕ}
    (Φ : HSMap n m) (_hPos : IsPositiveMap Φ) (f : ℝ → ℝ) (A B : Mₙ n)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    HSOp (outputSupportMatrixCornerModel Φ).dim :=
  conjHSOp (fullSupportIso Φ hΦ1) (jOperator f (Φ A) (Φ B))

private theorem outputSupportReducedMap_jOperator_conj {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) {A B : Mₙ n}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    jOperator f (outputSupportReducedMap Φ hPos A) (outputSupportReducedMap Φ hPos B) =
      outputSupportReducedMapJOperatorConjTarget Φ hPos f A B hΦ1 := by
  letI : NormedAddCommGroup (Mₙ m) := outputSupportBridgeMatrixNormedAddCommGroup (n := m)
  letI : NormedSpace ℂ (Mₙ m) := outputSupportBridgeMatrixNormedSpace (n := m)
  letI : InnerProductSpace ℂ (Mₙ m) := outputSupportBridgeMatrixInnerProductSpace (n := m)
  letI : CompleteSpace (Mₙ m) := outputSupportBridgeMatrixCompleteSpace (n := m)
  letI : FiniteDimensional ℂ (Mₙ m) := outputSupportBridgeMatrixFiniteDimensional (n := m)
  letI : NormedAddCommGroup (Mₙ (outputSupportMatrixCornerModel Φ).dim) :=
    outputSupportBridgeMatrixNormedAddCommGroup (n := (outputSupportMatrixCornerModel Φ).dim)
  letI : NormedSpace ℂ (Mₙ (outputSupportMatrixCornerModel Φ).dim) :=
    outputSupportBridgeMatrixNormedSpace (n := (outputSupportMatrixCornerModel Φ).dim)
  letI : InnerProductSpace ℂ (Mₙ (outputSupportMatrixCornerModel Φ).dim) :=
    outputSupportBridgeMatrixInnerProductSpace (n := (outputSupportMatrixCornerModel Φ).dim)
  letI : CompleteSpace (Mₙ (outputSupportMatrixCornerModel Φ).dim) :=
    outputSupportBridgeMatrixCompleteSpace (n := (outputSupportMatrixCornerModel Φ).dim)
  letI : FiniteDimensional ℂ (Mₙ (outputSupportMatrixCornerModel Φ).dim) :=
    outputSupportBridgeMatrixFiniteDimensional (n := (outputSupportMatrixCornerModel Φ).dim)
  have hΦA : MatrixPosDef (Φ A) :=
    isPositiveMap_matrixPosDef_of_map_one_matrixPosDef Φ hPos hΦ1 hA
  have hΦB : MatrixPosDef (Φ B) :=
    isPositiveMap_matrixPosDef_of_map_one_matrixPosDef Φ hPos hΦ1 hB
  rw [outputSupportReducedMap_eq_of_posDef (hΦ1 := hΦ1),
    outputSupportReducedMap_eq_of_posDef (hΦ1 := hΦ1)]
  simpa [outputSupportReducedMapJOperatorConjTarget, fullSupportIso, fullSupportToMat,
      fullSupportToMatLinearEquiv_apply] using
    (fullSupportToMat_conj_jOperator Φ hΦ1 f hf (A := Φ A) (B := Φ B) hΦA hΦB).symm

private noncomputable abbrev fullSupportSourceOp {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (A B : Mₙ n) : HSOp m :=
  Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))

private noncomputable abbrev fullSupportTargetOp {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (A B : Mₙ n) : HSOp m :=
  jOperator f (Φ A) (Φ B)

private abbrev fullSupportConditionIIIProp {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (A B : Mₙ n) : Prop :=
  HSLE (fullSupportSourceOp f Φ A B) (fullSupportTargetOp f Φ A B)

-- Full-support transport expands the matrix model and conjugation equivalence.
private theorem strictConditionIII_of_general_fullSupport (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) {n m : ℕ} (Φ : HSMap n m)
    (hIII : ConditionIII_general f Φ)
    {A B : Mₙ n} (hPos : IsPositiveMap Φ) (hTrace : _root_.HiaiPetz.TracePreserving Φ)
    (hSch : HSAdjointSchwarz Φ) (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    fullSupportConditionIIIProp f Φ A B := by
  let e := fullSupportIso Φ hΦ1
  have hred :
      HSLE
        ((outputSupportReducedMap Φ hPos).comp
          ((jOperator f A B).comp (hsAdjoint (outputSupportReducedMap Φ hPos))))
        (jOperator f (outputSupportReducedMap Φ hPos A)
          (outputSupportReducedMap Φ hPos B)) := by
    simpa [ConditionIII_general, outputSupportReducedHSMap] using
      hIII (A := A) (B := B) hPos hTrace hSch hA hB
  have hconj :
      HSLE
        (conjHSOp e (fullSupportSourceOp f Φ A B))
        (conjHSOp e (fullSupportTargetOp f Φ A B)) := by
    have hred₁ :
        HSLE
          (outputSupportReducedMapDirectConjTarget Φ hPos f A B hΦ1)
          (jOperator f (outputSupportReducedMap Φ hPos A)
            (outputSupportReducedMap Φ hPos B)) := by
      exact
        (outputSupportReducedMap_direct_conj
          (Φ := Φ) (hPos := hPos) (f := f) (A := A) (B := B) (hΦ1 := hΦ1)).symm ▸ hred
    have hred' :
        HSLE
          (outputSupportReducedMapDirectConjTarget Φ hPos f A B hΦ1)
          (outputSupportReducedMapJOperatorConjTarget Φ hPos f A B hΦ1) := by
      exact
        (outputSupportReducedMap_jOperator_conj
          (Φ := Φ) (hPos := hPos) (f := f) (hf := hf)
          (A := A) (B := B) (hA := hA) (hB := hB) (hΦ1 := hΦ1)) ▸ hred₁
    simpa [fullSupportSourceOp, fullSupportTargetOp,
      outputSupportReducedMapDirectConjTarget, outputSupportReducedMapJOperatorConjTarget, e] using
      hred'
  unfold fullSupportConditionIIIProp
  rw [HSLE] at hconj ⊢
  have hconjNonneg :
      HSNonneg
        (conjHSOp e (fullSupportTargetOp f Φ A B) -
          conjHSOp e (fullSupportSourceOp f Φ A B)) := hconj
  have hconjMapped :
      HSNonneg
        (conjHSOp e
          (fullSupportTargetOp f Φ A B - fullSupportSourceOp f Φ A B)) := by
    rw [conjHSOp_map_sub]
    exact hconjNonneg
  intro X
  have hX := hconjMapped (e X)
  have hInner :
      inner ℂ (e X)
          ((conjHSOp e
            (fullSupportTargetOp f Φ A B - fullSupportSourceOp f Φ A B)) (e X)) =
        inner ℂ X ((fullSupportTargetOp f Φ A B - fullSupportSourceOp f Φ A B) X) := by
    rw [conjHSOp_apply, e.symm_apply_apply]
    exact e.inner_map_map X ((fullSupportTargetOp f Φ A B - fullSupportSourceOp f Φ A B) X)
  have hTrace :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (e X) *
              ((conjHSOp e (fullSupportTargetOp f Φ A B - fullSupportSourceOp f Φ A B)) (e X)))) =
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((fullSupportTargetOp f Φ A B - fullSupportSourceOp f Φ A B) X))) := by
    calc
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (e X) *
              ((conjHSOp e (fullSupportTargetOp f Φ A B - fullSupportSourceOp f Φ A B)) (e X))))
          =
        Complex.re
          (Matrix.trace
            (((conjHSOp e (fullSupportTargetOp f Φ A B - fullSupportSourceOp f Φ A B)) (e X)) *
              Matrix.conjTranspose (e X))) := by
        rw [Matrix.trace_mul_comm]
      _ = Complex.re
          (inner ℂ (e X)
            ((conjHSOp e (fullSupportTargetOp f Φ A B - fullSupportSourceOp f Φ A B)) (e X))) := by
        rfl
      _ = Complex.re
          (inner ℂ X ((fullSupportTargetOp f Φ A B - fullSupportSourceOp f Φ A B) X)) := by
        rw [hInner]
      _ = Complex.re
          (Matrix.trace
            ((fullSupportTargetOp f Φ A B - fullSupportSourceOp f Φ A B) X *
              Matrix.conjTranspose X)) := by
        rfl
      _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((fullSupportTargetOp f Φ A B - fullSupportSourceOp f Φ A B) X))) := by
        rw [Matrix.trace_mul_comm]
  simpa [HSNonneg] using hTrace ▸ hX

/-! ### Final Hiai-Petz 6.2 Output-Support Wrappers -/

/-- General direct data processing implies the quasi-entropy joint concavity condition by
trivializing the full-support case and applying the strict-output bridge. -/
theorem conditionIII_general_implies_conditionIV (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hIII : ∀ {n m : ℕ} (Φ : HSMap n m), ConditionIII_general f Φ) :
    QuasiEntropyDPI.quasiEntropyJointConcavityCondition f := by
  apply jointConcavity_of_strictDirectDPI f hf
  intro n m Φ A B hPos hTrace hSch hA hB hΦ1
  exact strictConditionIII_of_general_fullSupport (f := f) (hf := hf) Φ (hIII Φ)
    hPos hTrace hSch hA hB hΦ1

/-- Proof-facing aggregate statement for the output-support layer of Hiai--Petz 6.2.
Theorem 6.2 of [hiai2025]. -/
def outputSupportQuasiEntropyDpiPackageStmt (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ioi (0 : ℝ)) →
  (∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) →
    (ConditionI f → ConditionIII f) ∧
    (ConditionII f ↔ ConditionIII f) ∧
    (ConditionIII f → QuasiEntropyDPI.quasiEntropyJointConcavityCondition f) ∧
    (QuasiEntropyDPI.quasiEntropyJointConcavityCondition f →
      QuasiEntropyDPI.matrixMonotoneConditionMatrix f) ∧
    (QuasiEntropyDPI.matrixMonotoneConditionMatrix f → ConditionI f)

/-- Book-facing aggregate statement for the output-support layer of Hiai--Petz 6.2.
Theorem 6.2 of [hiai2025]. -/
def bookOutputSupportQuasiEntropyDpiPackageStmt (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ioi (0 : ℝ)) →
  (∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) →
    (ConditionI f → ConditionIII_book f) ∧
    (ConditionII_book f ↔ ConditionIII_book f) ∧
    (ConditionIII_book f → QuasiEntropyDPI.quasiEntropyJointConcavityCondition f) ∧
    (QuasiEntropyDPI.quasiEntropyJointConcavityCondition f →
      QuasiEntropyDPI.matrixMonotoneConditionMatrix f) ∧
    (QuasiEntropyDPI.matrixMonotoneConditionMatrix f → ConditionI f)

/-- Output-support wrapper for `(i) -> (iii)`.
Theorem 6.2 of [hiai2025]. -/
theorem matrix_monotone_to_output_support_direct_dpi (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hposf : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    ConditionI f → ConditionIII f := by
  intro hI
  change ∀ {n m : ℕ} (Φ : HSMap n m), ConditionIII_general f Φ
  intro n m Φ
  exact conditionI_implies_conditionIII_general f hf hposf hI Φ

/-- Output-support wrapper for `(ii) <-> (iii)`.
Theorem 6.2 of [hiai2025]. -/
theorem output_support_inverse_dpi_iff_direct_dpi (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hposf : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    ConditionII f ↔ ConditionIII f := by
  constructor
  · intro hII
    change ∀ {n m : ℕ} (Φ : HSMap n m), ConditionIII_general f Φ
    intro n m Φ
    exact (conditionII_general_iff_conditionIII_general f hf hposf Φ).1 (hII Φ)
  · intro hIII
    change ∀ {n m : ℕ} (Φ : HSMap n m), ConditionII_general f Φ
    intro n m Φ
    exact (conditionII_general_iff_conditionIII_general f hf hposf Φ).2 (hIII Φ)

/-- Output-support wrapper for `(iii) -> (iv)`.
Theorem 6.2 of [hiai2025]. -/
theorem output_support_direct_dpi_to_quasiEntropy_jointConcavity (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    ConditionIII f → QuasiEntropyDPI.quasiEntropyJointConcavityCondition f := by
  intro hIII
  exact conditionIII_general_implies_conditionIV f hf hIII

/-- Output-support wrapper for `(iv) -> (i_matrix)`.
Theorem 6.2 of [hiai2025]. -/
theorem quasiEntropy_jointConcavity_to_matrix_monotone (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hposf : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    QuasiEntropyDPI.quasiEntropyJointConcavityCondition f →
      QuasiEntropyDPI.matrixMonotoneConditionMatrix f := by
  exact quasiEntropy_conditionIV_to_conditionI_matrix f hf hposf

/-- Output-support wrapper for `(i_matrix) -> (i)`.
Theorem 6.2 of [hiai2025]. -/
theorem output_support_matrix_condition_to_conditionI (f : ℝ → ℝ) :
    QuasiEntropyDPI.matrixMonotoneConditionMatrix f → ConditionI f := by
  exact matrix_surface_condition_to_conditionI f

/-- Internal proof-facing output-support package.
Theorem 6.2 of [hiai2025]. -/
theorem output_support_quasiEntropy_dpi_package_via_loewner {f : ℝ → ℝ} :
    outputSupportQuasiEntropyDpiPackageStmt f := by
  intro hf hposf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact matrix_monotone_to_output_support_direct_dpi f hf hposf
  · exact output_support_inverse_dpi_iff_direct_dpi f hf hposf
  · exact output_support_direct_dpi_to_quasiEntropy_jointConcavity f hf
  · exact quasiEntropy_jointConcavity_to_matrix_monotone f hf hposf
  · exact output_support_matrix_condition_to_conditionI f

/-- Public reduced output-support Hiai--Petz 6.2 package via the Carlen--Loewner route.
Theorem 6.2 of [hiai2025]. -/
theorem book_output_support_quasiEntropy_dpi_package_via_loewner {f : ℝ → ℝ} :
    bookOutputSupportQuasiEntropyDpiPackageStmt f := by
  intro hf hposf
  rcases output_support_quasiEntropy_dpi_package_via_loewner (f := f) hf hposf with
    ⟨hItoIII, hIIiffIII, hIIItoIV, hIVtoI_matrix, hI_matrix_toI⟩
  refine ⟨?_, ?_, ?_, hIVtoI_matrix, hI_matrix_toI⟩
  · intro hI
    exact (ConditionIII_book_iff_ConditionIII f).2 (hItoIII hI)
  · constructor
    · intro hIIbook
      exact (ConditionIII_book_iff_ConditionIII f).2
        (hIIiffIII.1 ((ConditionII_book_iff_ConditionII f).1 hIIbook))
    · intro hIIIbook
      exact (ConditionII_book_iff_ConditionII f).2
        (hIIiffIII.2 ((ConditionIII_book_iff_ConditionIII f).1 hIIIbook))
  · intro hIIIbook
    exact hIIItoIV ((ConditionIII_book_iff_ConditionIII f).1 hIIIbook)

/-- Alias name emphasizing the Carlen operator-monotonicity route.
Theorem 6.2 of [hiai2025]. -/
theorem book_output_support_quasiEntropy_dpi_package_via_carlen_opmontI {f : ℝ → ℝ} :
    bookOutputSupportQuasiEntropyDpiPackageStmt f :=
  book_output_support_quasiEntropy_dpi_package_via_loewner

end

end Quantum.TraceInequality.Loewner.HiaiPetz
