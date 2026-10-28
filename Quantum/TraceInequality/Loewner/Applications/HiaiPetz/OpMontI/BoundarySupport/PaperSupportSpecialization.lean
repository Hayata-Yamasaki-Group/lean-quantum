/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import
Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.BoundarySupport.SupportInfrastructure
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.ConditionOneRetained
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.CFCTransportRetained
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.ConditionsRetained
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.RankOneBridgeRetained
import Quantum.TraceInequality.TraceFunctionMonotonicity.Petz.LiebRuskai
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.SharedStages
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.JointConcavityToMonotone

/-!
# Carlen 2022 Theorem 1.46 boundary-support specialization

This module keeps the paper-support specialization stage while the
boundary-support infrastructure is split into its own imported module.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder Matrix.Norms.Frobenius

noncomputable section

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace
  carlenBoundaryHSOpCStarAlgebra
  carlenBoundaryHSOpStarRing
  carlenBoundaryHSOpComplexAlgebra
  carlenBoundaryHSOpNormedAlgebra
  carlenBoundaryHSOpPartialOrder
  carlenBoundaryHSOpStarOrderedRing
  carlenBoundaryHSOpNonnegSpectrumClass
  carlenBoundaryHSOpComplexCFC
  carlenBoundaryHSOpRealCFC

/-! ### Support Conditions and Strict-Reduced Rewriting -/
/-- Carlen inverse condition after reducing the input support of the adjoint images. -/
def CarlenOpMontICondition2_inputSupportReduced (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {X Y : Mₙ m},
    (hΦ : IsUnitalTwoPositiveMap Φ) →
    MatrixPosDef X →
    MatrixPosDef Y →
    let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
    let Ψ := carlenInputSupportReducedMap Φ hAdjPos
    HSLE
      (Ψ.comp
        ((gOperatorInv f (hsAdjoint Ψ X) (hsAdjoint Ψ Y)).comp (hsAdjoint Ψ)))
      (gOperatorInv f X Y)

/-- Carlen direct condition after reducing the input support of the adjoint images. -/
def CarlenOpMontICondition3_inputSupportReduced (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {X Y : Mₙ m},
    (hΦ : IsUnitalTwoPositiveMap Φ) →
    MatrixPosDef X →
    MatrixPosDef Y →
    let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
    let Ψ := carlenInputSupportReducedMap Φ hAdjPos
    HSLE
      ((hsAdjoint Ψ).comp ((gOperator f X Y).comp Ψ))
      (gOperator f (hsAdjoint Ψ X) (hsAdjoint Ψ Y))

/-- Carlen support-corner inverse condition, with the raw support `G_f^{-1}` transported to
the canonical input-support matrix model. -/
def CarlenOpMontICondition2_support (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {X Y : Mₙ m},
    (hΦ : IsUnitalTwoPositiveMap Φ) →
    MatrixPosDef X →
    MatrixPosDef Y →
    let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
    let Ψ := carlenInputSupportReducedMap Φ hAdjPos
    HSLE
      (Ψ.comp
        ((carlenSupportGOperatorInvModelConj f Φ hAdjPos X Y).comp (hsAdjoint Ψ)))
      (gOperatorInv f X Y)

/-- Carlen support-corner direct condition, with the raw support `G_f` transported to the
canonical input-support matrix model. -/
def CarlenOpMontICondition3_support (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {X Y : Mₙ m},
    (hΦ : IsUnitalTwoPositiveMap Φ) →
    MatrixPosDef X →
    MatrixPosDef Y →
    let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
    let Ψ := carlenInputSupportReducedMap Φ hAdjPos
    HSLE
      ((hsAdjoint Ψ).comp ((gOperator f X Y).comp Ψ))
      (carlenSupportGOperatorModelConj f Φ hAdjPos X Y)

/-- The raw support-corner inverse condition is exactly the strict reduced inverse condition. -/
theorem carlenCondition2_support_iff_strictReduced (f : ℝ → ℝ) :
    CarlenOpMontICondition2_support f ↔
      CarlenOpMontICondition2_inputSupportReduced f := by
  constructor
  · intro hII n m Φ X Y hΦ hX hY
    let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
    simpa [CarlenOpMontICondition2_support, CarlenOpMontICondition2_inputSupportReduced,
      hAdjPos, carlenSupportGOperatorInv_conj_eq_reducedMap_gOperatorInv,
      carlenInputSupportReducedMap_hsAdjoint_apply] using
      (hII (n := n) (m := m) Φ (X := X) (Y := Y) hΦ hX hY)
  · intro hII n m Φ X Y hΦ hX hY
    let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
    simpa [CarlenOpMontICondition2_support, CarlenOpMontICondition2_inputSupportReduced,
      hAdjPos, carlenSupportGOperatorInv_conj_eq_reducedMap_gOperatorInv,
      carlenInputSupportReducedMap_hsAdjoint_apply] using
      (hII (n := n) (m := m) Φ (X := X) (Y := Y) hΦ hX hY)

/-- The raw support-corner direct condition is exactly the strict reduced direct condition. -/
theorem carlenCondition3_support_iff_strictReduced (f : ℝ → ℝ) :
    CarlenOpMontICondition3_support f ↔
      CarlenOpMontICondition3_inputSupportReduced f := by
  constructor
  · intro hIII n m Φ X Y hΦ hX hY
    let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
    simpa [CarlenOpMontICondition3_support, CarlenOpMontICondition3_inputSupportReduced,
      hAdjPos, carlenSupportGOperator_conj_eq_reducedMap_gOperator,
      carlenInputSupportReducedMap_hsAdjoint_apply] using
      (hIII (n := n) (m := m) Φ (X := X) (Y := Y) hΦ hX hY)
  · intro hIII n m Φ X Y hΦ hX hY
    let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
    simpa [CarlenOpMontICondition3_support, CarlenOpMontICondition3_inputSupportReduced,
      hAdjPos, carlenSupportGOperator_conj_eq_reducedMap_gOperator,
      carlenInputSupportReducedMap_hsAdjoint_apply] using
      (hIII (n := n) (m := m) Φ (X := X) (Y := Y) hΦ hX hY)

/-! ### Carlen Support C5 and C6 Wrappers -/
/-- On input-support reduced maps, Carlen's inverse and direct conditions are equivalent. -/
theorem carlenCondition2_inputSupportReduced_iff_condition3_inputSupportReduced
    {f : ℝ → ℝ} (hf : CarlenOpMontIFunctionHypothesis f) :
    CarlenOpMontICondition2_inputSupportReduced f ↔
      CarlenOpMontICondition3_inputSupportReduced f := by
  constructor
  · intro hII n m Φ X Y hΦ hX hY
    let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
    let Ψ := carlenInputSupportReducedMap Φ hAdjPos
    have hΨX : MatrixPosDef (hsAdjoint Ψ X) := by
      simpa [Ψ, hAdjPos] using
        carlenInputSupportReducedMap_hsAdjoint_posDef_of_matrixPosDef Φ hAdjPos hX
    have hΨY : MatrixPosDef (hsAdjoint Ψ Y) := by
      simpa [Ψ, hAdjPos] using
        carlenInputSupportReducedMap_hsAdjoint_posDef_of_matrixPosDef Φ hAdjPos hY
    have hΨ : IsUnitalTwoPositiveMap Ψ := by
      simpa [Ψ, hAdjPos] using carlenInputSupportReducedMap_unitalTwoPositive hΦ
    exact
      (gOperator_inverse_dpi_iff_direct_dpi_of_carlenFunctionHypothesis
        Ψ hf hX hY hΨX hΨY).mp
        (by simpa [CarlenOpMontICondition2_inputSupportReduced, Ψ, hAdjPos] using
          (hII (n := n) (m := m) Φ (X := X) (Y := Y) hΦ hX hY))
  · intro hIII n m Φ X Y hΦ hX hY
    let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
    let Ψ := carlenInputSupportReducedMap Φ hAdjPos
    have hΨX : MatrixPosDef (hsAdjoint Ψ X) := by
      simpa [Ψ, hAdjPos] using
        carlenInputSupportReducedMap_hsAdjoint_posDef_of_matrixPosDef Φ hAdjPos hX
    have hΨY : MatrixPosDef (hsAdjoint Ψ Y) := by
      simpa [Ψ, hAdjPos] using
        carlenInputSupportReducedMap_hsAdjoint_posDef_of_matrixPosDef Φ hAdjPos hY
    have hΨ : IsUnitalTwoPositiveMap Ψ := by
      simpa [Ψ, hAdjPos] using carlenInputSupportReducedMap_unitalTwoPositive hΦ
    exact
      (gOperator_inverse_dpi_iff_direct_dpi_of_carlenFunctionHypothesis
        Ψ hf hX hY hΨX hΨY).mpr
        (by simpa [CarlenOpMontICondition3_inputSupportReduced, Ψ, hAdjPos] using
          (hIII (n := n) (m := m) Φ (X := X) (Y := Y) hΦ hX hY))

/-- Carlen condition (1) implies the support-corner direct condition. -/
theorem carlenCondition1_to_condition3_support_of_functionHypothesis
    {f : ℝ → ℝ} (hf : CarlenOpMontIFunctionHypothesis f)
    (h1 : CarlenOpMontICondition1 f) :
    CarlenOpMontICondition3_support f := by
  intro n m Φ X Y hΦ hX hY
  let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
  let Ψ := carlenInputSupportReducedMap Φ hAdjPos
  have hΨ : IsUnitalTwoPositiveMap Ψ := by
    simpa [Ψ, hAdjPos] using carlenInputSupportReducedMap_unitalTwoPositive hΦ
  have hΨX : MatrixPosDef (hsAdjoint Ψ X) := by
    simpa [Ψ, hAdjPos] using
      carlenInputSupportReducedMap_hsAdjoint_posDef_of_matrixPosDef Φ hAdjPos hX
  have hΨY : MatrixPosDef (hsAdjoint Ψ Y) := by
    simpa [Ψ, hAdjPos] using
      carlenInputSupportReducedMap_hsAdjoint_posDef_of_matrixPosDef Φ hAdjPos hY
  have hStrict :=
    condition1_to_condition3_of_functionHypothesis hf h1 Ψ hΨ hX hY hΨX hΨY
  simpa [CarlenOpMontICondition3_support, Ψ, hAdjPos,
    carlenSupportGOperator_conj_eq_reducedMap_gOperator,
    carlenInputSupportReducedMap_hsAdjoint_apply] using hStrict

/-- The support-corner inverse and direct Carlen conditions are equivalent. -/
theorem carlenCondition2_support_iff_condition3_support_of_functionHypothesis
    {f : ℝ → ℝ} (hf : CarlenOpMontIFunctionHypothesis f) :
    CarlenOpMontICondition2_support f ↔ CarlenOpMontICondition3_support f :=
  (carlenCondition2_support_iff_strictReduced f).trans
    ((carlenCondition2_inputSupportReduced_iff_condition3_inputSupportReduced hf).trans
      (carlenCondition3_support_iff_strictReduced f).symm)

/-! ### Full-Support Corner Identifications -/
/-- A positive semidefinite matrix whose support projection is the identity is positive
definite. -/
private theorem carlenMatrixPosDef_of_nonneg_supportProj_eq_one {n : ℕ} {C : Mₙ n}
    (hC : 0 ≤ C) (hsupp : matrixSupportProj C = 1) :
    MatrixPosDef C := by
  have hpsd : C.PosSemidef := (Matrix.nonneg_iff_posSemidef).1 hC
  apply matrixPosDef_of_posDef
  refine (Matrix.PosSemidef.posDef_iff_isUnit hpsd).2 ?_
  have hrange : matrixSupportSubspace C = ⊤ := by
    apply eq_top_iff.2
    intro x _
    have hfix : (matrixSupportProj C).mulVec x = x := by
      simp [hsupp]
    exact (matrixSupportProj_mulVec_eq_self_iff C x).1 hfix
  have hsurj : Function.Surjective C.mulVecLin :=
    LinearMap.range_eq_top.1 hrange
  have hinj : Function.Injective C.mulVecLin :=
    LinearMap.injective_iff_surjective.mpr hsurj
  exact Matrix.mulVec_injective_iff_isUnit.mp (by
    intro x y hxy
    exact hinj (by
      simpa [Matrix.mulVecLin_apply] using hxy))

private noncomputable def carlenFullSupportOneCornerLinearEquiv (n : ℕ) :
    Mₙ n ≃ₗ[ℂ] matrixCornerSubmodule (1 : Mₙ n) where
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

private noncomputable def carlenFullSupportToMatLinearEquiv {n m : ℕ}
    (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m))) :
    Mₙ n ≃ₗ[ℂ] Mₙ (carlenAdjointSupportMatrixCornerModel Φ).dim := by
  let hCorner :
      matrixCornerSubmodule (1 : Mₙ n) =
        matrixCornerSubmodule (carlenAdjointSupportProj Φ) := by
    simp [carlenAdjointSupportProj, outputSupportProj_eq_one_of_posDef (hsAdjoint Φ) hΦ1]
  exact (carlenFullSupportOneCornerLinearEquiv n).trans
    ((LinearEquiv.ofEq _ _ hCorner).trans (carlenAdjointSupportMatrixCornerModel Φ).toMat)

@[simp] private theorem carlenFullSupportToMatLinearEquiv_apply {n m : ℕ}
    (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m))) (X : Mₙ n) :
    carlenFullSupportToMatLinearEquiv Φ hΦ1 X =
      (carlenAdjointSupportMatrixCornerModel Φ).toMat
        ⟨X, by
          simp [carlenAdjointSupportProj,
            outputSupportProj_eq_one_of_posDef (hsAdjoint Φ) hΦ1]⟩ := by
  rfl

private noncomputable def carlenFullSupportToMatLinearIsometryEquiv {n m : ℕ}
    (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m))) :
    Mₙ n ≃ₗᵢ[ℂ] Mₙ (carlenAdjointSupportMatrixCornerModel Φ).dim :=
  (carlenFullSupportToMatLinearEquiv Φ hΦ1).isometryOfInner (by
    intro X Y
    change inner ℂ
        ((carlenAdjointSupportMatrixCornerModel Φ).toMat
          ⟨X, by
            simp [carlenAdjointSupportProj,
              outputSupportProj_eq_one_of_posDef (hsAdjoint Φ) hΦ1]⟩)
        ((carlenAdjointSupportMatrixCornerModel Φ).toMat
          ⟨Y, by
            simp [carlenAdjointSupportProj,
              outputSupportProj_eq_one_of_posDef (hsAdjoint Φ) hΦ1]⟩) =
      inner ℂ X Y
    simpa using
      MatrixCornerModel.inner_toMat_eq (carlenAdjointSupportMatrixCornerModel Φ)
        ⟨X, by
          simp [carlenAdjointSupportProj,
            outputSupportProj_eq_one_of_posDef (hsAdjoint Φ) hΦ1]⟩
        ⟨Y, by
          simp [carlenAdjointSupportProj,
            outputSupportProj_eq_one_of_posDef (hsAdjoint Φ) hΦ1]⟩)

@[simp] private theorem carlenFullSupportToMat_map_mul {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m))) (X Y : Mₙ n) :
    carlenFullSupportToMatLinearEquiv Φ hΦ1 (X * Y) =
      carlenFullSupportToMatLinearEquiv Φ hΦ1 X *
        carlenFullSupportToMatLinearEquiv Φ hΦ1 Y := by
  simpa [carlenFullSupportToMatLinearEquiv_apply] using
    (carlenAdjointSupportMatrixCornerModel Φ).map_mul
      ⟨X, by
        simp [carlenAdjointSupportProj,
          outputSupportProj_eq_one_of_posDef (hsAdjoint Φ) hΦ1]⟩
      ⟨Y, by
        simp [carlenAdjointSupportProj,
          outputSupportProj_eq_one_of_posDef (hsAdjoint Φ) hΦ1]⟩

@[simp] private theorem carlenFullSupportToMat_map_one {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m))) :
    carlenFullSupportToMatLinearEquiv Φ hΦ1 (1 : Mₙ n) = 1 := by
  simpa [carlenFullSupportToMatLinearEquiv_apply, carlenAdjointSupportProj,
    outputSupportProj_eq_one_of_posDef (hsAdjoint Φ) hΦ1] using
    (carlenAdjointSupportMatrixCornerModel Φ).map_proj

private noncomputable abbrev carlenFullSupportToMat {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m))) :
    Mₙ n ≃ₗ[ℂ] Mₙ (carlenAdjointSupportMatrixCornerModel Φ).dim :=
  carlenFullSupportToMatLinearEquiv Φ hΦ1

private noncomputable abbrev carlenFullSupportIso {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m))) :
    Mₙ n ≃ₗᵢ[ℂ] Mₙ (carlenAdjointSupportMatrixCornerModel Φ).dim :=
  carlenFullSupportToMatLinearIsometryEquiv Φ hΦ1

@[simp] private theorem carlenFullSupportIso_apply {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m))) (X : Mₙ n) :
    carlenFullSupportIso Φ hΦ1 X = carlenFullSupportToMat Φ hΦ1 X := by
  rfl

@[simp] private theorem carlenFullSupportIso_symm_apply {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m)))
    (Y : Mₙ (carlenAdjointSupportMatrixCornerModel Φ).dim) :
    (carlenFullSupportIso Φ hΦ1).symm Y =
      (carlenFullSupportToMat Φ hΦ1).symm Y := by
  apply (carlenFullSupportIso Φ hΦ1).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  rw [carlenFullSupportIso_apply]
  exact (LinearEquiv.apply_symm_apply (carlenFullSupportToMat Φ hΦ1) Y).symm

@[simp] private theorem carlenFullSupportToMat_symm_apply {n m : ℕ}
    (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m)))
    (Y : Mₙ (carlenAdjointSupportMatrixCornerModel Φ).dim) :
    (carlenAdjointSupportMatrixCornerModel Φ).toMat.symm Y =
      ⟨(carlenFullSupportToMatLinearEquiv Φ hΦ1).symm Y, by
        simp [carlenAdjointSupportProj,
          outputSupportProj_eq_one_of_posDef (hsAdjoint Φ) hΦ1]⟩ := by
  apply (carlenAdjointSupportMatrixCornerModel Φ).toMat.injective
  calc
    (carlenAdjointSupportMatrixCornerModel Φ).toMat
        ((carlenAdjointSupportMatrixCornerModel Φ).toMat.symm Y) = Y := by
          simp
    _ = (carlenAdjointSupportMatrixCornerModel Φ).toMat
          ⟨(carlenFullSupportToMatLinearEquiv Φ hΦ1).symm Y, by
            simp [carlenAdjointSupportProj,
              outputSupportProj_eq_one_of_posDef (hsAdjoint Φ) hΦ1]⟩ := by
          exact (LinearEquiv.apply_symm_apply (carlenFullSupportToMat Φ hΦ1) Y).symm

@[simp] private theorem carlenFullSupportToMat_symm_apply_val {n m : ℕ}
    (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m)))
    (Y : Mₙ (carlenAdjointSupportMatrixCornerModel Φ).dim) :
    ((carlenAdjointSupportMatrixCornerModel Φ).toMat.symm Y).1 =
      (carlenFullSupportToMatLinearEquiv Φ hΦ1).symm Y := by
  simpa using congrArg Subtype.val (carlenFullSupportToMat_symm_apply Φ hΦ1 Y)

private theorem carlenFullSupportToMat_map_posInv {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m))) {B : Mₙ n}
    (hB : MatrixPosDef B) :
    carlenFullSupportToMatLinearEquiv Φ hΦ1 (posInv B) =
      posInv (carlenFullSupportToMatLinearEquiv Φ hΦ1 B) := by
  rcases matrixPosDef_isUnit hB with ⟨u, rfl⟩
  let Fu : Units (Mₙ (carlenAdjointSupportMatrixCornerModel Φ).dim) := by
    refine
      { val := carlenFullSupportToMatLinearEquiv Φ hΦ1 (u : Mₙ n)
        inv := carlenFullSupportToMatLinearEquiv Φ hΦ1 (((u⁻¹ : Units (Mₙ n)) : Mₙ n))
        val_inv := ?_
        inv_val := ?_ }
    · simpa [carlenFullSupportToMat_map_one Φ hΦ1] using
        (carlenFullSupportToMat_map_mul Φ hΦ1
          (u : Mₙ n) (((u⁻¹ : Units (Mₙ n)) : Mₙ n))).symm
    · simpa [carlenFullSupportToMat_map_one Φ hΦ1] using
        (carlenFullSupportToMat_map_mul Φ hΦ1
          (((u⁻¹ : Units (Mₙ n)) : Mₙ n)) (u : Mₙ n)).symm
  change carlenFullSupportToMatLinearEquiv Φ hΦ1 (((u : Mₙ n)⁻¹)) =
    (carlenFullSupportToMatLinearEquiv Φ hΦ1 (u : Mₙ n))⁻¹
  rw [show ((u : Mₙ n)⁻¹) = (((u⁻¹ : Units (Mₙ n)) : Mₙ n)) by simp]
  rw [show (carlenFullSupportToMatLinearEquiv Φ hΦ1 (u : Mₙ n))⁻¹ =
      (((Fu : Units (Mₙ (carlenAdjointSupportMatrixCornerModel Φ).dim)) :
          Mₙ (carlenAdjointSupportMatrixCornerModel Φ).dim)⁻¹) by simp [Fu]]
  rw [show ((((Fu : Units (Mₙ (carlenAdjointSupportMatrixCornerModel Φ).dim)) :
      Mₙ (carlenAdjointSupportMatrixCornerModel Φ).dim))⁻¹) =
      (((Fu⁻¹ : Units (Mₙ (carlenAdjointSupportMatrixCornerModel Φ).dim)) :
          Mₙ (carlenAdjointSupportMatrixCornerModel Φ).dim)) by simp]
  rfl

/-! ### Full-Support Conjugation of G Operators -/
private noncomputable def carlenFullSupportConjHSOp {m k : ℕ}
    (e : Mₙ m ≃ₗᵢ[ℂ] Mₙ k) (T : HSOp m) : HSOp k :=
  e.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.comp e.symm.toContinuousLinearMap)

@[simp] private theorem carlenFullSupportConjHSOp_apply {m k : ℕ}
    (e : Mₙ m ≃ₗᵢ[ℂ] Mₙ k) (T : HSOp m) (X : Mₙ k) :
    carlenFullSupportConjHSOp e T X = e (T (e.symm X)) := rfl

private theorem carlenFullSupportConjHSOp_mul {m k : ℕ}
    (e : Mₙ m ≃ₗᵢ[ℂ] Mₙ k) (S T : HSOp m) :
    carlenFullSupportConjHSOp e (S * T) =
      carlenFullSupportConjHSOp e S * carlenFullSupportConjHSOp e T := by
  ext X
  simp [carlenFullSupportConjHSOp_apply]

private theorem carlenFullSupportToMat_conj_leftMul {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m))) (A : Mₙ n) :
    carlenFullSupportConjHSOp (carlenFullSupportIso Φ hΦ1) (leftMul A) =
      leftMul (carlenFullSupportToMat Φ hΦ1 A) := by
  ext X i j
  simpa [carlenFullSupportConjHSOp, carlenFullSupportIso,
    carlenFullSupportToMatLinearIsometryEquiv] using
    congrArg (fun M : Mₙ (carlenAdjointSupportMatrixCornerModel Φ).dim => M i j)
      (carlenFullSupportToMat_map_mul Φ hΦ1 A
        ((carlenFullSupportToMat Φ hΦ1).symm X))

private theorem carlenFullSupportToMat_conj_rightMul {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m))) (B : Mₙ n) :
    carlenFullSupportConjHSOp (carlenFullSupportIso Φ hΦ1) (rightMul B) =
      rightMul (carlenFullSupportToMat Φ hΦ1 B) := by
  ext X i j
  simpa [carlenFullSupportConjHSOp, carlenFullSupportIso,
    carlenFullSupportToMatLinearIsometryEquiv] using
    congrArg (fun M : Mₙ (carlenAdjointSupportMatrixCornerModel Φ).dim => M i j)
      (carlenFullSupportToMat_map_mul Φ hΦ1
        ((carlenFullSupportToMat Φ hΦ1).symm X) B)

private theorem carlenFullSupportToMat_conj_gArg {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m))) {A B : Mₙ n}
    (hB : MatrixPosDef B) :
    carlenFullSupportConjHSOp (carlenFullSupportIso Φ hΦ1) (gArg A B) =
      gArg (carlenFullSupportToMat Φ hΦ1 A)
        (carlenFullSupportToMat Φ hΦ1 B) := by
  change carlenFullSupportConjHSOp (carlenFullSupportIso Φ hΦ1)
      ((rightMul A) * leftMul (posInv B)) =
    (rightMul (carlenFullSupportToMat Φ hΦ1 A)) *
      leftMul (posInv (carlenFullSupportToMat Φ hΦ1 B))
  rw [carlenFullSupportConjHSOp_mul]
  rw [carlenFullSupportToMat_conj_rightMul, carlenFullSupportToMat_conj_leftMul,
    carlenFullSupportToMat_map_posInv Φ hΦ1 hB]

private theorem carlenFullSupportToMat_conj_gOperatorInv {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m))) (f : ℝ → ℝ)
    (hf : CarlenOpMontIFunctionHypothesis f) {A B : Mₙ n}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    carlenFullSupportConjHSOp (carlenFullSupportIso Φ hΦ1) (gOperatorInv f A B) =
      gOperatorInv f (carlenFullSupportToMat Φ hΦ1 A)
        (carlenFullSupportToMat Φ hΦ1 B) := by
  let k := (carlenAdjointSupportMatrixCornerModel Φ).dim
  let eIso : Mₙ n ≃ₗᵢ[ℂ] Mₙ k := carlenFullSupportIso Φ hΦ1
  let Φ₀ : HSOp n ≃⋆ₐ[ℂ] HSOp k :=
    @LinearIsometryEquiv.conjStarAlgEquiv ℂ
      (inferInstance : RCLike ℂ)
      (Mₙ n)
      (outputSupportBridgeMatrixNormedAddCommGroup (n := n))
      (outputSupportBridgeMatrixInnerProductSpace (n := n))
      (outputSupportBridgeMatrixCompleteSpace (n := n))
      (Mₙ k)
      (outputSupportBridgeMatrixNormedAddCommGroup (n := k))
      (outputSupportBridgeMatrixInnerProductSpace (n := k))
      (outputSupportBridgeMatrixCompleteSpace (n := k))
      eIso
  let Φop : HSOp n →⋆ₐ[ℂ] HSOp k :=
    { Φ₀.toAlgEquiv.toAlgHom with
      map_star' := by
        intro T
        simpa [Φ₀] using Φ₀.map_star' T }
  have hsrc : IsSelfAdjoint (gArg A B) := by
    simpa using gArg_isSelfAdjoint_of_matrixPosDef hA hB
  have hσ : spectrum ℝ (gArg A B) ⊆ Set.Ioi (0 : ℝ) :=
    gArg_spectrum_subset_Ioi_of_matrixPosDef hA hB
  have hcont :
      ContinuousOn (fun x : ℝ ↦ (f x)⁻¹) (spectrum ℝ (gArg A B)) := by
    have hfcont : ContinuousOn f (spectrum ℝ (gArg A B)) :=
      hf.1.mono hσ
    have hnonzero : ∀ x ∈ spectrum ℝ (gArg A B), f x ≠ 0 := by
      intro x hx
      exact ne_of_gt (hf.2 (hσ hx))
    exact hfcont.inv₀ hnonzero
  have hφa :
      IsSelfAdjoint (Φop (gArg A B)) := by
    have hEq : Φop (star (gArg A B)) = Φop (gArg A B) := congrArg Φop hsrc
    simpa [map_star] using hEq
  have hφ : Continuous Φop := by
    simpa [Φ₀, Φop, LinearIsometryEquiv.conjStarAlgEquiv_apply,
      ContinuousLinearEquiv.conjContinuousAlgEquiv_apply, ContinuousLinearMap.comp_assoc] using
      eIso.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous_toFun
  have hmap :
      Φ₀ (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (gArg A B)) =
        hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (Φ₀ (gArg A B)) := by
    simpa [Φop] using
      (StarAlgHomClass.map_cfc (φ := Φop) (f := fun x : ℝ ↦ (f x)⁻¹)
        (a := gArg A B)
        (hf := hcont)
        (hφ := hφ)
        (ha := hsrc) (hφa := hφa))
  have hleft :
      Φ₀ (leftMul (posInv B)) =
        leftMul (posInv (carlenFullSupportToMat Φ hΦ1 B)) := by
    have hraw := carlenFullSupportToMat_conj_leftMul Φ hΦ1 (posInv B)
    have hmap := carlenFullSupportToMat_map_posInv Φ hΦ1 hB
    simpa [Φ₀, carlenFullSupportConjHSOp, LinearIsometryEquiv.conjStarAlgEquiv_apply,
      carlenFullSupportToMatLinearEquiv_apply, hmap] using hraw
  calc
    Φ₀ (gOperatorInv f A B)
        = Φ₀ (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (gArg A B)) *
            leftMul (posInv (carlenFullSupportToMat Φ hΦ1 B)) := by
              rw [gOperatorInv]
              calc
                Φ₀ (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (gArg A B) * leftMul (posInv B))
                    = Φ₀ (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (gArg A B)) *
                        Φ₀ (leftMul (posInv B)) := by
                        simp
                _ = Φ₀ (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (gArg A B)) *
                      leftMul (posInv (carlenFullSupportToMat Φ hΦ1 B)) := by
                        rw [hleft]
    _ = hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (Φ₀ (gArg A B)) *
        leftMul (posInv (carlenFullSupportToMat Φ hΦ1 B)) := by
            rw [hmap]
    _ = gOperatorInv f (carlenFullSupportToMat Φ hΦ1 A)
          (carlenFullSupportToMat Φ hΦ1 B) := by
            rw [show Φ₀ (gArg A B) =
                gArg (carlenFullSupportToMat Φ hΦ1 A)
                  (carlenFullSupportToMat Φ hΦ1 B) by
                  simpa [Φ₀, LinearIsometryEquiv.conjStarAlgEquiv_apply] using
                    carlenFullSupportToMat_conj_gArg Φ hΦ1 hB]
            simp [gOperatorInv]

private theorem carlenInputSupportReducedMap_eq_fullSupport {n m : ℕ}
    (Φ : HSMap n m) (hAdjPos : IsPositiveMap (hsAdjoint Φ))
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m))) :
    carlenInputSupportReducedMap Φ hAdjPos =
      Φ.comp (carlenFullSupportToMat Φ hΦ1).symm.toContinuousLinearMap := by
  ext Y i j
  rw [carlenInputSupportReducedMap, outputSupportReducedHSMap]
  rw [outputSupportReducedMap_hsAdjoint_apply]
  rw [show
      ((outputSupportMatrixCornerModel (hsAdjoint Φ)).toMat.symm Y).1 =
        (carlenFullSupportToMatLinearEquiv Φ hΦ1).symm Y by
      simpa [carlenAdjointSupportMatrixCornerModel] using
        carlenFullSupportToMat_symm_apply_val (Φ := Φ) (hΦ1 := hΦ1) Y]
  change (hsAdjoint (hsAdjoint Φ)) ((carlenFullSupportToMatLinearEquiv Φ hΦ1).symm Y)
      i j =
    Φ ((carlenFullSupportToMatLinearEquiv Φ hΦ1).symm Y) i j
  simp [hsAdjoint_hsAdjoint]

private theorem carlenInputSupportReducedMap_hsAdjoint_eq_fullSupport {n m : ℕ}
    (Φ : HSMap n m) (hAdjPos : IsPositiveMap (hsAdjoint Φ))
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m))) :
    hsAdjoint (carlenInputSupportReducedMap Φ hAdjPos) =
      (carlenFullSupportToMat Φ hΦ1).toContinuousLinearMap.comp (hsAdjoint Φ) := by
  ext X i j
  rw [carlenInputSupportReducedMap_hsAdjoint_apply]
  change (outputSupportReducedMap (hsAdjoint Φ) hAdjPos X) i j =
    (((carlenFullSupportToMat Φ hΦ1).toContinuousLinearMap.comp (hsAdjoint Φ)) X) i j
  rw [outputSupportReducedMap_eq_of_posDef (Φ := hsAdjoint Φ) (hPos := hAdjPos)
    (hΦ1 := hΦ1)]
  rfl

private theorem carlenFullSupport_hsAdjoint_comp_eq {n m : ℕ}
    (Φ : HSMap n m) (hAdjPos : IsPositiveMap (hsAdjoint Φ))
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m))) :
    hsAdjoint (Φ.comp (carlenFullSupportToMat Φ hΦ1).symm.toContinuousLinearMap) =
      (carlenFullSupportToMat Φ hΦ1).toContinuousLinearMap.comp (hsAdjoint Φ) := by
  have hmap :=
    congrArg hsAdjoint (carlenInputSupportReducedMap_eq_fullSupport Φ hAdjPos hΦ1)
  exact hmap.symm.trans
    (carlenInputSupportReducedMap_hsAdjoint_eq_fullSupport Φ hAdjPos hΦ1)

private theorem carlenSupportGOperatorInvModelConj_eq_fullSupportConj {n m : ℕ}
    (Φ : HSMap n m) (hAdjPos : IsPositiveMap (hsAdjoint Φ))
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m))) (f : ℝ → ℝ)
    (hf : CarlenOpMontIFunctionHypothesis f) {X Y : Mₙ m}
    (hΦX : MatrixPosDef (hsAdjoint Φ X)) (hΦY : MatrixPosDef (hsAdjoint Φ Y)) :
    carlenSupportGOperatorInvModelConj f Φ hAdjPos X Y =
      carlenFullSupportConjHSOp (carlenFullSupportIso Φ hΦ1)
        (gOperatorInv f (hsAdjoint Φ X) (hsAdjoint Φ Y)) := by
  have hredX :
      outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos X =
        carlenFullSupportToMat Φ hΦ1 (hsAdjoint Φ X) := by
    have h :=
      congrArg (fun T => T X)
        (carlenInputSupportReducedMap_hsAdjoint_eq_fullSupport Φ hAdjPos hΦ1)
    simpa [carlenInputSupportReducedMap_hsAdjoint_apply] using h
  have hredY :
      outputSupportReducedHSMap (hsAdjoint Φ) hAdjPos Y =
        carlenFullSupportToMat Φ hΦ1 (hsAdjoint Φ Y) := by
    have h :=
      congrArg (fun T => T Y)
        (carlenInputSupportReducedMap_hsAdjoint_eq_fullSupport Φ hAdjPos hΦ1)
    simpa [carlenInputSupportReducedMap_hsAdjoint_apply] using h
  rw [carlenSupportGOperatorInv_conj_eq_reducedMap_gOperatorInv, hredX, hredY]
  exact (carlenFullSupportToMat_conj_gOperatorInv Φ hΦ1 f hf hΦX hΦY).symm

private theorem carlenFullSupport_comp_conj_comp {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m))) (O : HSOp n) :
    (Φ.comp (carlenFullSupportToMat Φ hΦ1).symm.toContinuousLinearMap).comp
        ((carlenFullSupportConjHSOp (carlenFullSupportIso Φ hΦ1) O).comp
          ((carlenFullSupportToMat Φ hΦ1).toContinuousLinearMap.comp (hsAdjoint Φ))) =
      Φ.comp (O.comp (hsAdjoint Φ)) := by
  apply ContinuousLinearMap.ext
  intro Z
  have hInner :
      (carlenFullSupportToMat Φ hΦ1).symm
        ((carlenFullSupportConjHSOp (carlenFullSupportIso Φ hΦ1) O)
          ((carlenFullSupportToMat Φ hΦ1) ((hsAdjoint Φ) Z))) =
        O ((hsAdjoint Φ) Z) := by
    rw [carlenFullSupportConjHSOp_apply]
    rw [carlenFullSupportIso_symm_apply]
    rw [carlenFullSupportIso_apply]
    apply (carlenFullSupportToMat Φ hΦ1).injective
    simp only [carlenFullSupportToMatLinearEquiv_apply, LinearEquiv.apply_symm_apply,
      EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]
    congr 1
    apply (carlenFullSupportToMat Φ hΦ1).injective
    simp [carlenFullSupportToMatLinearEquiv_apply]
  have hsymm : ∀ W, (carlenFullSupportToMat Φ hΦ1).symm.toContinuousLinearMap W =
      (carlenFullSupportToMat Φ hΦ1).symm W := fun _ => rfl
  have hfwd : ∀ W, (carlenFullSupportToMat Φ hΦ1).toContinuousLinearMap W =
      (carlenFullSupportToMat Φ hΦ1) W := fun _ => rfl
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hsymm, hfwd, hInner]
  rfl

/-! ### Paper-Support Full-Support Specialization and opmontI -/
/-- In the full-support specialization of the paper support condition, condition (2)
is exactly the strict Carlen condition (2). -/
theorem carlenCondition2_support_to_condition2_of_functionHypothesis
    {f : ℝ → ℝ} (hf : CarlenOpMontIFunctionHypothesis f)
    (h2 : CarlenOpMontICondition2_support f) :
    CarlenOpMontICondition2 f := by
  intro n m Φ X Y hΦ hX hY hΦX hΦY
  let hAdjPos := isPositiveMap_hsAdjoint_of_isUnitalTwoPositiveMap hΦ
  have hsupp :=
    h2 (n := n) (m := m) Φ (X := X) (Y := Y) hΦ hX hY
  have hSupportEq : carlenAdjointSupportProj Φ = 1 := by
    have hEq := hsAdjoint_image_supportProj_eq_adjointSupportProj Φ hAdjPos hX
    have hFull := matrixSupportProj_eq_one_of_posDef hΦX
    exact hEq.symm.trans hFull
  have hAdjOneNonneg : 0 ≤ hsAdjoint Φ (1 : Mₙ m) := by
    exact hAdjPos ((Matrix.nonneg_iff_posSemidef).2 Matrix.PosSemidef.one)
  have hAdjOne : MatrixPosDef (hsAdjoint Φ (1 : Mₙ m)) :=
    carlenMatrixPosDef_of_nonneg_supportProj_eq_one hAdjOneNonneg
      (by simpa [carlenAdjointSupportProj] using hSupportEq)
  have hsupp0 :
      HSLE
        ((carlenInputSupportReducedMap Φ hAdjPos).comp
          ((carlenSupportGOperatorInvModelConj f Φ hAdjPos X Y).comp
            (hsAdjoint (carlenInputSupportReducedMap Φ hAdjPos))))
        (gOperatorInv f X Y) := by
    simpa [hAdjPos] using hsupp
  rw [carlenInputSupportReducedMap_eq_fullSupport Φ hAdjPos hAdjOne] at hsupp0
  have hLeft :
      (Φ.comp (carlenFullSupportToMat Φ hAdjOne).symm.toContinuousLinearMap).comp
          ((carlenSupportGOperatorInvModelConj f Φ hAdjPos X Y).comp
            (hsAdjoint
              (Φ.comp (carlenFullSupportToMat Φ hAdjOne).symm.toContinuousLinearMap))) =
        Φ.comp
          ((gOperatorInv f ((hsAdjoint Φ) X) ((hsAdjoint Φ) Y)).comp
            (hsAdjoint Φ)) := by
    rw [carlenSupportGOperatorInvModelConj_eq_fullSupportConj
      Φ hAdjPos hAdjOne f hf hΦX hΦY]
    rw [carlenFullSupport_hsAdjoint_comp_eq Φ hAdjPos hAdjOne]
    exact carlenFullSupport_comp_conj_comp Φ hAdjOne
      (gOperatorInv f (hsAdjoint Φ X) (hsAdjoint Φ Y))
  exact hLeft ▸ hsupp0

/-- Carlen support condition (2) implies condition (4). -/
theorem carlenCondition2_support_to_condition4_of_functionHypothesis
    {f : ℝ → ℝ} (hf : CarlenOpMontIFunctionHypothesis f)
    (h2 : CarlenOpMontICondition2_support f) :
    CarlenOpMontICondition4 f :=
  condition2_to_condition4_of_carlenFunction hf
    (carlenCondition2_support_to_condition2_of_functionHypothesis hf h2)

/-- Paper-support Carlen `opmontI`: the paper-faithful support conditions (2) and
(3), together with the strict conditions (1) and (4), form the same equivalence cycle. -/
theorem carlenOpMontI_support_paper
    {f : ℝ → ℝ}
    (hf : CarlenOpMontIFunctionHypothesis f) :
    (CarlenOpMontICondition1 f ↔ CarlenOpMontICondition2_support f) ∧
      (CarlenOpMontICondition2_support f ↔ CarlenOpMontICondition3_support f) ∧
      (CarlenOpMontICondition3_support f ↔ CarlenOpMontICondition4 f) := by
  have h13 : CarlenOpMontICondition1 f → CarlenOpMontICondition3_support f :=
    carlenCondition1_to_condition3_support_of_functionHypothesis hf
  have h23 : CarlenOpMontICondition2_support f ↔ CarlenOpMontICondition3_support f :=
    carlenCondition2_support_iff_condition3_support_of_functionHypothesis hf
  have h24 : CarlenOpMontICondition2_support f → CarlenOpMontICondition4 f :=
    carlenCondition2_support_to_condition4_of_functionHypothesis hf
  have h41 : CarlenOpMontICondition4 f → CarlenOpMontICondition1 f :=
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
