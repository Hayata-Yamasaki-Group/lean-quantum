/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
import Quantum.TraceInequality.HiaiPetz.MatrixPosDef
import Quantum.TraceInequality.HansenPedersen.MainEquivalence
import Quantum.TraceInequality.HansenPedersen.Model.Basic
import Quantum.TraceInequality.HansenPedersen.Model.MatrixCorner
import Quantum.TraceInequality.HansenPedersen.Reduction.ReducedMap
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Model.MatrixCorner
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Reduction.Basic
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Reduction.Map
import Quantum.TraceInequality.HiaiPetz.Support
import Quantum.TraceInequality.HiaiPetz.Support.Corner
import Quantum.TraceInequality.HiaiPetzTheorem.Reduction.ReducedMap

/-!
# Output-support bridge for the general Hiai–Petz conditions

This module provides the "official bridge" nodes that connect the general
conditions `(i)`, `(ii)`, `(iii)`, `(iv)` of the Hiai–Petz quasi-entropy
data-processing theorem through the output-support reduction of a Hilbert–Schmidt map `Φ`
built from a fixed orthonormal matrix realization of the support corner.

When `Φ (1)` is positive definite the map already has full output support, and the
linear isometry `fullSupportIso` between `Mₙ m` and the corner model
`Mₙ (outputSupportMatrixCornerModel Φ).dim` transports the `J`-operators (`jArg`,
`jOperator`) together with the associated inequalities.  This lets the statements
for the reduced map be identified with those for the original map, so the
completed strict-output theorems apply after reduction.

## Main definitions

* `ReducedMapInverseInequalityAt`, `ReducedMapDirectInequalityAt`: the general
  conditions `(ii)` and `(iii)` phrased via the chosen reduction of `Φ`.

## Main results

* `outputSupportReducedHSMap_strictlyPositive`: the reduced map inherits positivity,
  trace preservation, the Schwarz property, and positive-definite output.
* `reducedMapInverseInequalityAt_iff_directInequalityAt`: general `(ii) ↔ (iii)`.
* `reducedMapDirectInequalityAt_of_operatorMonotone`: general `(i) → (iii)`.
* `jointConcavity_of_reducedMapDirectInequality`: general `(iii) → (iv)`.
-/

namespace HiaiPetz

namespace QuasiEntropyDataProcessing

open scoped MatrixOrder ComplexOrder
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

private noncomputable def oneCornerLinearEquiv (m : ℕ) :
    Mₙ m ≃ₗ[ℂ] matrixCornerSubmodule (1 : Mₙ m) where
  toFun := fun X => ⟨X, by simp [mem_matrixCornerSubmodule_iff]⟩
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
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) :
    Mₙ m ≃ₗ[ℂ] Mₙ (outputSupportMatrixCornerModel Φ).dim := by
  let hCorner : matrixCornerSubmodule (1 : Mₙ m) = matrixCornerSubmodule (outputSupportProj
    Φ) := by
    simp [outputSupportProj_eq_one_of_posDef Φ hΦ1]
  exact (oneCornerLinearEquiv m).trans
    ((LinearEquiv.ofEq _ _ hCorner).trans (outputSupportMatrixCornerModel Φ).toMat)

@[simp] private theorem fullSupportToMatLinearEquiv_apply {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) (X : Mₙ m) :
    fullSupportToMatLinearEquiv Φ hΦ1 X =
      (outputSupportMatrixCornerModel Φ).toMat
        ⟨X, by
          simp [mem_matrixCornerSubmodule_iff, outputSupportProj_eq_one_of_posDef Φ hΦ1]⟩ := by
  rfl

private noncomputable def fullSupportToMatLinearIsometryEquiv {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) :
    Mₙ m ≃ₗᵢ[ℂ] Mₙ (outputSupportMatrixCornerModel Φ).dim :=
  (fullSupportToMatLinearEquiv Φ hΦ1).isometryOfInner (by
    intro X Y
    simpa [fullSupportToMatLinearEquiv_apply] using
      MatrixCornerModel.inner_toMat_eq (outputSupportMatrixCornerModel Φ)
        ⟨X, by
          simp [mem_matrixCornerSubmodule_iff, outputSupportProj_eq_one_of_posDef Φ hΦ1]⟩
        ⟨Y, by
          simp [mem_matrixCornerSubmodule_iff, outputSupportProj_eq_one_of_posDef Φ hΦ1]⟩)

@[simp] private theorem fullSupportToMat_map_mul {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) (X Y : Mₙ m) :
    fullSupportToMatLinearEquiv Φ hΦ1 (X * Y) =
      fullSupportToMatLinearEquiv Φ hΦ1 X * fullSupportToMatLinearEquiv Φ hΦ1 Y := by
  simpa [fullSupportToMatLinearEquiv_apply] using
    (outputSupportMatrixCornerModel Φ).map_mul
      ⟨X, by simp [mem_matrixCornerSubmodule_iff, outputSupportProj_eq_one_of_posDef Φ hΦ1]⟩
      ⟨Y, by simp [mem_matrixCornerSubmodule_iff, outputSupportProj_eq_one_of_posDef Φ hΦ1]⟩

@[simp] private theorem fullSupportToMat_map_star {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) (X : Mₙ m) :
    fullSupportToMatLinearEquiv Φ hΦ1 (star X) =
      star (fullSupportToMatLinearEquiv Φ hΦ1 X) := by
  simpa [fullSupportToMatLinearEquiv_apply] using
    (outputSupportMatrixCornerModel Φ).preservesAdjoint
      ⟨X, by simp [mem_matrixCornerSubmodule_iff, outputSupportProj_eq_one_of_posDef Φ hΦ1]⟩

@[simp] private theorem fullSupportToMat_map_one {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) :
    fullSupportToMatLinearEquiv Φ hΦ1 (1 : Mₙ m) = 1 := by
  simpa [fullSupportToMatLinearEquiv_apply, outputSupportProj_eq_one_of_posDef Φ hΦ1] using
    (outputSupportMatrixCornerModel Φ).map_proj

private noncomputable abbrev fullSupportToMat {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) :
    Mₙ m ≃ₗ[ℂ] Mₙ (outputSupportMatrixCornerModel Φ).dim :=
  fullSupportToMatLinearEquiv Φ hΦ1

private noncomputable abbrev fullSupportIso {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) :
    Mₙ m ≃ₗᵢ[ℂ] Mₙ (outputSupportMatrixCornerModel Φ).dim :=
  fullSupportToMatLinearIsometryEquiv Φ hΦ1

private theorem fullSupportToMat_symm_apply {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n)))
    (Y : Mₙ (outputSupportMatrixCornerModel Φ).dim) :
    (outputSupportMatrixCornerModel Φ).toMat.symm Y =
      ⟨(fullSupportToMatLinearEquiv Φ hΦ1).symm Y, by
        simp [mem_matrixCornerSubmodule_iff, outputSupportProj_eq_one_of_posDef Φ hΦ1]⟩ := by
  apply (outputSupportMatrixCornerModel Φ).toMat.injective
  calc
    (outputSupportMatrixCornerModel Φ).toMat
        ((outputSupportMatrixCornerModel Φ).toMat.symm Y) = Y := by
          simp
    _ = (outputSupportMatrixCornerModel Φ).toMat
          ⟨(fullSupportToMatLinearEquiv Φ hΦ1).symm Y, by
            simp [mem_matrixCornerSubmodule_iff, outputSupportProj_eq_one_of_posDef Φ hΦ1]⟩
              := by
          exact (LinearEquiv.apply_symm_apply (fullSupportToMat Φ hΦ1) Y).symm

private theorem fullSupportToMat_symm_apply_val {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n)))
    (Y : Mₙ (outputSupportMatrixCornerModel Φ).dim) :
    ((outputSupportMatrixCornerModel Φ).toMat.symm Y).1 =
      (fullSupportToMatLinearEquiv Φ hΦ1).symm Y := by
  simpa using congrArg Subtype.val (fullSupportToMat_symm_apply Φ hΦ1 Y)

private theorem fullSupportToMat_map_posInv {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) {B : Mₙ m} (hB : Matrix.PosDef B) :
    fullSupportToMatLinearEquiv Φ hΦ1 (B⁻¹) =
      ((fullSupportToMatLinearEquiv Φ hΦ1 B)⁻¹) := by
  rcases Matrix.PosDef.isUnit hB with ⟨u, rfl⟩
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

private theorem spectrum_jArg_subset_Ioi_local {n : ℕ} {A B : Mₙ n}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    spectrum ℝ (jArg A B) ⊆ Set.Ioi (0 : ℝ) :=
  HiaiPetz.spectrum_jArg_subset_Ioi_of_posDef hA hB

private noncomputable def conjHSOp {m k : ℕ} (e : Mₙ m ≃ₗᵢ[ℂ] Mₙ k) (T : HSOp m)
  : HSOp k :=
  e.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap)

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

/-- Conjugation by a Hilbert-space linear isometry equivalence preserves and
reflects Mathlib positivity of continuous linear endomorphisms. -/
private theorem conjHSOp_isPositive_iff {m k : ℕ}
    (e : Mₙ m ≃ₗᵢ[ℂ] Mₙ k) (T : HSOp m) :
    (conjHSOp e T).IsPositive ↔ T.IsPositive := by
  constructor
  · intro hT
    have hback := hT.conj_adjoint e.symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hadj :
        ContinuousLinearMap.adjoint
            e.symm.toContinuousLinearEquiv.toContinuousLinearMap =
          e.toContinuousLinearEquiv.toContinuousLinearMap := by
      simpa using e.symm.adjoint_eq_symm
    rw [hadj] at hback
    simp only [LinearIsometryEquiv.toContinuousLinearEquiv_symm, conjHSOp,
      ContinuousLinearMap.comp_assoc, ContinuousLinearEquiv.coe_symm_comp_coe,
      ContinuousLinearMap.comp_id] at hback
    rw [← ContinuousLinearMap.comp_assoc] at hback
    simpa using hback
  · intro hT
    have hforward := hT.conj_adjoint e.toContinuousLinearEquiv.toContinuousLinearMap
    have hadj :
        ContinuousLinearMap.adjoint
            e.toContinuousLinearEquiv.toContinuousLinearMap =
          e.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
      simp
    rw [hadj] at hforward
    simpa [conjHSOp, ContinuousLinearMap.comp_assoc] using hforward

private noncomputable def fullSupportConjLeftMulTarget {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) (A : Mₙ m) :
    HSOp (outputSupportMatrixCornerModel Φ).dim :=
  conjHSOp (fullSupportIso Φ hΦ1) (leftMul A)

private theorem fullSupportToMat_conj_leftMul {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) (A : Mₙ m) :
    fullSupportConjLeftMulTarget Φ hΦ1 A =
      leftMul (fullSupportToMat Φ hΦ1 A) := by
  ext X i j
  simpa [fullSupportConjLeftMulTarget, conjHSOp] using
    congrArg (fun M : Mₙ (outputSupportMatrixCornerModel Φ).dim => M i j)
      (fullSupportToMat_map_mul Φ hΦ1 A
        ((fullSupportToMat Φ hΦ1).symm X))

private noncomputable def fullSupportConjRightMulTarget {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) (B : Mₙ m) :
    HSOp (outputSupportMatrixCornerModel Φ).dim :=
  conjHSOp (fullSupportIso Φ hΦ1) (rightMul B)

private theorem fullSupportToMat_conj_rightMul {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) (B : Mₙ m) :
    fullSupportConjRightMulTarget Φ hΦ1 B =
      rightMul (fullSupportToMat Φ hΦ1 B) := by
  ext X i j
  simpa [fullSupportConjRightMulTarget, conjHSOp] using
    congrArg (fun M : Mₙ (outputSupportMatrixCornerModel Φ).dim => M i j)
      (fullSupportToMat_map_mul Φ hΦ1
        ((fullSupportToMat Φ hΦ1).symm X) B)

private noncomputable def fullSupportConjJArgTarget {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) (A B : Mₙ m) :
    HSOp (outputSupportMatrixCornerModel Φ).dim :=
  conjHSOp (fullSupportIso Φ hΦ1) (jArg A B)

private theorem fullSupportToMat_conj_jArg {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) {A B : Mₙ m}
    (hB : Matrix.PosDef B) :
    fullSupportConjJArgTarget Φ hΦ1 A B =
      jArg (fullSupportToMat Φ hΦ1 A)
        (fullSupportToMat Φ hΦ1 B) := by
  rw [fullSupportConjJArgTarget]
  change conjHSOp (fullSupportIso Φ hΦ1)
      ((rightMul (B⁻¹)) * leftMul A) =
    (rightMul (((fullSupportToMat Φ hΦ1 B)⁻¹))) *
      leftMul (fullSupportToMat Φ hΦ1 A)
  rw [conjHSOp_mul]
  change fullSupportConjRightMulTarget Φ hΦ1 (B⁻¹) *
      fullSupportConjLeftMulTarget Φ hΦ1 A =
    (rightMul (((fullSupportToMat Φ hΦ1 B)⁻¹))) *
      leftMul (fullSupportToMat Φ hΦ1 A)
  rw [fullSupportToMat_conj_rightMul, fullSupportToMat_conj_leftMul,
    fullSupportToMat_map_posInv Φ hΦ1 hB]

private noncomputable def fullSupportConjJOperatorTarget {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) (f : ℝ → ℝ) (A B : Mₙ m) :
    HSOp (outputSupportMatrixCornerModel Φ).dim :=
  conjHSOp (fullSupportIso Φ hΦ1) (jOperator f A B)

private theorem fullSupportToMat_conj_jOperator {n m : ℕ} (Φ : HSMap n m)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) {A B : Mₙ m}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    fullSupportConjJOperatorTarget Φ hΦ1 f A B =
      jOperator f (fullSupportToMat Φ hΦ1 A)
        (fullSupportToMat Φ hΦ1 B) := by
  /- Step 1: Install the C*-algebra and CFC instances on the source and corner HS algebras. -/
  letI : NormedAddCommGroup (Mₙ m) := inferInstance
  letI : NormedSpace ℂ (Mₙ m) := inferInstance
  letI : InnerProductSpace ℂ (Mₙ m) := inferInstance
  letI : CompleteSpace (Mₙ m) := inferInstance
  letI : FiniteDimensional ℂ (Mₙ m) := inferInstance
  letI : SMul ℝ (HSOp m) := NormedAlgebra.complexToReal.toSMul
  letI : Algebra ℝ (HSOp m) := NormedAlgebra.complexToReal.toAlgebra
  letI : Ring (HSOp m) := by infer_instance
  letI : Semiring (HSOp m) := by infer_instance
  letI : SeminormedRing (HSOp m) := by infer_instance
  letI : NormedRing (HSOp m) := by infer_instance
  letI : Star (HSOp m) := by infer_instance
  letI : StarRing (HSOp m) := by infer_instance
  letI : Algebra ℂ (HSOp m) := by infer_instance
  letI : NormedAlgebra ℂ (HSOp m) := by infer_instance
  letI : CStarAlgebra (HSOp m) := by infer_instance
  letI : IsScalarTower ℝ ℂ (HSOp m) := by infer_instance
  letI : ContinuousFunctionalCalculus ℝ (HSOp m) IsSelfAdjoint := by infer_instance
  letI : ContinuousFunctionalCalculus ℂ (HSOp m) IsStarNormal := by infer_instance
  let k := (outputSupportMatrixCornerModel Φ).dim
  letI : NormedAddCommGroup (Mₙ k) := inferInstance
  letI : NormedSpace ℂ (Mₙ k) := inferInstance
  letI : InnerProductSpace ℂ (Mₙ k) := inferInstance
  letI : CompleteSpace (Mₙ k) := inferInstance
  letI : FiniteDimensional ℂ (Mₙ k) := inferInstance
  letI : NormedAddCommGroup (Mₙ (outputSupportMatrixCornerModel Φ).dim) :=
    inferInstance
  letI : NormedSpace ℂ (Mₙ (outputSupportMatrixCornerModel Φ).dim) :=
    inferInstance
  letI : InnerProductSpace ℂ (Mₙ (outputSupportMatrixCornerModel Φ).dim) :=
    inferInstance
  letI : CompleteSpace (Mₙ (outputSupportMatrixCornerModel Φ).dim) :=
    inferInstance
  letI : FiniteDimensional ℂ (Mₙ (outputSupportMatrixCornerModel Φ).dim) :=
    inferInstance
  letI : SMul ℝ (HSOp k) := NormedAlgebra.complexToReal.toSMul
  letI : Algebra ℝ (HSOp k) := NormedAlgebra.complexToReal.toAlgebra
  letI : Ring (HSOp k) := by infer_instance
  letI : Semiring (HSOp k) := by infer_instance
  letI : SeminormedRing (HSOp k) := by infer_instance
  letI : NormedRing (HSOp k) := by infer_instance
  letI : Star (HSOp k) := by infer_instance
  letI : StarRing (HSOp k) := by infer_instance
  letI : Algebra ℂ (HSOp k) := by infer_instance
  letI : NormedAlgebra ℂ (HSOp k) := by infer_instance
  letI : CStarAlgebra (HSOp k) := by infer_instance
  letI : IsScalarTower ℝ ℂ (HSOp k) := by infer_instance
  letI : ContinuousFunctionalCalculus ℝ (HSOp k) IsSelfAdjoint := by infer_instance
  letI : ContinuousFunctionalCalculus ℂ (HSOp k) IsStarNormal := by infer_instance
  /- Step 2: Build the star-algebra isomorphism Φop from the source-to-corner isometry. -/
  let eIso : Mₙ m ≃ₗᵢ[ℂ] Mₙ k := fullSupportIso Φ hΦ1
  let Φ₀ : HSOp m ≃⋆ₐ[ℂ] HSOp k :=
    @LinearIsometryEquiv.conjStarAlgEquiv ℂ
      (inferInstance : RCLike ℂ)
      (Mₙ m)
      (inferInstance : NormedAddCommGroup (Mₙ m))
      (inferInstance : InnerProductSpace ℂ (Mₙ m))
      (inferInstance : CompleteSpace (Mₙ m))
      (Mₙ k)
      (inferInstance : NormedAddCommGroup (Mₙ k))
      (inferInstance : InnerProductSpace ℂ (Mₙ k))
      (inferInstance : CompleteSpace (Mₙ k))
      eIso
  let Φop : HSOp m →⋆ₐ[ℂ] HSOp k :=
    { Φ₀.toAlgEquiv.toAlgHom with
      map_star' := by
        intro T
        simpa [Φ₀] using Φ₀.map_star' T }
  /- Step 3: Check the CFC hypotheses and transport the functional calculus through Φop. -/
  have hsrc : IsSelfAdjoint (jArg A B) := by
    simpa using jArg_isSelfAdjoint hA.1 hB
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
  have hmap := StarAlgHomClass.map_cfc Φop f (jArg A B)
    (hf := hcont)
    (hφ := hφ)
    (ha := hsrc) (hφa := hφa)
  /- Step 4: Transport the right-multiplication factor rightMul B to the corner. -/
  have hright :
      Φ₀ (rightMul B) = rightMul (fullSupportToMat Φ hΦ1 B) := by
    simpa [Φ₀, fullSupportConjRightMulTarget, conjHSOp,
      LinearIsometryEquiv.conjStarAlgEquiv_apply] using
      fullSupportToMat_conj_rightMul Φ hΦ1 B
  /- Step 5: Assemble the jOperator identity on the corner via the calc chain. -/
  calc
    Φ₀ (jOperator f A B)
        = Φop (hsCfcR f (jArg A B)) *
            rightMul (fullSupportToMat Φ hΦ1 B) := by
              rw [jOperator]
              calc
                Φ₀ (hsCfcR f (jArg A B) * rightMul B)
                    = Φ₀ (hsCfcR f (jArg A B)) * Φ₀ (rightMul B) := by
                        simp
                _ = Φop (hsCfcR f (jArg A B)) *
                      rightMul (fullSupportToMat Φ hΦ1 B) := by
                        rw [hright]
                        rfl
    _ = hsCfcR f (Φop (jArg A B)) * rightMul (fullSupportToMat Φ hΦ1 B) := by
            rw [hmap]
    _ = jOperator f (fullSupportToMat Φ hΦ1 A)
          (fullSupportToMat Φ hΦ1 B) := by
            rw [show Φop (jArg A B) =
                jArg (fullSupportToMat Φ hΦ1 A) (fullSupportToMat Φ hΦ1 B) by
                  simpa [Φop, Φ₀] using fullSupportToMat_conj_jArg Φ hΦ1 hB]
            simp [jOperator]

private theorem outputSupportReducedMap_eq_fullSupportToMat {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) :
    outputSupportReducedMap Φ hPos =
      (fullSupportIso Φ hΦ1).toContinuousLinearMap.comp Φ := by
  ext X
  rw [outputSupportReducedMap_eq_of_posDef (hΦ1 := hΦ1)]
  rfl

private theorem outputSupportReducedMap_hsAdjoint_eq_fullSupportToMat {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) :
    hsAdjoint (outputSupportReducedMap Φ hPos) =
      (hsAdjoint Φ).comp (fullSupportIso Φ hΦ1).symm.toContinuousLinearMap := by
  ext Y
  rw [outputSupportReducedMap_hsAdjoint_apply]
  rw [fullSupportToMat_symm_apply_val (Φ := Φ) (hΦ1 := hΦ1)]
  rfl

private noncomputable def outputSupportReducedMapDirectConjTarget {n m : ℕ}
    (Φ : HSMap n m) (_hPos : IsPositiveMap Φ) (f : ℝ → ℝ) (A B : Mₙ n)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) :
    HSOp (outputSupportMatrixCornerModel Φ).dim :=
  conjHSOp (fullSupportIso Φ hΦ1)
    (Φ.comp ((jOperator f A B).comp (hsAdjoint Φ)))

private theorem outputSupportReducedMap_direct_conj {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (f : ℝ → ℝ) {A B : Mₙ n}
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) :
    (outputSupportReducedMap Φ hPos).comp
        ((jOperator f A B).comp (hsAdjoint (outputSupportReducedMap Φ hPos))) =
      outputSupportReducedMapDirectConjTarget Φ hPos f A B hΦ1 := by
  ext Y i j
  rw [outputSupportReducedMap_hsAdjoint_eq_fullSupportToMat (Φ := Φ) (hPos := hPos) (hΦ1 :=
    hΦ1)]
  rw [outputSupportReducedMap_eq_fullSupportToMat (Φ := Φ) (hPos := hPos) (hΦ1 := hΦ1)]
  rfl

private noncomputable def outputSupportReducedMapJOperatorConjTarget {n m : ℕ}
    (Φ : HSMap n m) (_hPos : IsPositiveMap Φ) (f : ℝ → ℝ) (A B : Mₙ n)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) :
    HSOp (outputSupportMatrixCornerModel Φ).dim :=
  conjHSOp (fullSupportIso Φ hΦ1) (jOperator f (Φ A) (Φ B))

private theorem outputSupportReducedMap_jOperator_conj {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) {A B : Mₙ n}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) :
    jOperator f (outputSupportReducedMap Φ hPos A) (outputSupportReducedMap Φ hPos B) =
      outputSupportReducedMapJOperatorConjTarget Φ hPos f A B hΦ1 := by
  letI : NormedAddCommGroup (Mₙ m) := instMatrixNormedAddCommGroup (n := m)
  letI : NormedSpace ℂ (Mₙ m) := instMatrixNormedSpace (n := m)
  letI : InnerProductSpace ℂ (Mₙ m) := instMatrixInnerProductSpace (n := m)
  letI : CompleteSpace (Mₙ m) := instMatrixCompleteSpace (n := m)
  letI : FiniteDimensional ℂ (Mₙ m) := Matrix.finiteDimensional
  letI : NormedAddCommGroup (Mₙ (outputSupportMatrixCornerModel Φ).dim) :=
    instMatrixNormedAddCommGroup (n := (outputSupportMatrixCornerModel Φ).dim)
  letI : NormedSpace ℂ (Mₙ (outputSupportMatrixCornerModel Φ).dim) :=
    instMatrixNormedSpace (n := (outputSupportMatrixCornerModel Φ).dim)
  letI : InnerProductSpace ℂ (Mₙ (outputSupportMatrixCornerModel Φ).dim) :=
    instMatrixInnerProductSpace (n := (outputSupportMatrixCornerModel Φ).dim)
  letI : CompleteSpace (Mₙ (outputSupportMatrixCornerModel Φ).dim) :=
    instMatrixCompleteSpace (n := (outputSupportMatrixCornerModel Φ).dim)
  letI : FiniteDimensional ℂ (Mₙ (outputSupportMatrixCornerModel Φ).dim) :=
    Matrix.finiteDimensional
  have hΦA : Matrix.PosDef (Φ A) :=
    Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hΦB : Matrix.PosDef (Φ B) :=
    Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  rw [outputSupportReducedMap_eq_of_posDef (hΦ1 := hΦ1),
    outputSupportReducedMap_eq_of_posDef (hΦ1 := hΦ1)]
  simpa [outputSupportReducedMapJOperatorConjTarget, fullSupportIso, fullSupportToMat,
      fullSupportToMatLinearEquiv_apply] using
    (fullSupportToMat_conj_jOperator Φ hΦ1 f hf (A := Φ A) (B := Φ B) hΦA hΦB).symm

/-- Fixed-map proof-facing general `(ii)` phrased via an output-support reduction of `Φ` built
from a fixed orthonormal matrix realization of the support corner.
Source: Hiai, Theorem 6.2, condition (ii) = (6.3). -/
def ReducedMapInverseInequalityAt (f : ℝ → ℝ) {n m : ℕ} (Φ : HSMap n m) : Prop :=
  ∀ {A B : Mₙ n},
    (hPos : IsPositiveMap Φ) →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    let Ψ := outputSupportReducedHSMap Φ hPos
    (show HSOp n from
      (hsAdjoint Ψ).comp ((jOperatorInv f (Ψ A) (Ψ B)).comp Ψ)) ≤
      (jOperatorInv f A B)

/-- Fixed-map proof-facing general `(iii)` phrased via an output-support reduction of `Φ` built
from a fixed orthonormal matrix realization of the support corner.
Source: Hiai, Theorem 6.2, condition (iii) = (6.4). -/
def ReducedMapDirectInequalityAt (f : ℝ → ℝ) {n m : ℕ} (Φ : HSMap n m) : Prop :=
  ∀ {A B : Mₙ n},
    (hPos : IsPositiveMap Φ) →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    let Ψ := outputSupportReducedHSMap Φ hPos
    (show HSOp (outputSupportMatrixCornerModel Φ).dim from
      Ψ.comp ((jOperator f A B).comp (hsAdjoint Ψ))) ≤
      (jOperator f (Ψ A) (Ψ B))

/-- Official bridge node: general `(ii)` and `(iii)` are equivalent because the chosen
output-support reduction satisfies the strict-output hypotheses and the completed strict theorem
applies to the reduced map. -/
theorem reducedMapInverseInequalityAt_iff_directInequalityAt (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hposf : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    {n m : ℕ} (Φ : HSMap n m) :
    ReducedMapInverseInequalityAt f Φ ↔ ReducedMapDirectInequalityAt f Φ := by
  constructor
  · intro hII A B hPos hTrace hSch hA hB
    have hReady := outputSupportReducedHSMap_strictlyPositive Φ hPos hTrace hSch
    exact StrictlyPositive.inverse_implies_direct (f := f) (hf := hf) (hpos := hposf)
      (outputSupportReducedHSMap Φ hPos) (A := A) (B := B)
      hReady.positiveMap hA hB hReady.outputPosDef
      (hII hPos hTrace hSch hA hB)
  · intro hIII A B hPos hTrace hSch hA hB
    have hReady := outputSupportReducedHSMap_strictlyPositive Φ hPos hTrace hSch
    exact StrictlyPositive.direct_implies_inverse (f := f) (hf := hf) (hpos := hposf)
      (outputSupportReducedHSMap Φ hPos) (A := A) (B := B)
      hReady.positiveMap hA hB hReady.outputPosDef
      (hIII hPos hTrace hSch hA hB)

/-- Official bridge node: general `(i)` implies general `(iii)` because the chosen output-support
reduction satisfies the strict-output hypotheses and the completed strict `(i) → (iii)` theorem
applies to the reduced map. -/
theorem reducedMapDirectInequalityAt_of_operatorMonotone (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hposf : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hI : AllHOperatorMonotoneOnIoi f) {n m : ℕ} (Φ : HSMap n m)
    :
    ReducedMapDirectInequalityAt f Φ := by
  intro A B hPos hTrace hSch hA hB
  have hReady := outputSupportReducedHSMap_strictlyPositive Φ hPos hTrace hSch
  exact (strictlyPositiveDirectInequality_of_operatorMonotone f hf hposf hI)
    (outputSupportReducedMap Φ hPos) (A := A) (B := B) hReady.positiveMap
      hReady.tracePreserving hReady.adjointSchwarz hA hB hReady.outputPosDef

private noncomputable abbrev fullSupportSourceOp {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (A B : Mₙ n) : HSOp m :=
  Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))

private noncomputable abbrev fullSupportTargetOp {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (A B : Mₙ n) : HSOp m :=
  jOperator f (Φ A) (Φ B)

private abbrev FullSupportDirectInequality {n m : ℕ} (f : ℝ → ℝ)
    (Φ : HSMap n m) (A B : Mₙ n) : Prop :=
  fullSupportSourceOp f Φ A B ≤ fullSupportTargetOp f Φ A B

private theorem fullSupportDirectInequality_of_reducedMap (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) {n m : ℕ} (Φ : HSMap n m)
    (hIII : ReducedMapDirectInequalityAt f Φ)
    {A B : Mₙ n} (hPos : IsPositiveMap Φ) (hTrace : TracePreserving Φ)
    (hSch : HSAdjointSchwarz Φ) (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) :
    FullSupportDirectInequality f Φ A B := by
  /- Step 1: Set up the full-support isometry e and the positivity of the images Φ A, Φ B. -/
  let e := fullSupportIso Φ hΦ1
  have hΦA : Matrix.PosDef (Φ A) :=
    Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hΦB : Matrix.PosDef (Φ B) :=
    Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  /- Step 2: Invoke hypothesis (iii): the reduced-map direct inequality on the compressed maps. -/
  have hred :
      (show HSOp (outputSupportMatrixCornerModel Φ).dim from
        (outputSupportReducedMap Φ hPos).comp
          ((jOperator f A B).comp (hsAdjoint (outputSupportReducedMap Φ hPos))))
        ≤ (jOperator f (outputSupportReducedMap Φ hPos A)
          (outputSupportReducedMap Φ hPos B)) := by
    simpa [ReducedMapDirectInequalityAt] using hIII (A := A) (B := B) hPos hTrace hSch hA hB
  /- Step 3: Conjugate the inequality by the isometry e into the full-support picture. -/
  have hconj :
      conjHSOp e (fullSupportSourceOp f Φ A B) ≤
        (conjHSOp e (fullSupportTargetOp f Φ A B)) := by
    have hred₁ :
        outputSupportReducedMapDirectConjTarget Φ hPos f A B hΦ1 ≤
          (jOperator f (outputSupportReducedMap Φ hPos A)
            (outputSupportReducedMap Φ hPos B)) := by
      exact
        (outputSupportReducedMap_direct_conj
          (Φ := Φ) (hPos := hPos) (f := f) (A := A) (B := B) (hΦ1 := hΦ1)).symm ▸ hred
    have hred' :
        outputSupportReducedMapDirectConjTarget Φ hPos f A B hΦ1 ≤
          (outputSupportReducedMapJOperatorConjTarget Φ hPos f A B hΦ1) := by
      exact
        (outputSupportReducedMap_jOperator_conj
          (Φ := Φ) (hPos := hPos) (f := f) (hf := hf)
          (A := A) (B := B) (hA := hA) (hB := hB) (hΦ1 := hΦ1)) ▸ hred₁
    simpa [fullSupportSourceOp, fullSupportTargetOp,
      outputSupportReducedMapDirectConjTarget, outputSupportReducedMapJOperatorConjTarget, e] using
      hred'
  /- Step 4: Reflect standard positivity of the conjugated difference through the isometry. -/
  unfold FullSupportDirectInequality
  rw [ContinuousLinearMap.le_def] at hconj ⊢
  have hconjMapped :
      (conjHSOp e
        (fullSupportTargetOp f Φ A B - fullSupportSourceOp f Φ A B)).IsPositive := by
    rw [conjHSOp_map_sub]
    exact hconj
  exact (conjHSOp_isPositive_iff e
    (fullSupportTargetOp f Φ A B - fullSupportSourceOp f Φ A B)).mp hconjMapped

/-- Official bridge node: general `(iii)` implies book-facing `(iv)` by applying the completed
strict-output `(iii) → (iv)` theorem to the chosen reduced map and then trivializing the
full-support case back to the original map. -/
theorem jointConcavity_of_reducedMapDirectInequality (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hIII : ∀ {n m : ℕ} (Φ : HSMap n m), ReducedMapDirectInequalityAt f Φ) :
    JointConcavity f := by
  apply jointConcavity_of_strictDirectDPI f hf
  intro n m Φ A B hPos hTrace hSch hA hB hΦ1
  exact fullSupportDirectInequality_of_reducedMap (f := f) (hf := hf) Φ (hIII Φ)
    hPos hTrace hSch hA hB hΦ1

end MatrixScopedInstances

end QuasiEntropyDataProcessing

end HiaiPetz
