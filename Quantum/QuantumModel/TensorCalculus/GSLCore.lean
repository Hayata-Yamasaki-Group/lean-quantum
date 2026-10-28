/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.Calculus.GSLCore
import Mathlib.Analysis.Matrix.Order

/-!
# Tensor-product Kraus calculus

The categorical tensor in `CategoryInstances` is transported through operator
Kronecker coordinates.  This file identifies it with the product Kraus family.
-/

noncomputable section

namespace QuantumModel

open CategoryTheory
open CategoryTheory.MonoidalCategory
open QuantumState
open TensorProduct
open scoped ComplexOrder Kronecker Matrix MatrixOrder

variable {A B C D : Sys}

abbrev spaceONB (A : Sys) :=
  EuclideanSpace.basisFun (Fin A.dim) ℂ

abbrev spaceBasis (A : Sys) := (spaceONB A).toBasis

theorem operatorTensorEquiv_matrix_tmul (X : Operator A) (Y : Operator C) :
    operatorEquivMatrix (tensorSystem A C)
        (operatorTensorEquiv A C (X ⊗ₜ[ℂ] Y)) =
      Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv
        (operatorEquivMatrix A X ⊗ₖ operatorEquivMatrix C Y) := by
  change (operatorEquivMatrix (tensorSystem A C))
      ((operatorEquivMatrix (tensorSystem A C)).symm
        (Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv
          (operatorEquivMatrix A X ⊗ₖ operatorEquivMatrix C Y))) = _
  simp

theorem operatorTensorEquiv_tmul_nonneg
    {X : Operator A} {Y : Operator C} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ operatorTensorEquiv A C (X ⊗ₜ[ℂ] Y) := by
  apply (QuantumChannel.starAlgEquiv_nonneg_iff
    (operatorEquivMatrix (tensorSystem A C))).mp
  rw [operatorTensorEquiv_matrix_tmul]
  apply Matrix.nonneg_iff_posSemidef.mpr
  have hMX : (operatorEquivMatrix A X).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      ((QuantumChannel.starAlgEquiv_nonneg_iff
        (operatorEquivMatrix A)).mpr hX)
  have hMY : (operatorEquivMatrix C Y).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      ((QuantumChannel.starAlgEquiv_nonneg_iff
        (operatorEquivMatrix C)).mpr hY)
  exact (hMX.kronecker hMY).submatrix _

theorem operatorTensorEquiv_one_tmul_one :
    operatorTensorEquiv A C ((1 : Operator A) ⊗ₜ[ℂ] (1 : Operator C)) = 1 := by
  apply (operatorEquivMatrix (tensorSystem A C)).injective
  change operatorEquivMatrix (tensorSystem A C)
      (operatorTensorEquiv A C ((1 : Operator A) ⊗ₜ[ℂ] (1 : Operator C))) =
    operatorEquivMatrix (tensorSystem A C) 1
  rw [operatorTensorEquiv_matrix_tmul]
  simp only [map_one, Matrix.one_kronecker_one,
    Matrix.reindexLinearEquiv_one]
  rfl

theorem operatorTensorEquiv_tmul_le_one
    {X : Operator A} {Y : Operator C}
    (hX0 : 0 ≤ X) (hX1 : X ≤ 1) (hY1 : Y ≤ 1) :
    operatorTensorEquiv A C (X ⊗ₜ[ℂ] Y) ≤ 1 := by
  rw [← operatorTensorEquiv_one_tmul_one (A := A) (C := C)]
  rw [← sub_nonneg]
  have honeA : (0 : Operator A) ≤ 1 :=
    (LinearMap.nonneg_iff_isPositive _).mpr LinearMap.isPositive_one
  have honeC : (0 : Operator C) ≤ 1 :=
    (LinearMap.nonneg_iff_isPositive _).mpr LinearMap.isPositive_one
  have hdecomp :
      operatorTensorEquiv A C ((1 : Operator A) ⊗ₜ[ℂ] (1 : Operator C)) -
          operatorTensorEquiv A C (X ⊗ₜ[ℂ] Y) =
          operatorTensorEquiv A C ((1 - X) ⊗ₜ[ℂ] (1 : Operator C)) +
          operatorTensorEquiv A C (X ⊗ₜ[ℂ] (1 - Y)) := by
    rw [← map_sub, ← map_add]
    apply congrArg
      (fun Z : Operator A ⊗[ℂ] Operator C => operatorTensorEquiv A C Z)
    rw [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    abel
  rw [hdecomp]
  exact add_nonneg
    (operatorTensorEquiv_tmul_nonneg (sub_nonneg.mpr hX1) honeC)
    (operatorTensorEquiv_tmul_nonneg hX0 (sub_nonneg.mpr hY1))

theorem operatorEquivMatrix_krausTerm
    (V : Space A →ₗ[ℂ] Space B) (X : Operator A) :
    operatorEquivMatrix B (QuantumChannel.krausTerm V X) =
      LinearMap.toMatrix (spaceBasis A) (spaceBasis B) V *
        operatorEquivMatrix A X *
          (LinearMap.toMatrix (spaceBasis A) (spaceBasis B) V)ᴴ := by
  change LinearMap.toMatrix (spaceBasis B) (spaceBasis B)
    (V.comp (X.comp (LinearMap.adjoint V))) = _
  rw [← LinearMap.comp_assoc]
  rw [LinearMap.toMatrix_comp (spaceBasis B) (spaceBasis A) (spaceBasis B),
    LinearMap.toMatrix_comp (spaceBasis A) (spaceBasis A) (spaceBasis B),
    LinearMap.toMatrix_adjoint (spaceONB A) (spaceONB B)]
  rfl

/-- Kronecker product of two Hilbert-space linear maps, in the same coordinates
used by `operatorTensorEquiv`. -/
def tensorOperator (V : Space A →ₗ[ℂ] Space B)
    (W : Space C →ₗ[ℂ] Space D) :
    Space (tensorSystem A C) →ₗ[ℂ] Space (tensorSystem B D) :=
  Matrix.toLin (spaceBasis (tensorSystem A C)) (spaceBasis (tensorSystem B D))
    (Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv
      (LinearMap.toMatrix (spaceBasis A) (spaceBasis B) V ⊗ₖ
        LinearMap.toMatrix (spaceBasis C) (spaceBasis D) W))

@[simp]
theorem tensorOperator_matrix (V : Space A →ₗ[ℂ] Space B)
    (W : Space C →ₗ[ℂ] Space D) :
    LinearMap.toMatrix (spaceBasis (tensorSystem A C))
        (spaceBasis (tensorSystem B D)) (tensorOperator V W) =
      Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv
        (LinearMap.toMatrix (spaceBasis A) (spaceBasis B) V ⊗ₖ
          LinearMap.toMatrix (spaceBasis C) (spaceBasis D) W) := by
  simp [tensorOperator]

theorem krausTerm_tensorOperator_tmul
    (V : Space A →ₗ[ℂ] Space B) (W : Space C →ₗ[ℂ] Space D)
    (X : Operator A) (Y : Operator C) :
    QuantumChannel.krausTerm (tensorOperator V W)
        (operatorTensorEquiv A C (X ⊗ₜ[ℂ] Y)) =
      operatorTensorEquiv B D
        (QuantumChannel.krausTerm V X ⊗ₜ[ℂ]
          QuantumChannel.krausTerm W Y) := by
  apply (operatorEquivMatrix (tensorSystem B D)).injective
  simp only [QuantumChannel.krausTerm]
  change operatorEquivMatrix (tensorSystem B D)
      ((tensorOperator V W).comp
        ((operatorTensorEquiv A C (X ⊗ₜ[ℂ] Y)).comp
          (LinearMap.adjoint (tensorOperator V W)))) = _
  rw [← LinearMap.comp_assoc]
  change LinearMap.toMatrix (spaceBasis (tensorSystem B D))
      (spaceBasis (tensorSystem B D))
      (((tensorOperator V W).comp
        (operatorTensorEquiv A C (X ⊗ₜ[ℂ] Y))).comp
          (LinearMap.adjoint (tensorOperator V W))) = _
  rw [LinearMap.toMatrix_comp
      (spaceBasis (tensorSystem B D)) (spaceBasis (tensorSystem A C))
      (spaceBasis (tensorSystem B D)),
    LinearMap.toMatrix_comp
      (spaceBasis (tensorSystem A C)) (spaceBasis (tensorSystem A C))
      (spaceBasis (tensorSystem B D))]
  have hAC := operatorTensorEquiv_matrix_tmul (A := A) (C := C) X Y
  change LinearMap.toMatrix (spaceBasis (tensorSystem A C))
      (spaceBasis (tensorSystem A C))
      (operatorTensorEquiv A C (X ⊗ₜ[ℂ] Y)) = _ at hAC
  rw [hAC]
  change _ = LinearMap.toMatrix (spaceBasis (tensorSystem B D))
    (spaceBasis (tensorSystem B D))
    (operatorTensorEquiv B D
      (QuantumChannel.krausTerm V X ⊗ₜ[ℂ]
        QuantumChannel.krausTerm W Y))
  have hBD := operatorTensorEquiv_matrix_tmul (A := B) (C := D)
    (QuantumChannel.krausTerm V X) (QuantumChannel.krausTerm W Y)
  change LinearMap.toMatrix (spaceBasis (tensorSystem B D))
      (spaceBasis (tensorSystem B D))
      (operatorTensorEquiv B D
        (QuantumChannel.krausTerm V X ⊗ₜ[ℂ]
          QuantumChannel.krausTerm W Y)) = _ at hBD
  rw [hBD]
  rw [tensorOperator_matrix]
  rw [LinearMap.toMatrix_adjoint (spaceONB (tensorSystem A C))
    (spaceONB (tensorSystem B D))]
  rw [tensorOperator_matrix]
  conv_lhs =>
    rhs
    change (Matrix.reindex finProdFinEquiv finProdFinEquiv
      (LinearMap.toMatrix (spaceBasis A) (spaceBasis B) V ⊗ₖ
        LinearMap.toMatrix (spaceBasis C) (spaceBasis D) W))ᴴ
    change Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv
      ((LinearMap.toMatrix (spaceBasis A) (spaceBasis B) V ⊗ₖ
        LinearMap.toMatrix (spaceBasis C) (spaceBasis D) W)ᴴ)
  rw [Matrix.conjTranspose_kronecker]
  have hVmatrix :
      operatorEquivMatrix B (QuantumChannel.krausTerm V X) =
        LinearMap.toMatrix (spaceBasis A) (spaceBasis B) V *
          operatorEquivMatrix A X *
            (LinearMap.toMatrix (spaceBasis A) (spaceBasis B) V)ᴴ := by
    change LinearMap.toMatrix (spaceBasis B) (spaceBasis B)
      (V.comp (X.comp (LinearMap.adjoint V))) = _
    rw [← LinearMap.comp_assoc]
    rw [LinearMap.toMatrix_comp (spaceBasis B) (spaceBasis A) (spaceBasis B),
      LinearMap.toMatrix_comp (spaceBasis A) (spaceBasis A) (spaceBasis B),
      LinearMap.toMatrix_adjoint (spaceONB A) (spaceONB B)]
    rfl
  have hWmatrix :
      operatorEquivMatrix D (QuantumChannel.krausTerm W Y) =
        LinearMap.toMatrix (spaceBasis C) (spaceBasis D) W *
          operatorEquivMatrix C Y *
            (LinearMap.toMatrix (spaceBasis C) (spaceBasis D) W)ᴴ := by
    change LinearMap.toMatrix (spaceBasis D) (spaceBasis D)
      (W.comp (Y.comp (LinearMap.adjoint W))) = _
    rw [← LinearMap.comp_assoc]
    rw [LinearMap.toMatrix_comp (spaceBasis D) (spaceBasis C) (spaceBasis D),
      LinearMap.toMatrix_comp (spaceBasis C) (spaceBasis C) (spaceBasis D),
      LinearMap.toMatrix_adjoint (spaceONB C) (spaceONB D)]
    rfl
  unfold tensorSystem
  conv_lhs =>
    lhs
    rw [Matrix.reindexLinearEquiv_mul
      (R := ℂ) (A := ℂ)
      (eₘ := (finProdFinEquiv :
        (Fin B.dim × Fin D.dim) ≃ Fin (tensorSystem B D).dim))
      (eₙ := (finProdFinEquiv :
        (Fin A.dim × Fin C.dim) ≃ Fin (tensorSystem A C).dim))
      (eₒ := (finProdFinEquiv :
        (Fin A.dim × Fin C.dim) ≃ Fin (tensorSystem A C).dim))]
  rw [Matrix.reindexLinearEquiv_mul
    (R := ℂ) (A := ℂ)
    (eₘ := (finProdFinEquiv :
      (Fin B.dim × Fin D.dim) ≃ Fin (tensorSystem B D).dim))
    (eₙ := (finProdFinEquiv :
      (Fin A.dim × Fin C.dim) ≃ Fin (tensorSystem A C).dim))
    (eₒ := (finProdFinEquiv :
      (Fin B.dim × Fin D.dim) ≃ Fin (tensorSystem B D).dim))]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rw [← hVmatrix, ← hWmatrix]

/-- Tensor product of raw superoperators in the coordinates used by the HP tensor. -/
noncomputable def rawTensorMap (f : RawSuperoperator A B)
    (g : RawSuperoperator C D) :
    RawSuperoperator (tensorSystem A C) (tensorSystem B D) :=
  (operatorTensorEquiv B D).toLinearMap.comp
    ((TensorProduct.map f g).comp
      (operatorTensorEquiv A C).symm.toLinearMap)

@[simp]
theorem rawTensorMap_operatorTensorEquiv_tmul
    (f : RawSuperoperator A B) (g : RawSuperoperator C D)
    (X : Operator A) (Y : Operator C) :
    rawTensorMap f g (operatorTensorEquiv A C (X ⊗ₜ[ℂ] Y)) =
      operatorTensorEquiv B D (f X ⊗ₜ[ℂ] g Y) := by
  simp [rawTensorMap]

theorem rawTensorMap_sum_right {ι : Type*} [Fintype ι]
    (f : RawSuperoperator A B) (g : ι → RawSuperoperator C D) :
    (∑ i, rawTensorMap f (g i)) = rawTensorMap f (∑ i, g i) := by
  classical
  apply LinearMap.ext
  intro Z
  let z := (operatorTensorEquiv A C).symm Z
  have hz : operatorTensorEquiv A C z = Z := by simp [z]
  rw [← hz]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
      simp only [LinearMap.sum_apply, rawTensorMap_operatorTensorEquiv_tmul]
      rw [TensorProduct.tmul_sum, map_sum]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem rawTensorMap_sum_left {ι : Type*} [Fintype ι]
    (f : ι → RawSuperoperator A B) (g : RawSuperoperator C D) :
    (∑ i, rawTensorMap (f i) g) = rawTensorMap (∑ i, f i) g := by
  classical
  apply LinearMap.ext
  intro Z
  let z := (operatorTensorEquiv A C).symm Z
  have hz : operatorTensorEquiv A C z = Z := by simp [z]
  rw [← hz]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
      simp only [LinearMap.sum_apply, rawTensorMap_operatorTensorEquiv_tmul]
      rw [TensorProduct.sum_tmul, map_sum]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem krausTerm_tensorOperator
    (V : Space A →ₗ[ℂ] Space B) (W : Space C →ₗ[ℂ] Space D) :
    QuantumChannel.krausTerm (tensorOperator V W) =
      rawTensorMap (QuantumChannel.krausTerm V)
        (QuantumChannel.krausTerm W) := by
  apply LinearMap.ext
  intro Z
  let z := (operatorTensorEquiv A C).symm Z
  have hz : operatorTensorEquiv A C z = Z := by
    simp [z]
  rw [← hz]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
      rw [krausTerm_tensorOperator_tmul]
      exact (rawTensorMap_operatorTensorEquiv_tmul
        (QuantumChannel.krausTerm V) (QuantumChannel.krausTerm W) X Y).symm
  | add x y hx hy => simp [map_add, hx, hy]

theorem tensorOperator_adjoint_comp
    (V : Space A →ₗ[ℂ] Space B) (W : Space C →ₗ[ℂ] Space D) :
    (LinearMap.adjoint (tensorOperator V W)).comp (tensorOperator V W) =
      operatorTensorEquiv A C
        ((LinearMap.adjoint V).comp V ⊗ₜ[ℂ]
          (LinearMap.adjoint W).comp W) := by
  apply (operatorEquivMatrix (tensorSystem A C)).injective
  change LinearMap.toMatrix (spaceBasis (tensorSystem A C))
      (spaceBasis (tensorSystem A C))
      ((LinearMap.adjoint (tensorOperator V W)).comp
        (tensorOperator V W)) = _
  rw [LinearMap.toMatrix_comp
    (spaceBasis (tensorSystem A C)) (spaceBasis (tensorSystem B D))
    (spaceBasis (tensorSystem A C))]
  rw [LinearMap.toMatrix_adjoint (spaceONB (tensorSystem A C))
    (spaceONB (tensorSystem B D))]
  rw [tensorOperator_matrix]
  have hright := operatorTensorEquiv_matrix_tmul (A := A) (C := C)
    ((LinearMap.adjoint V).comp V) ((LinearMap.adjoint W).comp W)
  change _ = LinearMap.toMatrix (spaceBasis (tensorSystem A C))
    (spaceBasis (tensorSystem A C))
    (operatorTensorEquiv A C
      ((LinearMap.adjoint V).comp V ⊗ₜ[ℂ]
        (LinearMap.adjoint W).comp W))
  change LinearMap.toMatrix (spaceBasis (tensorSystem A C))
      (spaceBasis (tensorSystem A C))
      (operatorTensorEquiv A C
        ((LinearMap.adjoint V).comp V ⊗ₜ[ℂ]
          (LinearMap.adjoint W).comp W)) = _ at hright
  rw [hright]
  conv_lhs =>
    lhs
    change (Matrix.reindex finProdFinEquiv finProdFinEquiv
      (LinearMap.toMatrix (spaceBasis A) (spaceBasis B) V ⊗ₖ
        LinearMap.toMatrix (spaceBasis C) (spaceBasis D) W))ᴴ
    change Matrix.reindexLinearEquiv ℂ ℂ finProdFinEquiv finProdFinEquiv
      ((LinearMap.toMatrix (spaceBasis A) (spaceBasis B) V ⊗ₖ
        LinearMap.toMatrix (spaceBasis C) (spaceBasis D) W)ᴴ)
  rw [Matrix.conjTranspose_kronecker]
  have hVmatrix :
      LinearMap.toMatrix (spaceBasis A) (spaceBasis A)
          ((LinearMap.adjoint V).comp V) =
        (LinearMap.toMatrix (spaceBasis A) (spaceBasis B) V)ᴴ *
          LinearMap.toMatrix (spaceBasis A) (spaceBasis B) V := by
    rw [LinearMap.toMatrix_comp (spaceBasis A) (spaceBasis B) (spaceBasis A),
      LinearMap.toMatrix_adjoint (spaceONB A) (spaceONB B)]
  have hWmatrix :
      LinearMap.toMatrix (spaceBasis C) (spaceBasis C)
          ((LinearMap.adjoint W).comp W) =
        (LinearMap.toMatrix (spaceBasis C) (spaceBasis D) W)ᴴ *
          LinearMap.toMatrix (spaceBasis C) (spaceBasis D) W := by
    rw [LinearMap.toMatrix_comp (spaceBasis C) (spaceBasis D) (spaceBasis C),
      LinearMap.toMatrix_adjoint (spaceONB C) (spaceONB D)]
  unfold tensorSystem
  rw [Matrix.reindexLinearEquiv_mul
    (R := ℂ) (A := ℂ)
    (eₘ := (finProdFinEquiv :
      (Fin A.dim × Fin C.dim) ≃ Fin (tensorSystem A C).dim))
    (eₙ := (finProdFinEquiv :
      (Fin B.dim × Fin D.dim) ≃ Fin (tensorSystem B D).dim))
    (eₒ := (finProdFinEquiv :
      (Fin A.dim × Fin C.dim) ≃ Fin (tensorSystem A C).dim))]
  rw [← Matrix.mul_kronecker_mul]
  rw [← hVmatrix, ← hWmatrix]
  rfl

theorem sum_operatorTensorEquiv_tmul
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → Operator A) (y : κ → Operator C) :
    (∑ p : ι × κ, operatorTensorEquiv A C (x p.1 ⊗ₜ[ℂ] y p.2)) =
      operatorTensorEquiv A C ((∑ i, x i) ⊗ₜ[ℂ] ∑ j, y j) := by
  classical
  have htensor :
      (∑ p : ι × κ, x p.1 ⊗ₜ[ℂ] y p.2) =
        (∑ i, x i) ⊗ₜ[ℂ] ∑ j, y j := by
    calc
      (∑ p : ι × κ, x p.1 ⊗ₜ[ℂ] y p.2) =
          ∑ i, ∑ j, x i ⊗ₜ[ℂ] y j := Fintype.sum_prod_type _
      _ = ∑ i, x i ⊗ₜ[ℂ] ∑ j, y j := by
        apply Finset.sum_congr rfl
        intro i _
        simpa using (TensorProduct.tmul_sum (R := ℂ)
          (x i) Finset.univ y).symm
      _ = (∑ i, x i) ⊗ₜ[ℂ] ∑ j, y j := by
        simpa using (TensorProduct.sum_tmul (R := ℂ)
          Finset.univ x (∑ j, y j)).symm
  calc
    (∑ p : ι × κ, operatorTensorEquiv A C (x p.1 ⊗ₜ[ℂ] y p.2)) =
        operatorTensorEquiv A C
          (∑ p : ι × κ, x p.1 ⊗ₜ[ℂ] y p.2) := by
      exact (map_sum (operatorTensorEquiv A C)
        (fun p : ι × κ => x p.1 ⊗ₜ[ℂ] y p.2) Finset.univ).symm
    _ = _ := congrArg
      (fun Z : Operator A ⊗[ℂ] Operator C => operatorTensorEquiv A C Z)
      htensor

namespace KrausFamily

/-- Product Kraus family for the categorical tensor product. -/
def tensor (K : KrausFamily A B) (L : KrausFamily C D) :
    KrausFamily (tensorSystem A C) (tensorSystem B D) :=
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  letI := L.fintypeIndex
  letI := L.decidableEqIndex
  { index := K.index × L.index
    fintypeIndex := inferInstance
    decidableEqIndex := inferInstance
    operator := fun p => tensorOperator (K.operator p.1) (L.operator p.2) }

theorem tensor_map (K : KrausFamily A B) (L : KrausFamily C D) :
    (K.tensor L).map = K.map ⊗ₘ L.map := by
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  letI := L.fintypeIndex
  letI := L.decidableEqIndex
  apply HPHom.ext
  intro Z
  change (K.tensor L).rawMap Z = HPHom.tensorRaw K.map L.map Z
  have hraw : (K.tensor L).rawMap = rawTensorMap K.rawMap L.rawMap := by
    rw [rawMap]
    simp only [tensor, krausTerm_tensorOperator]
    have hright (i : K.index) :
        (∑ j, rawTensorMap (QuantumChannel.krausTerm (K.operator i))
          (QuantumChannel.krausTerm (L.operator j))) =
          rawTensorMap (QuantumChannel.krausTerm (K.operator i)) L.rawMap := by
      rw [rawMap]
      exact (rawTensorMap_sum_right
        (QuantumChannel.krausTerm (K.operator i))
        (fun j ↦ QuantumChannel.krausTerm (L.operator j)))
    calc
      (∑ x : K.index × L.index,
          rawTensorMap (QuantumChannel.krausTerm (K.operator x.1))
            (QuantumChannel.krausTerm (L.operator x.2))) =
          ∑ i, ∑ j,
            rawTensorMap (QuantumChannel.krausTerm (K.operator i))
              (QuantumChannel.krausTerm (L.operator j)) :=
        Fintype.sum_prod_type _
      _ = ∑ i, rawTensorMap (QuantumChannel.krausTerm (K.operator i))
          L.rawMap := by
        apply Finset.sum_congr rfl
        intro i _
        exact hright i
      _ = rawTensorMap K.rawMap L.rawMap := by
        rw [rawMap]
        exact (rawTensorMap_sum_left
          (fun i ↦ QuantumChannel.krausTerm (K.operator i)) L.rawMap)
  rw [hraw]
  rfl

/-- Input-side normalization of a product Kraus family. -/
def tensorNormalization (K : KrausFamily A B) (L : KrausFamily C D) :
    Operator (tensorSystem A C) :=
  operatorTensorEquiv A C (K.normalization ⊗ₜ[ℂ] L.normalization)

theorem tensor_normalization (K : KrausFamily A B) (L : KrausFamily C D) :
    (K.tensor L).normalization = K.tensorNormalization L := by
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  letI := L.fintypeIndex
  letI := L.decidableEqIndex
  rw [normalization]
  simp only [tensor]
  let x : K.index → Operator A := fun i =>
    (LinearMap.adjoint (K.operator i)).comp (K.operator i)
  let y : L.index → Operator C := fun j =>
    (LinearMap.adjoint (L.operator j)).comp (L.operator j)
  have hterm (p : K.index × L.index) :
      (LinearMap.adjoint
        (tensorOperator (K.operator p.1) (L.operator p.2))).comp
          (tensorOperator (K.operator p.1) (L.operator p.2)) =
        operatorTensorEquiv A C (x p.1 ⊗ₜ[ℂ] y p.2) := by
    exact tensorOperator_adjoint_comp (K.operator p.1) (L.operator p.2)
  calc
    (∑ p : K.index × L.index,
        (LinearMap.adjoint
          (tensorOperator (K.operator p.1) (L.operator p.2))).comp
            (tensorOperator (K.operator p.1) (L.operator p.2))) =
        ∑ p : K.index × L.index,
          operatorTensorEquiv A C (x p.1 ⊗ₜ[ℂ] y p.2) := by
      apply Finset.sum_congr rfl
      intro p _
      exact hterm p
    _ = operatorTensorEquiv A C ((∑ i, x i) ⊗ₜ[ℂ] ∑ j, y j) :=
      sum_operatorTensorEquiv_tmul x y
    _ = K.tensorNormalization L := by
      unfold tensorNormalization KrausFamily.normalization x y
      rfl

end KrausFamily

/-! ## Tensor closure of the physical predicates -/

theorem tensorHom_isEvent {f : A ⟶ B} {g : C ⟶ D}
    (hf : IsEvent f) (hg : IsEvent g) : IsEvent (f ⊗ₘ g) := by
  obtain ⟨K, hK⟩ := exists_krausFamily_of_isEvent
    (A := A) (B := B) (f := f) hf
  obtain ⟨L, hL⟩ := exists_krausFamily_of_isEvent
    (A := C) (B := D) (f := g) hg
  have hmap : (K.tensor L).map = f ⊗ₘ g := by
    rw [K.tensor_map L, hK, hL]
  rw [← hmap]
  exact (K.tensor L).map_isCompletelyPositive

theorem isTransformation_tensor {f : A ⟶ B} {g : C ⟶ D}
    (hf : IsTransformation f) (hg : IsTransformation g) :
    IsTransformation (f ⊗ₘ g) := by
  rcases hf with ⟨hfCP, K, hKmap, hKle⟩
  rcases hg with ⟨hgCP, L, hLmap, hLle⟩
  have hmap : (K.tensor L).map = f ⊗ₘ g := by
    rw [K.tensor_map L, hKmap, hLmap]
  refine ⟨tensorHom_isEvent hfCP hgCP, K.tensor L, hmap, ?_⟩
  rw [K.tensor_normalization L]
  exact operatorTensorEquiv_tmul_le_one
    (krausFamily_normalization_nonneg K) hKle hLle

theorem isChannel_tensor {f : A ⟶ B} {g : C ⟶ D}
    (hf : IsChannel f) (hg : IsChannel g) : IsChannel (f ⊗ₘ g) := by
  rcases hf with ⟨hfCP, K, hKmap, hKnorm⟩
  rcases hg with ⟨hgCP, L, hLmap, hLnorm⟩
  have hmap : (K.tensor L).map = f ⊗ₘ g := by
    rw [K.tensor_map L, hKmap, hLmap]
  refine ⟨tensorHom_isEvent hfCP hgCP, K.tensor L, hmap, ?_⟩
  rw [K.tensor_normalization L]
  unfold KrausFamily.tensorNormalization
  rw [hKnorm, hLnorm]
  exact operatorTensorEquiv_one_tmul_one

end QuantumModel
