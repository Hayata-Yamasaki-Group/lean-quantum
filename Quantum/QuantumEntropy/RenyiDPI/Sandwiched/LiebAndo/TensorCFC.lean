/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.RingTheory.Flat.Basic
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.LinearAlgebra.Lagrange
import Quantum.QuantumEntropy.TensorCFC
import Quantum.QuantumMechanics.Channel.Basic
import Quantum.QuantumMechanics.OperatorInstances
import Quantum.QuantumMechanics.QuantumState

/-!
# Tensor product CFC infrastructure

Infrastructure for the continuous functional calculus on tensor products,
proving that `CFC.rpow` distributes over tensor products of operators:
`(A ⊗ B)^p = A^p ⊗ B^p`.

## Strategy

Factor `TensorProduct.map A B = A.rTensor ℋ₂ * B.lTensor ℋ₁` where the two factors commute,
then use `StarAlgHomClass.map_cfc` to distribute `CFC.rpow` through each factor.

## Main results

* `TensorCFC.rTensorStarAlgHom` / `lTensorStarAlgHom`:
  The maps `A ↦ A.rTensor ℋ₂` and `B ↦ B.lTensor ℋ₁` as star algebra homomorphisms.
* `TensorCFC.rpow_rTensor` / `rpow_lTensor`:
  `CFC.rpow` distributes through `rTensor` / `lTensor`.
* `TensorCFC.rpow_tensorProduct`:
  `CFC.rpow (map A B) p = map (CFC.rpow A p) (CFC.rpow B p)` (modulo `rpow_mul_comm_nonneg`).
-/

open QuantumState QuantumChannel TensorProduct
open scoped NNReal Polynomial

namespace TensorCFC

universe u v
variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
variable [Nontrivial ℋ₁] [Nontrivial ℋ₂]

/-! ### Scalar tower instances -/

instance instIsScalarTower₁ : IsScalarTower ℝ≥0 ℂ (B ℋ₁) :=
  ⟨fun r s a => smul_assoc (r : ℂ) s a⟩
instance instIsScalarTower₂ : IsScalarTower ℝ≥0 ℂ (B ℋ₂) :=
  ⟨fun r s a => smul_assoc (r : ℂ) s a⟩
instance instIsScalarTowerTensor :
    IsScalarTower ℝ≥0 ℂ (B (ℋ₁ ⊗[ℂ] ℋ₂)) :=
  ⟨fun r s a => smul_assoc (r : ℂ) s a⟩

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
noncomputable def rTensorContinuousStarAlgHom :
    (ℋ₁ →L[ℂ] ℋ₁) →⋆ₐ[ℂ] ((ℋ₁ ⊗[ℂ] ℋ₂) →L[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂)) where
  toFun A := ((A : L ℋ₁).rTensor ℋ₂).toContinuousLinearMap
  map_one' := by
    change ((1 : L ℋ₁).rTensor ℋ₂).toContinuousLinearMap =
      (1 : L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap
    congr 1
    exact TensorProduct.ext' fun _ _ => rfl
  map_mul' A B := by
    change (((A : L ℋ₁).comp (B : L ℋ₁)).rTensor ℋ₂).toContinuousLinearMap =
      (((A : L ℋ₁).rTensor ℋ₂).comp
        ((B : L ℋ₁).rTensor ℋ₂)).toContinuousLinearMap
    congr 1
    exact TensorProduct.ext' fun _ _ => by simp
  map_zero' := by
    change ((0 : L ℋ₁).rTensor ℋ₂).toContinuousLinearMap =
      (0 : L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap
    congr 1
    exact TensorProduct.ext' fun _ _ => by simp
  map_add' A B := by
    change (((A : L ℋ₁) + (B : L ℋ₁)).rTensor ℋ₂).toContinuousLinearMap =
      ((A : L ℋ₁).rTensor ℋ₂ + (B : L ℋ₁).rTensor ℋ₂).toContinuousLinearMap
    congr 1
    exact TensorProduct.ext' fun _ _ => by simp
  commutes' r := by
    change ((algebraMap ℂ (L ℋ₁) r).rTensor ℋ₂).toContinuousLinearMap =
      (algebraMap ℂ (L (ℋ₁ ⊗[ℂ] ℋ₂)) r).toContinuousLinearMap
    congr 1
  map_star' A := by
    change ((LinearMap.adjoint (A : L ℋ₁)).rTensor ℋ₂).toContinuousLinearMap =
      (LinearMap.adjoint ((A : L ℋ₁).rTensor ℋ₂)).toContinuousLinearMap
    exact congrArg LinearMap.toContinuousLinearMap
      (LinearMap.adjoint_rTensor (A : L ℋ₁)).symm

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
noncomputable def lTensorContinuousStarAlgHom :
    (ℋ₂ →L[ℂ] ℋ₂) →⋆ₐ[ℂ] ((ℋ₁ ⊗[ℂ] ℋ₂) →L[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂)) where
  toFun B := ((B : L ℋ₂).lTensor ℋ₁).toContinuousLinearMap
  map_one' := by
    change ((1 : L ℋ₂).lTensor ℋ₁).toContinuousLinearMap =
      (1 : L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap
    congr 1
    exact TensorProduct.ext' fun _ _ => rfl
  map_mul' A B := by
    change (((A : L ℋ₂).comp (B : L ℋ₂)).lTensor ℋ₁).toContinuousLinearMap =
      (((A : L ℋ₂).lTensor ℋ₁).comp
        ((B : L ℋ₂).lTensor ℋ₁)).toContinuousLinearMap
    congr 1
    exact TensorProduct.ext' fun _ _ => by simp
  map_zero' := by
    change ((0 : L ℋ₂).lTensor ℋ₁).toContinuousLinearMap =
      (0 : L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap
    congr 1
    exact TensorProduct.ext' fun _ _ => by simp
  map_add' A B := by
    change (((A : L ℋ₂) + (B : L ℋ₂)).lTensor ℋ₁).toContinuousLinearMap =
      ((A : L ℋ₂).lTensor ℋ₁ + (B : L ℋ₂).lTensor ℋ₁).toContinuousLinearMap
    congr 1
    exact TensorProduct.ext' fun _ _ => by simp
  commutes' r := by
    change ((algebraMap ℂ (L ℋ₂) r).lTensor ℋ₁).toContinuousLinearMap =
      (algebraMap ℂ (L (ℋ₁ ⊗[ℂ] ℋ₂)) r).toContinuousLinearMap
    congr 1
    exact TensorProduct.ext' fun _ _ => by
      simp [Algebra.algebraMap_eq_smul_one, smul_tmul']
  map_star' A := by
    change ((LinearMap.adjoint (A : L ℋ₂)).lTensor ℋ₁).toContinuousLinearMap =
      (LinearMap.adjoint ((A : L ℋ₂).lTensor ℋ₁)).toContinuousLinearMap
    exact congrArg LinearMap.toContinuousLinearMap
      (LinearMap.adjoint_lTensor (A : L ℋ₂)).symm

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
@[simp] lemma rTensorContinuousStarAlgHom_apply (A : L ℋ₁) :
    rTensorContinuousStarAlgHom (ℋ₂ := ℋ₂) A.toContinuousLinearMap =
      ((rTensorStarAlgHom (ℋ₂ := ℋ₂)) A).toContinuousLinearMap := rfl

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
@[simp] lemma lTensorContinuousStarAlgHom_apply (B : L ℋ₂) :
    lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁) B.toContinuousLinearMap =
      ((lTensorStarAlgHom (ℋ₁ := ℋ₁)) B).toContinuousLinearMap := rfl

/-! ### Continuity -/

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma continuous_rTensorStarAlgHom :
    Continuous (rTensorContinuousStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)) :=
  (rTensorContinuousStarAlgHom (ℋ₁ := ℋ₁)
    (ℋ₂ := ℋ₂)).toLinearMap.continuous_of_finiteDimensional

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma continuous_lTensorStarAlgHom :
    Continuous (lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)) :=
  (lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁)
    (ℋ₂ := ℋ₂)).toLinearMap.continuous_of_finiteDimensional

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- Right tensoring as a star algebra homomorphism is monotone for the operator order. -/
@[gcongr]
lemma rTensorStarAlgHom_le_rTensorStarAlgHom {f g : L ℋ₁} (hfg : f ≤ g) :
    (rTensorStarAlgHom (ℋ₂ := ℋ₂)) f ≤ (rTensorStarAlgHom (ℋ₂ := ℋ₂)) g := by
  exact OrderHomClass.monotone (rTensorStarAlgHom (ℋ₂ := ℋ₂)) hfg

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- Left tensoring as a star algebra homomorphism is monotone for the operator order. -/
@[gcongr]
lemma lTensorStarAlgHom_le_lTensorStarAlgHom {f g : L ℋ₂} (hfg : f ≤ g) :
    (lTensorStarAlgHom (ℋ₁ := ℋ₁)) f ≤ (lTensorStarAlgHom (ℋ₁ := ℋ₁)) g := by
  exact OrderHomClass.monotone (lTensorStarAlgHom (ℋ₁ := ℋ₁)) hfg

/-! ### Unit reflection for rTensor / lTensor

In finite dimensions, `B.rTensor ℋ₂` is a unit iff `B` is a unit.
The forward direction uses a basis element to embed `ker B` into `ker (B.rTensor ℋ₂)`.
The reverse follows from flatness. -/

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma injective_rTensor_of_injective (B : L ℋ₁) (hB : Function.Injective B) :
    Function.Injective (B.rTensor ℋ₂) :=
  Module.Flat.rTensor_preserves_injective_linearMap B hB

omit [Nontrivial ℋ₁] in
private lemma injective_of_injective_rTensor (B : L ℋ₁) (hB : Function.Injective (B.rTensor ℋ₂)) :
    Function.Injective B := by
  intro v₁ v₂ hv
  have 𝒞 := Module.Free.chooseBasis ℂ ℋ₂
  haveI : Nonempty (Module.Free.ChooseBasisIndex ℂ ℋ₂) :=
    Fintype.card_pos_iff.mp (by
      have := Module.finrank_pos (R := ℂ) (M := ℋ₂)
      rwa [Module.finrank_eq_card_chooseBasisIndex] at this)
  obtain ⟨i₀⟩ := ‹Nonempty (Module.Free.ChooseBasisIndex ℂ ℋ₂)›
  have h : B.rTensor ℋ₂ (v₁ ⊗ₜ 𝒞 i₀) = B.rTensor ℋ₂ (v₂ ⊗ₜ 𝒞 i₀) := by
    simp [LinearMap.rTensor_tmul, hv]
  have hinj := hB h
  have key := congr_arg (TensorProduct.equivFinsuppOfBasisRight (M := ℋ₁) 𝒞) hinj
  simp only [TensorProduct.equivFinsuppOfBasisRight_apply_tmul,
    𝒞.repr_self, Finsupp.mapRange_single, one_smul] at key
  exact Finsupp.single_injective i₀ key

omit [Nontrivial ℋ₁] in
private lemma isUnit_rTensor_iff (B : L ℋ₁) :
    IsUnit (B.rTensor ℋ₂) ↔ IsUnit B := by
  simp only [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  exact ⟨injective_of_injective_rTensor B, injective_rTensor_of_injective B⟩

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma injective_lTensor_of_injective (B : L ℋ₂) (hB : Function.Injective B) :
    Function.Injective (B.lTensor ℋ₁) :=
  Module.Flat.lTensor_preserves_injective_linearMap B hB

omit [Nontrivial ℋ₂] in
private lemma injective_of_injective_lTensor (B : L ℋ₂) (hB : Function.Injective (B.lTensor ℋ₁)) :
    Function.Injective B := by
  intro v₁ v₂ hv
  have 𝒞 := Module.Free.chooseBasis ℂ ℋ₁
  haveI : Nonempty (Module.Free.ChooseBasisIndex ℂ ℋ₁) :=
    Fintype.card_pos_iff.mp (by
      have := Module.finrank_pos (R := ℂ) (M := ℋ₁)
      rwa [Module.finrank_eq_card_chooseBasisIndex] at this)
  obtain ⟨i₀⟩ := ‹Nonempty (Module.Free.ChooseBasisIndex ℂ ℋ₁)›
  have h : B.lTensor ℋ₁ (𝒞 i₀ ⊗ₜ v₁) = B.lTensor ℋ₁ (𝒞 i₀ ⊗ₜ v₂) := by
    simp [LinearMap.lTensor_tmul, hv]
  have hinj := hB h
  have key := congr_arg (fun x => (TensorProduct.equivFinsuppOfBasisLeft (N := ℋ₂) 𝒞 x) i₀) hinj
  simp only [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply] at key
  simp only [𝒞.repr_self, Finsupp.single_eq_same, one_smul] at key
  exact key

omit [Nontrivial ℋ₂] in
private lemma isUnit_lTensor_iff (B : L ℋ₂) :
    IsUnit (B.lTensor ℋ₁) ↔ IsUnit B := by
  simp only [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  exact ⟨injective_of_injective_lTensor B, injective_lTensor_of_injective B⟩

omit [Nontrivial ℋ₁] in
private lemma isUnit_rTensorContinuous_iff (B : ℋ₁ →L[ℂ] ℋ₁) :
    IsUnit (rTensorContinuousStarAlgHom (ℋ₂ := ℋ₂) B) ↔ IsUnit B := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap,
    ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap]
  exact isUnit_rTensor_iff (B : L ℋ₁)

omit [Nontrivial ℋ₂] in
private lemma isUnit_lTensorContinuous_iff (B : ℋ₂ →L[ℂ] ℋ₂) :
    IsUnit (lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁) B) ↔ IsUnit B := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap,
    ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap]
  exact isUnit_lTensor_iff (B : L ℋ₂)

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma rTensorContinuous_sub_algebraMap (A : B ℋ₁) (r : ℂ) :
    rTensorContinuousStarAlgHom (ℋ₂ := ℋ₂)
        (algebraMap ℂ (B ℋ₁) r - A) =
      algebraMap ℂ (B (ℋ₁ ⊗[ℂ] ℋ₂)) r -
        rTensorContinuousStarAlgHom (ℋ₂ := ℋ₂) A := by
  rw [map_sub]
  congr 1

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma lTensorContinuous_sub_algebraMap (B : ℋ₂ →L[ℂ] ℋ₂) (r : ℂ) :
    lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁)
        (algebraMap ℂ (ℋ₂ →L[ℂ] ℋ₂) r - B) =
      algebraMap ℂ ((ℋ₁ ⊗[ℂ] ℋ₂) →L[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂)) r -
        lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁) B := by
  rw [map_sub]
  congr 1
  exact (lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁)).commutes r

/-! ### Spectrum equality for tensor embeddings -/

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma rTensor_algebraMap (r : ℂ) :
    (algebraMap ℂ (L ℋ₁) r).rTensor ℋ₂ = algebraMap ℂ (L (ℋ₁ ⊗[ℂ] ℋ₂)) r :=
  TensorProduct.ext' fun _ _ => by simp [Algebra.algebraMap_eq_smul_one, smul_tmul']

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma lTensor_algebraMap (r : ℂ) :
    (algebraMap ℂ (L ℋ₂) r).lTensor ℋ₁ = algebraMap ℂ (L (ℋ₁ ⊗[ℂ] ℋ₂)) r :=
  TensorProduct.ext' fun _ _ => by simp [Algebra.algebraMap_eq_smul_one, smul_tmul']

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma rTensor_sub_algebraMap (A : L ℋ₁) (r : ℂ) :
    (algebraMap ℂ (L ℋ₁) r - A).rTensor ℋ₂ =
      algebraMap ℂ (L (ℋ₁ ⊗[ℂ] ℋ₂)) r - A.rTensor ℋ₂ := by
  rw [LinearMap.rTensor_sub, rTensor_algebraMap]

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma lTensor_sub_algebraMap (B : L ℋ₂) (r : ℂ) :
    (algebraMap ℂ (L ℋ₂) r - B).lTensor ℋ₁ =
      algebraMap ℂ (L (ℋ₁ ⊗[ℂ] ℋ₂)) r - B.lTensor ℋ₁ := by
  rw [LinearMap.lTensor_sub, lTensor_algebraMap]

omit [Nontrivial ℋ₁] in
lemma spectrum_rTensorStarAlgHom (A : B ℋ₁) :
    spectrum ℝ≥0 (rTensorContinuousStarAlgHom (ℋ₂ := ℋ₂) A) = spectrum ℝ≥0 A := by
  simp only [← spectrum.preimage_algebraMap ℂ (R := ℝ≥0)]
  congr 1
  ext r
  simp only [spectrum.mem_iff]
  constructor
  · intro h hunit
    apply h
    rw [← rTensorContinuous_sub_algebraMap]
    exact (isUnit_rTensorContinuous_iff _).mpr hunit
  · intro h hunit
    apply h
    rw [← rTensorContinuous_sub_algebraMap] at hunit
    exact (isUnit_rTensorContinuous_iff _).mp hunit

omit [Nontrivial ℋ₂] in
lemma spectrum_lTensorStarAlgHom (B : ℋ₂ →L[ℂ] ℋ₂) :
    spectrum ℝ≥0 (lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁) B) = spectrum ℝ≥0 B := by
  simp only [← spectrum.preimage_algebraMap ℂ (R := ℝ≥0)]
  congr 1
  ext r
  simp only [spectrum.mem_iff]
  constructor
  · intro h hunit
    apply h
    rw [← lTensorContinuous_sub_algebraMap]
    exact (isUnit_lTensorContinuous_iff _).mpr hunit
  · intro h hunit
    apply h
    rw [← lTensorContinuous_sub_algebraMap] at hunit
    exact (isUnit_lTensorContinuous_iff _).mp hunit

/-! ### Main result: rpow distributes over tensor products

Proved directly using eigenvector bases for A and B. The tensor product
of eigenvector bases provides a basis for `ℋ₁ ⊗ ℋ₂` of simultaneous
eigenvectors, reducing the proof to the scalar identity `(λμ)^p = λ^p μ^p`. -/

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma star_map (A : L ℋ₁) (B : L ℋ₂) :
    star (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
      TensorProduct.map (star A) (star B) := by
  simp only [LinearMap.star_eq_adjoint, TensorProduct.adjoint_map]

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma isSelfAdjoint_map_of_nonneg (A : L ℋ₁) (B : L ℋ₂)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    IsSelfAdjoint (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) := by
  rw [IsSelfAdjoint, star_map, (IsSelfAdjoint.of_nonneg hA).star_eq,
      (IsSelfAdjoint.of_nonneg hB).star_eq]

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- Tensoring on the right, bundled as a linear map in the left operator. -/
def tensorMapLeftₗ (B : L ℋ₂) : L ℋ₁ →ₗ[ℂ] L (ℋ₁ ⊗[ℂ] ℋ₂) where
  toFun A := TensorProduct.map A B
  map_add' A C := by
    ext x y
    simp [add_tmul]
  map_smul' c A := by
    ext x y
    simp [TensorProduct.smul_tmul']

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- Tensor product maps are monotone in the left factor when the right factor is nonnegative. -/
@[gcongr]
lemma tensorProduct_map_le_map_left
    {A C : L ℋ₁} (B : L ℋ₂) (hB : 0 ≤ B) (hAC : A ≤ C) :
    tensorMapLeftₗ B A ≤ tensorMapLeftₗ B C := by
  have hpos : 0 ≤ tensorMapLeftₗ B (C - A) :=
    map_nonneg_of_nonneg (C - A) B (sub_nonneg.mpr hAC) hB
  rw [map_sub] at hpos
  exact sub_nonneg.mp hpos

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- Tensoring on the left, bundled as a linear map in the right operator. -/
def tensorMapRightₗ (A : L ℋ₁) : L ℋ₂ →ₗ[ℂ] L (ℋ₁ ⊗[ℂ] ℋ₂) where
  toFun B := TensorProduct.map A B
  map_add' B D := by
    ext x y
    simp [tmul_add]
  map_smul' c B := by
    ext x y
    simp [TensorProduct.tmul_smul]

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- Tensor product maps are monotone in the right factor when the left factor is nonnegative. -/
@[gcongr]
lemma tensorProduct_map_le_map_right
    (A : L ℋ₁) (hA : 0 ≤ A) {B D : L ℋ₂} (hBD : B ≤ D) :
    tensorMapRightₗ A B ≤ tensorMapRightₗ A D := by
  have hpos : 0 ≤ tensorMapRightₗ A (D - B) :=
    map_nonneg_of_nonneg A (D - B) hA (sub_nonneg.mpr hBD)
  rw [map_sub] at hpos
  exact sub_nonneg.mp hpos

section TensorRpowStatements

-- The statements below need `NonnegSpectrumClass ℝ` on operators of a tensor product. Try first,
-- only inside this section, the C⋆-algebra instance that the default search ends up using.
attribute [local instance high] CStarAlgebra.instNonnegSpectrumClass'

/-! ### CFC distribution through rTensor / lTensor -/

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- `rTensorContinuousStarAlgHom` is the tensor product with the identity. -/
private lemma map_one_toCLM_eq_rTensor (A : B ℋ₁) :
    (TensorProduct.map (A : L ℋ₁) ((1 : B ℋ₂) : L ℋ₂) : L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap =
      (rTensorContinuousStarAlgHom (ℋ₂ := ℋ₂)) A := rfl

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- `lTensorContinuousStarAlgHom` is the tensor product with the identity. -/
private lemma one_map_toCLM_eq_lTensor (B : ℋ₂ →L[ℂ] ℋ₂) :
    (TensorProduct.map ((1 : ℋ₁ →L[ℂ] ℋ₁) : L ℋ₁) (B : L ℋ₂) :
        L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap =
      (lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁)) B := rfl

omit [Nontrivial ℋ₁] in
lemma rpow_rTensor (A : B ℋ₁) (p : ℝ) (hA : 0 ≤ A) :
    CFC.rpow ((rTensorContinuousStarAlgHom (ℋ₂ := ℋ₂)) A) p =
      (rTensorContinuousStarAlgHom (ℋ₂ := ℋ₂)) (CFC.rpow A p) := by
  have h := rpow_tensorProduct A (1 : B ℋ₂) p hA (by positivity)
  have hone : CFC.rpow (1 : B ℋ₂) p = 1 := by
    rw [CFC.rpow_eq_pow, CFC.one_rpow]
  rwa [hone, map_one_toCLM_eq_rTensor, map_one_toCLM_eq_rTensor] at h

omit [Nontrivial ℋ₂] in
lemma rpow_lTensor (B : ℋ₂ →L[ℂ] ℋ₂) (p : ℝ) (hB : 0 ≤ B) :
    CFC.rpow ((lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁)) B) p =
      (lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁)) (CFC.rpow B p) := by
  have h := rpow_tensorProduct (1 : ℋ₁ →L[ℂ] ℋ₁) B p (by positivity) hB
  have hone : CFC.rpow (1 : ℋ₁ →L[ℂ] ℋ₁) p = 1 := by
    rw [CFC.rpow_eq_pow, CFC.one_rpow]
  rwa [hone, one_map_toCLM_eq_lTensor, one_map_toCLM_eq_lTensor] at h

end TensorRpowStatements

end TensorCFC

namespace TensorCFC

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u

/-- `star (1 ⊗ g) = 1 ⊗ (star g)` for the right tensor factor. -/
lemma tensorMap_right_star {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂]
    (g : L ℋ₂) :
    star (TensorProduct.map (LinearMap.id (M := ℋ₁)) g : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
      TensorProduct.map (LinearMap.id (M := ℋ₁)) (star g) := by
  have h_id_sa : star (LinearMap.id : L ℋ₁) = LinearMap.id := by
    rw [show (LinearMap.id : L ℋ₁) = 1 from rfl,
        IsSelfAdjoint.star_eq (IsSelfAdjoint.one (R := L ℋ₁))]
  rw [LinearMap.star_eq_adjoint, TensorProduct.adjoint_map, ← LinearMap.star_eq_adjoint,
      ← LinearMap.star_eq_adjoint, h_id_sa]

end

end TensorCFC
