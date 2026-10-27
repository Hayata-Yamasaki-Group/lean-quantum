/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.Channel.Equivalence
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.LinearAlgebra.Lagrange

/-!
# Tensor product CFC on linear endomorphisms

Infrastructure for the continuous functional calculus on tensor products,
proving that `CFC.rpow` distributes over tensor products of operators:
`(A ⊗ B)^p = A^p ⊗ B^p`.

## Strategy

Use the tensor product of orthonormal eigenvector bases for `A` and `B`.
On each basis vector, the equality reduces to `(λμ)^p = λ^p μ^p` for nonnegative eigenvalues.

## Main results

* `TensorCFC.rTensorStarAlgHom` / `lTensorStarAlgHom`:
  The maps `A ↦ A.rTensor ℋ₂` and `B ↦ B.lTensor ℋ₁` as star algebra homomorphisms.
* `TensorCFC.rpow_rTensor` / `rpow_lTensor`:
  `CFC.rpow` distributes through `rTensor` / `lTensor`.
* `TensorCFC.rpow_tensorProduct`:
  `CFC.rpow (map A B) p = map (CFC.rpow A p) (CFC.rpow B p)`.
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

/-! ### Star algebra homomorphisms for rTensor / lTensor -/
noncomputable def rTensorStarAlgHom : L ℋ₁ →⋆ₐ[ℂ] L (ℋ₁ ⊗[ℂ] ℋ₂) where
  toFun f := f.rTensor ℋ₂
  map_one' := TensorProduct.ext' fun _ _ => rfl
  map_mul' _ _ := TensorProduct.ext' fun _ _ => by simp
  map_zero' := TensorProduct.ext' fun _ _ => by simp
  map_add' _ _ := TensorProduct.ext' fun _ _ => by simp
  commutes' r := TensorProduct.ext' fun _ _ => by
    simp [Algebra.algebraMap_eq_smul_one, smul_tmul']
  map_star' f := by
    simp only [LinearMap.star_eq_adjoint]
    exact (LinearMap.adjoint_rTensor f).symm

noncomputable def lTensorStarAlgHom : L ℋ₂ →⋆ₐ[ℂ] L (ℋ₁ ⊗[ℂ] ℋ₂) where
  toFun g := g.lTensor ℋ₁
  map_one' := TensorProduct.ext' fun _ _ => rfl
  map_mul' _ _ := TensorProduct.ext' fun _ _ => by simp
  map_zero' := TensorProduct.ext' fun _ _ => by simp
  map_add' _ _ := TensorProduct.ext' fun _ _ => by simp
  commutes' r := TensorProduct.ext' fun _ _ => by
    simp [Algebra.algebraMap_eq_smul_one, smul_tmul']
  map_star' g := by
    simp only [LinearMap.star_eq_adjoint]
    exact (LinearMap.adjoint_lTensor g).symm

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
@[simp] lemma rTensorStarAlgHom_apply (f : L ℋ₁) :
    (rTensorStarAlgHom (ℋ₂ := ℋ₂)) f = f.rTensor ℋ₂ := rfl

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
@[simp] lemma lTensorStarAlgHom_apply (g : L ℋ₂) :
    (lTensorStarAlgHom (ℋ₁ := ℋ₁)) g = g.lTensor ℋ₁ := rfl

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

/-! ### Factorization and commutativity -/

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma map_eq_rTensor_mul_lTensor (f : L ℋ₁) (g : L ℋ₂) :
    (TensorProduct.map f g : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
      rTensorStarAlgHom f * lTensorStarAlgHom g :=
  TensorProduct.ext' fun x y => by
    simp only [rTensorStarAlgHom_apply, lTensorStarAlgHom_apply]
    change TensorProduct.map f g (x ⊗ₜ y) =
      (f.rTensor ℋ₂).comp (g.lTensor ℋ₁) (x ⊗ₜ y)
    simp

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma map_eq_lTensor_mul_rTensor (f : L ℋ₁) (g : L ℋ₂) :
    (TensorProduct.map f g : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
      (lTensorStarAlgHom (ℋ₁ := ℋ₁)) g * (rTensorStarAlgHom (ℋ₂ := ℋ₂)) f :=
  TensorProduct.ext' fun x y => by
    simp only [rTensorStarAlgHom_apply, lTensorStarAlgHom_apply]
    change TensorProduct.map f g (x ⊗ₜ y) =
      (g.lTensor ℋ₁).comp (f.rTensor ℋ₂) (x ⊗ₜ y)
    simp

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma commute_rTensor_lTensor (f : L ℋ₁) (g : L ℋ₂) :
    Commute (rTensorStarAlgHom f) (lTensorStarAlgHom g) := by
  change _ * _ = _ * _
  rw [← map_eq_rTensor_mul_lTensor, ← map_eq_lTensor_mul_rTensor]

/-! ### Continuity -/

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma rTensorStarAlgHom_nonneg (f : L ℋ₁) (hf : 0 ≤ f) :
    0 ≤ (rTensorStarAlgHom (ℋ₂ := ℋ₂)) f := by
  obtain ⟨p, hp, rfl⟩ := (StarOrderedRing.le_iff 0 f).mp hf
  rw [StarOrderedRing.le_iff]
  simp only [zero_add]
  exact ⟨rTensorStarAlgHom p,
    AddSubmonoid.closure_induction
      (fun x ⟨s, hs⟩ => AddSubmonoid.subset_closure
        ⟨rTensorStarAlgHom s, by
          change star (rTensorStarAlgHom s) * rTensorStarAlgHom s = rTensorStarAlgHom x
          rw [← map_star rTensorStarAlgHom, ← map_mul rTensorStarAlgHom]
          exact congr_arg rTensorStarAlgHom hs⟩)
      (by rw [map_zero]; exact AddSubmonoid.zero_mem _)
      (fun x y _ _ hx hy => by rw [map_add]; exact AddSubmonoid.add_mem _ hx hy)
      hp,
    rfl⟩

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- Right tensoring as a star algebra homomorphism is monotone for the operator order. -/
@[gcongr]
lemma rTensorStarAlgHom_le_rTensorStarAlgHom {f g : L ℋ₁} (hfg : f ≤ g) :
    (rTensorStarAlgHom (ℋ₂ := ℋ₂)) f ≤ (rTensorStarAlgHom (ℋ₂ := ℋ₂)) g := by
  exact OrderHomClass.monotone (rTensorStarAlgHom (ℋ₂ := ℋ₂)) hfg

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
lemma lTensorStarAlgHom_nonneg (g : L ℋ₂) (hg : 0 ≤ g) :
    0 ≤ (lTensorStarAlgHom (ℋ₁ := ℋ₁)) g := by
  obtain ⟨p, hp, rfl⟩ := (StarOrderedRing.le_iff 0 g).mp hg
  rw [StarOrderedRing.le_iff]
  simp only [zero_add]
  exact ⟨lTensorStarAlgHom p,
    AddSubmonoid.closure_induction
      (fun x ⟨s, hs⟩ => AddSubmonoid.subset_closure
        ⟨lTensorStarAlgHom s, by
          change star (lTensorStarAlgHom s) * lTensorStarAlgHom s = lTensorStarAlgHom x
          rw [← map_star lTensorStarAlgHom, ← map_mul lTensorStarAlgHom]
          exact congr_arg lTensorStarAlgHom hs⟩)
      (by rw [map_zero]; exact AddSubmonoid.zero_mem _)
      (fun x y _ _ hx hy => by rw [map_add]; exact AddSubmonoid.add_mem _ hx hy)
      hp,
    rfl⟩

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
lemma isUnit_rTensor_iff (B : L ℋ₁) :
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
lemma isUnit_lTensor_iff (B : L ℋ₂) :
    IsUnit (B.lTensor ℋ₁) ↔ IsUnit B := by
  simp only [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  exact ⟨injective_of_injective_lTensor B, injective_lTensor_of_injective B⟩

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

/-! ### CFC eigenvalue property

In finite dimensions, the CFC maps eigenvectors to eigenvectors with eigenvalues
transformed by the function: if `T v = μ • v` then `cfc f T v = f(μ) • v`.
The proof uses Lagrange interpolation on the finite spectrum combined with
`cfc_congr` and `cfc_polynomial`. -/
private lemma isScalarTower_real {ℋ : Type*} [Qudit ℋ] :
    IsScalarTower ℝ ℂ (B ℋ) :=
  ⟨fun r s a => by
    change ((r : ℂ) • s) • a = (r : ℂ) • s • a
    rw [smul_assoc]⟩

private lemma pow_apply_eigenvector {ℋ : Type*} [Qudit ℋ]
    (T : B ℋ) (μ : ℂ) (v : ℋ) (hv : T v = μ • v) (n : ℕ) :
    (T ^ n) v = μ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : (T ^ (n + 1)) v = (T ^ n) (T v) := rfl
    rw [this, hv, map_smul, ih, smul_smul, pow_succ']

private lemma aeval_apply_eigenvector {ℋ : Type*} [Qudit ℋ]
    (T : B ℋ) (μ : ℂ) (v : ℋ) (hv : T v = μ • v) (q : ℝ[X]) :
    (Polynomial.aeval T q) v = (Polynomial.aeval μ q) • v := by
  letI : IsScalarTower ℝ ℂ (B ℋ) :=
    RestrictScalars.isScalarTower ℝ ℂ (B ℋ)
  induction q using Polynomial.induction_on' with
  | add p₁ p₂ hp₁ hp₂ =>
    simp only [map_add, ContinuousLinearMap.add_apply, hp₁, hp₂, add_smul]
  | monomial n r =>
    simp only [Polynomial.aeval_monomial]
    change (algebraMap ℝ (B ℋ) r) ((T ^ n) v) = _
    rw [pow_apply_eigenvector T μ v hv n, map_smul,
        IsScalarTower.algebraMap_apply ℝ ℂ (B ℋ)]
    simp only [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, smul_smul, mul_comm]

private lemma spectrum_real_finite {ℋ : Type*} [Qudit ℋ]
    (T : B ℋ) : Set.Finite (spectrum ℝ T) := by
  letI : IsScalarTower ℝ ℂ (B ℋ) :=
    RestrictScalars.isScalarTower ℝ ℂ (B ℋ)
  rw [← spectrum.preimage_algebraMap ℂ (R := ℝ), ContinuousLinearMap.spectrum_eq]
  exact (Module.End.finite_spectrum (T : L ℋ)).preimage
    (fun _ _ _ _ h => RCLike.ofReal_injective h)

-- Finite-spectrum interpolation gives this identity for arbitrary `f`.
private lemma cfc_apply_eigenvector_continuous {ℋ : Type*} [Qudit ℋ]
    (T : B ℋ) (hT_sa : IsSelfAdjoint T) (f : ℝ → ℝ)
    (v : ℋ) (μ : ℝ) (hv : T v = (algebraMap ℝ ℂ μ) • v) (hμ : μ ∈ spectrum ℝ T) :
    cfc f T v = (algebraMap ℝ ℂ (f μ)) • v := by
  letI : IsScalarTower ℝ ℂ (B ℋ) :=
    RestrictScalars.isScalarTower ℝ ℂ (B ℋ)
  have hfin := spectrum_real_finite T
  set S := hfin.toFinset
  have hS_mem : ∀ x : ℝ, x ∈ S ↔ x ∈ spectrum ℝ T := fun x => hfin.mem_toFinset
  have hμ_mem_S : μ ∈ S := (hS_mem μ).mpr hμ
  have hinj : Set.InjOn (id : ℝ → ℝ) (↑S : Set ℝ) :=
    Function.injective_id.injOn
  let q := Lagrange.interpolate S id (fun s => f s)
  have hq_eval : ∀ x ∈ S, Polynomial.eval x q = f x :=
    fun x hx => Lagrange.eval_interpolate_at_node (fun s => f s) hinj hx
  have hcfc_eq : cfc f T = cfc q.eval T := by
    apply cfc_congr
    intro x hx
    exact (hq_eval x ((hS_mem x).mpr hx)).symm
  have hpoly : cfc q.eval T = Polynomial.aeval T q :=
    cfc_polynomial q T
  rw [hcfc_eq, hpoly, aeval_apply_eigenvector T (algebraMap ℝ ℂ μ) v hv q]
  congr 1
  rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
  congr 1
  exact hq_eval μ hμ_mem_S

private lemma cfc_apply_eigenvector {ℋ : Type*} [Qudit ℋ]
    (T : B ℋ) (hT_sa : IsSelfAdjoint T) (f : ℝ → ℝ)
    (v : ℋ) (μ : ℝ) (hv : T v = (algebraMap ℝ ℂ μ) • v) (hμ : μ ∈ spectrum ℝ T) :
    cfc f T v = (algebraMap ℝ ℂ (f μ)) • v := by
  exact cfc_apply_eigenvector_continuous T hT_sa f v μ hv hμ

private lemma rpow_apply_eigenvector {ℋ : Type*} [Qudit ℋ]
    (T : B ℋ) (hT : 0 ≤ T) (p : ℝ) (v : ℋ) (μ : ℝ)
    (hv : T v = (algebraMap ℝ ℂ μ) • v) (hμ : μ ∈ spectrum ℝ T) :
    CFC.rpow T p v = (algebraMap ℝ ℂ (μ ^ p)) • v := by
  rw [CFC.rpow_eq_pow]
  rw [CFC.rpow_eq_cfc_real (a := T) (y := p) (ha := hT)]
  exact cfc_apply_eigenvector T (IsSelfAdjoint.of_nonneg hT)
    (fun x : ℝ => x ^ p) v μ hv hμ

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
lemma map_nonneg_of_nonneg (A : L ℋ₁) (B : L ℋ₂)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) := by
  rw [map_eq_rTensor_mul_lTensor]
  exact Commute.mul_nonneg
    (rTensorStarAlgHom_nonneg A hA)
    (lTensorStarAlgHom_nonneg B hB)
    (commute_rTensor_lTensor A B)

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

lemma eigenvalue_nonneg_of_nonneg {ℋ : Type*} [Qudit ℋ]
    {n : ℕ} (T : L ℋ) (hT : 0 ≤ T) (hT_sym : T.IsSymmetric) (hn : Module.finrank ℂ ℋ = n)
    (i : Fin n) : 0 ≤ hT_sym.eigenvalues hn i := by
  have hpos := (LinearMap.nonneg_iff_isPositive T).mp hT
  set v := hT_sym.eigenvectorBasis hn i
  have hv_ne : v ≠ 0 := (hT_sym.eigenvectorBasis hn).toBasis.ne_zero i
  have hinn := hpos.2 v
  rw [hT_sym.apply_eigenvectorBasis, inner_smul_left, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul] at hinn
  refine nonneg_of_mul_nonneg_left hinn ?_
  rw [inner_self_eq_norm_sq]
  exact pow_pos (norm_pos_iff.mpr hv_ne) 2

end TensorCFC

namespace TensorCFC

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u

/-- Natural-power eigenvector formula: `A v = c • v ⟹ Aⁿ v = cⁿ • v`. -/
private lemma pow_apply_of_eigenvector
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : B ℋ} {v : ℋ} {c : ℂ} (hv : A v = c • v) :
    ∀ n : ℕ, (A ^ n) v = c ^ n • v
  | 0 => by rw [pow_zero, ContinuousLinearMap.one_apply, pow_zero, one_smul]
  | n + 1 => by
    rw [pow_succ, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, hv, map_smul,
        pow_apply_of_eigenvector hv n, smul_smul]
    congr 1
    rw [← pow_succ']

end

end TensorCFC

namespace TensorCFC

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u

/-- Real-polynomial eigenvector formula: `A v = (c:ℂ) • v ⟹ (aeval A p) v = (p.eval c)
  • v`. -/
private lemma aeval_apply_of_eigenvector_real
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : B ℋ} {v : ℋ} {c : ℝ} (hv : A v = ((c : ℝ) : ℂ) • v) (p : Polynomial ℝ) :
    (Polynomial.aeval A p) v = ((p.eval c : ℝ) : ℂ) • v := by
  induction p using Polynomial.induction_on with
  | C r =>
    rw [Polynomial.aeval_C, Polynomial.eval_C]
    rw [show ((algebraMap ℝ (B ℋ)) r : B ℋ) = ((r : ℝ) : ℂ) • (1 : B ℋ) from by
      rw [show ((r : ℝ) : ℂ) • (1 : B ℋ) = (algebraMap ℂ (B ℋ)) ((r : ℝ) : ℂ) from
        (Algebra.algebraMap_eq_smul_one ((r : ℝ) : ℂ)).symm]
      rfl]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  | add p q hp hq =>
    rw [map_add, Polynomial.eval_add, ContinuousLinearMap.add_apply, hp, hq,
        Complex.ofReal_add, add_smul]
  | monomial n r _ =>
    rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        Complex.ofReal_mul, Complex.ofReal_pow]
    rw [show ((algebraMap ℝ (B ℋ)) r : B ℋ) = ((r : ℝ) : ℂ) • (1 : B ℋ) from by
      rw [show ((r : ℝ) : ℂ) • (1 : B ℋ) = (algebraMap ℂ (B ℋ)) ((r : ℝ) : ℂ) from
        (Algebra.algebraMap_eq_smul_one ((r : ℝ) : ℂ)).symm]
      rfl]
    rw [smul_mul_assoc, one_mul, ContinuousLinearMap.smul_apply,
        pow_apply_of_eigenvector hv (n + 1), smul_smul]

end

end TensorCFC

namespace TensorCFC

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u

/-- **CFC on an eigenvector (real version).** If `A` is self-adjoint, `A v = μ • v`, and
    `μ ∈ spectrum ℝ A`, then `cfc f A v = f(μ) • v`. Proof by Lagrange interpolation:
    a polynomial `q` agreeing with `f` on the (finite) spectrum gives `cfc f A = aeval A q`,
    and `aeval A q v = q(μ) • v = f(μ) • v`. -/
lemma cfc_real_apply_eigenvector
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : B ℋ} (hA : IsSelfAdjoint A) (f : ℝ → ℝ)
    {v : ℋ} {μ : ℝ} (hv : A v = (μ : ℂ) • v) (hμ : μ ∈ spectrum ℝ A) :
    cfc f A v = ((f μ : ℝ) : ℂ) • v := by
  classical
  set S : Finset ℝ := (TensorCFC.spectrum_real_finite A).toFinset with hS
  set q : Polynomial ℝ := Lagrange.interpolate S id f with hq
  have hInj : Set.InjOn (id : ℝ → ℝ) (S : Set ℝ) := Function.injective_id.injOn
  have hEvalNode : ∀ x ∈ S, q.eval x = f x := by
    intro x hx
    have := Lagrange.eval_interpolate_at_node (r := f) (v := id) hInj hx
    simpa using this
  have hEqOn : (spectrum ℝ A).EqOn f (fun x => q.eval x) := by
    intro x hx
    have hxS : x ∈ S := by rw [hS, Set.Finite.mem_toFinset]; exact hx
    exact (hEvalNode x hxS).symm
  have h1 : cfc f A = cfc (fun x => q.eval x) A := cfc_congr hEqOn
  have h2 : cfc (fun x => q.eval x) A = Polynomial.aeval A q := cfc_polynomial q A
  have hμS : μ ∈ S := by rw [hS, Set.Finite.mem_toFinset]; exact hμ
  rw [h1, h2, aeval_apply_of_eigenvector_real hv q, hEvalNode μ hμS]

end

end TensorCFC

namespace TensorCFC

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u

/-- A real eigenvalue (with nonzero eigenvector) lies in `spectrum ℝ A`. -/
lemma mem_spectrum_real_of_eigenvector
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : B ℋ} {v : ℋ} {μ : ℝ} (hv0 : v ≠ 0) (hv : A v = (μ : ℂ) • v) :
    μ ∈ spectrum ℝ A := by
  have hev : Module.End.HasEigenvalue (A : L ℋ) (μ : ℂ) := by
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hv0⟩
    rw [Module.End.mem_eigenspace_iff]; exact hv
  have hmem : (μ : ℂ) ∈ spectrum ℂ A := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact hev.mem_spectrum
  letI : IsScalarTower ℝ ℂ (B ℋ) :=
    RestrictScalars.isScalarTower ℝ ℂ (B ℋ)
  rw [← spectrum.preimage_algebraMap ℂ]
  simpa using hmem

end

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

namespace TensorCFC

section LinearMaps

universe u v

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]

lemma rpow_apply_eigenvector_linear {ℋ : Type*} [Qudit ℋ]
    (T : L ℋ) (hT : 0 ≤ T) (p : ℝ) (v : ℋ) (μ : ℝ)
    (hv : T v = (algebraMap ℝ ℂ μ) • v) (hμ : μ ∈ spectrum ℝ T) :
    CFC.rpow T p v = (algebraMap ℝ ℂ (μ ^ p)) • v := by
  classical
  haveI : IsScalarTower ℝ ℂ (L ℋ) := RestrictScalars.isScalarTower ℝ ℂ (L ℋ)
  have hfin : Set.Finite (spectrum ℝ T) := by
    rw [← spectrum.preimage_algebraMap ℂ (R := ℝ)]
    exact (Module.End.finite_spectrum T).preimage
      (fun _ _ _ _ h => RCLike.ofReal_injective h)
  let S := hfin.toFinset
  let q := Lagrange.interpolate S id (fun x : ℝ => x ^ p)
  have hq : ∀ x ∈ S, q.eval x = x ^ p :=
    fun x hx => Lagrange.eval_interpolate_at_node _ Function.injective_id.injOn hx
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real (a := T) (y := p) (ha := hT)]
  have hcfc : cfc (fun x : ℝ => x ^ p) T = cfc q.eval T :=
    cfc_congr fun x hx => (hq x (hfin.mem_toFinset.mpr hx)).symm
  rw [hcfc, cfc_polynomial q T (IsSelfAdjoint.of_nonneg hT)]
  by_cases hv0 : v = 0
  · simp [hv0]
  have hev : Module.End.HasEigenvector T (algebraMap ℝ ℂ μ) v :=
    ⟨Module.End.mem_eigenspace_iff.mpr hv, hv0⟩
  have hqapply : Polynomial.aeval T q v =
      (Polynomial.aeval (algebraMap ℝ ℂ μ) q) • v := by
    have hpoly : Polynomial.aeval T q =
        Polynomial.aeval T (q.map (algebraMap ℝ ℂ)) := by
      exact Polynomial.aeval_eq_aeval_map (IsScalarTower.algebraMap_eq ℝ ℂ (L ℋ)) q T
    rw [hpoly, Module.End.aeval_apply_of_hasEigenvector hev]
    congr 1
    rw [Polynomial.eval_map_algebraMap, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
  rw [hqapply, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
    hq μ (hfin.mem_toFinset.mpr hμ)]

/-- `CFC.rpow` distributes over tensor products of positive linear endomorphisms:
`(A ⊗ B) ^ p = A ^ p ⊗ B ^ p`. The proof compares the maps on the tensor product
of orthonormal eigenbases. Lagrange interpolation on the finite spectra gives the
real-power eigenvector formula, reducing the comparison to multiplicativity of scalar
real powers on nonnegative eigenvalues.

Source: arXiv:1306.3142v4, chapter-level reference (no numbered correspondence). -/
theorem rpow_tensorProduct (A : L ℋ₁) (B : L ℋ₂) (p : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    CFC.rpow (TensorProduct.map A B) p = TensorProduct.map (CFC.rpow A p) (CFC.rpow B p) := by
  haveI : IsScalarTower ℝ ℂ (L ℋ₁) := RestrictScalars.isScalarTower ℝ ℂ (L ℋ₁)
  haveI : IsScalarTower ℝ ℂ (L ℋ₂) := RestrictScalars.isScalarTower ℝ ℂ (L ℋ₂)
  haveI : IsScalarTower ℝ ℂ (L (ℋ₁ ⊗[ℂ] ℋ₂)) :=
    RestrictScalars.isScalarTower ℝ ℂ (L (ℋ₁ ⊗[ℂ] ℋ₂))
  have hA_pos := (LinearMap.nonneg_iff_isPositive A).mp hA
  have hB_pos := (LinearMap.nonneg_iff_isPositive B).mp hB
  let eA := hA_pos.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ₁) rfl
  let eB := hB_pos.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ₂) rfl
  let eigA := hA_pos.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ₁) rfl
  let eigB := hB_pos.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ₂) rfl
  have hAB : 0 ≤ (TensorProduct.map A B : L (ℋ₁ ⊗[ℂ] ℋ₂)) :=
    map_nonneg_of_nonneg A B hA hB
  apply (eA.toBasis.tensorProduct eB.toBasis).ext
  intro ⟨i, j⟩
  have hA_eig : A (eA i) = (algebraMap ℝ ℂ (eigA i)) • eA i := by
    rw [RCLike.algebraMap_eq_ofReal]
    exact hA_pos.isSymmetric.apply_eigenvectorBasis _ i
  have hB_eig : B (eB j) = (algebraMap ℝ ℂ (eigB j)) • eB j := by
    rw [RCLike.algebraMap_eq_ofReal]
    exact hB_pos.isSymmetric.apply_eigenvectorBasis _ j
  have hA_spec : eigA i ∈ spectrum ℝ A := by
    rw [← spectrum.preimage_algebraMap ℂ (R := ℝ), Set.mem_preimage]
    exact (hA_pos.isSymmetric.hasEigenvalue_eigenvalues _ i).mem_spectrum
  have hB_spec : eigB j ∈ spectrum ℝ B := by
    rw [← spectrum.preimage_algebraMap ℂ (R := ℝ), Set.mem_preimage]
    exact (hB_pos.isSymmetric.hasEigenvalue_eigenvalues _ j).mem_spectrum
  have hAB_eig : TensorProduct.map A B (eA i ⊗ₜ eB j) =
      (algebraMap ℝ ℂ (eigA i * eigB j)) • (eA i ⊗ₜ eB j) := by
    rw [map_tmul, hA_eig, hB_eig, TensorProduct.smul_tmul_smul, ← map_mul]
  have hAB_spec : eigA i * eigB j ∈ spectrum ℝ (TensorProduct.map A B) := by
    rw [← spectrum.preimage_algebraMap ℂ (R := ℝ), Set.mem_preimage]
    exact (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hAB_eig, by
        intro hzero
        exact (eA.toBasis.tensorProduct eB.toBasis).ne_zero (i, j)
          ((eA.toBasis.tensorProduct_apply eB.toBasis i j).trans hzero)⟩).mem_spectrum
  rw [eA.toBasis.tensorProduct_apply]
  change CFC.rpow (TensorProduct.map A B) p (eA i ⊗ₜ eB j) =
    TensorProduct.map (CFC.rpow A p) (CFC.rpow B p) (eA i ⊗ₜ eB j)
  rw [rpow_apply_eigenvector_linear _ hAB p _ _ hAB_eig hAB_spec, map_tmul,
    rpow_apply_eigenvector_linear A hA p _ _ hA_eig hA_spec,
    rpow_apply_eigenvector_linear B hB p _ _ hB_eig hB_spec,
    TensorProduct.smul_tmul_smul, ← map_mul,
    Real.mul_rpow (hA_pos.nonneg_eigenvalues rfl i) (hB_pos.nonneg_eigenvalues rfl j)]

/-- `CFC.rpow` commutes with `A ↦ A ⊗ 1` on positive linear endomorphisms. -/
theorem rpow_rTensor (A : L ℋ₁) (p : ℝ) (hA : 0 ≤ A) :
    CFC.rpow (rTensorStarAlgHom (ℋ₂ := ℋ₂) A) p =
      rTensorStarAlgHom (CFC.rpow A p) := by
  have h := rpow_tensorProduct (ℋ₂ := ℋ₂) A 1 p hA zero_le_one
  have hone : CFC.rpow (1 : L ℋ₂) p = 1 := by rw [CFC.rpow_eq_pow, CFC.one_rpow]
  rw [hone] at h
  exact h

/-- `CFC.rpow` commutes with `B ↦ 1 ⊗ B` on positive linear endomorphisms. -/
theorem rpow_lTensor (B : L ℋ₂) (p : ℝ) (hB : 0 ≤ B) :
    CFC.rpow (lTensorStarAlgHom (ℋ₁ := ℋ₁) B) p =
      lTensorStarAlgHom (CFC.rpow B p) := by
  have h := rpow_tensorProduct (ℋ₁ := ℋ₁) 1 B p zero_le_one hB
  have hone : CFC.rpow (1 : L ℋ₁) p = 1 := by rw [CFC.rpow_eq_pow, CFC.one_rpow]
  rw [hone] at h
  exact h

end LinearMaps

end TensorCFC
