/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.Common.Support
import Quantum.QuantumEntropy.TensorCFCUmegaki
import Quantum.QuantumEntropy.TensorCFC
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
import Quantum.QuantumMechanics.Channel.Basic

/-! # Tensor products of density operators and their supports

Density and support identities for tensor products.
-/

open QuantumState TensorProduct
open SandwichedRenyiRelativeEntropy
open scoped ComplexOrder

universe u v

namespace QuantumEntropy.TensorDensitySupport

lemma supportLE_iff_range_le
    {E : Type u} [Qudit E] [Nontrivial E] {A B : L E}
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    SupportLE A B ↔ LinearMap.range A ≤ LinearMap.range B := by
  have hAs : A.IsSymmetric :=
    ((LinearMap.nonneg_iff_isPositive A).mp hA).isSymmetric
  have hBs : B.IsSymmetric :=
    ((LinearMap.nonneg_iff_isPositive B).mp hB).isSymmetric
  constructor
  · intro h
    have ho := Submodule.orthogonal_le h
    simpa [LinearMap.orthogonal_ker, hAs.adjoint_eq, hBs.adjoint_eq] using ho
  · exact LinearMap.ker_le_ker_of_range hAs hBs

private noncomputable def tensorRightSliceDual
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (f : Module.Dual ℂ F) : E ⊗[ℂ] F →ₗ[ℂ] E :=
  (TensorProduct.lid ℂ E).toLinearMap.comp
    ((TensorProduct.map f LinearMap.id).comp
      (TensorProduct.comm ℂ E F).toLinearMap)

private noncomputable def tensorLeftSliceDual
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (f : Module.Dual ℂ E) : E ⊗[ℂ] F →ₗ[ℂ] F :=
  (TensorProduct.lid ℂ F).toLinearMap.comp
    (TensorProduct.map f LinearMap.id)

private lemma tensorRightSliceDual_map_mem_range
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (C : L E) (D : L F) (f : Module.Dual ℂ F) (z : E ⊗[ℂ] F) :
    tensorRightSliceDual f (TensorProduct.map C D z) ∈ LinearMap.range C := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      refine ⟨f (D y) • x, ?_⟩
      simp [tensorRightSliceDual]
  | add z w hz hw =>
      simpa using (LinearMap.range C).add_mem hz hw

private lemma tensorLeftSliceDual_map_mem_range
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (C : L E) (D : L F) (f : Module.Dual ℂ E) (z : E ⊗[ℂ] F) :
    tensorLeftSliceDual f (TensorProduct.map C D z) ∈ LinearMap.range D := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      refine ⟨f (C x) • y, ?_⟩
      simp [tensorLeftSliceDual]
  | add z w hz hw =>
      simpa using (LinearMap.range D).add_mem hz hw

lemma range_tensorMap_left_of_le
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    {A C : L E} {B D : L F}
    (h : LinearMap.range (TensorProduct.map A B) ≤
      LinearMap.range (TensorProduct.map C D))
    (hB : B ≠ 0) : LinearMap.range A ≤ LinearMap.range C := by
  intro x hx
  obtain ⟨a, rfl⟩ := hx
  have hex : ∃ b, B b ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hB
    ext b
    exact hall b
  obtain ⟨b, hb⟩ := hex
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hb
  have htensor : A a ⊗ₜ[ℂ] B b ∈
      LinearMap.range (TensorProduct.map A B) :=
    ⟨a ⊗ₜ[ℂ] b, rfl⟩
  obtain ⟨z, hz⟩ := h htensor
  have hslice := tensorRightSliceDual_map_mem_range C D f z
  rw [hz] at hslice
  simpa [tensorRightSliceDual, hf] using hslice

lemma range_tensorMap_right_of_le
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    {A C : L E} {B D : L F}
    (h : LinearMap.range (TensorProduct.map A B) ≤
      LinearMap.range (TensorProduct.map C D))
    (hA : A ≠ 0) : LinearMap.range B ≤ LinearMap.range D := by
  intro y hy
  obtain ⟨b, rfl⟩ := hy
  have hex : ∃ a, A a ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hA
    ext a
    exact hall a
  obtain ⟨a, ha⟩ := hex
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ ha
  have htensor : A a ⊗ₜ[ℂ] B b ∈
      LinearMap.range (TensorProduct.map A B) :=
    ⟨a ⊗ₜ[ℂ] b, rfl⟩
  obtain ⟨z, hz⟩ := h htensor
  have hslice := tensorLeftSliceDual_map_mem_range C D f z
  rw [hz] at hslice
  simpa [tensorLeftSliceDual, hf] using hslice

lemma density_ne_zero
    {E : Type u} [Qudit E] {rho : L E} (hrho : IsDensity rho) : rho ≠ 0 := by
  intro h
  have ht := hrho.2
  rw [h, map_zero] at ht
  exact zero_ne_one ht

lemma tensorMap_nonneg
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (A : L E) (B : L F) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ (TensorProduct.map A B : L (E ⊗[ℂ] F)) := by
  set a := CFC.sqrt A
  set b := CFC.sqrt B
  have ha := CFC.sqrt_nonneg A
  have hb := CFC.sqrt_nonneg B
  have hstar : star (TensorProduct.map a b : L (E ⊗[ℂ] F)) =
      TensorProduct.map (star a) (star b) := by
    simp only [LinearMap.star_eq_adjoint, TensorProduct.adjoint_map]
  rw [show TensorProduct.map A B =
      star (TensorProduct.map a b) * TensorProduct.map a b by
    rw [hstar, (IsSelfAdjoint.of_nonneg ha).star_eq,
      (IsSelfAdjoint.of_nonneg hb).star_eq, ← TensorProduct.map_mul,
      CFC.sqrt_mul_sqrt_self A hA, CFC.sqrt_mul_sqrt_self B hB]]
  exact star_mul_self_nonneg _

theorem isDensity_tensorMap
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (rho : L E) (sigma : L F) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    IsDensity (TensorProduct.map rho sigma : L (E ⊗[ℂ] F)) := by
  constructor
  · exact (LinearMap.nonneg_iff_isPositive _).mp
      (tensorMap_nonneg rho sigma
        ((LinearMap.nonneg_iff_isPositive _).mpr hrho.1)
        ((LinearMap.nonneg_iff_isPositive _).mpr hsigma.1))
  · rw [LinearMap.trace_tensorProduct', hrho.2, hsigma.2, one_mul]

theorem supportLE_tensorMap_iff
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    [Nontrivial E] [Nontrivial F] [Nontrivial (E ⊗[ℂ] F)]
    (rho₁ sigma₁ : L E) (rho₂ sigma₂ : L F)
    (hrho₁ : IsDensity rho₁) (hsigma₁ : IsDensity sigma₁)
    (hrho₂ : IsDensity rho₂) (hsigma₂ : IsDensity sigma₂) :
    SupportLE (TensorProduct.map rho₁ rho₂) (TensorProduct.map sigma₁ sigma₂) ↔
      SupportLE rho₁ sigma₁ ∧ SupportLE rho₂ sigma₂ := by
  have hr₁ : 0 ≤ rho₁ := (LinearMap.nonneg_iff_isPositive _).mpr hrho₁.1
  have hs₁ : 0 ≤ sigma₁ := (LinearMap.nonneg_iff_isPositive _).mpr hsigma₁.1
  have hr₂ : 0 ≤ rho₂ := (LinearMap.nonneg_iff_isPositive _).mpr hrho₂.1
  have hs₂ : 0 ≤ sigma₂ := (LinearMap.nonneg_iff_isPositive _).mpr hsigma₂.1
  have hrt : 0 ≤ (TensorProduct.map rho₁ rho₂ : L (E ⊗[ℂ] F)) := by
    set a := CFC.sqrt rho₁
    set b := CFC.sqrt rho₂
    have ha := CFC.sqrt_nonneg rho₁
    have hb := CFC.sqrt_nonneg rho₂
    have hstar : star (TensorProduct.map a b : L (E ⊗[ℂ] F)) =
        TensorProduct.map (star a) (star b) := by
      simp only [LinearMap.star_eq_adjoint, TensorProduct.adjoint_map]
    rw [show TensorProduct.map rho₁ rho₂ =
        star (TensorProduct.map a b) * TensorProduct.map a b by
      rw [hstar, (IsSelfAdjoint.of_nonneg ha).star_eq,
        (IsSelfAdjoint.of_nonneg hb).star_eq, ← TensorProduct.map_mul,
        CFC.sqrt_mul_sqrt_self rho₁ hr₁,
        CFC.sqrt_mul_sqrt_self rho₂ hr₂]]
    exact star_mul_self_nonneg _
  have hst : 0 ≤ (TensorProduct.map sigma₁ sigma₂ : L (E ⊗[ℂ] F)) := by
    set a := CFC.sqrt sigma₁
    set b := CFC.sqrt sigma₂
    have ha := CFC.sqrt_nonneg sigma₁
    have hb := CFC.sqrt_nonneg sigma₂
    have hstar : star (TensorProduct.map a b : L (E ⊗[ℂ] F)) =
        TensorProduct.map (star a) (star b) := by
      simp only [LinearMap.star_eq_adjoint, TensorProduct.adjoint_map]
    rw [show TensorProduct.map sigma₁ sigma₂ =
        star (TensorProduct.map a b) * TensorProduct.map a b by
      rw [hstar, (IsSelfAdjoint.of_nonneg ha).star_eq,
        (IsSelfAdjoint.of_nonneg hb).star_eq, ← TensorProduct.map_mul,
        CFC.sqrt_mul_sqrt_self sigma₁ hs₁,
        CFC.sqrt_mul_sqrt_self sigma₂ hs₂]]
    exact star_mul_self_nonneg _
  rw [supportLE_iff_range_le hrt hst,
    supportLE_iff_range_le hr₁ hs₁, supportLE_iff_range_le hr₂ hs₂]
  constructor
  · intro h
    exact ⟨range_tensorMap_left_of_le h (density_ne_zero hrho₂),
      range_tensorMap_right_of_le h (density_ne_zero hrho₁)⟩
  · rintro ⟨h₁, h₂⟩
    exact TensorProduct.range_map_mono h₁ h₂

end QuantumEntropy.TensorDensitySupport
