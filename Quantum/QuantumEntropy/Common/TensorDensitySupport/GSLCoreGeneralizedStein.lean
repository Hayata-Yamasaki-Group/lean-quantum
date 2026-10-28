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
import Quantum.QuantumEntropy.Common.TensorDensitySupport.GSLCore
import Quantum.QuantumMechanics.Channel.Basic

/-! # Tensor products of density operators and their supports

Density and support identities for tensor products.
-/

open QuantumState TensorProduct
open SandwichedRenyiRelativeEntropy
open scoped ComplexOrder

universe u v

namespace QuantumEntropy.TensorDensitySupport

lemma tensorMap_isSymmetric
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (A : L E) (B : L F) (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    (TensorProduct.map A B).IsSymmetric := by
  intro x y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul c d =>
          rw [TensorProduct.map_tmul, TensorProduct.map_tmul,
            TensorProduct.inner_tmul, TensorProduct.inner_tmul, hA a c, hB b d]
      | add y₁ y₂ h₁ h₂ =>
          rw [map_add, inner_add_right, inner_add_right, h₁, h₂]
  | add x₁ x₂ h₁ h₂ =>
      rw [map_add, inner_add_left, inner_add_left, h₁, h₂]

theorem tensorMap_ne_zero_iff
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (A : L E) (B : L F) :
    (TensorProduct.map A B : L (E ⊗[ℂ] F)) ≠ 0 ↔ A ≠ 0 ∧ B ≠ 0 := by
  constructor
  · intro h
    constructor
    · intro hA
      apply h
      simp [hA]
    · intro hB
      apply h
      simp [hB]
  · rintro ⟨hA, hB⟩ hmap
    have hle : LinearMap.range (TensorProduct.map A B) ≤
        LinearMap.range (TensorProduct.map (0 : L E) (0 : L F)) := by
      rw [hmap]
      simp
    have hArange := range_tensorMap_left_of_le hle hB
    apply hA
    ext x
    have hx : A x ∈ LinearMap.range A := ⟨x, rfl⟩
    simpa using hArange hx

lemma density_mul_ne_zero_of_supportLE
    {E : Type u} [Qudit E] [Nontrivial E]
    {rho sigma : L E} (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (hsupp : SupportLE rho sigma) : rho * sigma ≠ 0 := by
  have hrho_nonneg : (0 : L E) ≤ rho :=
    (LinearMap.nonneg_iff_isPositive rho).mpr hrho.1
  have hsigma_nonneg : (0 : L E) ≤ sigma :=
    (LinearMap.nonneg_iff_isPositive sigma).mpr hsigma.1
  have hrho_sa : IsSelfAdjoint rho := IsSelfAdjoint.of_nonneg hrho_nonneg
  have hsigma_sa : IsSelfAdjoint sigma := IsSelfAdjoint.of_nonneg hsigma_nonneg
  have hrho_ne : rho ≠ 0 := density_ne_zero hrho
  intro hmul
  have hrev : sigma * rho = 0 := by
    have hstar := congrArg star hmul
    simpa [star_mul, hrho_sa.star_eq, hsigma_sa.star_eq] using hstar
  have hsquare : rho * rho = 0 := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.zero_apply]
    have hx_sigma : sigma (rho x) = 0 := by
      have hx := LinearMap.congr_fun hrev x
      simpa using hx
    exact hsupp hx_sigma
  apply hrho_ne
  apply (CStarRing.star_mul_self_eq_zero_iff rho).mp
  simpa [hrho_sa.star_eq] using hsquare

theorem starProjection_tensorMap
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (A : L E) (B : L F) :
    (LinearMap.range (TensorProduct.map A B)).starProjection.toLinearMap =
      TensorProduct.map
        (LinearMap.range A).starProjection.toLinearMap
        (LinearMap.range B).starProjection.toLinearMap := by
  let P : L E := (LinearMap.range A).starProjection.toLinearMap
  let Q : L F := (LinearMap.range B).starProjection.toLinearMap
  let R : L (E ⊗[ℂ] F) := TensorProduct.map P Q
  have hP := Submodule.isSymmetricProjection_starProjection (LinearMap.range A)
  have hQ := Submodule.isSymmetricProjection_starProjection (LinearMap.range B)
  have hRid : IsIdempotentElem R := by
    change IsIdempotentElem (TensorProduct.map P Q)
    rw [IsIdempotentElem, ← TensorProduct.map_mul]
    change TensorProduct.map (P * P) (Q * Q) = TensorProduct.map P Q
    rw [hP.1, hQ.1]
  have hRs : R.IsSymmetric :=
    tensorMap_isSymmetric P Q hP.2 hQ.2
  have hRproj : R.IsSymmetricProjection := ⟨hRid, hRs⟩
  have hRP : LinearMap.range P = LinearMap.range A := by
    exact Submodule.range_starProjection (LinearMap.range A)
  have hRQ : LinearMap.range Q = LinearMap.range B := by
    exact Submodule.range_starProjection (LinearMap.range B)
  have hRrange : LinearMap.range R =
      LinearMap.range (TensorProduct.map A B) := by
    apply le_antisymm
    · exact TensorProduct.range_map_mono (by rw [hRP]) (by rw [hRQ])
    · exact TensorProduct.range_map_mono (by rw [hRP]) (by rw [hRQ])
  obtain ⟨_, hRstar⟩ :=
    LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hRproj
  change (LinearMap.range (TensorProduct.map A B)).starProjection.toLinearMap = R
  rw [hRstar]
  exact congrArg (fun S : Submodule ℂ (E ⊗[ℂ] F) =>
    S.starProjection.toLinearMap) hRrange.symm

end QuantumEntropy.TensorDensitySupport
