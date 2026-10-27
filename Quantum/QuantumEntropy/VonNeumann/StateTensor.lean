/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.VonNeumann.Basic
import Quantum.QuantumEntropy.VonNeumann.TensorLog
import Quantum.QuantumEntropy.HaarUnitaryMeasureCore
import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneDefinitions

/-!
# Entropy expansion of `D(ρ‖σ₁ ⊗ σ₂)`

Partial-trace duality identities
`Tr(ρ (X ⊗ 1)) = Tr(Tr₂(ρ) X)` and `Tr(ρ (1 ⊗ Y)) = Tr(Tr₁(ρ) Y)`,
and the entropy expansion of the Umegaki relative entropy against a
tensor-product second argument:

`D(ρ ‖ σ₁ ⊗ σ₂) = -S(ρ) - Re Tr(ρ₁ log σ₁) - Re Tr(ρ₂ log σ₂)`

for a state `ρ` (`Tr ρ = 1`) and positive-definite `σ₁, σ₂`, where
`ρ₁, ρ₂` are the marginals of `ρ`.  Specializing `σ₁, σ₂` to the marginals
gives the mutual-information form
`D(ρ ‖ ρ₁ ⊗ ρ₂) = S(ρ₁) + S(ρ₂) - S(ρ)`.
-/

namespace VonNeumann

open QuantumState QuantumChannel TensorProduct
open GeneralizedPerspectiveFunction SandwichedRenyiRelativeEntropy

universe u v

/-- A tensor product of nontrivial finite-dimensional spaces is nontrivial. -/
instance instNontrivialTensorProduct
    {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
    [Nontrivial ℋ₁] [Nontrivial ℋ₂] : Nontrivial (ℋ₁ ⊗[ℂ] ℋ₂) :=
  Module.nontrivial_of_finrank_pos (R := ℂ) (by
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos)

section LinearMapCarrier

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]

/-- The left partial trace of an elementary tensor endomorphism. -/
lemma traceOutLeft_map (P : L ℋ₁) (Q : L ℋ₂) :
    QuantumChannel.traceOutLeft (TensorProduct.map P Q) = Tr P • Q := by
  rw [← endomorphismTensorEquiv_symm_tmul, traceOutLeft_tmul]

/-- Swap conjugation exchanges the factors of an elementary tensor
endomorphism. -/
private lemma conjugateEnd_comm_map (P : L ℋ₁) (Q : L ℋ₂) :
    conjugateEnd (TensorProduct.comm ℂ ℋ₁ ℋ₂) (TensorProduct.map P Q) =
      TensorProduct.map Q P := by
  apply TensorProduct.ext'
  intro y x
  simp [conjugateEnd]

/-- The right partial trace of an elementary tensor endomorphism. -/
lemma traceOutRight_map (P : L ℋ₁) (Q : L ℋ₂) :
    QuantumChannel.traceOutRight (TensorProduct.map P Q) = Tr Q • P := by
  unfold QuantumChannel.traceOutRight
  rw [LinearMap.comp_apply, conjugateEnd_comm_map, traceOutLeft_map]

/-- **Partial-trace duality (right)**:
`Tr(Z ∘ (X ⊗ 1)) = Tr(Tr₂(Z) ∘ X)`. -/
private lemma trace_comp_map_id (Z : L (ℋ₁ ⊗[ℂ] ℋ₂)) (X : L ℋ₁) :
    Tr (Z ∘ₗ TensorProduct.map X (LinearMap.id (M := ℋ₂))) =
      Tr (QuantumChannel.traceOutRight (ℋ₂ := ℋ₁) (ℋ₃ := ℋ₂) Z ∘ₗ X) := by
  obtain ⟨W, rfl⟩ :=
    (endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).symm.surjective Z
  induction W using TensorProduct.induction_on with
  | zero => simp
  | tmul P Q =>
      rw [endomorphismTensorEquiv_symm_tmul, ← TensorProduct.map_comp, LinearMap.comp_id,
        LinearMap.trace_tensorProduct', traceOutRight_map, LinearMap.smul_comp,
        map_smul, smul_eq_mul]
      ring
  | add W₁ W₂ h₁ h₂ =>
      rw [map_add, LinearMap.add_comp, map_add, h₁, h₂, map_add, LinearMap.add_comp,
        map_add]

/-- **Partial-trace duality (left)**:
`Tr(Z ∘ (1 ⊗ Y)) = Tr(Tr₁(Z) ∘ Y)`. -/
private lemma trace_comp_id_map (Z : L (ℋ₁ ⊗[ℂ] ℋ₂)) (Y : L ℋ₂) :
    Tr (Z ∘ₗ TensorProduct.map (LinearMap.id (M := ℋ₁)) Y) =
      Tr (QuantumChannel.traceOutLeft (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) Z ∘ₗ Y) := by
  obtain ⟨W, rfl⟩ :=
    (endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).symm.surjective Z
  induction W using TensorProduct.induction_on with
  | zero => simp
  | tmul P Q =>
      rw [endomorphismTensorEquiv_symm_tmul, ← TensorProduct.map_comp, LinearMap.comp_id,
        LinearMap.trace_tensorProduct', traceOutLeft_map, LinearMap.smul_comp,
        map_smul, smul_eq_mul]
  | add W₁ W₂ h₁ h₂ =>
      rw [map_add, LinearMap.add_comp, map_add, h₁, h₂, map_add, LinearMap.add_comp,
        map_add]

end LinearMapCarrier

section LinearMapEntropy

variable {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂]
variable [Nontrivial ℋ₁] [Nontrivial ℋ₂]

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- Partial-trace duality (right):
`Tr(ρ · (X ⊗ 1)) = Tr(Tr₂(ρ) · X)`. -/
private lemma trace_mul_tensorMap_one (ρ : L (ℋ₁ ⊗[ℂ] ℋ₂)) (X : L ℋ₁) :
    Tr (ρ * TensorProduct.map X 1) =
      Tr (QuantumChannel.traceOutRight ρ * X) := by
  exact trace_comp_map_id ρ X

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- Partial-trace duality (left):
`Tr(ρ · (1 ⊗ Y)) = Tr(Tr₁(ρ) · Y)`. -/
private lemma trace_mul_one_tensorMap (ρ : L (ℋ₁ ⊗[ℂ] ℋ₂)) (Y : L ℋ₂) :
    Tr (ρ * TensorProduct.map 1 Y) =
      Tr (QuantumChannel.traceOutLeft ρ * Y) := by
  exact trace_comp_id_map ρ Y

/-- The CFC logarithm of a tensor product of positive-definite linear maps. -/
private lemma log_tensorMap (σ₁ : L ℋ₁) (σ₂ : L ℋ₂)
    (hσ₁ : σ₁ ∈ pdSetLM) (hσ₂ : σ₂ ∈ pdSetLM) :
    CFC.log (TensorProduct.map (σ₁.toContinuousLinearMap : L ℋ₁)
        (σ₂.toContinuousLinearMap : L ℋ₂)).toContinuousLinearMap =
      (TensorProduct.map ((CFC.log σ₁.toContinuousLinearMap : B ℋ₁) : L ℋ₁)
          1).toContinuousLinearMap +
        (TensorProduct.map 1
          ((CFC.log σ₂.toContinuousLinearMap : B ℋ₂) : L ℋ₂)).toContinuousLinearMap := by
  change σ₁.toContinuousLinearMap ∈ pdSet at hσ₁
  change σ₂.toContinuousLinearMap ∈ pdSet at hσ₂
  exact TensorCFC.log_tensorProduct (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)
    σ₁.toContinuousLinearMap σ₂.toContinuousLinearMap hσ₁ hσ₂

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- Taking the trace commutes with returning the lifted CFC product to `L`. -/
private lemma trace_mul_log_toContinuousLinearMap (A : L ℋ₁) :
    Tr (A * ((CFC.log A.toContinuousLinearMap : B ℋ₁) : L ℋ₁)) =
      Tr (((A.toContinuousLinearMap * CFC.log A.toContinuousLinearMap : B ℋ₁) :
        L ℋ₁)) := by
  congr 1

/-- **Entropy expansion of the Umegaki relative entropy against a tensor
second argument**: for a state `ρ` and positive-definite
`σ₁, σ₂`,
`D(ρ ‖ σ₁ ⊗ σ₂) = -S(ρ) - Re Tr(ρ₁ log σ₁) - Re Tr(ρ₂ log σ₂)`,
with `ρ₁, ρ₂` the marginals of `ρ`. -/
theorem umegakiNorm_state_tensor (ρ : L (ℋ₁ ⊗[ℂ] ℋ₂)) (σ₁ : L ℋ₁) (σ₂ : L ℋ₂)
    (hσ₁ : σ₁ ∈ pdSetLM) (hσ₂ : σ₂ ∈ pdSetLM)
    (hTr : Tr ρ = 1) :
    umegakiNorm ρ (TensorProduct.map σ₁ σ₂) =
      -vonNeumannEntropy ρ
        - (Tr (QuantumChannel.traceOutRight ρ *
          ((CFC.log σ₁.toContinuousLinearMap : B ℋ₁) : L ℋ₁))).re
        - (Tr (QuantumChannel.traceOutLeft ρ *
          ((CFC.log σ₂.toContinuousLinearMap : B ℋ₂) : L ℋ₂))).re := by
  rw [SandwichedRenyiRelativeEntropy.umegakiNorm_eq_toContinuousLinearMap]
  have hσ₁_lm : (σ₁.toContinuousLinearMap : L ℋ₁) = σ₁ := by
    ext x
    rfl
  have hσ₂_lm : (σ₂.toContinuousLinearMap : L ℋ₂) = σ₂ := by
    ext x
    rfl
  have hmap : (TensorProduct.map σ₁ σ₂).toContinuousLinearMap =
      (TensorProduct.map (σ₁.toContinuousLinearMap : L ℋ₁)
        (σ₂.toContinuousLinearMap : L ℋ₂)).toContinuousLinearMap := by
    rw [hσ₁_lm, hσ₂_lm]
  rw [hTr, Complex.one_re, div_one, hmap,
    log_tensorMap σ₁ σ₂ hσ₁ hσ₂]
  rw [mul_sub, mul_add]
  rw [show ((ρ.toContinuousLinearMap * CFC.log ρ.toContinuousLinearMap -
        (ρ.toContinuousLinearMap *
            (TensorProduct.map ((CFC.log σ₁.toContinuousLinearMap : B ℋ₁) : L ℋ₁)
              1).toContinuousLinearMap +
          ρ.toContinuousLinearMap *
            (TensorProduct.map 1
              ((CFC.log σ₂.toContinuousLinearMap : B ℋ₂) : L ℋ₂)).toContinuousLinearMap) :
        B (ℋ₁ ⊗[ℂ] ℋ₂)) : L (ℋ₁ ⊗[ℂ] ℋ₂)) =
      (ρ * ((CFC.log ρ.toContinuousLinearMap : B (ℋ₁ ⊗[ℂ] ℋ₂)) :
          L (ℋ₁ ⊗[ℂ] ℋ₂))) -
        (ρ * TensorProduct.map ((CFC.log σ₁.toContinuousLinearMap : B ℋ₁) : L ℋ₁) 1 +
          ρ * TensorProduct.map 1
            ((CFC.log σ₂.toContinuousLinearMap : B ℋ₂) : L ℋ₂)) from by
      ext x
      rfl]
  rw [map_sub, map_add, Complex.sub_re, Complex.add_re]
  rw [trace_mul_tensorMap_one ρ
      ((CFC.log σ₁.toContinuousLinearMap : B ℋ₁) : L ℋ₁),
    trace_mul_one_tensorMap ρ
      ((CFC.log σ₂.toContinuousLinearMap : B ℋ₂) : L ℋ₂)]
  rw [vonNeumannEntropy_def]
  rw [trace_mul_log_toContinuousLinearMap ρ]
  ring

/-- **Mutual-information form** of the entropy expansion: for a state `ρ`
whose marginals are positive definite,
`D(ρ ‖ ρ₁ ⊗ ρ₂) = S(ρ₁) + S(ρ₂) - S(ρ)`. -/
theorem umegakiNorm_state_tensor_marginals (ρ : L (ℋ₁ ⊗[ℂ] ℋ₂))
    (h₁ : QuantumChannel.traceOutRight ρ ∈ pdSetLM)
    (h₂ : QuantumChannel.traceOutLeft ρ ∈ pdSetLM)
    (hTr : Tr ρ = 1) :
    umegakiNorm ρ
        (TensorProduct.map (QuantumChannel.traceOutRight ρ)
          (QuantumChannel.traceOutLeft ρ)) =
      vonNeumannEntropy (QuantumChannel.traceOutRight ρ) +
        vonNeumannEntropy (QuantumChannel.traceOutLeft ρ) -
          vonNeumannEntropy ρ := by
  rw [umegakiNorm_state_tensor ρ _ _ h₁ h₂ hTr]
  simp_rw [vonNeumannEntropy_def]
  rw [trace_mul_log_toContinuousLinearMap (QuantumChannel.traceOutRight ρ),
    trace_mul_log_toContinuousLinearMap (QuantumChannel.traceOutLeft ρ)]
  ring

end LinearMapEntropy

end VonNeumann
