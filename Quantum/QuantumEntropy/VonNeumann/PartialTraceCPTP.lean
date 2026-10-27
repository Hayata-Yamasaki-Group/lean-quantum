/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.Channel.ChoiKraus

/-!
# The left partial trace as a CPTP channel

`traceOutLeft : T (ℋ₁ ⊗[ℂ] ℋ₂) ℋ₂` is bundled as a `CPTP` channel.

* Complete positivity: `traceOutLeft` factors through `traceOutRight` via the
  swap conjugation `conjugateEnd (TensorProduct.comm ℂ ℋ₁ ℋ₂)`, which is a
  single-Kraus-operator channel (the swap is a unitary); complete positivity
  of the composite follows from `cp_traceOutRight` and
  `isCompletelyPositive_comp`.
* Trace preservation: proved on the generators
  `endomorphismTensorEquiv.symm (X ⊗ₜ Y)` using `traceOutLeft_tmul` and
  `LinearMap.trace_tensorProduct'`.
-/

namespace QuantumChannel

open QuantumState TensorProduct

universe u v

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]

/-- The adjoint of the tensor swap is its inverse (the swap is unitary). -/
private lemma adjoint_comm_toLinearMap :
    LinearMap.adjoint
        ((TensorProduct.comm ℂ ℋ₁ ℋ₂ : (ℋ₁ ⊗[ℂ] ℋ₂) ≃ₗ[ℂ] (ℋ₂ ⊗[ℂ] ℋ₁)) :
          (ℋ₁ ⊗[ℂ] ℋ₂) →ₗ[ℂ] (ℋ₂ ⊗[ℂ] ℋ₁)) =
      ((TensorProduct.comm ℂ ℋ₁ ℋ₂).symm : (ℋ₂ ⊗[ℂ] ℋ₁) →ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂)) := by
  simpa [TensorProduct.toLinearEquiv_commIsometry] using
    LinearIsometryEquiv.adjoint_toLinearMap_eq_symm (TensorProduct.commIsometry ℂ ℋ₁ ℋ₂)

/-- Conjugation by the tensor swap is a single-operator Kraus channel. -/
private theorem krausRep_conjugateEnd_comm :
    KrausRep (ℋ₁ := ℋ₁ ⊗[ℂ] ℋ₂) (ℋ₂ := ℋ₂ ⊗[ℂ] ℋ₁)
      (conjugateEnd (TensorProduct.comm ℂ ℋ₁ ℋ₂)) (Fin 1) := by
  refine ⟨fun _ =>
    ((TensorProduct.comm ℂ ℋ₁ ℋ₂ : (ℋ₁ ⊗[ℂ] ℋ₂) ≃ₗ[ℂ] (ℋ₂ ⊗[ℂ] ℋ₁)) :
      (ℋ₁ ⊗[ℂ] ℋ₂) →ₗ[ℂ] (ℋ₂ ⊗[ℂ] ℋ₁)), fun X => ?_⟩
  rw [Fin.sum_univ_one, adjoint_comm_toLinearMap]
  rfl

/-- Swapping twice is the identity on endomorphisms. -/
private lemma conjugateEnd_comm_conjugateEnd_comm (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) :
    conjugateEnd (TensorProduct.comm ℂ ℋ₂ ℋ₁)
      (conjugateEnd (TensorProduct.comm ℂ ℋ₁ ℋ₂) X) = X := by
  have hswap : (TensorProduct.comm ℂ ℋ₂ ℋ₁ : (ℋ₂ ⊗[ℂ] ℋ₁) ≃ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂)) =
      (TensorProduct.comm ℂ ℋ₁ ℋ₂).symm := rfl
  apply LinearMap.ext
  intro z
  simp only [conjugateEnd, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    LinearEquiv.coe_coe, hswap, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply]

/-- `traceOutLeft` factors through `traceOutRight` and the swap conjugation. -/
private lemma traceOutLeft_eq_traceOutRight_comp :
    (traceOutLeft : T (ℋ₁ ⊗[ℂ] ℋ₂) ℋ₂) =
      (traceOutRight (ℋ₂ := ℋ₂) (ℋ₃ := ℋ₁)).comp
        (conjugateEnd (TensorProduct.comm ℂ ℋ₁ ℋ₂)) := by
  apply LinearMap.ext
  intro X
  change traceOutLeft X =
    traceOutRight (conjugateEnd (TensorProduct.comm ℂ ℋ₁ ℋ₂) X)
  unfold traceOutRight
  rw [LinearMap.comp_apply, conjugateEnd_comm_conjugateEnd_comm]

/-- **Complete positivity of the left partial trace**. -/
private theorem cp_traceOutLeft :
    IsCompletelyPositive (traceOutLeft : T (ℋ₁ ⊗[ℂ] ℋ₂) ℋ₂) := by
  rw [traceOutLeft_eq_traceOutRight_comp]
  exact isCompletelyPositive_comp
    (conjugateEnd (TensorProduct.comm ℂ ℋ₁ ℋ₂))
    (traceOutRight (ℋ₂ := ℋ₂) (ℋ₃ := ℋ₁))
    (cp_of_krausRep _ krausRep_conjugateEnd_comm)
    (cp_traceOutRight (stdOrthonormalBasis ℂ ℋ₁))

/-- **Trace preservation of the left partial trace**:
`Tr (traceOutLeft X) = Tr X`. -/
lemma trace_traceOutLeft (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) :
    Tr (traceOutLeft X) = Tr X := by
  obtain ⟨W, rfl⟩ :=
    (endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).symm.surjective X
  induction W using TensorProduct.induction_on with
  | zero => simp
  | tmul P Q =>
      rw [traceOutLeft_tmul, endomorphismTensorEquiv_symm_tmul, map_smul, smul_eq_mul,
        LinearMap.trace_tensorProduct']
  | add W₁ W₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, map_add, h₁, h₂]

/-- **The left partial trace as a CPTP channel**
`CPTP (ℋ₁ ⊗[ℂ] ℋ₂) ℋ₂`. -/
noncomputable def CPTP.traceOutLeft (ℋ₁ : Type u) (ℋ₂ : Type v)
    [Qudit ℋ₁] [Qudit ℋ₂] :
    CPTP (ℋ₁ ⊗[ℂ] ℋ₂) ℋ₂ := by
  let Ψ : CompletelyPositiveMap (L (ℋ₁ ⊗[ℂ] ℋ₂)) (L ℋ₂) :=
    { (QuantumChannel.traceOutLeft : T (ℋ₁ ⊗[ℂ] ℋ₂) ℋ₂) with
      map_cstarMatrix_nonneg' := by
        intro k M hM
        exact (isCompletelyPositive_iff_cstarMatrix_nonneg
          (QuantumChannel.traceOutLeft : T (ℋ₁ ⊗[ℂ] ℋ₂) ℋ₂)).mp
          (cp_traceOutLeft (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)) k M hM }
  exact
    { Ψ with
      trace_map := by
        intro ρ
        exact (trace_traceOutLeft ρ).symm }

/-- Action of the CPTP-bundled left partial trace. -/
@[simp] lemma CPTP.traceOutLeft_toFun (ρ : L (ℋ₁ ⊗[ℂ] ℋ₂)) :
    (CPTP.traceOutLeft ℋ₁ ℋ₂).toFun ρ =
      QuantumChannel.traceOutLeft ρ :=
  rfl

end QuantumChannel
