/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.ComplementaryCrossGram.GSLCore
import Quantum.QuantumModel.SSACarrierTransport.GSLCore
import Mathlib.LinearAlgebra.Dual.Lemmas
import Quantum.QuantumModel.RegularizationCarrier.GSLCore

/-!
# Carrier and tensor seam for measured-relative-entropy regularization

This module supplies the flat `Fin` systems for finitely many identical
copies, density-matrix tensor products, the standard-basis transport to
right-associated Hilbert tensor products, and support transport.

The target is **the Hiai–Petz regularization (1991, measured type) — a theorem distinct from the
Hiai–Petz type matrix inequality (trace powers)**.  No regularization limit or trace-power matrix
inequality is asserted here.
-/

noncomputable section

namespace QuantumModel

open QuantumState
open TensorProduct
open scoped TensorProduct

/-- Native Kronecker operator tensors become Hilbert tensor operators. -/
theorem nativeTensorOperatorTransport_operatorTensorEquiv_tmul
    {A B : Sys} (X : Operator A) (Y : Operator B) :
    nativeTensorOperatorTransport A B
        (operatorTensorEquiv A B (X ⊗ₜ[ℂ] Y)) =
      (QuantumChannel.l_tensor_equiv
        (ℋ₁ := Space A) (ℋ₂ := Space B)).symm (X ⊗ₜ[ℂ] Y) := by
  simpa [nativeTensorOperatorTransport, nativeTensorEquiv,
    jointOperatorReindex] using
    (jointOperatorReindex_operatorTensorEquiv_tmul X Y)

/-- Transporting a density tensor gives the ordinary tensor map of its two
operators. -/
theorem nativeTensorOperatorTransport_densityTensor_operator
    {A B : Sys} (rho : DensityMatrix A) (sigma : DensityMatrix B) :
    nativeTensorOperatorTransport A B (densityTensor rho sigma).operator =
      TensorProduct.map rho.operator sigma.operator := by
  rw [densityTensor_operator,
    nativeTensorOperatorTransport_operatorTensorEquiv_tmul,
    hilbertTensorOperator_eq_map]

/-! ## Support tensor lemmas -/

namespace DensityMatrix

private noncomputable def tensorRightSliceDual
    {E F : Type*} [Qudit E] [Qudit F] (f : Module.Dual ℂ F) :
    E ⊗[ℂ] F →ₗ[ℂ] E :=
  (TensorProduct.lid ℂ E).toLinearMap.comp
    ((TensorProduct.map f LinearMap.id).comp
      (TensorProduct.comm ℂ E F).toLinearMap)

private noncomputable def tensorLeftSliceDual
    {E F : Type*} [Qudit E] [Qudit F] (f : Module.Dual ℂ E) :
    E ⊗[ℂ] F →ₗ[ℂ] F :=
  (TensorProduct.lid ℂ F).toLinearMap.comp
    (TensorProduct.map f LinearMap.id)

private theorem tensorRightSliceDual_map_mem_range
    {E F : Type*} [Qudit E] [Qudit F]
    (C : L E) (D : L F) (f : Module.Dual ℂ F) (z : E ⊗[ℂ] F) :
    tensorRightSliceDual f (TensorProduct.map C D z) ∈ LinearMap.range C := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      refine ⟨f (D y) • x, ?_⟩
      simp [tensorRightSliceDual]
  | add z w hz hw =>
      simpa using (LinearMap.range C).add_mem hz hw

private theorem tensorLeftSliceDual_map_mem_range
    {E F : Type*} [Qudit E] [Qudit F]
    (C : L E) (D : L F) (f : Module.Dual ℂ E) (z : E ⊗[ℂ] F) :
    tensorLeftSliceDual f (TensorProduct.map C D z) ∈ LinearMap.range D := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      refine ⟨f (C x) • y, ?_⟩
      simp [tensorLeftSliceDual]
  | add z w hz hw =>
      simpa using (LinearMap.range D).add_mem hz hw

private theorem range_tensorMap_left_of_le
    {E F : Type*} [Qudit E] [Qudit F]
    {A C : L E} {B D : L F}
    (h : LinearMap.range (TensorProduct.map A B) ≤
      LinearMap.range (TensorProduct.map C D))
    (hB : B ≠ 0) : LinearMap.range A ≤ LinearMap.range C := by
  intro x hx
  obtain ⟨u, rfl⟩ := hx
  have hex : ∃ v, B v ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hB
    ext v
    exact hall v
  obtain ⟨v, hv⟩ := hex
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hv
  have htensor : A u ⊗ₜ[ℂ] B v ∈
      LinearMap.range (TensorProduct.map A B) :=
    ⟨u ⊗ₜ[ℂ] v, rfl⟩
  obtain ⟨z, hz⟩ := h htensor
  have hslice := tensorRightSliceDual_map_mem_range C D f z
  rw [hz] at hslice
  simpa [tensorRightSliceDual, hf] using hslice

private theorem range_tensorMap_right_of_le
    {E F : Type*} [Qudit E] [Qudit F]
    {A C : L E} {B D : L F}
    (h : LinearMap.range (TensorProduct.map A B) ≤
      LinearMap.range (TensorProduct.map C D))
    (hA : A ≠ 0) : LinearMap.range B ≤ LinearMap.range D := by
  intro y hy
  obtain ⟨v, rfl⟩ := hy
  have hex : ∃ u, A u ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hA
    ext u
    exact hall u
  obtain ⟨u, hu⟩ := hex
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hu
  have htensor : A u ⊗ₜ[ℂ] B v ∈
      LinearMap.range (TensorProduct.map A B) :=
    ⟨u ⊗ₜ[ℂ] v, rfl⟩
  obtain ⟨z, hz⟩ := h htensor
  have hslice := tensorLeftSliceDual_map_mem_range C D f z
  rw [hz] at hslice
  simpa [tensorLeftSliceDual, hf] using hslice

/-- Support inclusion for a density tensor is exactly componentwise support
inclusion. -/
theorem supportLE_densityTensor_iff
    {A B : Sys} (rho₁ sigma₁ : DensityMatrix A)
    (rho₂ sigma₂ : DensityMatrix B) :
    SupportLE (densityTensor rho₁ rho₂) (densityTensor sigma₁ sigma₂) ↔
      SupportLE rho₁ sigma₁ ∧ SupportLE rho₂ sigma₂ := by
  let U := nativeTensorEquiv A B
  have htransport :=
    OPT.Decomposition.unitaryConjugateEnd_range_le_iff U
      (densityTensor rho₁ rho₂).operator
      (densityTensor sigma₁ sigma₂).operator
  have hρ : nativeTensorOperatorTransport A B
      (densityTensor rho₁ rho₂).operator =
        TensorProduct.map rho₁.operator rho₂.operator :=
    nativeTensorOperatorTransport_densityTensor_operator rho₁ rho₂
  have hσ : nativeTensorOperatorTransport A B
      (densityTensor sigma₁ sigma₂).operator =
        TensorProduct.map sigma₁.operator sigma₂.operator :=
    nativeTensorOperatorTransport_densityTensor_operator sigma₁ sigma₂
  change LinearMap.range (densityTensor rho₁ rho₂).operator ≤
      LinearMap.range (densityTensor sigma₁ sigma₂).operator ↔ _
  constructor
  · intro h
    have ht := htransport.mpr h
    change LinearMap.range
        (nativeTensorOperatorTransport A B
          (densityTensor rho₁ rho₂).operator) ≤
      LinearMap.range
        (nativeTensorOperatorTransport A B
          (densityTensor sigma₁ sigma₂).operator) at ht
    rw [hρ, hσ] at ht
    exact ⟨range_tensorMap_left_of_le ht rho₂.operator_ne_zero,
      range_tensorMap_right_of_le ht rho₁.operator_ne_zero⟩
  · rintro ⟨h₁, h₂⟩
    apply htransport.mp
    change LinearMap.range
        (nativeTensorOperatorTransport A B
          (densityTensor rho₁ rho₂).operator) ≤
      LinearMap.range
        (nativeTensorOperatorTransport A B
          (densityTensor sigma₁ sigma₂).operator)
    rw [hρ, hσ]
    exact TensorProduct.range_map_mono h₁ h₂

end DensityMatrix

end QuantumModel
