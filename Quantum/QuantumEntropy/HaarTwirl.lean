/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.HaarUnitaryMeasureCore

/-!
# Haar averages of finite-dimensional linear maps

The normalized Haar measure is constructed on continuous linear unitary operators.
The averages are transported to linear maps along the canonical isomorphism.
The public statements mention only linear maps; `HaarUnitaryCLM` occurs in definition
bodies, the type of the private characterization lemma, and proofs.
-/

open QuantumState MeasureTheory TensorCFC
open HaarUnitaryCLM
open scoped TensorProduct

namespace HaarUnitaryL

universe u

/-! ## Averaging over the whole space -/

section Twirl

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

/-- The normalized Haar average of unitary conjugations of a linear map.

The integral is taken on continuous endomorphisms and transported back to linear maps. -/
noncomputable def twirl (X : L ℋ) : L ℋ :=
  ((∫ u : unitary (B ℋ),
      (u : B ℋ) * X.toContinuousLinearMap * star (u : B ℋ) ∂(haarUnitary ℋ) :
      B ℋ) : L ℋ)

/-- Viewed as a continuous linear map, `twirl X` equals the Bochner integral of `u X u†`
against the normalized Haar measure `HaarUnitaryCLM.haarUnitary ℋ`. -/
private theorem toContinuousLinearMap_twirl (X : L ℋ) :
    (twirl X).toContinuousLinearMap =
      ∫ u : unitary (B ℋ),
        (u : B ℋ) * X.toContinuousLinearMap * star (u : B ℋ) ∂(HaarUnitaryCLM.haarUnitary ℋ) :=
  rfl

omit [Nontrivial ℋ] in
private lemma scalar_of_commutes_unitaries (M : ℋ →L[ℂ] ℋ)
    (hM : ∀ V : unitary (ℋ →L[ℂ] ℋ),
      (V : ℋ →L[ℂ] ℋ) * M = M * (V : ℋ →L[ℂ] ℋ)) :
    ∃ c : ℂ, M = c • (1 : ℋ →L[ℂ] ℋ) := by
  let commutant : Submodule ℂ (ℋ →L[ℂ] ℋ) :=
    { carrier := {A | A * M = M * A}
      zero_mem' := by simp
      add_mem' := by
        intro A B hA hB
        simp only [Set.mem_setOf_eq, add_mul, mul_add]
        rw [hA, hB]
      smul_mem' := by
        intro c A hA
        simp only [Set.mem_setOf_eq, smul_mul_assoc, mul_smul_comm]
        rw [hA] }
  have hspan : Submodule.span ℂ (unitary (ℋ →L[ℂ] ℋ) : Set (ℋ →L[ℂ] ℋ)) ≤ commutant :=
    Submodule.span_le.mpr fun A hA => hM ⟨A, hA⟩
  have hcomm : ∀ A : ℋ →L[ℂ] ℋ, A * M = M * A := by
    intro A
    exact hspan (by rw [CStarAlgebra.span_unitary]; exact Submodule.mem_top)
  have hcenter : M ∈ Subalgebra.center ℂ (ℋ →L[ℂ] ℋ) := by
    rw [Subalgebra.mem_center_iff]
    exact hcomm
  obtain ⟨c, hc⟩ := (Algebra.IsCentral.mem_center_iff ℂ).mp hcenter
  exact ⟨c, by simpa [Algebra.algebraMap_eq_smul_one] using hc⟩

private noncomputable def traceCLM (ℋ : Type u) [Qudit ℋ] :
    (ℋ →L[ℂ] ℋ) →L[ℂ] ℂ :=
  { toFun := fun A => LinearMap.trace ℂ ℋ (A : L ℋ)
    map_add' := fun A B => by simp
    map_smul' := fun (c : ℂ) A => by
      change LinearMap.trace ℂ ℋ (c • (A : L ℋ)) =
        c • LinearMap.trace ℂ ℋ (A : L ℋ)
      exact map_smul (LinearMap.trace ℂ ℋ) c (A : L ℋ)
    cont := LinearMap.continuous_of_finiteDimensional
      { toFun := fun A : ℋ →L[ℂ] ℋ => LinearMap.trace ℂ ℋ (A : L ℋ)
        map_add' := fun A B => by simp
        map_smul' := fun (c : ℂ) A => by
          change LinearMap.trace ℂ ℋ (c • (A : L ℋ)) =
            c • LinearMap.trace ℂ ℋ (A : L ℋ)
          exact map_smul (LinearMap.trace ℂ ℋ) c (A : L ℋ) } }

private theorem integral_eq_smul_one (X : QuantumState.B ℋ) :
    ∫ u : unitary (QuantumState.B ℋ),
      (u : QuantumState.B ℋ) * X * star (u : QuantumState.B ℋ) ∂(haarUnitary ℋ) =
    ((Module.finrank ℂ ℋ : ℂ)⁻¹ * LinearMap.trace ℂ ℋ (X : L ℋ)) •
      (1 : QuantumState.B ℋ) := by
  set Φ := ∫ u : unitary (ℋ →L[ℂ] ℋ),
    (u : ℋ →L[ℂ] ℋ) * X * star (u : ℋ →L[ℂ] ℋ) ∂(haarUnitary ℋ)
  have hΦ_comm : ∀ V : unitary (ℋ →L[ℂ] ℋ),
      (V : ℋ →L[ℂ] ℋ) * Φ = Φ * (V : ℋ →L[ℂ] ℋ) := by
    intro V
    suffices h_conj : (V : ℋ →L[ℂ] ℋ) * Φ * star (V : ℋ →L[ℂ] ℋ) = Φ by
      have hVV : star (V : ℋ →L[ℂ] ℋ) * (V : ℋ →L[ℂ] ℋ) = 1 :=
        (Unitary.mem_iff.mp V.property).1
      calc
        (V : ℋ →L[ℂ] ℋ) * Φ = (V : ℋ →L[ℂ] ℋ) * Φ * 1 := (mul_one _).symm
        _ = (V : ℋ →L[ℂ] ℋ) * Φ *
            (star (V : ℋ →L[ℂ] ℋ) * (V : ℋ →L[ℂ] ℋ)) := by rw [hVV]
        _ = ((V : ℋ →L[ℂ] ℋ) * Φ * star (V : ℋ →L[ℂ] ℋ)) *
            (V : ℋ →L[ℂ] ℋ) := by rw [mul_assoc ((V : ℋ →L[ℂ] ℋ) * Φ)]
        _ = Φ * (V : ℋ →L[ℂ] ℋ) := by rw [h_conj]
    let conjV : (ℋ →L[ℂ] ℋ) →L[ℂ] (ℋ →L[ℂ] ℋ) :=
      { toFun := fun A => (V : ℋ →L[ℂ] ℋ) * A * star (V : ℋ →L[ℂ] ℋ)
        map_add' := fun A B => by rw [mul_add, add_mul]
        map_smul' := fun c A => by rw [RingHom.id_apply, mul_smul_comm, smul_mul_assoc]
        cont := (continuous_const.mul continuous_id).mul continuous_const }
    have h_pull := conjV.integral_comp_comm (integrable_unitaryConj X)
    have hfVu : ∀ u : unitary (ℋ →L[ℂ] ℋ),
        conjV ((u : ℋ →L[ℂ] ℋ) * X * star (u : ℋ →L[ℂ] ℋ)) =
        ((V * u : unitary (ℋ →L[ℂ] ℋ)) : ℋ →L[ℂ] ℋ) * X *
          star ((V * u : unitary (ℋ →L[ℂ] ℋ)) : ℋ →L[ℂ] ℋ) := by
      intro u
      change (V : ℋ →L[ℂ] ℋ) *
        ((u : ℋ →L[ℂ] ℋ) * X * star (u : ℋ →L[ℂ] ℋ)) *
        star (V : ℋ →L[ℂ] ℋ) = _
      simp only [MulMemClass.coe_mul, star_mul, mul_assoc]
    simp_rw [hfVu] at h_pull
    have h_haar := integral_mul_left_eq_self (μ := haarUnitary ℋ)
      (fun u : unitary (ℋ →L[ℂ] ℋ) =>
        (u : ℋ →L[ℂ] ℋ) * X * star (u : ℋ →L[ℂ] ℋ)) V
    exact h_pull.symm.trans h_haar
  obtain ⟨c, hc⟩ := scalar_of_commutes_unitaries Φ hΦ_comm
  have hc_val : c = (Module.finrank ℂ ℋ : ℂ)⁻¹ *
      LinearMap.trace ℂ ℋ (X : L ℋ) := by
    have hd : (Module.finrank ℂ ℋ : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℂ) (M := ℋ)).ne'
    have h1 : LinearMap.trace ℂ ℋ (Φ : L ℋ) =
        c * (Module.finrank ℂ ℋ : ℂ) := by
      rw [hc]
      change LinearMap.trace ℂ ℋ (c • (1 : L ℋ)) =
        c * (Module.finrank ℂ ℋ : ℂ)
      rw [map_smul, LinearMap.trace_one, smul_eq_mul]
    have h2 : LinearMap.trace ℂ ℋ (Φ : L ℋ) =
        LinearMap.trace ℂ ℋ (X : L ℋ) := by
      have h_tr := (traceCLM ℋ).integral_comp_comm (integrable_unitaryConj X)
      have h_cycl : ∀ u : unitary (ℋ →L[ℂ] ℋ),
          traceCLM ℋ ((u : ℋ →L[ℂ] ℋ) * X * star (u : ℋ →L[ℂ] ℋ)) =
          LinearMap.trace ℂ ℋ (X : L ℋ) := by
        intro u
        simp only [traceCLM]
        change LinearMap.trace ℂ ℋ
          ((((u : ℋ →L[ℂ] ℋ) * X * star (u : ℋ →L[ℂ] ℋ) :
            QuantumState.B ℋ) : L ℋ)) = _
        rw [show (((u : ℋ →L[ℂ] ℋ) * X * star (u : ℋ →L[ℂ] ℋ) :
            QuantumState.B ℋ) : L ℋ) =
            ((u : ℋ →L[ℂ] ℋ) : L ℋ) * (X : L ℋ) *
              ((star (u : ℋ →L[ℂ] ℋ) : QuantumState.B ℋ) : L ℋ) from rfl,
          LinearMap.trace_mul_cycle,
          show ((star (u : ℋ →L[ℂ] ℋ) : QuantumState.B ℋ) : L ℋ) *
              ((u : ℋ →L[ℂ] ℋ) : L ℋ) = 1 from
            congrArg ContinuousLinearMap.toLinearMap (Unitary.mem_iff.mp u.property).1,
          one_mul]
      simp_rw [h_cycl] at h_tr
      simp only [integral_const, probReal_univ, one_smul] at h_tr
      simpa only [traceCLM, Φ] using h_tr.symm
    have h := h1.symm.trans h2
    rw [← h, mul_comm c (Module.finrank ℂ ℋ : ℂ), ← mul_assoc,
      inv_mul_cancel₀ hd, one_mul]
  rw [hc, hc_val]

/-- The Haar average of a linear map is its trace divided by the dimension times the identity.

The proof unfolds the transported average and applies the scalar-identity formula
for the Haar integral, whose scalar is determined by trace preservation.
Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
theorem twirl_eq_smul_one (X : L ℋ) :
    twirl X = ((Module.finrank ℂ ℋ : ℂ)⁻¹ * Tr X) • (1 : L ℋ) := by
  unfold twirl
  rw [integral_eq_smul_one]
  rfl

end Twirl

/-! ## Averaging over the first tensor factor and the Stinespring–Haar identity -/

section TensorInfrastructure

variable {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂]

private lemma tensorMap_eq_mul (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    tensorMap A B =
      rTensorContinuousStarAlgHom (ℋ₂ := ℋ₂) A *
        lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁) B := by
  change (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂)).toContinuousLinearMap =
    ((rTensorStarAlgHom (ℋ₂ := ℋ₂)) (A : L ℋ₁) *
      (lTensorStarAlgHom (ℋ₁ := ℋ₁)) (B : L ℋ₂)).toContinuousLinearMap
  exact congrArg LinearMap.toContinuousLinearMap
    (TensorCFC.map_eq_rTensor_mul_lTensor (A : L ℋ₁) (B : L ℋ₂))

private lemma tensorMap_eq_mul_comm (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    tensorMap A B =
      lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁) B *
        rTensorContinuousStarAlgHom (ℋ₂ := ℋ₂) A := by
  change (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂)).toContinuousLinearMap =
    ((lTensorStarAlgHom (ℋ₁ := ℋ₁)) (B : L ℋ₂) *
      (rTensorStarAlgHom (ℋ₂ := ℋ₂)) (A : L ℋ₁)).toContinuousLinearMap
  exact congrArg LinearMap.toContinuousLinearMap
    (TensorCFC.map_eq_lTensor_mul_rTensor (A : L ℋ₁) (B : L ℋ₂))

private lemma tensorMap_add_left (A₁ A₂ : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    tensorMap (A₁ + A₂) B = tensorMap A₁ B + tensorMap A₂ B := by
  change (TensorProduct.map ((A₁ : L ℋ₁) + (A₂ : L ℋ₁))
      (B : L ℋ₂)).toContinuousLinearMap =
    (TensorProduct.map (A₁ : L ℋ₁) (B : L ℋ₂) +
      TensorProduct.map (A₂ : L ℋ₁) (B : L ℋ₂)).toContinuousLinearMap
  exact congrArg LinearMap.toContinuousLinearMap
    (TensorProduct.map_add_left (A₁ : L ℋ₁) (A₂ : L ℋ₁) (B : L ℋ₂))

private lemma tensorMap_add_right (A : B ℋ₁) (B₁ B₂ : B ℋ₂) :
    tensorMap A (B₁ + B₂) = tensorMap A B₁ + tensorMap A B₂ := by
  change (TensorProduct.map (A : L ℋ₁)
      ((B₁ : L ℋ₂) + (B₂ : L ℋ₂))).toContinuousLinearMap =
    (TensorProduct.map (A : L ℋ₁) (B₁ : L ℋ₂) +
      TensorProduct.map (A : L ℋ₁) (B₂ : L ℋ₂)).toContinuousLinearMap
  exact congrArg LinearMap.toContinuousLinearMap
    (TensorProduct.map_add_right (A : L ℋ₁) (B₁ : L ℋ₂) (B₂ : L ℋ₂))

private lemma tensorMap_smul_left (c : ℂ) (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    tensorMap (c • A) B = c • tensorMap A B := by
  rw [tensorMap_eq_mul, tensorMap_eq_mul, map_smul]
  exact smul_mul_assoc c _ _

private lemma tensorMap_smul_right (c : ℂ) (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    tensorMap A (c • B) = c • tensorMap A B := by
  rw [tensorMap_eq_mul, tensorMap_eq_mul, map_smul]
  exact mul_smul_comm c _ _

private lemma tensorMap_smul_swap
    (a b : ℂ) (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    tensorMap A ((a * b) • B) = tensorMap (b • A) (a • B) := by
  simp only [tensorMap_smul_left, tensorMap_smul_right, smul_smul]

private lemma tensorMap_mul (A₁ A₂ : B ℋ₁) (B₁ B₂ : B ℋ₂) :
    tensorMap A₁ B₁ * tensorMap A₂ B₂ = tensorMap (A₁ * A₂) (B₁ * B₂) := by
  change (TensorProduct.map (A₁ : L ℋ₁) (B₁ : L ℋ₂) *
      TensorProduct.map (A₂ : L ℋ₁) (B₂ : L ℋ₂)).toContinuousLinearMap =
    (TensorProduct.map ((A₁ : L ℋ₁) * (A₂ : L ℋ₁))
      ((B₁ : L ℋ₂) * (B₂ : L ℋ₂))).toContinuousLinearMap
  exact congrArg LinearMap.toContinuousLinearMap
    (TensorProduct.map_mul (A₁ : L ℋ₁) (A₂ : L ℋ₁)
      (B₁ : L ℋ₂) (B₂ : L ℋ₂)).symm

private lemma continuous_tensorMap_left (B : ℋ₂ →L[ℂ] ℋ₂) :
    Continuous (fun A : ℋ₁ →L[ℂ] ℋ₁ => tensorMap A B) := by
  simp_rw [tensorMap_eq_mul]
  exact (rTensorContinuousStarAlgHom (ℋ₁ := ℋ₁)
    (ℋ₂ := ℋ₂)).toLinearMap.continuous_of_finiteDimensional.mul continuous_const

private lemma continuous_tensorMap_right (A : ℋ₁ →L[ℂ] ℋ₁) :
    Continuous (fun B : ℋ₂ →L[ℂ] ℋ₂ => tensorMap A B) := by
  simp_rw [tensorMap_eq_mul]
  exact continuous_const.mul
    (lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁)
      (ℋ₂ := ℋ₂)).toLinearMap.continuous_of_finiteDimensional

private noncomputable def tensorMapRight (B : ℋ₂ →L[ℂ] ℋ₂) :
    (ℋ₁ →L[ℂ] ℋ₁) →L[ℂ] ((ℋ₁ ⊗[ℂ] ℋ₂) →L[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂)) :=
  { toFun := fun A => tensorMap A B
    map_add' := fun A₁ A₂ => tensorMap_add_left A₁ A₂ B
    map_smul' := fun c A => tensorMap_smul_left c A B
    cont := continuous_tensorMap_left B }

private noncomputable def tensorMapLeft (A : ℋ₁ →L[ℂ] ℋ₁) :
    (ℋ₂ →L[ℂ] ℋ₂) →L[ℂ] ((ℋ₁ ⊗[ℂ] ℋ₂) →L[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂)) :=
  { toFun := fun B => tensorMap A B
    map_add' := tensorMap_add_right A
    map_smul' := fun c B => tensorMap_smul_right c A B
    cont := continuous_tensorMap_right A }

private lemma traceOutLeft_tensorMap (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    traceOutLeft (tensorMap A B) =
      LinearMap.trace ℂ ℋ₁ (A : L ℋ₁) • B := by
  change (QuantumChannel.traceOutLeft
      (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂))).toContinuousLinearMap =
    (LinearMap.trace ℂ ℋ₁ (A : L ℋ₁) • (B : L ℋ₂)).toContinuousLinearMap
  congr 1
  rw [← QuantumChannel.endomorphismTensorEquiv_symm_tmul (A : L ℋ₁) (B : L ℋ₂),
    QuantumChannel.traceOutLeft_tmul]

private lemma traceOutRight_tensorMap (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    traceOutRight (tensorMap A B) =
      LinearMap.trace ℂ ℋ₂ (B : L ℋ₂) • A := by
  change (QuantumChannel.traceOutRight
      (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂))).toContinuousLinearMap =
    (LinearMap.trace ℂ ℋ₂ (B : L ℋ₂) • (A : L ℋ₁)).toContinuousLinearMap
  congr 1
  unfold QuantumChannel.traceOutRight
  simp only [LinearMap.comp_apply]
  have hswap : QuantumChannel.conjugateEnd (TensorProduct.comm ℂ ℋ₁ ℋ₂)
      (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂)) =
      TensorProduct.map (B : L ℋ₂) (A : L ℋ₁) := by
    apply TensorProduct.ext'
    intro y x
    simp [QuantumChannel.conjugateEnd, TensorProduct.map_tmul]
  rw [hswap, ← QuantumChannel.endomorphismTensorEquiv_symm_tmul (B : L ℋ₂) (A : L ℋ₁),
    QuantumChannel.traceOutLeft_tmul]

private lemma traceOutLeft_add
    (X Y : B (ℋ₁ ⊗[ℂ] ℋ₂)) :
    traceOutLeft (X + Y) = traceOutLeft X + traceOutLeft Y := by
  change (QuantumChannel.traceOutLeft
      ((X : L (ℋ₁ ⊗[ℂ] ℋ₂)) + (Y : L (ℋ₁ ⊗[ℂ] ℋ₂)))).toContinuousLinearMap =
    (QuantumChannel.traceOutLeft (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) +
      QuantumChannel.traceOutLeft (Y : L (ℋ₁ ⊗[ℂ] ℋ₂))).toContinuousLinearMap
  exact congrArg LinearMap.toContinuousLinearMap
    (QuantumChannel.traceOutLeft.map_add
      (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) (Y : L (ℋ₁ ⊗[ℂ] ℋ₂)))

private lemma traceOutRight_add
    (X Y : B (ℋ₁ ⊗[ℂ] ℋ₂)) :
    traceOutRight (X + Y) = traceOutRight X + traceOutRight Y := by
  change (QuantumChannel.traceOutRight
      ((X : L (ℋ₁ ⊗[ℂ] ℋ₂)) + (Y : L (ℋ₁ ⊗[ℂ] ℋ₂)))).toContinuousLinearMap =
    (QuantumChannel.traceOutRight (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) +
      QuantumChannel.traceOutRight (Y : L (ℋ₁ ⊗[ℂ] ℋ₂))).toContinuousLinearMap
  exact congrArg LinearMap.toContinuousLinearMap
    (QuantumChannel.traceOutRight.map_add
      (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) (Y : L (ℋ₁ ⊗[ℂ] ℋ₂)))

end TensorInfrastructure

section TwirlLeft

variable {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂] [Nontrivial ℋ₁]

/-- The normalized Haar average of conjugation by `u ⊗ I` on the first tensor factor. -/
noncomputable def twirlLeft (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) : L (ℋ₁ ⊗[ℂ] ℋ₂) :=
  ((∫ u : unitary (B ℋ₁),
      tensorMap (u : B ℋ₁) (1 : B ℋ₂) * X.toContinuousLinearMap *
        tensorMap (star (u : B ℋ₁)) (1 : B ℋ₂)
      ∂(haarUnitary ℋ₁) : B (ℋ₁ ⊗[ℂ] ℋ₂)) : L (ℋ₁ ⊗[ℂ] ℋ₂))

private lemma integrable_leftConjugation
    (X : B (ℋ₁ ⊗[ℂ] ℋ₂)) :
    Integrable (fun u : unitary (B ℋ₁) =>
      HaarUnitaryCLM.tensorMap (u : B ℋ₁) (1 : B ℋ₂) * X *
        HaarUnitaryCLM.tensorMap (star (u : B ℋ₁)) (1 : B ℋ₂))
      (haarUnitary ℋ₁) := by
  have hl : Continuous (fun u : unitary (B ℋ₁) =>
      HaarUnitaryCLM.tensorMap (u : B ℋ₁) (1 : B ℋ₂)) :=
    (continuous_tensorMap_left (1 : B ℋ₂)).comp continuous_subtype_val
  have hr : Continuous (fun u : unitary (B ℋ₁) =>
      HaarUnitaryCLM.tensorMap (star (u : B ℋ₁)) (1 : B ℋ₂)) :=
    (continuous_tensorMap_left (1 : B ℋ₂)).comp
      (continuous_star.comp continuous_subtype_val)
  exact ((hl.mul continuous_const).mul hr).integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))

private theorem integral_left_eq
    (X : (ℋ₁ ⊗[ℂ] ℋ₂) →L[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂)) :
    ∫ u : unitary (ℋ₁ →L[ℂ] ℋ₁),
      tensorMap (u : ℋ₁ →L[ℂ] ℋ₁) (1 : ℋ₂ →L[ℂ] ℋ₂) * X *
        tensorMap (star (u : ℋ₁ →L[ℂ] ℋ₁)) (1 : ℋ₂ →L[ℂ] ℋ₂)
    ∂(haarUnitary ℋ₁) =
    tensorMap ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ • (1 : ℋ₁ →L[ℂ] ℋ₁))
      (traceOutLeft X) := by
  let e₁ := Module.End.toContinuousLinearMap (𝕜 := ℂ) ℋ₁
  let e₂ := Module.End.toContinuousLinearMap (𝕜 := ℂ) ℋ₂
  let e₁₂ := Module.End.toContinuousLinearMap (𝕜 := ℂ) (ℋ₁ ⊗[ℂ] ℋ₂)
  suffices h : ∀ Y : L ℋ₁ ⊗[ℂ] L ℋ₂,
      (∫ u : unitary (ℋ₁ →L[ℂ] ℋ₁),
        tensorMap (u : ℋ₁ →L[ℂ] ℋ₁) (1 : ℋ₂ →L[ℂ] ℋ₂) *
          e₁₂ ((QuantumChannel.endomorphismTensorEquiv (ℋ₁ := ℋ₁)
            (ℋ₂ := ℋ₂)).symm Y) *
          tensorMap (star (u : ℋ₁ →L[ℂ] ℋ₁)) (1 : ℋ₂ →L[ℂ] ℋ₂)
        ∂(haarUnitary ℋ₁)) =
      tensorMap ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ • (1 : ℋ₁ →L[ℂ] ℋ₁))
        (traceOutLeft (e₁₂ ((QuantumChannel.endomorphismTensorEquiv (ℋ₁ := ℋ₁)
          (ℋ₂ := ℋ₂)).symm Y))) by
    simpa only [LinearEquiv.symm_apply_apply, e₁₂.apply_symm_apply] using
      h ((QuantumChannel.endomorphismTensorEquiv (ℋ₁ := ℋ₁)
        (ℋ₂ := ℋ₂)) (e₁₂.symm X))
  intro Y
  induction Y using TensorProduct.induction_on with
  | zero =>
      dsimp only [tensorMap, traceOutLeft]
      simp [TensorProduct.map_zero_right]
  | tmul A B =>
      rw [QuantumChannel.endomorphismTensorEquiv_symm_tmul]
      have htm : e₁₂ (TensorProduct.map A B) = tensorMap (e₁ A) (e₂ B) := by
        change e₁₂ (TensorProduct.map A B) =
          e₁₂ (TensorProduct.map (e₁.symm (e₁ A)) (e₂.symm (e₂ B)))
        rw [e₁.symm_apply_apply, e₂.symm_apply_apply]
      rw [htm]
      have hintegrand : ∀ u : unitary (ℋ₁ →L[ℂ] ℋ₁),
          tensorMap (u : ℋ₁ →L[ℂ] ℋ₁) (1 : ℋ₂ →L[ℂ] ℋ₂) *
            tensorMap (e₁ A) (e₂ B) *
            tensorMap (star (u : ℋ₁ →L[ℂ] ℋ₁)) (1 : ℋ₂ →L[ℂ] ℋ₂) =
          tensorMap ((u : ℋ₁ →L[ℂ] ℋ₁) * e₁ A *
            star (u : ℋ₁ →L[ℂ] ℋ₁)) (e₂ B) := by
        intro u
        rw [tensorMap_mul, tensorMap_mul]
        simp only [mul_one, one_mul]
      simp_rw [hintegrand]
      calc
        (∫ u : unitary (ℋ₁ →L[ℂ] ℋ₁),
            tensorMap ((u : ℋ₁ →L[ℂ] ℋ₁) * e₁ A *
              star (u : ℋ₁ →L[ℂ] ℋ₁)) (e₂ B) ∂(haarUnitary ℋ₁)) =
            tensorMapRight (e₂ B)
              (∫ u : unitary (ℋ₁ →L[ℂ] ℋ₁),
                (u : ℋ₁ →L[ℂ] ℋ₁) * e₁ A *
                  star (u : ℋ₁ →L[ℂ] ℋ₁) ∂(haarUnitary ℋ₁)) :=
          (tensorMapRight (e₂ B)).integral_comp_comm (integrable_unitaryConj (e₁ A))
        _ = tensorMap ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ • (1 : ℋ₁ →L[ℂ] ℋ₁))
              (traceOutLeft (tensorMap (e₁ A) (e₂ B))) := by
          rw [integral_eq_smul_one, traceOutLeft_tensorMap]
          change tensorMap
              (((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ * LinearMap.trace ℂ ℋ₁ A) •
                (1 : ℋ₁ →L[ℂ] ℋ₁)) (e₂ B) =
            tensorMap ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ •
              (1 : ℋ₁ →L[ℂ] ℋ₁))
              (LinearMap.trace ℂ ℋ₁ A • e₂ B)
          calc
            tensorMap
                (((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ * LinearMap.trace ℂ ℋ₁ A) •
                  (1 : ℋ₁ →L[ℂ] ℋ₁)) (e₂ B) =
                ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ * LinearMap.trace ℂ ℋ₁ A) •
                  tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (e₂ B) :=
              tensorMap_smul_left _ _ _
            _ = LinearMap.trace ℂ ℋ₁ A •
                ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ •
                  tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (e₂ B)) := by
              simp only [smul_smul]
              rw [mul_comm]
            _ = LinearMap.trace ℂ ℋ₁ A •
                tensorMap ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ •
                  (1 : ℋ₁ →L[ℂ] ℋ₁)) (e₂ B) := by
              rw [tensorMap_smul_left]
            _ = tensorMap ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ •
                  (1 : ℋ₁ →L[ℂ] ℋ₁))
                (LinearMap.trace ℂ ℋ₁ A • e₂ B) :=
              (tensorMap_smul_right _ _ _).symm
  | add Y₁ Y₂ hY₁ hY₂ =>
      simp only [map_add, mul_add, add_mul]
      rw [integral_add
        (integrable_leftConjugation _)
        (integrable_leftConjugation _),
        hY₁, hY₂, traceOutLeft_add, tensorMap_add_right]

/-- Averaging the first tensor factor gives its maximally mixed operator tensored with
the left partial trace, for an arbitrary linear map on the tensor product.
Explicitly, `twirlLeft X = ((finrank ℂ ℋ₁)⁻¹ • 1) ⊗ Tr_{ℋ₁} X`, where
`Tr_{ℋ₁}` (`QuantumChannel.traceOutLeft`) traces out the first tensor factor.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
theorem twirlLeft_eq (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) :
    twirlLeft X =
      TensorProduct.map ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ • (1 : L ℋ₁))
        (QuantumChannel.traceOutLeft X) := by
  unfold twirlLeft
  rw [integral_left_eq]
  rfl

/-- The Stinespring–Haar identity for linear maps: the maximally mixed first factor tensored
with the left partial trace of `U (τ ⊗ γ) U†` equals its first-factor Haar average.
Explicitly, `((finrank ℂ ℋ₁)⁻¹ • 1) ⊗ Tr_{ℋ₁} (U (τ ⊗ γ) U†) = twirlLeft (U (τ ⊗ γ) U†)`,
where `Tr_{ℋ₁}` (`QuantumChannel.traceOutLeft`) traces out the first tensor factor.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
theorem stinespring_haar_eq
    (U : unitary (L (ℋ₁ ⊗[ℂ] ℋ₂))) (τ : L ℋ₁) (γ : L ℋ₂) :
    TensorProduct.map ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ • (1 : L ℋ₁))
      (QuantumChannel.traceOutLeft
        ((U : L (ℋ₁ ⊗[ℂ] ℋ₂)) * TensorProduct.map τ γ * star (U : L (ℋ₁ ⊗[ℂ] ℋ₂)))) =
    twirlLeft
      ((U : L (ℋ₁ ⊗[ℂ] ℋ₂)) * TensorProduct.map τ γ * star (U : L (ℋ₁ ⊗[ℂ] ℋ₂))) :=
  (twirlLeft_eq _).symm

end TwirlLeft

/-! ## Averaging over the second tensor factor -/

section TwirlRight

variable {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂] [Nontrivial ℋ₂]

/-- The Haar average of conjugation over the second tensor factor. -/
noncomputable def twirlRight (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) : L (ℋ₁ ⊗[ℂ] ℋ₂) :=
  ((∫ u : unitary (B ℋ₂),
      tensorMap (1 : B ℋ₁) (u : B ℋ₂) * X.toContinuousLinearMap *
        tensorMap (1 : B ℋ₁) (star (u : B ℋ₂))
      ∂(haarUnitary ℋ₂) : B (ℋ₁ ⊗[ℂ] ℋ₂)) : L (ℋ₁ ⊗[ℂ] ℋ₂))

private theorem integral_right_eq
    (X : (ℋ₁ ⊗[ℂ] ℋ₂) →L[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂)) :
    ∫ u : unitary (ℋ₂ →L[ℂ] ℋ₂),
      tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (u : ℋ₂ →L[ℂ] ℋ₂) * X *
        tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (star (u : ℋ₂ →L[ℂ] ℋ₂))
    ∂(haarUnitary ℋ₂) =
    tensorMap (traceOutRight X)
      ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • (1 : ℋ₂ →L[ℂ] ℋ₂)) := by
  let e₁ := Module.End.toContinuousLinearMap (𝕜 := ℂ) ℋ₁
  let e₂ := Module.End.toContinuousLinearMap (𝕜 := ℂ) ℋ₂
  let e₁₂ := Module.End.toContinuousLinearMap (𝕜 := ℂ) (ℋ₁ ⊗[ℂ] ℋ₂)
  let Φ := fun Z : (ℋ₁ ⊗[ℂ] ℋ₂) →L[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂) =>
    ∫ u : unitary (ℋ₂ →L[ℂ] ℋ₂),
      tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (u : ℋ₂ →L[ℂ] ℋ₂) * Z *
        tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (star (u : ℋ₂ →L[ℂ] ℋ₂))
      ∂(haarUnitary ℋ₂)
  have hΦ_zero : Φ 0 = 0 := by
    simp [Φ]
  have hΦ_add (Z W : (ℋ₁ ⊗[ℂ] ℋ₂) →L[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂)) :
      Φ (Z + W) = Φ Z + Φ W := by
    simp only [Φ, mul_add, add_mul]
    rw [integral_add (integrable_unitaryConj_tensor_right Z)
      (integrable_unitaryConj_tensor_right W)]
  suffices h : ∀ Y : L ℋ₁ ⊗[ℂ] L ℋ₂,
      Φ (e₁₂ ((QuantumChannel.endomorphismTensorEquiv (ℋ₁ := ℋ₁)
        (ℋ₂ := ℋ₂)).symm Y)) =
      tensorMap
        (traceOutRight (e₁₂ ((QuantumChannel.endomorphismTensorEquiv (ℋ₁ := ℋ₁)
          (ℋ₂ := ℋ₂)).symm Y)))
        ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • (1 : ℋ₂ →L[ℂ] ℋ₂)) by
    simpa only [Φ, LinearEquiv.symm_apply_apply, e₁₂.apply_symm_apply] using
      h ((QuantumChannel.endomorphismTensorEquiv (ℋ₁ := ℋ₁)
        (ℋ₂ := ℋ₂)) (e₁₂.symm X))
  intro Y
  induction Y using TensorProduct.induction_on with
  | zero =>
      dsimp only [tensorMap, traceOutRight]
      simp [hΦ_zero, TensorProduct.map_zero_left]
  | tmul A B =>
      rw [QuantumChannel.endomorphismTensorEquiv_symm_tmul]
      have htm : e₁₂ (TensorProduct.map A B) = tensorMap (e₁ A) (e₂ B) := by
        change e₁₂ (TensorProduct.map A B) =
          e₁₂ (TensorProduct.map (e₁.symm (e₁ A)) (e₂.symm (e₂ B)))
        rw [e₁.symm_apply_apply, e₂.symm_apply_apply]
      rw [htm]
      simp only [Φ]
      have hintegrand : ∀ u : unitary (ℋ₂ →L[ℂ] ℋ₂),
          tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (u : ℋ₂ →L[ℂ] ℋ₂) *
            tensorMap (e₁ A) (e₂ B) *
            tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (star (u : ℋ₂ →L[ℂ] ℋ₂)) =
          tensorMap (e₁ A) ((u : ℋ₂ →L[ℂ] ℋ₂) * e₂ B *
            star (u : ℋ₂ →L[ℂ] ℋ₂)) := by
        intro u
        rw [tensorMap_mul, tensorMap_mul]
        simp only [mul_one, one_mul]
      simp_rw [hintegrand]
      calc
        (∫ u : unitary (ℋ₂ →L[ℂ] ℋ₂),
            tensorMap (e₁ A) ((u : ℋ₂ →L[ℂ] ℋ₂) * e₂ B *
              star (u : ℋ₂ →L[ℂ] ℋ₂)) ∂(haarUnitary ℋ₂)) =
            tensorMapLeft (e₁ A)
              (∫ u : unitary (ℋ₂ →L[ℂ] ℋ₂),
                (u : ℋ₂ →L[ℂ] ℋ₂) * e₂ B *
                  star (u : ℋ₂ →L[ℂ] ℋ₂) ∂(haarUnitary ℋ₂)) :=
          (tensorMapLeft (e₁ A)).integral_comp_comm (integrable_unitaryConj (e₂ B))
        _ = tensorMap (traceOutRight (tensorMap (e₁ A) (e₂ B)))
              ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • (1 : ℋ₂ →L[ℂ] ℋ₂)) := by
          rw [integral_eq_smul_one, traceOutRight_tensorMap]
          change tensorMap (e₁ A)
              (((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ * LinearMap.trace ℂ ℋ₂ B) •
                (1 : ℋ₂ →L[ℂ] ℋ₂)) =
            tensorMap (LinearMap.trace ℂ ℋ₂ B • e₁ A)
              ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • (1 : ℋ₂ →L[ℂ] ℋ₂))
          exact tensorMap_smul_swap _ _ _ _
  | add Y₁ Y₂ hY₁ hY₂ =>
      simp only [map_add, hΦ_add]
      rw [hY₁, hY₂, traceOutRight_add]
      exact (tensorMap_add_left (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) _ _ _).symm

/-- The second-factor Haar average is the right partial trace tensored with the mixed state. -/
theorem twirlRight_eq (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) :
    twirlRight X =
      TensorProduct.map (QuantumChannel.traceOutRight X)
        ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • (1 : L ℋ₂)) := by
  unfold twirlRight
  rw [integral_right_eq]
  rfl

end TwirlRight

end HaarUnitaryL
