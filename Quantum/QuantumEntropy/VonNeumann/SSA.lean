/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.PositiveDefiniteTensor
import Quantum.QuantumEntropy.VonNeumann.StateTensor
import Quantum.QuantumEntropy.VonNeumann.PartialTraceThirdCPTP
import Quantum.QuantumEntropy.UmegakiDPI.NonNegLift
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificatesStrongSubadditivity

/-!
# Strong subadditivity of the von Neumann entropy

The strong subadditivity (SSA) inequality

`S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`

for a state `ρ` on `ℋA ⊗ (ℋB ⊗ ℋC)` with positive-definite marginals,
derived by the standard route:

1. the data-processing inequality for the Umegaki relative entropy
   (`UmegakiDPI.monotoneNormOnNonNeg`) applied to the CPTP channel
   `CPTP.traceOutThird` tracing out the third factor;
2. the mutual-information expansion
   `D(ρ ‖ ρ₁ ⊗ ρ₂) = S(ρ₁) + S(ρ₂) - S(ρ)`
   (`umegakiNorm_state_tensor_marginals`) on both sides;
3. marginal-coherence identities for `traceOutThird`
   (`Tr_B ∘ Tr_C = Tr_{BC}`, `Tr_A ∘ Tr_C = Tr_C ∘ Tr_A`,
   `Tr_C (X ⊗ Y) = X ⊗ Tr_C Y`), proved on generator endomorphisms.

The positive-definiteness hypotheses on the marginals `ρ_A`, `ρ_BC` in
`strongSubadditivity` match the faithful-marginal convention of
`umegakiNorm_state_tensor_marginals`. Positive definiteness of `ρ_B`
follows from that of `ρ_BC` by partial trace. The closure theorem
`strongSubadditivity_of_state` removes these faithfulness hypotheses by mixing
with the maximally mixed product state and passing to the limit by finite-
dimensional entropy continuity.
-/

namespace VonNeumann

open QuantumState QuantumChannel TensorProduct
open GeneralizedPerspectiveFunction SandwichedRenyiRelativeEntropy
open scoped ComplexOrder Topology

universe u

section LinearMapCarrier

variable {ℋ₁ ℋ₂ ℋ₃ : Type u} [Qudit ℋ₁] [Qudit ℋ₂] [Qudit ℋ₃]

/-- The associator conjugation regroups an elementary triple tensor
endomorphism: `P ⊗ (R ⊗ S) ↦ (P ⊗ R) ⊗ S`. -/
private lemma conjugateEnd_assoc_symm_map (P : L ℋ₁) (R : L ℋ₂) (S : L ℋ₃) :
    conjugateEnd (TensorProduct.assoc ℂ ℋ₁ ℋ₂ ℋ₃).symm
      (TensorProduct.map P (TensorProduct.map R S)) =
      TensorProduct.map (TensorProduct.map P R) S := by
  apply TensorProduct.ext'
  intro xy z
  induction xy using TensorProduct.induction_on with
  | zero => simp [conjugateEnd]
  | tmul x y => simp [conjugateEnd]
  | add a b ha hb =>
      simp only [add_tmul, map_add] at ha hb ⊢
      rw [ha, hb]

/-- **Partial trace of the third factor on a tensor split**
`Tr_C (P ⊗ Q) = P ⊗ (Tr_C Q)` for `P` on `ℋ₁` and `Q` on `ℋ₂ ⊗ ℋ₃`. -/
private lemma traceOutThird_map (P : L ℋ₁) (Q : L (ℋ₂ ⊗[ℂ] ℋ₃)) :
    traceOutThird (TensorProduct.map P Q) =
      TensorProduct.map P
        (QuantumChannel.traceOutRight (ℋ₂ := ℋ₂) (ℋ₃ := ℋ₃) Q) := by
  obtain ⟨W, rfl⟩ :=
    (endomorphismTensorEquiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₃)).symm.surjective Q
  induction W using TensorProduct.induction_on with
  | zero =>
      simp only [map_zero, TensorProduct.map_zero_right]
  | tmul R S =>
      rw [endomorphismTensorEquiv_symm_tmul]
      unfold QuantumChannel.traceOutThird
      rw [LinearMap.comp_apply, conjugateEnd_assoc_symm_map,
        traceOutRight_map, traceOutRight_map, TensorProduct.map_smul_right]
  | add W₁ W₂ h₁ h₂ =>
      rw [map_add, TensorProduct.map_add_right, map_add, h₁, h₂, map_add,
        TensorProduct.map_add_right]

/-- **Marginal coherence (first factor)**: tracing out the third factor and
then the second gives the first marginal, `Tr_B (Tr_C Z) = Tr_{BC} Z`. -/
private lemma traceOutRight_traceOutThird (Z : L (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃))) :
    QuantumChannel.traceOutRight (ℋ₂ := ℋ₁) (ℋ₃ := ℋ₂)
        (traceOutThird Z) =
      QuantumChannel.traceOutRight (ℋ₂ := ℋ₁) (ℋ₃ := ℋ₂ ⊗[ℂ] ℋ₃) Z := by
  obtain ⟨W, rfl⟩ :=
    (endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂ ⊗[ℂ] ℋ₃)).symm.surjective Z
  induction W using TensorProduct.induction_on with
  | zero => simp
  | tmul P Q =>
      rw [endomorphismTensorEquiv_symm_tmul, traceOutThird_map, traceOutRight_map,
        traceOutRight_map, trace_traceOutRight]
  | add W₁ W₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, h₁, h₂, map_add]

/-- **Marginal coherence (middle factor)**: the partial traces over the
first and third factors commute, `Tr_A (Tr_C Z) = Tr_C (Tr_A Z)`. -/
private lemma traceOutLeft_traceOutThird (Z : L (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃))) :
    QuantumChannel.traceOutLeft (traceOutThird Z) =
      QuantumChannel.traceOutRight (ℋ₂ := ℋ₂) (ℋ₃ := ℋ₃)
        (QuantumChannel.traceOutLeft Z) := by
  obtain ⟨W, rfl⟩ :=
    (endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂ ⊗[ℂ] ℋ₃)).symm.surjective Z
  induction W using TensorProduct.induction_on with
  | zero => simp
  | tmul P Q =>
      rw [endomorphismTensorEquiv_symm_tmul, traceOutThird_map, traceOutLeft_map,
        traceOutLeft_map, map_smul]
  | add W₁ W₂ h₁ h₂ =>
      simp only [map_add]
      rw [h₁, h₂]

end LinearMapCarrier

section CLMCarrier

variable {ℋ₁ ℋ₂ ℋ₃ : Type u} [Qudit ℋ₁] [Qudit ℋ₂] [Qudit ℋ₃]

/-- Linear-map form of `Tr_C (X ⊗ Y) = X ⊗ (Tr_C Y)`. -/
private lemma traceOutThirdCLM_tensorMap (X : L ℋ₁) (Y : L (ℋ₂ ⊗[ℂ] ℋ₃)) :
    traceOutThird (TensorProduct.map X Y) =
      TensorProduct.map X (QuantumChannel.traceOutRight Y) := by
  exact traceOutThird_map _ _

/-- Linear-map form of the first-factor marginal coherence. -/
private lemma traceOutRight_traceOutThirdCLM
    (ρ : L (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃))) :
    QuantumChannel.traceOutRight (traceOutThird ρ) =
      QuantumChannel.traceOutRight ρ := by
  exact traceOutRight_traceOutThird _

/-- Linear-map form of the middle-factor marginal coherence. -/
private lemma traceOutLeft_traceOutThirdCLM
    (ρ : L (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃))) :
    QuantumChannel.traceOutLeft (traceOutThird ρ) =
      QuantumChannel.traceOutRight (QuantumChannel.traceOutLeft ρ) := by
  exact traceOutLeft_traceOutThird _

end CLMCarrier

section PdSetBridge

variable {ℋ : Type u} [Qudit ℋ]

private lemma mem_pdSet_of_pdSetLM {σ : L ℋ}
    (hσ : σ ∈ pdSetLM (ℋ := ℋ)) : σ.toContinuousLinearMap ∈ pdSet := by
  change σ.toContinuousLinearMap ∈ pdSet at hσ
  exact hσ

/-- Positive definiteness is preserved by the right partial trace. -/
private lemma traceOutRight_mem_pdSet {ℋ₁ ℋ₂ : Type u}
    [Qudit ℋ₁] [Qudit ℋ₂] [Nontrivial ℋ₁] [Nontrivial ℋ₂]
    {σ : L (ℋ₁ ⊗[ℂ] ℋ₂)} (hσ : σ ∈ pdSetLM) :
    QuantumChannel.traceOutRight σ ∈ pdSetLM := by
  apply (pdSetLM_uniformLowerBound_iff _).2
  obtain ⟨ε, hε, hεσ⟩ :=
    (pdSetLM_uniformLowerBound_iff σ).1 hσ
  refine ⟨ε * Module.finrank ℂ ℋ₂, mul_pos hε ?_, ?_⟩
  · exact_mod_cast Module.finrank_pos
  · have h := traceOutRight_le_traceOutRight hεσ
    have hleft :
        QuantumChannel.traceOutRight
            ((ε : ℂ) • (1 : L (ℋ₁ ⊗[ℂ] ℋ₂))) =
          ((ε * Module.finrank ℂ ℋ₂ : ℝ) : ℂ) • (1 : L ℋ₁) := by
      rw [map_smul, ← TensorProduct.map_one, traceOutRight_map,
        LinearMap.trace_one, smul_smul]
      norm_cast
    rwa [hleft] at h

end PdSetBridge

section FaithfulClosure

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

/-- **Finite-dimensional entropy closure along a faithful mixture**:
for `ρ ≥ 0` and `c > 0`, the von Neumann entropy of
`(1 - λ)ρ + λ cI` converges to the entropy of `ρ` as `λ → 0⁺`.

This is the entropy-continuity input for removing faithful-marginal
hypotheses. It is a direct specialization of
`tendsto_tr_faithful_cross`, whose finite-dimensional eigenbasis proof
handles the singular `x log x` boundary by `x log x → 0` at zero. -/
lemma tendsto_vonNeumannEntropy_faithful_mix {ρ : L ℋ}
    (hρ : 0 ≤ ρ) {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto
      (fun lam : ℝ => vonNeumannEntropy
        (((1 - lam : ℝ) : ℂ) • ρ + ((lam * c : ℝ) : ℂ) • 1))
      (𝓝[>] (0 : ℝ)) (𝓝 (vonNeumannEntropy ρ)) := by
  simp_rw [vonNeumannEntropy_def]
  have hρ_clm : (0 : B ℋ) ≤ ρ.toContinuousLinearMap :=
    (ContinuousLinearMap.coe_le_coe_iff 0 ρ.toContinuousLinearMap).mpr hρ
  exact (UmegakiDPI.tendsto_tr_faithful_cross (A := ρ.toContinuousLinearMap)
    (B := ρ.toContinuousLinearMap) hρ_clm hρ_clm (le_refl _) hc).neg

/-- **Full-rank component mixing**: if `ρ ≥ 0`, `c > 0`, and
`0 < λ ≤ 1`, then `(1 - λ)ρ + λ cI` is positive definite. -/
lemma faithful_mix_mem_pdSetLM {ρ : L ℋ}
    (hρ : 0 ≤ ρ) {c lam : ℝ} (hc : 0 < c)
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    (((1 - lam : ℝ) : ℂ) • ρ + ((lam * c : ℝ) : ℂ) • 1) ∈ pdSetLM := by
  apply pdSetLM_add_nonneg
  · exact smul_nonneg (Complex.zero_le_real.mpr (sub_nonneg.mpr hlam1)) hρ
  · exact pos_smul_one_pdSetLM (mul_pos hlam0 hc)

omit [Nontrivial ℋ] in
/-- A normalized identity mixture has trace one when its identity
coefficient is normalized by the dimension. -/
lemma faithful_mix_trace_one {ρ : L ℋ}
    (hTr : Tr ρ = 1) {c : ℝ}
    (hc_dim : c * (Module.finrank ℂ ℋ : ℝ) = 1) (lam : ℝ) :
    Tr (((1 - lam : ℝ) : ℂ) • ρ +
      ((lam * c : ℝ) : ℂ) • 1) = 1 := by
  rw [map_add, map_smul, map_smul, hTr, LinearMap.trace_one]
  simp only [smul_eq_mul]
  push_cast
  have hc_dim_complex :
      (c : ℂ) * (Module.finrank ℂ ℋ : ℂ) = 1 := by
    exact_mod_cast hc_dim
  calc
    _ = (1 : ℂ) - (lam : ℂ) +
        (lam : ℂ) * ((c : ℂ) * (Module.finrank ℂ ℋ : ℂ)) := by
          ring
    _ = 1 := by rw [hc_dim_complex]; ring

end FaithfulClosure

section MarginalFaithfulMix

variable {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂]

/-- The right partial trace of a faithful identity mixture is again such a
mixture; tracing the identity multiplies its coefficient by the dimension of
the discarded factor. -/
lemma traceOutRight_faithful_mix
    (ρ : L (ℋ₁ ⊗[ℂ] ℋ₂)) (c lam : ℝ) :
    QuantumChannel.traceOutRight
        (((1 - lam : ℝ) : ℂ) • ρ + ((lam * c : ℝ) : ℂ) • 1) =
      ((1 - lam : ℝ) : ℂ) • QuantumChannel.traceOutRight ρ +
        ((lam * (c * (Module.finrank ℂ ℋ₂ : ℝ)) : ℝ) : ℂ) • 1 := by
  rw [map_add, map_smul, map_smul, ← TensorProduct.map_one,
    traceOutRight_map, LinearMap.trace_one, smul_smul]
  congr 1
  push_cast
  ring_nf

/-- Left-partial-trace counterpart of `traceOutRight_faithful_mix`. -/
lemma traceOutLeft_faithful_mix
    (ρ : L (ℋ₁ ⊗[ℂ] ℋ₂)) (c lam : ℝ) :
    QuantumChannel.traceOutLeft
        (((1 - lam : ℝ) : ℂ) • ρ + ((lam * c : ℝ) : ℂ) • 1) =
      ((1 - lam : ℝ) : ℂ) • QuantumChannel.traceOutLeft ρ +
        ((lam * (c * (Module.finrank ℂ ℋ₁ : ℝ)) : ℝ) : ℂ) • 1 := by
  rw [map_add, map_smul, map_smul, ← TensorProduct.map_one,
    traceOutLeft_map, LinearMap.trace_one, smul_smul]
  congr 1
  push_cast
  ring_nf

variable {ℋ₃ : Type u} [Qudit ℋ₃]

/-- Third-factor-partial-trace counterpart of
`traceOutRight_faithful_mix`. -/
private lemma traceOutThird_faithful_mix
    (ρ : L (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃))) (c lam : ℝ) :
    traceOutThird
        (((1 - lam : ℝ) : ℂ) • ρ + ((lam * c : ℝ) : ℂ) • 1) =
      ((1 - lam : ℝ) : ℂ) • traceOutThird ρ +
        ((lam * (c * (Module.finrank ℂ ℋ₃ : ℝ)) : ℝ) : ℂ) • 1 := by
  rw [map_add, map_smul, map_smul]
  have hone : traceOutThird (1 : L (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃))) =
      ((Module.finrank ℂ ℋ₃ : ℂ)) • (1 : L (ℋ₁ ⊗[ℂ] ℋ₂)) := by
    unfold traceOutThird
    rw [LinearMap.comp_apply]
    have hconj : conjugateEnd (TensorProduct.assoc ℂ ℋ₁ ℋ₂ ℋ₃).symm
        (1 : L (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃))) =
        (1 : L ((ℋ₁ ⊗[ℂ] ℋ₂) ⊗[ℂ] ℋ₃)) := by
      ext x
      simp [conjugateEnd]
    rw [hconj, ← TensorProduct.map_one, traceOutRight_map,
      LinearMap.trace_one]
  rw [hone, smul_smul]
  congr 1
  push_cast
  ring_nf

end MarginalFaithfulMix

section SSA

variable {ℋA ℋB ℋC : Type u} [Qudit ℋA] [Qudit ℋB] [Qudit ℋC]
variable [Nontrivial ℋA] [Nontrivial ℋB] [Nontrivial ℋC]

/-- **Strong subadditivity of the von Neumann entropy**: for a state `ρ` on `ℋA ⊗ (ℋB ⊗ ℋC)` with
faithful (positive-definite) marginals `ρ_A` and `ρ_BC`,

`S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`.

Proof: apply the Umegaki data-processing inequality (`UmegakiDPI.monotoneNormOnNonNeg`) to the CPTP
partial trace over `ℋC` with second argument `ρ_A ⊗ ρ_BC`, and expand both sides by
the mutual-information identity. The marginal `ρ_B` is automatically
faithful because it is the partial trace of faithful `ρ_BC`. Extension to
general, possibly non-faithful states is `strongSubadditivity_of_state`,
proved below by faithful mixing and finite-dimensional entropy continuity. -/
theorem strongSubadditivity (ρ : L (ℋA ⊗[ℂ] (ℋB ⊗[ℂ] ℋC)))
    (hρ : 0 ≤ ρ)
    (hTr : Tr ρ = 1)
    (hA : QuantumChannel.traceOutRight ρ ∈ pdSetLM)
    (hBC : QuantumChannel.traceOutLeft ρ ∈ pdSetLM) :
    vonNeumannEntropy ρ +
        vonNeumannEntropy
          (QuantumChannel.traceOutRight (QuantumChannel.traceOutLeft ρ)) ≤
      vonNeumannEntropy (traceOutThird ρ) +
        vonNeumannEntropy (QuantumChannel.traceOutLeft ρ) := by
  have hB : QuantumChannel.traceOutRight
      (QuantumChannel.traceOutLeft ρ) ∈ pdSetLM :=
    traceOutRight_mem_pdSet hBC
  -- the tensor second argument `σ = ρ_A ⊗ ρ_BC` is positive definite
  have hσ_pd : TensorProduct.map (QuantumChannel.traceOutRight ρ)
      (QuantumChannel.traceOutLeft ρ) ∈ pdSetLM :=
    pdSetLM_tensorMap hA hBC
  have hσ_nonneg : (0 : L (ℋA ⊗[ℂ] (ℋB ⊗[ℂ] ℋC))) ≤
      TensorProduct.map (QuantumChannel.traceOutRight ρ)
        (QuantumChannel.traceOutLeft ρ) :=
    nonneg_of_pdSetLM hσ_pd
  have hsupp : SupportLE ρ
      (TensorProduct.map (QuantumChannel.traceOutRight ρ)
        (QuantumChannel.traceOutLeft ρ)) :=
    suppLE_of_pdSetLM_right _ hσ_pd
  -- data-processing inequality for the partial trace over ℋC
  have hDPI := UmegakiDPI.monotoneNormOnNonNeg (CPTP.traceOutThird ℋA ℋB ℋC)
    hρ hσ_nonneg hsupp
  rw [CPTP.traceOutThird_toFun, CPTP.traceOutThird_toFun,
    traceOutThirdCLM_tensorMap] at hDPI
  -- trace of the two-body marginal
  have hTrAB : Tr (traceOutThird ρ) = 1 := by
    rw [trace_traceOutThird]
    exact hTr
  -- entropy expansion of the left-hand side (marginals of ρ_AB)
  have hlhs : umegakiNorm
      (traceOutThird ρ)
      (TensorProduct.map (QuantumChannel.traceOutRight ρ)
        (QuantumChannel.traceOutRight (QuantumChannel.traceOutLeft ρ))) =
      vonNeumannEntropy (QuantumChannel.traceOutRight ρ) +
        vonNeumannEntropy
          (QuantumChannel.traceOutRight (QuantumChannel.traceOutLeft ρ)) -
        vonNeumannEntropy (traceOutThird ρ) := by
    have h := umegakiNorm_state_tensor_marginals (traceOutThird ρ)
      (by rw [traceOutRight_traceOutThirdCLM]; exact hA)
      (by rw [traceOutLeft_traceOutThirdCLM]; exact hB)
      hTrAB
    rwa [traceOutRight_traceOutThirdCLM, traceOutLeft_traceOutThirdCLM] at h
  -- entropy expansion of the right-hand side (marginals of ρ)
  have hrhs := umegakiNorm_state_tensor_marginals ρ hA hBC hTr
  rw [hlhs, hrhs] at hDPI
  linarith

/-- **Strong subadditivity for an arbitrary finite-dimensional state**:

S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC).

The state assumptions are only that the tripartite density operator is
positive semidefinite and has trace one; no additional faithfulness is assumed.
The proof mixes ρ with the maximally mixed product state, applies the theorem
`strongSubadditivity` above (the faithful-marginal case) at every positive mixing parameter, and
closes the inequality at zero using `tendsto_vonNeumannEntropy_faithful_mix`.

Original statement: Lieb–Ruskai (1973).
The basic route of this proof follows Carlen's lecture notes (version of May 3, 2009), p. 47, proof
of Theorem 6.6. The printed inequality in Theorem 6.6, S(ρ13) + S(ρ23) ≥ S(ρ123) + S(ρ3),
becomes S(ρ_AB) + S(ρ_BC) ≥ S(ρ_ABC) + S(ρ_B) under (1, 2, 3) = (A, C, B),
with the tensor factors permuted into the A ⊗ (B ⊗ C) order used in Lean.
The formalization uses the partial trace over the third system directly instead of the
conditional-expectation presentation. In the faithful-marginal case it proves the support inclusion
needed for the data-processing inequality; the general case follows by faithful mixing and
continuity of the entropy. The proof uses the Umegaki data-processing inequality and faithful
mixing. -/
theorem strongSubadditivity_of_state
    (ρ : L (ℋA ⊗[ℂ] (ℋB ⊗[ℂ] ℋC)))
    (hρ : 0 ≤ ρ)
    (hTr : Tr ρ = 1) :
    vonNeumannEntropy ρ +
        vonNeumannEntropy
          (QuantumChannel.traceOutRight (QuantumChannel.traceOutLeft ρ)) ≤
      vonNeumannEntropy (QuantumChannel.traceOutThird ρ) +
        vonNeumannEntropy (QuantumChannel.traceOutLeft ρ) := by
  have hA : (0 : L ℋA) ≤ QuantumChannel.traceOutRight ρ := by
    simpa using traceOutRight_le_traceOutRight hρ
  have hBC : (0 : L (ℋB ⊗[ℂ] ℋC)) ≤
      QuantumChannel.traceOutLeft ρ := by
    simpa only [CPTP.traceOutLeft_toFun] using
      map_nonneg
        (CPTP.traceOutLeft ℋA (ℋB ⊗[ℂ] ℋC)).toCompletelyPositiveMap hρ
  have hAB : (0 : L (ℋA ⊗[ℂ] ℋB)) ≤
      QuantumChannel.traceOutThird ρ := by
    simpa only [CPTP.traceOutThird_toFun] using
      map_nonneg
        (CPTP.traceOutThird ℋA ℋB ℋC).toCompletelyPositiveMap hρ
  have hB : (0 : L ℋB) ≤
      QuantumChannel.traceOutRight (QuantumChannel.traceOutLeft ρ) := by
    simpa using traceOutRight_le_traceOutRight hBC
  let cABC : ℝ :=
    (Module.finrank ℂ (ℋA ⊗[ℂ] (ℋB ⊗[ℂ] ℋC)) : ℝ)⁻¹
  let cA : ℝ := cABC * (Module.finrank ℂ (ℋB ⊗[ℂ] ℋC) : ℝ)
  let cBC : ℝ := cABC * (Module.finrank ℂ ℋA : ℝ)
  let cAB : ℝ := cABC * (Module.finrank ℂ ℋC : ℝ)
  let cB : ℝ := cBC * (Module.finrank ℂ ℋC : ℝ)
  let ρε : ℝ → L (ℋA ⊗[ℂ] (ℋB ⊗[ℂ] ℋC)) := fun lam =>
    ((1 - lam : ℝ) : ℂ) • ρ + ((lam * cABC : ℝ) : ℂ) • 1
  have hcABC : 0 < cABC := by
    dsimp [cABC]
    exact inv_pos.mpr (by exact_mod_cast
      (Module.finrank_pos (R := ℂ)
        (M := ℋA ⊗[ℂ] (ℋB ⊗[ℂ] ℋC))))
  have hcA : 0 < cA :=
    mul_pos hcABC (by exact_mod_cast Module.finrank_pos)
  have hcBC : 0 < cBC :=
    mul_pos hcABC (by exact_mod_cast Module.finrank_pos)
  have hcAB : 0 < cAB :=
    mul_pos hcABC (by exact_mod_cast Module.finrank_pos)
  have hcB : 0 < cB :=
    mul_pos hcBC (by exact_mod_cast Module.finrank_pos)
  have hρε_nonneg (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
      0 ≤ ρε lam :=
    nonneg_of_pdSetLM
      (faithful_mix_mem_pdSetLM hρ hcABC hlam0 hlam1)
  have hcABC_dim : cABC *
      (Module.finrank ℂ (ℋA ⊗[ℂ] (ℋB ⊗[ℂ] ℋC)) : ℝ) = 1 := by
    dsimp [cABC]
    exact inv_mul_cancel₀ (by exact_mod_cast
      (Module.finrank_pos (R := ℂ)
        (M := ℋA ⊗[ℂ] (ℋB ⊗[ℂ] ℋC))).ne')
  have hρε_trace (lam : ℝ) :
      Tr (ρε lam) = 1 := by
    simpa only [ρε] using
      faithful_mix_trace_one (ρ := ρ) hTr hcABC_dim lam
  have hSSA : ∀ᶠ lam : ℝ in 𝓝[>] (0 : ℝ),
      vonNeumannEntropy (ρε lam) +
          vonNeumannEntropy (QuantumChannel.traceOutRight
            (QuantumChannel.traceOutLeft (ρε lam))) ≤
        vonNeumannEntropy (QuantumChannel.traceOutThird (ρε lam)) +
          vonNeumannEntropy (QuantumChannel.traceOutLeft (ρε lam)) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with lam hlam0 hlam1
    apply strongSubadditivity (ρε lam)
      (hρε_nonneg lam hlam0 hlam1.le) (hρε_trace lam)
    · change QuantumChannel.traceOutRight
        (((1 - lam : ℝ) : ℂ) • ρ +
          ((lam * cABC : ℝ) : ℂ) • 1) ∈ pdSetLM
      rw [traceOutRight_faithful_mix]
      exact faithful_mix_mem_pdSetLM hA hcA hlam0 hlam1.le
    · change QuantumChannel.traceOutLeft
        (((1 - lam : ℝ) : ℂ) • ρ +
          ((lam * cABC : ℝ) : ℂ) • 1) ∈ pdSetLM
      rw [traceOutLeft_faithful_mix]
      exact faithful_mix_mem_pdSetLM hBC hcBC hlam0 hlam1.le
  have hρ_lim : Filter.Tendsto
      (fun lam : ℝ => vonNeumannEntropy (ρε lam))
      (𝓝[>] (0 : ℝ)) (𝓝 (vonNeumannEntropy ρ)) := by
    simpa only [ρε] using
      (tendsto_vonNeumannEntropy_faithful_mix hρ hcABC)
  have hBC_lim : Filter.Tendsto
      (fun lam : ℝ => vonNeumannEntropy
        (QuantumChannel.traceOutLeft (ρε lam)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (vonNeumannEntropy (QuantumChannel.traceOutLeft ρ))) := by
    simpa only [ρε, cBC, traceOutLeft_faithful_mix] using
      (tendsto_vonNeumannEntropy_faithful_mix hBC hcBC)
  have hAB_lim : Filter.Tendsto
      (fun lam : ℝ => vonNeumannEntropy (QuantumChannel.traceOutThird (ρε lam)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (vonNeumannEntropy (QuantumChannel.traceOutThird ρ))) := by
    simpa only [ρε, cAB, traceOutThird_faithful_mix] using
      (tendsto_vonNeumannEntropy_faithful_mix hAB hcAB)
  have hB_lim : Filter.Tendsto
      (fun lam : ℝ => vonNeumannEntropy
        (QuantumChannel.traceOutRight
          (QuantumChannel.traceOutLeft (ρε lam))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (vonNeumannEntropy
        (QuantumChannel.traceOutRight
          (QuantumChannel.traceOutLeft ρ)))) := by
    simpa only [ρε, cBC, cB, traceOutLeft_faithful_mix,
      traceOutRight_faithful_mix] using
      (tendsto_vonNeumannEntropy_faithful_mix hB hcB)
  haveI : (𝓝[>] (0 : ℝ)).NeBot :=
    nhdsWithin_Ioi_neBot (le_refl 0)
  exact le_of_tendsto_of_tendsto
    (hρ_lim.add hB_lim) (hAB_lim.add hBC_lim) hSSA

end SSA

end VonNeumann
