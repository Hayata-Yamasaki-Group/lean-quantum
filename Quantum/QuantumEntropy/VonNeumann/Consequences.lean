/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.VonNeumann.SSA
import Quantum.QuantumEntropy.UmegakiDPI.NonNegLift
import Quantum.QuantumEntropy.Common.TensorDensitySupport.GSLCoreGeneralizedStein
import Quantum.QuantumEntropy.Common.TraceReGeneralizedStein
import Quantum.QuantumEntropy.SandwichedRenyiRelativeEntropy
import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneCore
import Quantum.QuantumEntropy.UmegakiDPI.ViaPetz.FromRenyi.GSLCore

/-!
# Direct consequences of strong subadditivity

The conditional-entropy form of strong subadditivity,

`S(ρ_ABC) - S(ρ_BC) ≤ S(ρ_AB) - S(ρ_B)`,

under exactly the same faithful (positive-definite) marginal hypotheses as
`strongSubadditivity`, together with the corresponding theorem for arbitrary
states obtained from `strongSubadditivity_of_state`.

This module also derives state-level non-negativity of `umegakiNorm` from
data processing for the completely depolarizing channel, and uses it to prove
entropy subadditivity and non-negativity of the mutual-information expression.
-/

namespace VonNeumann

open QuantumState QuantumChannel TensorProduct
open GeneralizedPerspectiveFunction
open SandwichedRenyiRelativeEntropy
open scoped ComplexOrder Topology

universe u

section UmegakiNonneg

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

/-- The normalized Umegaki relative entropy of two states is non-negative
when the support of the first is contained in that of the second. -/
theorem umegakiNorm_nonneg_of_state
    (ρ σ : L ℋ)
    (hρ : 0 ≤ ρ)
    (hTrρ : Tr ρ = 1)
    (hσ : 0 ≤ σ)
    (hTrσ : Tr σ = 1)
    (hsupp : SupportLE ρ σ) :
    0 ≤ umegakiNorm ρ σ := by
  have hDPI := UmegakiDPI.monotoneNormOnNonNeg
    (depolarizingChannel ℋ ℋ) hρ hσ hsupp
  change umegakiNorm
      ((Tr ρ / (Module.finrank ℂ ℋ : ℂ)) • (1 : L ℋ))
      ((Tr σ / (Module.finrank ℂ ℋ : ℂ)) • (1 : L ℋ)) ≤
    umegakiNorm ρ σ at hDPI
  rw [hTrρ, hTrσ] at hDPI
  simpa [umegakiNorm_eq_toContinuousLinearMap] using hDPI

end UmegakiNonneg

variable {ℋA ℋB ℋC : Type u} [Qudit ℋA] [Qudit ℋB] [Qudit ℋC]
variable [Nontrivial ℋA] [Nontrivial ℋB] [Nontrivial ℋC]

/-- **Subadditivity of the von Neumann entropy**:
`S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)`. This is the faithful-marginal version: both
`ρ_A` and `ρ_B` are assumed positive definite. The general state version is
`subadditivity_of_state` below. -/
theorem subadditivity
    (ρ : L (ℋA ⊗[ℂ] ℋB))
    (hρ : 0 ≤ ρ)
    (hTr : Tr ρ = 1)
    (hA : QuantumChannel.traceOutRight ρ ∈ pdSetLM)
    (hB : QuantumChannel.traceOutLeft ρ ∈ pdSetLM) :
    vonNeumannEntropy ρ ≤
      vonNeumannEntropy (QuantumChannel.traceOutRight ρ) +
        vonNeumannEntropy (QuantumChannel.traceOutLeft ρ) := by
  have hσ_pd : TensorProduct.map
      (QuantumChannel.traceOutRight ρ) (QuantumChannel.traceOutLeft ρ) ∈ pdSetLM :=
    pdSetLM_tensorMap hA hB
  have hσ_nonneg : (0 : L (ℋA ⊗[ℂ] ℋB)) ≤
      TensorProduct.map
        (QuantumChannel.traceOutRight ρ) (QuantumChannel.traceOutLeft ρ) :=
    nonneg_of_pdSetLM hσ_pd
  have hsupp : SupportLE ρ
      (TensorProduct.map
        (QuantumChannel.traceOutRight ρ) (QuantumChannel.traceOutLeft ρ)) :=
    suppLE_of_pdSetLM_right _ hσ_pd
  have hTrA :
      Tr (QuantumChannel.traceOutRight ρ) = 1 := by
    rw [trace_traceOutRight]
    exact hTr
  have hTrB :
      Tr (QuantumChannel.traceOutLeft ρ) = 1 := by
    rw [trace_traceOutLeft]
    exact hTr
  have hTrσ : Tr (TensorProduct.map
      (QuantumChannel.traceOutRight ρ) (QuantumChannel.traceOutLeft ρ)) = 1 := by
    rw [LinearMap.trace_tensorProduct',
      hTrA, hTrB, mul_one]
  have hD := umegakiNorm_nonneg_of_state ρ
    (TensorProduct.map
      (QuantumChannel.traceOutRight ρ) (QuantumChannel.traceOutLeft ρ))
    hρ hTr hσ_nonneg hTrσ hsupp
  rw [umegakiNorm_state_tensor_marginals ρ hA hB hTr] at hD
  linarith

/-- **Subadditivity of the von Neumann entropy for an arbitrary
finite-dimensional state**:
`S(ρ_AB) ≤ S(ρ_A) + S(ρ_B)`, without faithful marginal hypotheses. -/
theorem subadditivity_of_state
    (ρ : L (ℋA ⊗[ℂ] ℋB))
    (hρ : 0 ≤ ρ)
    (hTr : Tr ρ = 1) :
    vonNeumannEntropy ρ ≤
      vonNeumannEntropy (QuantumChannel.traceOutRight ρ) +
        vonNeumannEntropy (QuantumChannel.traceOutLeft ρ) := by
  have hA : (0 : L ℋA) ≤ QuantumChannel.traceOutRight ρ := by
    simpa using traceOutRight_le_traceOutRight hρ
  have hB : (0 : L ℋB) ≤ QuantumChannel.traceOutLeft ρ := by
    simpa only [CPTP.traceOutLeft_toFun] using
      map_nonneg (CPTP.traceOutLeft ℋA ℋB).toCompletelyPositiveMap hρ
  let cAB : ℝ := (Module.finrank ℂ (ℋA ⊗[ℂ] ℋB) : ℝ)⁻¹
  let cA : ℝ := cAB * (Module.finrank ℂ ℋB : ℝ)
  let cB : ℝ := cAB * (Module.finrank ℂ ℋA : ℝ)
  let ρε : ℝ → L (ℋA ⊗[ℂ] ℋB) := fun lam =>
    ((1 - lam : ℝ) : ℂ) • ρ + ((lam * cAB : ℝ) : ℂ) • 1
  have hcAB : 0 < cAB := by
    dsimp [cAB]
    exact inv_pos.mpr (by exact_mod_cast
      (Module.finrank_pos (R := ℂ) (M := ℋA ⊗[ℂ] ℋB)))
  have hcA : 0 < cA :=
    mul_pos hcAB (by exact_mod_cast Module.finrank_pos)
  have hcB : 0 < cB :=
    mul_pos hcAB (by exact_mod_cast Module.finrank_pos)
  have hρε_nonneg (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
      0 ≤ ρε lam :=
    nonneg_of_pdSetLM
      (faithful_mix_mem_pdSetLM hρ hcAB hlam0 hlam1)
  have hcAB_dim :
      cAB * (Module.finrank ℂ (ℋA ⊗[ℂ] ℋB) : ℝ) = 1 := by
    dsimp [cAB]
    exact inv_mul_cancel₀ (by exact_mod_cast
      (Module.finrank_pos (R := ℂ) (M := ℋA ⊗[ℂ] ℋB)).ne')
  have hρε_trace (lam : ℝ) : Tr (ρε lam) = 1 := by
    simpa only [ρε] using
      faithful_mix_trace_one (ρ := ρ) hTr hcAB_dim lam
  have hSub : ∀ᶠ lam : ℝ in 𝓝[>] (0 : ℝ),
      vonNeumannEntropy (ρε lam) ≤
        vonNeumannEntropy (QuantumChannel.traceOutRight (ρε lam)) +
          vonNeumannEntropy (QuantumChannel.traceOutLeft (ρε lam)) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with lam hlam0 hlam1
    apply subadditivity (ρε lam)
      (hρε_nonneg lam hlam0 hlam1.le) (hρε_trace lam)
    · change QuantumChannel.traceOutRight
        (((1 - lam : ℝ) : ℂ) • ρ +
          ((lam * cAB : ℝ) : ℂ) • 1) ∈ pdSetLM
      rw [traceOutRight_faithful_mix]
      exact faithful_mix_mem_pdSetLM hA hcA hlam0 hlam1.le
    · change QuantumChannel.traceOutLeft
        (((1 - lam : ℝ) : ℂ) • ρ +
          ((lam * cAB : ℝ) : ℂ) • 1) ∈ pdSetLM
      rw [traceOutLeft_faithful_mix]
      exact faithful_mix_mem_pdSetLM hB hcB hlam0 hlam1.le
  have hρ_lim : Filter.Tendsto
      (fun lam : ℝ => vonNeumannEntropy (ρε lam))
      (𝓝[>] (0 : ℝ)) (𝓝 (vonNeumannEntropy ρ)) := by
    simpa only [ρε] using
      (tendsto_vonNeumannEntropy_faithful_mix hρ hcAB)
  have hA_lim : Filter.Tendsto
      (fun lam : ℝ => vonNeumannEntropy
        (QuantumChannel.traceOutRight (ρε lam)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (vonNeumannEntropy (QuantumChannel.traceOutRight ρ))) := by
    simpa only [ρε, cA, traceOutRight_faithful_mix] using
      (tendsto_vonNeumannEntropy_faithful_mix hA hcA)
  have hB_lim : Filter.Tendsto
      (fun lam : ℝ => vonNeumannEntropy
        (QuantumChannel.traceOutLeft (ρε lam)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (vonNeumannEntropy (QuantumChannel.traceOutLeft ρ))) := by
    simpa only [ρε, cB, traceOutLeft_faithful_mix] using
      (tendsto_vonNeumannEntropy_faithful_mix hB hcB)
  haveI : (𝓝[>] (0 : ℝ)).NeBot :=
    nhdsWithin_Ioi_neBot (le_refl 0)
  exact le_of_tendsto_of_tendsto hρ_lim (hA_lim.add hB_lim) hSub

/-- The mutual information
`S(ρ_A) + S(ρ_B) - S(ρ_AB)` is non-negative. This result inherits the
faithful-marginal restriction of `subadditivity`. The general state version is
`mutualInformation_nonneg_of_state` below. -/
theorem mutualInformation_nonneg
    (ρ : L (ℋA ⊗[ℂ] ℋB))
    (hρ : 0 ≤ ρ)
    (hTr : Tr ρ = 1)
    (hA : QuantumChannel.traceOutRight ρ ∈ pdSetLM)
    (hB : QuantumChannel.traceOutLeft ρ ∈ pdSetLM) :
    0 ≤ vonNeumannEntropy (QuantumChannel.traceOutRight ρ) +
        vonNeumannEntropy (QuantumChannel.traceOutLeft ρ) -
      vonNeumannEntropy ρ := by
  linarith [subadditivity ρ hρ hTr hA hB]

/-- The mutual-information expression is non-negative for an arbitrary
finite-dimensional state, without faithful marginal hypotheses. -/
theorem mutualInformation_nonneg_of_state
    (ρ : L (ℋA ⊗[ℂ] ℋB))
    (hρ : 0 ≤ ρ)
    (hTr : Tr ρ = 1) :
    0 ≤ vonNeumannEntropy (QuantumChannel.traceOutRight ρ) +
        vonNeumannEntropy (QuantumChannel.traceOutLeft ρ) -
      vonNeumannEntropy ρ := by
  linarith [subadditivity_of_state ρ hρ hTr]

/-- **Conditional-entropy form of strong subadditivity**:
`S(A | BC) ≤ S(A | B)`. This is the faithful-marginal version inherited from
`strongSubadditivity`: `ρ_A` and `ρ_BC` are assumed positive definite, and
faithfulness of `ρ_B` follows by partial trace. The general state version is
`conditionalEntropySubadditivity_of_state` below. -/
theorem conditionalEntropySubadditivity
    (ρ : L (ℋA ⊗[ℂ] (ℋB ⊗[ℂ] ℋC)))
    (hρ : 0 ≤ ρ)
    (hTr : Tr ρ = 1)
    (hA : QuantumChannel.traceOutRight ρ ∈ pdSetLM)
    (hBC : QuantumChannel.traceOutLeft ρ ∈ pdSetLM) :
    vonNeumannEntropy ρ -
        vonNeumannEntropy (QuantumChannel.traceOutLeft ρ) ≤
      vonNeumannEntropy (QuantumChannel.traceOutThird ρ) -
        vonNeumannEntropy
          (QuantumChannel.traceOutRight (QuantumChannel.traceOutLeft ρ)) := by
  linarith [strongSubadditivity ρ hρ hTr hA hBC]

/-- **Conditional-entropy form of strong subadditivity for an arbitrary
finite-dimensional state**: `S(A | BC) ≤ S(A | B)`, without faithful
marginal hypotheses. -/
theorem conditionalEntropySubadditivity_of_state
    (ρ : L (ℋA ⊗[ℂ] (ℋB ⊗[ℂ] ℋC)))
    (hρ : 0 ≤ ρ)
    (hTr : Tr ρ = 1) :
    vonNeumannEntropy ρ -
        vonNeumannEntropy (QuantumChannel.traceOutLeft ρ) ≤
      vonNeumannEntropy (QuantumChannel.traceOutThird ρ) -
        vonNeumannEntropy
          (QuantumChannel.traceOutRight (QuantumChannel.traceOutLeft ρ)) := by
  linarith [strongSubadditivity_of_state ρ hρ hTr]

end VonNeumann
