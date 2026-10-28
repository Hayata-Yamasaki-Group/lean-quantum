/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.UmegakiDPI.Interface
import Quantum.QuantumEntropy.RenyiDPI.Interface
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.AlphaOne

/-! # Positive-definite Umegaki data processing from Rényi limits

The nonnegative Rényi data-processing inequality and its one-sided order-one
limit imply the positive-definite Umegaki data-processing inequality.
-/

namespace UmegakiDPI

open QuantumState QuantumChannel QuantumEntropy SandwichedRenyiRelativeEntropy
open scoped ComplexOrder Topology

universe u

private local instance {H : Type u} [Qudit H] :
    ContinuousFunctionalCalculus ℝ (L H) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

private lemma petzDivNN_eq_coe_of_pd
    {H : Type u} [Qudit H] [Nontrivial H] (α : ℝ) {ρ σ : L H}
    (hρ : ρ ∈ pdSetLM (ℋ := H)) (hσ : σ ∈ pdSetLM (ℋ := H)) :
    RenyiDPI.petzDivNN α ρ σ = (RenyiDPI.petzDiv α ρ σ : EReal) := by
  let X := CFC.rpow ρ α
  let Y := CFC.rpow σ (1 - α)
  have hX : IsStrictlyPositive X :=
    ((pdSetLM_strictPositivity_certificate ρ).mp hρ).rpow
  have hY : IsStrictlyPositive Y :=
    ((pdSetLM_strictPositivity_certificate σ).mp hσ).rpow
  have hZ : CFC.sqrt X * CFC.sqrt Y ≠ 0 :=
    (hX.sqrt.isUnit.mul hY.sqrt.isUnit).ne_zero
  have ht := QuantumEntropy.trace_re_pos_of_ne_zero (star_mul_self_nonneg _)
    ((not_congr (CStarRing.star_mul_self_eq_zero_iff _)).mpr hZ)
  have htrace :
      Tr (star (CFC.sqrt X * CFC.sqrt Y) * (CFC.sqrt X * CFC.sqrt Y)) =
        Tr (X * Y) := by
    rw [star_mul, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg X)).star_eq,
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg Y)).star_eq]
    calc
      _ = Tr (CFC.sqrt Y * ((CFC.sqrt X * CFC.sqrt X) * CFC.sqrt Y)) := by
        simp only [mul_assoc]
      _ = Tr (CFC.sqrt Y * (X * CFC.sqrt Y)) := by
        rw [CFC.sqrt_mul_sqrt_self X hX.nonneg]
      _ = Tr ((X * CFC.sqrt Y) * CFC.sqrt Y) := LinearMap.trace_mul_comm _ _ _
      _ = Tr (X * Y) := by rw [mul_assoc, CFC.sqrt_mul_sqrt_self Y hY.nonneg]
  have hQ : 0 < RenyiDPI.petzTracePower α ρ σ := by
    unfold RenyiDPI.petzTracePower
    rw [← CFCTransport.cfc_rpow_toCLM ρ α, ← CFCTransport.cfc_rpow_toCLM σ (1 - α)]
    change 0 < (Tr (X * Y)).re
    rwa [htrace] at ht
  simp [RenyiDPI.petzDivNN, ne_of_gt hQ]

/-- Petz data processing and its order-one limit imply positive-definite Umegaki data processing. -/
theorem monotoneOnPosDef_of_petz (p : RenyiDPI.PetzSide.{u, u}) :
    MonotoneOnPosDef.{u} := by
  intro H _ _ K _ _ E ρ σ hρ hσ hEρ hEσ
  have hTarget := p.limitAtOne hEρ hEσ
  have hSource := p.limitAtOne hρ hσ
  refine le_of_tendsto_of_tendsto hTarget hSource ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with α hα
  have hDPI := p.monotoneOnNonNeg E hα (nonneg_of_pdSetLM hρ) (nonneg_of_pdSetLM hσ)
  rw [petzDivNN_eq_coe_of_pd α hEρ hEσ, petzDivNN_eq_coe_of_pd α hρ hσ] at hDPI
  exact_mod_cast hDPI

end UmegakiDPI
