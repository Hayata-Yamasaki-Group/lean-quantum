/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.RenyiDPI.Interface
import Quantum.QuantumEntropy.Common.OperatorCFC
import Quantum.QuantumEntropy.Common.TraceRe
import Quantum.QuantumEntropy.CFCDeriv
import Quantum.QuantumEntropy.Common.Umegaki.GSLCore
import Quantum.QuantumEntropy.Common.TracePositiveDefinite






open scoped Quantum.TraceInequality.Loewner

/-!
# Petz trace-power differentiation at α = 1

This analytic core preserves `UmegakiDPI.tendsto_tracePower_quotient_log`.
It imports neither data processing nor a provider/selector. The derivative of
log Q yields the left limit of the fixed divergence itself.
-/

namespace UmegakiDPI

open QuantumState QuantumChannel QuantumEntropy
open SandwichedRenyiRelativeEntropy
open scoped QuantumEntropy
open scoped ComplexOrder MatrixOrder Topology

noncomputable section

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- Exponent differentiation of the Petz trace power at one. -/
theorem hasDerivAt_tracePower_one
    {a b : B ℋ} (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    HasDerivAt (fun p : ℝ => realTrace (CFC.rpow a p * CFC.rpow b (1 - p)))
      (realTrace (a * (CFC.log a - CFC.log b))) 1 := by
  have hOneSub : HasDerivAt (fun p : ℝ => 1 - p) (-1) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).const_sub 1
  have haPow :
      HasDerivAt (fun s : ℝ => CFC.rpow a s)
        (CFC.rpow a 1 * CFC.log a) 1 := by
    simpa only [QuantumEntropy.operatorContinuousFunctionalCalculus] using
      CFC.hasDerivAt_rpow_exponent ha (1 : ℝ)
  have hbPow :
      HasDerivAt (fun p : ℝ => CFC.rpow b (1 - p))
        ((-1 : ℝ) • (CFC.rpow b (1 - (1 : ℝ)) * CFC.log b)) 1 := by
    simpa only [QuantumEntropy.operatorContinuousFunctionalCalculus] using
      CFC.hasDerivAt_rpow_exponent_comp hb hOneSub
  have hProduct :
      HasDerivAt
        (fun p : ℝ => CFC.rpow a p * CFC.rpow b (1 - p))
        (a * (CFC.log a - CFC.log b)) 1 := by
    simpa [CFC.rpow_one a ha.nonneg, CFC.rpow_zero b hb.nonneg, mul_add,
      mul_neg, sub_eq_add_neg] using haPow.mul hbPow
  have hTrace :
      HasDerivAt
        (fun p : ℝ => realTrace (CFC.rpow a p * CFC.rpow b (1 - p)))
        (realTrace (a * (CFC.log a - CFC.log b))) 1 := by
    simpa [realTrace] using
      QuantumState.hasDerivAt_reTrace_mul_left (1 : B ℋ) hProduct
  exact hTrace

/-- The left trace-power quotient converges to the Umegaki numerator. -/
theorem tendsto_tracePower_quotient_log
    {a b : B ℋ} (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b) :
    Filter.Tendsto
      (fun p : ℝ =>
        (realTrace a - realTrace (CFC.rpow a p * CFC.rpow b (1 - p))) / (1 - p))
      (𝓝[<] (1 : ℝ))
      (𝓝 (realTrace (a * (CFC.log a - CFC.log b)))) := by
  have haOne : CFC.rpow a (1 : ℝ) = a := by
    rw [CFC.rpow_eq_pow]
    exact CFC.rpow_one a ha.nonneg
  have hbZero : CFC.rpow b (0 : ℝ) = 1 := by
    rw [CFC.rpow_eq_pow]
    exact CFC.rpow_zero b hb.nonneg
  have hTrace := hasDerivAt_tracePower_one ha hb
  have hSlope := hTrace.tendsto_slope.mono_left (nhdsLT_le_nhdsNE (1 : ℝ))
  refine hSlope.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with p hp
  have hp_ne : p ≠ 1 := ne_of_lt hp.2
  have hAtOne :
      realTrace (CFC.rpow a (1 : ℝ) * CFC.rpow b (1 - (1 : ℝ))) = realTrace a := by
    rw [haOne, show (1 : ℝ) - 1 = 0 by norm_num, hbZero, mul_one]
  rw [slope_def_field]
  rw [hAtOne]
  have hOneSub_ne : 1 - p ≠ 0 := sub_ne_zero.mpr hp_ne.symm
  have hSubOne_ne : p - 1 ≠ 0 := sub_ne_zero.mpr hp_ne
  rw [div_eq_div_iff hSubOne_ne hOneSub_ne]
  ring

end

end UmegakiDPI

namespace RenyiDPI

open QuantumState QuantumEntropy SandwichedRenyiRelativeEntropy
open scoped QuantumEntropy ComplexOrder Topology

universe u

/-- The fixed Petz divergence itself tends to the normalized Umegaki quantity
from the left. The logarithmic derivative, not the trace-power quotient, is used. -/
theorem petzLimitAtOneOnPosDef : PetzLimitAtOneOnPosDef.{u} := by
  intro H _ _ ρ σ hρ hσ
  have ha : IsStrictlyPositive ρ.toContinuousLinearMap :=
    (GeneralizedPerspectiveFunction.pdSet_membership_certificate _).mp hρ
  have hb : IsStrictlyPositive σ.toContinuousLinearMap :=
    (GeneralizedPerspectiveFunction.pdSet_membership_certificate _).mp hσ
  have htr : 0 < (Tr ρ).re := trace_re_pos_of_pdSetLM hρ
  have hOne : petzTracePower 1 ρ σ = (Tr ρ).re := by
    unfold petzTracePower
    rw [show (1 : ℝ) - 1 = 0 by norm_num]
    change realTrace (CFC.rpow ρ.toContinuousLinearMap 1 *
      CFC.rpow σ.toContinuousLinearMap 0) = (Tr ρ).re
    simp only [CFC.rpow_eq_pow, CFC.rpow_one _ ha.nonneg,
      CFC.rpow_zero _ hb.nonneg, mul_one, realTrace_toCLM]
  have hderiv := UmegakiDPI.hasDerivAt_tracePower_one ha hb
  change HasDerivAt (fun p : ℝ => petzTracePower p ρ σ)
    (realTrace (ρ.toContinuousLinearMap *
      (CFC.log ρ.toContinuousLinearMap - CFC.log σ.toContinuousLinearMap))) 1 at hderiv
  have hlog : HasDerivAt (fun p : ℝ => Real.log (petzTracePower p ρ σ))
      (umegakiNorm ρ σ) 1 := by
    simpa only [hOne, umegakiNorm_eq_toContinuousLinearMap, realTrace] using
      hderiv.log (by rw [hOne]; exact htr.ne')
  have hpos : ∀ᶠ p : ℝ in 𝓝 1, 0 < petzTracePower p ρ σ :=
    hderiv.continuousAt.tendsto.eventually
      (lt_mem_nhds (show 0 < petzTracePower 1 ρ σ by rwa [hOne]))
  refine (hlog.tendsto_slope.mono_left (nhdsLT_le_nhdsNE (1 : ℝ))).congr' ?_
  filter_upwards [hpos.filter_mono nhdsWithin_le_nhds] with p hp
  rw [slope_def_field, hOne, petzDiv, Real.log_div hp.ne' htr.ne']

end RenyiDPI
