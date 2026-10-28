/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Interface
import Quantum.QuantumEntropy.RenyiDPI.Petz.TracePower
import Quantum.QuantumEntropy.Common.TensorDensitySupport.GSLCore
import Quantum.QuantumEntropy.TensorCFCLMCompat.GSLCore




open scoped Quantum.TraceInequality.Loewner

/-! # Petz tensor additivity on density operators

The four density hypotheses exclude the zero-first-input convention. The
proof uses the same raw tensor CFC and density lemmas as the legacy finite
additivity theorem, without importing its OPT laws or DPI dependencies.
-/

namespace RenyiDPI

open QuantumState QuantumEntropy.TensorDensitySupport
open scoped ComplexOrder TensorProduct

universe u v

/-- Multiplicativity of Q on nonnegative tensor factors. -/
theorem petzTracePower_tensorMap
    {H : Type u} {K : Type v} [Qudit H] [Qudit K]
    [Nontrivial H] [Nontrivial K] [Nontrivial (H ⊗[ℂ] K)]
    {α : ℝ} (ρ₁ σ₁ : L H) (ρ₂ σ₂ : L K) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hρ₁ : 0 ≤ ρ₁) (hσ₁ : 0 ≤ σ₁) (hρ₂ : 0 ≤ ρ₂) (hσ₂ : 0 ≤ σ₂) :
    petzTracePower α (TensorProduct.map ρ₁ ρ₂) (TensorProduct.map σ₁ σ₂) =
      petzTracePower α ρ₁ σ₁ * petzTracePower α ρ₂ σ₂ := by
  rw [petzTracePower_eq_trace_rpow_mul hα
    (tensorMap_nonneg ρ₁ ρ₂ hρ₁ hρ₂) (tensorMap_nonneg σ₁ σ₂ hσ₁ hσ₂)]
  -- The tensor power lemma and the Petz trace power carry instance terms that agree only after
  -- unfolding, so these steps rewrite up to definitional unfolding.
  erw [TensorCFC.rpow_tensorProduct_lm ρ₁ ρ₂ α hρ₁ hρ₂,
    TensorCFC.rpow_tensorProduct_lm σ₁ σ₂ (1 - α) hσ₁ hσ₂]
  rw [← TensorProduct.map_mul, LinearMap.trace_tensorProduct', Complex.mul_re,
    petzTracePower_eq_trace_rpow_mul hα hρ₁ hσ₁,
    petzTracePower_eq_trace_rpow_mul hα hρ₂ hσ₂]
  erw [(Complex.nonneg_iff.mp (trace_rpow_mul_nonneg α ρ₁ σ₁)).2.symm, zero_mul, sub_zero]
  rfl

private theorem divNN_zero {G : Type*} [Qudit G] [Nontrivial G] {α : ℝ} {r s : L G}
    (hn : r ≠ 0) (hq : petzTracePower α r s = 0) : petzDivNN α r s = ⊤ := by
  unfold petzDivNN
  exact if_pos ⟨hn, hq⟩

private theorem divNN_finite {G : Type*} [Qudit G] [Nontrivial G] {α : ℝ} {r s : L G}
    (hq : petzTracePower α r s ≠ 0) : petzDivNN α r s = (petzDiv α r s : EReal) := by
  unfold petzDivNN
  exact if_neg (fun h => hq h.2)

/-- The natural-log extended Petz divergence is additive on density pairs. -/
theorem petzTensorAdditiveOnDensity : PetzTensorAdditiveOnDensity.{u, v} := by
  intro H K _ _ _ _ _ α ρ₁ σ₁ ρ₂ σ₂ hα hρ₁ hσ₁ hρ₂ hσ₂
  have hρT := isDensity_tensorMap ρ₁ ρ₂ hρ₁ hρ₂
  have hσT := isDensity_tensorMap σ₁ σ₂ hσ₁ hσ₂
  have hQ := petzTracePower_tensorMap ρ₁ σ₁ ρ₂ σ₂ hα
    ((LinearMap.nonneg_iff_isPositive _).mpr hρ₁.1)
    ((LinearMap.nonneg_iff_isPositive _).mpr hσ₁.1)
    ((LinearMap.nonneg_iff_isPositive _).mpr hρ₂.1)
    ((LinearMap.nonneg_iff_isPositive _).mpr hσ₂.1)
  have hn₁ := density_ne_zero hρ₁
  have hn₂ := density_ne_zero hρ₂
  have hnT := density_ne_zero hρT
  by_cases hQ₁ : petzTracePower α ρ₁ σ₁ = 0
  · rw [divNN_zero hnT (by rw [hQ, hQ₁, zero_mul]), divNN_zero hn₁ hQ₁]
    by_cases hQ₂ : petzTracePower α ρ₂ σ₂ = 0
    · rw [divNN_zero hn₂ hQ₂, EReal.top_add_top]
    · rw [divNN_finite hQ₂, EReal.top_add_coe]
  by_cases hQ₂ : petzTracePower α ρ₂ σ₂ = 0
  · rw [divNN_zero hnT (by rw [hQ, hQ₂, mul_zero]), divNN_finite hQ₁, divNN_zero hn₂ hQ₂,
      EReal.coe_add_top]
  rw [divNN_finite (by rw [hQ]; exact mul_ne_zero hQ₁ hQ₂), divNN_finite hQ₁, divNN_finite hQ₂,
    ← EReal.coe_add]
  congr 1
  unfold petzDiv
  rw [hρT.2, hρ₁.2, hρ₂.2, Complex.one_re, div_one, div_one, div_one,
    hQ, Real.log_mul hQ₁ hQ₂, add_div]

end RenyiDPI
