/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Interface
import Quantum.QuantumEntropy.Common.TensorDensitySupport.GSLCore
import Quantum.QuantumEntropy.TensorCFCLMCompat.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiBase.NonNeg.Continuity




/-! # Natural-log sandwiched tensor additivity

This proof uses raw tensor CFC, density and support lemmas only. In particular,
it does not import Gour's all-order tensor theorem (whose endpoint branches
return to Petz laws and Umegaki DPI). Density excludes zero tensor factors.
-/

namespace RenyiDPI

open QuantumState SandwichedRenyiRelativeEntropy QuantumEntropy.TensorDensitySupport
open scoped ComplexOrder TensorProduct

universe u v

/-- The finite support branch of the existing extended divergence. -/
theorem sandwichedDivNN_eq_coe_of_supportLE
    {H : Type*} [Qudit H] [Nontrivial H] {α : ℝ} {ρ σ : L H}
    (hα : 1 < α) (hsupp : SupportLE ρ σ) :
    sandwichedRenyiDivNN α ρ σ = (sandwichedRenyiDiv α ρ σ : EReal) := by
  unfold sandwichedRenyiDivNN
  rw [if_neg]
  rintro (⟨_, h⟩ | ⟨h, _⟩)
  · exact h hsupp
  · linarith

/-- Support mismatch gives the infinite branch, independently of normalization. -/
theorem sandwichedDivNN_eq_top_of_not_supportLE
    {H : Type*} [Qudit H] [Nontrivial H] {α : ℝ} {ρ σ : L H}
    (hα : 1 < α) (hsupp : ¬ SupportLE ρ σ) :
    sandwichedRenyiDivNN α ρ σ = ⊤ := by
  unfold sandwichedRenyiDivNN
  exact if_pos (Or.inl ⟨hα, hsupp⟩)

/-- The extended divergence never takes the bottom value. -/
theorem sandwichedDivNN_ne_bot
    {H : Type*} [Qudit H] [Nontrivial H] (α : ℝ) (ρ σ : L H) :
    sandwichedRenyiDivNN α ρ σ ≠ ⊥ := by
  unfold sandwichedRenyiDivNN
  split_ifs
  · exact top_ne_bot
  · exact EReal.coe_ne_bot _

/-- Multiplicativity of the raw quasi-entropy from tensor CFC, including negative
inner exponents. No support condition is needed for this totalized CFC identity. -/
theorem sandwichedQuasi_tensorMap
    {H : Type u} {K : Type v} [Qudit H] [Qudit K]
    [Nontrivial H] [Nontrivial K] [Nontrivial (H ⊗[ℂ] K)]
    (α : ℝ) (ρ₁ σ₁ : L H) (ρ₂ σ₂ : L K)
    (hρ₁ : 0 ≤ ρ₁) (hσ₁ : 0 ≤ σ₁) (hρ₂ : 0 ≤ ρ₂) (hσ₂ : 0 ≤ σ₂) :
    sandwichedQuasi α (TensorProduct.map ρ₁ ρ₂) (TensorProduct.map σ₁ σ₂) =
      sandwichedQuasi α ρ₁ σ₁ * sandwichedQuasi α ρ₂ σ₂ := by
  rw [sandwichedQuasi_eq_direct, sandwichedQuasi_eq_direct, sandwichedQuasi_eq_direct,
    TensorCFC.rpow_tensorProduct_lm σ₁ σ₂ ((1 - α) / (2 * α)) hσ₁ hσ₂,
    ← TensorProduct.map_mul, ← TensorProduct.map_mul,
    TensorCFC.rpow_tensorProduct_lm
      (CFC.rpow σ₁ ((1 - α) / (2 * α)) * ρ₁ * CFC.rpow σ₁ ((1 - α) / (2 * α)))
      (CFC.rpow σ₂ ((1 - α) / (2 * α)) * ρ₂ * CFC.rpow σ₂ ((1 - α) / (2 * α))) α
      (conjugate_nonneg_of_nonneg hρ₁ CFC.rpow_nonneg)
      (conjugate_nonneg_of_nonneg hρ₂ CFC.rpow_nonneg),
    LinearMap.trace_tensorProduct']

private theorem quasi_im_zero {H : Type*} [Qudit H] [Nontrivial H]
    (α : ℝ) (ρ σ : L H) : (sandwichedQuasi α ρ σ).im = 0 := by
  rw [sandwichedQuasi_eq_direct]
  exact (Complex.nonneg_iff.mp
    ((LinearMap.nonneg_iff_isPositive _).mp CFC.rpow_nonneg).trace_nonneg).2.symm

/-- Natural-log extended additivity for four density inputs and α > 1.
The finite branch proves nonzero Q before using the logarithmic product rule;
the infinite branches use the tensor support equivalence and exclude bottom. -/
theorem sandwichedTensorAdditiveOnDensity : SandwichedTensorAdditiveOnDensity.{u, v} := by
  intro H K _ _ _ _ _ α ρ₁ σ₁ ρ₂ σ₂ hα hρ₁ hσ₁ hρ₂ hσ₂
  have hρ₁nn := (LinearMap.nonneg_iff_isPositive _).mpr hρ₁.1
  have hσ₁nn := (LinearMap.nonneg_iff_isPositive _).mpr hσ₁.1
  have hρ₂nn := (LinearMap.nonneg_iff_isPositive _).mpr hρ₂.1
  have hσ₂nn := (LinearMap.nonneg_iff_isPositive _).mpr hσ₂.1
  have hρT := isDensity_tensorMap ρ₁ ρ₂ hρ₁ hρ₂
  have hsupp := supportLE_tensorMap_iff ρ₁ σ₁ ρ₂ σ₂ hρ₁ hσ₁ hρ₂ hσ₂
  by_cases hs₁ : SupportLE ρ₁ σ₁
  · by_cases hs₂ : SupportLE ρ₂ σ₂
    · rw [sandwichedDivNN_eq_coe_of_supportLE hα (hsupp.mpr ⟨hs₁, hs₂⟩),
        sandwichedDivNN_eq_coe_of_supportLE hα hs₁,
        sandwichedDivNN_eq_coe_of_supportLE hα hs₂, ← EReal.coe_add]
      have hQ₁ := sandwichedQuasi_re_ne_zero_of_suppLE hα hρ₁nn hσ₁nn hs₁
        (density_ne_zero hρ₁)
      have hQ₂ := sandwichedQuasi_re_ne_zero_of_suppLE hα hρ₂nn hσ₂nn hs₂
        (density_ne_zero hρ₂)
      congr 1
      unfold sandwichedRenyiDiv
      rw [hρT.2, hρ₁.2, hρ₂.2, Complex.one_re, div_one, div_one, div_one,
        sandwichedQuasi_tensorMap α ρ₁ σ₁ ρ₂ σ₂ hρ₁nn hσ₁nn hρ₂nn hσ₂nn,
        Complex.mul_re, quasi_im_zero α ρ₁ σ₁, zero_mul, sub_zero,
        Real.log_mul hQ₁ hQ₂, mul_add]
    · rw [sandwichedDivNN_eq_top_of_not_supportLE hα (fun h => hs₂ (hsupp.mp h).2),
        sandwichedDivNN_eq_top_of_not_supportLE hα hs₂,
        EReal.add_top_of_ne_bot (sandwichedDivNN_ne_bot α ρ₁ σ₁)]
  · rw [sandwichedDivNN_eq_top_of_not_supportLE hα (fun h => hs₁ (hsupp.mp h).1),
      sandwichedDivNN_eq_top_of_not_supportLE hα hs₁,
      EReal.top_add_of_ne_bot (sandwichedDivNN_ne_bot α ρ₂ σ₂)]

end RenyiDPI
