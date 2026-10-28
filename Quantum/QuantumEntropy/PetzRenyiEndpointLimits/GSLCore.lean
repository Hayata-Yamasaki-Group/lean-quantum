/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.PetzRenyiSpectralReduction.GSLCore

/-!
# Endpoint limits of the Petz quantum Rényi divergence

This file proves existence and uniqueness of the right limit at order zero
and the two-sided limit at order one.  Both limits are transferred from the
finite classical spectral distributions constructed in the preceding file.
-/

namespace OPT

open Filter
open QuantumState
open scoped ENNReal Topology

universe u

/-- Petz orders strictly above zero and at most two. -/
abbrev PetzRenyiPositiveOrder := Set.Ioc (0 : ℝ) 2

/-- Order one in the positive Petz order interval. -/
def petzRenyiPositiveOrderOne : PetzRenyiPositiveOrder :=
  ⟨1, by norm_num⟩

private def petzRenyiPositiveOrderToPetz
    (alpha : PetzRenyiPositiveOrder) : PetzRenyiOrder :=
  ⟨alpha, alpha.property.1.le, alpha.property.2⟩

private def petzRenyiPositiveOrderToClassical
    (alpha : PetzRenyiPositiveOrder) : RenyiOrder :=
  ⟨alpha, alpha.property.1⟩

/-- The punctured Petz family on the positive part of Gour's order interval.
Its value at order one is irrelevant to both punctured endpoint filters. -/
noncomputable def petzRenyiPuncturedFamily
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (alpha : PetzRenyiPositiveOrder) : EReal :=
  if halpha_one : (alpha : ℝ) = 1 then
    0
  else
    petzRenyiPunctured (petzRenyiPositiveOrderToPetz alpha)
      rho sigma hrho hsigma (ne_of_gt alpha.property.1) halpha_one

private theorem petzRenyiPuncturedFamily_eq_classicalSpectral
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (alpha : PetzRenyiPositiveOrder) (halpha_one : (alpha : ℝ) ≠ 1) :
    petzRenyiPuncturedFamily rho sigma hrho hsigma alpha =
      ((classicalRenyiDivBitsFinitePMF
        (petzRenyiPositiveOrderToClassical alpha)
        (petzSpectralP rho sigma hrho hsigma)
        (petzSpectralQ rho sigma hrho hsigma) : ℝ≥0∞) : EReal) := by
  rw [petzRenyiPuncturedFamily, dif_neg halpha_one]
  exact petzRenyiPunctured_eq_classicalSpectral
    (petzRenyiPositiveOrderToPetz alpha) rho sigma hrho hsigma
      (ne_of_gt alpha.property.1) halpha_one

private theorem petzRenyiPositiveOrderToClassical_tendsto_atBot :
    Tendsto petzRenyiPositiveOrderToClassical atBot atBot := by
  apply tendsto_atBot_atBot_of_monotone
  · intro alpha beta hab
    exact hab
  · intro beta
    refine ⟨⟨min (beta : ℝ) 1, ?_, ?_⟩, ?_⟩
    · exact lt_min beta.property zero_lt_one
    · exact (min_le_right (beta : ℝ) 1).trans (by norm_num)
    · exact min_le_left (beta : ℝ) 1

private theorem petzRenyiPositiveOrderToClassical_tendsto_one :
    Tendsto petzRenyiPositiveOrderToClassical
      (𝓝[≠] petzRenyiPositiveOrderOne) (𝓝 RenyiOrder.one) := by
  have hcontinuous : Continuous petzRenyiPositiveOrderToClassical :=
    continuous_subtype_val.subtype_mk fun alpha => alpha.property.1
  simpa [petzRenyiPositiveOrderOne, petzRenyiPositiveOrderToClassical] using
    hcontinuous.continuousAt.mono_left inf_le_left

private theorem petzRenyiPuncturedFamily_tendsto_zero
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    Tendsto (petzRenyiPuncturedFamily rho sigma hrho hsigma) atBot
      (𝓝 (((classicalMinRelativeEntropyBitsPMF
        (petzSpectralP rho sigma hrho hsigma)
        (petzSpectralQ rho sigma hrho hsigma) : ℝ≥0∞) : EReal))) := by
  let p := petzSpectralP rho sigma hrho hsigma
  let q := petzSpectralQ rho sigma hrho hsigma
  have hclassical :
      Tendsto
        (fun alpha : RenyiOrder =>
          ((classicalRenyiDivBitsFinitePMF alpha p q : ℝ≥0∞) : EReal))
        atBot (𝓝 ((classicalMinRelativeEntropyBitsPMF p q : ℝ≥0∞) : EReal)) :=
    continuous_coe_ennreal_ereal.continuousAt.tendsto.comp
      (classicalRenyiDivBitsFinite_tendsto_zero p q)
  have htransferred := hclassical.comp
    petzRenyiPositiveOrderToClassical_tendsto_atBot
  apply htransferred.congr'
  filter_upwards [eventually_le_atBot
    (⟨1 / 2, by norm_num⟩ : PetzRenyiPositiveOrder)] with alpha halpha
  have halpha_one : (alpha : ℝ) ≠ 1 := by
    have halpha_le : (alpha : ℝ) ≤ 1 / 2 := halpha
    linarith
  exact (petzRenyiPuncturedFamily_eq_classicalSpectral
    rho sigma hrho hsigma alpha halpha_one).symm

private theorem petzRenyiPuncturedFamily_tendsto_one
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    Tendsto (petzRenyiPuncturedFamily rho sigma hrho hsigma)
      (𝓝[≠] petzRenyiPositiveOrderOne)
      (𝓝 (((classicalKLDivergenceBitsPMF
        (petzSpectralP rho sigma hrho hsigma)
        (petzSpectralQ rho sigma hrho hsigma) : ℝ≥0∞) : EReal))) := by
  let p := petzSpectralP rho sigma hrho hsigma
  let q := petzSpectralQ rho sigma hrho hsigma
  have hclassical :
      Tendsto
        (fun alpha : RenyiOrder =>
          ((classicalRenyiDivBitsFinitePMF alpha p q : ℝ≥0∞) : EReal))
        (𝓝 RenyiOrder.one)
        (𝓝 ((classicalKLDivergenceBitsPMF p q : ℝ≥0∞) : EReal)) :=
    continuous_coe_ennreal_ereal.continuousAt.tendsto.comp
      (classicalRenyiDivBitsFinite_tendsto_one p q)
  have htransferred := hclassical.comp
    petzRenyiPositiveOrderToClassical_tendsto_one
  apply htransferred.congr'
  filter_upwards [self_mem_nhdsWithin] with alpha halpha
  have halpha_ne : alpha ≠ petzRenyiPositiveOrderOne := by
    simpa using halpha
  have halpha_one : (alpha : ℝ) ≠ 1 := by
    intro h
    apply halpha_ne
    exact Subtype.ext h
  exact (petzRenyiPuncturedFamily_eq_classicalSpectral
    rho sigma hrho hsigma alpha halpha_one).symm

/-- The order-zero right limit and order-one two-sided limit exist uniquely. -/
theorem petzRenyiEndpointLimits_existsUnique
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    (∃! d0 : EReal,
      Tendsto (petzRenyiPuncturedFamily rho sigma hrho hsigma)
        atBot (𝓝 d0)) ∧
    (∃! d1 : EReal,
      Tendsto (petzRenyiPuncturedFamily rho sigma hrho hsigma)
        (𝓝[≠] petzRenyiPositiveOrderOne) (𝓝 d1)) := by
  letI : Nontrivial PetzRenyiPositiveOrder :=
    ⟨⟨⟨1 / 2, by norm_num⟩, petzRenyiPositiveOrderOne, by
      intro h
      have hvalue := congrArg Subtype.val h
      norm_num [petzRenyiPositiveOrderOne] at hvalue⟩⟩
  constructor
  · let d0 : EReal :=
      (classicalMinRelativeEntropyBitsPMF
        (petzSpectralP rho sigma hrho hsigma)
        (petzSpectralQ rho sigma hrho hsigma) : ℝ≥0∞)
    have hzero : Tendsto (petzRenyiPuncturedFamily rho sigma hrho hsigma)
        atBot (𝓝 d0) :=
      petzRenyiPuncturedFamily_tendsto_zero rho sigma hrho hsigma
    refine ⟨d0, hzero, ?_⟩
    intro d hd
    exact tendsto_nhds_unique hd hzero
  · let d1 : EReal :=
      (classicalKLDivergenceBitsPMF
        (petzSpectralP rho sigma hrho hsigma)
        (petzSpectralQ rho sigma hrho hsigma) : ℝ≥0∞)
    have hone : Tendsto (petzRenyiPuncturedFamily rho sigma hrho hsigma)
        (𝓝[≠] petzRenyiPositiveOrderOne) (𝓝 d1) :=
      petzRenyiPuncturedFamily_tendsto_one rho sigma hrho hsigma
    refine ⟨d1, hone, ?_⟩
    intro d hd
    exact tendsto_nhds_unique hd hone

end OPT

namespace OPT

open QuantumState
open scoped ENNReal

universe u

/-- The selected Petz endpoint values are the corresponding spectral values. -/
theorem petzRenyiEndpointValues_eq_classicalSpectral
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (rho sigma : L ℋ) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    Classical.choose
        (petzRenyiEndpointLimits_existsUnique rho sigma hrho hsigma).1.exists =
        ((classicalMinRelativeEntropyBitsPMF
          (petzSpectralP rho sigma hrho hsigma)
          (petzSpectralQ rho sigma hrho hsigma) : ℝ≥0∞) : EReal) ∧
      Classical.choose
        (petzRenyiEndpointLimits_existsUnique rho sigma hrho hsigma).2.exists =
        ((classicalKLDivergenceBitsPMF
          (petzSpectralP rho sigma hrho hsigma)
          (petzSpectralQ rho sigma hrho hsigma) : ℝ≥0∞) : EReal) := by
  let hlimits :=
    petzRenyiEndpointLimits_existsUnique rho sigma hrho hsigma
  constructor
  · exact hlimits.1.unique
      (Classical.choose_spec hlimits.1.exists)
      (petzRenyiPuncturedFamily_tendsto_zero rho sigma hrho hsigma)
  · exact hlimits.2.unique
      (Classical.choose_spec hlimits.2.exists)
      (petzRenyiPuncturedFamily_tendsto_one rho sigma hrho hsigma)

end OPT
