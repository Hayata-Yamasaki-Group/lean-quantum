/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivergence.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiDivergence.GSLCore
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory Set

/-!
# Concrete classical f-divergence generators

This file supplies the KL and power generators for `FDivGenerator`.  Their endpoint data follow the
closed perspective convention in `ClassicalFDivergence`.

The KL generator is connected exactly to the existing finite-PMF relative
entropy.  The proof treats absolute continuity explicitly: on the supported
branch the PMF measure is represented by a density and Mathlib's KL integral
is evaluated as a finite sum; on the unsupported branch both quantities are
infinite.

This is a purely classical layer.
-/

namespace OPT

noncomputable section

/-! ## Kullback--Leibler generator -/

/-- The KL f-divergence generator `t * log t`. -/
def klFDivFunction (t : ℝ) : ℝ :=
  t * Real.log t

/-- The normalized convex KL generator.  Its zero endpoint is `0`, while its
recession slope is `+∞`. -/
noncomputable def klFDivGenerator : FDivGenerator where
  f := klFDivFunction
  convexOn_pos :=
    Real.convexOn_mul_log.subset Ioi_subset_Ici_self (convex_Ioi 0)
  map_one := by simp [klFDivFunction]
  zeroValue := 0
  zeroValue_ne_bot := EReal.coe_ne_bot 0
  tendsto_zeroValue := by
    rw [show (0 : EReal) = ((0 : ℝ) : EReal) by rfl, EReal.tendsto_coe]
    simpa [klFDivFunction] using
      (Real.continuous_mul_log.tendsto 0).mono_left inf_le_left
  recessionSlope := ⊤
  recessionSlope_ne_bot := top_ne_bot
  tendsto_recessionSlope := by
    have hlog :
        Tendsto (fun t : ℝ => ((Real.log t : ℝ) : EReal)) atTop (𝓝 ⊤) :=
      EReal.tendsto_coe_atTop.comp Real.tendsto_log_atTop
    apply hlog.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp [klFDivFunction, ht.ne']

private noncomputable def pmfRatio {iota : Type}
    (p q : PMF iota) (i : iota) : ℝ≥0∞ :=
  p i / q i

private theorem pmf_toMeasure_eq_withDensity_ratio {iota : Type}
    [Finite iota] [MeasurableSpace iota] [MeasurableSingletonClass iota]
    (p q : PMF iota) (h : p.support ⊆ q.support) :
    p.toMeasure = q.toMeasure.withDensity (pmfRatio p q) := by
  letI := Fintype.ofFinite iota
  ext s hs
  rw [withDensity_apply _ hs, lintegral_fintype, p.toMeasure_apply_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.restrict_apply (measurableSet_singleton i)]
  by_cases hi : i ∈ s
  · rw [show ({i} : Set iota) ∩ s = {i} by ext; simp [hi]]
    rw [q.toMeasure_apply_singleton i (measurableSet_singleton i)]
    simp only [Set.indicator_of_mem hi, pmfRatio]
    by_cases hp : p i = 0
    · simp [hp]
    · have hq : q i ≠ 0 :=
        (q.mem_support_iff i).1 (h ((p.mem_support_iff i).2 hp))
      exact (ENNReal.div_mul_cancel hq (q.apply_ne_top i)).symm
  · rw [show ({i} : Set iota) ∩ s = ∅ by ext; simp [hi]]
    simp [Set.indicator_of_notMem hi]

private theorem kl_eq_explicit_of_support_subset {iota : Type}
    [Fintype iota] (p q : PMF iota) (h : p.support ⊆ q.support) :
    classicalRelEntropyPMF p q = ENNReal.ofReal
      (∑ i, (p i).toReal * Real.log ((pmfRatio p q i).toReal)) := by
  letI : MeasurableSpace iota := ⊤
  change InformationTheory.klDiv p.toMeasure q.toMeasure = _
  have hmeasure := pmf_toMeasure_eq_withDensity_ratio p q h
  have hac : p.toMeasure ≪ q.toMeasure := by
    rw [hmeasure]
    exact withDensity_absolutelyContinuous _ _
  have hrn :
      p.toMeasure.rnDeriv q.toMeasure =ᵐ[q.toMeasure] pmfRatio p q := by
    rw [hmeasure]
    exact Measure.rnDeriv_withDensity q.toMeasure (by fun_prop)
  have hllr_q :
      llr p.toMeasure q.toMeasure =ᵐ[q.toMeasure]
        fun i => Real.log ((pmfRatio p q i).toReal) := by
    filter_upwards [hrn] with i hi
    simp only [llr, hi]
  have hllr_p := hac.ae_eq hllr_q
  have hint : Integrable (llr p.toMeasure q.toMeasure) p.toMeasure :=
    Integrable.of_finite
  rw [InformationTheory.klDiv_of_ac_of_integrable hac hint]
  rw [integral_congr_ae hllr_p]
  rw [PMF.integral_eq_sum]
  simp

private theorem closedPerspective_kl_apply {iota : Type}
    (p q : PMF iota) (h : p.support ⊆ q.support) (i : iota) :
    closedPerspective klFDivGenerator (p i).toNNReal (q i).toNNReal =
      (((p i).toReal * Real.log ((pmfRatio p q i).toReal) : ℝ) : EReal) := by
  by_cases hp : p i = 0
  · have hpnn : (p i).toNNReal = 0 := by simp [hp]
    rw [hpnn, closedPerspective]
    simp [klFDivGenerator, pmfRatio, hp]
  · have hq : q i ≠ 0 :=
      (q.mem_support_iff i).1 (h ((p.mem_support_iff i).2 hp))
    have hpnn : (p i).toNNReal ≠ 0 :=
      ENNReal.toNNReal_ne_zero.mpr ⟨hp, p.apply_ne_top i⟩
    have hqnn : (q i).toNNReal ≠ 0 :=
      ENNReal.toNNReal_ne_zero.mpr ⟨hq, q.apply_ne_top i⟩
    have hqreal : (q i).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨hq, q.apply_ne_top i⟩
    rw [closedPerspective_of_ne_zero _ _ _ hpnn hqnn]
    simp only [klFDivGenerator, klFDivFunction, EReal.coe_eq_coe_iff]
    rw [ENNReal.coe_toNNReal_eq_toReal, ENNReal.coe_toNNReal_eq_toReal]
    rw [pmfRatio, ENNReal.toReal_div]
    field_simp [hqreal]

private theorem ereal_sum_coe {iota : Type}
    (s : Finset iota) (f : iota → ℝ) :
    (∑ i ∈ s, ((f i : ℝ) : EReal)) = ((∑ i ∈ s, f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, ← EReal.coe_add]

private theorem classicalFDivSum_kl_of_support_subset {iota : Type}
    [Fintype iota] (p q : PMF iota) (h : p.support ⊆ q.support) :
    classicalFDivSum klFDivGenerator p q =
      ((∑ i, (p i).toReal * Real.log ((pmfRatio p q i).toReal) : ℝ) :
        EReal) := by
  unfold classicalFDivSum
  calc
    (∑ i, closedPerspective klFDivGenerator
        (p i).toNNReal (q i).toNNReal) =
        ∑ i, (((p i).toReal * Real.log ((pmfRatio p q i).toReal) : ℝ) :
          EReal) := by
      exact Finset.sum_congr rfl fun i _ => closedPerspective_kl_apply p q h i
    _ = ((∑ i, (p i).toReal * Real.log ((pmfRatio p q i).toReal) : ℝ) :
        EReal) := by
      simpa using ereal_sum_coe (Finset.univ : Finset iota)
        (fun i => (p i).toReal * Real.log ((pmfRatio p q i).toReal))

private theorem classicalFDivPMF_kl_of_support_subset {iota : Type}
    [Fintype iota] (p q : PMF iota) (h : p.support ⊆ q.support) :
    classicalFDivPMF klFDivGenerator p q = ENNReal.ofReal
      (∑ i, (p i).toReal * Real.log ((pmfRatio p q i).toReal)) := by
  rw [classicalFDivPMF, classicalFDivSum_kl_of_support_subset p q h]
  rfl

private theorem classicalFDivSum_kl_eq_top_of_not_support_subset
    {iota : Type} [Fintype iota] (p q : PMF iota)
    (h : ¬p.support ⊆ q.support) :
    classicalFDivSum klFDivGenerator p q = ⊤ := by
  classical
  obtain ⟨i, hpi, hqi⟩ := Set.not_subset.mp h
  have hp : p i ≠ 0 := (p.mem_support_iff i).1 hpi
  have hq : q i = 0 := (q.apply_eq_zero_iff i).2 hqi
  have hpnn : (p i).toNNReal ≠ 0 :=
    ENNReal.toNNReal_ne_zero.mpr ⟨hp, p.apply_ne_top i⟩
  have hterm :
      closedPerspective klFDivGenerator (p i).toNNReal (q i).toNNReal = ⊤ := by
    rw [show (q i).toNNReal = 0 by simp [hq],
      closedPerspective_zero_right _ _ hpnn]
    exact EReal.coe_mul_top_of_pos (by positivity)
  unfold classicalFDivSum
  rw [Finset.sum_eq_add_sum_diff_singleton i _ (by simp), hterm]
  apply EReal.top_add_of_ne_bot
  apply ne_of_gt
  apply WithBot.sum_lt_bot
  intro j _
  exact closedPerspective_ne_bot klFDivGenerator (p j).toNNReal (q j).toNNReal

private theorem classicalFDivPMF_kl_eq_top_of_not_support_subset
    {iota : Type} [Fintype iota] (p q : PMF iota)
    (h : ¬p.support ⊆ q.support) :
    classicalFDivPMF klFDivGenerator p q = ⊤ := by
  rw [classicalFDivPMF,
    classicalFDivSum_kl_eq_top_of_not_support_subset p q h]
  rfl

private theorem pmf_not_absolutelyContinuous_of_not_support_subset
    {iota : Type} [MeasurableSpace iota] [MeasurableSingletonClass iota]
    (p q : PMF iota)
    (h : ¬p.support ⊆ q.support) :
    ¬p.toMeasure ≪ q.toMeasure := by
  obtain ⟨i, hpi, hqi⟩ := Set.not_subset.mp h
  intro hac
  have hq : q i = 0 := (q.apply_eq_zero_iff i).2 hqi
  have hzero : q.toMeasure ({i} : Set iota) = 0 := by
    rw [q.toMeasure_apply_singleton i (measurableSet_singleton i), hq]
  have hpzero := hac hzero
  rw [p.toMeasure_apply_singleton i (measurableSet_singleton i)] at hpzero
  exact (p.mem_support_iff i).1 hpi hpzero

private theorem kl_eq_top_of_not_support_subset {iota : Type}
    [Fintype iota] (p q : PMF iota) (h : ¬p.support ⊆ q.support) :
    classicalRelEntropyPMF p q = ⊤ := by
  letI : MeasurableSpace iota := ⊤
  change InformationTheory.klDiv p.toMeasure q.toMeasure = ⊤
  exact InformationTheory.klDiv_of_not_ac
    (pmf_not_absolutelyContinuous_of_not_support_subset p q h)

/-- The f-divergence of `t * log t` is exactly the existing natural-log KL
divergence, including the infinite support-mismatch branch. -/
@[simp]
theorem classicalFDivPMF_kl {iota : Type} [Fintype iota]
    (p q : PMF iota) :
    classicalFDivPMF klFDivGenerator p q = classicalRelEntropyPMF p q := by
  by_cases h : p.support ⊆ q.support
  · rw [classicalFDivPMF_kl_of_support_subset p q h,
      kl_eq_explicit_of_support_subset p q h]
  · rw [classicalFDivPMF_kl_eq_top_of_not_support_subset p q h,
      kl_eq_top_of_not_support_subset p q h]

/-! ## Power generators -/

/-- The power-divergence generator `(t^alpha - 1) / (alpha - 1)`.

The bundled generator below requires the positive Rényi order to differ from
one. -/
def powerFDivFunction (alpha : RenyiOrder) (t : ℝ) : ℝ :=
  (t ^ (alpha : ℝ) - 1) / ((alpha : ℝ) - 1)

/-- The normalized convex power generator for a positive order different from
one.  Its recession slope is `+∞` above one and `0` below one. -/
noncomputable def powerFDivGenerator (alpha : RenyiOrder)
    (halpha : (alpha : ℝ) ≠ 1) : FDivGenerator where
  f := powerFDivFunction alpha
  convexOn_pos := by
    rcases lt_or_gt_of_ne halpha with hlt | hgt
    · have hpow :
          ConcaveOn ℝ (Ioi 0) (fun t : ℝ => t ^ (alpha : ℝ)) :=
        (Real.concaveOn_rpow alpha.property.le hlt.le).subset
          Ioi_subset_Ici_self (convex_Ioi 0)
      have hdiff :
          ConcaveOn ℝ (Ioi 0) (fun t : ℝ => t ^ (alpha : ℝ) - 1) := by
        simpa only [Pi.sub_apply] using
          hpow.sub (convexOn_const (1 : ℝ) (convex_Ioi 0))
      have hscale := hdiff.neg.smul
        (inv_nonneg.mpr (sub_nonneg.mpr hlt.le))
      refine hscale.congr ?_
      intro t _
      simp only [Pi.neg_apply, smul_eq_mul, powerFDivFunction]
      rw [show (1 - (alpha : ℝ))⁻¹ = -(((alpha : ℝ) - 1)⁻¹) by
        rw [show 1 - (alpha : ℝ) = -((alpha : ℝ) - 1) by ring, inv_neg]]
      rw [div_eq_mul_inv]
      ring
    · have hpow :
          ConvexOn ℝ (Ioi 0) (fun t : ℝ => t ^ (alpha : ℝ)) :=
        (convexOn_rpow hgt.le).subset Ioi_subset_Ici_self (convex_Ioi 0)
      have hdiff :
          ConvexOn ℝ (Ioi 0) (fun t : ℝ => t ^ (alpha : ℝ) - 1) := by
        simpa only [Pi.sub_apply] using
          hpow.sub (concaveOn_const (1 : ℝ) (convex_Ioi 0))
      have hscale := hdiff.smul
        (inv_nonneg.mpr (sub_nonneg.mpr hgt.le))
      refine hscale.congr ?_
      intro t _
      simp only [smul_eq_mul, powerFDivFunction]
      rw [div_eq_mul_inv, mul_comm]
  map_one := by simp [powerFDivFunction]
  zeroValue := (((-1) / ((alpha : ℝ) - 1) : ℝ) : EReal)
  zeroValue_ne_bot := EReal.coe_ne_bot _
  tendsto_zeroValue := by
    rw [EReal.tendsto_coe]
    have hp : Continuous (fun t : ℝ => t ^ (alpha : ℝ)) :=
      Real.continuous_rpow_const alpha.property.le
    have hcont :
        Continuous fun t : ℝ =>
          (t ^ (alpha : ℝ) - 1) / ((alpha : ℝ) - 1) :=
      (hp.sub continuous_const).div_const _
    simpa [powerFDivFunction, ne_of_gt alpha.property] using
      (hcont.tendsto 0).mono_left inf_le_left
  recessionSlope := if 1 < (alpha : ℝ) then ⊤ else 0
  recessionSlope_ne_bot := by
    split
    · exact top_ne_bot
    · exact EReal.coe_ne_bot 0
  tendsto_recessionSlope := by
    by_cases hgt : 1 < (alpha : ℝ)
    · simp only [if_pos hgt]
      have hpow :
          Tendsto (fun t : ℝ => t ^ ((alpha : ℝ) - 1)) atTop atTop :=
        tendsto_rpow_atTop (sub_pos.2 hgt)
      have hinv : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) :=
        tendsto_id.const_div_atTop 1
      have hnum :
          Tendsto (fun t : ℝ => t ^ ((alpha : ℝ) - 1) - 1 / t)
            atTop atTop := by
        simpa only [sub_eq_add_neg] using hpow.atTop_add hinv.neg
      have hdiv := hnum.atTop_div_const (sub_pos.2 hgt)
      have hcoe :
          Tendsto
            (fun t : ℝ =>
              (((t ^ ((alpha : ℝ) - 1) - 1 / t) /
                ((alpha : ℝ) - 1) : ℝ) : EReal))
            atTop (𝓝 ⊤) := by
        simpa only [Function.comp_apply] using
          EReal.tendsto_coe_atTop.comp hdiv
      refine hcoe.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      simp only [powerFDivFunction, EReal.coe_eq_coe_iff]
      rw [Real.rpow_sub_one ht.ne' (alpha : ℝ)]
      field_simp [ht.ne', hgt.ne']
    · have hlt : (alpha : ℝ) < 1 :=
        lt_of_le_of_ne (le_of_not_gt hgt) halpha
      simp only [if_neg hgt]
      rw [show (0 : EReal) = ((0 : ℝ) : EReal) by rfl,
        EReal.tendsto_coe]
      have hpow :
          Tendsto (fun t : ℝ => t ^ ((alpha : ℝ) - 1)) atTop (𝓝 0) := by
        have hexp : (alpha : ℝ) - 1 = -(1 - (alpha : ℝ)) := by ring
        simpa only [hexp] using tendsto_rpow_neg_atTop (sub_pos.2 hlt)
      have hinv : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) :=
        tendsto_id.const_div_atTop 1
      have hdiv := (hpow.sub hinv).div_const ((alpha : ℝ) - 1)
      have hdiv' :
          Tendsto
            (fun t : ℝ =>
              (t ^ ((alpha : ℝ) - 1) - 1 / t) / ((alpha : ℝ) - 1))
            atTop (𝓝 0) := by
        simpa [halpha] using hdiv
      refine hdiv'.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      simp only [powerFDivFunction]
      rw [Real.rpow_sub_one ht.ne' (alpha : ℝ)]
      field_simp [ht.ne', halpha]

/-- Interior closed-perspective algebra for the power generator.  This is the
pointwise identity whose finite sum yields the Rényi power sum. -/
theorem mul_powerFDivFunction_div (alpha : RenyiOrder) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) :
    b * powerFDivFunction alpha (a / b) =
      (a ^ (alpha : ℝ) * b ^ (1 - (alpha : ℝ)) - b) /
        ((alpha : ℝ) - 1) := by
  rw [powerFDivFunction, Real.div_rpow ha hb.le]
  rw [Real.rpow_sub hb 1 (alpha : ℝ), Real.rpow_one]
  field_simp

end

end OPT
