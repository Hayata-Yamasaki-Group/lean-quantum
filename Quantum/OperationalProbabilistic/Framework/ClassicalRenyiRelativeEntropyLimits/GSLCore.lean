/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Topology.Order.AtTopBotIxx
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiOrder.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiRelativeEntropy.GSLCore

open scoped BigOperators ENNReal Topology
open Filter

/-!
# Endpoint limits of classical Rényi relative entropy

As the order tends to zero, the finite-order classical Rényi relative entropy in bits converges
to the order-zero value, including the support-boundary branch where the overlap vanishes
(`classicalRenyiDivBitsFinite_tendsto_zero`).  As the order tends to one it converges to the KL
value in bits (`classicalRenyiDivBitsFinite_tendsto_one`), obtained from the natural-logarithm
limits.
-/

namespace OPT

noncomputable section

private local instance renyiRelativeEntropy_orderSet_ordConnected :
    Set.OrdConnected {alpha : ℝ | 0 < alpha} := by
  change Set.OrdConnected (Set.Ioi (0 : ℝ))
  exact Set.ordConnected_Ioi

private local instance renyiRelativeEntropy_orderTopology : OrderTopology RenyiOrder :=
  @orderTopology_of_ordConnected ℝ inferInstance inferInstance inferInstance
    {alpha : ℝ | 0 < alpha} renyiRelativeEntropy_orderSet_ordConnected

private local instance renyiRelativeEntropy_denselyOrdered : DenselyOrdered RenyiOrder :=
  @Set.instDenselyOrdered ℝ inferInstance inferInstance
    {alpha : ℝ | 0 < alpha} renyiRelativeEntropy_orderSet_ordConnected

private theorem renyiRelativeEntropy_logTwo_pos : 0 < Real.log 2 :=
  Real.log_pos (by norm_num)

private theorem renyiRelativeEntropy_order_coe_tendsto_zero :
    Tendsto (fun alpha : RenyiOrder => (alpha : ℝ)) atBot (𝓝 0) := by
  have hright :
      Tendsto ((↑) : Set.Ioi (0 : ℝ) → ℝ) atBot (𝓝[>] 0) := by
    rw [← map_coe_Ioi_atBot (0 : ℝ)]
    exact tendsto_map
  exact hright.mono_right inf_le_left

private abbrev RenyiRelativeCommonSupport
    {ι : Type} [Fintype ι] (p q : PMF ι) :=
  {i : ι // p i ≠ 0 ∧ q i ≠ 0}

private noncomputable def renyiRelativeMoment
    {ι : Type} [Fintype ι] (p q : PMF ι) (alpha : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i ↦ p i ≠ 0 ∧ q i ≠ 0),
    (p i).toReal *
      Real.exp ((alpha - 1) *
        Real.log ((p i).toReal / (q i).toReal))

private theorem renyiRelativeCommon_p_pos
    {ι : Type} [Fintype ι] (p q : PMF ι)
    (i : RenyiRelativeCommonSupport p q) :
    0 < (p i).toReal :=
  ENNReal.toReal_pos i.property.1 (p.apply_ne_top i)

private theorem renyiRelativeMoment_pos
    {ι : Type} [Fintype ι] (p q : PMF ι)
    [Nonempty (RenyiRelativeCommonSupport p q)] (alpha : ℝ) :
    0 < renyiRelativeMoment p q alpha := by
  classical
  unfold renyiRelativeMoment
  let i : RenyiRelativeCommonSupport p q := Classical.choice inferInstance
  exact Finset.sum_pos' (fun j hj ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact mul_nonneg
        (ENNReal.toReal_pos hj.1 (p.apply_ne_top j)).le
        (Real.exp_pos _).le)
    ⟨i, by simp [i.property],
      mul_pos (renyiRelativeCommon_p_pos p q i) (Real.exp_pos _)⟩

private theorem renyiRelativeCommonSupport_nonempty_of_overlap_ne_zero
    {ι : Type} [Fintype ι] (p q : PMF ι)
    (hoverlap : classicalSupportOverlapPMF p q ≠ 0) :
    Nonempty (RenyiRelativeCommonSupport p q) := by
  classical
  cases isEmpty_or_nonempty (RenyiRelativeCommonSupport p q) with
  | inr hnonempty => exact hnonempty
  | inl hempty =>
      exfalso
      apply hoverlap
      unfold classicalSupportOverlapPMF
      apply Finset.sum_eq_zero
      intro i _
      by_cases hp : p i = 0
      · simp [hp, PMF.mem_support_iff]
      · have hq : q i = 0 := by
          by_contra hq
          exact isEmptyElim
            (⟨i, hp, hq⟩ : RenyiRelativeCommonSupport p q)
        simp [hq]

private theorem renyiRelativeOverlap_ne_top
    {ι : Type} [Fintype ι] (p q : PMF ι) :
    classicalSupportOverlapPMF p q ≠ ⊤ := by
  classical
  unfold classicalSupportOverlapPMF
  rw [ENNReal.sum_ne_top]
  intro i _
  split_ifs <;> simp [q.apply_ne_top]

private theorem renyiRelativeMoment_eq_powerSum_toReal_of_lt_one
    {ι : Type} [Fintype ι] (p q : PMF ι)
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    renyiRelativeMoment p q alpha =
      (renyiPowerSum ⟨alpha, halpha0⟩ p q).toReal := by
  classical
  unfold renyiRelativeMoment renyiPowerSum
  rw [ENNReal.toReal_sum]
  · calc
      (∑ i ∈ Finset.univ.filter (fun i ↦ p i ≠ 0 ∧ q i ≠ 0),
          (p i).toReal *
            Real.exp ((alpha - 1) *
              Real.log ((p i).toReal / (q i).toReal))) =
          ∑ i ∈ Finset.univ.filter (fun i ↦ p i ≠ 0 ∧ q i ≠ 0),
            (p i ^ alpha * q i ^ (1 - alpha)).toReal := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rcases hi with ⟨hp, hq⟩
        rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow]
        have hpr : 0 < (p i).toReal :=
          ENNReal.toReal_pos hp (p.apply_ne_top i)
        have hqr : 0 < (q i).toReal :=
          ENNReal.toReal_pos hq (q.apply_ne_top i)
        rw [Real.rpow_def_of_pos hpr, Real.rpow_def_of_pos hqr]
        rw [Real.log_div hpr.ne' hqr.ne']
        rw [← Real.exp_log hpr, ← Real.exp_add]
        rw [← Real.exp_add]
        simp only [Real.log_exp]
        congr 1
        ring
      _ = ∑ i, (p i ^ alpha * q i ^ (1 - alpha)).toReal := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i _ hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          not_and_or] at hi
        rcases hi with hp | hq
        · simp only [not_not] at hp
          simp [hp, ENNReal.zero_rpow_of_pos halpha0]
        · simp only [not_not] at hq
          simp [hq, ENNReal.zero_rpow_of_pos (sub_pos.2 halpha1)]
  · intro i _
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg halpha0.le (p.apply_ne_top i))
      (ENNReal.rpow_ne_top_of_nonneg (sub_pos.2 halpha1).le
        (q.apply_ne_top i))

private theorem renyiRelativeNatural_eq_ofReal_logMoment_div_of_lt_one
    {ι : Type} [Fintype ι] (p q : PMF ι)
    [Nonempty (RenyiRelativeCommonSupport p q)]
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    classicalRenyiDivPMF ⟨alpha, halpha0⟩ p q =
      ENNReal.ofReal
        (Real.log (renyiRelativeMoment p q alpha) / (alpha - 1)) := by
  let order : RenyiOrder := ⟨alpha, halpha0⟩
  have hmoment : 0 < renyiRelativeMoment p q alpha :=
    renyiRelativeMoment_pos p q alpha
  have hsumreal :
      (renyiPowerSum order p q).toReal =
        renyiRelativeMoment p q alpha := by
    simpa [order] using
      (renyiRelativeMoment_eq_powerSum_toReal_of_lt_one
        p q halpha0 halpha1).symm
  have hsumzero : renyiPowerSum order p q ≠ 0 := by
    intro h
    rw [h] at hsumreal
    simp at hsumreal
    exact hmoment.ne' hsumreal.symm
  rw [classicalRenyiDivPMF]
  simp only [halpha1.ne, ↓reduceIte,
    not_lt_of_ge halpha1.le, false_and]
  rw [if_neg (not_and_of_not_right _ hsumzero)]
  unfold renyiLogQuotient
  rw [ENNReal.log_pos_real' (hsumreal ▸ hmoment)]
  rw [hsumreal]
  rw [← EReal.coe_one, ← EReal.coe_sub, ← EReal.coe_inv,
    ← EReal.coe_mul, EReal.real_coe_toENNReal]
  congr 1
  rw [div_eq_mul_inv, mul_comm]

private theorem renyiRelativeBits_eq_ofReal_logMoment_div_of_lt_one
    {ι : Type} [Fintype ι] (p q : PMF ι)
    [Nonempty (RenyiRelativeCommonSupport p q)]
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    classicalRenyiDivBitsFinitePMF ⟨alpha, halpha0⟩ p q =
      ENNReal.ofReal
        ((Real.log (renyiRelativeMoment p q alpha) / (alpha - 1)) /
          Real.log 2) := by
  rw [classicalRenyiDivBitsFinitePMF,
    renyiRelativeNatural_eq_ofReal_logMoment_div_of_lt_one
      p q halpha0 halpha1,
    ← ENNReal.ofReal_div_of_pos renyiRelativeEntropy_logTwo_pos]

/-! ## The order-zero limit -/

private theorem renyiRelativeOverlap_eq_zero_implies_disjoint
    {ι : Type} [Fintype ι] (p q : PMF ι)
    (hoverlap : classicalSupportOverlapPMF p q = 0) :
    Disjoint p.support q.support := by
  classical
  apply Set.disjoint_left.2
  intro i hip hiq
  have hqi : q i = 0 := by
    apply bot_unique
    calc
      q i = (if i ∈ p.support then q i else 0) := by simp [hip]
      _ ≤ ∑ j, if j ∈ p.support then q j else 0 :=
        Finset.single_le_sum
          (s := Finset.univ)
          (f := fun j ↦ if j ∈ p.support then q j else (0 : ℝ≥0∞))
          (fun j _ ↦ by positivity) (Finset.mem_univ i)
      _ = 0 := hoverlap
  exact (q.mem_support_iff i).1 hiq hqi

private theorem renyiRelativeMoment_zero_eq_overlap_toReal
    {ι : Type} [Fintype ι] (p q : PMF ι) :
    renyiRelativeMoment p q 0 =
      (classicalSupportOverlapPMF p q).toReal := by
  classical
  unfold renyiRelativeMoment classicalSupportOverlapPMF
  rw [ENNReal.toReal_sum]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hp : p i = 0
    · simp [hp, PMF.mem_support_iff]
    · by_cases hq : q i = 0
      · simp [hq]
      · have hpr : 0 < (p i).toReal :=
          ENNReal.toReal_pos hp (p.apply_ne_top i)
        have hqr : 0 < (q i).toReal :=
          ENNReal.toReal_pos hq (q.apply_ne_top i)
        rw [if_pos ⟨hp, hq⟩]
        rw [if_pos ((p.mem_support_iff i).2 hp)]
        rw [show (0 : ℝ) - 1 = -1 by norm_num, neg_one_mul,
          Real.exp_neg, Real.exp_log (div_pos hpr hqr)]
        field_simp
  · intro i _
    split_ifs <;> simp [q.apply_ne_top]

private theorem renyiRelativeMoment_tendsto_zero
    {ι : Type} [Fintype ι] (p q : PMF ι) :
    Tendsto
      (fun alpha : RenyiOrder =>
        renyiRelativeMoment p q (alpha : ℝ))
      atBot (𝓝 (classicalSupportOverlapPMF p q).toReal) := by
  have hcontinuous : Continuous (renyiRelativeMoment p q) := by
    unfold renyiRelativeMoment
    fun_prop
  rw [← renyiRelativeMoment_zero_eq_overlap_toReal p q]
  exact hcontinuous.continuousAt.tendsto.comp
    renyiRelativeEntropy_order_coe_tendsto_zero

private theorem renyiRelativeBits_tendsto_zero_of_overlap_ne_zero
    {ι : Type} [Fintype ι] (p q : PMF ι)
    (hoverlap : classicalSupportOverlapPMF p q ≠ 0) :
    Tendsto
      (fun alpha : RenyiOrder =>
        classicalRenyiDivBitsFinitePMF alpha p q)
      atBot (𝓝 (classicalMinRelativeEntropyBitsPMF p q)) := by
  letI : Nonempty (RenyiRelativeCommonSupport p q) :=
    renyiRelativeCommonSupport_nonempty_of_overlap_ne_zero p q hoverlap
  have hoverlapPos :
      0 < (classicalSupportOverlapPMF p q).toReal :=
    ENNReal.toReal_pos hoverlap (renyiRelativeOverlap_ne_top p q)
  have hlog :
      Tendsto
        (fun alpha : RenyiOrder =>
          Real.log (renyiRelativeMoment p q (alpha : ℝ)))
        atBot (𝓝 (Real.log (classicalSupportOverlapPMF p q).toReal)) :=
    (Real.continuousAt_log hoverlapPos.ne').tendsto.comp
      (renyiRelativeMoment_tendsto_zero p q)
  have hdenom :
      Tendsto (fun alpha : RenyiOrder => (alpha : ℝ) - 1)
        atBot (𝓝 (-1)) := by
    simpa using renyiRelativeEntropy_order_coe_tendsto_zero.sub_const 1
  have hquotient :
      Tendsto
        (fun alpha : RenyiOrder =>
          Real.log (renyiRelativeMoment p q (alpha : ℝ)) /
            ((alpha : ℝ) - 1))
        atBot
        (𝓝 (-Real.log (classicalSupportOverlapPMF p q).toReal)) := by
    simpa only [div_neg, div_one] using
      hlog.div hdenom (by norm_num)
  have hbits := hquotient.div_const (Real.log 2)
  have hofReal := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hbits
  have hformula :
      (fun alpha : RenyiOrder =>
        classicalRenyiDivBitsFinitePMF alpha p q) =ᶠ[atBot]
      fun alpha : RenyiOrder =>
        ENNReal.ofReal
          ((Real.log (renyiRelativeMoment p q (alpha : ℝ)) /
            ((alpha : ℝ) - 1)) / Real.log 2) := by
    filter_upwards [eventually_le_atBot
      (⟨1 / 2, by norm_num⟩ : RenyiOrder)] with alpha halpha
    exact renyiRelativeBits_eq_ofReal_logMoment_div_of_lt_one
      p q alpha.property (lt_of_le_of_lt halpha (by norm_num))
  rw [classicalMinRelativeEntropyBitsPMF, if_neg hoverlap]
  have hscore := hofReal.congr' hformula.symm
  simpa only [Real.logb, neg_div] using hscore

private theorem renyiRelativeBits_tendsto_zero_of_overlap_eq_zero
    {ι : Type} [Fintype ι] (p q : PMF ι)
    (hoverlap : classicalSupportOverlapPMF p q = 0) :
    Tendsto
      (fun alpha : RenyiOrder =>
        classicalRenyiDivBitsFinitePMF alpha p q)
      atBot (𝓝 (classicalMinRelativeEntropyBitsPMF p q)) := by
  have hdisjoint :=
    renyiRelativeOverlap_eq_zero_implies_disjoint p q hoverlap
  rw [classicalMinRelativeEntropyBitsPMF_of_overlap_eq_zero p q hoverlap]
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [eventually_le_atBot
    (⟨1 / 2, by norm_num⟩ : RenyiOrder)] with alpha halpha
  have halphaOne : (alpha : ℝ) < 1 :=
    lt_of_le_of_lt halpha (by norm_num)
  rw [classicalRenyiDivBitsFinitePMF,
    classicalRenyiDivPMF_of_lt_one_of_disjoint_support
      alpha p q halphaOne hdisjoint]
  simp [ENNReal.top_div, ENNReal.ofReal_ne_top]

/-! ## The order-one limit -/

private theorem renyiRelativeNatural_tendsto_one
    {ι : Type} [Fintype ι] (p q : PMF ι) :
    Tendsto
      (fun alpha : RenyiOrder => classicalRenyiDivPMF alpha p q)
      (𝓝 RenyiOrder.one) (𝓝 (classicalRelEntropyPMF p q)) := by
  have hbelow :
      Tendsto (fun alpha : RenyiOrder => classicalRenyiDivPMF alpha p q)
        (nhdsWithin RenyiOrder.one (Set.Iio RenyiOrder.one))
        (𝓝 (classicalRelEntropyPMF p q)) := by
    rw [← map_coe_Iio_atTop RenyiOrder.one, tendsto_map'_iff]
    exact classicalRenyiDivPMF_tendsto_kl_fromBelow p q
  have habove :
      Tendsto (fun alpha : RenyiOrder => classicalRenyiDivPMF alpha p q)
        (nhdsWithin RenyiOrder.one (Set.Ioi RenyiOrder.one))
        (𝓝 (classicalRelEntropyPMF p q)) :=
    classicalRenyiDivPMF_tendsto_kl_fromAbove p q
  have hpure :
      Tendsto (fun alpha : RenyiOrder => classicalRenyiDivPMF alpha p q)
        (pure RenyiOrder.one) (𝓝 (classicalRelEntropyPMF p q)) := by
    simpa [classicalRenyiDivPMF_one] using
      tendsto_pure_nhds
        (fun alpha : RenyiOrder => classicalRenyiDivPMF alpha p q)
        RenyiOrder.one
  have hpunctured :
      Tendsto (fun alpha : RenyiOrder => classicalRenyiDivPMF alpha p q)
        (nhdsWithin RenyiOrder.one ({RenyiOrder.one}ᶜ))
        (𝓝 (classicalRelEntropyPMF p q)) := by
    rw [← nhdsLT_sup_nhdsGT]
    exact hbelow.sup habove
  rw [← pure_sup_nhdsNE RenyiOrder.one]
  exact hpure.sup hpunctured

/-! ## Source-facing limit statements -/

/-- The positive-finite bit Rényi relative entropy converges to the closed
order-zero formula as the order tends to zero from above. -/
theorem classicalRenyiDivBitsFinite_tendsto_zero
    {ι : Type} [Fintype ι] (p q : PMF ι) :
    Tendsto
      (fun alpha : RenyiOrder =>
        classicalRenyiDivBitsFinitePMF alpha p q)
      atBot (𝓝 (classicalMinRelativeEntropyBitsPMF p q)) := by
  by_cases hoverlap : classicalSupportOverlapPMF p q = 0
  · exact renyiRelativeBits_tendsto_zero_of_overlap_eq_zero
      p q hoverlap
  · exact renyiRelativeBits_tendsto_zero_of_overlap_ne_zero
      p q hoverlap

/-- The positive-finite bit Rényi relative entropy converges two-sidedly to
the exact bit KL value at order one. -/
theorem classicalRenyiDivBitsFinite_tendsto_one
    {ι : Type} [Fintype ι] (p q : PMF ι) :
    Tendsto
      (fun alpha : RenyiOrder =>
        classicalRenyiDivBitsFinitePMF alpha p q)
      (𝓝 RenyiOrder.one) (𝓝 (classicalKLDivergenceBitsPMF p q)) := by
  have hdenom : ENNReal.ofReal (Real.log 2) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr renyiRelativeEntropy_logTwo_pos
  exact (ENNReal.continuous_div_const _ hdenom).continuousAt.tendsto.comp
    (renyiRelativeNatural_tendsto_one p q)

end

end OPT
