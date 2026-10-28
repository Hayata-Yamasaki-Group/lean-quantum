/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiDivergence.GSLCore

open scoped BigOperators ENNReal Topology
open Filter MeasureTheory Set

/-!
# Order dependence and the left order limit of classical Rényi divergence

The classical Rényi divergence is monotone in its positive finite order.
Its limits as the order tends to one from below and from above are the
natural-logarithm KL divergence.
-/

namespace OPT

noncomputable section

/-- Positive finite Rényi orders strictly below the KL order.  Its inherited
order tends to `1` at `Filter.atTop`, so it is the fail-closed index used for
all left-order-limit statements. -/
abbrev RenyiOrderBelowOne := {alpha : RenyiOrder // (alpha : ℝ) < 1}

namespace ClassicalRenyiOrder

variable {iota : Type} [Fintype iota]

/-- The outcomes on which both PMFs are positive. -/
private abbrev CommonSupport (p q : PMF iota) :=
  {i : iota // p i ≠ 0 ∧ q i ≠ 0}

/-- Real exponential-moment presentation of the Rényi power sum. -/
private noncomputable def moment (p q : PMF iota) (alpha : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i ↦ p i ≠ 0 ∧ q i ≠ 0),
    (p i).toReal * Real.exp ((alpha - 1) * Real.log ((p i).toReal / (q i).toReal))

private noncomputable def rate (p q : PMF iota) (i : iota) : ℝ :=
  Real.log ((p i).toReal / (q i).toReal)

private noncomputable def momentDeriv (p q : PMF iota) (alpha : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i ↦ p i ≠ 0 ∧ q i ≠ 0),
    (p i).toReal * Real.exp ((alpha - 1) * rate p q i) * rate p q i

private noncomputable def momentDeriv2 (p q : PMF iota) (alpha : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i ↦ p i ≠ 0 ∧ q i ≠ 0),
    (p i).toReal * Real.exp ((alpha - 1) * rate p q i) * (rate p q i) ^ 2

private noncomputable def logMoment (p q : PMF iota) (alpha : ℝ) : ℝ :=
  Real.log (moment p q alpha)

private noncomputable def logMomentDeriv (p q : PMF iota) (alpha : ℝ) : ℝ :=
  momentDeriv p q alpha / moment p q alpha

private noncomputable def logMomentDeriv2 (p q : PMF iota) (alpha : ℝ) : ℝ :=
  (moment p q alpha * momentDeriv2 p q alpha - (momentDeriv p q alpha) ^ 2) /
    (moment p q alpha) ^ 2

omit [Fintype iota] in
private theorem common_p_pos (p q : PMF iota) (i : CommonSupport p q) :
    0 < (p i).toReal :=
  ENNReal.toReal_pos i.property.1 (p.apply_ne_top i)

private theorem moment_pos (p q : PMF iota) [Nonempty (CommonSupport p q)]
    (alpha : ℝ) : 0 < moment p q alpha := by
  classical
  unfold moment
  let i : CommonSupport p q := Classical.choice inferInstance
  exact Finset.sum_pos' (fun j hj ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact mul_nonneg
        (ENNReal.toReal_pos hj.1 (p.apply_ne_top j)).le (Real.exp_pos _).le)
    ⟨i, by simp [i.property],
      mul_pos (common_p_pos p q i) (Real.exp_pos _)⟩

private theorem moment_one (p q : PMF iota) :
    moment p q 1 =
      ∑ i ∈ Finset.univ.filter (fun i ↦ p i ≠ 0 ∧ q i ≠ 0), (p i).toReal := by
  simp [moment]

private theorem hasDerivAt_moment (p q : PMF iota) (alpha : ℝ) :
    HasDerivAt (moment p q) (momentDeriv p q alpha) alpha := by
  classical
  unfold moment momentDeriv rate
  let h := HasDerivAt.sum
    (u := Finset.univ.filter (fun i ↦ p i ≠ 0 ∧ q i ≠ 0))
    (fun i _ ↦ (hasDerivAt_const alpha (p i).toReal).mul
      ((Real.hasDerivAt_exp _).comp alpha
        (((hasDerivAt_id alpha).sub_const 1).mul_const
          (Real.log ((p i).toReal / (q i).toReal)))))
  convert h using 1
  · funext x
    simp only [Finset.sum_apply, Function.comp_def, Pi.mul_apply, id_eq]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Function.comp_apply, id_eq, zero_mul, zero_add]
    ring

private theorem hasDerivAt_momentDeriv (p q : PMF iota) (alpha : ℝ) :
    HasDerivAt (momentDeriv p q) (momentDeriv2 p q alpha) alpha := by
  classical
  unfold momentDeriv momentDeriv2 rate
  let h := HasDerivAt.sum
    (u := Finset.univ.filter (fun i ↦ p i ≠ 0 ∧ q i ≠ 0))
    (fun i _ ↦ ((hasDerivAt_const alpha (p i).toReal).mul
      ((Real.hasDerivAt_exp _).comp alpha
        (((hasDerivAt_id alpha).sub_const 1).mul_const
          (Real.log ((p i).toReal / (q i).toReal))))).mul_const
            (Real.log ((p i).toReal / (q i).toReal)))
  convert h using 1
  · funext x
    simp only [Finset.sum_apply, Function.comp_def, Pi.mul_apply, id_eq]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Function.comp_apply, id_eq, zero_mul, zero_add]
    ring

private theorem hasDerivAt_logMoment (p q : PMF iota) [Nonempty (CommonSupport p q)]
    (alpha : ℝ) :
    HasDerivAt (logMoment p q) (logMomentDeriv p q alpha) alpha := by
  unfold logMoment logMomentDeriv
  simpa only [Function.comp_apply, div_eq_mul_inv, mul_comm] using
    (Real.hasDerivAt_log (moment_pos p q alpha).ne').comp alpha
      (hasDerivAt_moment p q alpha)

private theorem hasDerivAt_logMomentDeriv
    (p q : PMF iota) [Nonempty (CommonSupport p q)] (alpha : ℝ) :
    HasDerivAt (logMomentDeriv p q) (logMomentDeriv2 p q alpha) alpha := by
  unfold logMomentDeriv logMomentDeriv2
  convert (hasDerivAt_momentDeriv p q alpha).div (hasDerivAt_moment p q alpha)
    (moment_pos p q alpha).ne' using 1
  ring

private theorem momentDeriv_sq_le (p q : PMF iota) (alpha : ℝ) :
    (momentDeriv p q alpha) ^ 2 ≤
      moment p q alpha * momentDeriv2 p q alpha := by
  classical
  let s := Finset.univ.filter (fun i ↦ p i ≠ 0 ∧ q i ≠ 0)
  let w : iota → ℝ := fun i ↦
    (p i).toReal * Real.exp ((alpha - 1) * rate p q i)
  have hw (i : iota) : 0 ≤ w i :=
    mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  have hleft :
      ∑ i ∈ s, (Real.sqrt (w i) * rate p q i) * Real.sqrt (w i) =
        momentDeriv p q alpha := by
    unfold momentDeriv
    change (∑ i ∈ s, (Real.sqrt (w i) * rate p q i) * Real.sqrt (w i)) =
      ∑ i ∈ s, w i * rate p q i
    apply Finset.sum_congr rfl
    intro i _
    have hsqrt := Real.sq_sqrt (hw i)
    calc
      Real.sqrt (w i) * rate p q i * Real.sqrt (w i) =
          (Real.sqrt (w i)) ^ 2 * rate p q i := by ring
      _ = w i * rate p q i := by rw [hsqrt]
  have hfirst :
      ∑ i ∈ s, (Real.sqrt (w i) * rate p q i) ^ 2 =
        momentDeriv2 p q alpha := by
    unfold momentDeriv2
    change (∑ i ∈ s, (Real.sqrt (w i) * rate p q i) ^ 2) =
      ∑ i ∈ s, w i * (rate p q i) ^ 2
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, Real.sq_sqrt (hw i)]
  have hsecond :
      ∑ i ∈ s, (Real.sqrt (w i)) ^ 2 = moment p q alpha := by
    unfold moment
    change (∑ i ∈ s, (Real.sqrt (w i)) ^ 2) = ∑ i ∈ s, w i
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.sq_sqrt (hw i)]
  rw [← hleft, ← hfirst, ← hsecond]
  simpa only [mul_comm] using Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i ↦ Real.sqrt (w i) * rate p q i) (fun i ↦ Real.sqrt (w i))

private theorem logMomentDeriv2_nonneg
    (p q : PMF iota) [Nonempty (CommonSupport p q)] (alpha : ℝ) :
    0 ≤ logMomentDeriv2 p q alpha := by
  unfold logMomentDeriv2
  apply div_nonneg
  · exact sub_nonneg.2 (momentDeriv_sq_le p q alpha)
  · positivity

private theorem convexOn_logMoment
    (p q : PMF iota) [Nonempty (CommonSupport p q)] :
    ConvexOn ℝ Set.univ (logMoment p q) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
  · exact (continuous_iff_continuousAt.2 fun alpha ↦
      (hasDerivAt_logMoment p q alpha).continuousAt).continuousOn
  · intro alpha _
    exact (hasDerivAt_logMoment p q alpha).hasDerivWithinAt
  · intro alpha _
    exact (hasDerivAt_logMomentDeriv p q alpha).hasDerivWithinAt
  · intro alpha _
    exact logMomentDeriv2_nonneg p q alpha

omit [Fintype iota] in
private theorem commonSupport_nonempty_of_support
    (p q : PMF iota) (hsupport : p.support ⊆ q.support) :
    Nonempty (CommonSupport p q) := by
  obtain ⟨i, hi⟩ := p.support_nonempty
  exact ⟨⟨i, (p.mem_support_iff i).1 hi,
    (q.mem_support_iff i).1 (hsupport hi)⟩⟩

private theorem moment_one_eq_one_of_support
    (p q : PMF iota) (hsupport : p.support ⊆ q.support) :
    moment p q 1 = 1 := by
  classical
  rw [moment_one]
  calc
    (∑ i ∈ Finset.univ.filter (fun i ↦ p i ≠ 0 ∧ q i ≠ 0), (p i).toReal) =
        ∑ i, (p i).toReal := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or] at hi
      rcases hi with hp | hq
      · simp only [not_not] at hp
        simp [hp]
      · simp only [not_not] at hq
        have hp : p i = 0 := by
          by_contra hp
          exact ((q.mem_support_iff i).1
            (hsupport ((p.mem_support_iff i).2 hp))) hq
        simp [hp]
    _ = 1 := by
      rw [← ENNReal.toReal_sum]
      · have hsum : ∑ i, p i = 1 := by
          simpa only [tsum_fintype] using p.tsum_coe
        rw [hsum]
        rfl
      · exact fun i _ ↦ p.apply_ne_top i

private theorem moment_one_le_one (p q : PMF iota) : moment p q 1 ≤ 1 := by
  classical
  rw [moment_one]
  calc
    (∑ i ∈ Finset.univ.filter (fun i ↦ p i ≠ 0 ∧ q i ≠ 0), (p i).toReal) ≤
        ∑ i, (p i).toReal :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ ENNReal.toReal_nonneg)
    _ = 1 := by
      rw [← ENNReal.toReal_sum]
      · have hsum : ∑ i, p i = 1 := by
          simpa only [tsum_fintype] using p.tsum_coe
        rw [hsum]
        rfl
      · exact fun i _ ↦ p.apply_ne_top i

private theorem moment_one_lt_one_of_supportMismatch
    (p q : PMF iota) (hmismatch : renyiSupportMismatch p q) :
    moment p q 1 < 1 := by
  classical
  obtain ⟨i, hip, hiq⟩ := Set.not_subset.1 hmismatch
  have hp : p i ≠ 0 := (p.mem_support_iff i).1 hip
  have hq : q i = 0 := (q.apply_eq_zero_iff i).2 hiq
  rw [moment_one]
  calc
    (∑ j ∈ Finset.univ.filter (fun j ↦ p j ≠ 0 ∧ q j ≠ 0), (p j).toReal) <
        ∑ j, (p j).toReal := by
      apply Finset.sum_lt_sum_of_subset (Finset.filter_subset _ _)
        (Finset.mem_univ i)
      · simp [hp, hq]
      · exact ENNReal.toReal_pos hp (p.apply_ne_top i)
      · intro j _ _
        exact ENNReal.toReal_nonneg
    _ = 1 := by
      rw [← ENNReal.toReal_sum]
      · have hsum : ∑ j, p j = 1 := by
          simpa only [tsum_fintype] using p.tsum_coe
        rw [hsum]
        rfl
      · exact fun j _ ↦ p.apply_ne_top j

private theorem logMoment_one_nonpos
    (p q : PMF iota) [Nonempty (CommonSupport p q)] :
    logMoment p q 1 ≤ 0 := by
  unfold logMoment
  exact Real.log_nonpos (moment_pos p q 1).le (moment_one_le_one p q)

private noncomputable def pmfDensity (p q : PMF iota) (i : iota) : ℝ≥0∞ :=
  p i / q i

omit [Fintype iota] in
private theorem pmf_toMeasure_ac_iff_support (p q : PMF iota) :
    letI : MeasurableSpace iota := ⊤
    p.toMeasure ≪ q.toMeasure ↔ p.support ⊆ q.support := by
  letI : MeasurableSpace iota := ⊤
  constructor
  · intro hac i hi
    by_contra hqi
    have hqzero : q i = 0 := (q.apply_eq_zero_iff i).2 hqi
    have hpzero : p i = 0 := by
      rw [← p.toMeasure_apply_singleton i (by simp)]
      apply hac
      rw [q.toMeasure_apply_singleton i (by simp), hqzero]
    exact (p.mem_support_iff i).1 hi hpzero
  · intro hsupport
    apply Measure.AbsolutelyContinuous.mk
    intro s hs hqzero
    rw [p.toMeasure_apply_eq_zero_iff hs]
    rw [q.toMeasure_apply_eq_zero_iff hs] at hqzero
    exact Set.disjoint_left.2 fun i hip his ↦
      Set.disjoint_left.1 hqzero (hsupport hip) his

omit [Fintype iota] in
private theorem withDensity_pmfDensity_eq [Finite iota]
    (p q : PMF iota) (hsupport : p.support ⊆ q.support) :
    letI : MeasurableSpace iota := ⊤
    q.toMeasure.withDensity (pmfDensity p q) = p.toMeasure := by
  letI : MeasurableSpace iota := ⊤
  apply Measure.ext_of_singleton
  intro i
  rw [MeasureTheory.withDensity_apply _ (by simp), lintegral_singleton]
  rw [p.toMeasure_apply_singleton i (by simp), q.toMeasure_apply_singleton i (by simp)]
  unfold pmfDensity
  by_cases hq : q i = 0
  · have hp : p i = 0 := by
      by_contra hp
      exact ((q.mem_support_iff i).1
        (hsupport ((p.mem_support_iff i).2 hp))) hq
    simp [hp, hq]
  · exact ENNReal.div_mul_cancel hq (q.apply_ne_top i)

private theorem classicalRelEntropyPMF_eq_ofReal_logMomentDeriv_of_support
    (p q : PMF iota) (hsupport : p.support ⊆ q.support) :
    classicalRelEntropyPMF p q = ENNReal.ofReal (logMomentDeriv p q 1) := by
  letI : MeasurableSpace iota := ⊤
  letI : Nonempty (CommonSupport p q) :=
    commonSupport_nonempty_of_support p q hsupport
  have hac : p.toMeasure ≪ q.toMeasure :=
    (pmf_toMeasure_ac_iff_support p q).2 hsupport
  have hdensity_measurable : Measurable (pmfDensity p q) := by fun_prop
  have hrn_q : p.toMeasure.rnDeriv q.toMeasure =ᵐ[q.toMeasure] pmfDensity p q := by
    have h := Measure.rnDeriv_withDensity q.toMeasure hdensity_measurable
    rw [withDensity_pmfDensity_eq p q hsupport] at h
    exact h
  have hrn_p : p.toMeasure.rnDeriv q.toMeasure =ᵐ[p.toMeasure] pmfDensity p q :=
    hac.ae_eq hrn_q
  have hllr : llr p.toMeasure q.toMeasure =ᵐ[p.toMeasure]
      fun i ↦ Real.log ((pmfDensity p q i).toReal) := by
    filter_upwards [hrn_p] with i hi
    simp [llr, hi]
  rw [classicalRelEntropyPMF]
  rw [InformationTheory.klDiv_of_ac_of_integrable hac Integrable.of_finite]
  rw [integral_congr_ae hllr, PMF.integral_eq_sum]
  simp only [smul_eq_mul, pmfDensity, ENNReal.toReal_div]
  have hsum :
      ∑ i, (p i).toReal * Real.log ((p i).toReal / (q i).toReal) =
        momentDeriv p q 1 := by
    unfold momentDeriv rate
    simp only [sub_self, zero_mul, Real.exp_zero, mul_one]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or] at hi
    rcases hi with hp | hq
    · simp only [not_not] at hp
      simp [hp]
    · simp only [not_not] at hq
      have hp : p i = 0 := by
        by_contra hp
        exact ((q.mem_support_iff i).1
          (hsupport ((p.mem_support_iff i).2 hp))) hq
      simp [hp]
  rw [hsum]
  simp only [MeasureTheory.measureReal_def]
  simp only [measure_univ, ENNReal.toReal_one, add_sub_cancel_right]
  unfold logMomentDeriv
  rw [moment_one_eq_one_of_support p q hsupport, div_one]

private noncomputable def realRenyiValue (p q : PMF iota) (alpha : ℝ) : ℝ :=
  if alpha = 1 then logMomentDeriv p q 1
  else logMoment p q alpha / (alpha - 1)

private theorem realRenyiValue_monotone_of_support
    (p q : PMF iota) (hsupport : p.support ⊆ q.support)
    {alpha beta : ℝ} (hab : alpha ≤ beta) :
    realRenyiValue p q alpha ≤ realRenyiValue p q beta := by
  letI : Nonempty (CommonSupport p q) :=
    commonSupport_nonempty_of_support p q hsupport
  have hconvex := convexOn_logMoment p q
  have hmone : logMoment p q 1 = 0 := by
    simp [logMoment, moment_one_eq_one_of_support p q hsupport]
  by_cases halpha : alpha = 1
  · subst alpha
    by_cases hbeta : beta = 1
    · subst beta
      rfl
    · have hbeta1 : 1 < beta := lt_of_le_of_ne hab (Ne.symm hbeta)
      have hslope := hconvex.le_slope_of_hasDerivAt
        (by simp) (by simp) hbeta1 (hasDerivAt_logMoment p q 1)
      unfold realRenyiValue
      rw [if_pos rfl, if_neg hbeta]
      convert hslope using 1
      simp only [slope, hmone, sub_zero, vsub_eq_sub, smul_eq_mul]
      rw [div_eq_mul_inv, mul_comm]
  · by_cases hbeta : beta = 1
    · subst beta
      have halpha1 : alpha < 1 := lt_of_le_of_ne hab halpha
      have hslope := hconvex.slope_le_of_hasDerivAt
        (by simp) (by simp) halpha1 (hasDerivAt_logMoment p q 1)
      unfold realRenyiValue
      rw [if_neg halpha, if_pos rfl]
      convert hslope using 1
      simp only [slope, hmone, zero_sub, vsub_eq_sub, smul_eq_mul]
      rw [div_eq_mul_inv]
      rw [show alpha - 1 = -(1 - alpha) by ring, inv_neg]
      ring
    · have hsecant := hconvex.secant_mono (a := 1)
        (by simp) (by simp) (by simp) halpha hbeta hab
      simpa [realRenyiValue, halpha, hbeta, hmone] using hsecant

private theorem logMoment_div_monotone_below_one
    (p q : PMF iota) [Nonempty (CommonSupport p q)]
    {alpha beta : ℝ} (hab : alpha ≤ beta) (hbeta : beta < 1) :
    logMoment p q alpha / (alpha - 1) ≤
      logMoment p q beta / (beta - 1) := by
  have halpha : alpha < 1 := hab.trans_lt hbeta
  have hsecant := (convexOn_logMoment p q).secant_mono (a := 1)
    (by simp) (by simp) (by simp) halpha.ne hbeta.ne hab
  have hconstant :
      logMoment p q 1 / (alpha - 1) ≤
        logMoment p q 1 / (beta - 1) := by
    have h := div_le_div_of_nonneg_left
      (neg_nonneg.2 (logMoment_one_nonpos p q)) (sub_pos.2 hbeta)
      (sub_le_sub_left hab 1)
    have halphaRewrite :
        logMoment p q 1 / (alpha - 1) =
          -logMoment p q 1 / (1 - alpha) := by
      rw [show alpha - 1 = -(1 - alpha) by ring, div_neg, neg_div]
    have hbetaRewrite :
        logMoment p q 1 / (beta - 1) =
          -logMoment p q 1 / (1 - beta) := by
      rw [show beta - 1 = -(1 - beta) by ring, div_neg, neg_div]
    rw [halphaRewrite, hbetaRewrite]
    exact h
  calc
    logMoment p q alpha / (alpha - 1) =
        (logMoment p q alpha - logMoment p q 1) / (alpha - 1) +
          logMoment p q 1 / (alpha - 1) := by
            field_simp [halpha.ne]
            ring
    _ ≤ (logMoment p q beta - logMoment p q 1) / (beta - 1) +
          logMoment p q 1 / (beta - 1) := add_le_add hsecant hconstant
    _ = logMoment p q beta / (beta - 1) := by
      field_simp [hbeta.ne]
      ring

omit [Fintype iota] in
private theorem disjoint_support_of_commonSupport_isEmpty
    (p q : PMF iota) [IsEmpty (CommonSupport p q)] :
    Disjoint p.support q.support := by
  apply Set.disjoint_left.2
  intro i hip hiq
  exact isEmptyElim (⟨i, (p.mem_support_iff i).1 hip,
    (q.mem_support_iff i).1 hiq⟩ : CommonSupport p q)

private theorem classicalRelEntropyPMF_eq_top_of_supportMismatch
    (p q : PMF iota) (hmismatch : renyiSupportMismatch p q) :
    classicalRelEntropyPMF p q = ⊤ := by
  letI : MeasurableSpace iota := ⊤
  unfold classicalRelEntropyPMF
  apply InformationTheory.klDiv_of_not_ac
  rw [pmf_toMeasure_ac_iff_support p q]
  exact hmismatch

private theorem moment_eq_powerSum_toReal_of_lt_one
    (p q : PMF iota) {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    moment p q alpha =
      (renyiPowerSum ⟨alpha, halpha0⟩ p q).toReal := by
  classical
  unfold moment renyiPowerSum
  rw [ENNReal.toReal_sum]
  · calc
      (∑ i ∈ Finset.univ.filter (fun i ↦ p i ≠ 0 ∧ q i ≠ 0),
          (p i).toReal *
            Real.exp ((alpha - 1) * Real.log ((p i).toReal / (q i).toReal))) =
          ∑ i ∈ Finset.univ.filter (fun i ↦ p i ≠ 0 ∧ q i ≠ 0),
            (p i ^ alpha * q i ^ (1 - alpha)).toReal := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rcases hi with ⟨hp, hq⟩
        rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow]
        have hpr : 0 < (p i).toReal := ENNReal.toReal_pos hp (p.apply_ne_top i)
        have hqr : 0 < (q i).toReal := ENNReal.toReal_pos hq (q.apply_ne_top i)
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
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or] at hi
        rcases hi with hp | hq
        · simp only [not_not] at hp
          simp [hp, ENNReal.zero_rpow_of_pos halpha0]
        · simp only [not_not] at hq
          simp [hq, ENNReal.zero_rpow_of_pos (sub_pos.2 halpha1)]
  · intro i _
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg halpha0.le (p.apply_ne_top i))
      (ENNReal.rpow_ne_top_of_nonneg (sub_pos.2 halpha1).le (q.apply_ne_top i))

private theorem moment_eq_powerSum_toReal_of_one_lt_of_support
    (p q : PMF iota) {alpha : ℝ} (halpha1 : 1 < alpha)
    (hsupport : p.support ⊆ q.support) :
    moment p q alpha =
      (renyiPowerSum ⟨alpha, zero_lt_one.trans halpha1⟩ p q).toReal := by
  classical
  unfold moment renyiPowerSum
  rw [ENNReal.toReal_sum]
  · calc
      (∑ i ∈ Finset.univ.filter (fun i ↦ p i ≠ 0 ∧ q i ≠ 0),
          (p i).toReal *
            Real.exp ((alpha - 1) * Real.log ((p i).toReal / (q i).toReal))) =
          ∑ i ∈ Finset.univ.filter (fun i ↦ p i ≠ 0 ∧ q i ≠ 0),
            (p i ^ alpha * q i ^ (1 - alpha)).toReal := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rcases hi with ⟨hp, hq⟩
        rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow]
        have hpr : 0 < (p i).toReal := ENNReal.toReal_pos hp (p.apply_ne_top i)
        have hqr : 0 < (q i).toReal := ENNReal.toReal_pos hq (q.apply_ne_top i)
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
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or] at hi
        rcases hi with hp | hq
        · simp only [not_not] at hp
          simp [hp, ENNReal.zero_rpow_of_pos (zero_lt_one.trans halpha1)]
        · simp only [not_not] at hq
          have hp : p i = 0 := by
            by_contra hp
            exact ((q.mem_support_iff i).1
              (hsupport ((p.mem_support_iff i).2 hp))) hq
          simp [hp, ENNReal.zero_rpow_of_pos (zero_lt_one.trans halpha1)]
  · intro i _
    by_cases hp : p i = 0
    · simp [hp, ENNReal.zero_rpow_of_pos (zero_lt_one.trans halpha1)]
    · have hq : q i ≠ 0 := (q.mem_support_iff i).1
        (hsupport ((p.mem_support_iff i).2 hp))
      exact ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (zero_lt_one.trans halpha1).le (p.apply_ne_top i))
        (ENNReal.rpow_ne_top_of_ne_zero hq (q.apply_ne_top i))

private theorem classical_eq_ofReal_log_moment_div_of_lt_one
    (p q : PMF iota) [Nonempty (CommonSupport p q)]
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    classicalRenyiDivPMF ⟨alpha, halpha0⟩ p q =
      ENNReal.ofReal (Real.log (moment p q alpha) / (alpha - 1)) := by
  let order : RenyiOrder := ⟨alpha, halpha0⟩
  have hmoment : 0 < moment p q alpha := moment_pos p q alpha
  have hsumreal :
      (renyiPowerSum order p q).toReal = moment p q alpha := by
    simpa [order] using (moment_eq_powerSum_toReal_of_lt_one p q halpha0 halpha1).symm
  have hsumzero : renyiPowerSum order p q ≠ 0 := by
    intro h
    rw [h] at hsumreal
    simp at hsumreal
    exact hmoment.ne' hsumreal.symm
  rw [classicalRenyiDivPMF]
  simp only [halpha1.ne, ↓reduceIte, not_lt_of_ge halpha1.le,
    false_and]
  rw [if_neg (not_and_of_not_right _ hsumzero)]
  unfold renyiLogQuotient
  rw [ENNReal.log_pos_real' (hsumreal ▸ hmoment)]
  rw [hsumreal]
  rw [← EReal.coe_one, ← EReal.coe_sub, ← EReal.coe_inv, ← EReal.coe_mul,
    EReal.real_coe_toENNReal]
  congr 1
  rw [div_eq_mul_inv, mul_comm]

private theorem classical_eq_ofReal_log_moment_div_of_one_lt_of_support
    (p q : PMF iota) [Nonempty (CommonSupport p q)]
    {alpha : ℝ} (halpha1 : 1 < alpha) (hsupport : p.support ⊆ q.support) :
    classicalRenyiDivPMF ⟨alpha, zero_lt_one.trans halpha1⟩ p q =
      ENNReal.ofReal (Real.log (moment p q alpha) / (alpha - 1)) := by
  let order : RenyiOrder := ⟨alpha, zero_lt_one.trans halpha1⟩
  have hmoment : 0 < moment p q alpha := moment_pos p q alpha
  have hsumreal :
      (renyiPowerSum order p q).toReal = moment p q alpha := by
    simpa [order] using
      (moment_eq_powerSum_toReal_of_one_lt_of_support p q halpha1 hsupport).symm
  have hsumzero : renyiPowerSum order p q ≠ 0 := by
    intro h
    rw [h] at hsumreal
    simp at hsumreal
    exact hmoment.ne' hsumreal.symm
  rw [classicalRenyiDivPMF]
  simp only [halpha1.ne', halpha1, renyiSupportMismatch,
    not_not.mpr hsupport, and_false, false_and, not_lt_of_ge halpha1.le, ↓reduceIte]
  unfold renyiLogQuotient
  rw [ENNReal.log_pos_real' (hsumreal ▸ hmoment)]
  rw [hsumreal]
  rw [← EReal.coe_one, ← EReal.coe_sub, ← EReal.coe_inv, ← EReal.coe_mul,
    EReal.real_coe_toENNReal]
  congr 1
  rw [div_eq_mul_inv, mul_comm]

private theorem tendsto_order_coe_fromBelow :
    Tendsto (fun alpha : RenyiOrderBelowOne => (alpha.1 : ℝ)) atTop (𝓝[<] 1) := by
  have hrange :
      Set.range (fun alpha : RenyiOrderBelowOne => (alpha.1 : ℝ)) = Set.Ioo 0 1 := by
    ext x
    constructor
    · rintro ⟨alpha, rfl⟩
      exact ⟨alpha.1.property, alpha.property⟩
    · rintro ⟨hx0, hx1⟩
      exact ⟨⟨⟨x, hx0⟩, hx1⟩, rfl⟩
  have hmono : Monotone (fun alpha : RenyiOrderBelowOne => (alpha.1 : ℝ)) :=
    fun _ _ h ↦ h
  have hnhds :
      Tendsto (fun alpha : RenyiOrderBelowOne => (alpha.1 : ℝ)) atTop (𝓝 1) := by
    apply tendsto_atTop_isLUB hmono
    rw [hrange]
    exact isLUB_Ioo zero_lt_one
  exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hnhds
    (Filter.Eventually.of_forall fun alpha ↦ alpha.property)

private theorem tendsto_order_coe_fromAbove :
    Tendsto (fun alpha : RenyiOrder => (alpha : ℝ))
      (nhdsWithin RenyiOrder.one (Ioi RenyiOrder.one)) (𝓝[>] 1) := by
  have hnhds :
      Tendsto (fun alpha : RenyiOrder => (alpha : ℝ))
        (nhdsWithin RenyiOrder.one (Ioi RenyiOrder.one)) (𝓝 1) := by
    exact (continuous_subtype_val.tendsto RenyiOrder.one).mono_left inf_le_left
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hnhds
  filter_upwards [self_mem_nhdsWithin] with alpha halpha
  exact halpha

private theorem tendsto_classical_fromBelow_of_support
    (p q : PMF iota) (hsupport : p.support ⊆ q.support) :
    Tendsto
        (fun alpha : RenyiOrderBelowOne => classicalRenyiDivPMF alpha.1 p q)
        atTop (𝓝 (classicalRelEntropyPMF p q)) := by
  letI : Nonempty (CommonSupport p q) :=
    commonSupport_nonempty_of_support p q hsupport
  have hcoeNE :
      Tendsto (fun alpha : RenyiOrderBelowOne => (alpha.1 : ℝ)) atTop (𝓝[≠] 1) :=
    tendsto_order_coe_fromBelow.mono_right
      (nhdsWithin_mono 1 (by intro x hx; exact ne_of_lt hx))
  have hslope := (hasDerivAt_logMoment p q 1).tendsto_slope.comp hcoeNE
  have hratio :
      Tendsto
          (fun alpha : RenyiOrderBelowOne =>
            logMoment p q (alpha.1 : ℝ) / ((alpha.1 : ℝ) - 1))
          atTop (𝓝 (logMomentDeriv p q 1)) := by
    convert hslope using 1
    funext alpha
    simp only [Function.comp_apply, slope, vsub_eq_sub, smul_eq_mul]
    rw [show logMoment p q 1 = 0 by
      simp [logMoment, moment_one_eq_one_of_support p q hsupport]]
    rw [sub_zero, div_eq_mul_inv, mul_comm]
  rw [classicalRelEntropyPMF_eq_ofReal_logMomentDeriv_of_support p q hsupport]
  convert ENNReal.continuous_ofReal.continuousAt.tendsto.comp hratio using 1
  funext alpha
  exact (classical_eq_ofReal_log_moment_div_of_lt_one
    p q alpha.1.property alpha.property)

private theorem tendsto_classical_fromAbove_of_support
    (p q : PMF iota) (hsupport : p.support ⊆ q.support) :
    Tendsto
        (fun alpha : RenyiOrder => classicalRenyiDivPMF alpha p q)
        (nhdsWithin RenyiOrder.one (Ioi RenyiOrder.one))
        (𝓝 (classicalRelEntropyPMF p q)) := by
  letI : Nonempty (CommonSupport p q) :=
    commonSupport_nonempty_of_support p q hsupport
  have hcoeNE :
      Tendsto (fun alpha : RenyiOrder => (alpha : ℝ))
        (nhdsWithin RenyiOrder.one (Ioi RenyiOrder.one)) (𝓝[≠] 1) :=
    tendsto_order_coe_fromAbove.mono_right
      (nhdsWithin_mono 1 (by intro x hx; exact ne_of_gt hx))
  have hslope := (hasDerivAt_logMoment p q 1).tendsto_slope.comp hcoeNE
  have hratio :
      Tendsto
          (fun alpha : RenyiOrder =>
            logMoment p q (alpha : ℝ) / ((alpha : ℝ) - 1))
          (nhdsWithin RenyiOrder.one (Ioi RenyiOrder.one))
          (𝓝 (logMomentDeriv p q 1)) := by
    convert hslope using 1
    funext alpha
    simp only [Function.comp_apply, slope, vsub_eq_sub, smul_eq_mul]
    rw [show logMoment p q 1 = 0 by
      simp [logMoment, moment_one_eq_one_of_support p q hsupport]]
    rw [sub_zero, div_eq_mul_inv, mul_comm]
  rw [classicalRelEntropyPMF_eq_ofReal_logMomentDeriv_of_support p q hsupport]
  apply Filter.Tendsto.congr' _
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hratio)
  filter_upwards [self_mem_nhdsWithin] with alpha halpha
  change 1 < (alpha : ℝ) at halpha
  exact (classical_eq_ofReal_log_moment_div_of_one_lt_of_support
    p q halpha hsupport).symm

private theorem tendsto_classical_fromBelow_of_supportMismatch_nonempty
    (p q : PMF iota) [Nonempty (CommonSupport p q)]
    (hmismatch : renyiSupportMismatch p q) :
    Tendsto
        (fun alpha : RenyiOrderBelowOne => classicalRenyiDivPMF alpha.1 p q)
        atTop (𝓝 ⊤) := by
  have hcoe :
      Tendsto (fun alpha : RenyiOrderBelowOne => (alpha.1 : ℝ)) atTop (𝓝 1) :=
    tendsto_order_coe_fromBelow.mono_right inf_le_left
  have hlog :
      Tendsto (fun alpha : RenyiOrderBelowOne => logMoment p q (alpha.1 : ℝ))
        atTop (𝓝 (logMoment p q 1)) :=
    (hasDerivAt_logMoment p q 1).continuousAt.tendsto.comp hcoe
  have hlogNeg : logMoment p q 1 < 0 := by
    exact Real.log_neg (moment_pos p q 1)
      (moment_one_lt_one_of_supportMismatch p q hmismatch)
  have hdenNhds :
      Tendsto (fun alpha : RenyiOrderBelowOne => (alpha.1 : ℝ) - 1)
        atTop (𝓝 0) := by
    simpa using hcoe.sub_const 1
  have hden :
      Tendsto (fun alpha : RenyiOrderBelowOne => (alpha.1 : ℝ) - 1)
        atTop (𝓝[<] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hdenNhds
      (Filter.Eventually.of_forall fun alpha ↦ sub_neg.2 alpha.property)
  have hinv :
      Tendsto (fun alpha : RenyiOrderBelowOne => ((alpha.1 : ℝ) - 1)⁻¹)
        atTop atBot :=
    tendsto_inv_nhdsLT_zero.comp hden
  have hratio :
      Tendsto
          (fun alpha : RenyiOrderBelowOne =>
            logMoment p q (alpha.1 : ℝ) / ((alpha.1 : ℝ) - 1))
          atTop atTop := by
    simpa only [div_eq_mul_inv] using hlog.neg_mul_atBot hlogNeg hinv
  apply ENNReal.tendsto_ofReal_nhds_top.2 at hratio
  convert hratio using 1
  funext alpha
  exact (classical_eq_ofReal_log_moment_div_of_lt_one
    p q alpha.1.property alpha.property)

private theorem tendsto_classical_fromBelow_of_supportMismatch_empty
    (p q : PMF iota) [IsEmpty (CommonSupport p q)]
    (hmismatch : renyiSupportMismatch p q) :
    Tendsto
        (fun alpha : RenyiOrderBelowOne => classicalRenyiDivPMF alpha.1 p q)
        atTop (𝓝 (classicalRelEntropyPMF p q)) := by
  have hdisjoint := disjoint_support_of_commonSupport_isEmpty p q
  rw [classicalRelEntropyPMF_eq_top_of_supportMismatch p q hmismatch]
  have hfun :
      (fun alpha : RenyiOrderBelowOne => classicalRenyiDivPMF alpha.1 p q) =
        fun _ ↦ (⊤ : ℝ≥0∞) := by
    funext alpha
    exact classicalRenyiDivPMF_of_lt_one_of_disjoint_support
      alpha.1 p q alpha.property hdisjoint
  rw [hfun]
  exact tendsto_const_nhds

private theorem tendsto_classical_fromAbove_of_supportMismatch
    (p q : PMF iota) (hmismatch : renyiSupportMismatch p q) :
    Tendsto
        (fun alpha : RenyiOrder => classicalRenyiDivPMF alpha p q)
        (nhdsWithin RenyiOrder.one (Ioi RenyiOrder.one))
        (𝓝 (classicalRelEntropyPMF p q)) := by
  rw [classicalRelEntropyPMF_eq_top_of_supportMismatch p q hmismatch]
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with alpha halpha
  change 1 < (alpha : ℝ) at halpha
  exact (classicalRenyiDivPMF_of_one_lt_of_supportMismatch
    alpha p q halpha hmismatch).symm

end ClassicalRenyiOrder

/-- Classical finite-PMF Rényi divergence is monotone in its positive finite
order, including the exact order-one KL branch. -/
theorem classicalRenyiDivPMF_monotone_order
    {iota : Type} [Fintype iota] {alpha beta : RenyiOrder}
    (hab : alpha ≤ beta) (p q : PMF iota) :
    classicalRenyiDivPMF alpha p q ≤ classicalRenyiDivPMF beta p q := by
  classical
  by_cases hsupport : p.support ⊆ q.support
  · letI : Nonempty (ClassicalRenyiOrder.CommonSupport p q) :=
      ClassicalRenyiOrder.commonSupport_nonempty_of_support p q hsupport
    have hreal := ClassicalRenyiOrder.realRenyiValue_monotone_of_support
      p q hsupport hab
    have hformula (gamma : RenyiOrder) :
        classicalRenyiDivPMF gamma p q =
          ENNReal.ofReal (ClassicalRenyiOrder.realRenyiValue p q gamma) := by
      rcases gamma.lt_one_or_eq_one_or_one_lt with hlt | heq | hgt
      · rw [ClassicalRenyiOrder.classical_eq_ofReal_log_moment_div_of_lt_one
          p q gamma.property hlt]
        simp [ClassicalRenyiOrder.realRenyiValue, ClassicalRenyiOrder.logMoment, hlt.ne]
      · have hgamma : gamma = RenyiOrder.one := Subtype.ext heq
        subst gamma
        rw [classicalRenyiDivPMF_one,
          ClassicalRenyiOrder.classicalRelEntropyPMF_eq_ofReal_logMomentDeriv_of_support
            p q hsupport]
        simp [ClassicalRenyiOrder.realRenyiValue]
      · rw [ClassicalRenyiOrder.classical_eq_ofReal_log_moment_div_of_one_lt_of_support
          p q hgt hsupport]
        simp [ClassicalRenyiOrder.realRenyiValue, ClassicalRenyiOrder.logMoment, hgt.ne']
    rw [hformula alpha, hformula beta]
    exact ENNReal.ofReal_le_ofReal hreal
  · have hmismatch : renyiSupportMismatch p q := hsupport
    rcases beta.lt_one_or_eq_one_or_one_lt with hbeta | hbeta | hbeta
    · have halpha : (alpha : ℝ) < 1 := lt_of_le_of_lt hab hbeta
      cases isEmpty_or_nonempty (ClassicalRenyiOrder.CommonSupport p q) with
      | inl hempty =>
          letI := hempty
          have hdisjoint := ClassicalRenyiOrder.disjoint_support_of_commonSupport_isEmpty p q
          rw [classicalRenyiDivPMF_of_lt_one_of_disjoint_support alpha p q halpha hdisjoint,
            classicalRenyiDivPMF_of_lt_one_of_disjoint_support beta p q hbeta hdisjoint]
      | inr hnonempty =>
          letI := hnonempty
          rw [ClassicalRenyiOrder.classical_eq_ofReal_log_moment_div_of_lt_one
              p q alpha.property halpha,
            ClassicalRenyiOrder.classical_eq_ofReal_log_moment_div_of_lt_one
              p q beta.property hbeta]
          exact ENNReal.ofReal_le_ofReal
            (ClassicalRenyiOrder.logMoment_div_monotone_below_one p q hab hbeta)
    · have hbetaOrder : beta = RenyiOrder.one := Subtype.ext hbeta
      subst beta
      rw [classicalRenyiDivPMF_one,
        ClassicalRenyiOrder.classicalRelEntropyPMF_eq_top_of_supportMismatch p q hmismatch]
      exact le_top
    · rw [classicalRenyiDivPMF_of_one_lt_of_supportMismatch beta p q hbeta hmismatch]
      exact le_top

/-- Classical finite-PMF Rényi divergence converges from orders below one to
the existing order-one KL branch.  The index type makes the one-sided
approach explicit; this theorem does not assert a right or two-sided limit. -/
theorem classicalRenyiDivPMF_tendsto_kl_fromBelow
    {iota : Type} [Fintype iota] (p q : PMF iota) :
    Tendsto
        (fun alpha : RenyiOrderBelowOne => classicalRenyiDivPMF alpha.1 p q)
        atTop (𝓝 (classicalRelEntropyPMF p q)) := by
  classical
  by_cases hsupport : p.support ⊆ q.support
  · exact ClassicalRenyiOrder.tendsto_classical_fromBelow_of_support
      p q hsupport
  · cases isEmpty_or_nonempty (ClassicalRenyiOrder.CommonSupport p q) with
    | inl hempty =>
        letI := hempty
        exact ClassicalRenyiOrder.tendsto_classical_fromBelow_of_supportMismatch_empty
          p q hsupport
    | inr hnonempty =>
        letI := hnonempty
        rw [ClassicalRenyiOrder.classicalRelEntropyPMF_eq_top_of_supportMismatch
          p q hsupport]
        exact
          ClassicalRenyiOrder.tendsto_classical_fromBelow_of_supportMismatch_nonempty
            p q hsupport

/-- Classical finite-PMF Rényi divergence converges from orders above one to
the existing order-one KL branch.  The source filter is the strict upper
neighborhood of `RenyiOrder.one`. -/
theorem classicalRenyiDivPMF_tendsto_kl_fromAbove
    {iota : Type} [Fintype iota] (p q : PMF iota) :
    Tendsto
        (fun alpha : RenyiOrder => classicalRenyiDivPMF alpha p q)
        (nhdsWithin RenyiOrder.one (Ioi RenyiOrder.one))
        (𝓝 (classicalRelEntropyPMF p q)) := by
  classical
  by_cases hsupport : p.support ⊆ q.support
  · exact ClassicalRenyiOrder.tendsto_classical_fromAbove_of_support
      p q hsupport
  · exact ClassicalRenyiOrder.tendsto_classical_fromAbove_of_supportMismatch
      p q hsupport

end

end OPT
