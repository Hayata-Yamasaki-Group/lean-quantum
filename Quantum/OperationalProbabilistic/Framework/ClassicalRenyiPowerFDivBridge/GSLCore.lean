/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.ClassicalFDivConcrete.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivDPI.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiRelativeEntropy.GSLCore

open scoped BigOperators ENNReal NNReal

/-!
# Rényi power sums as power f-divergences

The closed-perspective terms of the power generator are identified with the Rényi power-sum
terms for orders above and below one, and the Rényi power sum is one plus the power
f-divergence sum (`renyiPowerSum_eq_one_add_powerFDivSum_of_one_lt`,
`renyiPowerSum_eq_one_add_powerFDivSum_of_lt_one`).  Above order one the power sum is at least
one.  Finite-sum identities in `EReal` are included.
-/

namespace OPT

noncomputable section

/-! # B. The endpoint-closed power-sum bridge -/

private lemma powerClosedPerspective_term_eq_of_one_lt
    (alpha : RenyiOrder) (halpha : 1 < (alpha : ℝ)) (a b : ℝ≥0) :
    ((((a : ℝ≥0∞) ^ (alpha : ℝ) *
          (b : ℝ≥0∞) ^ (1 - (alpha : ℝ))) : ℝ≥0∞) : EReal) =
      ((b : ℝ) : EReal) +
        (((alpha : ℝ) - 1 : ℝ) : EReal) *
          closedPerspective (powerFDivGenerator alpha halpha.ne') a b := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      simp [closedPerspective, ENNReal.zero_rpow_of_pos alpha.property,
        ENNReal.zero_rpow_of_neg (sub_neg.mpr halpha)]
    · simp only [ENNReal.coe_zero]
      rw [ENNReal.zero_rpow_of_pos alpha.property, zero_mul,
        closedPerspective_zero_left _ b hb]
      simp only [powerFDivGenerator, EReal.coe_ennreal_zero]
      have hreal : (0 : ℝ) = (b : ℝ) + ((alpha : ℝ) - 1) *
          ((b : ℝ) * (-1 / ((alpha : ℝ) - 1))) := by
        have hc : (alpha : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr halpha)
        field_simp [hc]
        ring
      exact_mod_cast hreal
  · by_cases hb : b = 0
    · subst b
      simp only [ENNReal.coe_zero]
      rw [ENNReal.zero_rpow_of_neg (sub_neg.mpr halpha),
        closedPerspective_zero_right _ a ha]
      have haPos : 0 < ((a : ℝ) : EReal) := by positivity
      have hcPos : 0 < ((alpha : ℝ) : EReal) - 1 := by
        exact_mod_cast sub_pos.mpr halpha
      simp only [powerFDivGenerator, if_pos halpha]
      rw [ENNReal.mul_top]
      · rw [EReal.mul_top_of_pos haPos]
        simp only [EReal.coe_ennreal_top, NNReal.coe_zero, EReal.coe_zero,
          EReal.coe_sub, EReal.coe_one, zero_add]
        exact (EReal.mul_top_of_pos hcPos).symm
      · exact (ENNReal.rpow_pos (by exact_mod_cast pos_iff_ne_zero.mpr ha)
          ENNReal.coe_ne_top).ne'
    · rw [closedPerspective_of_ne_zero _ a b ha hb]
      simp only [powerFDivGenerator]
      rw [← ENNReal.coe_rpow_of_ne_zero ha,
        ← ENNReal.coe_rpow_of_ne_zero hb, ← ENNReal.coe_mul,
        EReal.coe_nnreal_eq_coe_real]
      norm_cast
      simp only [NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_div]
      have hbPos : 0 < (b : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hb
      rw [mul_powerFDivFunction_div alpha (by positivity) hbPos]
      have hreal :
          (a : ℝ) ^ (alpha : ℝ) * (b : ℝ) ^ (1 - (alpha : ℝ)) =
            (b : ℝ) + ((alpha : ℝ) - 1) *
              (((a : ℝ) ^ (alpha : ℝ) *
                  (b : ℝ) ^ (1 - (alpha : ℝ)) - (b : ℝ)) /
                ((alpha : ℝ) - 1)) := by
        have hc : (alpha : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr halpha)
        field_simp [hc]
        ring
      exact_mod_cast hreal

private lemma powerClosedPerspective_term_eq_of_lt_one
    (alpha : RenyiOrder) (halpha : (alpha : ℝ) < 1) (a b : ℝ≥0) :
    ((((a : ℝ≥0∞) ^ (alpha : ℝ) *
          (b : ℝ≥0∞) ^ (1 - (alpha : ℝ))) : ℝ≥0∞) : EReal) =
      ((b : ℝ) : EReal) +
        (((alpha : ℝ) - 1 : ℝ) : EReal) *
          closedPerspective (powerFDivGenerator alpha halpha.ne) a b := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      simp [closedPerspective, ENNReal.zero_rpow_of_pos alpha.property,
        ENNReal.zero_rpow_of_pos (sub_pos.mpr halpha)]
    · simp only [ENNReal.coe_zero]
      rw [ENNReal.zero_rpow_of_pos alpha.property, zero_mul,
        closedPerspective_zero_left _ b hb]
      simp only [powerFDivGenerator, EReal.coe_ennreal_zero]
      have hreal : (0 : ℝ) = (b : ℝ) + ((alpha : ℝ) - 1) *
          ((b : ℝ) * (-1 / ((alpha : ℝ) - 1))) := by
        have hc : (alpha : ℝ) - 1 ≠ 0 := ne_of_lt (sub_neg.mpr halpha)
        field_simp [hc]
        ring
      exact_mod_cast hreal
  · by_cases hb : b = 0
    · subst b
      simp only [ENNReal.coe_zero]
      rw [ENNReal.zero_rpow_of_pos (sub_pos.mpr halpha), mul_zero,
        closedPerspective_zero_right _ a ha]
      simp [powerFDivGenerator, not_lt.mpr halpha.le]
    · rw [closedPerspective_of_ne_zero _ a b ha hb]
      simp only [powerFDivGenerator]
      rw [← ENNReal.coe_rpow_of_ne_zero ha,
        ← ENNReal.coe_rpow_of_ne_zero hb, ← ENNReal.coe_mul,
        EReal.coe_nnreal_eq_coe_real]
      norm_cast
      simp only [NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_div]
      have hbPos : 0 < (b : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hb
      rw [mul_powerFDivFunction_div alpha (by positivity) hbPos]
      have hreal :
          (a : ℝ) ^ (alpha : ℝ) * (b : ℝ) ^ (1 - (alpha : ℝ)) =
            (b : ℝ) + ((alpha : ℝ) - 1) *
              (((a : ℝ) ^ (alpha : ℝ) *
                  (b : ℝ) ^ (1 - (alpha : ℝ)) - (b : ℝ)) /
                ((alpha : ℝ) - 1)) := by
        have hc : (alpha : ℝ) - 1 ≠ 0 := ne_of_lt (sub_neg.mpr halpha)
        field_simp [hc]
        ring
      exact_mod_cast hreal

private lemma EReal_coe_ennreal_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ≥0∞) :
    (((∑ i ∈ s, f i : ℝ≥0∞)) : EReal) =
      ∑ i ∈ s, ((f i : ℝ≥0∞) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      simp only [Finset.sum_insert, hx, not_false_eq_true]
      rw [EReal.coe_ennreal_add, ih]

private lemma EReal_coe_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, ((f i : ℝ) : EReal) = (((∑ i ∈ s, f i : ℝ)) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      simp only [Finset.sum_insert, hx, not_false_eq_true]
      rw [ih, ← EReal.coe_add]

private lemma pmf_toNNReal_sum {ι : Type} [Fintype ι] (p : PMF ι) :
    ∑ i, (p i).toNNReal = 1 := by
  rw [← ENNReal.toNNReal_sum (s := Finset.univ)
    (fun i _hi => p.apply_ne_top i)]
  have hsum : ∑ i, p i = 1 := by
    simpa only [tsum_fintype] using p.tsum_coe
  rw [hsum]
  simp

private lemma pmf_toNNReal_sum_EReal {ι : Type} [Fintype ι] (p : PMF ι) :
    ∑ i, ((((p i).toNNReal : ℝ)) : EReal) = 1 := by
  have h := pmf_toNNReal_sum p
  have hR : ∑ i, ((p i).toNNReal : ℝ) = 1 := by exact_mod_cast h
  rw [EReal_coe_finset_sum Finset.univ, hR]
  rfl

private lemma EReal_mul_finset_sum_of_nonneg_coeff {ι : Type*}
    (s : Finset ι) (c : EReal) (hc : 0 ≤ c) (hcTop : c ≠ ⊤)
    (f : ι → EReal) :
    c * (∑ i ∈ s, f i) = ∑ i ∈ s, c * f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      simp only [Finset.sum_insert, hx, not_false_eq_true]
      rw [EReal.left_distrib_of_nonneg_of_ne_top hc hcTop, ih]

private lemma EReal_finset_sum_ne_top {ι : Type*} (s : Finset ι)
    (f : ι → EReal) (hf : ∀ i ∈ s, f i ≠ ⊤) :
    ∑ i ∈ s, f i ≠ ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      simp only [Finset.sum_insert, hx, not_false_eq_true]
      exact EReal.add_ne_top (hf x (Finset.mem_insert_self x s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

private lemma EReal_finset_sum_ne_bot {ι : Type*} (s : Finset ι)
    (f : ι → EReal) (hf : ∀ i ∈ s, f i ≠ ⊥) :
    ∑ i ∈ s, f i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      simp only [Finset.sum_insert, hx, not_false_eq_true]
      exact EReal.add_ne_bot_iff.mpr
        ⟨hf x (Finset.mem_insert_self x s),
          ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))⟩

private lemma EReal_left_distrib_of_finite (c x y : EReal)
    (hcTop : c ≠ ⊤) (hcBot : c ≠ ⊥)
    (hxTop : x ≠ ⊤) (hxBot : x ≠ ⊥)
    (hyTop : y ≠ ⊤) (hyBot : y ≠ ⊥) :
    c * (x + y) = c * x + c * y := by
  lift c to ℝ using ⟨hcTop, hcBot⟩
  lift x to ℝ using ⟨hxTop, hxBot⟩
  lift y to ℝ using ⟨hyTop, hyBot⟩
  simp only [← EReal.coe_add, ← EReal.coe_mul]
  ring_nf

private lemma EReal_mul_finset_sum_of_finite {ι : Type*}
    (s : Finset ι) (c : EReal) (hcTop : c ≠ ⊤) (hcBot : c ≠ ⊥)
    (f : ι → EReal) (hfTop : ∀ i ∈ s, f i ≠ ⊤)
    (hfBot : ∀ i ∈ s, f i ≠ ⊥) :
    c * (∑ i ∈ s, f i) = ∑ i ∈ s, c * f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      simp only [Finset.sum_insert, hx, not_false_eq_true]
      rw [EReal_left_distrib_of_finite c (f x) (∑ i ∈ s, f i)
        hcTop hcBot (hfTop x (Finset.mem_insert_self x s))
        (hfBot x (Finset.mem_insert_self x s))
        (EReal_finset_sum_ne_top s f
          (fun i hi => hfTop i (Finset.mem_insert_of_mem hi)))
        (EReal_finset_sum_ne_bot s f
          (fun i hi => hfBot i (Finset.mem_insert_of_mem hi))),
        ih (fun i hi => hfTop i (Finset.mem_insert_of_mem hi))
          (fun i hi => hfBot i (Finset.mem_insert_of_mem hi))]

private lemma powerClosedPerspective_ne_top_of_lt_one
    (alpha : RenyiOrder) (halpha : (alpha : ℝ) < 1) (a b : ℝ≥0) :
    closedPerspective (powerFDivGenerator alpha halpha.ne) a b ≠ ⊤ := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      simp
    · rw [closedPerspective_zero_left _ b hb]
      simp only [powerFDivGenerator]
      rw [← EReal.coe_mul]
      exact EReal.coe_ne_top _
  · by_cases hb : b = 0
    · subst b
      rw [closedPerspective_zero_right _ a ha]
      simp [powerFDivGenerator, not_lt.mpr halpha.le]
    · rw [closedPerspective_of_ne_zero _ a b ha hb]
      exact EReal.coe_ne_top _

/-! # C. Power sums from the raw power f-divergence -/

/-- Above order one, the endpoint-closed power f-divergence recovers the
Rényi power sum, including the `q i = 0 < p i` infinite branch. -/
lemma renyiPowerSum_eq_one_add_powerFDivSum_of_one_lt
    (alpha : RenyiOrder) (halpha : 1 < (alpha : ℝ))
    {ι : Type} [Fintype ι] (p q : PMF ι) :
    (renyiPowerSum alpha p q : EReal) =
      1 + ((((alpha : ℝ) - 1 : ℝ)) : EReal) *
        classicalFDivSum (powerFDivGenerator alpha halpha.ne') p q := by
  classical
  have hc : 0 ≤ (((alpha : ℝ) - 1 : ℝ) : EReal) := by
    exact_mod_cast sub_nonneg.mpr halpha.le
  calc
    (renyiPowerSum alpha p q : EReal) =
        ∑ i, ((((p i) ^ (alpha : ℝ) *
          (q i) ^ (1 - (alpha : ℝ))) : ℝ≥0∞) : EReal) := by
      unfold renyiPowerSum
      exact EReal_coe_ennreal_finset_sum Finset.univ _
    _ = ∑ i, (((((q i).toNNReal : ℝ)) : EReal) +
        ((((alpha : ℝ) - 1 : ℝ)) : EReal) *
          closedPerspective (powerFDivGenerator alpha halpha.ne')
            (p i).toNNReal (q i).toNNReal) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simpa only [ENNReal.coe_toNNReal (p.apply_ne_top i),
        ENNReal.coe_toNNReal (q.apply_ne_top i)] using
          powerClosedPerspective_term_eq_of_one_lt alpha halpha
            (p i).toNNReal (q i).toNNReal
    _ = (∑ i, ((((q i).toNNReal : ℝ)) : EReal)) +
        ∑ i, ((((alpha : ℝ) - 1 : ℝ)) : EReal) *
          closedPerspective (powerFDivGenerator alpha halpha.ne')
            (p i).toNNReal (q i).toNNReal := Finset.sum_add_distrib
    _ = 1 + ((((alpha : ℝ) - 1 : ℝ)) : EReal) *
        classicalFDivSum (powerFDivGenerator alpha halpha.ne') p q := by
      rw [pmf_toNNReal_sum_EReal q]
      unfold classicalFDivSum
      rw [EReal_mul_finset_sum_of_nonneg_coeff Finset.univ
        ((((alpha : ℝ) - 1 : ℝ)) : EReal) hc
        (EReal.coe_ne_top _) (fun i =>
          closedPerspective (powerFDivGenerator alpha halpha.ne')
            (p i).toNNReal (q i).toNNReal)]

/-- Below order one, the same identity is finite in every boundary branch;
the negative coefficient is therefore distributed through a finite real
sum without an indeterminate extended-real operation. -/
lemma renyiPowerSum_eq_one_add_powerFDivSum_of_lt_one
    (alpha : RenyiOrder) (halpha : (alpha : ℝ) < 1)
    {ι : Type} [Fintype ι] (p q : PMF ι) :
    (renyiPowerSum alpha p q : EReal) =
      1 + ((((alpha : ℝ) - 1 : ℝ)) : EReal) *
        classicalFDivSum (powerFDivGenerator alpha halpha.ne) p q := by
  classical
  calc
    (renyiPowerSum alpha p q : EReal) =
        ∑ i, ((((p i) ^ (alpha : ℝ) *
          (q i) ^ (1 - (alpha : ℝ))) : ℝ≥0∞) : EReal) := by
      unfold renyiPowerSum
      exact EReal_coe_ennreal_finset_sum Finset.univ _
    _ = ∑ i, (((((q i).toNNReal : ℝ)) : EReal) +
        ((((alpha : ℝ) - 1 : ℝ)) : EReal) *
          closedPerspective (powerFDivGenerator alpha halpha.ne)
            (p i).toNNReal (q i).toNNReal) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simpa only [ENNReal.coe_toNNReal (p.apply_ne_top i),
        ENNReal.coe_toNNReal (q.apply_ne_top i)] using
          powerClosedPerspective_term_eq_of_lt_one alpha halpha
            (p i).toNNReal (q i).toNNReal
    _ = (∑ i, ((((q i).toNNReal : ℝ)) : EReal)) +
        ∑ i, ((((alpha : ℝ) - 1 : ℝ)) : EReal) *
          closedPerspective (powerFDivGenerator alpha halpha.ne)
            (p i).toNNReal (q i).toNNReal := Finset.sum_add_distrib
    _ = 1 + ((((alpha : ℝ) - 1 : ℝ)) : EReal) *
        classicalFDivSum (powerFDivGenerator alpha halpha.ne) p q := by
      rw [pmf_toNNReal_sum_EReal q]
      unfold classicalFDivSum
      rw [EReal_mul_finset_sum_of_finite Finset.univ
        ((((alpha : ℝ) - 1 : ℝ)) : EReal)
        (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
        (fun i => closedPerspective (powerFDivGenerator alpha halpha.ne)
          (p i).toNNReal (q i).toNNReal)
        (fun i _hi => powerClosedPerspective_ne_top_of_lt_one alpha halpha
          (p i).toNNReal (q i).toNNReal)
        (fun i _hi => closedPerspective_ne_bot
          (powerFDivGenerator alpha halpha.ne)
          (p i).toNNReal (q i).toNNReal)]

/-! # D. Power sums above order one -/

/-- A finite-PMF Rényi power sum is at least one above order one. -/
theorem one_le_renyiPowerSum_of_one_lt
    (alpha : RenyiOrder) (halpha : 1 < (alpha : ℝ))
    {ι : Type} [Fintype ι] (p q : PMF ι) :
    1 ≤ renyiPowerSum alpha p q := by
  have hraw := classicalFDivSum_nonnegative
    (powerFDivGenerator alpha halpha.ne') p q
  have hc : 0 ≤ ((((alpha : ℝ) - 1 : ℝ)) : EReal) := by
    exact_mod_cast sub_nonneg.mpr halpha.le
  have hterm : 0 ≤ ((((alpha : ℝ) - 1 : ℝ)) : EReal) *
      classicalFDivSum (powerFDivGenerator alpha halpha.ne') p q :=
    EReal.mul_nonneg hc hraw
  have hcoe : ((1 : ℝ≥0∞) : EReal) ≤
      (renyiPowerSum alpha p q : EReal) := by
    rw [renyiPowerSum_eq_one_add_powerFDivSum_of_one_lt alpha halpha p q]
    calc
      ((1 : ℝ≥0∞) : EReal) = 1 + 0 := by simp
      _ ≤ 1 + ((((alpha : ℝ) - 1 : ℝ)) : EReal) *
          classicalFDivSum (powerFDivGenerator alpha halpha.ne') p q := by
        simpa [add_comm] using add_le_add_left hterm 1
  exact EReal.coe_ennreal_le_coe_ennreal_iff.mp hcoe
end

end OPT
