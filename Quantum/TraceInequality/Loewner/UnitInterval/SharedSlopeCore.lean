import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Quantum.TraceInequality.Loewner.Kernel.FiniteMatrixData

/-!
# Shared unit-interval slope core

This module contains the route-neutral scalar slope facts shared by the
finite-order and operator-monotone arguments.
-/

namespace Quantum.TraceInequality.Loewner

noncomputable section

/-
The declarations below are shared by the Chapter 3 and Chapter 20 arguments of
Simon (2019); each of them was previously stated separately for the two arguments.
-/

/--
The slope inequality on `(-1, 1)` used in Hiai's regularity argument: for `a < c < b < d`
in `(-1, 1)`, writing `s x = slope f c x`,
`0 ≤ ((d - a) / (b - a)) * s a * s d - s a * s b - ((d - b) / (b - a)) * s b * s d`.
-/
def hiaiSlopeCoreOnUnitInterval (f : ℝ → ℝ) : Prop :=
  ∀ {a c b d : ℝ},
    a ∈ Set.Ioo (-1 : ℝ) 1 →
    b ∈ Set.Ioo (-1 : ℝ) 1 →
    c ∈ Set.Ioo (-1 : ℝ) 1 →
    d ∈ Set.Ioo (-1 : ℝ) 1 →
    a < c →
    c < b →
    b < d →
      0 ≤
        (((d - a) / (b - a)) * slope f c a * slope f c d -
          slope f c a * slope f c b -
          ((d - b) / (b - a)) * slope f c b * slope f c d)

/--
Scalar bound behind the slope estimates: if `A, D ≥ 0`, `q > 0`, `B = 0` whenever
`A = D = 0`, and `0 ≤ (1 + q) * A * D - A * B - q * B * D`, then `B ≤ D + q * D`.
-/
lemma hiai_core_le_far_add_q
    {A B D q : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hq : 0 < q)
    (hzero : A = 0 → D = 0 → B = 0)
    (hcore : 0 ≤ (1 + q) * A * D - A * B - q * B * D) :
    B ≤ D + q * D := by
  have hq_nonneg : 0 ≤ q := le_of_lt hq
  have hden_nonneg : 0 ≤ A + q * D := add_nonneg hA (mul_nonneg hq_nonneg hD)
  by_cases hden_zero : A + q * D = 0
  · have hA0 : A = 0 := by nlinarith
    have hD0 : D = 0 := by
      have hqD0 : q * D = 0 := by nlinarith
      exact (mul_eq_zero.mp hqD0).resolve_left (ne_of_gt hq)
    have hB0 : B = 0 := hzero hA0 hD0
    simp [hB0, hD0]
  · have hden_pos : 0 < A + q * D :=
      lt_of_le_of_ne hden_nonneg (Ne.symm hden_zero)
    have hBden : B * (A + q * D) ≤ (1 + q) * A * D := by
      nlinarith
    have htarget :
        (1 + q) * A * D ≤ (D + q * D) * (A + q * D) := by
      have hcalc :
          0 ≤ (D + q * D) * (A + q * D) - (1 + q) * A * D := by
        nlinarith [mul_nonneg hq_nonneg (sq_nonneg D),
          mul_nonneg (mul_nonneg hq_nonneg hq_nonneg) (sq_nonneg D)]
      nlinarith
    have hmul : B * (A + q * D) ≤ (D + q * D) * (A + q * D) :=
      le_trans hBden htarget
    exact le_of_mul_le_mul_right hmul hden_pos

/--
Scalar bound behind the slope estimates: under the hypotheses of `hiai_core_le_far_add_q`,
`B ≤ A + A / q`.
-/
lemma hiai_core_le_left_add_inv_q
    {A B D q : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hq : 0 < q)
    (hzero : A = 0 → D = 0 → B = 0)
    (hcore : 0 ≤ (1 + q) * A * D - A * B - q * B * D) :
    B ≤ A + A / q := by
  have hq_nonneg : 0 ≤ q := le_of_lt hq
  have hden_nonneg : 0 ≤ A + q * D := add_nonneg hA (mul_nonneg hq_nonneg hD)
  by_cases hden_zero : A + q * D = 0
  · have hA0 : A = 0 := by nlinarith
    have hD0 : D = 0 := by
      have hqD0 : q * D = 0 := by nlinarith
      exact (mul_eq_zero.mp hqD0).resolve_left (ne_of_gt hq)
    have hB0 : B = 0 := hzero hA0 hD0
    simp [hB0, hA0]
  · have hden_pos : 0 < A + q * D :=
      lt_of_le_of_ne hden_nonneg (Ne.symm hden_zero)
    have hBden : B * (A + q * D) ≤ (1 + q) * A * D := by
      nlinarith
    have htarget :
        (1 + q) * A * D ≤ (A + A / q) * (A + q * D) := by
      have hq_ne : q ≠ 0 := ne_of_gt hq
      have hcalc :
          0 ≤ (A + A / q) * (A + q * D) - (1 + q) * A * D := by
        field_simp [hq_ne]
        nlinarith [sq_nonneg A]
      nlinarith
    have hmul : B * (A + q * D) ≤ (A + A / q) * (A + q * D) :=
      le_trans hBden htarget
    exact le_of_mul_le_mul_right hmul hden_pos

/--
If `A, D ≥ 0`, `q > 0`, `0 < A + q * D` and `0 ≤ (1 + q) * A * D - A * B - q * B * D`,
then `B ≤ max A D`.
-/
lemma hiai_slopeCore_bound_of_posDen
    {A B D q : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hq : 0 < q)
    (hden : 0 < A + q * D)
    (hcore : 0 ≤ (1 + q) * A * D - A * B - q * B * D) :
    B ≤ max A D := by
  have hBden : B * (A + q * D) ≤ (1 + q) * A * D := by
    nlinarith
  have hmaxA : A ≤ max A D := le_max_left A D
  have hmaxD : D ≤ max A D := le_max_right A D
  have hq_nonneg : 0 ≤ q := le_of_lt hq
  have hprod :
      (1 + q) * A * D ≤ max A D * (A + q * D) := by
    have h1 : A * D ≤ max A D * A := by
      have h1' := mul_le_mul_of_nonneg_right hmaxD hA
      nlinarith [h1']
    have h2 : q * A * D ≤ max A D * (q * D) := by
      have h2' := mul_le_mul_of_nonneg_right hmaxA (mul_nonneg hq_nonneg hD)
      nlinarith [h2']
    nlinarith
  have hBden' : B * (A + q * D) ≤ max A D * (A + q * D) :=
    le_trans hBden hprod
  exact le_of_mul_le_mul_right hBden' hden

/--
For `f` monotone on `(-1, 1)` and `a < c < b < d` there, if the slopes of `f` from `c` to
`a` and from `c` to `d` vanish, then so does the slope from `c` to `b`.
-/
lemma hiai_slope_zeroAnchor_middle_eq_zero
    {f : ℝ → ℝ}
    (hmono : MonotoneOn f (Set.Ioo (-1 : ℝ) 1))
    {a c b d : ℝ} (_ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d)
    (hleft : slope f c a = 0) (hright : slope f c d = 0) :
    slope f c b = 0 := by
  have hfa : f a = f c := by
    have hne : a - c ≠ 0 := sub_ne_zero.mpr (ne_of_lt hac)
    rw [slope_def_field] at hleft
    field_simp [hne] at hleft
    have hzero : f a - f c = 0 := by simpa using hleft
    exact sub_eq_zero.mp hzero
  have hfd : f d = f c := by
    have hne : d - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans hcb hbd))
    rw [slope_def_field] at hright
    field_simp [hne] at hright
    have hzero : f d - f c = 0 := by simpa using hright
    exact sub_eq_zero.mp hzero
  have hcfb : f c ≤ f b := hmono hc hb hcb.le
  have hbfc : f b ≤ f c := by
    have hbfd : f b ≤ f d := hmono hb hd hbd.le
    simpa [hfd] using hbfd
  have hfb : f b = f c := le_antisymm hbfc hcfb
  rw [slope_def_field]
  simp [hfb]

/--
Under `hiaiSlopeCoreOnUnitInterval f` and monotonicity on `(-1, 1)`, for `a < c < b < d`
there, `slope f c b ≤ slope f c d + ((d - b) / (b - a)) * slope f c d`.
-/
lemma hiaiSlopeCore_rightSecant_le_far_addQ
    {f : ℝ → ℝ}
    (hmono : MonotoneOn f (Set.Ioo (-1 : ℝ) 1))
    (hcore : hiaiSlopeCoreOnUnitInterval f)
    {a c b d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d) :
    slope f c b ≤
      slope f c d + ((d - b) / (b - a)) * slope f c d := by
  let A := slope f c a
  let B := slope f c b
  let D := slope f c d
  let q := (d - b) / (b - a)
  have hA : 0 ≤ A :=
    MonotoneOn.slope_nonneg hmono hc ha
  have hD : 0 ≤ D :=
    MonotoneOn.slope_nonneg hmono hc hd
  have hq : 0 < q := by
    have hnum : 0 < d - b := sub_pos.mpr hbd
    have hden : 0 < b - a := sub_pos.mpr (lt_trans hac hcb)
    exact div_pos hnum hden
  have hzero : A = 0 → D = 0 → B = 0 := by
    intro hA0 hD0
    exact hiai_slope_zeroAnchor_middle_eq_zero
      hmono ha hb hc hd hac hcb hbd (by simpa [A] using hA0)
        (by simpa [D] using hD0)
  have hcore0 := hcore ha hb hc hd hac hcb hbd
  have hcore' :
      0 ≤ (1 + q) * A * D - A * B - q * B * D := by
    have hab : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans hac hcb))
    dsimp [A, B, D, q]
    convert hcore0 using 1
    field_simp [hab]
    ring
  simpa [A, B, D, q] using
    hiai_core_le_far_add_q hA hD hq hzero hcore'

/--
Under `hiaiSlopeCoreOnUnitInterval f` and monotonicity on `(-1, 1)`, for `a < c < b < d`
there, `slope f c b ≤ slope f c a + slope f c a / ((d - b) / (b - a))`.
-/
lemma hiaiSlopeCore_rightSecant_le_left_add_invQ
    {f : ℝ → ℝ}
    (hmono : MonotoneOn f (Set.Ioo (-1 : ℝ) 1))
    (hcore : hiaiSlopeCoreOnUnitInterval f)
    {a c b d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d) :
    slope f c b ≤
      slope f c a + slope f c a / ((d - b) / (b - a)) := by
  let A := slope f c a
  let B := slope f c b
  let D := slope f c d
  let q := (d - b) / (b - a)
  have hA : 0 ≤ A :=
    MonotoneOn.slope_nonneg hmono hc ha
  have hD : 0 ≤ D :=
    MonotoneOn.slope_nonneg hmono hc hd
  have hq : 0 < q := by
    have hnum : 0 < d - b := sub_pos.mpr hbd
    have hden : 0 < b - a := sub_pos.mpr (lt_trans hac hcb)
    exact div_pos hnum hden
  have hzero : A = 0 → D = 0 → B = 0 := by
    intro hA0 hD0
    exact hiai_slope_zeroAnchor_middle_eq_zero
      hmono ha hb hc hd hac hcb hbd (by simpa [A] using hA0)
        (by simpa [D] using hD0)
  have hcore0 := hcore ha hb hc hd hac hcb hbd
  have hcore' :
      0 ≤ (1 + q) * A * D - A * B - q * B * D := by
    have hab : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans hac hcb))
    dsimp [A, B, D, q]
    convert hcore0 using 1
    field_simp [hab]
    ring
  simpa [A, B, D, q] using
    hiai_core_le_left_add_inv_q hA hD hq hzero hcore'

/--
Under `hiaiSlopeCoreOnUnitInterval f` and monotonicity on `(-1, 1)`, for `a < c < b < d`
there, `slope f c b ≤ max (slope f c a) (slope f c d)`.
-/
lemma hiaiSlopeCore_rightSecant_maxBound
    {f : ℝ → ℝ}
    (hmono : MonotoneOn f (Set.Ioo (-1 : ℝ) 1))
    (hcore : hiaiSlopeCoreOnUnitInterval f)
    {a c b d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d) :
    slope f c b ≤ max (slope f c a) (slope f c d) := by
  let A := slope f c a
  let B := slope f c b
  let D := slope f c d
  let q := (d - b) / (b - a)
  have hA : 0 ≤ A :=
    MonotoneOn.slope_nonneg hmono hc ha
  have hD : 0 ≤ D :=
    MonotoneOn.slope_nonneg hmono hc hd
  have hq : 0 < q := by
    have hnum : 0 < d - b := sub_pos.mpr hbd
    have hden : 0 < b - a := sub_pos.mpr (lt_trans hac hcb)
    exact div_pos hnum hden
  by_cases hden : 0 < A + q * D
  · have hcore0 := hcore ha hb hc hd hac hcb hbd
    have hcore' :
        0 ≤ (1 + q) * A * D - A * B - q * B * D := by
      have hab : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans hac hcb))
      dsimp [A, B, D, q]
      convert hcore0 using 1
      field_simp [hab]
      ring
    simpa [A, B, D, q] using
      hiai_slopeCore_bound_of_posDen hA hD hq hden hcore'
  · have hsum_nonneg : 0 ≤ A + q * D := add_nonneg hA (mul_nonneg (le_of_lt hq) hD)
    have hsum_zero : A + q * D = 0 := le_antisymm (le_of_not_gt hden) hsum_nonneg
    have hA0 : A = 0 := by
      have hqD_nonneg : 0 ≤ q * D := mul_nonneg (le_of_lt hq) hD
      nlinarith
    have hD0 : D = 0 := by
      have hqD_zero : q * D = 0 := by nlinarith
      exact (mul_eq_zero.mp hqD_zero).resolve_left (ne_of_gt hq)
    have hmid :=
      hiai_slope_zeroAnchor_middle_eq_zero
        hmono ha hb hc hd hac hcb hbd (by simpa [A] using hA0) (by simpa [D] using hD0)
    simp [hmid, A, D, hA0, hD0]

/--
For `y ≠ x`, the slope of `f` between `x` and `y` is the Löwner kernel value
`loewnerKernel f x y`.
-/
theorem slope_eq_loewnerKernel_of_ne
    (f : ℝ → ℝ) {x y : ℝ} (hyx : y ≠ x) :
    slope f x y = loewnerKernel f x y := by
  rw [slope_fun_def_field]
  unfold loewnerKernel
  rw [if_neg hyx.symm]
  field_simp [sub_ne_zero.mpr hyx, sub_ne_zero.mpr hyx.symm]
  ring

/--
If `y < x < z` and `x` is the midpoint of `y` and `z`, then `slope f y z` is the average of
`slope f x y` and `slope f x z`.
-/
lemma slope_midpoint_cross_formula
    (f : ℝ → ℝ) {y x z : ℝ} (hyx : y < x) (_hxz : x < z)
    (hm : z - x = x - y) :
    slope f y z = (slope f x y + slope f x z) / 2 := by
  rw [slope_def_field, slope_def_field, slope_def_field]
  have hxy_ne : x - y ≠ 0 := sub_ne_zero.mpr (ne_of_gt hyx)
  have hzy_eq : z - y = 2 * (x - y) := by linarith
  have hzx_eq : z - x = x - y := hm
  have hyx_eq : y - x = -(x - y) := by ring
  rw [hzy_eq, hzx_eq, hyx_eq]
  field_simp [hxy_ne]
  ring

end

end Quantum.TraceInequality.Loewner
