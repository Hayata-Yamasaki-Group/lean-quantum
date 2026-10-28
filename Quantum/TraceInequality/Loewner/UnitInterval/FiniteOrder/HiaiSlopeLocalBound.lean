import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.RegularizedSecondDerivativeLimit
import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.TwoThreePointDiagnostics
import Quantum.Analysis.Calculus.SharedSecantFilter
import Quantum.TraceInequality.Loewner.UnitInterval.SharedSlopeCore

/-!
# Chapter 20 Hiai slope local-bound package

This file contains the local secant-oscillation package and the public C1
regularity wrappers that use the Hiai slope core.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped Interval
open scoped ComplexOrder
open scoped MatrixOrder
open scoped NNReal
open scoped ENNReal
open scoped Convolution
open scoped fwdDiff

noncomputable section

/--
The Hiai slope-core gives a local positive upper bound for punctured secants
based at any interior point.
-/
lemma hiaiSlopeCore_local_secant_bound
    {f : ℝ → ℝ}
    (hmono : MonotoneOn f (Set.Ioo (-1 : ℝ) 1))
    (hcore : hiaiSlopeCoreOnUnitInterval f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∃ δ > 0, ∃ M > 0,
      ∀ {y : ℝ},
        y ∈ Set.Ioo (-1 : ℝ) 1 →
        y ≠ x →
        dist y x < δ →
          0 ≤ slope f x y ∧ slope f x y ≤ M := by
  rcases exists_between hx.1 with ⟨a, ha_left, hax⟩
  rcases exists_between hx.2 with ⟨d, hxd, hd_right⟩
  let δ : ℝ := min ((x - a) / 2) ((d - x) / 2)
  have hδ_pos : 0 < δ := by
    have hleft : 0 < (x - a) / 2 := by linarith
    have hright : 0 < (d - x) / 2 := by linarith
    exact lt_min hleft hright
  let fixedM : ℝ := max (slope f x a) (slope f x d)
  let leftM : ℝ := (f d - f a) / ((x - a) / 2)
  let rightM : ℝ := (f d - f a) / ((d - x) / 2)
  let M : ℝ := max fixedM (max leftM rightM) + 1
  have haI : a ∈ Set.Ioo (-1 : ℝ) 1 := ⟨ha_left, lt_trans hax hx.2⟩
  have hdI : d ∈ Set.Ioo (-1 : ℝ) 1 := ⟨lt_trans hx.1 hxd, hd_right⟩
  have hfd_fa_nonneg : 0 ≤ f d - f a := by
    exact sub_nonneg.mpr (hmono haI hdI (le_of_lt (lt_trans hax hxd)))
  have hleftDen_pos : 0 < (x - a) / 2 := by linarith
  have hrightDen_pos : 0 < (d - x) / 2 := by linarith
  have hM_pos : 0 < M := by
    have hleft_nonneg : 0 ≤ (f d - f a) / ((x - a) / 2) :=
      div_nonneg hfd_fa_nonneg (le_of_lt hleftDen_pos)
    have hleftM_nonneg : 0 ≤ leftM := by
      dsimp [leftM]
      exact hleft_nonneg
    have hmax_nonneg : 0 ≤ max leftM rightM := by
      exact le_max_of_le_left hleftM_nonneg
    have hbase_nonneg : 0 ≤ max fixedM (max leftM rightM) :=
      le_trans hmax_nonneg (le_max_right fixedM (max leftM rightM))
    dsimp [M]
    linarith
  refine ⟨δ, hδ_pos, M, hM_pos, ?_⟩
  intro y hy hy_ne hdist
  have hnonneg : 0 ≤ slope f x y :=
    MonotoneOn.slope_nonneg hmono hx hy
  have hdist_abs : |y - x| < δ := by
    simpa [Real.dist_eq] using hdist
  have hδ_le_left : δ ≤ (x - a) / 2 := min_le_left _ _
  have hδ_le_right : δ ≤ (d - x) / 2 := min_le_right _ _
  have hupper : slope f x y ≤ M := by
    by_cases hxy : x < y
    · have hyd : y < d := by
        have hy_gap : y - x < (d - x) / 2 := by
          have habs : |y - x| = y - x :=
            abs_of_nonneg (sub_nonneg.mpr hxy.le)
          exact lt_of_lt_of_le (by simpa [habs] using hdist_abs) hδ_le_right
        linarith
      have hbound := hiaiSlopeCore_rightSecant_maxBound
        hmono hcore haI hy hx hdI hax hxy hyd
      have hfixed_le_M : fixedM ≤ M := by
        dsimp [M]
        exact le_trans (le_max_left fixedM (max leftM rightM)) (by linarith)
      exact le_trans hbound hfixed_le_M
    · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hxy) hy_ne
      have hay : a < y := by
        have hy_gap : x - y < (x - a) / 2 := by
          have habs : |y - x| = x - y := by
            rw [abs_of_nonpos (sub_nonpos.mpr hyx.le)]
            ring
          exact lt_of_lt_of_le (by simpa [habs] using hdist_abs) hδ_le_left
        linarith
      have hbound_center_y := hiaiSlopeCore_rightSecant_maxBound
        hmono hcore haI hx hy hdI hay hyx hxd
      have hslope_yx : slope f x y = slope f y x := slope_comm f x y
      have hya_le_leftM : slope f y a ≤ leftM := by
        have hfy_fd : f y ≤ f d := hmono hy hdI (le_of_lt (lt_trans hyx hxd))
        have hfa_fy : f a ≤ f y := hmono haI hy (le_of_lt hay)
        have hnum_nonneg : 0 ≤ f y - f a := sub_nonneg.mpr hfa_fy
        have hnum_le : f y - f a ≤ f d - f a := by linarith
        have hden_lower : (x - a) / 2 ≤ y - a := by
          have hy_gap : x - y < (x - a) / 2 := by
            have habs : |y - x| = x - y := by
              rw [abs_of_nonpos (sub_nonpos.mpr hyx.le)]
              ring
            exact lt_of_lt_of_le (by simpa [habs] using hdist_abs) hδ_le_left
          linarith
        have hdiv :
            (f y - f a) / (y - a) ≤ (f d - f a) / ((x - a) / 2) :=
          div_le_div₀ hfd_fa_nonneg hnum_le hleftDen_pos hden_lower
        rw [slope_comm f y a, slope_def_field]
        have hya_ne : y - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hay)
        field_simp [hya_ne]
        simpa [leftM] using hdiv
      have hyd_le_rightM : slope f y d ≤ rightM := by
        have hfy_fd : f y ≤ f d := hmono hy hdI (le_of_lt (lt_trans hyx hxd))
        have hfa_fy : f a ≤ f y := hmono haI hy (le_of_lt hay)
        have hnum_nonneg : 0 ≤ f d - f y := sub_nonneg.mpr hfy_fd
        have hnum_le : f d - f y ≤ f d - f a := by linarith
        have hden_lower : (d - x) / 2 ≤ d - y := by
          have hy_gap : x - y < (x - a) / 2 := by
            have habs : |y - x| = x - y := by
              rw [abs_of_nonpos (sub_nonpos.mpr hyx.le)]
              ring
            exact lt_of_lt_of_le (by simpa [habs] using hdist_abs) hδ_le_left
          linarith
        have hdiv :
            (f d - f y) / (d - y) ≤ (f d - f a) / ((d - x) / 2) :=
          div_le_div₀ hfd_fa_nonneg hnum_le hrightDen_pos hden_lower
        have hsd : slope f y d = (f d - f y) / (d - y) := by
          rw [slope_def_field]
        rw [hsd]
        simpa [rightM] using hdiv
      have hmax_anchor : max (slope f y a) (slope f y d) ≤ max leftM rightM :=
        max_le
          (le_trans hya_le_leftM (le_max_left leftM rightM))
          (le_trans hyd_le_rightM (le_max_right leftM rightM))
      have hmax_le_M : max leftM rightM ≤ M := by
        dsimp [M]
        exact le_trans (le_max_right fixedM (max leftM rightM)) (by linarith)
      exact le_trans (by simpa [hslope_yx] using hbound_center_y)
        (le_trans hmax_anchor hmax_le_M)
  exact ⟨hnonneg, hupper⟩

/--
Near an interior point, a right secant is bounded by a nearby left secant plus
an arbitrary additive error.
-/
theorem hiaiSlopeCore_rightSecant_le_left_add
    {f : ℝ → ℝ}
    (hmono : MonotoneOn f (Set.Ioo (-1 : ℝ) 1))
    (hcore : hiaiSlopeCoreOnUnitInterval f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ η > 0, ∃ δ > 0,
      ∀ {y z : ℝ},
        y ∈ Set.Ioo (-1 : ℝ) x →
        z ∈ Set.Ioo x (1 : ℝ) →
        dist y x < δ →
        dist z x < δ →
          slope f x z ≤ slope f x y + η := by
  intro η hη
  rcases hiaiSlopeCore_local_secant_bound hmono hcore hx with
    ⟨δ0, hδ0, M, hM_pos, hlocal⟩
  rcases exists_between hx.2 with ⟨d, hxd, hd_right⟩
  let δ : ℝ := min δ0 (min ((d - x) / 4) (η * (d - x) / (8 * M)))
  have hdI : d ∈ Set.Ioo (-1 : ℝ) 1 := ⟨lt_trans hx.1 hxd, hd_right⟩
  have hδ_pos : 0 < δ := by
    have hgap : 0 < (d - x) / 4 := by linarith
    have hsmall : 0 < η * (d - x) / (8 * M) := by
      exact div_pos (mul_pos hη (sub_pos.mpr hxd)) (mul_pos (by norm_num) hM_pos)
    exact lt_min hδ0 (lt_min hgap hsmall)
  refine ⟨δ, hδ_pos, ?_⟩
  intro y z hy hz hydist hzdist
  have hδ_le_δ0 : δ ≤ δ0 := min_le_left _ _
  have hδ_le_gap : δ ≤ (d - x) / 4 := by
    exact le_trans (min_le_right δ0 _) (min_le_left _ _)
  have hδ_le_small : δ ≤ η * (d - x) / (8 * M) := by
    exact le_trans (min_le_right δ0 _) (min_le_right _ _)
  have hyI : y ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hy.1, lt_trans hy.2 hx.2⟩
  have hzI : z ∈ Set.Ioo (-1 : ℝ) 1 := ⟨lt_trans hx.1 hz.1, hz.2⟩
  have hy_ne : y ≠ x := ne_of_lt hy.2
  have hydist0 : dist y x < δ0 := lt_of_lt_of_le hydist hδ_le_δ0
  have hleft_bound := (hlocal hyI hy_ne hydist0).2
  have hz_abs : |z - x| < δ := by
    simpa [Real.dist_eq] using hzdist
  have hz_gap : z - x < δ := by
    have habs : |z - x| = z - x := abs_of_nonneg (sub_nonneg.mpr hz.1.le)
    simpa [habs] using hz_abs
  have hzd : z < d := by
    have hzgap : z - x < (d - x) / 4 := lt_of_lt_of_le hz_gap hδ_le_gap
    linarith
  have hyz : y < z := lt_trans hy.2 hz.1
  have hq_pos : 0 < (d - z) / (z - y) := by
    exact div_pos (sub_pos.mpr hzd) (sub_pos.mpr hyz)
  have hzy_lt : z - y < 2 * δ := by
    have hy_abs : |y - x| < δ := by
      simpa [Real.dist_eq] using hydist
    have hy_gap : x - y < δ := by
      have habs : |y - x| = x - y := by
        rw [abs_of_nonpos (sub_nonpos.mpr hy.2.le)]
        ring
      simpa [habs] using hy_abs
    linarith
  have htarget_mul : M * (z - y) ≤ η * (d - z) := by
    have hzyle : z - y ≤ 2 * δ := le_of_lt hzy_lt
    have hM_nonneg : 0 ≤ M := le_of_lt hM_pos
    have h1 : M * (z - y) ≤ M * (2 * δ) :=
      mul_le_mul_of_nonneg_left hzyle hM_nonneg
    have h2small : M * (2 * δ) ≤ η * ((d - x) / 4) := by
      have hM_ne : M ≠ 0 := ne_of_gt hM_pos
      field_simp [hM_ne] at hδ_le_small ⊢
      nlinarith [hδ_le_small, hη, hxd, hM_pos]
    have h3 : η * ((d - x) / 4) ≤ η * (d - z) := by
      have hquarter : (d - x) / 4 ≤ d - z := by linarith
      exact mul_le_mul_of_nonneg_left hquarter (le_of_lt hη)
    exact le_trans h1 (le_trans h2small h3)
  have herror : slope f x y / ((d - z) / (z - y)) ≤ η := by
    have hM_le : M ≤ η * ((d - z) / (z - y)) := by
      rw [← mul_div_assoc, le_div_iff₀ (sub_pos.mpr hyz)]
      simpa [mul_comm, mul_left_comm, mul_assoc] using htarget_mul
    have hleft_le : slope f x y ≤ η * ((d - z) / (z - y)) :=
      le_trans hleft_bound hM_le
    rwa [div_le_iff₀ hq_pos]
  exact
    hiaiSlopeCore_rightSecant_le_left_add_of_invQ_le
      hmono hcore hyI hzI hx hdI hy.2 hz.1 hzd herror

/--
Near an interior point, a left secant is bounded by the mirrored right secant
plus an arbitrary additive error.
-/
theorem hiaiSlopeCore_leftSecant_le_mirrorRight_add
    {f : ℝ → ℝ}
    (hmono : MonotoneOn f (Set.Ioo (-1 : ℝ) 1))
    (hcore : hiaiSlopeCoreOnUnitInterval f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ η > 0, ∃ δ > 0,
      ∀ {y : ℝ},
        y ∈ Set.Ioo (-1 : ℝ) x →
        dist y x < δ →
          slope f x y ≤ slope f x (2 * x - y) + η := by
  intro η hη
  rcases hiaiSlopeCore_local_secant_bound hmono hcore hx with
    ⟨δ0, hδ0, M, hM_pos, hlocal⟩
  rcases exists_between hx.1 with ⟨u, hu_left, hux⟩
  let δ : ℝ := min δ0 (min ((x - u) / 4) (min ((1 - x) / 4) (η * (x - u) / (8 * M))))
  have huI : u ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hu_left, lt_trans hux hx.2⟩
  have hδ_pos : 0 < δ := by
    have hleft : 0 < (x - u) / 4 := by linarith
    have hright : 0 < (1 - x) / 4 := by linarith [hx.2]
    have hsmall : 0 < η * (x - u) / (8 * M) := by
      exact div_pos (mul_pos hη (sub_pos.mpr hux)) (mul_pos (by norm_num) hM_pos)
    exact lt_min hδ0 (lt_min hleft (lt_min hright hsmall))
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy hydist
  let z : ℝ := 2 * x - y
  have hδ_le_δ0 : δ ≤ δ0 := min_le_left _ _
  have hδ_le_left : δ ≤ (x - u) / 4 := by
    exact le_trans (min_le_right δ0 _) (min_le_left _ _)
  have hδ_le_right : δ ≤ (1 - x) / 4 := by
    exact le_trans (le_trans (min_le_right δ0 _) (min_le_right _ _)) (min_le_left _ _)
  have hδ_le_small : δ ≤ η * (x - u) / (8 * M) := by
    exact le_trans (le_trans (min_le_right δ0 _) (min_le_right _ _)) (min_le_right _ _)
  have hyI : y ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hy.1, lt_trans hy.2 hx.2⟩
  have hy_ne : y ≠ x := ne_of_lt hy.2
  have hydist0 : dist y x < δ0 := lt_of_lt_of_le hydist hδ_le_δ0
  have hL_bound := (hlocal hyI hy_ne hydist0).2
  have hL_nonneg := (hlocal hyI hy_ne hydist0).1
  have hy_abs : |y - x| < δ := by
    simpa [Real.dist_eq] using hydist
  have hy_gap : x - y < δ := by
    have habs : |y - x| = x - y := by
      rw [abs_of_nonpos (sub_nonpos.mpr hy.2.le)]
      ring
    simpa [habs] using hy_abs
  have huy : u < y := by
    have hsmall : x - y < (x - u) / 4 := lt_of_lt_of_le hy_gap hδ_le_left
    linarith
  have hxz : x < z := by
    dsimp [z]
    linarith [hy.2]
  have hzx_eq : z - x = x - y := by
    dsimp [z]
    ring
  have hz_dist : dist z x < δ := by
    rw [Real.dist_eq]
    have hz_nonneg : 0 ≤ z - x := by linarith
    rw [abs_of_nonneg hz_nonneg, hzx_eq]
    exact hy_gap
  have hzdist0 : dist z x < δ0 := lt_of_lt_of_le hz_dist hδ_le_δ0
  have hz_lt_one : z < 1 := by
    have hzgap : z - x < (1 - x) / 4 := by
      rw [hzx_eq]
      exact lt_of_lt_of_le hy_gap hδ_le_right
    linarith
  have hzI : z ∈ Set.Ioo (-1 : ℝ) 1 := ⟨lt_trans hx.1 hxz, hz_lt_one⟩
  have hz_ne : z ≠ x := ne_of_gt hxz
  have hR_bound := (hlocal hzI hz_ne hzdist0).2
  have hR_nonneg := (hlocal hzI hz_ne hzdist0).1
  have hmid :
      slope f y z = (slope f x y + slope f x z) / 2 :=
    slope_midpoint_cross_formula f hy.2 hxz hzx_eq
  have hD_nonneg : 0 ≤ slope f y z := by
    rw [hmid]
    nlinarith
  have hD_bound : slope f y z ≤ M := by
    rw [hmid]
    nlinarith
  have hqD_error : ((z - x) / (x - u)) * slope f y z ≤ η / 2 := by
    have hzx_le_delta : z - x ≤ δ := by
      rw [hzx_eq]
      exact le_of_lt hy_gap
    have hmul_le : (z - x) * slope f y z ≤ δ * M :=
      mul_le_mul hzx_le_delta hD_bound hD_nonneg (le_of_lt hδ_pos)
    have hdeltaM : δ * M ≤ η * (x - u) / 8 := by
      have hM_ne : M ≠ 0 := ne_of_gt hM_pos
      field_simp [hM_ne] at hδ_le_small ⊢
      nlinarith [hδ_le_small, hη, hux, hM_pos]
    have hnum : (z - x) * slope f y z ≤ (η / 2) * (x - u) := by
      nlinarith [hmul_le, hdeltaM, hη, hux]
    rw [div_mul_eq_mul_div, div_le_iff₀ (sub_pos.mpr hux)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hnum
  have hfar := hiaiSlopeCore_rightSecant_le_far_add_of_qMul_le
    hmono hcore huI hx hyI hzI huy hy.2 hxz hqD_error
  have hsym : slope f x y = slope f y x := slope_comm f x y
  have hL_far : slope f x y ≤ slope f y z + η / 2 := by
    simpa [hsym] using hfar
  rw [hmid] at hL_far
  nlinarith

/--
Near an interior point, a left secant is bounded by any nearby right secant
plus an arbitrary additive error.
-/
theorem hiaiSlopeCore_leftSecant_le_right_add
    {f : ℝ → ℝ}
    (hmono : MonotoneOn f (Set.Ioo (-1 : ℝ) 1))
    (hcore : hiaiSlopeCoreOnUnitInterval f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ η > 0, ∃ δ > 0,
      ∀ {y z : ℝ},
        y ∈ Set.Ioo (-1 : ℝ) x →
        z ∈ Set.Ioo x (1 : ℝ) →
        dist y x < δ →
        dist z x < δ →
          slope f x y ≤ slope f x z + η := by
  intro η hη
  have hη3 : 0 < η / 3 := by linarith
  rcases hiaiSlopeCore_leftSecant_le_mirrorRight_add
      hmono hcore hx (η / 3) hη3 with ⟨δm, hδm, hmirror⟩
  rcases hiaiSlopeCore_rightSecant_le_left_add
      hmono hcore hx (η / 3) hη3 with ⟨δr, hδr, hright_left⟩
  let δ : ℝ := min δm (min δr (min ((1 - x) / 2) ((x + 1) / 2)))
  have hδ_pos : 0 < δ := by
    have hright : 0 < (1 - x) / 2 := by linarith [hx.2]
    have hleft : 0 < (x + 1) / 2 := by linarith [hx.1]
    exact lt_min hδm (lt_min hδr (lt_min hright hleft))
  refine ⟨δ, hδ_pos, ?_⟩
  intro y z hy hz hydist hzdist
  let m : ℝ := 2 * x - y
  let w : ℝ := 2 * x - z
  have hδ_le_m : δ ≤ δm := min_le_left _ _
  have hδ_le_r : δ ≤ δr := by
    exact le_trans (min_le_right δm _) (min_le_left _ _)
  have hδ_le_right : δ ≤ (1 - x) / 2 := by
    exact le_trans (le_trans (min_le_right δm _) (min_le_right _ _)) (min_le_left _ _)
  have hδ_le_left : δ ≤ (x + 1) / 2 := by
    exact le_trans (le_trans (min_le_right δm _) (min_le_right _ _)) (min_le_right _ _)
  have hy_gap : x - y < δ := by
    have hy_abs : |y - x| < δ := by
      simpa [Real.dist_eq] using hydist
    have habs : |y - x| = x - y := by
      rw [abs_of_nonpos (sub_nonpos.mpr hy.2.le)]
      ring
    simpa [habs] using hy_abs
  have hz_gap : z - x < δ := by
    have hz_abs : |z - x| < δ := by
      simpa [Real.dist_eq] using hzdist
    have habs : |z - x| = z - x := abs_of_nonneg (sub_nonneg.mpr hz.1.le)
    simpa [habs] using hz_abs
  have hxm : x < m := by
    dsimp [m]
    linarith [hy.2]
  have hm_lt_one : m < 1 := by
    have hmgap : m - x < (1 - x) / 2 := by
      dsimp [m]
      linarith [hy_gap, hδ_le_right]
    linarith
  have hmI : m ∈ Set.Ioo x (1 : ℝ) := ⟨hxm, hm_lt_one⟩
  have hwx : w < x := by
    dsimp [w]
    linarith [hz.1]
  have hneg_one_lt_w : -1 < w := by
    have hwgap : x - w < (x + 1) / 2 := by
      dsimp [w]
      linarith [hz_gap, hδ_le_left]
    linarith
  have hwI : w ∈ Set.Ioo (-1 : ℝ) x := ⟨hneg_one_lt_w, hwx⟩
  have hdist_m_delta : dist m x < δ := by
    rw [Real.dist_eq]
    have hnonneg : 0 ≤ m - x := sub_nonneg.mpr hxm.le
    rw [abs_of_nonneg hnonneg]
    dsimp [m]
    linarith [hy_gap]
  have hdist_w_delta : dist w x < δ := by
    rw [Real.dist_eq]
    have hnonpos : w - x ≤ 0 := sub_nonpos.mpr hwx.le
    rw [abs_of_nonpos hnonpos]
    have hw_abs : -(w - x) = z - x := by
      dsimp [w]
      ring
    rw [hw_abs]
    exact hz_gap
  have hdist_m : dist m x < δm := lt_of_lt_of_le hdist_m_delta hδ_le_m
  have hdist_w : dist w x < δm := lt_of_lt_of_le hdist_w_delta hδ_le_m
  have hdist_m_r : dist m x < δr := lt_of_lt_of_le hdist_m_delta hδ_le_r
  have hdist_w_r : dist w x < δr := lt_of_lt_of_le hdist_w_delta hδ_le_r
  have hy_dist_m : dist y x < δm := lt_of_lt_of_le hydist hδ_le_m
  have h1 := hmirror hy hy_dist_m
  have h2mid := hright_left hwI hmI hdist_w_r hdist_m_r
  have h3 := hmirror hwI hdist_w
  have hmirror_w :
      slope f x w ≤ slope f x z + η / 3 := by
    simpa [w] using h3
  have hmirror_y :
      slope f x y ≤ slope f x m + η / 3 := by
    simpa [m] using h1
  nlinarith

/--
The Hiai slope-core makes left and right secants at an interior point
arbitrarily close in value.
-/
theorem hiaiSlopeCore_crossSecants_dist
    {f : ℝ → ℝ}
    (hmono : MonotoneOn f (Set.Ioo (-1 : ℝ) 1))
    (hcore : hiaiSlopeCoreOnUnitInterval f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ η > 0, ∃ δ > 0,
      ∀ {y z : ℝ},
        y ∈ Set.Ioo (-1 : ℝ) x →
        z ∈ Set.Ioo x (1 : ℝ) →
        dist y x < δ →
        dist z x < δ →
          dist (slope f x y) (slope f x z) < η := by
  intro η hη
  have hη2 : 0 < η / 2 := by linarith
  rcases hiaiSlopeCore_rightSecant_le_left_add
      hmono hcore hx (η / 2) hη2 with ⟨δr, hδr, hright_left⟩
  rcases hiaiSlopeCore_leftSecant_le_right_add
      hmono hcore hx (η / 2) hη2 with ⟨δl, hδl, hleft_right⟩
  let δ : ℝ := min δr δl
  have hδ_pos : 0 < δ := lt_min hδr hδl
  refine ⟨δ, hδ_pos, ?_⟩
  intro y z hy hz hydist hzdist
  have hδ_le_r : δ ≤ δr := min_le_left _ _
  have hδ_le_l : δ ≤ δl := min_le_right _ _
  have hR_le_L :
      slope f x z ≤ slope f x y + η / 2 :=
    hright_left hy hz (lt_of_lt_of_le hydist hδ_le_r)
      (lt_of_lt_of_le hzdist hδ_le_r)
  have hL_le_R :
      slope f x y ≤ slope f x z + η / 2 :=
    hleft_right hy hz (lt_of_lt_of_le hydist hδ_le_l)
      (lt_of_lt_of_le hzdist hδ_le_l)
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

/-!
## First public regularity step

The non-smooth public hard direction is reduced to a Hiai/Loewner regularity
ladder.  The lemmas below record the filter and `C¹` packaging pieces used by
the completed finite-order route.
-/

/--
The Hiai slope-core implies local oscillation control for all punctured
secants at an interior point.
-/
theorem secant_localOscillation_of_hiaiSlopeCore
    {f : ℝ → ℝ}
    (hmono : MonotoneOn f (Set.Ioo (-1 : ℝ) 1))
    (hcore : hiaiSlopeCoreOnUnitInterval f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ ε > 0,
      ∃ U ∈ 𝓝[Set.Ioo (-1 : ℝ) 1 \ {x}] x,
        ∀ y ∈ U, ∀ z ∈ U,
          dist (slope f x y) (slope f x z) < ε :=
  secant_localOscillation_of_crossSecants hx
    (hiaiSlopeCore_crossSecants_dist hmono hcore hx)

/--
The Hiai slope-core gives existence of a punctured secant limit at every
interior point.
-/
theorem secant_tendsto_of_hiaiSlopeCore
    {f : ℝ → ℝ}
    (hmono : MonotoneOn f (Set.Ioo (-1 : ℝ) 1))
    (hcore : hiaiSlopeCoreOnUnitInterval f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∃ D : ℝ,
      Filter.Tendsto (slope f x)
        (𝓝[Set.Ioo (-1 : ℝ) 1 \ {x}] x) (𝓝 D) :=
  secant_tendsto_of_localOscillation hx
    (secant_localOscillation_of_hiaiSlopeCore hmono hcore hx)

/--
The public input already contains differentiability, so any punctured secant
limit at an interior point must be the ordinary derivative.  The finite-order
route supplies derivative continuity separately.
-/
theorem secant_tendsto_deriv_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Filter.Tendsto (slope f x)
      (𝓝[Set.Ioo (-1 : ℝ) 1 \ {x}] x) (𝓝 (deriv f x)) := by
  have hAt : HasDerivAt f (deriv f x) x :=
    (differentiableAt_of_loewnerPosOnUnitInterval hpos hx).hasDerivAt
  refine hAt.tendsto_slope.mono_left ?_
  exact nhdsWithin_mono x (by
    intro y hy
    exact hy.2)

/--
Closed packaging from derivative continuity to the first finite-order
regularity step.
-/
theorem publicC1Regularity_of_deriv_continuousOn
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (hderiv : ContinuousOn (deriv f) (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ 1 f (Set.Ioo (-1 : ℝ) 1) := by
  have h :
      ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1) f
        (Set.Ioo (-1 : ℝ) 1) := by
    rw [contDiffOn_succ_iff_deriv_of_isOpen
      (n := (0 : WithTop ℕ∞)) (f := f) isOpen_Ioo]
    refine ⟨hpos.differentiable, ?_, ?_⟩
    · intro h
      cases h
    · exact contDiffOn_zero.2 hderiv
  simpa using h

/--
Thin public `C¹` wrapper for the regularized derivative limit-transfer data.
Pointwise convergence and equicontinuity are explicit inputs here; the broad
theorem from `LoewnerPosOnUnitInterval` is
`publicC1Regularity_of_loewnerPosOnUnitInterval` below.
-/
theorem publicC1Regularity_of_regularized_deriv_tendsto_and_eventual_equi
    {φ f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (hpoint :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (fun z : ℝ => hiaiRegularization φ ε f z) x)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv f x)))
    (hequi :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ∀ η > 0, ∃ U ∈ 𝓝 x,
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ U,
          dist
            (deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)
            (deriv (fun z : ℝ => hiaiRegularization φ ε f z) x) < η) :
    ContDiffOn ℝ 1 f (Set.Ioo (-1 : ℝ) 1) :=
  publicC1Regularity_of_deriv_continuousOn hpos
    (deriv_continuousOn_of_regularized_deriv_tendsto_and_eventual_equi
      (φ := φ) (f := f) hpoint hequi)

/--
Thin public `C¹` wrapper using the local Lipschitz version of the regularized
derivative limit-transfer data.
-/
theorem publicC1Regularity_of_regularized_deriv_tendsto_and_eventual_local_lipschitz
    {φ f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (hpoint :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (fun z : ℝ => hiaiRegularization φ ε f z) x)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv f x)))
    (hLip :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ C : ℝ, 0 ≤ C ∧ ∃ U ∈ 𝓝 x,
          ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ U,
            dist
              (deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)
              (deriv (fun z : ℝ => hiaiRegularization φ ε f z) x) ≤
                C * dist y x) :
    ContDiffOn ℝ 1 f (Set.Ioo (-1 : ℝ) 1) :=
  publicC1Regularity_of_deriv_continuousOn hpos
    (deriv_continuousOn_of_regularized_deriv_tendsto_and_eventual_local_lipschitz
      (φ := φ) (f := f) hpoint hLip)

/--
Thin public `C¹` wrapper using a Mathlib `LipschitzOnWith` producer for the
regularized derivative limit-transfer data.
-/
theorem publicC1Regularity_of_regularized_deriv_tendsto_and_lipschitzOnWith
    {φ f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (hpoint :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (fun z : ℝ => hiaiRegularization φ ε f z) x)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv f x)))
    (hLip :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ K : ℝ≥0, ∃ U ∈ 𝓝 x, x ∈ U ∧
          ∀ᶠ ε in 𝓝[>] (0 : ℝ),
            LipschitzOnWith K
              (fun y : ℝ =>
                deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)
              U) :
    ContDiffOn ℝ 1 f (Set.Ioo (-1 : ℝ) 1) :=
  publicC1Regularity_of_deriv_continuousOn hpos
    (deriv_continuousOn_of_regularized_deriv_tendsto_and_lipschitzOnWith
      (φ := φ) (f := f) hpoint hLip)

/--
Thin public `C¹` wrapper where the `LipschitzOnWith` input is produced from
eventual local convexity plus an eventual local uniform absolute-value bound.
-/
theorem publicC1Regularity_of_regularized_deriv_tendsto_and_eventual_convex_abs_le
    {φ f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (hpoint :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (fun z : ℝ => hiaiRegularization φ ε f z) x)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv f x)))
    (hlocal :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ r δ M : ℝ, 0 < δ ∧ δ < r ∧
          (∀ᶠ ε in 𝓝[>] (0 : ℝ),
            ConvexOn ℝ (Metric.ball x r)
              (fun y : ℝ =>
                deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)) ∧
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
            abs (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z) y) ≤ M)) :
    ContDiffOn ℝ 1 f (Set.Ioo (-1 : ℝ) 1) :=
  publicC1Regularity_of_deriv_continuousOn hpos
    (deriv_continuousOn_of_regularized_deriv_tendsto_and_eventual_convex_abs_le
      (φ := φ) (f := f) hpoint hlocal)

/--
Public `C¹` regularity follows from public Löwner positivity once a Hiai
mollifier is supplied.
-/
theorem publicC1Regularity_of_loewnerPosOnUnitInterval_of_hiaiMollifier
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    ContDiffOn ℝ 1 f (Set.Ioo (-1 : ℝ) 1) :=
  publicC1Regularity_of_deriv_continuousOn hpos
    (deriv_continuousOn_of_loewnerPosOnUnitInterval_of_hiaiMollifier
      (φ := φ) (f := f) hφ hpos)

/--
Public Löwner positivity gives `C¹` regularity, with the Hiai mollifier
chosen from Mathlib's normalized bump functions.
-/
theorem publicC1Regularity_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    ContDiffOn ℝ 1 f (Set.Ioo (-1 : ℝ) 1) := by
  rcases exists_hiaiMollifier with ⟨φ, hφ⟩
  exact
    publicC1Regularity_of_deriv_continuousOn hpos
      (deriv_continuousOn_of_loewnerPosOnUnitInterval_of_hiaiMollifier
        (φ := φ) (f := f) hφ hpos)

/-- Public `C¹` regularity, with the former smooth-Hiai and limit inputs closed. -/
theorem publicC1Regularity_of_C3SmoothHiai_pointwiseLimitData
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    ContDiffOn ℝ 1 f (Set.Ioo (-1 : ℝ) 1) :=
  publicC1Regularity_of_loewnerPosOnUnitInterval hpos

/-- Public `C¹` regularity, with the former smooth-Hiai input closed. -/
theorem publicC1Regularity_of_C3SmoothHiai
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    ContDiffOn ℝ 1 f (Set.Ioo (-1 : ℝ) 1) :=
  publicC1Regularity_of_loewnerPosOnUnitInterval hpos

end

end Quantum.TraceInequality.Loewner
