import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.HiaiInterlacingCore
import Quantum.Analysis.Calculus.SharedSecantFilter
import Quantum.TraceInequality.Loewner.UnitInterval.SharedSlopeCore

/-!
# Chapter 3 Hiai four-point secant squeeze

This file contains the final reflection and cross-secant squeeze steps built
from the Hiai four-point interlacing core.
-/

namespace Quantum.TraceInequality.Loewner

universe u

noncomputable section

open scoped ComplexOrder
open scoped Matrix
open scoped MatrixOrder
open scoped Matrix.Norms.L2Operator
open scoped Polynomial
open scoped Topology

/-- Reflection preserves the ordinary secant slope after negating both nodes. -/
lemma reflect_slope_neg_neg (f : ℝ → ℝ) (x y : ℝ) :
    slope (reflect f) (-x) (-y) = slope f x y := by
  by_cases h : y = x
  · subst y
    rw [slope_def_field, slope_def_field]
    norm_num [reflect]
  · rw [slope_def_field, slope_def_field]
    simp [reflect]
    have hden : y - x ≠ 0 := sub_ne_zero.mpr h
    have hden' : -y + x ≠ 0 := by
      intro h0
      apply hden
      linarith
    field_simp [hden, hden']
    ring

/--
Eventual right-neighborhood form of the Hiai max-bound.  This is the closed
filter-level consequence of the four-point inequality used by the downstream
scalar squeeze to obtain matching one-sided secant limits.
-/
theorem twoByTwo_cfc_order_hiai_rightSecant_limsup_le
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a x d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hax : a < x) :
    ∀ᶠ b in 𝓝[Set.Ioo x d] x,
      slope f x b ≤ max (slope f x a) (slope f x d) := by
  filter_upwards [self_mem_nhdsWithin] with b hb
  have hbI : b ∈ Set.Ioo (-1 : ℝ) 1 := by
    exact ⟨lt_trans hx.1 hb.1, lt_trans hb.2 hd.2⟩
  exact twoByTwo_cfc_order_hiai_rightSecant_maxBound
    h2 ha hbI hx hd hax hb.1 hb.2

/--
Eventual left-neighborhood form of the Hiai max-bound, obtained by reflecting
the function and the four nodes.  This records the symmetric filter-level
control available from the same `2×2` CFC comparison.
-/
theorem twoByTwo_cfc_order_hiai_leftSecant_limsup_le
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a x d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hxd : x < d) :
    ∀ᶠ y in 𝓝[Set.Ioo a x] x,
      slope f x y ≤ max (slope f x a) (slope f x d) := by
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hyI : y ∈ Set.Ioo (-1 : ℝ) 1 := by
    exact ⟨lt_trans ha.1 hy.1, lt_trans hy.2 hx.2⟩
  have hreflect :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => reflect f t - reflect f 0) A ≤
            cfcₙ (fun t : ℝ => reflect f t - reflect f 0) B := by
    intro A B hA hB hAB
    exact twoByTwo_cfc_order_reflect h2 hA hB hAB
  have hneg_d : -d ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor <;> linarith [hd.1, hd.2]
  have hneg_y : -y ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor <;> linarith [hyI.1, hyI.2]
  have hneg_x : -x ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hneg_a : -a ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor <;> linarith [ha.1, ha.2]
  have hbound := twoByTwo_cfc_order_hiai_rightSecant_maxBound
    (f := reflect f) hreflect hneg_d hneg_y hneg_x hneg_a
    (by linarith [hxd]) (by linarith [hy.2]) (by linarith [hy.1])
  simpa [reflect_slope_neg_neg, max_comm] using hbound

/--
Pointwise left-neighborhood form of the Hiai max-bound, obtained by reflecting
the pointwise right-neighborhood bound.  This is used only for local boundedness
in the final Hiai squeeze.
-/
theorem twoByTwo_cfc_order_hiai_leftSecant_maxBound
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a y x d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hay : a < y) (hyx : y < x) (hxd : x < d) :
    slope f x y ≤ max (slope f x a) (slope f x d) := by
  have hreflect :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => reflect f t - reflect f 0) A ≤
            cfcₙ (fun t : ℝ => reflect f t - reflect f 0) B := by
    intro A B hA hB hAB
    exact twoByTwo_cfc_order_reflect h2 hA hB hAB
  have hneg_d : -d ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor <;> linarith [hd.1, hd.2]
  have hneg_y : -y ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor <;> linarith [hy.1, hy.2]
  have hneg_x : -x ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hneg_a : -a ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor <;> linarith [ha.1, ha.2]
  have hbound := twoByTwo_cfc_order_hiai_rightSecant_maxBound
    (f := reflect f) hreflect hneg_d hneg_y hneg_x hneg_a
    (by linarith [hxd]) (by linarith [hyx]) (by linarith [hay])
  simpa [reflect_slope_neg_neg, max_comm] using hbound

/--
Full `2×2` CFC order comparison gives a local two-sided bound for all secant
slopes based at an interior point.  The proof uses the Hiai max-bound only as a
boundedness tool; the final common-limit squeeze keeps the sharper `q`-form.
-/
theorem twoByTwo_cfc_order_local_secant_bound
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
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
  let M : ℝ := max (slope f x a) (slope f x d) + 1
  have hmono := scalarMonotoneOn_Ioo_of_twoByTwo_cfc_order h2
  have haI : a ∈ Set.Ioo (-1 : ℝ) 1 := ⟨ha_left, lt_trans hax hx.2⟩
  have hdI : d ∈ Set.Ioo (-1 : ℝ) 1 := ⟨lt_trans hx.1 hxd, hd_right⟩
  have hxa_nonneg : 0 ≤ slope f x a :=
    MonotoneOn.slope_nonneg hmono hx haI
  have hxd_nonneg : 0 ≤ slope f x d :=
    MonotoneOn.slope_nonneg hmono hx hdI
  have hM_pos : 0 < M := by
    have hmax_nonneg : 0 ≤ max (slope f x a) (slope f x d) :=
      le_max_of_le_left hxa_nonneg
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
      have hbound := twoByTwo_cfc_order_hiai_rightSecant_maxBound
        h2 haI hy hx hdI hax hxy hyd
      have hmax_le_M : max (slope f x a) (slope f x d) ≤ M := by
        dsimp [M]
        linarith
      exact le_trans hbound hmax_le_M
    · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hxy) hy_ne
      have hay : a < y := by
        have hy_gap : x - y < (x - a) / 2 := by
          have habs : |y - x| = x - y := by
            rw [abs_of_nonpos (sub_nonpos.mpr hyx.le)]
            ring
          exact lt_of_lt_of_le (by simpa [habs] using hdist_abs) hδ_le_left
        linarith
      have hbound := twoByTwo_cfc_order_hiai_leftSecant_maxBound
        h2 haI hy hx hdI hay hyx hxd
      have hmax_le_M : max (slope f x a) (slope f x d) ≤ M := by
        dsimp [M]
        linarith
      exact le_trans hbound hmax_le_M
  exact ⟨hnonneg, hupper⟩

/--
Full `2×2` CFC order comparison supplies the `q → ∞` Hiai secant estimate in
four-point form.
-/
theorem twoByTwo_cfc_order_hiai_rightSecant_le_left_add_invQ
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a c b d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d) :
    slope f c b ≤
      slope f c a + slope f c a / ((d - b) / (b - a)) := by
  have hmono := scalarMonotoneOn_Ioo_of_twoByTwo_cfc_order h2
  have hcore : hiaiSlopeCoreOnUnitInterval f :=
    hiaiSlopeCoreOnUnitInterval_of_twoByTwo_cfc_order h2
  exact hiaiSlopeCore_rightSecant_le_left_add_invQ
    hmono hcore ha hb hc hd hac hcb hbd

/--
Full `2×2` CFC order comparison supplies the `q → 0` Hiai secant estimate in
four-point form.
-/
theorem twoByTwo_cfc_order_hiai_rightSecant_le_far_addQ
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a c b d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d) :
    slope f c b ≤
      slope f c d + ((d - b) / (b - a)) * slope f c d := by
  have hmono := scalarMonotoneOn_Ioo_of_twoByTwo_cfc_order h2
  have hcore : hiaiSlopeCoreOnUnitInterval f :=
    hiaiSlopeCoreOnUnitInterval_of_twoByTwo_cfc_order h2
  exact hiaiSlopeCore_rightSecant_le_far_addQ
    hmono hcore ha hb hc hd hac hcb hbd

/--
Additive-error form of the `q → ∞` Hiai estimate.  The remaining scalar
squeeze only has to make the displayed inverse-`q` error small.
-/
theorem twoByTwo_cfc_order_hiai_rightSecant_le_left_add_of_invQ_le
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a c b d η : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d)
    (herror : slope f c a / ((d - b) / (b - a)) ≤ η) :
    slope f c b ≤ slope f c a + η := by
  have h :=
    twoByTwo_cfc_order_hiai_rightSecant_le_left_add_invQ
      h2 ha hb hc hd hac hcb hbd
  linarith

/--
Additive-error form of the `q → 0` Hiai estimate.  The remaining scalar
squeeze only has to make the displayed `q` error small.
-/
theorem twoByTwo_cfc_order_hiai_rightSecant_le_far_add_of_qMul_le
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a c b d η : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d)
    (herror : ((d - b) / (b - a)) * slope f c d ≤ η) :
    slope f c b ≤ slope f c d + η := by
  have h :=
    twoByTwo_cfc_order_hiai_rightSecant_le_far_addQ
      h2 ha hb hc hd hac hcb hbd
  linarith

/--
One-sided Hiai squeeze: near an interior base point, every right secant is
bounded by every nearby left secant up to an arbitrary additive error.  This is
the `q → ∞` use of the four-point slope-core with a fixed far-right anchor.
-/
theorem twoByTwo_cfc_order_hiai_rightSecant_le_left_add
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ η > 0, ∃ δ > 0,
      ∀ {y z : ℝ},
        y ∈ Set.Ioo (-1 : ℝ) x →
        z ∈ Set.Ioo x (1 : ℝ) →
        dist y x < δ →
        dist z x < δ →
          slope f x z ≤ slope f x y + η := by
  intro η hη
  rcases twoByTwo_cfc_order_local_secant_bound h2 hx with
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
  have hz_ne : z ≠ x := ne_of_gt hz.1
  have hydist0 : dist y x < δ0 := lt_of_lt_of_le hydist hδ_le_δ0
  have hleft_bound := (hlocal hyI hy_ne hydist0).2
  have hleft_nonneg := (hlocal hyI hy_ne hydist0).1
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
  have hdz_ge : (d - x) / 2 ≤ d - z := by
    have hzgap : z - x < (d - x) / 4 := lt_of_lt_of_le hz_gap hδ_le_gap
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
    twoByTwo_cfc_order_hiai_rightSecant_le_left_add_of_invQ_le
      h2 hyI hzI hx hdI hy.2 hz.1 hzd herror

/--
Mirror Hiai squeeze: a nearby left secant is controlled by the secant to its
right mirror point.  This is the `q → 0` use of the four-point slope-core with
the center moved to the left node.
-/
theorem twoByTwo_cfc_order_hiai_leftSecant_le_mirrorRight_add
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ η > 0, ∃ δ > 0,
      ∀ {y : ℝ},
        y ∈ Set.Ioo (-1 : ℝ) x →
        dist y x < δ →
          slope f x y ≤ slope f x (2 * x - y) + η := by
  intro η hη
  rcases twoByTwo_cfc_order_local_secant_bound h2 hx with
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
  have hfar := twoByTwo_cfc_order_hiai_rightSecant_le_far_add_of_qMul_le
    h2 huI hx hyI hzI huy hy.2 hxz hqD_error
  have hsym : slope f x y = slope f y x := slope_comm f x y
  have hL_far : slope f x y ≤ slope f y z + η / 2 := by
    simpa [hsym] using hfar
  rw [hmid] at hL_far
  nlinarith

/--
The mirror-chain Hiai squeeze: every nearby left secant is bounded by every
nearby right secant up to an arbitrary additive error.
-/
theorem twoByTwo_cfc_order_hiai_leftSecant_le_right_add
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
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
  rcases twoByTwo_cfc_order_hiai_leftSecant_le_mirrorRight_add
      h2 hx (η / 3) hη3 with ⟨δm, hδm, hmirror⟩
  rcases twoByTwo_cfc_order_hiai_rightSecant_le_left_add
      h2 hx (η / 3) hη3 with ⟨δr, hδr, hright_left⟩
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
  have hz_dist_m : dist z x < δm := lt_of_lt_of_le hzdist hδ_le_m
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
Nearby left and right secants based at the same interior point are arbitrarily
close.  This is the metric form of the Hiai scalar squeeze before passing to
filters.
-/
theorem twoByTwo_cfc_order_hiai_crossSecants_dist
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
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
  rcases twoByTwo_cfc_order_hiai_rightSecant_le_left_add
      h2 hx (η / 2) hη2 with ⟨δr, hδr, hright_left⟩
  rcases twoByTwo_cfc_order_hiai_leftSecant_le_right_add
      h2 hx (η / 2) hη2 with ⟨δl, hδl, hleft_right⟩
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

/--
The Hiai cross-secant estimate supplied by full `2×2` CFC order comparison
gives local oscillation of punctured secant slopes.
-/
theorem twoByTwo_cfc_order_secant_localOscillation_of_hiai_cross
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ ε > 0,
      ∃ U ∈ 𝓝[Set.Ioo (-1 : ℝ) 1 \ {x}] x,
        ∀ y ∈ U, ∀ z ∈ U,
          dist (slope f x y) (slope f x z) < ε :=
  secant_localOscillation_of_crossSecants hx
    (twoByTwo_cfc_order_hiai_crossSecants_dist h2 hx)

/--
The Hiai four-point secant squeeze inequality obtained from full `2×2` CFC
order comparison.
-/
theorem twoByTwo_cfc_order_hiai_fourPoint_secant_squeeze
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {a c b d : ℝ} (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (hb : b ∈ Set.Ioo (-1 : ℝ) 1)
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hd : d ∈ Set.Ioo (-1 : ℝ) 1)
    (hac : a < c) (hcb : c < b) (hbd : b < d) :
    0 ≤ hiaiInterlacingSchurSecantExpression f a c b d :=
  hiaiInterlacingCFCDifference_schur_secantFormula
    h2 ha hb hc hd hac hcb hbd


end

end Quantum.TraceInequality.Loewner
