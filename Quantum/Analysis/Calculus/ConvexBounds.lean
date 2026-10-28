import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.Tactic

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter
open scoped Topology Interval NNReal ENNReal

noncomputable section

private theorem convex_value_le_interval_average
    {F : ℝ → ℝ} {y ρ : ℝ} (hρ : 0 < ρ)
    (hconv : ConvexOn ℝ (Set.Icc (y - ρ) (y + ρ)) F)
    (hcont : ContinuousOn F (Set.Icc (y - ρ) (y + ρ))) :
    F y ≤ (∫ z in (y - ρ)..(y + ρ), F z) / (2 * ρ) := by
  let a : ℝ := y - ρ
  let b : ℝ := y + ρ
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have havg_id : (⨍ z in a..b, z) = y := by
    rw [interval_average_eq_div, integral_id]
    dsimp [a, b]
    field_simp [hρ.ne']
    ring
  have hzero : volume (Ι a b) ≠ 0 := by
    rw [Set.uIoc_of_le hab, Real.volume_Ioc]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by dsimp [a, b]; linarith)
  have htop : volume (Ι a b) ≠ ∞ := by
    rw [Set.uIoc_of_le hab, Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hfs :
      ∀ᵐ z ∂(volume.restrict (Ι a b)), (fun z : ℝ => z) z ∈ Set.Icc a b := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with z hz
    have hz' : z ∈ Set.Ioc a b := by
      simpa [Set.uIoc_of_le hab] using hz
    exact ⟨hz'.1.le, hz'.2⟩
  have hfi : IntegrableOn (fun z : ℝ => z) (Ι a b) volume :=
    intervalIntegrable_iff.mp
      (Continuous.intervalIntegrable continuous_id a b)
  have hgi : IntegrableOn (F ∘ fun z : ℝ => z) (Ι a b) volume := by
    simpa [Function.comp_def] using
      intervalIntegrable_iff.mp
        (hcont.intervalIntegrable_of_Icc hab)
  have hJ :=
    hconv.map_set_average_le (μ := volume) (t := Ι a b)
      (f := fun z : ℝ => z) (g := F)
      hcont isClosed_Icc hzero htop hfs hfi hgi
  have hJ' : F y ≤ ⨍ z in a..b, F z := by
    simpa [havg_id, Function.comp_def] using hJ
  calc
    F y ≤ ⨍ z in a..b, F z := hJ'
    _ = (∫ z in a..b, F z) / (b - a) := interval_average_eq_div F a b
    _ = (∫ z in (y - ρ)..(y + ρ), F z) / (2 * ρ) := by
      dsimp [a, b]
      ring_nf

/--
A nonnegative convex function with a bounded interval integral is uniformly
bounded on the inner ball.  The loose constant `A / ρ` is the one used by the
regularized-derivative handoff below.
-/
theorem convex_nonneg_abs_le_on_inner_ball_of_integral_le
    {F : ℝ → ℝ} {x ρ A : ℝ}
    (hρ : 0 < ρ) (hA : 0 ≤ A)
    (hconv : ConvexOn ℝ (Metric.ball x (2 * ρ)) F)
    (hnonneg : ∀ z ∈ Metric.ball x (2 * ρ), 0 ≤ F z)
    (hcont : ContinuousOn F (Metric.ball x (2 * ρ)))
    (hbig_int : IntervalIntegrable F volume (x - 2 * ρ) (x + 2 * ρ))
    (hintegral : ∫ z in (x - 2 * ρ)..(x + 2 * ρ), F z ≤ A) :
    ∀ y ∈ Metric.ball x ρ, |F y| ≤ A / ρ := by
  intro y hy
  let a : ℝ := y - ρ
  let b : ℝ := y + ρ
  let c : ℝ := x - 2 * ρ
  let d : ℝ := x + 2 * ρ
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hyIoo : y ∈ Set.Ioo (x - ρ) (x + ρ) := by
    simpa [Real.ball_eq_Ioo] using hy
  have hca : c ≤ a := by dsimp [a, c]; linarith [hyIoo.1]
  have hbd : b ≤ d := by dsimp [b, d]; linarith [hyIoo.2]
  have hsub_ball :
      Set.Icc a b ⊆ Metric.ball x (2 * ρ) := by
    intro z hz
    have hzy_closed : z ∈ Metric.closedBall y ρ := by
      simpa [Real.closedBall_eq_Icc, a, b] using hz
    have hzy : dist z y ≤ ρ := Metric.mem_closedBall.mp hzy_closed
    have hyx : dist y x < ρ := Metric.mem_ball.mp hy
    exact Metric.mem_ball.mpr <| by
      calc
        dist z x ≤ dist z y + dist y x := dist_triangle z y x
        _ < ρ + ρ := add_lt_add_of_le_of_lt hzy hyx
        _ = 2 * ρ := by ring
  have hconv_sub : ConvexOn ℝ (Set.Icc a b) F :=
    hconv.subset hsub_ball (convex_Icc a b)
  have hcont_sub : ContinuousOn F (Set.Icc a b) := hcont.mono hsub_ball
  have hFy_le :
      F y ≤ (∫ z in a..b, F z) / (2 * ρ) := by
    simpa [a, b] using
      convex_value_le_interval_average (F := F) (y := y) (ρ := ρ)
        hρ hconv_sub hcont_sub
  have hnonneg_ae :
      0 ≤ᵐ[volume.restrict (Set.Ioc c d)] F := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact hnonneg z (by
      simpa [Real.ball_eq_Ioo, c, d] using hz)
  have hsub_le_big :
      (∫ z in a..b, F z) ≤ ∫ z in c..d, F z :=
    intervalIntegral.integral_mono_interval hca hab hbd hnonneg_ae hbig_int
  have hhalf_le :
      (∫ z in a..b, F z) / (2 * ρ) ≤
        (∫ z in c..d, F z) / (2 * ρ) :=
    div_le_div_of_nonneg_right hsub_le_big (by positivity)
  have hbig_le_A :
      (∫ z in c..d, F z) / (2 * ρ) ≤ A / (2 * ρ) := by
    dsimp [c, d]
    exact div_le_div_of_nonneg_right hintegral (by positivity)
  have hA_half_le : A / (2 * ρ) ≤ A / ρ := by
    field_simp [hρ.ne']
    nlinarith [hA, hρ]
  have hFy_bound : F y ≤ A / ρ :=
    hFy_le.trans (hhalf_le.trans (hbig_le_A.trans hA_half_le))
  have hy_big : y ∈ Metric.ball x (2 * ρ) := by
    exact Metric.mem_ball.mpr <| by
      have hyx : dist y x < ρ := Metric.mem_ball.mp hy
      linarith
  simpa [abs_of_nonneg (hnonneg y hy_big)] using hFy_bound

/--
If a convex nonnegative function is bounded at two fixed outer endpoints, then
its derivative is uniformly bounded on the inner ball.  This is the
non-integral endpoint version used for the `Rε'` family: endpoint convergence
of `Rε'` bounds the inner values of `Rε''`.
-/
theorem convex_nonneg_abs_deriv_le_on_inner_ball_of_endpoint_le
    {F : ℝ → ℝ} {x ρ M : ℝ}
    (hρ : 0 < ρ) (hM : 0 ≤ M)
    (hconv : ConvexOn ℝ (Metric.ball x (4 * ρ)) F)
    (hdiff : ∀ z ∈ Metric.ball x (4 * ρ), DifferentiableAt ℝ F z)
    (hnonneg : ∀ z ∈ Metric.ball x (4 * ρ), 0 ≤ F z)
    (hleft : F (x - 2 * ρ) ≤ M)
    (hright : F (x + 2 * ρ) ≤ M) :
    ∀ y ∈ Metric.ball x ρ, |deriv F y| ≤ M / ρ := by
  intro y hy
  let a : ℝ := x - 2 * ρ
  let b : ℝ := x + 2 * ρ
  have houter_pos : 0 < 4 * ρ := by positivity
  have ha_outer : a ∈ Metric.ball x (4 * ρ) := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [a]
    rw [abs_of_nonpos (by linarith : x - 2 * ρ - x ≤ 0)]
    linarith
  have hb_outer : b ∈ Metric.ball x (4 * ρ) := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [b]
    rw [abs_of_nonneg (by linarith : 0 ≤ x + 2 * ρ - x)]
    linarith
  have hy_outer : y ∈ Metric.ball x (4 * ρ) := by
    exact Metric.mem_ball.mpr <|
      lt_trans (Metric.mem_ball.mp hy) (by linarith)
  have hyIoo : y ∈ Set.Ioo (x - ρ) (x + ρ) := by
    simpa [Real.ball_eq_Ioo] using hy
  have hay : a < y := by
    dsimp [a]
    linarith [hyIoo.1]
  have hyb : y < b := by
    dsimp [b]
    linarith [hyIoo.2]
  have hden_left : ρ ≤ y - a := by
    dsimp [a]
    linarith [hyIoo.1]
  have hden_right : ρ ≤ b - y := by
    dsimp [b]
    linarith [hyIoo.2]
  have hden_left_pos : 0 < y - a := by linarith
  have hden_right_pos : 0 < b - y := by linarith
  have hslope_left_le_deriv :
      slope F a y ≤ deriv F y :=
    hconv.slope_le_deriv ha_outer hy_outer hay (hdiff y hy_outer)
  have hderiv_le_slope_right :
      deriv F y ≤ slope F y b :=
    hconv.deriv_le_slope hy_outer hb_outer hyb (hdiff y hy_outer)
  have hleft_slope_lower : -M / ρ ≤ slope F a y := by
    have hnum_lower : -M ≤ F y - F a := by
      have hy_nonneg := hnonneg y hy_outer
      linarith
    have hmul₁ : (-M) * (y - a) ≤ (-M) * ρ := by
      exact mul_le_mul_of_nonpos_left hden_left (by linarith)
    have hmul₂ : (-M) * ρ ≤ (F y - F a) * ρ := by
      exact mul_le_mul_of_nonneg_right hnum_lower hρ.le
    rw [slope_def_field]
    rw [div_le_div_iff₀ hρ hden_left_pos]
    nlinarith
  have hslope_right_upper : slope F y b ≤ M / ρ := by
    have hnum_upper : F b - F y ≤ M := by
      have hy_nonneg := hnonneg y hy_outer
      linarith
    have hmul₁ : (F b - F y) * ρ ≤ M * ρ :=
      mul_le_mul_of_nonneg_right hnum_upper hρ.le
    have hmul₂ : M * ρ ≤ M * (b - y) :=
      mul_le_mul_of_nonneg_left hden_right hM
    rw [slope_def_field]
    rw [div_le_div_iff₀ hden_right_pos hρ]
    nlinarith
  have hlower : -(M / ρ) ≤ deriv F y := by
    simpa [neg_div] using hleft_slope_lower.trans hslope_left_le_deriv
  rw [abs_le]
  exact ⟨hlower, hderiv_le_slope_right.trans hslope_right_upper⟩

/--
Mathlib's convexity estimate supplies a uniform `LipschitzOnWith` bound on a
smaller ball from eventual convexity and an eventual uniform absolute-value
bound on a larger ball.
-/
theorem eventual_lipschitzOnWith_of_eventual_convexOn_ball_abs_le
    {ι : Type*} {l : Filter ι}
    {F : ι → ℝ → ℝ} {x r δ M : ℝ}
    (hδ : 0 < δ) (hδr : δ < r)
    (hconv : ∀ᶠ i in l, ConvexOn ℝ (Metric.ball x r) (F i))
    (habs :
      ∀ᶠ i in l, ∀ y ∈ Metric.ball x r, |F i y| ≤ M) :
    ∃ K : ℝ≥0, ∃ U ∈ 𝓝 x, x ∈ U ∧
      ∀ᶠ i in l, LipschitzOnWith K (F i) U := by
  let K : ℝ≥0 := (2 * M / δ).toNNReal
  let U : Set ℝ := Metric.ball x (r - δ)
  have hU_mem : U ∈ 𝓝 x :=
    Metric.ball_mem_nhds x (sub_pos.2 hδr)
  have hxU : x ∈ U := by
    simp [U, sub_pos.2 hδr]
  refine ⟨K, U, hU_mem, hxU, ?_⟩
  filter_upwards [hconv, habs] with i hconv_i habs_i
  simpa [K, U] using hconv_i.lipschitzOnWith_of_abs_le hδ
    (fun y hy => habs_i y hy)

end

end Quantum.TraceInequality.Loewner
