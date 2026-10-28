import Quantum.TraceInequality.Loewner.UnitInterval.Pick.OutsideSupportBridge
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Topology.Sequences

/-!
# Chapter 3 Proposition 3.5 Poisson-kernel core

This module contains the Poisson-kernel identities and approximate-identity
preparations used by the Proposition 3.5 inversion step.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set
open Filter
open scoped Topology
open scoped NNReal
open scoped ENNReal

noncomputable section

/-! ### Proposition 3.5 Poisson kernel inversion core -/

/-- The scalar Poisson kernel appearing in book Proposition 3.5. -/
def unitIntervalHerglotzPoissonKernel (ε x y : ℝ) : ℝ :=
  (1 + y ^ (2 : ℕ)) * ε / ((y - x) ^ (2 : ℕ) + ε ^ (2 : ℕ))

/-- Rewrite the raw Herglotz kernel as `z + (1 + z^2) / (y - z)`. -/
theorem unitIntervalHerglotzRawKernel_eq_z_add
    {z : ℂ} {y : ℝ} (hden : (y : ℂ) - z ≠ 0) :
    unitIntervalHerglotzRawKernel z y =
      z + ((1 : ℂ) + z ^ (2 : ℕ)) / ((y : ℂ) - z) := by
  unfold unitIntervalHerglotzRawKernel
  field_simp [hden]
  ring

/-- The raw Herglotz denominator is nonzero in the upper half-plane. -/
theorem unitIntervalHerglotzRawKernel_den_ne_zero_of_im_pos
    {z : ℂ} (hz : 0 < z.im) (y : ℝ) :
    (y : ℂ) - z ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp [Complex.sub_im] at him
  linarith

/-- The raw Herglotz kernel is integrable against any finite measure upstairs. -/
theorem unitIntervalHerglotzRawKernel_integrable_of_im_pos
    (μ : FiniteMeasure ℝ) {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun y : ℝ => unitIntervalHerglotzRawKernel z y) (μ : Measure ℝ) := by
  have hmeas :
      AEStronglyMeasurable
        (fun y : ℝ => unitIntervalHerglotzRawKernel z y) (μ : Measure ℝ) := by
    have hmeas' :
        Measurable fun y : ℝ => unitIntervalHerglotzRawKernel z y := by
      unfold unitIntervalHerglotzRawKernel
      measurability
    exact hmeas'.aestronglyMeasurable
  refine Integrable.of_bound hmeas
    (‖z‖ + ‖(1 : ℂ) + z ^ (2 : ℕ)‖ / z.im) ?_
  filter_upwards with y
  have hden : (y : ℂ) - z ≠ 0 :=
    unitIntervalHerglotzRawKernel_den_ne_zero_of_im_pos hz y
  have hden_lower : z.im ≤ ‖(y : ℂ) - z‖ := by
    have h := Complex.abs_im_le_norm ((y : ℂ) - z)
    have him : |(((y : ℂ) - z).im)| = z.im := by
      simp [Complex.sub_im, abs_of_pos hz]
    calc
      z.im = |(((y : ℂ) - z).im)| := him.symm
      _ ≤ ‖(y : ℂ) - z‖ := h
  have hden_pos : 0 < ‖(y : ℂ) - z‖ :=
    lt_of_lt_of_le hz hden_lower
  rw [unitIntervalHerglotzRawKernel_eq_z_add hden]
  calc
    ‖z + ((1 : ℂ) + z ^ (2 : ℕ)) / ((y : ℂ) - z)‖
        ≤ ‖z‖ + ‖((1 : ℂ) + z ^ (2 : ℕ)) / ((y : ℂ) - z)‖ :=
          norm_add_le _ _
    _ = ‖z‖ + ‖(1 : ℂ) + z ^ (2 : ℕ)‖ / ‖(y : ℂ) - z‖ := by
          simp
    _ ≤ ‖z‖ + ‖(1 : ℂ) + z ^ (2 : ℕ)‖ / z.im := by
          exact add_le_add (le_refl ‖z‖)
            (div_le_div_of_nonneg_left (norm_nonneg _) hz hden_lower)

/-- The imaginary part of the raw Herglotz kernel is the weighted Poisson kernel. -/
theorem unitIntervalHerglotzRawKernel_im_eq_poisson
    (z : ℂ) (y : ℝ) :
    (unitIntervalHerglotzRawKernel z y).im =
      unitIntervalHerglotzPoissonKernel z.im z.re y := by
  unfold unitIntervalHerglotzRawKernel unitIntervalHerglotzPoissonKernel
  simp [Complex.div_im, Complex.normSq_apply]
  ring

/-- The raw Herglotz kernel has nonnegative imaginary part in the upper half-plane. -/
theorem unitIntervalHerglotzRawKernel_im_nonneg_of_upper
    {z : ℂ} (hz : 0 < z.im) (y : ℝ) :
    0 ≤ (unitIntervalHerglotzRawKernel z y).im := by
  rw [unitIntervalHerglotzRawKernel_im_eq_poisson]
  unfold unitIntervalHerglotzPoissonKernel
  positivity

/-- The boundary approach sequence has real part `x`. -/
theorem unitIntervalUpperBoundarySeq_re (x : ℝ) (n : ℕ) :
    (unitIntervalUpperBoundarySeq x n).re = x := by
  simp [unitIntervalUpperBoundarySeq]

/-- The boundary approach sequence has imaginary height `1 / (n + 1)`. -/
theorem unitIntervalUpperBoundarySeq_im (x : ℝ) (n : ℕ) :
    (unitIntervalUpperBoundarySeq x n).im = 1 / ((n : ℝ) + 1) := by
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  simp [unitIntervalUpperBoundarySeq, one_div]
  field_simp [hne]
  simp [Complex.normSq_apply]
  ring

/-- Boundary approach rewrites the raw kernel imaginary part as the Poisson kernel. -/
theorem unitIntervalHerglotzRawKernel_im_eq_poisson_boundary
    (x y : ℝ) (n : ℕ) :
    (unitIntervalHerglotzRawKernel (unitIntervalUpperBoundarySeq x n) y).im =
      unitIntervalHerglotzPoissonKernel (1 / ((n : ℝ) + 1)) x y := by
  rw [unitIntervalHerglotzRawKernel_im_eq_poisson]
  simp [unitIntervalUpperBoundarySeq_re, unitIntervalUpperBoundarySeq_im]

/-- The imaginary part of the raw integral is the integral of the Poisson kernel. -/
theorem UnitIntervalPickHerglotzUpperRawData.raw_integral_im_eq_integral_poisson
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    {z : ℂ} (hz : 0 < z.im) :
    (∫ y : ℝ, unitIntervalHerglotzRawKernel z y ∂(data.measure : Measure ℝ)).im =
      ∫ y : ℝ, unitIntervalHerglotzPoissonKernel z.im z.re y
        ∂(data.measure : Measure ℝ) := by
  have hInt :=
    unitIntervalHerglotzRawKernel_integrable_of_im_pos data.measure hz
  have him :=
    (integral_im (μ := (data.measure : Measure ℝ))
      (f := fun y : ℝ => unitIntervalHerglotzRawKernel z y) hInt)
  calc
    (∫ y : ℝ, unitIntervalHerglotzRawKernel z y ∂(data.measure : Measure ℝ)).im
        = ∫ y : ℝ, (unitIntervalHerglotzRawKernel z y).im
            ∂(data.measure : Measure ℝ) := him.symm
    _ = ∫ y : ℝ, unitIntervalHerglotzPoissonKernel z.im z.re y
            ∂(data.measure : Measure ℝ) := by
          refine integral_congr_ae ?_
          filter_upwards with y
          exact unitIntervalHerglotzRawKernel_im_eq_poisson z y

/-- The upper half-plane imaginary part splits into slope plus Poisson integral. -/
theorem UnitIntervalPickHerglotzUpperRawData.upper_im_eq_slope_add_poissonIntegral
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    {z : ℂ} (hz : 0 < z.im) :
    (data.pick.F z).im =
      (data.slope : ℝ) * z.im +
        ∫ y : ℝ, unitIntervalHerglotzPoissonKernel z.im z.re y
          ∂(data.measure : Measure ℝ) := by
  rw [data.upper_formula hz]
  simp [Complex.add_im, Complex.mul_im,
    data.raw_integral_im_eq_integral_poisson hz]

/-- Along the boundary approach sequence, the imaginary part has the Poisson form. -/
theorem UnitIntervalPickHerglotzUpperRawData.boundary_im_eq_slope_add_poissonIntegral
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (x : ℝ) (n : ℕ) :
    (data.pick.F (unitIntervalUpperBoundarySeq x n)).im =
      (data.slope : ℝ) * (1 / ((n : ℝ) + 1)) +
        ∫ y : ℝ, unitIntervalHerglotzPoissonKernel
          (1 / ((n : ℝ) + 1)) x y ∂(data.measure : Measure ℝ) := by
  have h :=
    data.upper_im_eq_slope_add_poissonIntegral
      (unitIntervalUpperBoundarySeq_im_pos x n)
  simpa [unitIntervalUpperBoundarySeq_re, unitIntervalUpperBoundarySeq_im] using h

/-- The weighted Poisson kernel is nonnegative for positive height. -/
theorem unitIntervalHerglotzPoissonKernel_nonneg
    {ε x y : ℝ} (hε : 0 < ε) :
    0 ≤ unitIntervalHerglotzPoissonKernel ε x y := by
  unfold unitIntervalHerglotzPoissonKernel
  positivity

/-- If boundary imaginary parts vanish, then the associated Poisson integrals vanish. -/
theorem UnitIntervalPickHerglotzUpperRawData.poissonIntegral_tendsto_zero_of_boundary_im_zero
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (x : ℝ)
    (hboundary :
      Tendsto
        (fun n : ℕ => (data.pick.F (unitIntervalUpperBoundarySeq x n)).im)
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        ∫ y : ℝ, unitIntervalHerglotzPoissonKernel
          (1 / ((n : ℝ) + 1)) x y ∂(data.measure : Measure ℝ))
      atTop (𝓝 0) := by
  refine squeeze_zero ?h_nonneg ?h_le hboundary
  · intro n
    exact integral_nonneg_of_ae
      (MeasureTheory.ae_of_all (data.measure : Measure ℝ) fun y =>
        unitIntervalHerglotzPoissonKernel_nonneg (by positivity : 0 < 1 / ((n : ℝ) + 1)))
  · intro n
    have heq := data.boundary_im_eq_slope_add_poissonIntegral x n
    have hslope_nonneg :
        0 ≤ (data.slope : ℝ) * (1 / ((n : ℝ) + 1)) := by
      positivity
    linarith

/-! ### Proposition 3.5 approximate-identity measure recovery -/

/--
The test density appearing in book Proposition 3.5, equation (3.44).

It is the imaginary part of the raw Herglotz representation multiplied by the
normalizing factor `(1 + x^2)^{-1}/π`.
-/
def unitIntervalHerglotzProp35TestKernel (ε x y : ℝ) : ℝ :=
  (Real.pi)⁻¹ * (1 + x ^ (2 : ℕ))⁻¹ *
    unitIntervalHerglotzPoissonKernel ε x y

/-- The Proposition 3.5 test kernel is nonnegative for positive height. -/
theorem unitIntervalHerglotzProp35TestKernel_nonneg
    {ε x y : ℝ} (hε : 0 < ε) :
    0 ≤ unitIntervalHerglotzProp35TestKernel ε x y := by
  unfold unitIntervalHerglotzProp35TestKernel
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
    (inv_nonneg.mpr (by nlinarith [sq_nonneg x])))
    (unitIntervalHerglotzPoissonKernel_nonneg hε)

/-- On the `ε`-ball around `x`, the Poisson kernel is bounded below by `(2ε)⁻¹`. -/
theorem unitIntervalHerglotzPoissonKernel_lower_on_eps_ball
    {ε x y : ℝ} (hε : 0 < ε) (hxy : |y - x| ≤ ε) :
    (2 * ε)⁻¹ ≤ unitIntervalHerglotzPoissonKernel ε x y := by
  unfold unitIntervalHerglotzPoissonKernel
  have hsq : (y - x) ^ (2 : ℕ) ≤ ε ^ (2 : ℕ) := by
    have hxy' : |y - x| ≤ |ε| := by simpa [abs_of_pos hε] using hxy
    exact sq_le_sq.mpr hxy'
  have hden_pos : 0 < (y - x) ^ (2 : ℕ) + ε ^ (2 : ℕ) := by positivity
  have hden_le : (y - x) ^ (2 : ℕ) + ε ^ (2 : ℕ) ≤ 2 * ε ^ (2 : ℕ) := by
    nlinarith
  have hmain :
      ε / (2 * ε ^ (2 : ℕ)) ≤
        ε / ((y - x) ^ (2 : ℕ) + ε ^ (2 : ℕ)) := by
    exact div_le_div_of_nonneg_left hε.le hden_pos hden_le
  have hfactor :
      ε / ((y - x) ^ (2 : ℕ) + ε ^ (2 : ℕ)) ≤
        (1 + y ^ (2 : ℕ)) * ε /
          ((y - x) ^ (2 : ℕ) + ε ^ (2 : ℕ)) := by
    have hy : 1 ≤ 1 + y ^ (2 : ℕ) := by nlinarith [sq_nonneg y]
    exact div_le_div_of_nonneg_right
      (by simpa [one_mul] using mul_le_mul_of_nonneg_right hy hε.le) hden_pos.le
  have hsimp : ε / (2 * ε ^ (2 : ℕ)) = (2 * ε)⁻¹ := by
    field_simp [hε.ne']
  exact hsimp ▸ hmain.trans hfactor

/-- The vertical upper-boundary sequence converges uniformly to the real embedding. -/
theorem unitIntervalUpperBoundarySeq_tendstoUniformlyOn_ofReal
    (K : Set ℝ) :
    TendstoUniformlyOn
      (fun n : ℕ => fun x : ℝ => unitIntervalUpperBoundarySeq x n)
      (fun x : ℝ => (x : ℂ)) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hsmall :
      ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε := by
    refine ((tendsto_one_div_add_atTop_nhds_zero_nat
      (𝕜 := ℝ)).eventually (Metric.ball_mem_nhds (0 : ℝ) hε)).mono ?_
    intro n hn
    have hden_pos : 0 < (n : ℝ) + 1 := by positivity
    simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_of_pos hden_pos] using hn
  filter_upwards [hsmall] with n hn x _hx
  have him_nonneg : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  have hdist :
      dist ((x : ℂ)) (unitIntervalUpperBoundarySeq x n) =
        1 / ((n : ℝ) + 1) := by
    have hre :
        ((x : ℂ)).re = (unitIntervalUpperBoundarySeq x n).re := by
      simp [unitIntervalUpperBoundarySeq]
    rw [Complex.dist_of_re_eq hre]
    simp only [unitIntervalUpperBoundarySeq, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_one,
      mul_zero, Real.dist_eq]
    have hden_nonneg : 0 ≤ (n : ℝ) + 1 := by positivity
    simp [hden_nonneg]
  simpa [hdist] using hn

/-- Boundary imaginary parts vanish uniformly on compact subsets of `(-1,1)`. -/
theorem pickExtension_boundary_im_tendstoUniformlyOn_zero_of_isCompact
    {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f)
    {K : Set ℝ} (hKc : IsCompact K)
    (hKsub : K ⊆ Set.Ioo (-1 : ℝ) 1) :
    TendstoUniformlyOn
      (fun n : ℕ => fun x : ℝ =>
        (pick.F (unitIntervalUpperBoundarySeq x n)).im)
      (fun _x : ℝ => 0) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hloc :
      ∀ x : K, ∃ δ : ℝ, 0 < δ ∧
        ∀ ⦃z : ℂ⦄, dist z (x : ℂ) < δ →
          dist ((pick.F z).im) 0 < ε := by
    intro x
    have hxI : (x : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := hKsub x.2
    have hcont :
        ContinuousAt (fun z : ℂ => (pick.F z).im) (x : ℂ) :=
      Complex.continuous_im.continuousAt.comp
        (pick.continuousAt_real hxI)
    have hreal : (pick.F (x : ℂ)).im = 0 := by
      simp [pick.agreesOnReal hxI]
    rw [Metric.continuousAt_iff] at hcont
    rcases hcont ε hε with ⟨δ, hδpos, hδ⟩
    refine ⟨δ, hδpos, ?_⟩
    intro z hz
    simpa [hreal] using hδ hz
  choose δ hδpos hδ using hloc
  rcases hKc.elim_finite_subcover
      (fun x : K => Metric.ball (x : ℝ) (δ x / 4))
      (fun _x => Metric.isOpen_ball)
      (by
        intro x hx
        refine mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
        simp [Metric.mem_ball, hδpos]) with ⟨t, ht⟩
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        ∀ x ∈ t, 1 / ((n : ℝ) + 1) < δ x / 4 := by
    rw [Filter.eventually_all_finset]
    intro x hx
    refine ((tendsto_one_div_add_atTop_nhds_zero_nat
      (𝕜 := ℝ)).eventually
        (Metric.ball_mem_nhds (0 : ℝ)
          (div_pos (hδpos x) (by norm_num : (0 : ℝ) < 4)))).mono ?_
    intro n hn
    have hden_pos : 0 < (n : ℝ) + 1 := by positivity
    simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_of_pos hden_pos] using hn
  filter_upwards [hevent] with n hn x hxK
  rcases mem_iUnion₂.1 (ht hxK) with ⟨c, hct, hxc⟩
  have hvertical : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  have hdist_vertical :
      dist ((x : ℂ)) (unitIntervalUpperBoundarySeq x n) =
        1 / ((n : ℝ) + 1) := by
    have hre :
        ((x : ℂ)).re = (unitIntervalUpperBoundarySeq x n).re := by
      simp [unitIntervalUpperBoundarySeq]
    rw [Complex.dist_of_re_eq hre]
    simp only [unitIntervalUpperBoundarySeq, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_one,
      mul_zero, Real.dist_eq]
    have hden_nonneg : 0 ≤ (n : ℝ) + 1 := by positivity
    simp [hden_nonneg]
  have hzdist :
      dist (unitIntervalUpperBoundarySeq x n) (c : ℂ) < δ c := by
    calc
      dist (unitIntervalUpperBoundarySeq x n) (c : ℂ)
          ≤ dist (unitIntervalUpperBoundarySeq x n) (x : ℂ) +
              dist ((x : ℂ)) (c : ℂ) := dist_triangle _ _ _
      _ = 1 / ((n : ℝ) + 1) + dist x (c : ℝ) := by
            rw [dist_comm (unitIntervalUpperBoundarySeq x n) (x : ℂ)]
            simpa [hdist_vertical] using
              congrArg (fun r => 1 / ((n : ℝ) + 1) + r)
                (Complex.isometry_ofReal.dist_eq x (c : ℝ))
      _ < δ c / 4 + δ c / 4 := by
            exact add_lt_add (hn c hct) (by simpa [Metric.mem_ball] using hxc)
      _ < δ c := by
            linarith [hδpos c]
  simpa using hδ c hzdist

end

end Quantum.TraceInequality.Loewner
