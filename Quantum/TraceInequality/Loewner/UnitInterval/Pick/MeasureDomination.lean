import Quantum.TraceInequality.Loewner.UnitInterval.Pick.CauchyApproxIdentity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Chapter 3 measure-side domination assembly

This module assembles measurability and domination inputs for the measure-side
part of Proposition 3.5.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set
open Filter
open scoped Topology
open scoped NNReal
open scoped ENNReal

noncomputable section

/-! ### Measure-side domination assembly -/

/--
For fixed Herglotz variable `y`, the normalized Proposition 3.5 kernel is
integrable in the averaging variable `x`.
-/
theorem unitIntervalHerglotzProp35TestKernel_integrable_x
    {ε y : ℝ} (hε : 0 < ε) :
    Integrable (fun x : ℝ => unitIntervalHerglotzProp35TestKernel ε x y)
      (volume : Measure ℝ) := by
  let A : ℝ → ℝ := fun x =>
    2 * ((Real.pi)⁻¹ * ε / ((x - y) ^ (2 : ℕ) + ε ^ (2 : ℕ)))
  let B : ℝ → ℝ := fun x =>
    2 * ((Real.pi)⁻¹ * ε * (1 + x ^ (2 : ℕ))⁻¹)
  have hA_int : Integrable A (volume : Measure ℝ) := by
    exact (ProbabilityTheory.integrable_cauchyPDFReal y (γ := ⟨ε, hε.le⟩)).const_mul 2
  have hB_int : Integrable B (volume : Measure ℝ) := by
    exact (integrable_inv_one_add_sq.const_mul ((Real.pi)⁻¹ * ε)).const_mul 2
  have hAB_int : Integrable (fun x : ℝ => A x + B x) (volume : Measure ℝ) :=
    hA_int.add hB_int
  have hmeas :
      AEStronglyMeasurable
        (fun x : ℝ => unitIntervalHerglotzProp35TestKernel ε x y)
        (volume : Measure ℝ) := by
    have hm : Measurable
        (fun x : ℝ => unitIntervalHerglotzProp35TestKernel ε x y) := by
      unfold unitIntervalHerglotzProp35TestKernel unitIntervalHerglotzPoissonKernel
      fun_prop
    exact hm.aestronglyMeasurable
  refine hAB_int.mono' hmeas ?_
  filter_upwards with x
  dsimp [A, B]
  exact unitIntervalHerglotzProp35TestKernel_norm_pointwise_bound hε

/-- The scales `ε_n = 1/(n+1)` used in Proposition 3.5 are at most one. -/
theorem unitIntervalHerglotz_prop35Scale_le_one (n : ℕ) :
    1 / ((n : ℝ) + 1) ≤ 1 := by
  have hden_pos : 0 < (n : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hden_pos]
  have hn : 0 ≤ (n : ℝ) := by positivity
  nlinarith

/-- Measurability of the Fubini-side inner integral as a function of `y`. -/
theorem UnitIntervalPickHerglotzUpperRawData.prop35FubiniApproxInner_aestronglyMeasurable
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (hg_cont : Continuous g) (n : ℕ) :
    AEStronglyMeasurable
      (fun y : ℝ => data.prop35FubiniApproxInner g n y)
      (data.measure : Measure ℝ) := by
  have hstrong : StronglyMeasurable (fun p : ℝ × ℝ =>
      g p.1 * unitIntervalHerglotzProp35TestKernel
        (1 / ((n : ℝ) + 1)) p.1 p.2) := by
    have hm : Measurable (fun p : ℝ × ℝ =>
        g p.1 * unitIntervalHerglotzProp35TestKernel
          (1 / ((n : ℝ) + 1)) p.1 p.2) := by
      unfold unitIntervalHerglotzProp35TestKernel unitIntervalHerglotzPoissonKernel
      fun_prop
    exact hm.stronglyMeasurable
  have hsm : StronglyMeasurable (fun y : ℝ =>
      ∫ x : ℝ, (fun p : ℝ × ℝ =>
        g p.1 * unitIntervalHerglotzProp35TestKernel
          (1 / ((n : ℝ) + 1)) p.1 p.2) (x, y)) := by
    exact MeasureTheory.StronglyMeasurable.integral_prod_left'
      (μ := (volume : Measure ℝ)) hstrong
  refine hsm.aestronglyMeasurable.congr ?_
  filter_upwards with y
  simp [UnitIntervalPickHerglotzUpperRawData.prop35FubiniApproxInner]

/--
The Fubini-side inner integral is uniformly bounded by `4` for regularity test
functions.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35FubiniApproxInner_norm_bound_four
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_le_one : ∀ x : ℝ, g x ≤ 1)
    (n : ℕ) (y : ℝ) :
    ‖data.prop35FubiniApproxInner g n y‖ ≤ 4 := by
  have hε : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hε_le : 1 / ((n : ℝ) + 1) ≤ 1 :=
    unitIntervalHerglotz_prop35Scale_le_one n
  have hK_norm_int :
      Integrable
        (fun x : ℝ =>
          ‖unitIntervalHerglotzProp35TestKernel
            (1 / ((n : ℝ) + 1)) x y‖)
        (volume : Measure ℝ) :=
    (unitIntervalHerglotzProp35TestKernel_integrable_x
      (y := y) hε).norm
  have hinner_norm := MeasureTheory.norm_integral_le_integral_norm
    (μ := (volume : Measure ℝ))
    (f := fun x : ℝ =>
      g x * unitIntervalHerglotzProp35TestKernel
        (1 / ((n : ℝ) + 1)) x y)
  have hmono :
      (∫ x : ℝ,
        ‖g x * unitIntervalHerglotzProp35TestKernel
          (1 / ((n : ℝ) + 1)) x y‖) ≤
        ∫ x : ℝ,
          ‖unitIntervalHerglotzProp35TestKernel
            (1 / ((n : ℝ) + 1)) x y‖ := by
    have hgK_int :
        Integrable
          (fun x : ℝ =>
            ‖g x * unitIntervalHerglotzProp35TestKernel
              (1 / ((n : ℝ) + 1)) x y‖)
          (volume : Measure ℝ) := by
      refine hK_norm_int.mono' ?_ ?_
      · have hm : Measurable
            (fun x : ℝ =>
              ‖g x * unitIntervalHerglotzProp35TestKernel
                (1 / ((n : ℝ) + 1)) x y‖) := by
          unfold unitIntervalHerglotzProp35TestKernel unitIntervalHerglotzPoissonKernel
          fun_prop
        exact hm.aestronglyMeasurable
      · filter_upwards with x
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        change
          ‖g x * unitIntervalHerglotzProp35TestKernel
            (1 / ((n : ℝ) + 1)) x y‖ ≤
          ‖unitIntervalHerglotzProp35TestKernel
            (1 / ((n : ℝ) + 1)) x y‖
        rw [norm_mul]
        have hg_abs : ‖g x‖ ≤ 1 := by
          rw [Real.norm_eq_abs]
          exact abs_le.mpr ⟨(by linarith [hg_nonneg x]), hg_le_one x⟩
        exact mul_le_of_le_one_left (norm_nonneg _) hg_abs
    refine integral_mono hgK_int hK_norm_int ?_
    intro x
    change
      ‖g x * unitIntervalHerglotzProp35TestKernel
        (1 / ((n : ℝ) + 1)) x y‖ ≤
      ‖unitIntervalHerglotzProp35TestKernel
        (1 / ((n : ℝ) + 1)) x y‖
    rw [norm_mul]
    have hg_abs : ‖g x‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(by linarith [hg_nonneg x]), hg_le_one x⟩
    exact mul_le_of_le_one_left (norm_nonneg _) hg_abs
  calc
    ‖data.prop35FubiniApproxInner g n y‖
        ≤ ∫ x : ℝ,
            ‖g x * unitIntervalHerglotzProp35TestKernel
              (1 / ((n : ℝ) + 1)) x y‖ := by
          simpa [UnitIntervalPickHerglotzUpperRawData.prop35FubiniApproxInner]
            using hinner_norm
    _ ≤ ∫ x : ℝ,
          ‖unitIntervalHerglotzProp35TestKernel
            (1 / ((n : ℝ) + 1)) x y‖ := hmono
    _ ≤ 4 :=
          unitIntervalHerglotzProp35TestKernel_xIntegral_norm_bound_concrete
            hε hε_le

/--
Concrete Fubini-side convergence for continuous `g` with values in `[0, 1]`:
the pointwise Cauchy-average limit is combined here with the concrete
`y`-measure domination bound.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35FubiniApproxSeq_tendsto_integral_concrete
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_le_one : ∀ x : ℝ, g x ≤ 1) :
    Tendsto (fun n : ℕ => data.prop35FubiniApproxSeq g n) atTop
      (𝓝 (∫ y : ℝ, g y ∂(data.measure : Measure ℝ))) := by
  refine data.prop35FubiniApproxSeq_tendsto_integral_of_cauchyApprox
    g hg_cont hg_nonneg hg_le_one (fun _y : ℝ => (4 : ℝ)) ?_ ?_ ?_
  · intro n
    exact data.prop35FubiniApproxInner_aestronglyMeasurable g hg_cont n
  · exact MeasureTheory.integrable_const (4 : ℝ)
  · intro n
    exact MeasureTheory.ae_of_all (data.measure : Measure ℝ) fun y =>
      data.prop35FubiniApproxInner_norm_bound_four
        g hg_cont hg_nonneg hg_le_one n y

/-- Measurability of the weighted Poisson-side integrand. -/
theorem UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonIntegrand_aestronglyMeasurable
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (hg_cont : Continuous g) (n : ℕ) :
    AEStronglyMeasurable
      (fun x : ℝ => data.prop35WeightedPoissonIntegrand g n x)
      (volume : Measure ℝ) := by
  have hkernel_strong : StronglyMeasurable (Function.uncurry fun x y : ℝ =>
      unitIntervalHerglotzPoissonKernel (1 / ((n : ℝ) + 1)) x y) := by
    have hm : Measurable (Function.uncurry fun x y : ℝ =>
        unitIntervalHerglotzPoissonKernel (1 / ((n : ℝ) + 1)) x y) := by
      unfold unitIntervalHerglotzPoissonKernel
      fun_prop
    exact hm.stronglyMeasurable
  have hinner : StronglyMeasurable (fun x : ℝ =>
      ∫ y : ℝ, unitIntervalHerglotzPoissonKernel
        (1 / ((n : ℝ) + 1)) x y ∂(data.measure : Measure ℝ)) := by
    exact MeasureTheory.StronglyMeasurable.integral_prod_right
      (ν := (data.measure : Measure ℝ)) hkernel_strong
  have hmeas : Measurable (fun x : ℝ =>
      g x * ((Real.pi)⁻¹ * (1 + x ^ (2 : ℕ))⁻¹) *
        (∫ y : ℝ, unitIntervalHerglotzPoissonKernel
          (1 / ((n : ℝ) + 1)) x y ∂(data.measure : Measure ℝ))) := by
    exact (hg_cont.measurable.mul (by fun_prop)).mul hinner.measurable
  exact hmeas.aestronglyMeasurable

/-- The weighted Poisson-side integrand is nonnegative for nonnegative tests. -/
theorem UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonIntegrand_nonneg
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (n : ℕ) (x : ℝ) :
    0 ≤ data.prop35WeightedPoissonIntegrand g n x := by
  unfold UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonIntegrand
  have hfac : 0 ≤ (Real.pi)⁻¹ * (1 + x ^ (2 : ℕ))⁻¹ := by positivity
  have hinner : 0 ≤ ∫ y : ℝ,
      unitIntervalHerglotzPoissonKernel (1 / ((n : ℝ) + 1)) x y
        ∂(data.measure : Measure ℝ) := by
    exact integral_nonneg_of_ae
      (MeasureTheory.ae_of_all (data.measure : Measure ℝ) fun y =>
        unitIntervalHerglotzPoissonKernel_nonneg
          (by positivity : 0 < 1 / ((n : ℝ) + 1)))
  exact mul_nonneg (mul_nonneg (hg_nonneg x) hfac) hinner

/--
The weighted Poisson-side integrand vanishes outside the regularity interval
whenever the test function does.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonIntegrand_eq_zero_of_not_mem_Ioo
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (hg_zero : EqOn g 0 (Set.Ioo (-1 : ℝ) 1)ᶜ)
    (n : ℕ) {x : ℝ} (hx : x ∉ Set.Ioo (-1 : ℝ) 1) :
    data.prop35WeightedPoissonIntegrand g n x = 0 := by
  unfold UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonIntegrand
  have hgx : g x = 0 := by simpa using hg_zero hx
  rw [hgx]
  simp

/--
The Poisson integral is bounded above by the boundary imaginary part; the
discarded term is the nonnegative Herglotz slope contribution.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35PoissonIntegral_le_boundary_im
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (n : ℕ) (x : ℝ) :
    (∫ y : ℝ, unitIntervalHerglotzPoissonKernel
      (1 / ((n : ℝ) + 1)) x y ∂(data.measure : Measure ℝ)) ≤
      (data.pick.F (unitIntervalUpperBoundarySeq x n)).im := by
  have heq := data.boundary_im_eq_slope_add_poissonIntegral x n
  have hslope_nonneg : 0 ≤ (data.slope : ℝ) * (1 / ((n : ℝ) + 1)) := by
    positivity
  have hP_nonneg : 0 ≤ ∫ y : ℝ, unitIntervalHerglotzPoissonKernel
      (1 / ((n : ℝ) + 1)) x y ∂(data.measure : Measure ℝ) := by
    exact integral_nonneg_of_ae
      (MeasureTheory.ae_of_all (data.measure : Measure ℝ) fun y =>
        unitIntervalHerglotzPoissonKernel_nonneg
          (by positivity : 0 < 1 / ((n : ℝ) + 1)))
  linarith

/--
Pointwise comparison used for the compact part of the weighted Poisson side.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonIntegrand_le_boundary_im
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (n : ℕ) (x : ℝ) :
    data.prop35WeightedPoissonIntegrand g n x ≤
      g x * ((Real.pi)⁻¹ * (1 + x ^ (2 : ℕ))⁻¹) *
        (data.pick.F (unitIntervalUpperBoundarySeq x n)).im := by
  unfold UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonIntegrand
  have hfactor : 0 ≤ (Real.pi)⁻¹ * (1 + x ^ (2 : ℕ))⁻¹ := by positivity
  have hfac_nonneg :
      0 ≤ g x * ((Real.pi)⁻¹ * (1 + x ^ (2 : ℕ))⁻¹) :=
    mul_nonneg (hg_nonneg x) hfactor
  exact mul_le_mul_of_nonneg_left
    (data.prop35PoissonIntegral_le_boundary_im n x) hfac_nonneg

/--
Weighted Poisson-side DCT wrapper with the concrete measurability input supplied.
The remaining hypothesis is precisely the book collar/domination estimate.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonSeq_tendsto_zero_of_bound
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_zero : EqOn g 0 (Set.Ioo (-1 : ℝ) 1)ᶜ)
    (bound : ℝ → ℝ)
    (hbound_int : Integrable bound (volume : Measure ℝ))
    (hbound :
      ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure ℝ),
        ‖data.prop35WeightedPoissonIntegrand g n x‖ ≤ bound x) :
    Tendsto (fun n : ℕ => data.prop35WeightedPoissonSeq g n) atTop (𝓝 0) := by
  exact data.prop35WeightedPoissonSeq_tendsto_zero g hg_zero bound
    (fun n => data.prop35WeightedPoissonIntegrand_aestronglyMeasurable g hg_cont n)
    hbound_int hbound

end

end Quantum.TraceInequality.Loewner
