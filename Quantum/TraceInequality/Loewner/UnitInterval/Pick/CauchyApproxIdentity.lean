import Quantum.TraceInequality.Loewner.UnitInterval.Pick.CauchyKernel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Topology.Sequences

/-!
# Chapter 3 Cauchy-average approximate identity

This module proves the fixed-point Cauchy-average approximate identity used by
Proposition 3.5.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set
open Filter
open scoped Topology
open scoped NNReal
open scoped ENNReal

noncomputable section

/-! ### Cauchy-average approximate identity -/

/--
The standard centered Cauchy density that appears after the scale change
`x = y + ε t`.
-/
def unitIntervalHerglotzStandardCauchyKernel (t : ℝ) : ℝ :=
  Real.pi⁻¹ * (1 + t ^ (2 : ℕ))⁻¹

/-- The standard centered Cauchy density is nonnegative. -/
theorem unitIntervalHerglotzStandardCauchyKernel_nonneg (t : ℝ) :
    0 ≤ unitIntervalHerglotzStandardCauchyKernel t := by
  dsimp [unitIntervalHerglotzStandardCauchyKernel]
  positivity

/-- The standard centered Cauchy density is integrable. -/
theorem unitIntervalHerglotzStandardCauchyKernel_integrable :
    Integrable unitIntervalHerglotzStandardCauchyKernel
      (volume : Measure ℝ) := by
  simpa [unitIntervalHerglotzStandardCauchyKernel, mul_comm] using
    integrable_inv_one_add_sq.const_mul (Real.pi⁻¹)

/-- The standard centered Cauchy density has total mass one. -/
theorem unitIntervalHerglotzStandardCauchyKernel_integral :
    (∫ t : ℝ, unitIntervalHerglotzStandardCauchyKernel t) = 1 := by
  change
    (∫ t : ℝ, Real.pi⁻¹ * (1 + t ^ (2 : ℕ))⁻¹) = 1
  rw [integral_const_mul, integral_univ_inv_one_add_sq]
  field_simp [Real.pi_ne_zero]

/--
The weighted test function on which the fixed-`y` Cauchy average acts in
Proposition 3.5.
-/
def unitIntervalHerglotzProp35WeightedTest (g : ℝ → ℝ) (y x : ℝ) : ℝ :=
  g x * ((1 + y ^ (2 : ℕ)) * (1 + x ^ (2 : ℕ))⁻¹)

/-- At the base point, the Proposition 3.5 weight is exactly one. -/
theorem unitIntervalHerglotzProp35WeightedTest_self
    (g : ℝ → ℝ) (y : ℝ) :
    unitIntervalHerglotzProp35WeightedTest g y y = g y := by
  unfold unitIntervalHerglotzProp35WeightedTest
  have h : 1 + y ^ (2 : ℕ) ≠ 0 := by positivity
  field_simp [h]

/-- Continuity of the weighted test function for fixed `y`. -/
theorem unitIntervalHerglotzProp35WeightedTest_continuous
    (g : ℝ → ℝ) (hg_cont : Continuous g) (y : ℝ) :
    Continuous (fun x : ℝ => unitIntervalHerglotzProp35WeightedTest g y x) := by
  unfold unitIntervalHerglotzProp35WeightedTest
  have hden : Continuous (fun x : ℝ => 1 + x ^ (2 : ℕ)) := by fun_prop
  exact hg_cont.mul
    (continuous_const.mul (hden.inv₀ (by intro x; positivity)))

/--
Uniform-in-`x` bound for the fixed-`y` weighted test function.  This is the
tail domination input for the Cauchy approximate-identity argument.
-/
theorem unitIntervalHerglotzProp35WeightedTest_norm_bound
    (g : ℝ → ℝ) (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_le_one : ∀ x : ℝ, g x ≤ 1) (y x : ℝ) :
    ‖unitIntervalHerglotzProp35WeightedTest g y x‖ ≤
      1 + y ^ (2 : ℕ) := by
  unfold unitIntervalHerglotzProp35WeightedTest
  have hy_nonneg : 0 ≤ 1 + y ^ (2 : ℕ) := by positivity
  have hfac_nonneg :
      0 ≤ (1 + y ^ (2 : ℕ)) * (1 + x ^ (2 : ℕ))⁻¹ := by
    positivity
  have hfac_le :
      (1 + y ^ (2 : ℕ)) * (1 + x ^ (2 : ℕ))⁻¹ ≤
        1 + y ^ (2 : ℕ) := by
    have hinv_le_one : (1 + x ^ (2 : ℕ))⁻¹ ≤ 1 := by
      have hge : 1 ≤ 1 + x ^ (2 : ℕ) := by nlinarith [sq_nonneg x]
      exact inv_le_one_of_one_le₀ hge
    simpa using mul_le_mul_of_nonneg_left hinv_le_one hy_nonneg
  have hprod_nonneg :
      0 ≤ g x * ((1 + y ^ (2 : ℕ)) * (1 + x ^ (2 : ℕ))⁻¹) := by
    exact mul_nonneg (hg_nonneg x) hfac_nonneg
  rw [Real.norm_of_nonneg hprod_nonneg]
  calc
    g x * ((1 + y ^ (2 : ℕ)) * (1 + x ^ (2 : ℕ))⁻¹)
        ≤ 1 * ((1 + y ^ (2 : ℕ)) * (1 + x ^ (2 : ℕ))⁻¹) := by
          exact mul_le_mul_of_nonneg_right (hg_le_one x) hfac_nonneg
    _ ≤ 1 + y ^ (2 : ℕ) := by simpa using hfac_le

/--
Scale-change normal form for Cauchy averages.  After substituting
`x = y + ε t`, the location/scale Cauchy density becomes the standard
centered Cauchy density.
-/
theorem unitIntervalHerglotz_cauchyAverage_eq_scaled
    (φ : ℝ → ℝ) {ε y : ℝ} (hε : 0 < ε) :
    (∫ x : ℝ, φ x * ProbabilityTheory.cauchyPDFReal y ⟨ε, hε.le⟩ x) =
      ∫ t : ℝ,
        φ (y + ε * t) * unitIntervalHerglotzStandardCauchyKernel t := by
  let F : ℝ → ℝ := fun x =>
    φ x * ProbabilityTheory.cauchyPDFReal y ⟨ε, hε.le⟩ x
  let G : ℝ → ℝ := fun u => ε * F (y + u)
  have hscale := MeasureTheory.Measure.integral_comp_mul_left
    (g := G) (a := ε)
  have hleft :
      (∫ t : ℝ, G (ε * t)) =
        ∫ t : ℝ,
          φ (y + ε * t) * unitIntervalHerglotzStandardCauchyKernel t := by
    refine integral_congr_ae ?_
    filter_upwards with t
    dsimp [G, F, unitIntervalHerglotzStandardCauchyKernel]
    rw [ProbabilityTheory.cauchyPDFReal_def]
    simp only [NNReal.coe_mk]
    field_simp [hε.ne']
    ring_nf
  have hright :
      |ε⁻¹| • (∫ u : ℝ, G u) =
        ∫ u : ℝ, F (y + u) := by
    dsimp [G]
    rw [integral_const_mul]
    simp [hε.ne', abs_of_pos (inv_pos.mpr hε)]
  have htrans :
      (∫ u : ℝ, F (y + u)) = ∫ x : ℝ, F x := by
    simpa [F, add_comm] using
      (MeasureTheory.integral_add_right_eq_self (fun x : ℝ => F x) y)
  calc
    (∫ x : ℝ, F x) = ∫ u : ℝ, F (y + u) := htrans.symm
    _ = |ε⁻¹| • (∫ u : ℝ, G u) := hright.symm
    _ = ∫ t : ℝ, G (ε * t) := hscale.symm
    _ = ∫ t : ℝ,
          φ (y + ε * t) *
            unitIntervalHerglotzStandardCauchyKernel t := hleft

/--
Local continuity plus the standard Cauchy domination gives the scaled
Cauchy-average approximate identity.
-/
theorem unitIntervalHerglotz_scaledCauchyAverage_tendsto
    (φ : ℝ → ℝ) (y M : ℝ) (hφ_cont : Continuous φ)
    (hM : ∀ x : ℝ, ‖φ x‖ ≤ M) :
    Tendsto
      (fun n : ℕ => ∫ t : ℝ,
        φ (y + (1 / ((n : ℝ) + 1)) * t) *
          unitIntervalHerglotzStandardCauchyKernel t)
      atTop (𝓝 (φ y)) := by
  let F : ℕ → ℝ → ℝ := fun n t =>
    φ (y + (1 / ((n : ℝ) + 1)) * t) *
      unitIntervalHerglotzStandardCauchyKernel t
  let f0 : ℝ → ℝ := fun t =>
    φ y * unitIntervalHerglotzStandardCauchyKernel t
  let bound : ℝ → ℝ := fun t =>
    M * unitIntervalHerglotzStandardCauchyKernel t
  have hbound_int : Integrable bound (volume : Measure ℝ) :=
    unitIntervalHerglotzStandardCauchyKernel_integrable.const_mul M
  have hmeas :
      ∀ n : ℕ, AEStronglyMeasurable (F n) (volume : Measure ℝ) := by
    intro n
    exact (by
      dsimp [F, unitIntervalHerglotzStandardCauchyKernel]
      fun_prop : Measurable (F n)).aestronglyMeasurable
  have hbound :
      ∀ n : ℕ, ∀ᵐ t ∂(volume : Measure ℝ), ‖F n t‖ ≤ bound t := by
    intro n
    filter_upwards with t
    dsimp [F, bound]
    rw [abs_mul]
    have hstd_nonneg := unitIntervalHerglotzStandardCauchyKernel_nonneg t
    have hstd_abs :
        |unitIntervalHerglotzStandardCauchyKernel t| =
          unitIntervalHerglotzStandardCauchyKernel t :=
      abs_of_nonneg hstd_nonneg
    have hφ_bound :
        |φ (y + 1 / ((n : ℝ) + 1) * t)| ≤ M := by
      simpa [Real.norm_eq_abs] using
        hM (y + 1 / ((n : ℝ) + 1) * t)
    rw [hstd_abs]
    exact mul_le_mul_of_nonneg_right hφ_bound hstd_nonneg
  have hlim :
      ∀ᵐ t ∂(volume : Measure ℝ),
        Tendsto (fun n : ℕ => F n t) atTop (𝓝 (f0 t)) := by
    filter_upwards with t
    dsimp [F, f0]
    have heps :
        Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) * t)
          atTop (𝓝 0) := by
      simpa [zero_mul] using
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul
          tendsto_const_nhds)
    have harg :
        Tendsto (fun n : ℕ => y + (1 / ((n : ℝ) + 1)) * t)
          atTop (𝓝 y) := by
      simpa [add_zero] using tendsto_const_nhds.add heps
    exact (hφ_cont.continuousAt.tendsto.comp harg).mul
      tendsto_const_nhds
  have hdct :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      bound hmeas hbound_int hbound hlim
  have htarget : (∫ t : ℝ, f0 t) = φ y := by
    dsimp [f0]
    rw [integral_const_mul, unitIntervalHerglotzStandardCauchyKernel_integral]
    ring
  simpa [F, htarget] using hdct

/--
The fixed-`y` Cauchy average is an approximate identity for continuous bounded
test functions.
-/
theorem unitIntervalHerglotz_cauchyAverage_tendsto
    (φ : ℝ → ℝ) (y M : ℝ) (hφ_cont : Continuous φ)
    (hM : ∀ x : ℝ, ‖φ x‖ ≤ M) :
    Tendsto
      (fun n : ℕ => ∫ x : ℝ,
        φ x * ProbabilityTheory.cauchyPDFReal y
          ⟨1 / ((n : ℝ) + 1), by positivity⟩ x)
      atTop (𝓝 (φ y)) := by
  have hscaled :=
    unitIntervalHerglotz_scaledCauchyAverage_tendsto
      φ y M hφ_cont hM
  refine hscaled.congr' ?_
  filter_upwards with n
  exact (unitIntervalHerglotz_cauchyAverage_eq_scaled
    φ (y := y) (ε := 1 / ((n : ℝ) + 1)) (by positivity)).symm

/--
Concrete pointwise approximate-identity input for the Proposition 3.5 weighted
test function.
-/
theorem unitIntervalHerglotzProp35WeightedTest_cauchyAverage_tendsto
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_le_one : ∀ x : ℝ, g x ≤ 1) (y : ℝ) :
    Tendsto
      (fun n : ℕ => ∫ x : ℝ,
        unitIntervalHerglotzProp35WeightedTest g y x *
          ProbabilityTheory.cauchyPDFReal y
            ⟨1 / ((n : ℝ) + 1), by positivity⟩ x)
      atTop (𝓝 (g y)) := by
  have h :=
    unitIntervalHerglotz_cauchyAverage_tendsto
      (fun x : ℝ => unitIntervalHerglotzProp35WeightedTest g y x)
      y (1 + y ^ (2 : ℕ))
      (unitIntervalHerglotzProp35WeightedTest_continuous g hg_cont y)
      (unitIntervalHerglotzProp35WeightedTest_norm_bound
        g hg_nonneg hg_le_one y)
  simpa [unitIntervalHerglotzProp35WeightedTest_self] using h

/--
Normal form for the Fubini inner integral: it is the Cauchy average of the
weighted test function `g x * (1+y^2)/(1+x^2)`.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35FubiniApproxInner_eq_cauchyAverage
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    (∫ x : ℝ, g x * unitIntervalHerglotzProp35TestKernel ε x y) =
      ∫ x : ℝ,
        (g x * ((1 + y ^ (2 : ℕ)) * (1 + x ^ (2 : ℕ))⁻¹)) *
          ProbabilityTheory.cauchyPDFReal y ⟨ε, hε.le⟩ x := by
  let _μ : Measure ℝ := (data.measure : Measure ℝ)
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [unitIntervalHerglotzProp35TestKernel_eq_weighted_cauchyPDFReal hε.le]
  ring

/--
Sequence form of the fixed-`y` Cauchy average.  The genuine approximation
identity estimate is isolated in the hypothesis; this lemma connects that
estimate to the canonical `prop35FubiniApproxInner` name.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35FubiniApproxInner_tendsto_of_cauchyAverage
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (y : ℝ)
    (hpoint :
      Tendsto
        (fun n : ℕ =>
          ∫ x : ℝ,
            (g x * ((1 + y ^ (2 : ℕ)) * (1 + x ^ (2 : ℕ))⁻¹)) *
              ProbabilityTheory.cauchyPDFReal y
                ⟨1 / ((n : ℝ) + 1), by positivity⟩ x)
        atTop (𝓝 (g y))) :
    Tendsto (fun n : ℕ => data.prop35FubiniApproxInner g n y)
      atTop (𝓝 (g y)) := by
  refine hpoint.congr' ?_
  filter_upwards with n
  unfold UnitIntervalPickHerglotzUpperRawData.prop35FubiniApproxInner
  exact (data.prop35FubiniApproxInner_eq_cauchyAverage g
    (by positivity : 0 < 1 / ((n : ℝ) + 1)) y).symm

/--
The Cauchy-average theorem supplies the fixed-`y` pointwise limit required by
the Cauchy-kernel bridge.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35FubiniApproxInner_tendsto_pointwise
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_le_one : ∀ x : ℝ, g x ≤ 1) (y : ℝ) :
    Tendsto (fun n : ℕ => data.prop35FubiniApproxInner g n y)
      atTop (𝓝 (g y)) := by
  refine data.prop35FubiniApproxInner_tendsto_of_cauchyAverage g y ?_
  simpa [unitIntervalHerglotzProp35WeightedTest] using
    unitIntervalHerglotzProp35WeightedTest_cauchyAverage_tendsto
      g hg_cont hg_nonneg hg_le_one y

/--
Concrete Cauchy-kernel wrapper for the Fubini-side DCT producer: after the Cauchy
pointwise averages and domination are supplied in concrete kernel form, the
sequence converges to the original test integral.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35FubiniApproxSeq_tendsto_integral_of_cauchyInputs
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ)
    (bound : ℝ → ℝ)
    (hmeas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun y : ℝ => data.prop35FubiniApproxInner g n y)
        (data.measure : Measure ℝ))
    (hbound_int : Integrable bound (data.measure : Measure ℝ))
    (hbound :
      ∀ n : ℕ, ∀ᵐ y ∂(data.measure : Measure ℝ),
        ‖data.prop35FubiniApproxInner g n y‖ ≤ bound y)
    (hpoint :
      ∀ᵐ y ∂(data.measure : Measure ℝ),
        Tendsto
          (fun n : ℕ =>
            ∫ x : ℝ,
              (g x * ((1 + y ^ (2 : ℕ)) * (1 + x ^ (2 : ℕ))⁻¹)) *
                ProbabilityTheory.cauchyPDFReal y
                  ⟨1 / ((n : ℝ) + 1), by positivity⟩ x)
          atTop (𝓝 (g y))) :
    Tendsto (fun n : ℕ => data.prop35FubiniApproxSeq g n) atTop
      (𝓝 (∫ y : ℝ, g y ∂(data.measure : Measure ℝ))) := by
  refine data.prop35FubiniApproxSeq_tendsto_integral g bound hmeas hbound_int hbound ?_
  filter_upwards [hpoint] with y hy
  exact data.prop35FubiniApproxInner_tendsto_of_cauchyAverage g y hy

/--
Cauchy-average wrapper for the Fubini-side DCT producer: the Cauchy approximate
identity now supplies the pointwise input without an extra hypothesis.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35FubiniApproxSeq_tendsto_integral_of_cauchyApprox
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_le_one : ∀ x : ℝ, g x ≤ 1)
    (bound : ℝ → ℝ)
    (hmeas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun y : ℝ => data.prop35FubiniApproxInner g n y)
        (data.measure : Measure ℝ))
    (hbound_int : Integrable bound (data.measure : Measure ℝ))
    (hbound :
      ∀ n : ℕ, ∀ᵐ y ∂(data.measure : Measure ℝ),
        ‖data.prop35FubiniApproxInner g n y‖ ≤ bound y) :
    Tendsto (fun n : ℕ => data.prop35FubiniApproxSeq g n) atTop
      (𝓝 (∫ y : ℝ, g y ∂(data.measure : Measure ℝ))) := by
  refine data.prop35FubiniApproxSeq_tendsto_integral_of_cauchyInputs
    g bound hmeas hbound_int hbound ?_
  filter_upwards with y
  simpa [unitIntervalHerglotzProp35WeightedTest] using
    unitIntervalHerglotzProp35WeightedTest_cauchyAverage_tendsto
      g hg_cont hg_nonneg hg_le_one y

end

end Quantum.TraceInequality.Loewner
