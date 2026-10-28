import Quantum.TraceInequality.Loewner.UnitInterval.Pick.TestIntegralBridge
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Topology.Sequences

/-!
# Chapter 3 Proposition 3.5 bridge discharge

This module discharges the abstract Proposition 3.5 bridge assumptions up to
the concrete Cauchy-kernel and endpoint-collar estimates that follow.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set
open Filter
open scoped Topology
open scoped NNReal
open scoped ENNReal

noncomputable section

/-! ### Discharging the Proposition 3.5 bridge assumptions -/

/--
Uniform elementary bound for the book Poisson kernel on the `x ∈ [-1,1]`
slice.  This is the domination estimate used to make the Fubini product
integrability in the test-integral bridge automatic for regularity test functions.
-/
theorem unitIntervalHerglotzPoissonKernel_bound_on_Icc
    {ε x y : ℝ} (hε : 0 < ε)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    unitIntervalHerglotzPoissonKernel ε x y ≤ 3 * (ε + ε⁻¹) := by
  unfold unitIntervalHerglotzPoissonKernel
  have hden_pos : 0 < (y - x) ^ (2 : ℕ) + ε ^ (2 : ℕ) := by
    positivity
  rw [div_le_iff₀ hden_pos]
  have hnum_bound :
      (1 + y ^ (2 : ℕ)) * ε ≤
        3 * (ε + ε⁻¹) * ((y - x) ^ (2 : ℕ) + ε ^ (2 : ℕ)) := by
    have hy_bound :
        1 + y ^ (2 : ℕ) ≤ 3 * ((y - x) ^ (2 : ℕ) + 1) := by
      have hx2 : x ^ (2 : ℕ) ≤ 1 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), hx.1, hx.2]
      have hy2 : y ^ (2 : ℕ) ≤
          2 * ((y - x) ^ (2 : ℕ) + x ^ (2 : ℕ)) := by
        nlinarith [sq_nonneg (y - 2 * x)]
      nlinarith [sq_nonneg (y - x)]
    have hA : 0 ≤ (y - x) ^ (2 : ℕ) := sq_nonneg (y - x)
    have htail :
        ((y - x) ^ (2 : ℕ) + 1) * ε ≤
          (ε + ε⁻¹) * ((y - x) ^ (2 : ℕ) + ε ^ (2 : ℕ)) := by
      field_simp [hε.ne']
      nlinarith [sq_nonneg ε, hA]
    nlinarith [mul_le_mul_of_nonneg_right hy_bound hε.le]
  simpa [mul_assoc] using hnum_bound

/--
The normalized Proposition 3.5 test kernel is uniformly bounded on
`x ∈ [-1,1]`, uniformly in the Herglotz measure variable `y`.
-/
theorem unitIntervalHerglotzProp35TestKernel_norm_bound_on_Icc
    {ε x y : ℝ} (hε : 0 < ε)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖unitIntervalHerglotzProp35TestKernel ε x y‖ ≤
      Real.pi⁻¹ * (3 * (ε + ε⁻¹)) := by
  have hpk_nonneg :=
    unitIntervalHerglotzProp35TestKernel_nonneg hε (x := x) (y := y)
  rw [Real.norm_of_nonneg hpk_nonneg]
  unfold unitIntervalHerglotzProp35TestKernel
  have hfac_nonneg :
      0 ≤ (Real.pi)⁻¹ * (1 + x ^ (2 : ℕ))⁻¹ := by
    positivity
  have hkernel_bound :=
    unitIntervalHerglotzPoissonKernel_bound_on_Icc (y := y) hε hx
  calc
    Real.pi⁻¹ * (1 + x ^ (2 : ℕ))⁻¹ *
        unitIntervalHerglotzPoissonKernel ε x y
        ≤ Real.pi⁻¹ * (1 + x ^ (2 : ℕ))⁻¹ *
            (3 * (ε + ε⁻¹)) := by
          exact mul_le_mul_of_nonneg_left hkernel_bound hfac_nonneg
    _ ≤ Real.pi⁻¹ * (3 * (ε + ε⁻¹)) := by
          have hinv_le : (1 + x ^ (2 : ℕ))⁻¹ ≤ 1 := by
            exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
          have hleft :
              Real.pi⁻¹ * (1 + x ^ (2 : ℕ))⁻¹ ≤ Real.pi⁻¹ := by
            simpa using
              mul_le_mul_of_nonneg_left hinv_le
                (inv_nonneg.mpr Real.pi_pos.le)
          have hright_nonneg : 0 ≤ 3 * (ε + ε⁻¹) := by
            positivity
          simpa [mul_assoc] using
            mul_le_mul_of_nonneg_right hleft hright_nonneg

/--
Product integrability needed by the test-integral Fubini lemma.  The compact support
comes from the test function vanishing off `(-1,1)`, while the preceding kernel
bound supplies domination on `[-1,1] × ℝ`.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35_testKernel_integrable_prod
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hg_cont : Continuous g)
    (hg_zero : EqOn g 0 (Set.Ioo (-1 : ℝ) 1)ᶜ)
    (hg_nonneg : 0 ≤ g) (hg_le_one : g ≤ 1) :
    Integrable
      (Function.uncurry fun x y : ℝ =>
        g x * unitIntervalHerglotzProp35TestKernel ε x y)
      ((volume : Measure ℝ).prod (data.measure : Measure ℝ)) := by
  classical
  let μ : Measure (ℝ × ℝ) :=
    (volume : Measure ℝ).prod (data.measure : Measure ℝ)
  let s : Set (ℝ × ℝ) := Set.Icc (-1 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)
  let F : ℝ × ℝ → ℝ := Function.uncurry fun x y : ℝ =>
    g x * unitIntervalHerglotzProp35TestKernel ε x y
  have hmeas : AEStronglyMeasurable F μ := by
    have hm : Measurable F := by
      dsimp [F]
      unfold unitIntervalHerglotzProp35TestKernel unitIntervalHerglotzPoissonKernel
      fun_prop
    exact hm.aestronglyMeasurable
  have hs_meas : MeasurableSet s := by
    dsimp [s]
    exact measurableSet_Icc.prod MeasurableSet.univ
  have hs_finite : μ s ≠ ∞ := by
    dsimp [μ, s]
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top (by simp) (by finiteness)
  let C : ℝ := Real.pi⁻¹ * (3 * (ε + ε⁻¹))
  have h_on : IntegrableOn F s μ := by
    refine Measure.integrableOn_of_bounded (M := C) hs_finite hmeas ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict hs_meas] with p hp
    have hg_abs : ‖g p.1‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr
        ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans (hg_nonneg p.1),
          hg_le_one p.1⟩
    have hkernel :
        ‖unitIntervalHerglotzProp35TestKernel ε p.1 p.2‖ ≤ C := by
      exact unitIntervalHerglotzProp35TestKernel_norm_bound_on_Icc hε hp.1
    calc
      ‖F p‖ =
          ‖g p.1‖ * ‖unitIntervalHerglotzProp35TestKernel ε p.1 p.2‖ := by
            rcases p with ⟨x, y⟩
            simp [F, norm_mul]
      _ ≤ 1 * C := by
            exact mul_le_mul hg_abs hkernel (norm_nonneg _) zero_le_one
      _ = C := by simp
  have h_ind : Integrable (s.indicator F) μ := h_on.integrable_indicator hs_meas
  refine h_ind.congr ?_
  filter_upwards with p
  by_cases hp : p ∈ s
  · simp [s, F, hp]
  · have hx_not : p.1 ∉ Set.Ioo (-1 : ℝ) 1 := by
      intro hx
      exact hp ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, trivial⟩
    have hgx : g p.1 = 0 := hg_zero hx_not
    change (s.indicator F) p = F p
    rw [Set.indicator_of_notMem hp]
    rcases p with ⟨x, y⟩
    dsimp [F] at hgx ⊢
    rw [hgx, zero_mul]

/-- The Poisson-side weighted sequence before applying the zero-limit estimate. -/
def UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonSeq
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x : ℝ,
    g x * ((Real.pi)⁻¹ * (1 + x ^ (2 : ℕ))⁻¹) *
      (∫ y : ℝ, unitIntervalHerglotzPoissonKernel
        (1 / ((n : ℝ) + 1)) x y ∂(data.measure : Measure ℝ))

/-- The Fubini-swapped approximate-identity sequence. -/
def UnitIntervalPickHerglotzUpperRawData.prop35FubiniApproxSeq
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ y : ℝ, (∫ x : ℝ,
    g x * unitIntervalHerglotzProp35TestKernel
      (1 / ((n : ℝ) + 1)) x y) ∂(data.measure : Measure ℝ)

/--
The original test-integral sequence is the weighted Poisson sequence.  This is the
normal form used by the boundary-imaginary-part vanishing estimate.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35TestIntegralSeq_eq_weightedPoissonSeq
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (n : ℕ) :
    data.prop35TestIntegralSeq g n =
      data.prop35WeightedPoissonSeq g n := by
  unfold UnitIntervalPickHerglotzUpperRawData.prop35TestIntegralSeq
  unfold UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonSeq
  refine integral_congr_ae ?_
  filter_upwards with x
  have hconst := integral_const_mul
    (r := g x * ((Real.pi)⁻¹ * (1 + x ^ (2 : ℕ))⁻¹))
    (f := fun y : ℝ => unitIntervalHerglotzPoissonKernel
      (1 / ((n : ℝ) + 1)) x y)
    (μ := (data.measure : Measure ℝ))
  calc
    (∫ y : ℝ,
      g x * unitIntervalHerglotzProp35TestKernel
        (1 / ((n : ℝ) + 1)) x y ∂(data.measure : Measure ℝ))
        = ∫ y : ℝ,
            (g x * ((Real.pi)⁻¹ * (1 + x ^ (2 : ℕ))⁻¹)) *
              unitIntervalHerglotzPoissonKernel (1 / ((n : ℝ) + 1)) x y
            ∂(data.measure : Measure ℝ) := by
            refine integral_congr_ae ?_
            filter_upwards with y
            unfold unitIntervalHerglotzProp35TestKernel
            ring
    _ = g x * (Real.pi⁻¹ * (1 + x ^ (2 : ℕ))⁻¹) *
          (∫ y : ℝ, unitIntervalHerglotzPoissonKernel
            (1 / ((n : ℝ) + 1)) x y ∂(data.measure : Measure ℝ)) := by
            simpa [mul_assoc] using hconst

/--
Zero-limit transfer for the Proposition 3.5 Poisson side.  The analytic estimate to be
supplied here is the weighted Poisson sequence tending to zero.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35_testIntegralSeq_tendsto_zero
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ)
    (hzero : Tendsto
      (fun n : ℕ => data.prop35WeightedPoissonSeq g n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => data.prop35TestIntegralSeq g n) atTop (𝓝 0) := by
  refine hzero.congr' ?_
  filter_upwards with n
  exact (data.prop35TestIntegralSeq_eq_weightedPoissonSeq g n).symm

/--
Fubini identifies the test-integral sequence with the approximate-identity sequence
once product integrability is supplied.  For continuous tests vanishing off
`(-1,1)` with values in `[0,1]` it is
`UnitIntervalPickHerglotzUpperRawData.prop35_testKernel_integrable_prod` above.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35TestIntegralSeq_eq_fubiniApproxSeq
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (n : ℕ)
    (hInt : Integrable
      (Function.uncurry fun x y : ℝ =>
        g x * unitIntervalHerglotzProp35TestKernel
          (1 / ((n : ℝ) + 1)) x y)
      ((volume : Measure ℝ).prod (data.measure : Measure ℝ))) :
    data.prop35TestIntegralSeq g n =
      data.prop35FubiniApproxSeq g n := by
  unfold UnitIntervalPickHerglotzUpperRawData.prop35TestIntegralSeq
  unfold UnitIntervalPickHerglotzUpperRawData.prop35FubiniApproxSeq
  exact data.prop35_fubini_testKernel g (1 / ((n : ℝ) + 1)) hInt

/--
Approximate-identity limit transfer for the Proposition 3.5 Fubini side.  The
analytic input is the convergence of the Fubini-swapped normalized Cauchy
kernel to the original test integral; for continuous `g` with values in `[0, 1]`
it is `UnitIntervalPickHerglotzUpperRawData.prop35FubiniApproxSeq_tendsto_integral_concrete`
(`MeasureDomination.lean`).
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35_testIntegralSeq_tendsto_integral
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ)
    (hInt : ∀ n : ℕ, Integrable
      (Function.uncurry fun x y : ℝ =>
        g x * unitIntervalHerglotzProp35TestKernel
          (1 / ((n : ℝ) + 1)) x y)
      ((volume : Measure ℝ).prod (data.measure : Measure ℝ)))
    (happrox : Tendsto
      (fun n : ℕ => data.prop35FubiniApproxSeq g n) atTop
        (𝓝 (∫ y : ℝ, g y ∂(data.measure : Measure ℝ)))) :
    Tendsto (fun n : ℕ => data.prop35TestIntegralSeq g n) atTop
      (𝓝 (∫ y : ℝ, g y ∂(data.measure : Measure ℝ))) := by
  refine happrox.congr' ?_
  filter_upwards with n
  exact (data.prop35TestIntegralSeq_eq_fubiniApproxSeq g n (hInt n)).symm

/-! ### Tendsto inputs for the Proposition 3.5 bridge -/

/--
Uniform `x`-integral domination contract for the normalized Proposition 3.5
kernel.  The book proof supplies this by the normalized Cauchy kernel estimate;
the declaration records the exact Lean shape needed by the dominated
convergence step.
-/
theorem unitIntervalHerglotzProp35TestKernel_xIntegral_norm_bound
    (B : ℝ)
    (hB :
      ∀ {ε y : ℝ}, 0 < ε → ε ≤ 1 →
        (∫ x : ℝ, ‖unitIntervalHerglotzProp35TestKernel ε x y‖) ≤ B)
    {ε y : ℝ} (hε : 0 < ε) (hε_le : ε ≤ 1) :
    (∫ x : ℝ, ‖unitIntervalHerglotzProp35TestKernel ε x y‖) ≤ B :=
  hB hε hε_le

/-- The weighted Poisson integrand used for the zero-limit side of the recovery bridge. -/
def UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonIntegrand
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  g x * ((Real.pi)⁻¹ * (1 + x ^ (2 : ℕ))⁻¹) *
    (∫ y : ℝ, unitIntervalHerglotzPoissonKernel
      (1 / ((n : ℝ) + 1)) x y ∂(data.measure : Measure ℝ))

/-- The weighted Poisson sequence is the integral of its named integrand. -/
theorem UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonSeq_eq_integral_integrand
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (n : ℕ) :
    data.prop35WeightedPoissonSeq g n =
      ∫ x : ℝ, data.prop35WeightedPoissonIntegrand g n x := by
  rfl

/-- The weighted Poisson integrand tends pointwise to zero for supported tests. -/
theorem UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonIntegrand_tendsto_zero
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ)
    (hg_zero : EqOn g 0 (Set.Ioo (-1 : ℝ) 1)ᶜ)
    (x : ℝ) :
    Tendsto (fun n : ℕ => data.prop35WeightedPoissonIntegrand g n x)
      atTop (𝓝 0) := by
  by_cases hxg : g x = 0
  · rw [show
        (fun n : ℕ => data.prop35WeightedPoissonIntegrand g n x) =
          fun _n : ℕ => (0 : ℝ) by
        funext n
        simp [UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonIntegrand,
          hxg]]
    exact tendsto_const_nhds
  · have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := by
      by_contra hxI
      exact hxg (hg_zero hxI)
    have hP :
        Tendsto
          (fun n : ℕ =>
            ∫ y : ℝ, unitIntervalHerglotzPoissonKernel
              (1 / ((n : ℝ) + 1)) x y ∂(data.measure : Measure ℝ))
          atTop (𝓝 0) :=
      data.poissonIntegral_tendsto_zero_of_boundary_im_zero x
        (pickExtension_boundary_im_tendsto_zero_on_Ioo data.pick hxI)
    have hmul :
        Tendsto
          (fun n : ℕ =>
            (g x * ((Real.pi)⁻¹ * (1 + x ^ (2 : ℕ))⁻¹)) *
              (∫ y : ℝ, unitIntervalHerglotzPoissonKernel
                (1 / ((n : ℝ) + 1)) x y ∂(data.measure : Measure ℝ)))
          atTop (𝓝 ((g x * ((Real.pi)⁻¹ *
            (1 + x ^ (2 : ℕ))⁻¹)) * 0)) :=
      tendsto_const_nhds.mul hP
    simpa [UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonIntegrand]
      using hmul

/--
Dominated-convergence producer for the zero-limit normal form.  The pointwise
limit comes from the boundary-imaginary vanishing already proved above; the
remaining book estimate is the stated domination hypothesis.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonSeq_tendsto_zero
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ)
    (hg_zero : EqOn g 0 (Set.Ioo (-1 : ℝ) 1)ᶜ)
    (bound : ℝ → ℝ)
    (hmeas :
      ∀ n : ℕ, AEStronglyMeasurable
        (fun x : ℝ => data.prop35WeightedPoissonIntegrand g n x)
        (volume : Measure ℝ))
    (hbound_int : Integrable bound (volume : Measure ℝ))
    (hbound :
      ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure ℝ),
        ‖data.prop35WeightedPoissonIntegrand g n x‖ ≤ bound x) :
    Tendsto (fun n : ℕ => data.prop35WeightedPoissonSeq g n) atTop (𝓝 0) := by
  have hlim :
      ∀ᵐ x ∂(volume : Measure ℝ),
        Tendsto (fun n : ℕ => data.prop35WeightedPoissonIntegrand g n x)
          atTop (𝓝 (0 : ℝ)) :=
    MeasureTheory.ae_of_all (volume : Measure ℝ) fun x =>
      data.prop35WeightedPoissonIntegrand_tendsto_zero g hg_zero x
  have h :=
    tendsto_integral_of_dominated_convergence
      (μ := (volume : Measure ℝ)) bound hmeas hbound_int hbound hlim
  simpa [UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonSeq,
    UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonIntegrand]
    using h

/-- The inner `x`-integral in the Fubini approximate-identity normal form. -/
def UnitIntervalPickHerglotzUpperRawData.prop35FubiniApproxInner
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  let _μ : Measure ℝ := (data.measure : Measure ℝ)
  ∫ x : ℝ, g x *
    unitIntervalHerglotzProp35TestKernel (1 / ((n : ℝ) + 1)) x y

/-- The Fubini approximate-identity sequence is the integral of its inner kernel. -/
theorem UnitIntervalPickHerglotzUpperRawData.prop35FubiniApproxSeq_eq_integral_inner
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (n : ℕ) :
    data.prop35FubiniApproxSeq g n =
      ∫ y : ℝ, data.prop35FubiniApproxInner g n y
        ∂(data.measure : Measure ℝ) := by
  rfl

/--
Dominated-convergence producer for the Fubini approximate-identity normal form
over the finite Herglotz measure.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35FubiniApproxSeq_tendsto_integral
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
        Tendsto (fun n : ℕ => data.prop35FubiniApproxInner g n y)
          atTop (𝓝 (g y))) :
    Tendsto (fun n : ℕ => data.prop35FubiniApproxSeq g n) atTop
      (𝓝 (∫ y : ℝ, g y ∂(data.measure : Measure ℝ))) := by
  have h :=
    tendsto_integral_of_dominated_convergence
      (μ := (data.measure : Measure ℝ)) bound hmeas hbound_int hbound hpoint
  simpa [UnitIntervalPickHerglotzUpperRawData.prop35FubiniApproxSeq,
    UnitIntervalPickHerglotzUpperRawData.prop35FubiniApproxInner]
    using h

/--
The recovery consumer immediately before the full Proposition 3.5 producer turns
the two generated Tendsto normal-form inputs into the measure-zero conclusion
required by the already implemented measure-recovery bridge.

Lean-deviation: the former bridge input is integrated into the closed recovery
chain here.
-/
theorem UnitIntervalPickHerglotzUpperRawData.measure_Ioo_eq_zero_of_prop35_limits
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (hzero :
      ∀ (g : ℝ → ℝ), Continuous g →
        EqOn g 0 (Set.Ioo (-1 : ℝ) 1)ᶜ →
        0 ≤ g → g ≤ 1 →
        Tendsto (fun n : ℕ => data.prop35WeightedPoissonSeq g n) atTop (𝓝 0))
    (happrox :
      ∀ (g : ℝ → ℝ), Continuous g →
        EqOn g 0 (Set.Ioo (-1 : ℝ) 1)ᶜ →
        0 ≤ g → g ≤ 1 →
        Tendsto (fun n : ℕ => data.prop35FubiniApproxSeq g n) atTop
          (𝓝 (∫ y : ℝ, g y ∂(data.measure : Measure ℝ)))) :
    (data.measure : Measure ℝ) (Set.Ioo (-1 : ℝ) 1) = 0 :=
by
  refine data.measure_Ioo_eq_zero_of_continuous_test_integrals_zero ?_
  intro g hg_cont hg_zero hg_nonneg hg_le_one
  exact data.prop35_testIntegral_eq_zero_of_tendsto_zero_and_approx g
    (data.prop35_testIntegralSeq_tendsto_zero g
      (hzero g hg_cont hg_zero hg_nonneg hg_le_one)
    )
    (data.prop35_testIntegralSeq_tendsto_integral g
      (fun n => data.prop35_testKernel_integrable_prod g
        (by positivity : 0 < 1 / ((n : ℝ) + 1))
        hg_cont hg_zero hg_nonneg hg_le_one)
      (happrox g hg_cont hg_zero hg_nonneg hg_le_one))

end

end Quantum.TraceInequality.Loewner
