import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.RegularizedDerivativeContinuityCore


/-!
# Chapter 20 smooth-Hiai derivative continuity handoff

This file contains the theorem-facing smooth-Hiai handoff, endpoint
oscillation discharge, and final derivative-continuity wrappers.  The
affine convexity and local Lipschitz transfer lemmas live in
`RegularizedDerivativeContinuityCore`.
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

noncomputable section

/--
Conditional smooth-Hiai producer for the regularized derivatives.  The smooth
Hiai input supplies eventual local convexity; the local uniform absolute-value
bound is an explicit analytic input here, supplied from the endpoint oscillation in
`regularized_deriv_eventual_lipschitzOnWith_of_C3SmoothHiai_endpointOscillation`
below.
-/
theorem regularized_deriv_eventual_lipschitzOnWith_of_C3SmoothHiai_absBound
    (smoothHiai :
      ∀ {g : ℝ → ℝ}, LoewnerPosOnUnitInterval g →
        ContDiffOn ℝ 3 g (Set.Ioo (-1 : ℝ) 1) →
          ConvexOn ℝ (Set.Ioo (-1 : ℝ) 1) (deriv g))
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (habs :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ r δ M : ℝ, 0 < δ ∧ δ < r ∧
          (-1 : ℝ) < x - r ∧ x + r < 1 ∧
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
            abs (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z) y) ≤ M)) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ K : ℝ≥0, ∃ U ∈ 𝓝 x, x ∈ U ∧
        ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          LipschitzOnWith K
            (fun y : ℝ =>
              deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)
            U := by
  refine
    regularized_deriv_eventual_lipschitzOnWith_of_eventual_convex_abs_le
      (φ := φ) (f := f) ?_
  intro x hx
  rcases habs x hx with ⟨r, δ, M, hδ, hδr, hleft0, hright0, habsε⟩
  have hr : 0 < r := lt_trans hδ hδr
  have hleftMargin : 0 < x - r + 1 := by linarith
  have hrightMargin : 0 < 1 - (x + r) := by linarith
  have hε_left : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < x - r + 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds hleftMargin)
  have hε_right : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 - (x + r) :=
    nhdsWithin_le_nhds (Iio_mem_nhds hrightMargin)
  have hconv :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ConvexOn ℝ (Metric.ball x r)
          (fun y : ℝ =>
            deriv (fun z : ℝ => hiaiRegularization φ ε f z) y) := by
    filter_upwards [self_mem_nhdsWithin, hε_left, hε_right] with
      ε hεpos hεleft hεright
    have hconvIoo :
        ConvexOn ℝ (Set.Ioo (x - r) (x + r))
          (deriv (fun z : ℝ => hiaiRegularization φ ε f z)) :=
      hiaiRegularization_deriv_convexOn_localAt_of_C3SmoothHiai
        smoothHiai (φ := φ) (f := f) hφ hεpos hr
        (by linarith) (by linarith) hpos
    simpa [Real.ball_eq_Ioo] using hconvIoo
  exact ⟨r, δ, M, hδ, hδr, hconv, habsε⟩

/--
Conditional smooth-Hiai producer where the local uniform derivative bound is
itself produced from a local endpoint oscillation bound for the regularized
functions.
-/
theorem regularized_deriv_eventual_lipschitzOnWith_of_C3SmoothHiai_endpointOscillation
    (smoothHiai :
      ∀ {g : ℝ → ℝ}, LoewnerPosOnUnitInterval g →
        ContDiffOn ℝ 3 g (Set.Ioo (-1 : ℝ) 1) →
          ConvexOn ℝ (Set.Ioo (-1 : ℝ) 1) (deriv g))
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (hosc :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ ρ A : ℝ, 0 < ρ ∧ 0 ≤ A ∧
          (-1 : ℝ) < x - 2 * ρ ∧ x + 2 * ρ < 1 ∧
          (∀ᶠ ε in 𝓝[>] (0 : ℝ),
            |hiaiRegularization φ ε f (x + 2 * ρ) -
              hiaiRegularization φ ε f (x - 2 * ρ)| ≤ A)) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ K : ℝ≥0, ∃ U ∈ 𝓝 x, x ∈ U ∧
        ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          LipschitzOnWith K
            (fun y : ℝ =>
              deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)
            U := by
  have habs :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ r δ M : ℝ, 0 < δ ∧ δ < r ∧
          (-1 : ℝ) < x - r ∧ x + r < 1 ∧
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
            abs (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z) y) ≤ M) :=
    regularized_deriv_eventual_abs_le_of_endpointOscillation
      (φ := φ) (f := f) hφ hpos ?_
  · exact
      regularized_deriv_eventual_lipschitzOnWith_of_C3SmoothHiai_absBound
        smoothHiai (φ := φ) (f := f) hφ hpos habs
  intro x hx
  rcases hosc x hx with ⟨ρ, A, hρ, hA, hleft, hright, hoscEv⟩
  refine ⟨ρ, A, hρ, hA, hleft, hright, ?_, hoscEv⟩
  have hleftMargin : 0 < x - 2 * ρ + 1 := by linarith
  have hrightMargin : 0 < 1 - (x + 2 * ρ) := by linarith
  have hε_left : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < x - 2 * ρ + 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds hleftMargin)
  have hε_right : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 - (x + 2 * ρ) :=
    nhdsWithin_le_nhds (Iio_mem_nhds hrightMargin)
  filter_upwards [self_mem_nhdsWithin, hε_left, hε_right] with
    ε hεpos hεleft hεright
  have hR : 0 < 2 * ρ := by positivity
  have hconvIoo :
      ConvexOn ℝ (Set.Ioo (x - 2 * ρ) (x + 2 * ρ))
        (deriv (fun z : ℝ => hiaiRegularization φ ε f z)) :=
    hiaiRegularization_deriv_convexOn_localAt_of_C3SmoothHiai
      smoothHiai (φ := φ) (f := f) hφ hεpos hR
      (by linarith) (by linarith) hpos
  simpa [Real.ball_eq_Ioo] using hconvIoo

/--
Public scalar monotonicity bounds the endpoint oscillation of the Hiai
regularization by the oscillation of the original function on a slightly larger
interval.
-/
theorem hiaiRegularization_endpointOscillation_le_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    {ε η a b : ℝ} (hab : a ≤ b) (hε_nonneg : 0 ≤ ε) (hεη : ε ≤ η)
    (hleft : (-1 : ℝ) < a - η) (hright : b + η < 1) :
    |hiaiRegularization φ ε f b -
      hiaiRegularization φ ε f a| ≤
        f (b + η) - f (a - η) := by
  have hη_nonneg : 0 ≤ η := le_trans hε_nonneg hεη
  have hmono := scalarMonotoneOn_Ioo_of_loewnerPosOnUnitInterval hpos
  have ha_reg : a ∈ hiaiRegularizedInterior ε := by
    dsimp [hiaiRegularizedInterior]
    constructor
    · linarith
    · linarith
  have hb_reg : b ∈ hiaiRegularizedInterior ε := by
    dsimp [hiaiRegularizedInterior]
    constructor
    · linarith
    · linarith
  have haη_mem : a - η ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · exact hleft
    · linarith
  have hbη_mem : b + η ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · linarith
    · exact hright
  let C : ℝ := f (b + η) - f (a - η)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact sub_nonneg.mpr (hmono haη_mem hbη_mem (by linarith))
  have ha_int :
      IntervalIntegrable (fun t : ℝ => φ t * f (a - ε * t))
        volume (-1 : ℝ) 1 :=
    hiaiRegularization_value_intervalIntegrable_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hε_nonneg ha_reg hpos
  have hb_int :
      IntervalIntegrable (fun t : ℝ => φ t * f (b - ε * t))
        volume (-1 : ℝ) 1 :=
    hiaiRegularization_value_intervalIntegrable_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hε_nonneg hb_reg hpos
  have hdiff_int :
      IntervalIntegrable
        (fun t : ℝ => φ t * (f (b - ε * t) - f (a - ε * t)))
        volume (-1 : ℝ) 1 := by
    simpa [mul_sub] using hb_int.sub ha_int
  have hφ_int : IntervalIntegrable φ volume (-1 : ℝ) 1 :=
    hφ.smooth.continuous.intervalIntegrable (-1 : ℝ) 1
  have hφC_int :
      IntervalIntegrable (fun t : ℝ => φ t * C) volume (-1 : ℝ) 1 :=
    hφ_int.mul_const C
  have hdiff_eq :
      hiaiRegularization φ ε f b -
        hiaiRegularization φ ε f a =
          ∫ t in (-1 : ℝ)..1,
            φ t * (f (b - ε * t) - f (a - ε * t)) := by
    unfold hiaiRegularization
    rw [← intervalIntegral.integral_sub hb_int ha_int]
    refine intervalIntegral.integral_congr ?_
    intro t _ht
    ring
  have hpoint_nonneg :
      ∀ t ∈ Set.Icc (-1 : ℝ) 1,
        0 ≤ φ t * (f (b - ε * t) - f (a - ε * t)) := by
    intro t ht
    have ha_shift_mem :
        a - ε * t ∈ Set.Ioo (-1 : ℝ) 1 :=
      hiaiRegularization_shift_mem_Ioo hε_nonneg ha_reg ht
    have hb_shift_mem :
        b - ε * t ∈ Set.Ioo (-1 : ℝ) 1 :=
      hiaiRegularization_shift_mem_Ioo hε_nonneg hb_reg ht
    have hshift_le : a - ε * t ≤ b - ε * t := by linarith
    exact mul_nonneg (hφ.nonneg t)
      (sub_nonneg.mpr (hmono ha_shift_mem hb_shift_mem hshift_le))
  have hpoint_le_C :
      ∀ t ∈ Set.Icc (-1 : ℝ) 1,
        φ t * (f (b - ε * t) - f (a - ε * t)) ≤ φ t * C := by
    intro t ht
    have ha_shift_mem :
        a - ε * t ∈ Set.Ioo (-1 : ℝ) 1 :=
      hiaiRegularization_shift_mem_Ioo hε_nonneg ha_reg ht
    have hb_shift_mem :
        b - ε * t ∈ Set.Ioo (-1 : ℝ) 1 :=
      hiaiRegularization_shift_mem_Ioo hε_nonneg hb_reg ht
    have hεt_le_ε : ε * t ≤ ε := by
      have h := mul_le_mul_of_nonneg_left ht.2 hε_nonneg
      simpa using h
    have hεt_le_η : ε * t ≤ η := le_trans hεt_le_ε hεη
    have hnegε_le_εt : -ε ≤ ε * t := by
      have h := mul_le_mul_of_nonneg_left ht.1 hε_nonneg
      linarith
    have haη_le_shift : a - η ≤ a - ε * t := by linarith
    have hshift_le_bη : b - ε * t ≤ b + η := by linarith
    have hfa_low : f (a - η) ≤ f (a - ε * t) :=
      hmono haη_mem ha_shift_mem haη_le_shift
    have hfb_high : f (b - ε * t) ≤ f (b + η) :=
      hmono hb_shift_mem hbη_mem hshift_le_bη
    have hdiff_le : f (b - ε * t) - f (a - ε * t) ≤ C := by
      dsimp [C]
      linarith
    exact mul_le_mul_of_nonneg_left hdiff_le (hφ.nonneg t)
  have hnonneg_int :
      0 ≤ ∫ t in (-1 : ℝ)..1,
        φ t * (f (b - ε * t) - f (a - ε * t)) :=
    intervalIntegral.integral_nonneg (μ := volume)
      (a := (-1 : ℝ)) (b := 1) (by norm_num) hpoint_nonneg
  have hupper_int :
      (∫ t in (-1 : ℝ)..1,
        φ t * (f (b - ε * t) - f (a - ε * t))) ≤
          ∫ t in (-1 : ℝ)..1, φ t * C :=
    intervalIntegral.integral_mono_on (μ := volume)
      (a := (-1 : ℝ)) (b := 1)
      (f := fun t : ℝ => φ t * (f (b - ε * t) - f (a - ε * t)))
      (g := fun t : ℝ => φ t * C)
      (by norm_num) hdiff_int hφC_int hpoint_le_C
  have hupper_C :
      (∫ t in (-1 : ℝ)..1, φ t * C) = C := by
    rw [intervalIntegral.integral_mul_const, hφ.integral_eq_one, one_mul]
  calc
    |hiaiRegularization φ ε f b -
        hiaiRegularization φ ε f a|
        = |∫ t in (-1 : ℝ)..1,
            φ t * (f (b - ε * t) - f (a - ε * t))| := by
          rw [hdiff_eq]
    _ = ∫ t in (-1 : ℝ)..1,
            φ t * (f (b - ε * t) - f (a - ε * t)) :=
          abs_of_nonneg hnonneg_int
    _ ≤ ∫ t in (-1 : ℝ)..1, φ t * C := hupper_int
    _ = f (b + η) - f (a - η) := hupper_C

/--
The endpoint oscillation input required by the derivative absolute-value
producer is supplied by public scalar monotonicity of the original function.
-/
theorem regularized_endpointOscillation_eventual_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ ρ A : ℝ, 0 < ρ ∧ 0 ≤ A ∧
        (-1 : ℝ) < x - 2 * ρ ∧ x + 2 * ρ < 1 ∧
        (∀ᶠ ε in 𝓝[>] (0 : ℝ),
          |hiaiRegularization φ ε f (x + 2 * ρ) -
            hiaiRegularization φ ε f (x - 2 * ρ)| ≤ A) := by
  intro x hx
  let m : ℝ := min (x + 1) (1 - x)
  let ρ : ℝ := m / 4
  let A : ℝ := f (x + 3 * ρ) - f (x - 3 * ρ)
  have hx_left_pos : 0 < x + 1 := by linarith [hx.1]
  have hx_right_pos : 0 < 1 - x := by linarith [hx.2]
  have hm_pos : 0 < m := by
    dsimp [m]
    exact lt_min hx_left_pos hx_right_pos
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hm_le_left : m ≤ x + 1 := min_le_left (x + 1) (1 - x)
  have hm_le_right : m ≤ 1 - x := min_le_right (x + 1) (1 - x)
  have hleft3 : (-1 : ℝ) < x - 3 * ρ := by
    dsimp [ρ]
    nlinarith
  have hright3 : x + 3 * ρ < 1 := by
    dsimp [ρ]
    nlinarith
  have hleft2 : (-1 : ℝ) < x - 2 * ρ := by
    nlinarith [hleft3, hρ]
  have hright2 : x + 2 * ρ < 1 := by
    nlinarith [hright3, hρ]
  have hmono := scalarMonotoneOn_Ioo_of_loewnerPosOnUnitInterval hpos
  have hmem_left3 : x - 3 * ρ ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · exact hleft3
    · nlinarith [hright3, hρ]
  have hmem_right3 : x + 3 * ρ ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · nlinarith [hleft3, hρ]
    · exact hright3
  have hA : 0 ≤ A := by
    dsimp [A]
    exact sub_nonneg.mpr (hmono hmem_left3 hmem_right3 (by nlinarith [hρ]))
  refine ⟨ρ, A, hρ, hA, hleft2, hright2, ?_⟩
  have hε_ltρ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ρ :=
    nhdsWithin_le_nhds (Iio_mem_nhds hρ)
  filter_upwards [self_mem_nhdsWithin, hε_ltρ] with ε hεpos hερ
  have hosc :
      |hiaiRegularization φ ε f (x + 2 * ρ) -
        hiaiRegularization φ ε f (x - 2 * ρ)| ≤
          f ((x + 2 * ρ) + ρ) - f ((x - 2 * ρ) - ρ) :=
    hiaiRegularization_endpointOscillation_le_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hpos
      (a := x - 2 * ρ) (b := x + 2 * ρ) (ε := ε) (η := ρ)
      (by nlinarith [hρ]) hεpos.le (le_of_lt hερ)
      (by nlinarith [hleft3]) (by nlinarith [hright3])
  dsimp [A]
  convert hosc using 2 <;> ring_nf

/--
Endpoint oscillation is now closed from public monotonicity, so the conditional
smooth-Hiai route supplies the eventual `LipschitzOnWith` data with only the
smooth Hiai theorem parameter left as a convexity source.
-/
theorem regularized_deriv_eventual_lipschitzOnWith_of_C3SmoothHiai
    (smoothHiai :
      ∀ {g : ℝ → ℝ}, LoewnerPosOnUnitInterval g →
        ContDiffOn ℝ 3 g (Set.Ioo (-1 : ℝ) 1) →
          ConvexOn ℝ (Set.Ioo (-1 : ℝ) 1) (deriv g))
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ K : ℝ≥0, ∃ U ∈ 𝓝 x, x ∈ U ∧
        ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          LipschitzOnWith K
            (fun y : ℝ =>
              deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)
            U :=
  regularized_deriv_eventual_lipschitzOnWith_of_C3SmoothHiai_endpointOscillation
    smoothHiai (φ := φ) (f := f) hφ hpos
    (regularized_endpointOscillation_eventual_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hpos)

/--
Conditional smooth-Hiai handoff after closing the endpoint oscillation input.
Only pointwise convergence of the regularized derivatives is explicit here; it
is supplied by `regularized_deriv_tendsto_of_loewnerPosOnUnitInterval`
(`RegularizationConvolution.lean`) in `deriv_continuousOn_of_C3SmoothHiai` below.
-/
theorem deriv_continuousOn_of_C3SmoothHiai_pointwiseLimitData
    (smoothHiai :
      ∀ {g : ℝ → ℝ}, LoewnerPosOnUnitInterval g →
        ContDiffOn ℝ 3 g (Set.Ioo (-1 : ℝ) 1) →
          ConvexOn ℝ (Set.Ioo (-1 : ℝ) 1) (deriv g))
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (hpoint :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (fun z : ℝ => hiaiRegularization φ ε f z) x)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv f x))) :
    ContinuousOn (deriv f) (Set.Ioo (-1 : ℝ) 1) :=
  deriv_continuousOn_of_regularized_deriv_tendsto_and_lipschitzOnWith
    (φ := φ) (f := f) hpoint
    (regularized_deriv_eventual_lipschitzOnWith_of_C3SmoothHiai
      smoothHiai (φ := φ) (f := f) hφ hpos)

/--
Smooth-Hiai handoff after the pointwise derivative convergence and endpoint
oscillation inputs have both been discharged from public Löwner positivity.
The smooth Hiai `C³` theorem body is the only explicit upstream input; it is
`smoothHiai_C3_deriv_convexOn_of_loewnerPosOnUnitInterval`
(`RegularizedSecondDerivativeLimit.lean`), used in
`deriv_continuousOn_of_loewnerPosOnUnitInterval_of_hiaiMollifier`.
-/
theorem deriv_continuousOn_of_C3SmoothHiai
    (smoothHiai :
      ∀ {g : ℝ → ℝ}, LoewnerPosOnUnitInterval g →
        ContDiffOn ℝ 3 g (Set.Ioo (-1 : ℝ) 1) →
          ConvexOn ℝ (Set.Ioo (-1 : ℝ) 1) (deriv g))
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    ContinuousOn (deriv f) (Set.Ioo (-1 : ℝ) 1) :=
  deriv_continuousOn_of_C3SmoothHiai_pointwiseLimitData
    smoothHiai (φ := φ) (f := f) hφ hpos
    (regularized_deriv_tendsto_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hpos)
end

end Quantum.TraceInequality.Loewner
