import Quantum.Analysis.Calculus.UniformCauchy
import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.SecondDerivativeLimitCore


/-!
# Chapter 20 second-derivative local-uniform Cauchy limit

This file contains the canonical second-derivative limit and the final
local uniform-Cauchy handoff to public C2 regularity.
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
Canonical pointwise candidate for the ordinary second derivatives of the Hiai
regularizations.  The next C² pilot layer proves that this `limUnder` candidate
is the actual continuous pointwise limit from local uniform-Cauchy data.
-/
noncomputable def hiaiRegularizationSecondDerivLimit
    (φ f : ℝ → ℝ) (y : ℝ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ))
    (fun ε : ℝ =>
      deriv (deriv
        (fun z : ℝ => hiaiRegularization φ ε f z)) y)

/--
If the second derivatives are Cauchy along the positive-ε filter at one point,
then they converge to the canonical `limUnder` value at that point.
-/
theorem hiaiRegularization_secondDerivLimit_tendsto_of_pointwise_cauchy
    {φ f : ℝ → ℝ} {y : ℝ}
    (hcauchy :
      Cauchy
        (Filter.map
          (fun ε : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          (𝓝[>] (0 : ℝ)))) :
    Filter.Tendsto
      (fun ε : ℝ =>
        deriv (deriv
          (fun z : ℝ => hiaiRegularization φ ε f z)) y)
      (𝓝[>] (0 : ℝ))
      (𝓝 (hiaiRegularizationSecondDerivLimit φ f y)) := by
  have hlim :
      ∃ L : ℝ,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          (𝓝[>] (0 : ℝ)) (𝓝 L) :=
    cauchy_map_iff_exists_tendsto.mp hcauchy
  simpa [hiaiRegularizationSecondDerivLimit] using
    (tendsto_nhds_limUnder hlim)

/--
On a fixed ball compactly inside the normalized interval, the ordinary second
derivatives of the Hiai regularizations are eventually continuous on the ball.
-/
theorem hiaiRegularization_secondDeriv_continuousOn_eventually_on_ball
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    {x r : ℝ} (_hr : 0 < r)
    (hleft : (-1 : ℝ) < x - r) (hright : x + r < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ContinuousOn
        (fun y : ℝ =>
          deriv (deriv
            (fun z : ℝ => hiaiRegularization φ ε f z)) y)
        (Metric.ball x r) := by
  have hderiv :=
    hiaiRegularization_secondDeriv_hasDerivAt_eventually_on_ball
      (φ := φ) (f := f) hφ hpos hleft hright
  filter_upwards [hderiv] with ε hε
  intro y hy
  exact (hε y hy).continuousAt.continuousWithinAt

/--
Local uniform-Cauchy control produces the continuous pointwise limit data
required by the PSD diagonal C² wrapper, with the limit fixed canonically by
`hiaiRegularizationSecondDerivLimit`.
-/
theorem hiaiRegularization_secondDerivLimitData_of_eventual_local_uniformCauchy
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (hCauchy :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ r : ℝ, 0 < r ∧ (-1 : ℝ) < x - r ∧ x + r < 1 ∧
          ∀ η > 0, ∀ y ∈ Metric.ball x r,
            ∃ U ∈ 𝓝[Metric.ball x r] y,
              ∀ᶠ ε in 𝓝[>] (0 : ℝ),
                ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ z ∈ U,
                  dist
                    (deriv (deriv
                      (fun w : ℝ =>
                        hiaiRegularization φ ε f w)) z)
                    (deriv (deriv
                      (fun w : ℝ =>
                        hiaiRegularization φ δ f w)) z) < η) :
    ∃ G : ℝ → ℝ,
      ContinuousOn G (Set.Ioo (-1 : ℝ) 1) ∧
        ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
          Filter.Tendsto
            (fun ε : ℝ =>
              deriv (deriv
                (fun z : ℝ => hiaiRegularization φ ε f z)) y)
            (𝓝[>] (0 : ℝ)) (𝓝 (G y)) := by
  let G : ℝ → ℝ := hiaiRegularizationSecondDerivLimit φ f
  have hpoint :
      ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          (𝓝[>] (0 : ℝ)) (𝓝 (G y)) := by
    intro y hy
    rcases hCauchy y hy with ⟨r, hr, _hleft, _hright, huc⟩
    have hyball : y ∈ Metric.ball y r := Metric.mem_ball_self hr
    have hcauchy :
        Cauchy
          (Filter.map
            (fun ε : ℝ =>
              deriv (deriv
                (fun z : ℝ => hiaiRegularization φ ε f z)) y)
            (𝓝[>] (0 : ℝ))) :=
      pointwise_cauchy_of_eventual_local_uniformCauchy
        (F := fun ε z : ℝ =>
          deriv (deriv
            (fun w : ℝ => hiaiRegularization φ ε f w)) z)
        (x := y) (r := r) (y := y) hyball huc
    simpa [G] using
      hiaiRegularization_secondDerivLimit_tendsto_of_pointwise_cauchy
        (φ := φ) (f := f) (y := y) hcauchy
  have hGcont : ContinuousOn G (Set.Ioo (-1 : ℝ) 1) := by
    refine continuousOn_of_locally_continuousOn ?_
    intro x hx
    rcases hCauchy x hx with ⟨r, hr, hleft, hright, huc⟩
    refine ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr, ?_⟩
    have hpointBall :
        ∀ y ∈ Metric.ball x r,
          Filter.Tendsto
            (fun ε : ℝ =>
              deriv (deriv
                (fun z : ℝ => hiaiRegularization φ ε f z)) y)
            (𝓝[>] (0 : ℝ)) (𝓝 (G y)) := by
      intro y hy
      have hyIoo : y ∈ Set.Ioo (-1 : ℝ) 1 := by
        have hyball : y ∈ Set.Ioo (x - r) (x + r) := by
          simpa [Real.ball_eq_Ioo] using hy
        constructor
        · exact lt_trans hleft hyball.1
        · exact lt_trans hyball.2 hright
      exact hpoint y hyIoo
    have hlocal :
        TendstoLocallyUniformlyOn
          (fun ε y : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          G (𝓝[>] (0 : ℝ)) (Metric.ball x r) :=
      regularized_secondDeriv_tendstoLocallyUniformlyOn_of_eventual_local_uniformCauchy
        (φ := φ) (f := f) (G := G) (x := x) (r := r) hpointBall huc
    have hcontEv :=
      hiaiRegularization_secondDeriv_continuousOn_eventually_on_ball
        (φ := φ) (f := f) hφ hpos hr hleft hright
    have hcontBall : ContinuousOn G (Metric.ball x r) :=
      hlocal.continuousOn hcontEv.frequently
    exact hcontBall.mono Set.inter_subset_right
  exact ⟨G, hGcont, hpoint⟩

/--
Public Löwner positivity supplies the local uniform-Cauchy estimate for the
ordinary second derivatives of the Hiai regularizations.  The proof uses the
closed `Rε' → f'` pointwise limit and the PSD diagonal source for local
third-derivative bounds; it does not use the pointwise `Rε''` limit data.
-/
theorem hiaiRegularization_secondDeriv_localUniformCauchy_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ r : ℝ, 0 < r ∧ (-1 : ℝ) < x - r ∧ x + r < 1 ∧
        ∀ η > 0, ∀ y ∈ Metric.ball x r,
          ∃ U ∈ 𝓝[Metric.ball x r] y,
            ∀ᶠ ε in 𝓝[>] (0 : ℝ),
              ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ z ∈ U,
                dist
                  (deriv (deriv
                    (fun w : ℝ =>
                      hiaiRegularization φ ε f w)) z)
                  (deriv (deriv
                    (fun w : ℝ =>
                      hiaiRegularization φ δ f w)) z) < η := by
  intro x hx
  rcases
    hiaiRegularization_confluentLoewnerHankel3_det_nonneg_eventually_local
      (φ := φ) (f := f) hφ hpos x hx with
    ⟨r, hr, hleft, hright, hHankel⟩
  have hball : Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro y hy
    have hyIoo : y ∈ Set.Ioo (x - r) (x + r) := by
      simpa [Real.ball_eq_Ioo] using hy
    constructor
    · exact lt_trans hleft hyIoo.1
    · exact lt_trans hyIoo.2 hright
  refine ⟨r, hr, hleft, hright, ?_⟩
  have hregDeriv :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
        HasDerivAt
          (fun z : ℝ =>
            deriv (fun w : ℝ => hiaiRegularization φ ε f w) z)
          (deriv (deriv
            (fun w : ℝ => hiaiRegularization φ ε f w)) y)
          y :=
    hiaiRegularization_deriv_hasDerivAt_eventually_on_ball
      (φ := φ) (f := f) hφ hpos hleft hright
  have hsecondDeriv :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
        HasDerivAt
          (fun z : ℝ =>
            deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w)) z)
          (deriv (deriv (deriv
            (fun w : ℝ => hiaiRegularization φ ε f w))) y)
          y :=
    hiaiRegularization_secondDeriv_hasDerivAt_eventually_on_ball
      (φ := φ) (f := f) hφ hpos hleft hright
  have hthirdBound :=
    hiaiRegularization_thirdDeriv_bound_eventually_local_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hpos x hx r hr hball hHankel
  intro η hη y hy
  rcases hthirdBound y hy with ⟨C, hC, ρ, hρ, hρsub, hthird⟩
  have hpoint :
      ∀ t ∈ Metric.ball y ρ,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (fun z : ℝ => hiaiRegularization φ ε f z) t)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv f t)) := by
    intro t ht
    exact
      regularized_deriv_tendsto_of_loewnerPosOnUnitInterval
        (φ := φ) (f := f) hφ hpos t (hball (hρsub ht))
  have hregSmall :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Metric.ball y ρ,
        HasDerivAt
          (fun z : ℝ =>
            deriv (fun w : ℝ => hiaiRegularization φ ε f w) z)
          (deriv (deriv
            (fun w : ℝ => hiaiRegularization φ ε f w)) t)
          t := by
    filter_upwards [hregDeriv] with ε hε
    intro t ht
    exact hε t (hρsub ht)
  have hLip :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        LipschitzOnWith (Real.toNNReal C)
          (fun t : ℝ =>
            deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w)) t)
          (Metric.ball y ρ) := by
    filter_upwards [hsecondDeriv, hthird] with ε hεDeriv hεBound
    refine (convex_ball y ρ).lipschitzOnWith_of_nnnorm_deriv_le ?_ ?_
    · intro z hz
      exact (hεDeriv z (hρsub hz)).differentiableAt
    · intro z hz
      have hderiv_eq :
          deriv
              (fun t : ℝ =>
                deriv (deriv
                  (fun w : ℝ => hiaiRegularization φ ε f w)) t) z =
            deriv (deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w))) z :=
        (hεDeriv z (hρsub hz)).deriv
      rw [← NNReal.coe_le_coe, Real.toNNReal_of_nonneg hC,
        coe_nnnorm, Real.norm_eq_abs, hderiv_eq]
      exact hεBound z hz
  rcases
    deriv_family_eventual_local_uniformCauchy_at_of_lipschitzOnWith
      (l := 𝓝[>] (0 : ℝ))
      (G := fun ε t : ℝ =>
        deriv (fun z : ℝ => hiaiRegularization φ ε f z) t)
      (F := fun ε t : ℝ =>
        deriv (deriv
          (fun w : ℝ => hiaiRegularization φ ε f w)) t)
      (g := deriv f) (y := y) (ρ := ρ) (K := C)
      hρ hC hpoint hregSmall hLip η hη with
    ⟨U, hU, hUCauchy⟩
  exact ⟨U, mem_nhdsWithin_of_mem_nhds hU, hUCauchy⟩

/--
No-input public C² pilot for the normalized interval.  This is the C² layer
consumed by the higher finite-order regularity ladder and final theorem
packaging.
-/
theorem publicC2Regularity_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    ContDiffOn ℝ 2 f (Set.Ioo (-1 : ℝ) 1) := by
  rcases exists_hiaiMollifier with ⟨φ, hφ⟩
  rcases
    hiaiRegularization_secondDerivLimitData_of_eventual_local_uniformCauchy
      (φ := φ) (f := f) hφ hpos
      (hiaiRegularization_secondDeriv_localUniformCauchy_of_loewnerPosOnUnitInterval
        (φ := φ) (f := f) hφ hpos) with
    ⟨G, hGcont, hsecondPoint⟩
  exact
    publicC2Regularity_of_regularized_secondDeriv_hankelPsdDiagonalLimitData_closedHpoint
      (φ := φ) (f := f) (G := G) hφ hpos hsecondPoint hGcont

/-- Public C² regularity, with the former existential second-limit input closed. -/
theorem publicC2Regularity_of_hankel_psdDiagonalLimitData_of_existsSecondDerivLimit
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    ContDiffOn ℝ 2 f (Set.Ioo (-1 : ℝ) 1) :=
  publicC2Regularity_of_loewnerPosOnUnitInterval hpos

/-- Public C² regularity, with the former Hiai second-limit input closed. -/
theorem publicC2Regularity_of_loewnerPos_of_hiaiSecondDerivLimitData
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    ContDiffOn ℝ 2 f (Set.Ioo (-1 : ℝ) 1) :=
  publicC2Regularity_of_loewnerPosOnUnitInterval hpos

/-- Public C² regularity, with the former local uniform-Cauchy input closed. -/
theorem
    publicC2Regularity_of_loewnerPosOnUnitInterval_of_hiaiSecondDerivLocalUniformCauchyData
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    ContDiffOn ℝ 2 f (Set.Ioo (-1 : ℝ) 1) :=
  publicC2Regularity_of_loewnerPosOnUnitInterval hpos



end

end Quantum.TraceInequality.Loewner
