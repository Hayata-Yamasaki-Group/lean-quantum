import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.SecondDerivativeLimit
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Chapter 20 third-derivative limit package

This file contains the C3 handoff and regularized third-derivative local
uniform limit package used by the finite-order regularity ladder.
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
Closed packaging from `C¹` regularity of the second derivative to the third
finite-order regularity step.
-/
theorem publicC3Regularity_of_secondDeriv_contDiffOn
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (hsecond : ContDiffOn ℝ 1 (deriv (deriv f)) (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ 3 f (Set.Ioo (-1 : ℝ) 1) := by
  have hC2 : ContDiffOn ℝ 2 f (Set.Ioo (-1 : ℝ) 1) :=
    publicC2Regularity_of_loewnerPosOnUnitInterval hpos
  have hderivC1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (-1 : ℝ) 1) := by
    simpa using hC2.deriv_of_isOpen (m := 1) isOpen_Ioo (by decide)
  have hderivC2 : ContDiffOn ℝ 2 (deriv f) (Set.Ioo (-1 : ℝ) 1) := by
    have h :
        ContDiffOn ℝ ((1 : WithTop ℕ∞) + 1) (deriv f)
          (Set.Ioo (-1 : ℝ) 1) := by
      rw [contDiffOn_succ_iff_deriv_of_isOpen
        (n := (1 : WithTop ℕ∞)) (f := deriv f) isOpen_Ioo]
      refine ⟨hderivC1.differentiableOn (by decide), ?_, hsecond⟩
      intro htop
      cases htop
    simpa using h
  have h :
      ContDiffOn ℝ ((2 : WithTop ℕ∞) + 1) f
        (Set.Ioo (-1 : ℝ) 1) := by
    rw [contDiffOn_succ_iff_deriv_of_isOpen
      (n := (2 : WithTop ℕ∞)) (f := f) isOpen_Ioo]
    refine ⟨hpos.differentiable, ?_, hderivC2⟩
    intro htop
    cases htop
  simpa using h

/--
On a fixed ball compactly inside the normalized interval, the ordinary third
derivatives of the Hiai regularizations are eventually differentiable.
-/
theorem hiaiRegularization_thirdDeriv_hasDerivAt_eventually_on_ball
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    {x r : ℝ}
    (hleft : (-1 : ℝ) < x - r) (hright : x + r < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
      HasDerivAt
        (fun z : ℝ =>
          deriv (deriv (deriv
            (fun w : ℝ => hiaiRegularization φ ε f w))) z)
        (deriv (deriv (deriv (deriv
          (fun w : ℝ => hiaiRegularization φ ε f w)))) y)
        y := by
  have hleftMargin : 0 < x - r + 1 := by linarith
  have hrightMargin : 0 < 1 - (x + r) := by linarith
  have hε_left : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < x - r + 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds hleftMargin)
  have hε_right : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 - (x + r) :=
    nhdsWithin_le_nhds (Iio_mem_nhds hrightMargin)
  filter_upwards [self_mem_nhdsWithin, hε_left, hε_right] with
    ε hεpos hεleft hεright
  intro y hy
  let R : ℝ → ℝ := fun w : ℝ => hiaiRegularization φ ε f w
  have hyIoo : y ∈ Set.Ioo (x - r) (x + r) := by
    simpa [Real.ball_eq_Ioo] using hy
  have hyreg : y ∈ hiaiRegularizedInterior ε := by
    dsimp [hiaiRegularizedInterior]
    constructor
    · linarith [hyIoo.1, hεleft]
    · linarith [hyIoo.2, hεright]
  have hopen : IsOpen (hiaiRegularizedInterior ε) := by
    simpa [hiaiRegularizedInterior] using isOpen_Ioo
  have hC5 :
      ContDiffOn ℝ 5 R (hiaiRegularizedInterior ε) := by
    dsimp [R]
    exact hiaiRegularization_contDiffOn_regularizedInterior_order5
      (φ := φ) (f := f) hφ hεpos hpos
  have hderivC4 :
      ContDiffOn ℝ 4 (deriv R) (hiaiRegularizedInterior ε) := by
    simpa using hC5.deriv_of_isOpen (m := 4) hopen (by decide)
  have hsecondC3 :
      ContDiffOn ℝ 3 (deriv (deriv R))
        (hiaiRegularizedInterior ε) := by
    simpa using hderivC4.deriv_of_isOpen (m := 3) hopen (by decide)
  have hthirdC2 :
      ContDiffOn ℝ 2 (deriv (deriv (deriv R)))
        (hiaiRegularizedInterior ε) := by
    simpa using hsecondC3.deriv_of_isOpen (m := 2) hopen (by decide)
  have hdiffWithin :
      DifferentiableWithinAt ℝ (deriv (deriv (deriv R)))
        (hiaiRegularizedInterior ε) y :=
    hthirdC2.differentiableOn (by decide) y hyreg
  have hdiffAt : DifferentiableAt ℝ (deriv (deriv (deriv R))) y :=
    hdiffWithin.differentiableAt (hopen.mem_nhds hyreg)
  simpa [R] using hdiffAt.hasDerivAt

/--
The closed `Rε''` local uniform-Cauchy producer identifies the canonical
second-derivative limit with the ordinary second derivative of `f`.
-/
theorem regularized_secondDeriv_tendsto_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      Filter.Tendsto
        (fun ε : ℝ =>
          deriv (deriv
            (fun z : ℝ => hiaiRegularization φ ε f z)) y)
        (𝓝[>] (0 : ℝ)) (𝓝 (deriv (deriv f) y)) := by
  intro y hy
  have hCauchy :=
    hiaiRegularization_secondDeriv_localUniformCauchy_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hpos
  rcases
    hiaiRegularization_secondDerivLimitData_of_eventual_local_uniformCauchy
      (φ := φ) (f := f) hφ hpos hCauchy with
    ⟨G, _hGcont, hGpoint⟩
  rcases hCauchy y hy with ⟨r, hr, hleft, hright, huc⟩
  have hball : Metric.ball y r ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro z hz
    have hzIoo : z ∈ Set.Ioo (y - r) (y + r) := by
      simpa [Real.ball_eq_Ioo] using hz
    constructor
    · exact lt_trans hleft hzIoo.1
    · exact lt_trans hzIoo.2 hright
  have hpointDeriv :
      ∀ z ∈ Metric.ball y r,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (fun w : ℝ => hiaiRegularization φ ε f w) z)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv f z)) := by
    intro z hz
    exact regularized_deriv_tendsto_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hpos z (hball hz)
  have hpointG :
      ∀ z ∈ Metric.ball y r,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w)) z)
          (𝓝[>] (0 : ℝ)) (𝓝 (G z)) := by
    intro z hz
    exact hGpoint z (hball hz)
  have hsecond :
      TendstoLocallyUniformlyOn
        (fun ε z : ℝ =>
          deriv (deriv
            (fun w : ℝ => hiaiRegularization φ ε f w)) z)
        G (𝓝[>] (0 : ℝ)) (Metric.ball y r) :=
    regularized_secondDeriv_tendstoLocallyUniformlyOn_of_eventual_local_uniformCauchy
      (φ := φ) (f := f) (G := G) (x := y) (r := r) hpointG huc
  have hreg :=
    hiaiRegularization_deriv_hasDerivAt_eventually_on_ball
      (φ := φ) (f := f) hφ hpos hleft hright
  have hhas :
      HasDerivAt (deriv f) (G y) y :=
    hasDerivAt_deriv_of_regularized_deriv_local_limit
      (φ := φ) (f := f) (G := G) (x := y) (r := r) hr
      hpointDeriv hsecond hreg
  have hderiv_eq : deriv (deriv f) y = G y := hhas.deriv
  simpa [hderiv_eq] using hGpoint y hy

/--
Local derivative-limit transfer for the C³ pilot.  If the regularized second
derivatives converge pointwise to `deriv (deriv f)` and their derivatives
converge locally uniformly, then the second derivative of `f` is differentiable
at the center.
-/
theorem hasDerivAt_secondDeriv_of_regularized_secondDeriv_local_limit
    {φ f H : ℝ → ℝ} {x r : ℝ} (hr : 0 < r)
    (hpoint :
      ∀ y ∈ Metric.ball x r,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv (deriv f) y)))
    (hthird :
      TendstoLocallyUniformlyOn
        (fun ε y : ℝ =>
          deriv (deriv (deriv
            (fun z : ℝ => hiaiRegularization φ ε f z))) y)
        H (𝓝[>] (0 : ℝ)) (Metric.ball x r))
    (hreg :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
        HasDerivAt
          (fun z : ℝ =>
            deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w)) z)
          (deriv (deriv (deriv
            (fun w : ℝ => hiaiRegularization φ ε f w))) y)
          y) :
    HasDerivAt (deriv (deriv f)) (H x) x :=
  hasDerivAt_of_tendstoLocallyUniformlyOn
    (f := fun ε y : ℝ =>
      deriv (deriv (fun z : ℝ => hiaiRegularization φ ε f z)) y)
    (g := deriv (deriv f))
    (f' := fun ε y : ℝ =>
      deriv (deriv (deriv
        (fun z : ℝ => hiaiRegularization φ ε f z))) y)
    (g' := H)
    (s := Metric.ball x r) (l := 𝓝[>] (0 : ℝ))
    Metric.isOpen_ball hthird hreg hpoint (Metric.mem_ball_self hr)

/--
Abstract C³-pilot handoff.  The analytic input is local uniform
convergence of the regularized third derivatives to a continuous limit `H`;
for the Hiai regularizations it comes from
`hiaiRegularization_thirdDeriv_localUniformCauchy_of_loewnerPosOnUnitInterval`
below (see `publicC3Regularity_of_loewnerPosOnUnitInterval`).
-/
theorem secondDeriv_contDiffOn_of_regularized_secondDeriv_local_tendstoLocallyUniformlyOn
    {φ f H : ℝ → ℝ}
    (hpoint :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) x)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv (deriv f) x)))
    (hlocal :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 ∧
          TendstoLocallyUniformlyOn
            (fun ε y : ℝ =>
              deriv (deriv (deriv
                (fun z : ℝ => hiaiRegularization φ ε f z))) y)
            H (𝓝[>] (0 : ℝ)) (Metric.ball x r) ∧
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
            HasDerivAt
              (fun z : ℝ =>
                deriv (deriv
                  (fun w : ℝ => hiaiRegularization φ ε f w)) z)
              (deriv (deriv (deriv
                (fun w : ℝ => hiaiRegularization φ ε f w))) y)
              y))
    (hHcont : ContinuousOn H (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ 1 (deriv (deriv f)) (Set.Ioo (-1 : ℝ) 1) := by
  have hdiff :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (deriv (deriv f)) (H x) x := by
    intro x hx
    rcases hlocal x hx with ⟨r, hr, hball_sub, hthird, hreg⟩
    exact
      hasDerivAt_secondDeriv_of_regularized_secondDeriv_local_limit
        (φ := φ) (f := f) (H := H) hr
        (by
          intro y hy
          exact hpoint y (hball_sub hy))
        hthird hreg
  have hdiffOn : DifferentiableOn ℝ (deriv (deriv f)) (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    exact (hdiff x hx).differentiableAt.differentiableWithinAt
  have hderiv_eq : Set.EqOn (deriv (deriv (deriv f))) H (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    exact (hdiff x hx).deriv
  have hderiv_cont :
      ContinuousOn (deriv (deriv (deriv f))) (Set.Ioo (-1 : ℝ) 1) :=
    hHcont.congr hderiv_eq
  have h :
      ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1)
        (deriv (deriv f)) (Set.Ioo (-1 : ℝ) 1) := by
    rw [contDiffOn_succ_iff_deriv_of_isOpen
      (n := (0 : WithTop ℕ∞)) (f := deriv (deriv f)) isOpen_Ioo]
    refine ⟨hdiffOn, ?_, ?_⟩
    · intro htop
      cases htop
    · exact contDiffOn_zero.2 hderiv_cont
  simpa using h

/--
Conditional public C³ wrapper for the regularized third-derivative handoff.
-/
theorem publicC3Regularity_of_regularized_thirdDeriv_local_tendstoLocallyUniformlyOn
    {φ f H : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (hpoint :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) x)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv (deriv f) x)))
    (hlocal :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 ∧
          TendstoLocallyUniformlyOn
            (fun ε y : ℝ =>
              deriv (deriv (deriv
                (fun z : ℝ => hiaiRegularization φ ε f z))) y)
            H (𝓝[>] (0 : ℝ)) (Metric.ball x r) ∧
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
            HasDerivAt
              (fun z : ℝ =>
                deriv (deriv
                  (fun w : ℝ => hiaiRegularization φ ε f w)) z)
              (deriv (deriv (deriv
                (fun w : ℝ => hiaiRegularization φ ε f w))) y)
              y))
    (hHcont : ContinuousOn H (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ 3 f (Set.Ioo (-1 : ℝ) 1) :=
  publicC3Regularity_of_secondDeriv_contDiffOn hpos
    (secondDeriv_contDiffOn_of_regularized_secondDeriv_local_tendstoLocallyUniformlyOn
      (φ := φ) (f := f) (H := H) hpoint hlocal hHcont)

/--
The PSD diagonal signs plus local third-derivative bounds give the local
fourth-derivative bound needed to make `Rε'''` locally Lipschitz.
-/
theorem hiaiRegularization_fourthDeriv_bound_eventually_local_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ∀ r : ℝ,
      0 < r → Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 →
        ∀ y ∈ Metric.ball x r, ∃ C : ℝ, 0 ≤ C ∧
          ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball y ρ ⊆ Metric.ball x r ∧
            ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ Metric.ball y ρ,
              |deriv (deriv (deriv (deriv
                (fun w : ℝ => hiaiRegularization φ ε f w)))) z| ≤ C := by
  intro x _hx r _hr hball y hy
  have hyIoo : y ∈ Set.Ioo (-1 : ℝ) 1 := hball hy
  rcases
    hiaiRegularization_confluentLoewnerHankel3_posSemidef_eventually_local
      (φ := φ) (f := f) hφ hpos y hyIoo with
    ⟨θ, hθ, hθleft, hθright, hpsdθ⟩
  have hballθ : Metric.ball y θ ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro z hz
    have hzIoo : z ∈ Set.Ioo (y - θ) (y + θ) := by
      simpa [Real.ball_eq_Ioo] using hz
    constructor
    · exact lt_trans hθleft hzIoo.1
    · exact lt_trans hzIoo.2 hθright
  have hdetθ :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ Metric.ball y θ,
        0 ≤
          (confluentLoewnerHankel3
            (fun w : ℝ => hiaiRegularization φ ε f w) z).det := by
    filter_upwards [hpsdθ] with ε hε
    intro z hz
    exact Matrix.PosSemidef.det_nonneg (hε z hz)
  have hthirdLocal :=
    hiaiRegularization_thirdDeriv_bound_eventually_local_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hpos y hyIoo θ hθ hballθ hdetθ
  have hyBallIoo : y ∈ Set.Ioo (x - r) (x + r) := by
    simpa [Real.ball_eq_Ioo] using hy
  let τ : ℝ := min (y - (x - r)) (x + r - y)
  have hτ : 0 < τ := by
    dsimp [τ]
    exact lt_min (by linarith [hyBallIoo.1]) (by linarith [hyBallIoo.2])
  let ρ : ℝ := min (θ / 8) (τ / 8)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by positivity) (by positivity)
  have hρ_le_θ_eighth : ρ ≤ θ / 8 := by
    dsimp [ρ]
    exact min_le_left _ _
  have hρ_le_τ_eighth : ρ ≤ τ / 8 := by
    dsimp [ρ]
    exact min_le_right _ _
  have h4ρ_lt_θ : 4 * ρ < θ := by nlinarith [hρ_le_θ_eighth, hθ]
  have h2ρ_lt_θ : 2 * ρ < θ := by nlinarith [hρ_le_θ_eighth, hθ]
  have h2ρ_lt_τ : 2 * ρ < τ := by nlinarith [hρ_le_τ_eighth, hτ]
  have hτ_le_left : τ ≤ y - (x - r) := by
    dsimp [τ]
    exact min_le_left _ _
  have hτ_le_right : τ ≤ x + r - y := by
    dsimp [τ]
    exact min_le_right _ _
  have h2ρ_lt_left : 2 * ρ < y - (x - r) :=
    lt_of_lt_of_le h2ρ_lt_τ hτ_le_left
  have h2ρ_lt_right : 2 * ρ < x + r - y :=
    lt_of_lt_of_le h2ρ_lt_τ hτ_le_right
  let a : ℝ := y - 2 * ρ
  let b : ℝ := y + 2 * ρ
  have haθ : a ∈ Metric.ball y θ := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [a]
    rw [abs_of_nonpos (by linarith : y - 2 * ρ - y ≤ 0)]
    linarith
  have hbθ : b ∈ Metric.ball y θ := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [b]
    rw [abs_of_nonneg (by linarith : 0 ≤ y + 2 * ρ - y)]
    linarith
  rcases hthirdLocal a haθ with ⟨Ca, hCa, σa, hσa, _hσaSub, hbounda⟩
  rcases hthirdLocal b hbθ with ⟨Cb, hCb, σb, hσb, _hσbSub, hboundb⟩
  let B : ℝ := max Ca Cb
  have hB : 0 ≤ B := by
    dsimp [B]
    exact le_max_of_le_left hCa
  have hboundA :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        deriv (deriv (deriv
          (fun w : ℝ => hiaiRegularization φ ε f w))) a ≤ B := by
    filter_upwards [hbounda] with ε hε
    have ha_self : a ∈ Metric.ball a σa := Metric.mem_ball_self hσa
    have habs := hε a ha_self
    calc
      deriv (deriv (deriv
          (fun w : ℝ => hiaiRegularization φ ε f w))) a
          ≤ |deriv (deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w))) a| := le_abs_self _
      _ ≤ Ca := habs
      _ ≤ B := by dsimp [B]; exact le_max_left _ _
  have hboundB :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        deriv (deriv (deriv
          (fun w : ℝ => hiaiRegularization φ ε f w))) b ≤ B := by
    filter_upwards [hboundb] with ε hε
    have hb_self : b ∈ Metric.ball b σb := Metric.mem_ball_self hσb
    have habs := hε b hb_self
    calc
      deriv (deriv (deriv
          (fun w : ℝ => hiaiRegularization φ ε f w))) b
          ≤ |deriv (deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w))) b| := le_abs_self _
      _ ≤ Cb := habs
      _ ≤ B := by dsimp [B]; exact le_max_right _ _
  have hρsub : Metric.ball y ρ ⊆ Metric.ball x r := by
    intro z hz
    have hzIoo : z ∈ Set.Ioo (y - ρ) (y + ρ) := by
      simpa [Real.ball_eq_Ioo] using hz
    have hzBallIoo : z ∈ Set.Ioo (x - r) (x + r) := by
      constructor <;> linarith [hzIoo.1, hzIoo.2, h2ρ_lt_left, h2ρ_lt_right, hρ]
    simpa [Real.ball_eq_Ioo] using hzBallIoo
  refine ⟨B / ρ, by positivity, ρ, hρ, hρsub, ?_⟩
  have hleftMargin : 0 < y - θ + 1 := by linarith [hθleft]
  have hrightMargin : 0 < 1 - (y + θ) := by linarith [hθright]
  have hε_left : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < y - θ + 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds hleftMargin)
  have hε_right : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 - (y + θ) :=
    nhdsWithin_le_nhds (Iio_mem_nhds hrightMargin)
  filter_upwards [self_mem_nhdsWithin, hε_left, hε_right, hpsdθ, hboundA, hboundB] with
    ε hεpos hεleft hεright hpsdε hAε hBε
  intro z hz
  let R : ℝ → ℝ := fun w : ℝ => hiaiRegularization φ ε f w
  let Fε : ℝ → ℝ := fun w : ℝ => deriv (deriv (deriv R)) w
  have hball4_sub_θ : Metric.ball y (4 * ρ) ⊆ Metric.ball y θ := by
    intro w hw
    exact Metric.mem_ball.mpr <|
      lt_of_lt_of_le (Metric.mem_ball.mp hw) (le_of_lt h4ρ_lt_θ)
  have hball4_reg :
      Metric.ball y (4 * ρ) ⊆ hiaiRegularizedInterior ε := by
    intro w hw
    have hwθ : w ∈ Metric.ball y θ := hball4_sub_θ hw
    have hwIoo : w ∈ Set.Ioo (y - θ) (y + θ) := by
      simpa [Real.ball_eq_Ioo] using hwθ
    dsimp [hiaiRegularizedInterior]
    constructor
    · linarith [hwIoo.1, hεleft]
    · linarith [hwIoo.2, hεright]
  have hopen : IsOpen (hiaiRegularizedInterior ε) := by
    simpa [hiaiRegularizedInterior] using isOpen_Ioo
  have hC5 :
      ContDiffOn ℝ 5 R (hiaiRegularizedInterior ε) := by
    dsimp [R]
    exact hiaiRegularization_contDiffOn_regularizedInterior_order5
      (φ := φ) (f := f) hφ hεpos hpos
  have hderivC4 :
      ContDiffOn ℝ 4 (deriv R) (hiaiRegularizedInterior ε) := by
    simpa using hC5.deriv_of_isOpen (m := 4) hopen (by decide)
  have hsecondC3 :
      ContDiffOn ℝ 3 (deriv (deriv R))
        (hiaiRegularizedInterior ε) := by
    simpa using hderivC4.deriv_of_isOpen (m := 3) hopen (by decide)
  have hthirdC2 :
      ContDiffOn ℝ 2 Fε (hiaiRegularizedInterior ε) := by
    dsimp [Fε]
    simpa using hsecondC3.deriv_of_isOpen (m := 2) hopen (by decide)
  have hthirdC2_ball :
      ContDiffOn ℝ 2 Fε (Metric.ball y (4 * ρ)) :=
    hthirdC2.mono hball4_reg
  have hfourthC1 :
      ContDiffOn ℝ 1 (deriv Fε) (hiaiRegularizedInterior ε) := by
    simpa using hthirdC2.deriv_of_isOpen (m := 1) hopen (by decide)
  have hfourthC1_ball :
      ContDiffOn ℝ 1 (deriv Fε) (Metric.ball y (4 * ρ)) :=
    hfourthC1.mono hball4_reg
  have hconv : ConvexOn ℝ (Metric.ball y (4 * ρ)) Fε := by
    refine
      convexOn_of_deriv2_nonneg' (convex_ball y (4 * ρ))
        (hthirdC2_ball.differentiableOn (by decide))
        (hfourthC1_ball.differentiableOn (by decide)) ?_
    intro w hw
    have hwθ : w ∈ Metric.ball y θ := hball4_sub_θ hw
    have hdiag :=
      (hpsdε w hwθ).diag_nonneg (i := (2 : Fin 3))
    have hentry :
        0 ≤ deriv (deriv (deriv (deriv (deriv R)))) w / 120 := by
      dsimp [R]
      simpa [confluentLoewnerHankel3_apply_two_two] using hdiag
    have hfive : 0 ≤ deriv (deriv (deriv (deriv (deriv R)))) w := by
      nlinarith
    simpa [Fε, Function.iterate_succ_apply] using hfive
  have hdiff : ∀ w ∈ Metric.ball y (4 * ρ), DifferentiableAt ℝ Fε w := by
    intro w hw
    exact (hthirdC2_ball.differentiableOn (by decide) w hw).differentiableAt
      (Metric.isOpen_ball.mem_nhds hw)
  have hnonneg : ∀ w ∈ Metric.ball y (4 * ρ), 0 ≤ Fε w := by
    intro w hw
    have hwθ : w ∈ Metric.ball y θ := hball4_sub_θ hw
    have hdiag :=
      (hpsdε w hwθ).diag_nonneg (i := (1 : Fin 3))
    have hentry :
        0 ≤ deriv (deriv (deriv R)) w / 6 := by
      dsimp [R]
      simpa [confluentLoewnerHankel3_apply_one_one] using hdiag
    dsimp [Fε]
    nlinarith
  have hinner :=
    convex_nonneg_abs_deriv_le_on_inner_ball_of_endpoint_le
      (F := Fε) (x := y) (ρ := ρ) (M := B)
      hρ hB hconv hdiff hnonneg (by simpa [Fε, R, a] using hAε)
      (by simpa [Fε, R, b] using hBε) z hz
  simpa [Fε, R] using hinner

/--
Public Löwner positivity supplies the local uniform-Cauchy estimate for the
ordinary third derivatives of the Hiai regularizations.
-/
theorem hiaiRegularization_thirdDeriv_localUniformCauchy_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ r : ℝ, 0 < r ∧ (-1 : ℝ) < x - r ∧ x + r < 1 ∧
        ∀ η > 0, ∀ y ∈ Metric.ball x r,
          ∃ U ∈ 𝓝[Metric.ball x r] y,
            ∀ᶠ ε in 𝓝[>] (0 : ℝ),
              ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ z ∈ U,
                dist
                  (deriv (deriv (deriv
                    (fun w : ℝ =>
                      hiaiRegularization φ ε f w))) z)
                  (deriv (deriv (deriv
                    (fun w : ℝ =>
                      hiaiRegularization φ δ f w))) z) < η := by
  intro x hx
  rcases
    hiaiRegularization_confluentLoewnerHankel3_det_nonneg_eventually_local
      (φ := φ) (f := f) hφ hpos x hx with
    ⟨r, hr, hleft, hright, _hHankel⟩
  have hball : Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro y hy
    have hyIoo : y ∈ Set.Ioo (x - r) (x + r) := by
      simpa [Real.ball_eq_Ioo] using hy
    constructor
    · exact lt_trans hleft hyIoo.1
    · exact lt_trans hyIoo.2 hright
  refine ⟨r, hr, hleft, hright, ?_⟩
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
  have hthirdDeriv :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
        HasDerivAt
          (fun z : ℝ =>
            deriv (deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w))) z)
          (deriv (deriv (deriv (deriv
            (fun w : ℝ => hiaiRegularization φ ε f w)))) y)
          y :=
    hiaiRegularization_thirdDeriv_hasDerivAt_eventually_on_ball
      (φ := φ) (f := f) hφ hpos hleft hright
  have hfourthBound :=
    hiaiRegularization_fourthDeriv_bound_eventually_local_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hpos x hx r hr hball
  intro η hη y hy
  rcases hfourthBound y hy with ⟨C, hC, ρ, hρ, hρsub, hfourth⟩
  have hpoint :
      ∀ t ∈ Metric.ball y ρ,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) t)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv (deriv f) t)) := by
    intro t ht
    exact
      regularized_secondDeriv_tendsto_of_loewnerPosOnUnitInterval
        (φ := φ) (f := f) hφ hpos t (hball (hρsub ht))
  have hregSmall :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Metric.ball y ρ,
        HasDerivAt
          (fun z : ℝ =>
            deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w)) z)
          (deriv (deriv (deriv
            (fun w : ℝ => hiaiRegularization φ ε f w))) t)
          t := by
    filter_upwards [hsecondDeriv] with ε hε
    intro t ht
    exact hε t (hρsub ht)
  have hLip :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        LipschitzOnWith (Real.toNNReal C)
          (fun t : ℝ =>
            deriv (deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w))) t)
          (Metric.ball y ρ) := by
    filter_upwards [hthirdDeriv, hfourth] with ε hεDeriv hεBound
    refine (convex_ball y ρ).lipschitzOnWith_of_nnnorm_deriv_le ?_ ?_
    · intro z hz
      exact (hεDeriv z (hρsub hz)).differentiableAt
    · intro z hz
      have hderiv_eq :
          deriv
              (fun t : ℝ =>
                deriv (deriv (deriv
                  (fun w : ℝ => hiaiRegularization φ ε f w))) t) z =
            deriv (deriv (deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w)))) z :=
        (hεDeriv z (hρsub hz)).deriv
      rw [← NNReal.coe_le_coe, Real.toNNReal_of_nonneg hC,
        coe_nnnorm, Real.norm_eq_abs, hderiv_eq]
      exact hεBound z hz
  rcases
    deriv_family_eventual_local_uniformCauchy_at_of_lipschitzOnWith
      (l := 𝓝[>] (0 : ℝ))
      (G := fun ε t : ℝ =>
        deriv (deriv
          (fun z : ℝ => hiaiRegularization φ ε f z)) t)
      (F := fun ε t : ℝ =>
        deriv (deriv (deriv
          (fun w : ℝ => hiaiRegularization φ ε f w))) t)
      (g := deriv (deriv f)) (y := y) (ρ := ρ) (K := C)
      hρ hC hpoint hregSmall hLip η hη with
    ⟨U, hU, hUCauchy⟩
  exact ⟨U, mem_nhdsWithin_of_mem_nhds hU, hUCauchy⟩

/-- Canonical pointwise candidate for the regularized third derivatives. -/
noncomputable def hiaiRegularizationThirdDerivLimit
    (φ f : ℝ → ℝ) (y : ℝ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ))
    (fun ε : ℝ =>
      deriv (deriv (deriv
        (fun z : ℝ => hiaiRegularization φ ε f z))) y)

/--
A pointwise Cauchy family of regularized third derivatives converges to its
canonical `limUnder` candidate.
-/
theorem hiaiRegularization_thirdDerivLimit_tendsto_of_pointwise_cauchy
    {φ f : ℝ → ℝ} {y : ℝ}
    (hcauchy :
      Cauchy
        (Filter.map
          (fun ε : ℝ =>
            deriv (deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z))) y)
          (𝓝[>] (0 : ℝ)))) :
    Filter.Tendsto
      (fun ε : ℝ =>
        deriv (deriv (deriv
          (fun z : ℝ => hiaiRegularization φ ε f z))) y)
      (𝓝[>] (0 : ℝ))
      (𝓝 (hiaiRegularizationThirdDerivLimit φ f y)) := by
  have hlim :
      ∃ L : ℝ,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z))) y)
          (𝓝[>] (0 : ℝ)) (𝓝 L) :=
    cauchy_map_iff_exists_tendsto.mp hcauchy
  simpa [hiaiRegularizationThirdDerivLimit] using
    (tendsto_nhds_limUnder hlim)

/--
Locally uniform convergence interface for the ordinary third derivatives of the
Hiai regularizations.
-/
theorem regularized_thirdDeriv_tendstoLocallyUniformlyOn_of_eventual_local_uniformCauchy
    {φ f H : ℝ → ℝ} {x r : ℝ}
    (hpoint :
      ∀ y ∈ Metric.ball x r,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z))) y)
          (𝓝[>] (0 : ℝ)) (𝓝 (H y)))
    (hcauchy :
      ∀ η > 0, ∀ y ∈ Metric.ball x r,
        ∃ U ∈ 𝓝[Metric.ball x r] y,
          ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ z ∈ U,
            dist
              (deriv (deriv (deriv
                (fun w : ℝ => hiaiRegularization φ ε f w))) z)
              (deriv (deriv (deriv
                (fun w : ℝ => hiaiRegularization φ δ f w))) z) < η) :
    TendstoLocallyUniformlyOn
      (fun ε y : ℝ =>
        deriv (deriv (deriv
          (fun z : ℝ => hiaiRegularization φ ε f z))) y)
      H (𝓝[>] (0 : ℝ)) (Metric.ball x r) :=
  tendstoLocallyUniformlyOn_of_eventual_local_uniformCauchy_and_pointwise
    (F := fun ε y : ℝ =>
      deriv (deriv (deriv
        (fun z : ℝ => hiaiRegularization φ ε f z))) y)
    (G := H) (s := Metric.ball x r) hpoint hcauchy

/--
On a fixed ball compactly inside the normalized interval, the ordinary third
derivatives of the Hiai regularizations are eventually continuous on the ball.
-/
theorem hiaiRegularization_thirdDeriv_continuousOn_eventually_on_ball
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    {x r : ℝ} (_hr : 0 < r)
    (hleft : (-1 : ℝ) < x - r) (hright : x + r < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ContinuousOn
        (fun y : ℝ =>
          deriv (deriv (deriv
            (fun z : ℝ => hiaiRegularization φ ε f z))) y)
        (Metric.ball x r) := by
  have hderiv :=
    hiaiRegularization_thirdDeriv_hasDerivAt_eventually_on_ball
      (φ := φ) (f := f) hφ hpos hleft hright
  filter_upwards [hderiv] with ε hε
  intro y hy
  exact (hε y hy).continuousAt.continuousWithinAt

/--
Local uniform-Cauchy control produces the continuous pointwise limit data
required by the C³ wrapper, with the limit fixed canonically by `limUnder`.
-/
theorem hiaiRegularization_thirdDerivLimitData_of_eventual_local_uniformCauchy
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
                    (deriv (deriv (deriv
                      (fun w : ℝ =>
                        hiaiRegularization φ ε f w))) z)
                    (deriv (deriv (deriv
                      (fun w : ℝ =>
                        hiaiRegularization φ δ f w))) z) < η) :
    ∃ H : ℝ → ℝ,
      ContinuousOn H (Set.Ioo (-1 : ℝ) 1) ∧
        ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
          Filter.Tendsto
            (fun ε : ℝ =>
              deriv (deriv (deriv
                (fun z : ℝ => hiaiRegularization φ ε f z))) y)
            (𝓝[>] (0 : ℝ)) (𝓝 (H y)) := by
  let H : ℝ → ℝ := hiaiRegularizationThirdDerivLimit φ f
  have hpoint :
      ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z))) y)
          (𝓝[>] (0 : ℝ)) (𝓝 (H y)) := by
    intro y hy
    rcases hCauchy y hy with ⟨r, hr, _hleft, _hright, huc⟩
    have hyball : y ∈ Metric.ball y r := Metric.mem_ball_self hr
    have hcauchy :
        Cauchy
          (Filter.map
            (fun ε : ℝ =>
              deriv (deriv (deriv
                (fun z : ℝ => hiaiRegularization φ ε f z))) y)
            (𝓝[>] (0 : ℝ))) :=
      pointwise_cauchy_of_eventual_local_uniformCauchy
        (F := fun ε z : ℝ =>
          deriv (deriv (deriv
            (fun w : ℝ => hiaiRegularization φ ε f w))) z)
        (x := y) (r := r) (y := y) hyball huc
    simpa [H] using
      hiaiRegularization_thirdDerivLimit_tendsto_of_pointwise_cauchy
        (φ := φ) (f := f) (y := y) hcauchy
  have hHcont : ContinuousOn H (Set.Ioo (-1 : ℝ) 1) := by
    refine continuousOn_of_locally_continuousOn ?_
    intro x hx
    rcases hCauchy x hx with ⟨r, hr, hleft, hright, huc⟩
    refine ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr, ?_⟩
    have hpointBall :
        ∀ y ∈ Metric.ball x r,
          Filter.Tendsto
            (fun ε : ℝ =>
              deriv (deriv (deriv
                (fun z : ℝ => hiaiRegularization φ ε f z))) y)
            (𝓝[>] (0 : ℝ)) (𝓝 (H y)) := by
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
            deriv (deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z))) y)
          H (𝓝[>] (0 : ℝ)) (Metric.ball x r) :=
      regularized_thirdDeriv_tendstoLocallyUniformlyOn_of_eventual_local_uniformCauchy
        (φ := φ) (f := f) (H := H) (x := x) (r := r) hpointBall huc
    have hcontEv :=
      hiaiRegularization_thirdDeriv_continuousOn_eventually_on_ball
        (φ := φ) (f := f) hφ hpos hr hleft hright
    have hcontBall : ContinuousOn H (Metric.ball x r) :=
      hlocal.continuousOn hcontEv.frequently
    exact hcontBall.mono Set.inter_subset_right
  exact ⟨H, hHcont, hpoint⟩

/--
No-input public C³ pilot for the normalized interval.  This closes the first
finite-order regularity layer beyond the C² pilot.  Higher finite-order
regularity is `publicFiniteOrderRegularity_of_loewnerPosOnUnitInterval`
(`FiniteOrderLadder.lean`), and the public statements are in `LoewnerTheorem.lean`.
-/
theorem publicC3Regularity_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    ContDiffOn ℝ 3 f (Set.Ioo (-1 : ℝ) 1) := by
  rcases exists_hiaiMollifier with ⟨φ, hφ⟩
  have hCauchy :=
    hiaiRegularization_thirdDeriv_localUniformCauchy_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hpos
  rcases
    hiaiRegularization_thirdDerivLimitData_of_eventual_local_uniformCauchy
      (φ := φ) (f := f) hφ hpos hCauchy with
    ⟨H, hHcont, hHpoint⟩
  refine
    publicC3Regularity_of_regularized_thirdDeriv_local_tendstoLocallyUniformlyOn
      (φ := φ) (f := f) (H := H) hpos
      (regularized_secondDeriv_tendsto_of_loewnerPosOnUnitInterval
        (φ := φ) (f := f) hφ hpos)
      ?_ hHcont
  intro x hx
  rcases hCauchy x hx with ⟨r, hr, hleft, hright, huc⟩
  have hball : Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro y hy
    have hyIoo : y ∈ Set.Ioo (x - r) (x + r) := by
      simpa [Real.ball_eq_Ioo] using hy
    constructor
    · exact lt_trans hleft hyIoo.1
    · exact lt_trans hyIoo.2 hright
  have hpointBall :
      ∀ y ∈ Metric.ball x r,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z))) y)
          (𝓝[>] (0 : ℝ)) (𝓝 (H y)) := by
    intro y hy
    exact hHpoint y (hball hy)
  have hthird :
      TendstoLocallyUniformlyOn
        (fun ε y : ℝ =>
          deriv (deriv (deriv
            (fun z : ℝ => hiaiRegularization φ ε f z))) y)
        H (𝓝[>] (0 : ℝ)) (Metric.ball x r) :=
    regularized_thirdDeriv_tendstoLocallyUniformlyOn_of_eventual_local_uniformCauchy
      (φ := φ) (f := f) (H := H) (x := x) (r := r) hpointBall huc
  have hreg :=
    hiaiRegularization_secondDeriv_hasDerivAt_eventually_on_ball
      (φ := φ) (f := f) hφ hpos hleft hright
  exact ⟨r, hr, hball, hthird, hreg⟩

/-- Public C³ regularity, with the former local uniform-Cauchy input closed. -/
theorem
    publicC3Regularity_of_loewnerPosOnUnitInterval_of_hiaiThirdDerivLocalUniformCauchyData
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    ContDiffOn ℝ 3 f (Set.Ioo (-1 : ℝ) 1) :=
  publicC3Regularity_of_loewnerPosOnUnitInterval hpos

/--
The closed `Rε'''` local uniform-Cauchy producer identifies the canonical
third-derivative limit with the ordinary third derivative of `f`.
-/
theorem regularized_thirdDeriv_tendsto_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      Filter.Tendsto
        (fun ε : ℝ =>
          deriv (deriv (deriv
            (fun z : ℝ => hiaiRegularization φ ε f z))) y)
        (𝓝[>] (0 : ℝ)) (𝓝 (deriv (deriv (deriv f)) y)) := by
  intro y hy
  have hCauchy :=
    hiaiRegularization_thirdDeriv_localUniformCauchy_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hpos
  rcases
    hiaiRegularization_thirdDerivLimitData_of_eventual_local_uniformCauchy
      (φ := φ) (f := f) hφ hpos hCauchy with
    ⟨H, _hHcont, hHpoint⟩
  rcases hCauchy y hy with ⟨r, hr, hleft, hright, huc⟩
  have hball : Metric.ball y r ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro z hz
    have hzIoo : z ∈ Set.Ioo (y - r) (y + r) := by
      simpa [Real.ball_eq_Ioo] using hz
    constructor
    · exact lt_trans hleft hzIoo.1
    · exact lt_trans hzIoo.2 hright
  have hpointSecond :
      ∀ z ∈ Metric.ball y r,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w)) z)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv (deriv f) z)) := by
    intro z hz
    exact
      regularized_secondDeriv_tendsto_of_loewnerPosOnUnitInterval
        (φ := φ) (f := f) hφ hpos z (hball hz)
  have hpointH :
      ∀ z ∈ Metric.ball y r,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w))) z)
          (𝓝[>] (0 : ℝ)) (𝓝 (H z)) := by
    intro z hz
    exact hHpoint z (hball hz)
  have hthird :
      TendstoLocallyUniformlyOn
        (fun ε z : ℝ =>
          deriv (deriv (deriv
            (fun w : ℝ => hiaiRegularization φ ε f w))) z)
        H (𝓝[>] (0 : ℝ)) (Metric.ball y r) :=
    regularized_thirdDeriv_tendstoLocallyUniformlyOn_of_eventual_local_uniformCauchy
      (φ := φ) (f := f) (H := H) (x := y) (r := r) hpointH huc
  have hreg :=
    hiaiRegularization_secondDeriv_hasDerivAt_eventually_on_ball
      (φ := φ) (f := f) hφ hpos hleft hright
  have hhas :
      HasDerivAt (deriv (deriv f)) (H y) y :=
    hasDerivAt_secondDeriv_of_regularized_secondDeriv_local_limit
      (φ := φ) (f := f) (H := H) hr hpointSecond hthird hreg
  have hderiv_eq : deriv (deriv (deriv f)) y = H y := hhas.deriv
  simpa [hderiv_eq] using hHpoint y hy

end

end Quantum.TraceInequality.Loewner
