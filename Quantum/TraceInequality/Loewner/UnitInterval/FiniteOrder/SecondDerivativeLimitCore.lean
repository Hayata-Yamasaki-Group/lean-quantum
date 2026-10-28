import Quantum.Analysis.Calculus.UniformCauchy
import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.HiaiSlopeLocalBound
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Convex.Continuous

/-!
# Chapter 20 second-derivative limit package

This file contains the C2 handoff and the regularized second-derivative local
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

/-! ### C2 handoff from derivative regularity -/

/--
Closed packaging from `C¹` regularity of the derivative to the second
finite-order regularity step.  The unconditional C² theorem is
`publicC2Regularity_of_loewnerPosOnUnitInterval` (`SecondDerivativeLimit.lean`).
-/
theorem publicC2Regularity_of_deriv_contDiffOn
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (hderiv : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ 2 f (Set.Ioo (-1 : ℝ) 1) := by
  have h :
      ContDiffOn ℝ ((1 : WithTop ℕ∞) + 1) f
        (Set.Ioo (-1 : ℝ) 1) := by
    rw [contDiffOn_succ_iff_deriv_of_isOpen
      (n := (1 : WithTop ℕ∞)) (f := f) isOpen_Ioo]
    refine ⟨hpos.differentiable, ?_, hderiv⟩
    intro h
    cases h
  simpa using h

/-! ### Regularized derivative differentiability on balls -/

/--
On a fixed ball compactly inside the normalized interval, the derivatives of
the Hiai regularizations are eventually differentiable.  The derivative is the
ordinary second derivative of the regularized function.
-/
theorem hiaiRegularization_deriv_hasDerivAt_eventually_on_ball
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    {x r : ℝ}
    (hleft : (-1 : ℝ) < x - r) (hright : x + r < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
      HasDerivAt
        (fun z : ℝ =>
          deriv (fun w : ℝ => hiaiRegularization φ ε f w) z)
        (deriv (deriv (fun w : ℝ => hiaiRegularization φ ε f w)) y)
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
  have hdiffWithin :
      DifferentiableWithinAt ℝ (deriv R) (hiaiRegularizedInterior ε) y :=
    hderivC4.differentiableOn (by decide) y hyreg
  have hdiffAt : DifferentiableAt ℝ (deriv R) y :=
    hdiffWithin.differentiableAt (hopen.mem_nhds hyreg)
  simpa [R] using hdiffAt.hasDerivAt

/--
On a fixed ball compactly inside the normalized interval, the ordinary second
derivatives of the Hiai regularizations are eventually differentiable.  This is
the differentiability input needed to turn a local third-derivative bound into
a local Lipschitz estimate for the regularized second derivatives.
-/
theorem hiaiRegularization_secondDeriv_hasDerivAt_eventually_on_ball
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    {x r : ℝ}
    (hleft : (-1 : ℝ) < x - r) (hright : x + r < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
      HasDerivAt
        (fun z : ℝ =>
          deriv (deriv
            (fun w : ℝ => hiaiRegularization φ ε f w)) z)
        (deriv (deriv (deriv
          (fun w : ℝ => hiaiRegularization φ ε f w))) y)
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
  have hdiffWithin :
      DifferentiableWithinAt ℝ (deriv (deriv R))
        (hiaiRegularizedInterior ε) y :=
    hsecondC3.differentiableOn (by decide) y hyreg
  have hdiffAt : DifferentiableAt ℝ (deriv (deriv R)) y :=
    hdiffWithin.differentiableAt (hopen.mem_nhds hyreg)
  simpa [R] using hdiffAt.hasDerivAt

/-! ### Local Hankel C2 scaffold -/

/--
The closed local Hankel determinant control and the differentiability of the
regularized derivative family can be placed on the same small ball.  Local
uniform control of the ordinary second derivatives is
`hiaiRegularization_secondDeriv_localUniformCauchy_of_loewnerPosOnUnitInterval` in
`SecondDerivativeLimit.lean`.
-/
theorem hiaiRegularization_secondDeriv_local_scaffold
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 ∧
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
          0 ≤
            (confluentLoewnerHankel3
              (fun z : ℝ => hiaiRegularization φ ε f z) y).det) ∧
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
          HasDerivAt
            (fun z : ℝ =>
              deriv (fun w : ℝ => hiaiRegularization φ ε f w) z)
            (deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w)) y)
            y) := by
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
  have hreg :=
    hiaiRegularization_deriv_hasDerivAt_eventually_on_ball
      (φ := φ) (f := f) hφ hpos hleft hright
  exact ⟨r, hr, hball, hHankel, hreg⟩

/-! ### Local uniform convergence interfaces -/

/--
Metric form of the locally-uniform convergence input for the regularized
second derivatives.  This keeps the equicontinuity or uniform-Cauchy argument
separate from the derivative-limit handoff; for the Hiai regularizations the
uniform-Cauchy estimate is
`hiaiRegularization_secondDeriv_localUniformCauchy_of_loewnerPosOnUnitInterval`
(`SecondDerivativeLimit.lean`).
-/
theorem regularized_secondDeriv_tendstoLocallyUniformlyOn_of_local_dist
    {φ f G : ℝ → ℝ} {x r : ℝ}
    (hdist :
      ∀ η > 0, ∀ y ∈ Metric.ball x r,
        ∃ U ∈ 𝓝[Metric.ball x r] y,
          ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ U,
            dist
              (G z)
              (deriv (deriv
                (fun w : ℝ => hiaiRegularization φ ε f w)) z) < η) :
    TendstoLocallyUniformlyOn
      (fun ε y : ℝ =>
        deriv (deriv
          (fun z : ℝ => hiaiRegularization φ ε f z)) y)
      G (𝓝[>] (0 : ℝ)) (Metric.ball x r) := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  exact hdist

/--
Specialization of the uniform-Cauchy interface to the ordinary second
derivatives of the Hiai regularizations.
-/
theorem regularized_secondDeriv_tendstoLocallyUniformlyOn_of_eventual_local_uniformCauchy
    {φ f G : ℝ → ℝ} {x r : ℝ}
    (hpoint :
      ∀ y ∈ Metric.ball x r,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          (𝓝[>] (0 : ℝ)) (𝓝 (G y)))
    (hcauchy :
      ∀ η > 0, ∀ y ∈ Metric.ball x r,
        ∃ U ∈ 𝓝[Metric.ball x r] y,
          ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ z ∈ U,
            dist
              (deriv (deriv
                (fun w : ℝ => hiaiRegularization φ ε f w)) z)
              (deriv (deriv
                (fun w : ℝ => hiaiRegularization φ δ f w)) z) < η) :
    TendstoLocallyUniformlyOn
      (fun ε y : ℝ =>
        deriv (deriv
          (fun z : ℝ => hiaiRegularization φ ε f z)) y)
      G (𝓝[>] (0 : ℝ)) (Metric.ball x r) :=
  tendstoLocallyUniformlyOn_of_eventual_local_uniformCauchy_and_pointwise
    (F := fun ε y : ℝ =>
      deriv (deriv (fun z : ℝ => hiaiRegularization φ ε f z)) y)
    (G := G) (s := Metric.ball x r) hpoint hcauchy

/--
Specialized local-Lipschitz-to-uniform-Cauchy bridge for the ordinary second
derivatives of the Hiai regularizations.
-/
theorem regularized_secondDeriv_eventual_local_uniformCauchy_of_eventual_local_lipschitz
    {φ f G : ℝ → ℝ} {x r : ℝ}
    (hpoint :
      ∀ y ∈ Metric.ball x r,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          (𝓝[>] (0 : ℝ)) (𝓝 (G y)))
    (hLip :
      ∀ y ∈ Metric.ball x r, ∃ C : ℝ, 0 ≤ C ∧
        ∃ U ∈ 𝓝[Metric.ball x r] y,
          ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ U,
            dist
              (deriv (deriv
                (fun w : ℝ => hiaiRegularization φ ε f w)) z)
              (deriv (deriv
                (fun w : ℝ => hiaiRegularization φ ε f w)) y) ≤
                C * dist z y) :
    ∀ η > 0, ∀ y ∈ Metric.ball x r,
      ∃ U ∈ 𝓝[Metric.ball x r] y,
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ z ∈ U,
          dist
            (deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w)) z)
            (deriv (deriv
              (fun w : ℝ => hiaiRegularization φ δ f w)) z) < η :=
  eventual_local_uniformCauchy_of_eventual_local_lipschitz_and_pointwise_tendsto
    (F := fun ε y : ℝ =>
      deriv (deriv (fun z : ℝ => hiaiRegularization φ ε f z)) y)
    (G := G) (s := Metric.ball x r) hpoint hLip

/-! ### Derivative bounds to local Lipschitz control -/

/--
Produces the exact `hlocal` hypothesis of the C² wrapper from a
Hankel-to-second-derivative local-uniform convergence statement, taken as a
hypothesis.  The Hankel nonnegativity and the regularized `HasDerivAt` facts are
already closed here.  The unconditional C² theorem
`publicC2Regularity_of_loewnerPosOnUnitInterval` (`SecondDerivativeLimit.lean`)
uses the local uniform-Cauchy estimate instead.
-/
theorem regularized_secondDeriv_hlocal_of_hankel_tendstoLocallyUniformlyOn
    {φ f G : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (hsecond :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ∀ r : ℝ,
        0 < r → Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 →
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
            0 ≤
              (confluentLoewnerHankel3
                (fun z : ℝ => hiaiRegularization φ ε f z) y).det) →
          TendstoLocallyUniformlyOn
            (fun ε y : ℝ =>
              deriv (deriv
                (fun z : ℝ => hiaiRegularization φ ε f z)) y)
            G (𝓝[>] (0 : ℝ)) (Metric.ball x r)) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 ∧
        TendstoLocallyUniformlyOn
          (fun ε y : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          G (𝓝[>] (0 : ℝ)) (Metric.ball x r) ∧
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
          HasDerivAt
            (fun z : ℝ =>
              deriv (fun w : ℝ => hiaiRegularization φ ε f w) z)
            (deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w)) y)
            y) := by
  intro x hx
  rcases hiaiRegularization_secondDeriv_local_scaffold
      (φ := φ) (f := f) hφ hpos x hx with
    ⟨r, hr, hball, hHankel, hreg⟩
  exact ⟨r, hr, hball, hsecond x hx r hr hball hHankel, hreg⟩

/--
Produces the exact `hlocal` hypothesis of the C² wrapper from pointwise
second-derivative convergence plus a Hankel-to-uniform-Cauchy producer, taken
as a hypothesis.  This is one layer lower than directly assuming locally-uniform
convergence.  For the Hiai regularizations the uniform-Cauchy estimate is
`hiaiRegularization_secondDeriv_localUniformCauchy_of_loewnerPosOnUnitInterval`
(`SecondDerivativeLimit.lean`), proved from local third-derivative bounds.
-/
theorem regularized_secondDeriv_hlocal_of_hankel_uniformCauchyLimitData
    {φ f G : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (hsecondPoint :
      ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          (𝓝[>] (0 : ℝ)) (𝓝 (G y)))
    (hCauchy :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ∀ r : ℝ,
        0 < r → Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 →
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
            0 ≤
              (confluentLoewnerHankel3
                (fun z : ℝ => hiaiRegularization φ ε f z) y).det) →
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
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 ∧
        TendstoLocallyUniformlyOn
          (fun ε y : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          G (𝓝[>] (0 : ℝ)) (Metric.ball x r) ∧
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
          HasDerivAt
            (fun z : ℝ =>
              deriv (fun w : ℝ => hiaiRegularization φ ε f w) z)
            (deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w)) y)
            y) :=
  regularized_secondDeriv_hlocal_of_hankel_tendstoLocallyUniformlyOn
    (φ := φ) (f := f) (G := G) hφ hpos
    (by
      intro x hx r hr hball hHankel
      exact
        regularized_secondDeriv_tendstoLocallyUniformlyOn_of_eventual_local_uniformCauchy
          (φ := φ) (f := f) (G := G) (x := x) (r := r)
          (by
            intro y hy
            exact hsecondPoint y (hball hy))
          (hCauchy x hx r hr hball hHankel))

/--
Produces the exact `hlocal` hypothesis of the C² wrapper from pointwise
second-derivative convergence plus a Hankel-to-local-Lipschitz producer, taken
as a hypothesis.  For the Hiai regularizations the local third-derivative bounds
are `hiaiRegularization_thirdDeriv_bound_eventually_local_of_loewnerPosOnUnitInterval`
(`RegularizedConfluentHankel.lean`).
-/
theorem regularized_secondDeriv_hlocal_of_hankel_localLipschitzLimitData
    {φ f G : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (hsecondPoint :
      ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          (𝓝[>] (0 : ℝ)) (𝓝 (G y)))
    (hLip :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ∀ r : ℝ,
        0 < r → Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 →
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
            0 ≤
              (confluentLoewnerHankel3
                (fun z : ℝ => hiaiRegularization φ ε f z) y).det) →
          ∀ y ∈ Metric.ball x r, ∃ C : ℝ, 0 ≤ C ∧
            ∃ U ∈ 𝓝[Metric.ball x r] y,
              ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ U,
                dist
                  (deriv (deriv
                    (fun w : ℝ =>
                      hiaiRegularization φ ε f w)) z)
                  (deriv (deriv
                    (fun w : ℝ =>
                      hiaiRegularization φ ε f w)) y) ≤
                    C * dist z y) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 ∧
        TendstoLocallyUniformlyOn
          (fun ε y : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          G (𝓝[>] (0 : ℝ)) (Metric.ball x r) ∧
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
          HasDerivAt
            (fun z : ℝ =>
              deriv (fun w : ℝ => hiaiRegularization φ ε f w) z)
            (deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w)) y)
            y) :=
  regularized_secondDeriv_hlocal_of_hankel_uniformCauchyLimitData
    (φ := φ) (f := f) (G := G) hφ hpos hsecondPoint
    (by
      intro x hx r hr hball hHankel
      exact
        regularized_secondDeriv_eventual_local_uniformCauchy_of_eventual_local_lipschitz
          (φ := φ) (f := f) (G := G) (x := x) (r := r)
          (by
            intro y hy
            exact hsecondPoint y (hball hy))
          (hLip x hx r hr hball hHankel))

/--
Produces the exact `hlocal` hypothesis of the C² wrapper from pointwise
second-derivative convergence plus a Hankel-to-local-third-derivative bound
producer.  This lowers the analytic producer from Lipschitz control to a local
uniform bound on the third derivatives of the regularized functions; such a
producer is `hiaiRegularization_thirdDeriv_bound_eventually_local_of_loewnerPosOnUnitInterval`
(`RegularizedConfluentHankel.lean`).
-/
theorem regularized_secondDeriv_hlocal_of_hankel_thirdDerivBoundLimitData
    {φ f G : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (hsecondPoint :
      ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          (𝓝[>] (0 : ℝ)) (𝓝 (G y)))
    (hthirdBound :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ∀ r : ℝ,
        0 < r → Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 →
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
            0 ≤
              (confluentLoewnerHankel3
                (fun z : ℝ => hiaiRegularization φ ε f z) y).det) →
          ∀ y ∈ Metric.ball x r, ∃ C : ℝ, 0 ≤ C ∧
            ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball y ρ ⊆ Metric.ball x r ∧
              ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ Metric.ball y ρ,
                |deriv (deriv (deriv
                  (fun w : ℝ =>
                    hiaiRegularization φ ε f w))) z| ≤ C) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 ∧
        TendstoLocallyUniformlyOn
          (fun ε y : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          G (𝓝[>] (0 : ℝ)) (Metric.ball x r) ∧
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
          HasDerivAt
            (fun z : ℝ =>
              deriv (fun w : ℝ => hiaiRegularization φ ε f w) z)
            (deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w)) y)
            y) := by
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
  have hreg :=
    hiaiRegularization_deriv_hasDerivAt_eventually_on_ball
      (φ := φ) (f := f) hφ hpos hleft hright
  have hsecondDeriv :=
    hiaiRegularization_secondDeriv_hasDerivAt_eventually_on_ball
      (φ := φ) (f := f) hφ hpos hleft hright
  have hpointBall :
      ∀ y ∈ Metric.ball x r,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          (𝓝[>] (0 : ℝ)) (𝓝 (G y)) := by
    intro y hy
    exact hsecondPoint y (hball hy)
  have hLip :
      ∀ y ∈ Metric.ball x r, ∃ C : ℝ, 0 ≤ C ∧
        ∃ U ∈ 𝓝[Metric.ball x r] y,
          ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ U,
            dist
              (deriv (deriv
                (fun w : ℝ => hiaiRegularization φ ε f w)) z)
              (deriv (deriv
                (fun w : ℝ => hiaiRegularization φ ε f w)) y) ≤
                C * dist z y :=
    eventual_local_lipschitz_of_eventual_hasDerivAt_bound_on_ball
      (F := fun ε y : ℝ =>
        deriv (deriv
          (fun w : ℝ => hiaiRegularization φ ε f w)) y)
      (F' := fun ε y : ℝ =>
        deriv (deriv (deriv
          (fun w : ℝ => hiaiRegularization φ ε f w))) y)
      (x := x) (r := r) (l := 𝓝[>] (0 : ℝ))
      hsecondDeriv (hthirdBound x hx r hr hball hHankel)
  have hsecond :
      TendstoLocallyUniformlyOn
        (fun ε y : ℝ =>
          deriv (deriv
            (fun z : ℝ => hiaiRegularization φ ε f z)) y)
        G (𝓝[>] (0 : ℝ)) (Metric.ball x r) :=
    regularized_secondDeriv_tendstoLocallyUniformlyOn_of_eventual_local_uniformCauchy
      (φ := φ) (f := f) (G := G) (x := x) (r := r)
      hpointBall
      (regularized_secondDeriv_eventual_local_uniformCauchy_of_eventual_local_lipschitz
        (φ := φ) (f := f) (G := G) (x := x) (r := r)
        hpointBall hLip)
  exact ⟨r, hr, hball, hsecond, hreg⟩

/-! ### Middle-entry third-derivative bound -/

/--
Conditional Hankel producer for the third-derivative bound.  The determinant
nonnegativity is threaded through the producer contract, while the additional
local input is the boundedness of the middle diagonal Hankel entry
`(1,1) = f''' / 6`.
-/
theorem
    regularized_thirdDeriv_eventual_local_bound_of_hankel_det_nonneg_and_middleEntryBound
    {φ f : ℝ → ℝ}
    (hmiddleBound :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ∀ r : ℝ,
        0 < r → Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 →
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
            0 ≤
              (confluentLoewnerHankel3
                (fun z : ℝ => hiaiRegularization φ ε f z) y).det) →
          ∀ y ∈ Metric.ball x r, ∃ C : ℝ, 0 ≤ C ∧
            ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball y ρ ⊆ Metric.ball x r ∧
              ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ Metric.ball y ρ,
                |confluentLoewnerHankel3
                  (fun w : ℝ => hiaiRegularization φ ε f w) z 1 1| ≤ C) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ∀ r : ℝ,
      0 < r → Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 →
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
          0 ≤
            (confluentLoewnerHankel3
              (fun z : ℝ => hiaiRegularization φ ε f z) y).det) →
        ∀ y ∈ Metric.ball x r, ∃ C : ℝ, 0 ≤ C ∧
          ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball y ρ ⊆ Metric.ball x r ∧
            ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ Metric.ball y ρ,
              |deriv (deriv (deriv
                (fun w : ℝ =>
                  hiaiRegularization φ ε f w))) z| ≤ C := by
  intro x hx r hr hball hHankel y hy
  rcases hmiddleBound x hx r hr hball hHankel y hy with
    ⟨C, hC, ρ, hρ, hρsub, hentry⟩
  refine ⟨6 * C, by nlinarith, ρ, hρ, hρsub, ?_⟩
  filter_upwards [hentry] with ε hε
  intro z hz
  exact
    abs_thirdDeriv_le_of_confluentLoewnerHankel3_apply_one_one_bound
      (F := fun w : ℝ => hiaiRegularization φ ε f w)
      (z := z) (C := C) (hε z hz)

/--
The PSD diagonal data supply the local middle-entry bound needed by the C²
handoff, once the ordinary second derivatives of the regularizations have
pointwise endpoint limits.  The determinant hypothesis is kept in the contract
for compatibility with the older producer interface, but the proof uses the
stronger local PSD source.
-/
theorem regularization_hankel3_middleEntry_bound_eventually_local_of_secondDeriv_pointwise
    {φ f G : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (hsecondPoint :
      ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          (𝓝[>] (0 : ℝ)) (𝓝 (G y))) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ∀ r : ℝ,
      0 < r → Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 →
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
          0 ≤
            (confluentLoewnerHankel3
              (fun z : ℝ => hiaiRegularization φ ε f z) y).det) →
        ∀ y ∈ Metric.ball x r, ∃ C : ℝ, 0 ≤ C ∧
          ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball y ρ ⊆ Metric.ball x r ∧
            ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ Metric.ball y ρ,
              |confluentLoewnerHankel3
                (fun w : ℝ => hiaiRegularization φ ε f w) z 1 1| ≤ C := by
  intro x _hx r _hr hball _hHankel y hy
  have hyIoo : y ∈ Set.Ioo (-1 : ℝ) 1 := hball hy
  rcases
    hiaiRegularization_confluentLoewnerHankel3_posSemidef_eventually_local
      (φ := φ) (f := f) hφ hpos y hyIoo with
    ⟨σ, hσ, hσleft, hσright, hpsdσ⟩
  have hyBallIoo : y ∈ Set.Ioo (x - r) (x + r) := by
    simpa [Real.ball_eq_Ioo] using hy
  let τ : ℝ := min (y - (x - r)) (x + r - y)
  have hτ : 0 < τ := by
    dsimp [τ]
    exact lt_min (by linarith [hyBallIoo.1]) (by linarith [hyBallIoo.2])
  let ρ : ℝ := min (σ / 4) (τ / 4)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by positivity) (by positivity)
  have hρ_le_σ_quarter : ρ ≤ σ / 4 := by
    dsimp [ρ]
    exact min_le_left _ _
  have hρ_le_τ_quarter : ρ ≤ τ / 4 := by
    dsimp [ρ]
    exact min_le_right _ _
  have h2ρ_lt_σ : 2 * ρ < σ := by nlinarith [hρ_le_σ_quarter, hσ]
  have h2ρ_lt_τ : 2 * ρ < τ := by nlinarith [hρ_le_τ_quarter, hτ]
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
  have ha_ball : a ∈ Metric.ball x r := by
    have haIoo : a ∈ Set.Ioo (x - r) (x + r) := by
      dsimp [a]
      constructor <;> linarith
    simpa [Real.ball_eq_Ioo] using haIoo
  have hb_ball : b ∈ Metric.ball x r := by
    have hbIoo : b ∈ Set.Ioo (x - r) (x + r) := by
      dsimp [b]
      constructor <;> linarith
    simpa [Real.ball_eq_Ioo] using hbIoo
  have haIoo : a ∈ Set.Ioo (-1 : ℝ) 1 := hball ha_ball
  have hbIoo : b ∈ Set.Ioo (-1 : ℝ) 1 := hball hb_ball
  let S : ℝ → ℝ → ℝ := fun ε z : ℝ =>
    deriv (deriv
      (fun w : ℝ => hiaiRegularization φ ε f w)) z
  let A : ℝ := |G b - G a| + 1
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hlimDiff :
      Filter.Tendsto (fun ε : ℝ => S ε b - S ε a)
        (𝓝[>] (0 : ℝ)) (𝓝 (G b - G a)) := by
    dsimp [S]
    exact (hsecondPoint b hbIoo).sub (hsecondPoint a haIoo)
  have hoscEv :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), |S ε b - S ε a| ≤ A := by
    have hnear :=
      hlimDiff.eventually
        (Metric.ball_mem_nhds (G b - G a) (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hnear] with ε hεnear
    have hdist_abs : |S ε b - S ε a + G a - G b| < 1 := by
      simpa [Real.dist_eq] using hεnear
    have htri :
        |S ε b - S ε a| ≤ |S ε b - S ε a + G a - G b| + |G b - G a| := by
      calc
        |S ε b - S ε a| =
            |(S ε b - S ε a + G a - G b) + (G b - G a)| := by
          congr 1
          ring
        _ ≤ |S ε b - S ε a + G a - G b| + |G b - G a| :=
          abs_add_le (S ε b - S ε a + G a - G b) (G b - G a)
    dsimp [A]
    linarith
  have hρsub : Metric.ball y ρ ⊆ Metric.ball x r := by
    intro z hz
    have hzIoo : z ∈ Set.Ioo (y - ρ) (y + ρ) := by
      simpa [Real.ball_eq_Ioo] using hz
    have hzBallIoo : z ∈ Set.Ioo (x - r) (x + r) := by
      constructor <;> linarith [hzIoo.1, hzIoo.2, h2ρ_lt_left, h2ρ_lt_right, hρ]
    simpa [Real.ball_eq_Ioo] using hzBallIoo
  refine ⟨A / ρ, by positivity, ρ, hρ, hρsub, ?_⟩
  have hleftMargin : 0 < y - σ + 1 := by linarith [hσleft]
  have hrightMargin : 0 < 1 - (y + σ) := by linarith [hσright]
  have hε_left : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < y - σ + 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds hleftMargin)
  have hε_right : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 - (y + σ) :=
    nhdsWithin_le_nhds (Iio_mem_nhds hrightMargin)
  filter_upwards [self_mem_nhdsWithin, hε_left, hε_right, hpsdσ, hoscEv] with
    ε hεpos hεleft hεright hpsdε hoscε
  intro z hz
  let R : ℝ → ℝ := fun w : ℝ => hiaiRegularization φ ε f w
  let Fε : ℝ → ℝ := fun w : ℝ => deriv (deriv (deriv R)) w
  have hball_two_sub_σ : Metric.ball y (2 * ρ) ⊆ Metric.ball y σ := by
    intro w hw
    exact Metric.mem_ball.mpr <|
      lt_of_lt_of_le (Metric.mem_ball.mp hw) (le_of_lt h2ρ_lt_σ)
  have hball_two_reg :
      Metric.ball y (2 * ρ) ⊆ hiaiRegularizedInterior ε := by
    intro w hw
    have hwσ : w ∈ Metric.ball y σ := hball_two_sub_σ hw
    have hwIoo : w ∈ Set.Ioo (y - σ) (y + σ) := by
      simpa [Real.ball_eq_Ioo] using hwσ
    dsimp [hiaiRegularizedInterior]
    constructor
    · linarith [hwIoo.1, hεleft]
    · linarith [hwIoo.2, hεright]
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith [hρ]
  have hIcc_reg : Set.Icc a b ⊆ hiaiRegularizedInterior ε := by
    intro w hw
    have hwσ : w ∈ Set.Ioo (y - σ) (y + σ) := by
      dsimp [a, b] at hw
      constructor <;> linarith [hw.1, hw.2, h2ρ_lt_σ]
    dsimp [hiaiRegularizedInterior]
    constructor
    · linarith [hwσ.1, hεleft]
    · linarith [hwσ.2, hεright]
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
      ContDiffOn ℝ 2 Fε (Metric.ball y (2 * ρ)) :=
    hthirdC2.mono hball_two_reg
  have hfourthC1 :
      ContDiffOn ℝ 1 (deriv Fε) (hiaiRegularizedInterior ε) := by
    simpa using hthirdC2.deriv_of_isOpen (m := 1) hopen (by decide)
  have hfourthC1_ball :
      ContDiffOn ℝ 1 (deriv Fε) (Metric.ball y (2 * ρ)) :=
    hfourthC1.mono hball_two_reg
  have hconv : ConvexOn ℝ (Metric.ball y (2 * ρ)) Fε := by
    refine
      convexOn_of_deriv2_nonneg' (convex_ball y (2 * ρ))
        (hthirdC2_ball.differentiableOn (by decide))
        (hfourthC1_ball.differentiableOn (by decide)) ?_
    intro w hw
    have hwσ : w ∈ Metric.ball y σ := hball_two_sub_σ hw
    have hdiag :=
      (hpsdε w hwσ).diag_nonneg (i := (2 : Fin 3))
    have hentry :
        0 ≤ deriv (deriv (deriv (deriv (deriv R)))) w / 120 := by
      dsimp [R]
      simpa [confluentLoewnerHankel3_apply_two_two] using hdiag
    have hfive : 0 ≤ deriv (deriv (deriv (deriv (deriv R)))) w := by
      nlinarith
    simpa [Fε, Function.iterate_succ_apply] using hfive
  have hnonneg : ∀ w ∈ Metric.ball y (2 * ρ), 0 ≤ Fε w := by
    intro w hw
    have hwσ : w ∈ Metric.ball y σ := hball_two_sub_σ hw
    have hdiag :=
      (hpsdε w hwσ).diag_nonneg (i := (1 : Fin 3))
    have hentry :
        0 ≤ deriv (deriv (deriv R)) w / 6 := by
      dsimp [R]
      simpa [confluentLoewnerHankel3_apply_one_one] using hdiag
    dsimp [Fε]
    nlinarith
  have hcont : ContinuousOn Fε (Metric.ball y (2 * ρ)) :=
    hthirdC2_ball.continuousOn
  have hbig_int : IntervalIntegrable Fε volume a b := by
    exact (hthirdC2.continuousOn.mono hIcc_reg).intervalIntegrable_of_Icc hab
  have hsecondC1_Icc :
      ContDiffOn ℝ 1 (deriv (deriv R)) (Set.Icc a b) :=
    (hsecondC3.of_le (by norm_num)).mono hIcc_reg
  have hintegral : ∫ w in a..b, Fε w ≤ A := by
    have hFTC :=
      intervalIntegral.integral_deriv_of_contDiffOn_Icc hsecondC1_Icc hab
    dsimp [Fε, S, R, a, b] at hFTC ⊢
    rw [hFTC]
    exact (le_abs_self _).trans hoscε
  have hthird_bound :
      |Fε z| ≤ A / ρ :=
    convex_nonneg_abs_le_on_inner_ball_of_integral_le
      (F := Fε) (x := y) (ρ := ρ) (A := A)
      hρ hA hconv hnonneg hcont hbig_int hintegral z hz
  have hentry_abs :
      |confluentLoewnerHankel3 R z 1 1| = |Fε z| / 6 := by
    dsimp [Fε]
    simp [confluentLoewnerHankel3_apply_one_one, abs_div]
  rw [hentry_abs]
  nlinarith [hthird_bound, abs_nonneg (Fε z)]

/-! ### Middle-entry and PSD diagonal limit data -/

/--
Produces the exact `hlocal` hypothesis of the C² wrapper when the
Hankel input has been reduced to a local bound on the middle diagonal Hankel
entry.  This is conditional: it does not claim determinant nonnegativity alone
bounds that entry.  The unconditional C² theorem is
`publicC2Regularity_of_loewnerPosOnUnitInterval` (`SecondDerivativeLimit.lean`).
-/
theorem regularized_secondDeriv_hlocal_of_hankel_middleEntryBoundLimitData
    {φ f G : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (hsecondPoint :
      ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          (𝓝[>] (0 : ℝ)) (𝓝 (G y)))
    (hmiddleBound :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ∀ r : ℝ,
        0 < r → Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 →
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
            0 ≤
              (confluentLoewnerHankel3
                (fun z : ℝ => hiaiRegularization φ ε f z) y).det) →
          ∀ y ∈ Metric.ball x r, ∃ C : ℝ, 0 ≤ C ∧
            ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball y ρ ⊆ Metric.ball x r ∧
              ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ Metric.ball y ρ,
                |confluentLoewnerHankel3
                  (fun w : ℝ => hiaiRegularization φ ε f w) z 1 1| ≤ C) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 ∧
        TendstoLocallyUniformlyOn
          (fun ε y : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          G (𝓝[>] (0 : ℝ)) (Metric.ball x r) ∧
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
          HasDerivAt
            (fun z : ℝ =>
              deriv (fun w : ℝ => hiaiRegularization φ ε f w) z)
            (deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w)) y)
            y) :=
  regularized_secondDeriv_hlocal_of_hankel_thirdDerivBoundLimitData
    (φ := φ) (f := f) (G := G) hφ hpos hsecondPoint
    (regularized_thirdDeriv_eventual_local_bound_of_hankel_det_nonneg_and_middleEntryBound
      (φ := φ) (f := f) hmiddleBound)

/--
Closed C² handoff hypothesis from the PSD diagonal source and pointwise limits
of the regularized second derivatives.
-/
theorem regularized_secondDeriv_hlocal_of_hankel_psdDiagonalLimitData
    {φ f G : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (hsecondPoint :
      ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          (𝓝[>] (0 : ℝ)) (𝓝 (G y))) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 ∧
        TendstoLocallyUniformlyOn
          (fun ε y : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          G (𝓝[>] (0 : ℝ)) (Metric.ball x r) ∧
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
          HasDerivAt
            (fun z : ℝ =>
              deriv (fun w : ℝ => hiaiRegularization φ ε f w) z)
            (deriv (deriv
              (fun w : ℝ => hiaiRegularization φ ε f w)) y)
            y) :=
  regularized_secondDeriv_hlocal_of_hankel_middleEntryBoundLimitData
    (φ := φ) (f := f) (G := G) hφ hpos hsecondPoint
    (regularization_hankel3_middleEntry_bound_eventually_local_of_secondDeriv_pointwise
      (φ := φ) (f := f) (G := G) hφ hpos hsecondPoint)

/-! ### Derivative-limit transfer to C1 regularity -/

/--
Local derivative-limit transfer for the C² pilot.  If the regularized
derivatives converge pointwise to `deriv f` on a small ball and their
derivatives converge locally uniformly there, then `deriv f` is differentiable
at the center.
-/
theorem hasDerivAt_deriv_of_regularized_deriv_local_limit
    {φ f G : ℝ → ℝ} {x r : ℝ} (hr : 0 < r)
    (hpoint :
      ∀ y ∈ Metric.ball x r,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv f y)))
    (hsecond :
      TendstoLocallyUniformlyOn
        (fun ε y : ℝ =>
          deriv (deriv (fun z : ℝ => hiaiRegularization φ ε f z)) y)
        G (𝓝[>] (0 : ℝ)) (Metric.ball x r))
    (hreg :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
        HasDerivAt
          (fun z : ℝ =>
            deriv (fun w : ℝ => hiaiRegularization φ ε f w) z)
          (deriv (deriv (fun w : ℝ => hiaiRegularization φ ε f w)) y)
          y) :
    HasDerivAt (deriv f) (G x) x :=
  hasDerivAt_of_tendstoLocallyUniformlyOn
    (f := fun ε y : ℝ =>
      deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)
    (g := deriv f)
    (f' := fun ε y : ℝ =>
      deriv (deriv (fun z : ℝ => hiaiRegularization φ ε f z)) y)
    (g' := G)
    (s := Metric.ball x r) (l := 𝓝[>] (0 : ℝ))
    Metric.isOpen_ball hsecond hreg hpoint (Metric.mem_ball_self hr)

/--
Abstract C²-pilot handoff.  The only analytic input is local uniform
convergence of the regularized second derivatives to a continuous limit `G`;
for the Hiai regularizations it comes from
`hiaiRegularization_secondDeriv_localUniformCauchy_of_loewnerPosOnUnitInterval`
(`SecondDerivativeLimit.lean`).  The local differentiability of the regularized
derivative family is supplied separately so the theorem can be used with either
the Hiai regularizations or another approximant family.
-/
theorem deriv_contDiffOn_of_regularized_deriv_local_tendstoLocallyUniformlyOn
    {φ f G : ℝ → ℝ}
    (hpoint :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (fun z : ℝ => hiaiRegularization φ ε f z) x)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv f x)))
    (hlocal :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 ∧
          TendstoLocallyUniformlyOn
            (fun ε y : ℝ =>
              deriv (deriv
                (fun z : ℝ => hiaiRegularization φ ε f z)) y)
            G (𝓝[>] (0 : ℝ)) (Metric.ball x r) ∧
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
            HasDerivAt
              (fun z : ℝ =>
                deriv (fun w : ℝ => hiaiRegularization φ ε f w) z)
              (deriv (deriv
                (fun w : ℝ => hiaiRegularization φ ε f w)) y)
              y))
    (hGcont : ContinuousOn G (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ 1 (deriv f) (Set.Ioo (-1 : ℝ) 1) := by
  have hdiff :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (deriv f) (G x) x := by
    intro x hx
    rcases hlocal x hx with ⟨r, hr, hball_sub, hsecond, hreg⟩
    exact
      hasDerivAt_deriv_of_regularized_deriv_local_limit
        (φ := φ) (f := f) (G := G) hr
        (by
          intro y hy
          exact hpoint y (hball_sub hy))
        hsecond hreg
  have hdiffOn : DifferentiableOn ℝ (deriv f) (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    exact (hdiff x hx).differentiableAt.differentiableWithinAt
  have hderiv_eq : Set.EqOn (deriv (deriv f)) G (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    exact (hdiff x hx).deriv
  have hderiv_cont :
      ContinuousOn (deriv (deriv f)) (Set.Ioo (-1 : ℝ) 1) :=
    hGcont.congr hderiv_eq
  have h :
      ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1)
        (deriv f) (Set.Ioo (-1 : ℝ) 1) := by
    rw [contDiffOn_succ_iff_deriv_of_isOpen
      (n := (0 : WithTop ℕ∞)) (f := deriv f) isOpen_Ioo]
    refine ⟨hdiffOn, ?_, ?_⟩
    · intro htop
      cases htop
    · exact contDiffOn_zero.2 hderiv_cont
  simpa using h

/--
Conditional public C² wrapper for the regularized derivative handoff.  Local
uniform convergence/control of the regularized second derivatives is an explicit
hypothesis here; the no-input C² theorem is
`publicC2Regularity_of_loewnerPosOnUnitInterval` (`SecondDerivativeLimit.lean`).
-/
theorem publicC2Regularity_of_regularized_deriv_local_tendstoLocallyUniformlyOn
    {φ f G : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (hpoint :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (fun z : ℝ => hiaiRegularization φ ε f z) x)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv f x)))
    (hlocal :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 ∧
          TendstoLocallyUniformlyOn
            (fun ε y : ℝ =>
              deriv (deriv
                (fun z : ℝ => hiaiRegularization φ ε f z)) y)
            G (𝓝[>] (0 : ℝ)) (Metric.ball x r) ∧
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
            HasDerivAt
              (fun z : ℝ =>
                deriv (fun w : ℝ => hiaiRegularization φ ε f w) z)
              (deriv (deriv
                (fun w : ℝ => hiaiRegularization φ ε f w)) y)
              y))
    (hGcont : ContinuousOn G (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ 2 f (Set.Ioo (-1 : ℝ) 1) :=
  publicC2Regularity_of_deriv_contDiffOn hpos
    (deriv_contDiffOn_of_regularized_deriv_local_tendstoLocallyUniformlyOn
      (φ := φ) (f := f) (G := G) hpoint hlocal hGcont)

/--
Conditional public C² wrapper with the Hankel input lowered to an
eventual local bound on the third derivatives of the regularized functions.
This is not the no-input C² theorem: both derivative pointwise limits and the
Hankel-to-third-derivative-bound producer are explicit hypotheses here.  The
producer is `hiaiRegularization_thirdDeriv_bound_eventually_local_of_loewnerPosOnUnitInterval`,
and the no-input C² theorem is `publicC2Regularity_of_loewnerPosOnUnitInterval`.
-/
theorem publicC2Regularity_of_regularized_secondDeriv_hankelThirdDerivBoundLimitData
    {φ f G : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (hpoint :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (fun z : ℝ => hiaiRegularization φ ε f z) x)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv f x)))
    (hsecondPoint :
      ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          (𝓝[>] (0 : ℝ)) (𝓝 (G y)))
    (hthirdBound :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ∀ r : ℝ,
        0 < r → Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 →
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
            0 ≤
              (confluentLoewnerHankel3
                (fun z : ℝ => hiaiRegularization φ ε f z) y).det) →
          ∀ y ∈ Metric.ball x r, ∃ C : ℝ, 0 ≤ C ∧
            ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball y ρ ⊆ Metric.ball x r ∧
              ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ Metric.ball y ρ,
                |deriv (deriv (deriv
                  (fun w : ℝ =>
                    hiaiRegularization φ ε f w))) z| ≤ C)
    (hGcont : ContinuousOn G (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ 2 f (Set.Ioo (-1 : ℝ) 1) :=
  publicC2Regularity_of_regularized_deriv_local_tendstoLocallyUniformlyOn
    (φ := φ) (f := f) (G := G) hpos hpoint
    (regularized_secondDeriv_hlocal_of_hankel_thirdDerivBoundLimitData
      (φ := φ) (f := f) (G := G) hφ hpos hsecondPoint hthirdBound)
    hGcont

/--
Conditional public C² wrapper with the Hankel input lowered to PSD
diagonal data plus pointwise limits of the regularized second derivatives.
This is a C² pilot theorem; the unconditional C² theorem is
`publicC2Regularity_of_loewnerPosOnUnitInterval` (`SecondDerivativeLimit.lean`).
-/
theorem publicC2Regularity_of_regularized_secondDeriv_hankelPsdDiagonalLimitData
    {φ f G : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (hpoint :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (fun z : ℝ => hiaiRegularization φ ε f z) x)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv f x)))
    (hsecondPoint :
      ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          (𝓝[>] (0 : ℝ)) (𝓝 (G y)))
    (hGcont : ContinuousOn G (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ 2 f (Set.Ioo (-1 : ℝ) 1) :=
  publicC2Regularity_of_regularized_deriv_local_tendstoLocallyUniformlyOn
    (φ := φ) (f := f) (G := G) hpos hpoint
    (regularized_secondDeriv_hlocal_of_hankel_psdDiagonalLimitData
      (φ := φ) (f := f) (G := G) hφ hpos hsecondPoint)
    hGcont

/-! ### Closed second-derivative limit data -/

/--
Variant of the PSD diagonal C² pilot wrapper after the first-derivative
pointwise convergence input has been closed from public Löwner positivity.
The limit data is the pointwise convergence of the regularized second
derivatives to a continuous candidate `G`, supplied in
`publicC2Regularity_of_loewnerPosOnUnitInterval` (`SecondDerivativeLimit.lean`).
-/
theorem
    publicC2Regularity_of_regularized_secondDeriv_hankelPsdDiagonalLimitData_closedHpoint
    {φ f G : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (hsecondPoint :
      ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z)) y)
          (𝓝[>] (0 : ℝ)) (𝓝 (G y)))
    (hGcont : ContinuousOn G (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ 2 f (Set.Ioo (-1 : ℝ) 1) :=
  publicC2Regularity_of_regularized_secondDeriv_hankelPsdDiagonalLimitData
    (φ := φ) (f := f) (G := G) hφ hpos
    (regularized_deriv_tendsto_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hpos)
    hsecondPoint hGcont


end

end Quantum.TraceInequality.Loewner
