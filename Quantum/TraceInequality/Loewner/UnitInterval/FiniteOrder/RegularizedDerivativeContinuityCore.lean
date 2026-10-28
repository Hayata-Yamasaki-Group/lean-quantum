import Quantum.Analysis.Calculus.EquicontinuousFamily
import Quantum.Analysis.Calculus.ConvexBounds
import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.RegularizationSmoothness
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic


/-!
# Chapter 20 regularized derivative continuity transfer

This file contains the affine-pullback derivative identity, the conditional
smooth-Hiai convexity transfer, and the equicontinuity/local-Lipschitz package
that turns regularized derivative convergence into continuity of `deriv f`.
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
The derivative of the affine pullback is the positive scale `r` times the
derivative of the regularized function at the corresponding point.
-/
theorem hiaiRegularization_affinePullback_deriv_eq
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r u : ℝ} (hε : 0 < ε)
    (hu : x + r * u ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    deriv (hiaiRegularizationAffinePullback φ ε f x r) u =
      r * deriv (fun z : ℝ => hiaiRegularization φ ε f z) (x + r * u) := by
  have hg :=
    regularization_original_hasDerivAt_scaledWeight_of_loewnerPos
      (φ := φ) (f := f) hφ hε hu hpos
  have hlin : HasDerivAt (fun w : ℝ => x + r * w) r u := by
    simpa [mul_comm] using ((hasDerivAt_id u).const_mul r).const_add x
  have hgdiff : DifferentiableAt ℝ
      (fun z : ℝ => hiaiRegularization φ ε f z) (x + r * u) :=
    hg.differentiableAt
  have hcomp : HasDerivAt
      (hiaiRegularizationAffinePullback φ ε f x r)
      (r * deriv (fun z : ℝ => hiaiRegularization φ ε f z) (x + r * u))
      u := by
    simpa [hiaiRegularizationAffinePullback, Function.comp_def, mul_comm,
      mul_left_comm, mul_assoc] using
      hgdiff.hasDerivAt.comp u hlin
  simpa using hcomp.deriv

/--
Thin consumer for the smooth Hiai `C³` theorem.  Once the theorem supplies
convexity of the derivative from unit-interval Löwner positivity plus `C³`, the
regularized affine pullback can be fed to it directly.
-/
theorem hiaiRegularization_affinePullback_deriv_convexOn_of_C3SmoothHiai
    (smoothHiai :
      ∀ {g : ℝ → ℝ}, LoewnerPosOnUnitInterval g →
        ContDiffOn ℝ 3 g (Set.Ioo (-1 : ℝ) 1) →
          ConvexOn ℝ (Set.Ioo (-1 : ℝ) 1) (deriv g))
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    ConvexOn ℝ (Set.Ioo (-1 : ℝ) 1)
      (deriv (hiaiRegularizationAffinePullback φ ε f x r)) := by
  rcases hiaiRegularization_affinePullback_C3_loewnerPosInput
      (φ := φ) (f := f) hφ hε hr hsub hpos with ⟨hpull_pos, hpull_c3⟩
  exact smoothHiai hpull_pos hpull_c3

/--
Convexity of the affine-pullback derivative transfers back to convexity of the
regularized derivative on the original small interval.
-/
theorem hiaiRegularization_deriv_convexOn_Ioo_of_affinePullback
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f)
    (hconv :
      ConvexOn ℝ (Set.Ioo (-1 : ℝ) 1)
        (deriv (hiaiRegularizationAffinePullback φ ε f x r))) :
    ConvexOn ℝ (Set.Ioo (x - r) (x + r))
      (deriv (fun z : ℝ => hiaiRegularization φ ε f z)) := by
  refine ⟨convex_Ioo _ _, ?_⟩
  intro y hy z hz a b ha hb hab
  let uy : ℝ := (y - x) / r
  let uz : ℝ := (z - x) / r
  have huy : uy ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · dsimp [uy]
      rw [lt_div_iff₀ hr]
      linarith [hy.1]
    · dsimp [uy]
      rw [div_lt_one hr]
      linarith [hy.2]
  have huz : uz ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · dsimp [uz]
      rw [lt_div_iff₀ hr]
      linarith [hz.1]
    · dsimp [uz]
      rw [div_lt_one hr]
      linarith [hz.2]
  have hy_geom : x + r * uy = y := by
    dsimp [uy]
    field_simp [hr.ne']
    ring
  have hz_geom : x + r * uz = z := by
    dsimp [uz]
    field_simp [hr.ne']
    ring
  have hmid_mem : a • y + b • z ∈ Set.Ioo (x - r) (x + r) :=
    (convex_Ioo (𝕜 := ℝ) (x - r) (x + r)) hy hz ha hb hab
  have hmid_geom : x + r * (a • uy + b • uz) = a • y + b • z := by
    rw [← hy_geom, ← hz_geom]
    simp only [smul_eq_mul]
    calc
      x + r * (a * uy + b * uz)
          = (a + b) * x + r * (a * uy + b * uz) := by
            rw [hab]
            ring
      _ = a * (x + r * uy) + b * (x + r * uz) := by
            ring
  have hy_reg : x + r * uy ∈ hiaiRegularizedInterior ε := by
    simpa [hy_geom] using hsub ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hz_reg : x + r * uz ∈ hiaiRegularizedInterior ε := by
    simpa [hz_geom] using hsub ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  have hmid_reg :
      x + r * (a • uy + b • uz) ∈ hiaiRegularizedInterior ε := by
    have hmid_reg' : a • y + b • z ∈ hiaiRegularizedInterior ε :=
      hsub ⟨le_of_lt hmid_mem.1, le_of_lt hmid_mem.2⟩
    rwa [hmid_geom]
  have hdy :=
    hiaiRegularization_affinePullback_deriv_eq
      (φ := φ) (f := f) hφ hε hy_reg hpos
  have hdz :=
    hiaiRegularization_affinePullback_deriv_eq
      (φ := φ) (f := f) hφ hε hz_reg hpos
  have hdm :=
    hiaiRegularization_affinePullback_deriv_eq
      (φ := φ) (f := f) hφ hε hmid_reg hpos
  have hineq := hconv.2 huy huz ha hb hab
  rw [hdy, hdz, hdm] at hineq
  change
    deriv (fun z : ℝ => hiaiRegularization φ ε f z) (a • y + b • z) ≤
      a • deriv (fun z : ℝ => hiaiRegularization φ ε f z) y +
        b • deriv (fun z : ℝ => hiaiRegularization φ ε f z) z
  rw [← hmid_geom, ← hy_geom, ← hz_geom]
  exact (mul_le_mul_iff_left₀ hr).1 <| by
    simpa [smul_eq_mul, mul_add, mul_assoc, mul_left_comm, mul_comm] using hineq

/--
Combining the `C³` smooth Hiai consumer with the affine pullback gives local
convexity of the derivative of the regularized function on any small interval
inside the regularized interior.
-/
theorem hiaiRegularization_deriv_convexOn_local_of_C3SmoothHiai
    (smoothHiai :
      ∀ {g : ℝ → ℝ}, LoewnerPosOnUnitInterval g →
        ContDiffOn ℝ 3 g (Set.Ioo (-1 : ℝ) 1) →
          ConvexOn ℝ (Set.Ioo (-1 : ℝ) 1) (deriv g))
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    ConvexOn ℝ (Set.Ioo (x - r) (x + r))
      (deriv (fun z : ℝ => hiaiRegularization φ ε f z)) :=
  hiaiRegularization_deriv_convexOn_Ioo_of_affinePullback
    (φ := φ) (f := f) hφ hε hr hsub hpos
    (hiaiRegularization_affinePullback_deriv_convexOn_of_C3SmoothHiai
      smoothHiai (φ := φ) (f := f) hφ hε hr hsub hpos)

/--
Family form of the conditional smooth-Hiai consumer.  This keeps the theorem
parameter for the smooth Hiai `C³` step explicit while making the resulting
local convexity of the regularized derivatives available uniformly in all
small intervals contained in the regularized interior.
-/
theorem hiaiRegularization_deriv_convexOn_local_family_of_C3SmoothHiai
    (smoothHiai :
      ∀ {g : ℝ → ℝ}, LoewnerPosOnUnitInterval g →
        ContDiffOn ℝ 3 g (Set.Ioo (-1 : ℝ) 1) →
          ConvexOn ℝ (Set.Ioo (-1 : ℝ) 1) (deriv g))
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    ∀ {ε x r : ℝ}, 0 < ε → 0 < r →
      Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε →
        ConvexOn ℝ (Set.Ioo (x - r) (x + r))
          (deriv (fun z : ℝ => hiaiRegularization φ ε f z)) := by
  intro ε x r hε hr hsub
  exact
    hiaiRegularization_deriv_convexOn_local_of_C3SmoothHiai
      smoothHiai (φ := φ) (f := f) hφ hε hr hsub hpos

/--
Endpoint-inequality version of the same local convexity handoff.  This is the
form used in the later `ε ↓ 0` transfer, where one chooses a concrete small
radius around a fixed interior point.
-/
theorem hiaiRegularization_deriv_convexOn_localAt_of_C3SmoothHiai
    (smoothHiai :
      ∀ {g : ℝ → ℝ}, LoewnerPosOnUnitInterval g →
        ContDiffOn ℝ 3 g (Set.Ioo (-1 : ℝ) 1) →
          ConvexOn ℝ (Set.Ioo (-1 : ℝ) 1) (deriv g))
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hleft : (-1 : ℝ) + ε < x - r) (hright : x + r < 1 - ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    ConvexOn ℝ (Set.Ioo (x - r) (x + r))
      (deriv (fun z : ℝ => hiaiRegularization φ ε f z)) := by
  refine
    hiaiRegularization_deriv_convexOn_local_family_of_C3SmoothHiai
      smoothHiai (φ := φ) (f := f) hφ hpos hε hr ?_
  intro y hy
  exact ⟨lt_of_lt_of_le hleft hy.1, lt_of_le_of_lt hy.2 hright⟩

/--
Specialized `ε ↓ 0` transfer for the derivatives of the Hiai regularizations.
The analytic input is isolated in the two hypotheses: pointwise derivative
convergence and eventual local equicontinuity of the regularized derivatives.
For Löwner-positive `f` both are supplied on the way to
`deriv_continuousOn_of_loewnerPosOnUnitInterval_of_hiaiMollifier`
(`RegularizedSecondDerivativeLimit.lean`); the pointwise convergence is
`regularized_deriv_tendsto_of_loewnerPosOnUnitInterval`.
-/
theorem deriv_continuousOn_of_regularized_deriv_tendsto_and_eventual_equi
    {φ f : ℝ → ℝ}
    (hpoint :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (fun z : ℝ => hiaiRegularization φ ε f z) x)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv f x)))
    (hequi :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ∀ η > 0, ∃ U ∈ 𝓝 x,
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ U,
          dist
            (deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)
            (deriv (fun z : ℝ => hiaiRegularization φ ε f z) x) < η) :
    ContinuousOn (deriv f) (Set.Ioo (-1 : ℝ) 1) := by
  intro x hx
  have hnear :
      ∀ᶠ y in 𝓝 x,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv f y)) :=
    by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hpoint y hy
  exact
    (continuousAt_of_eventual_equi_tendsto
      (F := fun ε y =>
        deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)
      (g := deriv f) (x := x)
      (hpoint x hx) hnear (hequi x hx)).continuousWithinAt

/--
Specialized eventual equicontinuity producer for the derivatives of the Hiai
regularizations.  The analytic input is an eventual local Lipschitz estimate
for those derivatives.  For Löwner-positive `f` it is supplied on the way to
`deriv_continuousOn_of_loewnerPosOnUnitInterval_of_hiaiMollifier`
(`RegularizedSecondDerivativeLimit.lean`), from
`regularized_deriv_eventual_lipschitzOnWith_of_C3SmoothHiai`.
-/
theorem regularized_deriv_eventual_equi_of_eventual_local_lipschitz
    {φ f : ℝ → ℝ}
    (hLip :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ C : ℝ, 0 ≤ C ∧ ∃ U ∈ 𝓝 x,
          ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ U,
            dist
              (deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)
              (deriv (fun z : ℝ => hiaiRegularization φ ε f z) x) ≤
                C * dist y x) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ∀ η > 0, ∃ U ∈ 𝓝 x,
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ U,
        dist
          (deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)
          (deriv (fun z : ℝ => hiaiRegularization φ ε f z) x) < η := by
  intro x hx
  exact
    eventual_equi_of_eventual_local_lipschitz
      (F := fun ε y =>
        deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)
      (x := x) (l := 𝓝[>] (0 : ℝ)) (hLip x hx)

/--
Derivative continuity follows from pointwise derivative convergence plus the
local Lipschitz version of the equicontinuity input.
-/
theorem deriv_continuousOn_of_regularized_deriv_tendsto_and_eventual_local_lipschitz
    {φ f : ℝ → ℝ}
    (hpoint :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (fun z : ℝ => hiaiRegularization φ ε f z) x)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv f x)))
    (hLip :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ C : ℝ, 0 ≤ C ∧ ∃ U ∈ 𝓝 x,
          ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ U,
            dist
              (deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)
              (deriv (fun z : ℝ => hiaiRegularization φ ε f z) x) ≤
                C * dist y x) :
    ContinuousOn (deriv f) (Set.Ioo (-1 : ℝ) 1) :=
  deriv_continuousOn_of_regularized_deriv_tendsto_and_eventual_equi
    (φ := φ) (f := f) hpoint
    (regularized_deriv_eventual_equi_of_eventual_local_lipschitz
      (φ := φ) (f := f) hLip)

/--
Specialization of the `LipschitzOnWith` bridge to the regularized derivative
family used in the book route.
-/
theorem regularized_deriv_eventual_local_lipschitz_of_lipschitzOnWith
    {φ f : ℝ → ℝ}
    (hLip :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ K : ℝ≥0, ∃ U ∈ 𝓝 x, x ∈ U ∧
          ∀ᶠ ε in 𝓝[>] (0 : ℝ),
            LipschitzOnWith K
              (fun y : ℝ =>
                deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)
              U) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ C : ℝ, 0 ≤ C ∧ ∃ U ∈ 𝓝 x,
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ U,
          dist
            (deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)
            (deriv (fun z : ℝ => hiaiRegularization φ ε f z) x) ≤
              C * dist y x := by
  intro x hx
  exact
    eventual_local_lipschitz_of_lipschitzOnWith
      (F := fun ε y =>
        deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)
      (x := x) (l := 𝓝[>] (0 : ℝ)) (hLip x hx)

/--
Derivative continuity follows from pointwise derivative convergence plus a
Mathlib `LipschitzOnWith` producer for the regularized derivatives.
-/
theorem deriv_continuousOn_of_regularized_deriv_tendsto_and_lipschitzOnWith
    {φ f : ℝ → ℝ}
    (hpoint :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (fun z : ℝ => hiaiRegularization φ ε f z) x)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv f x)))
    (hLip :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ K : ℝ≥0, ∃ U ∈ 𝓝 x, x ∈ U ∧
          ∀ᶠ ε in 𝓝[>] (0 : ℝ),
            LipschitzOnWith K
              (fun y : ℝ =>
                deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)
              U) :
    ContinuousOn (deriv f) (Set.Ioo (-1 : ℝ) 1) :=
  deriv_continuousOn_of_regularized_deriv_tendsto_and_eventual_local_lipschitz
    (φ := φ) (f := f) hpoint
    (regularized_deriv_eventual_local_lipschitz_of_lipschitzOnWith
      (φ := φ) (f := f) hLip)

/--
For the Hiai regularized derivatives, a local endpoint oscillation bound for
the regularized functions supplies the eventual local uniform absolute-value
bound needed by the `LipschitzOnWith` producer.
-/
theorem regularized_deriv_eventual_abs_le_of_endpointOscillation
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (hlocal :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ ρ A : ℝ, 0 < ρ ∧ 0 ≤ A ∧
          (-1 : ℝ) < x - 2 * ρ ∧ x + 2 * ρ < 1 ∧
          (∀ᶠ ε in 𝓝[>] (0 : ℝ),
            ConvexOn ℝ (Metric.ball x (2 * ρ))
              (fun y : ℝ =>
                deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)) ∧
          (∀ᶠ ε in 𝓝[>] (0 : ℝ),
            |hiaiRegularization φ ε f (x + 2 * ρ) -
              hiaiRegularization φ ε f (x - 2 * ρ)| ≤ A)) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ r δ M : ℝ, 0 < δ ∧ δ < r ∧
        (-1 : ℝ) < x - r ∧ x + r < 1 ∧
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
          abs (deriv
            (fun z : ℝ => hiaiRegularization φ ε f z) y) ≤ M) := by
  intro x hx
  rcases hlocal x hx with
    ⟨ρ, A, hρ, hA, hleft, hright, hconvEv, hoscEv⟩
  refine ⟨ρ, ρ / 2, A / ρ, by positivity, by linarith, ?_, ?_, ?_⟩
  · linarith
  · linarith
  have hleftMargin : 0 < x - 2 * ρ + 1 := by linarith
  have hrightMargin : 0 < 1 - (x + 2 * ρ) := by linarith
  have hε_left : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < x - 2 * ρ + 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds hleftMargin)
  have hε_right : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 - (x + 2 * ρ) :=
    nhdsWithin_le_nhds (Iio_mem_nhds hrightMargin)
  filter_upwards [self_mem_nhdsWithin, hε_left, hε_right, hconvEv, hoscEv] with
    ε hεpos hεleft hεright hconvε hoscε
  intro y hy
  let Fε : ℝ → ℝ :=
    fun y : ℝ => deriv (fun z : ℝ => hiaiRegularization φ ε f z) y
  let c : ℝ := x - 2 * ρ
  let d : ℝ := x + 2 * ρ
  have hcd : c ≤ d := by dsimp [c, d]; linarith
  have hball_sub :
      Metric.ball x (2 * ρ) ⊆ hiaiRegularizedInterior ε := by
    intro z hz
    have hzIoo : z ∈ Set.Ioo (x - 2 * ρ) (x + 2 * ρ) := by
      simpa [Real.ball_eq_Ioo] using hz
    dsimp [hiaiRegularizedInterior]
    exact ⟨by linarith [hεleft, hzIoo.1],
      by linarith [hεright, hzIoo.2]⟩
  have hIcc_sub :
      Set.Icc c d ⊆ hiaiRegularizedInterior ε := by
    intro z hz
    dsimp [hiaiRegularizedInterior, c, d] at *
    exact ⟨by linarith [hεleft, hz.1], by linarith [hεright, hz.2]⟩
  have hderiv_cont_reg :
      ContinuousOn
        (deriv (fun z : ℝ => hiaiRegularization φ ε f z))
        (hiaiRegularizedInterior ε) :=
    hiaiRegularization_deriv_continuousOn_regularizedInterior
      (φ := φ) (f := f) hφ hεpos hpos
  have hcont : ContinuousOn Fε (Metric.ball x (2 * ρ)) :=
    hderiv_cont_reg.mono hball_sub
  have hcont_Icc : ContinuousOn Fε (Set.Icc c d) :=
    hderiv_cont_reg.mono hIcc_sub
  have hbig_int : IntervalIntegrable Fε volume c d :=
    hcont_Icc.intervalIntegrable_of_Icc hcd
  have hreg_c1 :
      ContDiffOn ℝ 1
        (fun z : ℝ => hiaiRegularization φ ε f z)
        (hiaiRegularizedInterior ε) :=
    hiaiRegularization_contDiffOn_regularizedInterior_order
      (φ := φ) (f := f) hφ hεpos hpos
  have hreg_c1_Icc :
      ContDiffOn ℝ 1
        (fun z : ℝ => hiaiRegularization φ ε f z)
        (Set.Icc c d) :=
    hreg_c1.mono hIcc_sub
  have hintegral :
      ∫ z in c..d, Fε z ≤ A := by
    have hFTC :=
      intervalIntegral.integral_deriv_of_contDiffOn_Icc hreg_c1_Icc hcd
    dsimp [Fε, c, d]
    rw [hFTC]
    exact (le_abs_self _).trans hoscε
  have hnonneg : ∀ z ∈ Metric.ball x (2 * ρ), 0 ≤ Fε z := by
    intro z hz
    let R : ℝ := 2 * ρ
    let u : ℝ := (z - x) / R
    have hR : 0 < R := by dsimp [R]; positivity
    have hzIoo : z ∈ Set.Ioo (x - R) (x + R) := by
      simpa [Real.ball_eq_Ioo, R] using hz
    have hu : u ∈ Set.Ioo (-1 : ℝ) 1 := by
      constructor
      · dsimp [u]
        rw [lt_div_iff₀ hR]
        linarith [hzIoo.1]
      · dsimp [u]
        rw [div_lt_one hR]
        linarith [hzIoo.2]
    have hsubR :
        Set.Icc (x - R) (x + R) ⊆ hiaiRegularizedInterior ε := by
      intro w hw
      dsimp [hiaiRegularizedInterior, R] at *
      exact ⟨by linarith [hεleft, hw.1], by linarith [hεright, hw.2]⟩
    have hpull :
        LoewnerPosOnUnitInterval
          (hiaiRegularizationAffinePullback φ ε f x R) :=
      hiaiRegularization_affinePullback_loewnerPosOnUnitInterval
        (φ := φ) (f := f) hφ hεpos hR hsubR hpos
    have hpull_nonneg :=
      deriv_nonneg_on_Ioo_of_loewnerPosOnUnitInterval hpull hu
    have hgeom : x + R * u = z := by
      dsimp [u]
      field_simp [hR.ne']
      ring
    have hzu : x + R * u ∈ hiaiRegularizedInterior ε := by
      simpa [hgeom] using hball_sub hz
    have hderiv_eq :=
      hiaiRegularization_affinePullback_deriv_eq
        (φ := φ) (f := f) hφ hεpos hzu hpos
    rw [hderiv_eq] at hpull_nonneg
    have hscaled :
        0 ≤ R * deriv (fun w : ℝ => hiaiRegularization φ ε f w) z := by
      simpa [hgeom] using hpull_nonneg
    dsimp [Fε]
    nlinarith [hscaled, hR]
  exact
    convex_nonneg_abs_le_on_inner_ball_of_integral_le
      (F := Fε) (x := x) (ρ := ρ) (A := A)
      hρ hA hconvε hnonneg hcont hbig_int hintegral y hy

/--
Specialized `LipschitzOnWith` producer for the regularized derivative family.
The inputs are now exactly the local convexity producer and the local uniform
absolute-value bound on a slightly larger ball.
-/
theorem regularized_deriv_eventual_lipschitzOnWith_of_eventual_convex_abs_le
    {φ f : ℝ → ℝ}
    (hlocal :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ r δ M : ℝ, 0 < δ ∧ δ < r ∧
          (∀ᶠ ε in 𝓝[>] (0 : ℝ),
            ConvexOn ℝ (Metric.ball x r)
              (fun y : ℝ =>
                deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)) ∧
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
  intro x hx
  rcases hlocal x hx with ⟨r, δ, M, hδ, hδr, hconv, habs⟩
  exact
    eventual_lipschitzOnWith_of_eventual_convexOn_ball_abs_le
      (F := fun ε y =>
        deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)
      (x := x) (r := r) (δ := δ) (M := M)
      hδ hδr hconv habs

/--
Derivative continuity follows from pointwise derivative convergence plus local
convexity and a local uniform absolute-value bound for the regularized
derivatives.
-/
theorem deriv_continuousOn_of_regularized_deriv_tendsto_and_eventual_convex_abs_le
    {φ f : ℝ → ℝ}
    (hpoint :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ =>
            deriv (fun z : ℝ => hiaiRegularization φ ε f z) x)
          (𝓝[>] (0 : ℝ)) (𝓝 (deriv f x)))
    (hlocal :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ r δ M : ℝ, 0 < δ ∧ δ < r ∧
          (∀ᶠ ε in 𝓝[>] (0 : ℝ),
            ConvexOn ℝ (Metric.ball x r)
              (fun y : ℝ =>
                deriv (fun z : ℝ => hiaiRegularization φ ε f z) y)) ∧
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
            abs (deriv
              (fun z : ℝ => hiaiRegularization φ ε f z) y) ≤ M)) :
    ContinuousOn (deriv f) (Set.Ioo (-1 : ℝ) 1) :=
  deriv_continuousOn_of_regularized_deriv_tendsto_and_lipschitzOnWith
    (φ := φ) (f := f) hpoint
    (regularized_deriv_eventual_lipschitzOnWith_of_eventual_convex_abs_le
      (φ := φ) (f := f) hlocal)


end

end Quantum.TraceInequality.Loewner
