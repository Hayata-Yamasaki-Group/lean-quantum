import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.ThirdDerivativeLimit
import Quantum.TraceInequality.Loewner.RealComplexOrder
import Quantum.QuantumEntropy.Common.RealComplexOrder
import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.ForwardFiniteDifferenceLow
import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.ForwardCoefficientSource
import Mathlib.Algebra.Group.ForwardDiff -- finite-difference moments for the finite-order ladder
import Mathlib.Analysis.Calculus.ParametricIntegral -- dominated differentiation under integral
import Mathlib.Analysis.Calculus.Taylor -- finite-order Taylor limits for the smooth Hiai C3 body
import Mathlib.Analysis.Calculus.UniformLimitsDeriv -- local uniform derivative-limit transfer
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Convex.Continuous -- convex bounded functions are Lipschitz on smaller balls
import Mathlib.Analysis.Convex.Integral -- Jensen inequality for convex functions
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic -- elementary interval integrals
import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-!
# Chapter 20 finite-order ladder

This file contains the generic finite-order regularity ladder built after the
hand-written C10 through C14 regularity handoffs.
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

/-! ### Core derivative-ladder predicates -/

private lemma natCast_withTopENat_le {m n : ℕ} (h : m ≤ n) :
    (m : WithTop ℕ∞) ≤ (n : ℕ) :=
  WithTop.coe_le_coe.mpr (WithTop.coe_le_coe.mpr h)

private lemma natCast_withTopENat_lt {m n : ℕ} (h : m < n) :
    (m : WithTop ℕ∞) < (n : ℕ) :=
  WithTop.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr h)

/-- Uniform notation for the `q`th ordinary derivative of the Hiai regularization. -/
def hiaiDeriv (q : ℕ) (φ : ℝ → ℝ) (ε : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  deriv^[q] (fun w : ℝ => hiaiRegularization φ ε f w)

/-- Eventual local bound for a fixed Hiai derivative order. -/
def HiaiEventualLocalBound
    (q : ℕ) (φ f : ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ∀ r : ℝ,
    0 < r → Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 →
      ∀ y ∈ Metric.ball x r, ∃ C : ℝ, 0 ≤ C ∧
        ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball y ρ ⊆ Metric.ball x r ∧
          ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ Metric.ball y ρ,
            |hiaiDeriv q φ ε f z| ≤ C

/-- Eventual local nonnegativity for a fixed regularized derivative order. -/
def HiaiOddDerivNonnegLocal
    (q : ℕ) (φ f : ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
    ∃ θ : ℝ, 0 < θ ∧ (-1 : ℝ) < x - θ ∧ x + θ < 1 ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ Metric.ball x θ,
        0 ≤ hiaiDeriv q φ ε f z

/-- Eventual local uniform-Cauchy control for a fixed Hiai derivative order. -/
def HiaiEventualLocalUniformCauchy
    (q : ℕ) (φ f : ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
    ∃ r : ℝ, 0 < r ∧ (-1 : ℝ) < x - r ∧ x + r < 1 ∧
      ∀ η > 0, ∀ y ∈ Metric.ball x r,
        ∃ U ∈ 𝓝[Metric.ball x r] y,
          ∀ᶠ ε in 𝓝[>] (0 : ℝ),
            ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ z ∈ U,
              dist (hiaiDeriv q φ ε f z)
                (hiaiDeriv q φ δ f z) < η

/-- Eventual derivative identity on every interior ball. -/
def HiaiEventualHasDerivAtOnBalls
    (q : ℕ) (φ f : ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ∀ r : ℝ,
    0 < r → (-1 : ℝ) < x - r → x + r < 1 →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
        HasDerivAt (hiaiDeriv q φ ε f)
          (hiaiDeriv (q + 1) φ ε f y) y

/-! ### Eventual derivative identities on interior balls -/
/--
On every ball compactly inside the normalized interval, the regularized
derivative tower satisfies the expected derivative identity at arbitrary order.
-/
theorem hiaiRegularization_hiaiDeriv_hasDerivAt_eventually_on_ball
    (q : ℕ) {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    HiaiEventualHasDerivAtOnBalls q φ f := by
  intro x _hx r _hr hx_left hx_right
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
  let s : Set ℝ := hiaiRegularizedInterior ε
  have hyIoo : y ∈ Set.Ioo (x - r) (x + r) := by
    simpa [Real.ball_eq_Ioo] using hy
  have hyreg : y ∈ s := by
    dsimp [s, hiaiRegularizedInterior]
    constructor
    · linarith [hyIoo.1, hεleft]
    · linarith [hyIoo.2, hεright]
  have hsopen : IsOpen s := by
    simpa [s, hiaiRegularizedInterior] using isOpen_Ioo
  have hC : ContDiffOn ℝ (q + 1) R s := by
    dsimp [R, s]
    exact hiaiRegularization_contDiffOn_regularizedInterior_anyOrder
      (m := q + 1) (φ := φ) (f := f) hφ hεpos hpos
  have hq_lt : (q : WithTop ℕ∞) < (q + 1 : ℕ) := by
    exact natCast_withTopENat_lt (Nat.lt_succ_self q)
  have hdiffWithin :
      DifferentiableWithinAt ℝ (iteratedDerivWithin q R s) s y :=
    hC.differentiableOn_iteratedDerivWithin hq_lt hsopen.uniqueDiffOn y hyreg
  have hdiffAt :
      DifferentiableAt ℝ (iteratedDerivWithin q R s) y :=
    hdiffWithin.differentiableAt (hsopen.mem_nhds hyreg)
  have hEq :
      (deriv^[q] R) =ᶠ[𝓝 y] (iteratedDerivWithin q R s) := by
    filter_upwards [hsopen.mem_nhds hyreg] with z hz
    exact (iteratedDerivWithin_of_isOpen_eq_iterate (f := R) (n := q) hsopen hz).symm
  have hdiffIter : DifferentiableAt ℝ (deriv^[q] R) y :=
    hdiffAt.congr_of_eventuallyEq hEq
  have hderiv_eq :
      deriv (deriv^[q] R) y = (deriv^[q] (deriv R)) y := by
    have hleft :
        deriv (deriv^[q] R) = iteratedDeriv (q + 1) R := by
      rw [← iteratedDeriv_eq_iterate (n := q) (f := R), ← iteratedDeriv_succ]
    have hright :
        (deriv^[q] (deriv R)) = iteratedDeriv (q + 1) R := by
      rw [← iteratedDeriv_eq_iterate (n := q) (f := deriv R), ← iteratedDeriv_succ']
    exact congrFun (hleft.trans hright.symm) y
  exact
    (by
      simpa [hiaiDeriv, R, Function.iterate_succ_apply] using
        hdiffIter.hasDerivAt.congr_deriv hderiv_eq)

/-- Eventual derivative identities for arbitrary Hiai derivative order. -/
theorem hiaiRegularization_hiaiDeriv_hasDerivAt_eventually_on_balls
    (q : ℕ) {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    HiaiEventualHasDerivAtOnBalls q φ f :=
  hiaiRegularization_hiaiDeriv_hasDerivAt_eventually_on_ball
    (q := q) (φ := φ) (f := f) hφ hpos

/-! ### Local uniform Cauchy propagation -/
/--
Abstract Hiai derivative Cauchy step: pointwise convergence of order `q`,
eventual derivative identities for orders `q` and `q+1`, and a local bound for
order `q+2` imply local uniform-Cauchy control of order `q+1`.
-/
theorem hiaiDeriv_localUniformCauchy_of_nextDeriv_bound
    {q : ℕ} {φ f g : ℝ → ℝ}
    (hpoint :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ => hiaiDeriv q φ ε f x)
          (𝓝[>] (0 : ℝ)) (𝓝 (g x)))
    (hderiv :
      HiaiEventualHasDerivAtOnBalls q φ f)
    (hnextDeriv :
      HiaiEventualHasDerivAtOnBalls (q + 1) φ f)
    (hbound :
      HiaiEventualLocalBound (q + 2) φ f) :
    HiaiEventualLocalUniformCauchy (q + 1) φ f := by
  intro x hx
  let leftMargin : ℝ := x - (-1 : ℝ)
  let rightMargin : ℝ := (1 : ℝ) - x
  let r : ℝ := min leftMargin rightMargin / 2
  have hleft_pos : 0 < leftMargin := by
    dsimp [leftMargin]
    linarith [hx.1]
  have hright_pos : 0 < rightMargin := by
    dsimp [rightMargin]
    linarith [hx.2]
  have hmin_pos : 0 < min leftMargin rightMargin := lt_min hleft_pos hright_pos
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hr_lt_left : r < leftMargin := by
    have hr_le_half : r ≤ leftMargin / 2 := by
      dsimp [r]
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hhalf_lt : leftMargin / 2 < leftMargin := by linarith
    exact lt_of_le_of_lt hr_le_half hhalf_lt
  have hr_lt_right : r < rightMargin := by
    have hr_le_half : r ≤ rightMargin / 2 := by
      dsimp [r]
      exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    have hhalf_lt : rightMargin / 2 < rightMargin := by linarith
    exact lt_of_le_of_lt hr_le_half hhalf_lt
  have hleft : (-1 : ℝ) < x - r := by
    dsimp [leftMargin] at hr_lt_left
    linarith
  have hright : x + r < 1 := by
    dsimp [rightMargin] at hr_lt_right
    linarith
  have hball : Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro y hy
    have hyIoo : y ∈ Set.Ioo (x - r) (x + r) := by
      simpa [Real.ball_eq_Ioo] using hy
    constructor
    · exact lt_trans hleft hyIoo.1
    · exact lt_trans hyIoo.2 hright
  refine ⟨r, hr, hleft, hright, ?_⟩
  have hderivBall := hderiv x hx r hr hleft hright
  have hnextDerivBall := hnextDeriv x hx r hr hleft hright
  have hboundBall := hbound x hx r hr hball
  intro η hη y hy
  rcases hboundBall y hy with ⟨C, hC, ρ, hρ, hρsub, hnextBound⟩
  have hpointSmall :
      ∀ t ∈ Metric.ball y ρ,
        Filter.Tendsto
          (fun ε : ℝ => hiaiDeriv q φ ε f t)
          (𝓝[>] (0 : ℝ)) (𝓝 (g t)) := by
    intro t ht
    exact hpoint t (hball (hρsub ht))
  have hregSmall :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Metric.ball y ρ,
        HasDerivAt (hiaiDeriv q φ ε f)
          (hiaiDeriv (q + 1) φ ε f t) t := by
    filter_upwards [hderivBall] with ε hε
    intro t ht
    exact hε t (hρsub ht)
  have hLip :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        LipschitzOnWith (Real.toNNReal C)
          (hiaiDeriv (q + 1) φ ε f) (Metric.ball y ρ) := by
    filter_upwards [hnextDerivBall, hnextBound] with ε hεDeriv hεBound
    refine (convex_ball y ρ).lipschitzOnWith_of_nnnorm_deriv_le ?_ ?_
    · intro z hz
      exact (hεDeriv z (hρsub hz)).differentiableAt
    · intro z hz
      have hderiv_eq :
          deriv (hiaiDeriv (q + 1) φ ε f) z =
            hiaiDeriv (q + 2) φ ε f z :=
        (hεDeriv z (hρsub hz)).deriv
      rw [← NNReal.coe_le_coe, Real.toNNReal_of_nonneg hC,
        coe_nnnorm, Real.norm_eq_abs, hderiv_eq]
      exact hεBound z hz
  rcases
    deriv_family_eventual_local_uniformCauchy_at_of_lipschitzOnWith
      (l := 𝓝[>] (0 : ℝ))
      (G := fun ε t : ℝ => hiaiDeriv q φ ε f t)
      (F := fun ε t : ℝ => hiaiDeriv (q + 1) φ ε f t)
      (g := g) (y := y) (ρ := ρ) (K := C)
      hρ hC hpointSmall hregSmall hLip η hη with
    ⟨U, hU, hUCauchy⟩
  exact ⟨U, mem_nhdsWithin_of_mem_nhds hU, hUCauchy⟩

/-! ### Source nonnegativity transport -/
/--
Conditional transport of an arbitrary odd-source theorem to one Hiai
regularization on its regularized interior.

The source theorem is intentionally separated out: the hard part of Lemma 72
is the forward finite-difference source for all odd orders, proved as
`oddIteratedDeriv_nonneg_of_loewnerPosOnUnitInterval` in `FiniteOrderLadder.lean`.
-/
theorem hiaiRegularization_hiaiDeriv_nonneg_on_Ioo_of_source
    (q : ℕ)
    (hsource :
      ∀ {g : ℝ → ℝ}, LoewnerPosOnUnitInterval g →
        ContDiffOn ℝ q g (Set.Ioo (-1 : ℝ) 1) →
          ∀ z ∈ Set.Ioo (-1 : ℝ) 1, 0 ≤ (deriv^[q] g) z)
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ z ∈ hiaiRegularizedInterior ε,
      0 ≤ hiaiDeriv q φ ε f z := by
  intro z hz
  let leftMargin : ℝ := z - ((-1 : ℝ) + ε)
  let rightMargin : ℝ := (1 - ε) - z
  let r : ℝ := min leftMargin rightMargin / 4
  have hleft_pos : 0 < leftMargin := by
    dsimp [leftMargin]
    linarith [hz.1]
  have hright_pos : 0 < rightMargin := by
    dsimp [rightMargin]
    linarith [hz.2]
  have hmin_pos : 0 < min leftMargin rightMargin :=
    lt_min hleft_pos hright_pos
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hr_le_left_quarter : r ≤ leftMargin / 4 := by
    dsimp [r]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hr_le_right_quarter : r ≤ rightMargin / 4 := by
    dsimp [r]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hsub : Set.Icc (z - r) (z + r) ⊆ hiaiRegularizedInterior ε := by
    intro y hy
    dsimp [hiaiRegularizedInterior, leftMargin, rightMargin] at *
    constructor
    · nlinarith [hy.1, hr_le_left_quarter, hleft_pos]
    · nlinarith [hy.2, hr_le_right_quarter, hright_pos]
  let R : ℝ → ℝ := fun w : ℝ => hiaiRegularization φ ε f w
  let L : ℝ → ℝ :=
    hiaiRegularization φ ε
      (hiaiLocalClip f (z - (ε + r)) (z + (ε + r)))
  let A : ℝ → ℝ := hiaiRegularizationAffinePullback φ ε f z r
  let AL : ℝ → ℝ := fun v : ℝ => L (z + r * v)
  have hleft_mem : z - r ∈ Set.Icc (z - r) (z + r) := by
    constructor
    · rfl
    · linarith [hr]
  have hright_mem : z + r ∈ Set.Icc (z - r) (z + r) := by
    constructor
    · linarith [hr]
    · rfl
  have hleft := hsub hleft_mem
  have hright := hsub hright_mem
  have hη_nonneg : 0 ≤ ε + r := by linarith
  have hzη : z ∈ hiaiRegularizedInterior (ε + r) := by
    dsimp [hiaiRegularizedInterior] at *
    constructor
    · linarith [hleft.1]
    · linarith [hright.2]
  have hclip : ContDiff ℝ q L := by
    dsimp [L]
    exact hiaiRegularization_localClip_contDiff_anyOrder
      (φ := φ) (f := f) hφ q hε hη_nonneg hzη hpos
  have hzero : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  have hApos : LoewnerPosOnUnitInterval A :=
    hiaiRegularization_affinePullback_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hε hr hsub hpos
  have hACq : ContDiffOn ℝ q A (Set.Ioo (-1 : ℝ) 1) :=
    hiaiRegularization_affinePullback_contDiffOn_anyOrder
      (φ := φ) (f := f) hφ q hε hr hsub hpos
  have hA_nonneg : 0 ≤ (deriv^[q] A) 0 :=
    hsource hApos hACq 0 hzero
  have hA_iter_nonneg : 0 ≤ iteratedDeriv q A 0 := by
    simpa [iteratedDeriv_eq_iterate] using hA_nonneg
  have hzsmall : z ∈ Set.Ioo (z - r) (z + r) := by
    constructor <;> linarith [hr]
  have hR_eq_L : R =ᶠ[𝓝 z] L := by
    filter_upwards [isOpen_Ioo.mem_nhds hzsmall] with y hy
    dsimp [R, L]
    exact hiaiRegularization_eq_localClip_on_small_interval
      (φ := φ) (f := f) (ε := ε) (δ := r) (x := z) (z := y)
      hε hy
  have hpre : {v : ℝ | z + r * v ∈ Set.Ioo (z - r) (z + r)} ∈ 𝓝 (0 : ℝ) := by
    have hcont : ContinuousAt (fun v : ℝ => z + r * v) 0 := by
      fun_prop
    exact hcont (isOpen_Ioo.mem_nhds (by simpa using hzsmall))
  have hA_eq_AL : A =ᶠ[𝓝 (0 : ℝ)] AL := by
    filter_upwards [hpre] with v hv
    dsimp [A, AL, L, hiaiRegularizationAffinePullback]
    exact hiaiRegularization_eq_localClip_on_small_interval
      (φ := φ) (f := f) (ε := ε) (δ := r) (x := z) (z := z + r * v)
      hε hv
  have hA_iter_eq_AL : iteratedDeriv q A 0 = iteratedDeriv q AL 0 :=
    hA_eq_AL.iteratedDeriv_eq q
  have hR_iter_eq_L : iteratedDeriv q R z = iteratedDeriv q L z :=
    hR_eq_L.iteratedDeriv_eq q
  have hscaleL :
      iteratedDeriv q AL 0 = r ^ q * iteratedDeriv q L z := by
    simpa [AL] using
      affinePullback_iteratedDeriv_eq_anyOrder
        (F := L) (M := q) (n := q) hclip z r 0 le_rfl
  have hscaleR : iteratedDeriv q A 0 = r ^ q * iteratedDeriv q R z := by
    rw [hA_iter_eq_AL, hscaleL, hR_iter_eq_L]
  have hmul_nonneg : 0 ≤ r ^ q * iteratedDeriv q R z := by
    simpa [hscaleR] using hA_iter_nonneg
  have hR_iter_nonneg : 0 ≤ iteratedDeriv q R z :=
    nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hmul_nonneg) (pow_pos hr q)
  simpa [hiaiDeriv, R, iteratedDeriv_eq_iterate] using hR_iter_nonneg

/--
Conditional eventual-local transport of an arbitrary odd-source theorem to the
Hiai regularized derivatives.
-/
theorem hiaiRegularization_hiaiDeriv_nonneg_eventually_local_of_source
    (q : ℕ)
    (hsource :
      ∀ {g : ℝ → ℝ}, LoewnerPosOnUnitInterval g →
        ContDiffOn ℝ q g (Set.Ioo (-1 : ℝ) 1) →
          ∀ z ∈ Set.Ioo (-1 : ℝ) 1, 0 ≤ (deriv^[q] g) z)
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    HiaiOddDerivNonnegLocal q φ f := by
  intro x hx
  let m : ℝ := min (x + 1) (1 - x)
  let θ : ℝ := m / 4
  have hx_left_pos : 0 < x + 1 := by linarith [hx.1]
  have hx_right_pos : 0 < 1 - x := by linarith [hx.2]
  have hm_pos : 0 < m := by
    dsimp [m]
    exact lt_min hx_left_pos hx_right_pos
  have hθ : 0 < θ := by
    dsimp [θ]
    positivity
  have hθ_le_left_quarter : θ ≤ (x + 1) / 4 := by
    dsimp [θ, m]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hθ_le_right_quarter : θ ≤ (1 - x) / 4 := by
    dsimp [θ, m]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hleft : (-1 : ℝ) < x - θ := by
    nlinarith [hθ_le_left_quarter, hx_left_pos]
  have hright : x + θ < 1 := by
    nlinarith [hθ_le_right_quarter, hx_right_pos]
  refine ⟨θ, hθ, hleft, hright, ?_⟩
  have hε_ltθ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < θ :=
    nhdsWithin_le_nhds (Iio_mem_nhds hθ)
  filter_upwards [self_mem_nhdsWithin, hε_ltθ] with ε hεpos hεθ
  intro z hz
  have hε_left_bound : ε + θ < x + 1 := by
    nlinarith [hεθ, hθ_le_left_quarter, hx_left_pos]
  have hε_right_bound : ε + θ < 1 - x := by
    nlinarith [hεθ, hθ_le_right_quarter, hx_right_pos]
  have hzIoo : z ∈ Set.Ioo (x - θ) (x + θ) := by
    simpa [Real.ball_eq_Ioo] using hz
  have hzreg : z ∈ hiaiRegularizedInterior ε := by
    dsimp [hiaiRegularizedInterior]
    constructor
    · linarith [hzIoo.1, hε_left_bound]
    · linarith [hzIoo.2, hε_right_bound]
  exact
    hiaiRegularization_hiaiDeriv_nonneg_on_Ioo_of_source
      (q := q) hsource (φ := φ) (f := f) hφ hpos hεpos z hzreg

/-! ### Even-parity local bounds -/
/--
Generic even-parity bound producer: a local bound for order `q`, together
with nonnegativity of the regularized derivatives of orders `q` and `q+2`,
bounds order `q+1`.
-/
theorem regularization_succDeriv_bound_eventually_local_of_bound_nonneg_twoStep
    (q : ℕ) {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (hbound : HiaiEventualLocalBound q φ f)
    (hnonneg : HiaiOddDerivNonnegLocal q φ f)
    (htwoStepNonneg : HiaiOddDerivNonnegLocal (q + 2) φ f) :
    HiaiEventualLocalBound (q + 1) φ f := by
  intro x _hx r _hr hball y hy
  have hyIoo : y ∈ Set.Ioo (-1 : ℝ) 1 := hball hy
  rcases hnonneg y hyIoo with
    ⟨θ, hθ, hθleft, hθright, hnonnegθ⟩
  rcases htwoStepNonneg y hyIoo with
    ⟨χ, hχ, hχleft, hχright, htwoStepχ⟩
  let lam : ℝ := min θ χ
  have hlam : 0 < lam := by
    dsimp [lam]
    exact lt_min hθ hχ
  have hlam_le_θ : lam ≤ θ := by
    dsimp [lam]
    exact min_le_left _ _
  have hlam_le_χ : lam ≤ χ := by
    dsimp [lam]
    exact min_le_right _ _
  have hlamleft : (-1 : ℝ) < y - lam := by
    nlinarith [hθleft, hχleft, hlam_le_θ, hlam_le_χ]
  have hlamright : y + lam < 1 := by
    nlinarith [hθright, hχright, hlam_le_θ, hlam_le_χ]
  have hball_lam : Metric.ball y lam ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro z hz
    have hzIoo : z ∈ Set.Ioo (y - lam) (y + lam) := by
      simpa [Real.ball_eq_Ioo] using hz
    constructor
    · exact lt_trans hlamleft hzIoo.1
    · exact lt_trans hzIoo.2 hlamright
  have hlocalBound := hbound y hyIoo lam hlam hball_lam
  have hyBallIoo : y ∈ Set.Ioo (x - r) (x + r) := by
    simpa [Real.ball_eq_Ioo] using hy
  let τ : ℝ := min (y - (x - r)) (x + r - y)
  have hτ : 0 < τ := by
    dsimp [τ]
    exact lt_min (by linarith [hyBallIoo.1]) (by linarith [hyBallIoo.2])
  let ρ : ℝ := min (lam / 8) (τ / 8)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by positivity) (by positivity)
  have hρ_le_lam_eighth : ρ ≤ lam / 8 := by
    dsimp [ρ]
    exact min_le_left _ _
  have hρ_le_τ_eighth : ρ ≤ τ / 8 := by
    dsimp [ρ]
    exact min_le_right _ _
  have h4ρ_lt_lam : 4 * ρ < lam := by nlinarith [hρ_le_lam_eighth, hlam]
  have h2ρ_lt_left : 2 * ρ < y - (x - r) := by
    have h2ρ_lt_τ : 2 * ρ < τ := by nlinarith [hρ_le_τ_eighth, hτ]
    have hτ_le_left : τ ≤ y - (x - r) := by
      dsimp [τ]
      exact min_le_left _ _
    exact lt_of_lt_of_le h2ρ_lt_τ hτ_le_left
  have h2ρ_lt_right : 2 * ρ < x + r - y := by
    have h2ρ_lt_τ : 2 * ρ < τ := by nlinarith [hρ_le_τ_eighth, hτ]
    have hτ_le_right : τ ≤ x + r - y := by
      dsimp [τ]
      exact min_le_right _ _
    exact lt_of_lt_of_le h2ρ_lt_τ hτ_le_right
  have hleft4 : (-1 : ℝ) < y - 4 * ρ := by
    nlinarith [hlamleft, h4ρ_lt_lam]
  have hright4 : y + 4 * ρ < 1 := by
    nlinarith [hlamright, h4ρ_lt_lam]
  let a : ℝ := y - 2 * ρ
  let b : ℝ := y + 2 * ρ
  have ha_lam : a ∈ Metric.ball y lam := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [a]
    rw [abs_of_nonpos (by linarith : y - 2 * ρ - y ≤ 0)]
    linarith
  have hb_lam : b ∈ Metric.ball y lam := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [b]
    rw [abs_of_nonneg (by linarith : 0 ≤ y + 2 * ρ - y)]
    linarith
  rcases hlocalBound a ha_lam with ⟨Ca, hCa, σa, hσa, _hσaSub, hbounda⟩
  rcases hlocalBound b hb_lam with ⟨Cb, hCb, σb, hσb, _hσbSub, hboundb⟩
  let B : ℝ := max Ca Cb
  have hB : 0 ≤ B := by
    dsimp [B]
    exact le_max_of_le_left hCa
  have hboundA :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        hiaiDeriv q φ ε f a ≤ B := by
    filter_upwards [hbounda] with ε hε
    have ha_self : a ∈ Metric.ball a σa := Metric.mem_ball_self hσa
    have habs := hε a ha_self
    calc
      hiaiDeriv q φ ε f a
          ≤ |hiaiDeriv q φ ε f a| := le_abs_self _
      _ ≤ Ca := habs
      _ ≤ B := by dsimp [B]; exact le_max_left _ _
  have hboundB :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        hiaiDeriv q φ ε f b ≤ B := by
    filter_upwards [hboundb] with ε hε
    have hb_self : b ∈ Metric.ball b σb := Metric.mem_ball_self hσb
    have habs := hε b hb_self
    calc
      hiaiDeriv q φ ε f b
          ≤ |hiaiDeriv q φ ε f b| := le_abs_self _
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
  have hderivQ :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ w ∈ Metric.ball y (4 * ρ),
        HasDerivAt (hiaiDeriv q φ ε f)
          (hiaiDeriv (q + 1) φ ε f w) w :=
    hiaiRegularization_hiaiDeriv_hasDerivAt_eventually_on_ball
      (q := q) (φ := φ) (f := f) hφ hpos y hyIoo
      (4 * ρ) (by positivity) hleft4 hright4
  have hderivQsucc :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ w ∈ Metric.ball y (4 * ρ),
        HasDerivAt (hiaiDeriv (q + 1) φ ε f)
          (hiaiDeriv (q + 2) φ ε f w) w :=
    hiaiRegularization_hiaiDeriv_hasDerivAt_eventually_on_ball
      (q := q + 1) (φ := φ) (f := f) hφ hpos y hyIoo
      (4 * ρ) (by positivity) hleft4 hright4
  have hleftMargin : 0 < y - lam + 1 := by linarith [hlamleft]
  have hrightMargin : 0 < 1 - (y + lam) := by linarith [hlamright]
  have hε_left : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < y - lam + 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds hleftMargin)
  have hε_right : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 - (y + lam) :=
    nhdsWithin_le_nhds (Iio_mem_nhds hrightMargin)
  filter_upwards [self_mem_nhdsWithin, hε_left, hε_right,
    hnonnegθ, htwoStepχ, hboundA, hboundB, hderivQ, hderivQsucc] with
    ε hεpos hεleft hεright hnonnegε htwoStepε hAε hBε hderivQε hderivQsuccε
  intro z hz
  let Fε : ℝ → ℝ := hiaiDeriv q φ ε f
  have hball4_sub_lam : Metric.ball y (4 * ρ) ⊆ Metric.ball y lam := by
    intro w hw
    exact Metric.mem_ball.mpr <|
      lt_of_lt_of_le (Metric.mem_ball.mp hw) (le_of_lt h4ρ_lt_lam)
  have hball4_sub_θ : Metric.ball y (4 * ρ) ⊆ Metric.ball y θ := by
    intro w hw
    exact Metric.mem_ball.mpr <|
      lt_of_lt_of_le (Metric.mem_ball.mp (hball4_sub_lam hw)) hlam_le_θ
  have hball4_sub_χ : Metric.ball y (4 * ρ) ⊆ Metric.ball y χ := by
    intro w hw
    exact Metric.mem_ball.mpr <|
      lt_of_lt_of_le (Metric.mem_ball.mp (hball4_sub_lam hw)) hlam_le_χ
  have hρ_to_ball4 : Metric.ball y ρ ⊆ Metric.ball y (4 * ρ) := by
    intro w hw
    exact Metric.mem_ball.mpr <|
      lt_trans (Metric.mem_ball.mp hw) (by linarith [hρ])
  have hdiffF : DifferentiableOn ℝ Fε (Metric.ball y (4 * ρ)) := by
    intro w hw
    exact (hderivQε w hw).differentiableAt.differentiableWithinAt
  have hdiffNext :
      DifferentiableOn ℝ (hiaiDeriv (q + 1) φ ε f)
        (Metric.ball y (4 * ρ)) := by
    intro w hw
    exact (hderivQsuccε w hw).differentiableAt.differentiableWithinAt
  have hderiv_eq :
      ∀ w ∈ Metric.ball y (4 * ρ),
        deriv Fε w = hiaiDeriv (q + 1) φ ε f w := by
    intro w hw
    exact (hderivQε w hw).deriv
  have hdiffDerivF :
      DifferentiableOn ℝ (deriv Fε) (Metric.ball y (4 * ρ)) :=
    hdiffNext.congr (fun w hw => hderiv_eq w hw)
  have hconv : ConvexOn ℝ (Metric.ball y (4 * ρ)) Fε := by
    refine
      convexOn_of_deriv2_nonneg' (convex_ball y (4 * ρ))
        hdiffF hdiffDerivF ?_
    intro w hw
    change 0 ≤ deriv (deriv Fε) w
    have heqEvent :
        deriv Fε =ᶠ[𝓝 w] hiaiDeriv (q + 1) φ ε f := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hw] with t ht
      exact hderiv_eq t ht
    have hsecond_eq :
        deriv (deriv Fε) w =
          deriv (hiaiDeriv (q + 1) φ ε f) w :=
      heqEvent.deriv_eq
    have hsucc_deriv :=
      (hderivQsuccε w hw).deriv
    rw [hsecond_eq, hsucc_deriv]
    exact htwoStepε w (hball4_sub_χ hw)
  have hdiff : ∀ w ∈ Metric.ball y (4 * ρ), DifferentiableAt ℝ Fε w := by
    intro w hw
    exact (hderivQε w hw).differentiableAt
  have hnonnegF : ∀ w ∈ Metric.ball y (4 * ρ), 0 ≤ Fε w := by
    intro w hw
    exact hnonnegε w (hball4_sub_θ hw)
  have hinner :=
    convex_nonneg_abs_deriv_le_on_inner_ball_of_endpoint_le
      (F := Fε) (x := y) (ρ := ρ) (M := B)
      hρ hB hconv hdiff hnonnegF
      (by simpa [Fε, a] using hAε)
      (by simpa [Fε, b] using hBε)
      z hz
  have hz4 : z ∈ Metric.ball y (4 * ρ) := hρ_to_ball4 hz
  have htarget_eq :
      deriv Fε z = hiaiDeriv (q + 1) φ ε f z :=
    hderiv_eq z hz4
  simpa [Fε, htarget_eq] using hinner

/-! ### Odd-parity local bounds -/
/--
Generic odd-parity bound producer: a local bound for order `q`, together with
nonnegativity of the regularized derivatives of orders `q+1` and `q+3`,
bounds order `q+1`.
-/
theorem regularization_succDeriv_bound_eventually_local_of_bound_succ_nonneg_threeStep
    (q : ℕ) {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (hbound : HiaiEventualLocalBound q φ f)
    (hsuccNonneg : HiaiOddDerivNonnegLocal (q + 1) φ f)
    (hthreeStepNonneg : HiaiOddDerivNonnegLocal (q + 3) φ f) :
    HiaiEventualLocalBound (q + 1) φ f := by
  intro x _hx r _hr hball y hy
  have hyIoo : y ∈ Set.Ioo (-1 : ℝ) 1 := hball hy
  rcases hsuccNonneg y hyIoo with
    ⟨θ, hθ, hθleft, hθright, hsuccθ⟩
  rcases hthreeStepNonneg y hyIoo with
    ⟨χ, hχ, hχleft, hχright, hthreeStepχ⟩
  let lam : ℝ := min θ χ
  have hlam : 0 < lam := by
    dsimp [lam]
    exact lt_min hθ hχ
  have hlam_le_θ : lam ≤ θ := by
    dsimp [lam]
    exact min_le_left _ _
  have hlam_le_χ : lam ≤ χ := by
    dsimp [lam]
    exact min_le_right _ _
  have hlamleft : (-1 : ℝ) < y - lam := by
    nlinarith [hθleft, hχleft, hlam_le_θ, hlam_le_χ]
  have hlamright : y + lam < 1 := by
    nlinarith [hθright, hχright, hlam_le_θ, hlam_le_χ]
  have hball_lam : Metric.ball y lam ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro z hz
    have hzIoo : z ∈ Set.Ioo (y - lam) (y + lam) := by
      simpa [Real.ball_eq_Ioo] using hz
    constructor
    · exact lt_trans hlamleft hzIoo.1
    · exact lt_trans hzIoo.2 hlamright
  have hlocalBound := hbound y hyIoo lam hlam hball_lam
  have hyBallIoo : y ∈ Set.Ioo (x - r) (x + r) := by
    simpa [Real.ball_eq_Ioo] using hy
  let τ : ℝ := min (y - (x - r)) (x + r - y)
  have hτ : 0 < τ := by
    dsimp [τ]
    exact lt_min (by linarith [hyBallIoo.1]) (by linarith [hyBallIoo.2])
  let ρ : ℝ := min (lam / 8) (τ / 8)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by positivity) (by positivity)
  have hρ_le_lam_eighth : ρ ≤ lam / 8 := by
    dsimp [ρ]
    exact min_le_left _ _
  have hρ_le_τ_eighth : ρ ≤ τ / 8 := by
    dsimp [ρ]
    exact min_le_right _ _
  have h4ρ_lt_lam : 4 * ρ < lam := by nlinarith [hρ_le_lam_eighth, hlam]
  have h2ρ_lt_left : 2 * ρ < y - (x - r) := by
    have h2ρ_lt_τ : 2 * ρ < τ := by nlinarith [hρ_le_τ_eighth, hτ]
    have hτ_le_left : τ ≤ y - (x - r) := by
      dsimp [τ]
      exact min_le_left _ _
    exact lt_of_lt_of_le h2ρ_lt_τ hτ_le_left
  have h2ρ_lt_right : 2 * ρ < x + r - y := by
    have h2ρ_lt_τ : 2 * ρ < τ := by nlinarith [hρ_le_τ_eighth, hτ]
    have hτ_le_right : τ ≤ x + r - y := by
      dsimp [τ]
      exact min_le_right _ _
    exact lt_of_lt_of_le h2ρ_lt_τ hτ_le_right
  have hleft4 : (-1 : ℝ) < y - 4 * ρ := by
    nlinarith [hlamleft, h4ρ_lt_lam]
  have hright4 : y + 4 * ρ < 1 := by
    nlinarith [hlamright, h4ρ_lt_lam]
  let a : ℝ := y - 2 * ρ
  let b : ℝ := y + 2 * ρ
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith [hρ]
  have ha_lam : a ∈ Metric.ball y lam := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [a]
    rw [abs_of_nonpos (by linarith : y - 2 * ρ - y ≤ 0)]
    linarith
  have hb_lam : b ∈ Metric.ball y lam := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [b]
    rw [abs_of_nonneg (by linarith : 0 ≤ y + 2 * ρ - y)]
    linarith
  rcases hlocalBound a ha_lam with ⟨Ca, hCa, σa, hσa, _hσaSub, hbounda⟩
  rcases hlocalBound b hb_lam with ⟨Cb, hCb, σb, hσb, _hσbSub, hboundb⟩
  let B : ℝ := max Ca Cb
  have hB : 0 ≤ B := by
    dsimp [B]
    exact le_max_of_le_left hCa
  let A : ℝ := 2 * B
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hoscEv :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        |hiaiDeriv q φ ε f b -
          hiaiDeriv q φ ε f a| ≤ A := by
    filter_upwards [hbounda, hboundb] with ε hεa hεb
    have ha_self : a ∈ Metric.ball a σa := Metric.mem_ball_self hσa
    have hb_self : b ∈ Metric.ball b σb := Metric.mem_ball_self hσb
    have habsA := hεa a ha_self
    have habsB := hεb b hb_self
    have htri :
        |hiaiDeriv q φ ε f b -
          hiaiDeriv q φ ε f a| ≤
        |hiaiDeriv q φ ε f b| +
          |hiaiDeriv q φ ε f a| := by
      simpa [sub_eq_add_neg, abs_neg] using
        abs_add_le (hiaiDeriv q φ ε f b)
          (-(hiaiDeriv q φ ε f a))
    have hsum :
        |hiaiDeriv q φ ε f b| +
          |hiaiDeriv q φ ε f a| ≤ A := by
      have hCaB : Ca ≤ B := by dsimp [B]; exact le_max_left _ _
      have hCbB : Cb ≤ B := by dsimp [B]; exact le_max_right _ _
      have hA' : |hiaiDeriv q φ ε f a| ≤ B :=
        le_trans habsA hCaB
      have hB' : |hiaiDeriv q φ ε f b| ≤ B :=
        le_trans habsB hCbB
      dsimp [A]
      calc
        |hiaiDeriv q φ ε f b| +
            |hiaiDeriv q φ ε f a|
            ≤ B + B := add_le_add hB' hA'
        _ = 2 * B := by ring
    exact htri.trans hsum
  have hρsub : Metric.ball y ρ ⊆ Metric.ball x r := by
    intro z hz
    have hzIoo : z ∈ Set.Ioo (y - ρ) (y + ρ) := by
      simpa [Real.ball_eq_Ioo] using hz
    have hzBallIoo : z ∈ Set.Ioo (x - r) (x + r) := by
      constructor <;> linarith [hzIoo.1, hzIoo.2, h2ρ_lt_left, h2ρ_lt_right, hρ]
    simpa [Real.ball_eq_Ioo] using hzBallIoo
  refine ⟨A / ρ, by positivity, ρ, hρ, hρsub, ?_⟩
  have hderivQ :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ w ∈ Metric.ball y (4 * ρ),
        HasDerivAt (hiaiDeriv q φ ε f)
          (hiaiDeriv (q + 1) φ ε f w) w :=
    hiaiRegularization_hiaiDeriv_hasDerivAt_eventually_on_ball
      (q := q) (φ := φ) (f := f) hφ hpos y hyIoo
      (4 * ρ) (by positivity) hleft4 hright4
  have hderivQsucc :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ w ∈ Metric.ball y (4 * ρ),
        HasDerivAt (hiaiDeriv (q + 1) φ ε f)
          (hiaiDeriv (q + 2) φ ε f w) w :=
    hiaiRegularization_hiaiDeriv_hasDerivAt_eventually_on_ball
      (q := q + 1) (φ := φ) (f := f) hφ hpos y hyIoo
      (4 * ρ) (by positivity) hleft4 hright4
  have hderivQsuccsucc :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ w ∈ Metric.ball y (4 * ρ),
        HasDerivAt (hiaiDeriv (q + 2) φ ε f)
          (hiaiDeriv (q + 3) φ ε f w) w :=
    hiaiRegularization_hiaiDeriv_hasDerivAt_eventually_on_ball
      (q := q + 2) (φ := φ) (f := f) hφ hpos y hyIoo
      (4 * ρ) (by positivity) hleft4 hright4
  have hleftMargin : 0 < y - lam + 1 := by linarith [hlamleft]
  have hrightMargin : 0 < 1 - (y + lam) := by linarith [hlamright]
  have hε_left : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < y - lam + 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds hleftMargin)
  have hε_right : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 - (y + lam) :=
    nhdsWithin_le_nhds (Iio_mem_nhds hrightMargin)
  filter_upwards [self_mem_nhdsWithin, hε_left, hε_right,
    hsuccθ, hthreeStepχ, hoscEv, hderivQ, hderivQsucc, hderivQsuccsucc] with
    ε hεpos hεleft hεright hsuccε hthreeStepε hoscε hderivQε
      hderivQsuccε hderivQsuccsuccε
  intro z hz
  let Gε : ℝ → ℝ := hiaiDeriv q φ ε f
  let Fε : ℝ → ℝ := hiaiDeriv (q + 1) φ ε f
  have hball4_sub_lam : Metric.ball y (4 * ρ) ⊆ Metric.ball y lam := by
    intro w hw
    exact Metric.mem_ball.mpr <|
      lt_of_lt_of_le (Metric.mem_ball.mp hw) (le_of_lt h4ρ_lt_lam)
  have hball2_sub_4 : Metric.ball y (2 * ρ) ⊆ Metric.ball y (4 * ρ) := by
    intro w hw
    exact Metric.mem_ball.mpr <|
      lt_trans (Metric.mem_ball.mp hw) (by linarith [hρ])
  have hball4_sub_θ : Metric.ball y (4 * ρ) ⊆ Metric.ball y θ := by
    intro w hw
    exact Metric.mem_ball.mpr <|
      lt_of_lt_of_le (Metric.mem_ball.mp (hball4_sub_lam hw)) hlam_le_θ
  have hball4_sub_χ : Metric.ball y (4 * ρ) ⊆ Metric.ball y χ := by
    intro w hw
    exact Metric.mem_ball.mpr <|
      lt_of_lt_of_le (Metric.mem_ball.mp (hball4_sub_lam hw)) hlam_le_χ
  have hρ_to_ball2 : Metric.ball y ρ ⊆ Metric.ball y (2 * ρ) := by
    intro w hw
    exact Metric.mem_ball.mpr <|
      lt_trans (Metric.mem_ball.mp hw) (by linarith [hρ])
  have hIcc_ball4 : Set.Icc a b ⊆ Metric.ball y (4 * ρ) := by
    intro w hw
    have hwy : |w - y| ≤ 2 * ρ := by
      have hwleft : y - 2 * ρ ≤ w := by simpa [a] using hw.1
      have hwright : w ≤ y + 2 * ρ := by simpa [b] using hw.2
      rw [abs_le]
      constructor <;> linarith
    rw [Metric.mem_ball, Real.dist_eq]
    exact lt_of_le_of_lt hwy (by linarith [hρ])
  have hdiffF : DifferentiableOn ℝ Fε (Metric.ball y (2 * ρ)) := by
    intro w hw
    exact (hderivQsuccε w (hball2_sub_4 hw)).differentiableAt.differentiableWithinAt
  have hdiffNext :
      DifferentiableOn ℝ (hiaiDeriv (q + 2) φ ε f)
        (Metric.ball y (2 * ρ)) := by
    intro w hw
    exact (hderivQsuccsuccε w (hball2_sub_4 hw)).differentiableAt.differentiableWithinAt
  have hderiv_eq :
      ∀ w ∈ Metric.ball y (2 * ρ),
        deriv Fε w = hiaiDeriv (q + 2) φ ε f w := by
    intro w hw
    exact (hderivQsuccε w (hball2_sub_4 hw)).deriv
  have hdiffDerivF :
      DifferentiableOn ℝ (deriv Fε) (Metric.ball y (2 * ρ)) :=
    hdiffNext.congr (fun w hw => hderiv_eq w hw)
  have hconv : ConvexOn ℝ (Metric.ball y (2 * ρ)) Fε := by
    refine
      convexOn_of_deriv2_nonneg' (convex_ball y (2 * ρ))
        hdiffF hdiffDerivF ?_
    intro w hw
    change 0 ≤ deriv (deriv Fε) w
    have heqEvent :
        deriv Fε =ᶠ[𝓝 w] hiaiDeriv (q + 2) φ ε f := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hw] with t ht
      exact hderiv_eq t ht
    have hsecond_eq :
        deriv (deriv Fε) w =
          deriv (hiaiDeriv (q + 2) φ ε f) w :=
      heqEvent.deriv_eq
    have hsucc_deriv :=
      (hderivQsuccsuccε w (hball2_sub_4 hw)).deriv
    rw [hsecond_eq, hsucc_deriv]
    exact hthreeStepε w (hball4_sub_χ (hball2_sub_4 hw))
  have hnonnegF : ∀ w ∈ Metric.ball y (2 * ρ), 0 ≤ Fε w := by
    intro w hw
    exact hsuccε w (hball4_sub_θ (hball2_sub_4 hw))
  have hcontF : ContinuousOn Fε (Metric.ball y (2 * ρ)) := by
    intro w hw
    exact (hderivQsuccε w (hball2_sub_4 hw)).continuousAt.continuousWithinAt
  have hcontF_Icc : ContinuousOn Fε (Set.Icc a b) := by
    intro w hw
    exact (hderivQsuccε w (hIcc_ball4 hw)).continuousAt.continuousWithinAt
  have hbig_int : IntervalIntegrable Fε volume a b :=
    hcontF_Icc.intervalIntegrable_of_Icc hab
  have hFTC :
      ∫ w in a..b, Fε w = Gε b - Gε a := by
    have hderivIcc :
        ∀ w ∈ [[a, b]], HasDerivAt Gε (Fε w) w := by
      intro w hw
      have hwIcc : w ∈ Set.Icc a b := by
        simpa [Set.uIcc_of_le hab] using hw
      exact hderivQε w (hIcc_ball4 hwIcc)
    simpa [Gε, Fε] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := a) (b := b) (f := Gε) (f' := Fε) hderivIcc hbig_int
  have hintegral : ∫ w in a..b, Fε w ≤ A := by
    rw [hFTC]
    exact (le_abs_self _).trans hoscε
  have hinner :=
    convex_nonneg_abs_le_on_inner_ball_of_integral_le
      (F := Fε) (x := y) (ρ := ρ) (A := A)
      hρ hA hconv hnonnegF hcontF hbig_int hintegral z hz
  simpa [Fε] using hinner

/-! ### Canonical derivative-limit data -/
/-- Canonical pointwise candidate for the `q`th Hiai derivative limit. -/
noncomputable def hiaiRegularizationIteratedDerivLimit
    (q : ℕ) (φ f : ℝ → ℝ) (y : ℝ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ))
    (fun ε : ℝ => hiaiDeriv q φ ε f y)

/--
If the `q`th Hiai derivatives are Cauchy at one point, then they converge to
the canonical `limUnder` value there.
-/
theorem hiaiRegularization_hiaiDerivLimit_tendsto_of_pointwise_cauchy
    {q : ℕ} {φ f : ℝ → ℝ} {y : ℝ}
    (hcauchy :
      Cauchy
        (Filter.map
          (fun ε : ℝ => hiaiDeriv q φ ε f y)
          (𝓝[>] (0 : ℝ)))) :
    Filter.Tendsto
      (fun ε : ℝ => hiaiDeriv q φ ε f y)
      (𝓝[>] (0 : ℝ))
      (𝓝 (hiaiRegularizationIteratedDerivLimit q φ f y)) := by
  have hlim :
      ∃ L : ℝ,
        Filter.Tendsto
          (fun ε : ℝ => hiaiDeriv q φ ε f y)
          (𝓝[>] (0 : ℝ)) (𝓝 L) :=
    cauchy_map_iff_exists_tendsto.mp hcauchy
  simpa [hiaiRegularizationIteratedDerivLimit] using
    (tendsto_nhds_limUnder hlim)

/-- Locally uniform convergence interface for arbitrary Hiai derivative order. -/
theorem regularized_hiaiDeriv_tendstoLocallyUniformlyOn_of_eventual_local_uniformCauchy
    {q : ℕ} {φ f H : ℝ → ℝ} {x r : ℝ}
    (hpoint :
      ∀ y ∈ Metric.ball x r,
        Filter.Tendsto
          (fun ε : ℝ => hiaiDeriv q φ ε f y)
          (𝓝[>] (0 : ℝ)) (𝓝 (H y)))
    (hcauchy :
      ∀ η > 0, ∀ y ∈ Metric.ball x r,
        ∃ U ∈ 𝓝[Metric.ball x r] y,
          ∀ᶠ ε in 𝓝[>] (0 : ℝ),
            ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ z ∈ U,
              dist (hiaiDeriv q φ ε f z)
                (hiaiDeriv q φ δ f z) < η) :
    TendstoLocallyUniformlyOn
      (fun ε y : ℝ => hiaiDeriv q φ ε f y)
      H (𝓝[>] (0 : ℝ)) (Metric.ball x r) :=
  tendstoLocallyUniformlyOn_of_eventual_local_uniformCauchy_and_pointwise
    (F := fun ε y : ℝ => hiaiDeriv q φ ε f y)
    (G := H) (s := Metric.ball x r) hpoint hcauchy

/--
On a fixed ball compactly inside the normalized interval, arbitrary Hiai
derivative order is eventually continuous on the ball.
-/
theorem hiaiRegularization_hiaiDeriv_continuousOn_eventually_on_ball
    (q : ℕ) {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    {x r : ℝ} (hr : 0 < r)
    (hleft : (-1 : ℝ) < x - r) (hright : x + r < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ContinuousOn (fun y : ℝ => hiaiDeriv q φ ε f y)
        (Metric.ball x r) := by
  have hx : x ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor <;> linarith
  have hderiv :=
    hiaiRegularization_hiaiDeriv_hasDerivAt_eventually_on_ball
      (q := q) (φ := φ) (f := f) hφ hpos x hx r hr hleft hright
  filter_upwards [hderiv] with ε hε
  intro y hy
  exact (hε y hy).continuousAt.continuousWithinAt

/--
Local uniform-Cauchy control produces the continuous pointwise `limUnder` data
for arbitrary Hiai derivative order.
-/
theorem hiaiRegularization_hiaiDerivLimitData_of_eventual_local_uniformCauchy
    (q : ℕ) {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (hCauchy : HiaiEventualLocalUniformCauchy q φ f) :
    ∃ H : ℝ → ℝ,
      ContinuousOn H (Set.Ioo (-1 : ℝ) 1) ∧
        ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
          Filter.Tendsto
            (fun ε : ℝ => hiaiDeriv q φ ε f y)
            (𝓝[>] (0 : ℝ)) (𝓝 (H y)) := by
  let H : ℝ → ℝ := hiaiRegularizationIteratedDerivLimit q φ f
  have hpoint :
      ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ => hiaiDeriv q φ ε f y)
          (𝓝[>] (0 : ℝ)) (𝓝 (H y)) := by
    intro y hy
    rcases hCauchy y hy with ⟨r, hr, _hleft, _hright, huc⟩
    have hyball : y ∈ Metric.ball y r := Metric.mem_ball_self hr
    have hpointCauchy :
        Cauchy
          (Filter.map
            (fun ε : ℝ => hiaiDeriv q φ ε f y)
            (𝓝[>] (0 : ℝ))) := by
      exact pointwise_cauchy_of_eventual_local_uniformCauchy
        (F := fun ε z : ℝ => hiaiDeriv q φ ε f z)
        (x := y) (r := r) (y := y) hyball huc
    exact
      hiaiRegularization_hiaiDerivLimit_tendsto_of_pointwise_cauchy
        (q := q) (φ := φ) (f := f) (y := y) hpointCauchy
  have hcont : ContinuousOn H (Set.Ioo (-1 : ℝ) 1) := by
    refine continuousOn_of_locally_continuousOn ?_
    intro x hx
    rcases hCauchy x hx with ⟨r, hr, hleft, hright, huc⟩
    refine ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr, ?_⟩
    have hpointBall :
        ∀ y ∈ Metric.ball x r,
          Filter.Tendsto
            (fun ε : ℝ => hiaiDeriv q φ ε f y)
            (𝓝[>] (0 : ℝ)) (𝓝 (H y)) := by
      intro y hy
      have hyIoo : y ∈ Set.Ioo (-1 : ℝ) 1 := by
        have hyball : y ∈ Set.Ioo (x - r) (x + r) := by
          simpa [Real.ball_eq_Ioo] using hy
        constructor
        · exact lt_trans hleft hyball.1
        · exact lt_trans hyball.2 hright
      exact hpoint y hyIoo
    have hloc :
        TendstoLocallyUniformlyOn
          (fun ε y : ℝ => hiaiDeriv q φ ε f y)
          H (𝓝[>] (0 : ℝ)) (Metric.ball x r) :=
      regularized_hiaiDeriv_tendstoLocallyUniformlyOn_of_eventual_local_uniformCauchy
        (q := q) (φ := φ) (f := f) (H := H) (x := x) (r := r) hpointBall huc
    have hcontEv :=
      hiaiRegularization_hiaiDeriv_continuousOn_eventually_on_ball
        (q := q) (φ := φ) (f := f) hφ hpos hr hleft hright
    have hcontBall : ContinuousOn H (Metric.ball x r) :=
      hloc.continuousOn hcontEv.frequently
    exact hcontBall.mono Set.inter_subset_right
  exact ⟨H, hcont, hpoint⟩

/-! ### Successor limit identification -/
/--
Generic limit identification step: if order `q` regularized derivatives
converge pointwise to `f^[q]` and order `q+1` is locally uniform-Cauchy, then
the canonical order `q+1` limit is the actual derivative of `f^[q]`.
-/
theorem regularized_hiaiDeriv_succ_tendsto_of_pointwise_cauchy
    (q : ℕ) {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (hpoint :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        Filter.Tendsto
          (fun ε : ℝ => hiaiDeriv q φ ε f x)
          (𝓝[>] (0 : ℝ)) (𝓝 ((deriv^[q] f) x)))
    (hCauchySucc : HiaiEventualLocalUniformCauchy (q + 1) φ f) :
    ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      Filter.Tendsto
        (fun ε : ℝ => hiaiDeriv (q + 1) φ ε f y)
        (𝓝[>] (0 : ℝ)) (𝓝 ((deriv^[q + 1] f) y)) := by
  intro y hy
  rcases
    hiaiRegularization_hiaiDerivLimitData_of_eventual_local_uniformCauchy
      (q := q + 1) (φ := φ) (f := f) hφ hpos hCauchySucc with
    ⟨H, _hHcont, hHpoint⟩
  rcases hCauchySucc y hy with ⟨r, hr, hleft, hright, huc⟩
  have hball : Metric.ball y r ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro z hz
    have hzIoo : z ∈ Set.Ioo (y - r) (y + r) := by
      simpa [Real.ball_eq_Ioo] using hz
    constructor
    · exact lt_trans hleft hzIoo.1
    · exact lt_trans hzIoo.2 hright
  have hpointQ :
      ∀ z ∈ Metric.ball y r,
        Filter.Tendsto
          (fun ε : ℝ => hiaiDeriv q φ ε f z)
          (𝓝[>] (0 : ℝ)) (𝓝 ((deriv^[q] f) z)) := by
    intro z hz
    exact hpoint z (hball hz)
  have hpointH :
      ∀ z ∈ Metric.ball y r,
        Filter.Tendsto
          (fun ε : ℝ => hiaiDeriv (q + 1) φ ε f z)
          (𝓝[>] (0 : ℝ)) (𝓝 (H z)) := by
    intro z hz
    exact hHpoint z (hball hz)
  have hlocal :
      TendstoLocallyUniformlyOn
        (fun ε z : ℝ => hiaiDeriv (q + 1) φ ε f z)
        H (𝓝[>] (0 : ℝ)) (Metric.ball y r) :=
    regularized_hiaiDeriv_tendstoLocallyUniformlyOn_of_eventual_local_uniformCauchy
      (q := q + 1) (φ := φ) (f := f) (H := H) (x := y) (r := r) hpointH huc
  have hreg :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ Metric.ball y r,
        HasDerivAt (hiaiDeriv q φ ε f)
          (hiaiDeriv (q + 1) φ ε f z) z :=
    hiaiRegularization_hiaiDeriv_hasDerivAt_eventually_on_ball
      (q := q) (φ := φ) (f := f) hφ hpos y hy r hr hleft hright
  have hhas :
      HasDerivAt (deriv^[q] f) (H y) y :=
    hasDerivAt_of_tendstoLocallyUniformlyOn
      (f := fun ε z : ℝ => hiaiDeriv q φ ε f z)
      (g := deriv^[q] f)
      (f' := fun ε z : ℝ => hiaiDeriv (q + 1) φ ε f z)
      (g' := H)
      (s := Metric.ball y r) (l := 𝓝[>] (0 : ℝ))
      Metric.isOpen_ball hlocal hreg hpointQ (Metric.mem_ball_self hr)
  have hsucc_eq :
      (deriv^[q + 1] f) y = deriv (deriv^[q] f) y := by
    have hleft' :
        deriv (deriv^[q] f) = iteratedDeriv (q + 1) f := by
      rw [← iteratedDeriv_eq_iterate (n := q) (f := f), ← iteratedDeriv_succ]
    have hright' :
        (deriv^[q + 1] f) = iteratedDeriv (q + 1) f := by
      rw [← iteratedDeriv_eq_iterate (n := q + 1) (f := f)]
    exact congrFun (hright'.trans hleft'.symm) y
  have hyEq : (deriv^[q + 1] f) y = H y := by
    rw [hsucc_eq, hhas.deriv]
  simpa [hyEq] using hHpoint y hy

/-- Pointwise limit statement for an arbitrary regularized derivative order. -/
def HiaiPointwiseLimit
    (q : ℕ) (φ f : ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
    Filter.Tendsto
      (fun ε : ℝ => hiaiDeriv q φ ε f x)
      (𝓝[>] (0 : ℝ)) (𝓝 ((deriv^[q] f) x))

/--
Pointwise limit propagation for the Hiai derivative tower: once order `q`
converges pointwise and order `q+1` is locally uniform-Cauchy, the order
`q+1` pointwise limit is the actual iterated derivative of `f`.
-/
theorem hiaiPointwiseLimit_succ_of_localUniformCauchy
    (q : ℕ) {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (hpoint : HiaiPointwiseLimit q φ f)
    (hCauchySucc : HiaiEventualLocalUniformCauchy (q + 1) φ f) :
    HiaiPointwiseLimit (q + 1) φ f :=
  regularized_hiaiDeriv_succ_tendsto_of_pointwise_cauchy
    (q := q) (φ := φ) (f := f) hφ hpos hpoint hCauchySucc

/-! ### Public C1 handoff -/
/--
Generic `C¹` handoff for the `q`th public derivative from locally uniform
limits of the regularized `(q+1)`st derivatives.
-/
theorem hiaiDeriv_contDiffOn_one_of_regularized_hiaiDeriv_local_tendstoLocallyUniformlyOn
    (q : ℕ) {φ f H : ℝ → ℝ}
    (hpoint : HiaiPointwiseLimit q φ f)
    (hlocal :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 ∧
          TendstoLocallyUniformlyOn
            (fun ε y : ℝ => hiaiDeriv (q + 1) φ ε f y)
            H (𝓝[>] (0 : ℝ)) (Metric.ball x r) ∧
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
            HasDerivAt (hiaiDeriv q φ ε f)
              (hiaiDeriv (q + 1) φ ε f y) y))
    (hHcont : ContinuousOn H (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ 1 (deriv^[q] f) (Set.Ioo (-1 : ℝ) 1) := by
  have hdiff :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        HasDerivAt (deriv^[q] f) (H x) x := by
    intro x hx
    rcases hlocal x hx with ⟨r, hr, hball_sub, hsucc, hreg⟩
    exact
      hasDerivAt_of_tendstoLocallyUniformlyOn
        (f := fun ε y : ℝ => hiaiDeriv q φ ε f y)
        (g := deriv^[q] f)
        (f' := fun ε y : ℝ => hiaiDeriv (q + 1) φ ε f y)
        (g' := H)
        (s := Metric.ball x r) (l := 𝓝[>] (0 : ℝ))
        Metric.isOpen_ball hsucc hreg
        (by
          intro y hy
          exact hpoint y (hball_sub hy))
        (Metric.mem_ball_self hr)
  have hdiffOn :
      DifferentiableOn ℝ (deriv^[q] f) (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    exact (hdiff x hx).differentiableAt.differentiableWithinAt
  have hderiv_eq :
      Set.EqOn (deriv (deriv^[q] f)) H (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    exact (hdiff x hx).deriv
  have hderiv_cont :
      ContinuousOn (deriv (deriv^[q] f)) (Set.Ioo (-1 : ℝ) 1) :=
    hHcont.congr hderiv_eq
  have h :
      ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1) (deriv^[q] f)
        (Set.Ioo (-1 : ℝ) 1) := by
    rw [contDiffOn_succ_iff_deriv_of_isOpen
      (n := (0 : WithTop ℕ∞)) (f := deriv^[q] f) isOpen_Ioo]
    refine ⟨hdiffOn, ?_, ?_⟩
    · intro htop
      cases htop
    · exact contDiffOn_zero.2 hderiv_cont
  simpa using h

/-! ### ContDiff successor assembly -/
private theorem contDiffOn_succ_of_iteratedDeriv_contDiffOn_one_core
    {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) (n : ℕ)
    (hf : ContDiffOn ℝ n f s)
    (htop : ContDiffOn ℝ 1 (deriv^[n] f) s) :
    ContDiffOn ℝ (n + 1) f s := by
  induction n generalizing f with
  | zero =>
      simpa using htop
  | succ n ih =>
      have hderivBase : ContDiffOn ℝ n (deriv f) s := by
        simpa [Function.iterate_succ_apply] using
          hf.deriv_of_isOpen (m := n) hs (by
            exact natCast_withTopENat_le (Nat.le_refl (n + 1)))
      have htopDeriv : ContDiffOn ℝ 1 (deriv^[n] (deriv f)) s := by
        simpa [Function.iterate_succ_apply] using htop
      have hderivHigh : ContDiffOn ℝ (n + 1) (deriv f) s :=
        ih hderivBase htopDeriv
      have hdiff : DifferentiableOn ℝ f s :=
        hf.differentiableOn (by
          norm_num)
      have h :
          ContDiffOn ℝ ((n + 1 : WithTop ℕ∞) + 1) f s := by
        rw [contDiffOn_succ_iff_deriv_of_isOpen
          (n := (n + 1 : WithTop ℕ∞)) (f := f) hs]
        refine ⟨hdiff, ?_, ?_⟩
        · intro htopEq
          cases htopEq
        · simpa using hderivHigh
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using h

/--
Generic public successor step, conditional on pointwise convergence at order
`q` and local uniform-Cauchy control at order `q+1`.
-/
theorem publicSuccRegularity_of_hiaiDerivLocalUniformCauchyData
    (q : ℕ) {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (hf : ContDiffOn ℝ q f (Set.Ioo (-1 : ℝ) 1))
    (hpoint : HiaiPointwiseLimit q φ f)
    (hCauchySucc : HiaiEventualLocalUniformCauchy (q + 1) φ f) :
    ContDiffOn ℝ (q + 1) f (Set.Ioo (-1 : ℝ) 1) := by
  rcases
    hiaiRegularization_hiaiDerivLimitData_of_eventual_local_uniformCauchy
      (q := q + 1) (φ := φ) (f := f) hφ hpos hCauchySucc with
    ⟨H, hHcont, hHpoint⟩
  have hlocal :
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 ∧
          TendstoLocallyUniformlyOn
            (fun ε y : ℝ => hiaiDeriv (q + 1) φ ε f y)
            H (𝓝[>] (0 : ℝ)) (Metric.ball x r) ∧
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
            HasDerivAt (hiaiDeriv q φ ε f)
              (hiaiDeriv (q + 1) φ ε f y) y) := by
    intro x hx
    rcases hCauchySucc x hx with ⟨r, hr, hleft, hright, huc⟩
    have hball : Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 := by
      intro y hy
      have hyIoo : y ∈ Set.Ioo (x - r) (x + r) := by
        simpa [Real.ball_eq_Ioo] using hy
      constructor
      · exact lt_trans hleft hyIoo.1
      · exact lt_trans hyIoo.2 hright
    refine ⟨r, hr, hball, ?_, ?_⟩
    · have hpointBall :
          ∀ y ∈ Metric.ball x r,
            Filter.Tendsto
              (fun ε : ℝ => hiaiDeriv (q + 1) φ ε f y)
              (𝓝[>] (0 : ℝ)) (𝓝 (H y)) := by
        intro y hy
        exact hHpoint y (hball hy)
      exact
        regularized_hiaiDeriv_tendstoLocallyUniformlyOn_of_eventual_local_uniformCauchy
          (q := q + 1) (φ := φ) (f := f) (H := H)
          (x := x) (r := r) hpointBall huc
    · exact
        hiaiRegularization_hiaiDeriv_hasDerivAt_eventually_on_ball
          (q := q) (φ := φ) (f := f) hφ hpos x hx r hr hleft hright
  have htop :
      ContDiffOn ℝ 1 (deriv^[q] f) (Set.Ioo (-1 : ℝ) 1) :=
    hiaiDeriv_contDiffOn_one_of_regularized_hiaiDeriv_local_tendstoLocallyUniformlyOn
      (q := q) (φ := φ) (f := f) (H := H) hpoint hlocal hHcont
  exact
    contDiffOn_succ_of_iteratedDeriv_contDiffOn_one_core
      (f := f) (s := Set.Ioo (-1 : ℝ) 1) isOpen_Ioo q hf htop


end

end Quantum.TraceInequality.Loewner
