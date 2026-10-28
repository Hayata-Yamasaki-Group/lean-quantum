import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.FiniteOrderLadderCore

/-!
# Chapter 20 public finite-order ladder

This file contains the public induction state, odd-derivative source,
and theorem-facing finite-order regularity wrappers.  The generic Hiai
derivative propagation lemmas live in `FiniteOrderLadderCore`.
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

private lemma natCast_withTopENat_le {m n : ℕ} (h : m ≤ n) :
    (m : WithTop ℕ∞) ≤ (n : ℕ) :=
  WithTop.coe_le_coe.mpr (WithTop.coe_le_coe.mpr h)

/--
Lightweight induction state for the finite-order ladder.  Unlike the older
state, this keeps the pointwise limit datum needed by the generic successor
step.
-/
structure PublicRegularityInductionState (n : ℕ) (f : ℝ → ℝ) : Prop where
  regularity : ContDiffOn ℝ n f (Set.Ioo (-1 : ℝ) 1)
  pointwise :
    ∀ {φ : ℝ → ℝ}, HiaiMollifier φ →
      HiaiPointwiseLimit n φ f
  nextBound :
    ∀ {φ : ℝ → ℝ}, HiaiMollifier φ →
      HiaiEventualLocalBound (n + 1) φ f

/--
The low-order base state used by the finite-order ladder.  It packages the
closed C3 regularity, the pointwise `Rε''' → f'''` limit, and the fourth
regularized-derivative local bound.
-/
theorem publicRegularityInductionState3_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    PublicRegularityInductionState 3 f where
  regularity := publicC3Regularity_of_loewnerPosOnUnitInterval hpos
  pointwise := by
    intro φ hφ
    simpa [HiaiPointwiseLimit, hiaiDeriv] using
      regularized_thirdDeriv_tendsto_of_loewnerPosOnUnitInterval
        (φ := φ) (f := f) hφ hpos
  nextBound := by
    intro φ hφ
    simpa [HiaiEventualLocalBound, hiaiDeriv] using
      hiaiRegularization_fourthDeriv_bound_eventually_local_of_loewnerPosOnUnitInterval
        (φ := φ) (f := f) hφ hpos

/--
Generic successor for the lightweight state once the next local bound has been
produced by the parity-specific bound step.
-/
theorem publicRegularityInductionState_succ_of_nextBound
    (n : ℕ) {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (state : PublicRegularityInductionState n f)
    (hnext :
      ∀ {φ : ℝ → ℝ}, HiaiMollifier φ →
        HiaiEventualLocalBound (n + 2) φ f) :
    PublicRegularityInductionState (n + 1) f where
  regularity := by
    rcases exists_hiaiMollifier with ⟨φ, hφ⟩
    have hCauchy :
        HiaiEventualLocalUniformCauchy (n + 1) φ f :=
      hiaiDeriv_localUniformCauchy_of_nextDeriv_bound
        (q := n) (φ := φ) (f := f) (g := deriv^[n] f)
        (state.pointwise hφ)
        (hiaiRegularization_hiaiDeriv_hasDerivAt_eventually_on_balls
          (q := n) (φ := φ) (f := f) hφ hpos)
        (hiaiRegularization_hiaiDeriv_hasDerivAt_eventually_on_balls
          (q := n + 1) (φ := φ) (f := f) hφ hpos)
        (hnext hφ)
    exact
      publicSuccRegularity_of_hiaiDerivLocalUniformCauchyData
        (q := n) (φ := φ) (f := f) hφ hpos state.regularity
        (state.pointwise hφ) hCauchy
  pointwise := by
    intro φ hφ
    have hCauchy :
        HiaiEventualLocalUniformCauchy (n + 1) φ f :=
      hiaiDeriv_localUniformCauchy_of_nextDeriv_bound
        (q := n) (φ := φ) (f := f) (g := deriv^[n] f)
        (state.pointwise hφ)
        (hiaiRegularization_hiaiDeriv_hasDerivAt_eventually_on_balls
          (q := n) (φ := φ) (f := f) hφ hpos)
        (hiaiRegularization_hiaiDeriv_hasDerivAt_eventually_on_balls
          (q := n + 1) (φ := φ) (f := f) hφ hpos)
        (hnext hφ)
    exact
      hiaiPointwiseLimit_succ_of_localUniformCauchy
        (q := n) (φ := φ) (f := f) hφ hpos (state.pointwise hφ) hCauchy
  nextBound := by
    intro φ hφ
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext hφ

/--
Public odd-derivative source needed by the finite-order ladder.

This predicate is filled by
`oddIteratedDeriv_nonneg_of_loewnerPosOnUnitInterval` below, via the
forward finite-difference confluent-diagonal limit.
-/
def OddIteratedDerivNonnegSource : Prop :=
  ∀ q : ℕ, q % 2 = 1 →
    ∀ {g : ℝ → ℝ}, LoewnerPosOnUnitInterval g →
      ContDiffOn ℝ q g (Set.Ioo (-1 : ℝ) 1) →
        ∀ z ∈ Set.Ioo (-1 : ℝ) 1, 0 ≤ (deriv^[q] g) z

/--
Odd iterated derivatives are nonnegative on the unit interval, obtained from
the forward finite-difference confluent-diagonal limit.
-/
theorem oddIteratedDeriv_nonneg_of_loewnerPosOnUnitInterval
    (q : ℕ) (hq : q % 2 = 1)
    {g : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval g)
    (hCq : ContDiffOn ℝ q g (Set.Ioo (-1 : ℝ) 1))
    {z : ℝ} (hz : z ∈ Set.Ioo (-1 : ℝ) 1) :
    0 ≤ (deriv^[q] g) z := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q = 2 * k + 1 := by
    use q / 2
    omega
  subst q
  have hlim :=
    forward_topCoeffQuadratic_tendsto_confluentDiagonal
      (f := g) (k := k) hCq hz
  have hquad :=
    forward_topCoeffQuadratic_nonneg_eventually_of_loewnerPosOnUnitInterval
      (f := g) (k := k) hpos hz
  have hcoeff :
      0 ≤ (deriv^[2 * k] (deriv g)) z /
        (Nat.factorial (2 * k + 1) : ℝ) :=
    ge_of_tendsto hlim hquad
  have hfactpos : 0 < (Nat.factorial (2 * k + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 * k + 1)
  have hnonneg : 0 ≤ (deriv^[2 * k] (deriv g)) z := by
    have hmul :=
      mul_nonneg hcoeff hfactpos.le
    have hcancel :
        ((deriv^[2 * k] (deriv g)) z /
            (Nat.factorial (2 * k + 1) : ℝ)) *
          (Nat.factorial (2 * k + 1) : ℝ) =
        (deriv^[2 * k] (deriv g)) z := by
      field_simp [ne_of_gt hfactpos]
    simpa [hcancel] using hmul
  have hiter :
      (deriv^[2 * k] (deriv g)) z =
        deriv (deriv^[2 * k] g) z := by
    have hleft :
        (deriv^[2 * k] (deriv g)) =
          iteratedDeriv (2 * k + 1) g := by
      rw [← iteratedDeriv_eq_iterate (n := 2 * k) (f := deriv g),
        ← iteratedDeriv_succ']
    have hright :
        deriv (deriv^[2 * k] g) =
          iteratedDeriv (2 * k + 1) g := by
      rw [← iteratedDeriv_eq_iterate (n := 2 * k) (f := g),
        ← iteratedDeriv_succ]
    exact congrFun (hleft.trans hright.symm) z
  have hsucc :
      (deriv^[2 * k + 1] g) z =
        deriv (deriv^[2 * k] g) z := by
    have hleft :
        (deriv^[2 * k + 1] g) =
          iteratedDeriv (2 * k + 1) g := by
      rw [← iteratedDeriv_eq_iterate (n := 2 * k + 1) (f := g)]
    have hright :
        deriv (deriv^[2 * k] g) =
          iteratedDeriv (2 * k + 1) g := by
      rw [← iteratedDeriv_eq_iterate (n := 2 * k) (f := g),
        ← iteratedDeriv_succ]
    exact congrFun (hleft.trans hright.symm) z
  simpa [hsucc, hiter] using hnonneg

/--
Package the odd-derivative nonnegativity theorem as the source predicate used
by the finite-order ladder.
-/
theorem oddIteratedDerivNonnegSource_of_loewnerPosOnUnitInterval :
    OddIteratedDerivNonnegSource := by
  intro q hq g hpos hCq z hz
  exact
    oddIteratedDeriv_nonneg_of_loewnerPosOnUnitInterval
      q hq hpos hCq hz

/--
Parity split for the next local-bound producer.

For `q = n + 1`, an odd `q` uses nonnegativity of `q` and `q+2`; an even
`q` uses nonnegativity of `q+1` and `q+3`.  This is the generic C15 step from
the previous commit, now packaged for arbitrary successor stages.
-/
theorem regularization_nextBound_of_oddIteratedDerivNonnegSource
    (hsource : OddIteratedDerivNonnegSource)
    (n : ℕ) {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f)
    (state : PublicRegularityInductionState n f) :
    HiaiEventualLocalBound (n + 2) φ f := by
  let q : ℕ := n + 1
  have hboundq : HiaiEventualLocalBound q φ f := by
    simpa [q] using state.nextBound hφ
  by_cases hqeven : q % 2 = 0
  · have hq1odd : (q + 1) % 2 = 1 := by omega
    have hq3odd : (q + 3) % 2 = 1 := by omega
    have hsuccNonneg : HiaiOddDerivNonnegLocal (q + 1) φ f :=
      hiaiRegularization_hiaiDeriv_nonneg_eventually_local_of_source
        (q := q + 1) (hsource (q + 1) hq1odd) (φ := φ) (f := f) hφ hpos
    have hthreeStepNonneg :
        HiaiOddDerivNonnegLocal (q + 3) φ f :=
      hiaiRegularization_hiaiDeriv_nonneg_eventually_local_of_source
        (q := q + 3) (hsource (q + 3) hq3odd) (φ := φ) (f := f) hφ hpos
    have hnext :=
      regularization_succDeriv_bound_eventually_local_of_bound_succ_nonneg_threeStep
        (q := q) (φ := φ) (f := f) hφ hpos hboundq
        hsuccNonneg hthreeStepNonneg
    simpa [q, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext
  · have hqodd : q % 2 = 1 := by omega
    have hq2odd : (q + 2) % 2 = 1 := by omega
    have hnonneg : HiaiOddDerivNonnegLocal q φ f :=
      hiaiRegularization_hiaiDeriv_nonneg_eventually_local_of_source
        (q := q) (hsource q hqodd) (φ := φ) (f := f) hφ hpos
    have htwoStepNonneg : HiaiOddDerivNonnegLocal (q + 2) φ f :=
      hiaiRegularization_hiaiDeriv_nonneg_eventually_local_of_source
        (q := q + 2) (hsource (q + 2) hq2odd) (φ := φ) (f := f) hφ hpos
    have hnext :=
      regularization_succDeriv_bound_eventually_local_of_bound_nonneg_twoStep
        (q := q) (φ := φ) (f := f) hφ hpos hboundq hnonneg
        htwoStepNonneg
    simpa [q, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext

/--
Generic finite-order induction state from an arbitrary base.  The Löwner
positivity hypothesis is kept explicit because the successor and parity-bound
producers both use it.
-/
theorem publicRegularityInductionState_from_base_of_oddIteratedDerivNonnegSource
    {n0 : ℕ} {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (state0 : PublicRegularityInductionState n0 f)
    (hsource : OddIteratedDerivNonnegSource) :
    ∀ d : ℕ, PublicRegularityInductionState (n0 + d) f := by
  intro d
  induction d with
  | zero =>
      simpa using state0
  | succ d ih =>
      have hnext :
          ∀ {φ : ℝ → ℝ}, HiaiMollifier φ →
            HiaiEventualLocalBound ((n0 + d) + 2) φ f := by
        intro φ hφ
        exact
          regularization_nextBound_of_oddIteratedDerivNonnegSource
            hsource (n := n0 + d) (φ := φ) (f := f) hφ hpos ih
      have hsucc :=
        publicRegularityInductionState_succ_of_nextBound
          (n := n0 + d) (f := f) hpos ih hnext
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsucc

/--
Public Löwner positivity gives finite-order smoothness of every order on the
open unit interval.
-/
theorem publicFiniteOrderRegularity_of_loewnerPosOnUnitInterval
    (m : ℕ) {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    ContDiffOn ℝ m f (Set.Ioo (-1 : ℝ) 1) := by
  let state3 :=
    publicRegularityInductionState3_of_loewnerPosOnUnitInterval
      (f := f) hpos
  by_cases hm : m ≤ 3
  · exact
      state3.regularity.of_le (natCast_withTopENat_le hm)
  · have h3le : 3 ≤ m := by omega
    rcases Nat.exists_eq_add_of_le h3le with ⟨d, rfl⟩
    exact
      (publicRegularityInductionState_from_base_of_oddIteratedDerivNonnegSource
        hpos state3 oddIteratedDerivNonnegSource_of_loewnerPosOnUnitInterval d).regularity

/-- Public finite-order regularity, with the former odd-derivative source input closed. -/
theorem publicFiniteOrderRegularity_of_oddIteratedDerivNonnegSource
    (m : ℕ) {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    ContDiffOn ℝ m f (Set.Ioo (-1 : ℝ) 1) :=
  publicFiniteOrderRegularity_of_loewnerPosOnUnitInterval m hpos


end

end Quantum.TraceInequality.Loewner
