import Quantum.TraceInequality.Loewner.UnitInterval.HardDirection.LimitTransfer

/-!
# Chapter 20 book-route bridge consumers

This file keeps the theorem-facing bridge consumers for the Chapter 20
book-route hard direction.  The strict input, route contracts, smooth
approximants, and limit-transfer machinery are split into the
`UnitInterval.HardDirection` subdirectory.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory
open Filter

open scoped NNReal
open scoped Topology
open scoped BoundedContinuousFunction
open scoped ComplexOrder
open scoped Matrix
open scoped MatrixOrder

noncomputable section

/--
The concrete approximant has the book derivative formula at the anchor `0`.
This is the differential identity behind equation (20.5).
-/
theorem bookSmoothApprox_hasDerivAt_zero_of_globalStrictPosDef
    {f : ℝ → ℝ} (hf : GlobalStrictPosDef f) (ε δ : ℝ) :
    HasDerivAt (bookSmoothApprox f ε δ)
      ((1 - δ) * deriv f 0 + ε * deriv bookG0 0) 0 := by
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  have hdf := (differentiableAt_of_globalStrictPosDef hf h0mem).hasDerivAt
  have hdf_arg : HasDerivAt f (deriv f 0) ((1 - δ) * 0) := by
    simpa using hdf
  have hlin : HasDerivAt (fun x : ℝ => (1 - δ) * x) (1 - δ) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (1 - δ)
  have hscaled :
      HasDerivAt (fun x : ℝ => f ((1 - δ) * x)) ((1 - δ) * deriv f 0) 0 := by
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
      hdf_arg.comp 0 hlin
  have hg0raw :=
    (bookG0_hasDerivAt_of_lt_two (x := (0 : ℝ)) (by norm_num)).const_mul ε
  have hg0 :
      HasDerivAt (fun x : ℝ => ε * bookG0 x)
        (ε * deriv bookG0 0) 0 := by
    simpa [bookG0_deriv_eq_of_lt_two (x := (0 : ℝ)) (by norm_num)] using
      hg0raw
  simpa [bookSmoothApprox] using hscaled.add hg0

/-- Derivative form of the book identity for `f_{ε,δ}` at `0`. -/
theorem bookSmoothApprox_deriv_zero_eq_of_globalStrictPosDef
    {f : ℝ → ℝ} (hf : GlobalStrictPosDef f) (ε δ : ℝ) :
    deriv (bookSmoothApprox f ε δ) 0 =
      (1 - δ) * deriv f 0 + ε * deriv bookG0 0 :=
  (bookSmoothApprox_hasDerivAt_zero_of_globalStrictPosDef hf ε δ).deriv

/--
The book derivative identity is bounded by the derivative of `f` at `0` plus
the size of the positive perturbation parameter.
-/
theorem bookSmoothApprox_deriv_zero_bound_of_globalStrictPosDef
    {f : ℝ → ℝ} (hf : GlobalStrictPosDef f) {ε δ : ℝ} {Kf E : ℝ≥0}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (hε : 0 ≤ ε)
    (hKf : ENNReal.ofReal (deriv f 0) ≤ (Kf : ENNReal))
    (hE : ENNReal.ofReal ε ≤ (E : ENNReal)) :
    ENNReal.ofReal (deriv (bookSmoothApprox f ε δ) 0) ≤
      ((Kf + E : ℝ≥0) : ENNReal) := by
  have hderiv_pos : 0 ≤ deriv f 0 :=
    (deriv_pos_of_globalStrictPosDef hf
      (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1)).le
  have hscale_le_one : 1 - δ ≤ 1 := by linarith [hδ.1]
  have hscaled_le : (1 - δ) * deriv f 0 ≤ deriv f 0 :=
    mul_le_of_le_one_left hderiv_pos hscale_le_one
  have hg0_le : deriv bookG0 0 ≤ 1 :=
    bookG0_deriv_le_one_on_Icc 0 (by norm_num)
  have heps_le : ε * deriv bookG0 0 ≤ ε :=
    mul_le_of_le_one_right hε hg0_le
  rw [bookSmoothApprox_deriv_zero_eq_of_globalStrictPosDef hf ε δ]
  calc
    ENNReal.ofReal ((1 - δ) * deriv f 0 + ε * deriv bookG0 0)
        ≤ ENNReal.ofReal ((1 - δ) * deriv f 0) +
            ENNReal.ofReal (ε * deriv bookG0 0) :=
          ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (deriv f 0) + ENNReal.ofReal ε :=
          add_le_add (ENNReal.ofReal_le_ofReal hscaled_le)
            (ENNReal.ofReal_le_ofReal heps_le)
    _ ≤ (Kf : ENNReal) + (E : ENNReal) :=
          add_le_add hKf hE
    _ = ((Kf + E : ℝ≥0) : ENNReal) := by
          simp

/--
A scaled-regularity producer, a bound for `f'(0)`, and a uniform bound for the
book perturbation parameters supply the derivative mass-bound package.
-/
noncomputable def
    bookScaledRegularityDerivativeMassBoundInput_of_deriv_zero_bounds
    {f : ℝ → ℝ}
    (toScaledRegularity :
      GlobalStrictPosDef f → BookScaledRegularityFamilyInput f)
    (Kf E : GlobalStrictPosDef f → ℝ≥0)
    (hKf :
      ∀ h : GlobalStrictPosDef f, ENNReal.ofReal (deriv f 0) ≤ (Kf h : ENNReal))
    (hE :
      ∀ h : GlobalStrictPosDef f, ∀ n : ℕ,
        ENNReal.ofReal ((toScaledRegularity h).epsilon n) ≤ (E h : ENNReal)) :
    BookScaledRegularityDerivativeMassBoundInput f :=
  bookScaledRegularityDerivativeMassBoundInput_of_deriv_bound
    toScaledRegularity (fun h => Kf h + E h) (by
      intro h n
      exact
        bookSmoothApprox_deriv_zero_bound_of_globalStrictPosDef h
          ((toScaledRegularity h).delta_mem_Ioo n)
          ((toScaledRegularity h).epsilon_pos n).le
          (hKf h) (hE h n))

/--
Since `GlobalStrictPosDef` already makes `f'(0)` positive and finite, the only
other scalar input for the derivative mass-bound package is a uniform bound
for the perturbation parameters `ε_n`; it is supplied from `ε_n → 0` in
`bookScaledRegularityDerivativeMassBoundInput_of_scaledRegularity` below.
-/
noncomputable def
    bookScaledRegularityDerivativeMassBoundInput_of_epsilon_bound
    {f : ℝ → ℝ}
    (toScaledRegularity :
      GlobalStrictPosDef f → BookScaledRegularityFamilyInput f)
    (E : GlobalStrictPosDef f → ℝ≥0)
    (hE :
      ∀ h : GlobalStrictPosDef f, ∀ n : ℕ,
        ENNReal.ofReal ((toScaledRegularity h).epsilon n) ≤ (E h : ENNReal)) :
    BookScaledRegularityDerivativeMassBoundInput f :=
  bookScaledRegularityDerivativeMassBoundInput_of_deriv_zero_bounds
    toScaledRegularity (fun _h => Real.toNNReal (deriv f 0)) E
    (by
      intro _h
      rw [ENNReal.ofNNReal_toNNReal])
    hE

/--
A perturbation sequence tending to `0` is uniformly bounded as an `ENNReal`
sequence.  This supplies the last scalar input left by the derivative
mass-bound reduction.
-/
theorem book_exists_epsilon_bound_of_tendsto_zero
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    ∃ E : ℝ≥0, ∀ n : ℕ, ENNReal.ofReal (ε n) ≤ (E : ENNReal) := by
  have hlt_eventually : ∀ᶠ n : ℕ in atTop, ε n < 1 :=
    hε.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  rcases Filter.eventually_atTop.1 hlt_eventually with ⟨N, hN⟩
  let s : Finset ℕ := Finset.range (N + 1)
  have hs : s.Nonempty := by
    refine ⟨0, ?_⟩
    simp [s]
  let B : ℝ := max 1 (s.sup' hs ε)
  refine ⟨Real.toNNReal B, ?_⟩
  intro n
  have hnle : ε n ≤ B := by
    by_cases hn : n < N + 1
    · have hmem : n ∈ s := by
        simpa [s] using hn
      have hle_sup : ε n ≤ s.sup' hs ε := by
        exact (Finset.le_sup'_iff (s := s) (H := hs) (f := ε)).2
          ⟨n, hmem, le_rfl⟩
      exact hle_sup.trans (le_max_right 1 (s.sup' hs ε))
    · have hNle : N ≤ n :=
        Nat.le_trans (Nat.le_succ N) (not_lt.mp hn)
      have htail : ε n < 1 := hN n hNle
      exact (le_of_lt htail).trans (le_max_left 1 (s.sup' hs ε))
  rw [ENNReal.ofNNReal_toNNReal]
  exact ENNReal.ofReal_le_ofReal hnle

/--
The scaled-regularity package already contains `ε_n → 0`, so it supplies the
uniform perturbation bound required by the derivative-style input.
-/
noncomputable def
    bookScaledRegularityDerivativeMassBoundInput_of_scaledRegularity
    {f : ℝ → ℝ}
    (toScaledRegularity :
      GlobalStrictPosDef f → BookScaledRegularityFamilyInput f) :
    BookScaledRegularityDerivativeMassBoundInput f :=
  bookScaledRegularityDerivativeMassBoundInput_of_epsilon_bound
    toScaledRegularity
    (fun h =>
      Classical.choose
        (book_exists_epsilon_bound_of_tendsto_zero
          (toScaledRegularity h).epsilon_tendsto_zero))
    (by
      intro h n
      exact
        (Classical.choose_spec
          (book_exists_epsilon_bound_of_tendsto_zero
            (toScaledRegularity h).epsilon_tendsto_zero)) n)

/--
The packaged scaled-regularity and compactness-level measure-limit inputs give
the abstract book-route bridge.
-/
noncomputable def bookRouteBridge_of_scaledRegularityMeasureLimitInput
    {f : ℝ → ℝ} (input : BookScaledRegularityMeasureLimitInput f) :
    BookRouteBridge f :=
  bookRouteBridge_of_scaledRegularityLimitTransferInput
    (bookScaledRegularityLimitTransferInput_of_measureLimitInput input)

/--
The packaged scaled-regularity and separated compactness/kernel-convergence
inputs give the abstract book-route bridge.
-/
noncomputable def bookRouteBridge_of_scaledRegularityKernelConvergenceInput
    {f : ℝ → ℝ} (input : BookScaledRegularityKernelConvergenceInput f) :
    BookRouteBridge f :=
  bookRouteBridge_of_scaledRegularityMeasureLimitInput
    (bookScaledRegularityMeasureLimitInput_of_kernelConvergenceInput input)

/--
The packaged scaled-regularity and measure-compactness inputs give the abstract
book-route bridge.
-/
noncomputable def bookRouteBridge_of_scaledRegularityMeasureCompactnessInput
    {f : ℝ → ℝ} (input : BookScaledRegularityMeasureCompactnessInput f) :
    BookRouteBridge f :=
  bookRouteBridge_of_scaledRegularityKernelConvergenceInput
    (bookScaledRegularityKernelConvergenceInput_of_measureCompactnessInput
      input)

/--
The packaged scaled-regularity and mass-bound inputs give the abstract
book-route bridge.
-/
noncomputable def bookRouteBridge_of_scaledRegularityMassBoundInput
    {f : ℝ → ℝ} (input : BookScaledRegularityMassBoundInput f) :
    BookRouteBridge f :=
  bookRouteBridge_of_scaledRegularityMeasureCompactnessInput
    (bookScaledRegularityMeasureCompactnessInput_of_massBoundInput input)

/--
The packaged scaled-regularity and derivative-style mass-bound inputs give the
abstract book-route bridge.
-/
noncomputable def bookRouteBridge_of_scaledRegularityDerivativeMassBoundInput
    {f : ℝ → ℝ} (input : BookScaledRegularityDerivativeMassBoundInput f) :
    BookRouteBridge f :=
  bookRouteBridge_of_scaledRegularityMassBoundInput
    (bookScaledRegularityMassBoundInput_of_derivativeMassBoundInput input)

/--
A scaled-regularity producer alone supplies the derivative mass-bound bridge
input, because `ε_n → 0` gives the uniform perturbation bound.
-/
noncomputable def bookRouteBridge_of_scaledRegularityProducer
    {f : ℝ → ℝ}
    (toScaledRegularity :
      GlobalStrictPosDef f → BookScaledRegularityFamilyInput f) :
    BookRouteBridge f :=
  bookRouteBridge_of_scaledRegularityDerivativeMassBoundInput
    (bookScaledRegularityDerivativeMassBoundInput_of_scaledRegularity
      toScaledRegularity)

/--
Consumer for the Theorem 20.1-style bridge: the smooth strict case is supplied
by the implemented Chapter 27 book-route package.
-/
noncomputable def integralRepOnUnitInterval_of_globalStrictPosDef_of_bookRouteBridge
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) (bridge : BookRouteBridge f) :
    IntegralRepOnUnitInterval f :=
  bridge.reduction h fun _ hg =>
    integralRepOnUnitInterval_of_smoothStrictBookRouteInput hg

/--
Conditional strict hard-direction consumer from a scaled-regularity producer.
The perturbation bound and the derivative-style mass-bound side are now
supplied internally from `ε_n → 0`.
-/
noncomputable def
    integralRepOnUnitInterval_of_globalStrictPosDef_of_bookScaledRegularityProducer
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f)
    (toScaledRegularity :
      GlobalStrictPosDef f → BookScaledRegularityFamilyInput f) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_globalStrictPosDef_of_bookRouteBridge h
    (bookRouteBridge_of_scaledRegularityProducer toScaledRegularity)

/--
Conditional strict hard-direction consumer from strict positivity plus the
interior smooth source used in the book Theorem 20.1 approximation.
-/
noncomputable def integralRepOnUnitInterval_of_globalStrictPosDef_of_interiorSmooth
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f)
    (hfSmooth : ContDiffOn ℝ loewnerBookSmoothOrder f (Set.Ioo (-1 : ℝ) 1)) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_globalStrictPosDef_of_bookScaledRegularityProducer
    h (fun _ => bookScaledRegularityFamilyInput_of_interiorSmooth hfSmooth)

end

end Quantum.TraceInequality.Loewner
