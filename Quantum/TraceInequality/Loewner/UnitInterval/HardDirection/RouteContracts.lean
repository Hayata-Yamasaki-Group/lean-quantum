import Quantum.TraceInequality.Loewner.UnitInterval.HardDirection.StrictInput

/-!
# Chapter 20 book-route contracts

This file records the contract structures for the Theorem 20.1 book-route
reduction, approximation families, and measure-limit transfer packages.
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
Theorem 20.1-style bridge contract for the book route.

It says that, for the fixed strict input `f`, it is enough to prove the public
integral representation for every smooth strict Chapter 27 input.
-/
structure BookRouteBridge (f : ℝ → ℝ) where
  reduction :
    GlobalStrictPosDef f →
      (∀ g : ℝ → ℝ, SmoothStrictBookRouteInput g → IntegralRepOnUnitInterval g) →
        IntegralRepOnUnitInterval f

/--
Theorem 20.1-style approximation and limit-transfer package.

It records a sequence of smooth strict approximants and the final weak-limit
transfer from interval representations of those approximants back to the
original function.  The mass bounds and weak compactness proof used in the book
are intentionally bundled into `limit_integralRep`.
-/
structure BookRouteApproximationInput (f : ℝ → ℝ) where
  approximant : ℕ → ℝ → ℝ
  smoothStrict : ∀ n : ℕ, SmoothStrictBookRouteInput (approximant n)
  approximant_tendsto :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (-1 : ℝ) 1 →
      Tendsto (fun n : ℕ => approximant n x) atTop (𝓝 (f x))
  approximant_zero_tendsto :
    Tendsto (fun n : ℕ => approximant n 0) atTop (𝓝 (f 0))
  limit_integralRep :
    ((n : ℕ) → IntegralRepOnUnitInterval (approximant n)) →
      IntegralRepOnUnitInterval f

/--
Measure-level limit-transfer contract for the Theorem 20.1 approximation step.

Given integral representations for all smooth strict approximants, it selects a
limit measure, proves its support condition, and proves the limiting formula for
the original function.
-/
structure BookRouteLimitTransferInput
    (f : ℝ → ℝ) (approximant : ℕ → ℝ → ℝ) where
  approximant_tendsto :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (-1 : ℝ) 1 →
      Tendsto (fun n : ℕ => approximant n x) atTop (𝓝 (f x))
  approximant_zero_tendsto :
    Tendsto (fun n : ℕ => approximant n 0) atTop (𝓝 (f 0))
  limitMeasure :
    ((n : ℕ) → IntegralRepOnUnitInterval (approximant n)) → FiniteMeasure ℝ
  limitMeasure_support :
    ∀ reps : (n : ℕ) → IntegralRepOnUnitInterval (approximant n),
      ((limitMeasure reps : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0)
  limitMeasure_formula :
    ∀ (reps : (n : ℕ) → IntegralRepOnUnitInterval (approximant n)) ⦃x : ℝ⦄,
      x ∈ Set.Ioo (-1 : ℝ) 1 →
        (f x : ℂ) =
          (f 0 : ℂ) +
            ∫ t : ℝ, ((x : ℂ) / (1 + (t : ℂ) * x))
              ∂(limitMeasure reps : Measure ℝ)

/--
Mass-bound-only transfer contract for the Theorem 20.1 approximation step.

The support of each representing measure is already part of
`IntegralRepOnUnitInterval`; this package records the remaining pointwise
convergence and uniform mass bound needed to extract a weakly convergent
subsequence.
-/
structure BookRouteMassBoundInput
    (f : ℝ → ℝ) (approximant : ℕ → ℝ → ℝ) where
  approximant_tendsto :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (-1 : ℝ) 1 →
      Tendsto (fun n : ℕ => approximant n x) atTop (𝓝 (f x))
  approximant_zero_tendsto :
    Tendsto (fun n : ℕ => approximant n 0) atTop (𝓝 (f 0))
  massBound :
    ((n : ℕ) → IntegralRepOnUnitInterval (approximant n)) → ℝ≥0
  mass_le :
    ∀ (reps : (n : ℕ) → IntegralRepOnUnitInterval (approximant n)) (n : ℕ),
      (reps n).ν.mass ≤ massBound reps

/--
Derivative mass-bound contract for the Theorem 20.1 approximation step.

Book equation (20.5) supplies a representation-independent uniform mass bound
through the derivative at zero.  This contract records that output; the
derivative/mass bound is proved in `bookRouteDerivativeMassBoundInput_of_deriv_bound`
(`LimitTransfer.lean`).
-/
structure BookRouteDerivativeMassBoundInput
    (f : ℝ → ℝ) (approximant : ℕ → ℝ → ℝ) where
  approximant_tendsto :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (-1 : ℝ) 1 →
      Tendsto (fun n : ℕ => approximant n x) atTop (𝓝 (f x))
  approximant_zero_tendsto :
    Tendsto (fun n : ℕ => approximant n 0) atTop (𝓝 (f 0))
  K : ℝ≥0
  mass_le :
    ∀ (reps : (n : ℕ) → IntegralRepOnUnitInterval (approximant n)) (n : ℕ),
      (reps n).ν.mass ≤ K

/--
Compactness-only measure-limit contract for the Theorem 20.1 approximation step.

This is one layer closer to the book proof than `BookRouteLimitTransferInput`:
it records the uniform mass bound and a weakly convergent subsequence of
representing measures.  Kernel integral convergence is separated in
`BookRouteKernelConvergenceInput`.
-/
structure BookRouteMeasureCompactnessInput
    (f : ℝ → ℝ) (approximant : ℕ → ℝ → ℝ) where
  approximant_tendsto :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (-1 : ℝ) 1 →
      Tendsto (fun n : ℕ => approximant n x) atTop (𝓝 (f x))
  approximant_zero_tendsto :
    Tendsto (fun n : ℕ => approximant n 0) atTop (𝓝 (f 0))
  massBound :
    ((n : ℕ) → IntegralRepOnUnitInterval (approximant n)) → ℝ≥0
  mass_le :
    ∀ (reps : (n : ℕ) → IntegralRepOnUnitInterval (approximant n)) (n : ℕ),
      (reps n).ν.mass ≤ massBound reps
  limitMeasure :
    ((n : ℕ) → IntegralRepOnUnitInterval (approximant n)) → FiniteMeasure ℝ
  subseq :
    ((n : ℕ) → IntegralRepOnUnitInterval (approximant n)) → ℕ → ℕ
  subseq_strictMono :
    ∀ reps : (n : ℕ) → IntegralRepOnUnitInterval (approximant n),
      StrictMono (subseq reps)
  measure_tendsto :
    ∀ reps : (n : ℕ) → IntegralRepOnUnitInterval (approximant n),
      Tendsto (fun k : ℕ => (reps (subseq reps k)).ν) atTop
        (𝓝 (limitMeasure reps))
  limitMeasure_support :
    ∀ reps : (n : ℕ) → IntegralRepOnUnitInterval (approximant n),
      ((limitMeasure reps : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0)

/--
Kernel convergence contract over a compactness-only measure-limit package.

This isolates the analytic step that follows from weak convergence and
continuity/boundedness of the kernel `x / (1 + λ * x)`; it is proved in
`bookRouteKernelConvergenceInput_of_measureCompactnessInput` (`LimitTransfer.lean`).
-/
structure BookRouteKernelConvergenceInput
    (f : ℝ → ℝ) (approximant : ℕ → ℝ → ℝ) where
  compactness : BookRouteMeasureCompactnessInput f approximant
  kernel_integral_tendsto :
    ∀ (reps : (n : ℕ) → IntegralRepOnUnitInterval (approximant n)) ⦃x : ℝ⦄,
      x ∈ Set.Ioo (-1 : ℝ) 1 →
        Tendsto
          (fun k : ℕ =>
            ∫ t : ℝ, ((x : ℂ) / (1 + (t : ℂ) * x))
              ∂((reps (compactness.subseq reps k)).ν : Measure ℝ))
          atTop
          (𝓝
            (∫ t : ℝ, ((x : ℂ) / (1 + (t : ℂ) * x))
              ∂(compactness.limitMeasure reps : Measure ℝ)))

/--
Backward-compatible combined measure-limit contract for the Theorem 20.1
approximation step.

It bundles the compactness data and the kernel integral convergence needed to
recover the direct `BookRouteLimitTransferInput`.
-/
structure BookRouteMeasureLimitInput
    (f : ℝ → ℝ) (approximant : ℕ → ℝ → ℝ) where
  approximant_tendsto :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (-1 : ℝ) 1 →
      Tendsto (fun n : ℕ => approximant n x) atTop (𝓝 (f x))
  approximant_zero_tendsto :
    Tendsto (fun n : ℕ => approximant n 0) atTop (𝓝 (f 0))
  massBound :
    ((n : ℕ) → IntegralRepOnUnitInterval (approximant n)) → ℝ≥0
  mass_le :
    ∀ (reps : (n : ℕ) → IntegralRepOnUnitInterval (approximant n)) (n : ℕ),
      (reps n).ν.mass ≤ massBound reps
  limitMeasure :
    ((n : ℕ) → IntegralRepOnUnitInterval (approximant n)) → FiniteMeasure ℝ
  subseq :
    ((n : ℕ) → IntegralRepOnUnitInterval (approximant n)) → ℕ → ℕ
  subseq_strictMono :
    ∀ reps : (n : ℕ) → IntegralRepOnUnitInterval (approximant n),
      StrictMono (subseq reps)
  measure_tendsto :
    ∀ reps : (n : ℕ) → IntegralRepOnUnitInterval (approximant n),
      Tendsto (fun k : ℕ => (reps (subseq reps k)).ν) atTop
        (𝓝 (limitMeasure reps))
  limitMeasure_support :
    ∀ reps : (n : ℕ) → IntegralRepOnUnitInterval (approximant n),
      ((limitMeasure reps : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0)
  kernel_integral_tendsto :
    ∀ (reps : (n : ℕ) → IntegralRepOnUnitInterval (approximant n)) ⦃x : ℝ⦄,
      x ∈ Set.Ioo (-1 : ℝ) 1 →
        Tendsto
          (fun k : ℕ =>
            ∫ t : ℝ, ((x : ℂ) / (1 + (t : ℂ) * x))
              ∂((reps (subseq reps k)).ν : Measure ℝ))
          atTop
          (𝓝
            (∫ t : ℝ, ((x : ℂ) / (1 + (t : ℂ) * x))
              ∂(limitMeasure reps : Measure ℝ)))

/--
Concrete Theorem 20.1 approximation-family contract.

It records parameter sequences `ε_n`, `δ_n` tending to zero, the fact that the
corresponding book approximants are smooth strict Chapter 27 inputs, and the
measure-level limit-transfer package for this concrete approximant sequence.
-/
structure BookApproximationFamilyInput (f : ℝ → ℝ) where
  /-- Simon Ch.3 [simon2019]: the positive regularization scales `ε_n`. -/
  epsilon : ℕ → ℝ
  /-- Simon Ch.3 [simon2019]: the interval shrink parameters `δ_n`. -/
  delta : ℕ → ℝ
  /-- Simon Ch.3 [simon2019]: the scales `ε_n` tend to zero. -/
  epsilon_tendsto_zero : Tendsto epsilon atTop (𝓝 0)
  /-- Simon Ch.3 [simon2019]: the shrink parameters `δ_n` tend to zero. -/
  delta_tendsto_zero : Tendsto delta atTop (𝓝 0)
  /-- Simon Ch.3 [simon2019]: each book approximant is smooth and strict. -/
  smoothStrict :
    ∀ n : ℕ,
      SmoothStrictBookRouteInput
        (bookSmoothApprox f (epsilon n) (delta n))
  /-- Simon Ch.3 [simon2019]: transfer integral representations to the limit. -/
  limitTransfer :
    BookRouteLimitTransferInput f
      (fun n : ℕ => bookSmoothApprox f (epsilon n) (delta n))

/--
The smooth-strict part of the concrete Theorem 20.1 approximation family,
separated from the measure-limit transfer data.
-/
structure BookSmoothStrictFamilyInput (f : ℝ → ℝ) where
  /-- Simon Ch.3 [simon2019]: the positive regularization scales `ε_n`. -/
  epsilon : ℕ → ℝ
  /-- Simon Ch.3 [simon2019]: the interval shrink parameters `δ_n`. -/
  delta : ℕ → ℝ
  /-- Simon Ch.3 [simon2019]: every regularization scale is positive. -/
  epsilon_pos : ∀ n : ℕ, 0 < epsilon n
  /-- Simon Ch.3 [simon2019]: every shrink parameter lies in `(0,1)`. -/
  delta_mem_Ioo : ∀ n : ℕ, delta n ∈ Set.Ioo (0 : ℝ) 1
  /-- Simon Ch.3 [simon2019]: the scales `ε_n` tend to zero. -/
  epsilon_tendsto_zero : Tendsto epsilon atTop (𝓝 0)
  /-- Simon Ch.3 [simon2019]: the shrink parameters `δ_n` tend to zero. -/
  delta_tendsto_zero : Tendsto delta atTop (𝓝 0)
  /-- Simon Ch.3 [simon2019]: each book approximant is smooth and strict. -/
  smoothStrict :
    ∀ n : ℕ,
      SmoothStrictBookRouteInput
        (bookSmoothApprox f (epsilon n) (delta n))

/--
Regularity package for only the scaled part `x ↦ f((1 - δ_n) * x)`.

The `ε_n g₀` contribution is smooth and has a uniform derivative bound by the
closed `g₀` package, so the full regularity package can be built from this
smaller contract.
-/
structure BookScaledRegularityFamilyInput (f : ℝ → ℝ) where
  /-- Simon Ch.3 [simon2019]: the positive regularization scales `ε_n`. -/
  epsilon : ℕ → ℝ
  /-- Simon Ch.3 [simon2019]: the interval shrink parameters `δ_n`. -/
  delta : ℕ → ℝ
  /-- Simon Ch.3 [simon2019]: every regularization scale is positive. -/
  epsilon_pos : ∀ n : ℕ, 0 < epsilon n
  /-- Simon Ch.3 [simon2019]: every shrink parameter lies in `(0,1)`. -/
  delta_mem_Ioo : ∀ n : ℕ, delta n ∈ Set.Ioo (0 : ℝ) 1
  /-- Simon Ch.3 [simon2019]: the scales `ε_n` tend to zero. -/
  epsilon_tendsto_zero : Tendsto epsilon atTop (𝓝 0)
  /-- Simon Ch.3 [simon2019]: the shrink parameters `δ_n` tend to zero. -/
  delta_tendsto_zero : Tendsto delta atTop (𝓝 0)
  /-- Simon Ch.3 [simon2019]: derivative bounds for the scaled part. -/
  K_scaled : ℕ → ℝ≥0
  /-- Simon Ch.3 [simon2019]: the scaled functions are smooth near `[-1,1]`. -/
  scaled_smooth_neighborhood :
    ∀ n : ℕ, ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (-1 : ℝ) 1 ⊆ U ∧
      ContDiffOn ℝ loewnerBookSmoothOrder (fun x : ℝ => f ((1 - delta n) * x)) U
  /-- Simon Ch.3 [simon2019]: scaled derivatives are bounded on `[-1,1]`. -/
  scaled_deriv_bound_on_Icc :
    ∀ n : ℕ, ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ENNReal.ofReal (deriv (fun x : ℝ => f ((1 - delta n) * x)) x) ≤
        (K_scaled n : ENNReal)

/--
The Theorem 20.1 inputs after reducing regularity to the scaled part: a
scaled-regularity producer and the matching measure-limit transfer producer.
For Löwner-positive `f` they are supplied on the way to
`integralRepOnUnitInterval_of_loewnerPosOnUnitInterval` (`LoewnerTheorem.lean`).
-/
structure BookScaledRegularityLimitTransferInput (f : ℝ → ℝ) where
  /-- Simon Ch.3 [simon2019]: produce scaled regularity from strict positivity. -/
  toScaledRegularity :
    GlobalStrictPosDef f → BookScaledRegularityFamilyInput f
  /-- Simon Ch.3 [simon2019]: transfer the scaled approximants to the limit. -/
  limitTransfer :
    ∀ h : GlobalStrictPosDef f,
      BookRouteLimitTransferInput f
        (fun n : ℕ =>
          bookSmoothApprox f
            ((toScaledRegularity h).epsilon n) ((toScaledRegularity h).delta n))

/--
Variant of the Theorem 20.1 input with the measure-limit side kept at the
compactness contract level.
-/
structure BookScaledRegularityMeasureLimitInput (f : ℝ → ℝ) where
  /-- Simon Ch.3 [simon2019]: produce scaled regularity from strict positivity. -/
  toScaledRegularity :
    GlobalStrictPosDef f → BookScaledRegularityFamilyInput f
  /-- Simon Ch.3 [simon2019]: provide the measure-limit transfer package. -/
  measureLimit :
    ∀ h : GlobalStrictPosDef f,
      BookRouteMeasureLimitInput f
        (fun n : ℕ =>
          bookSmoothApprox f
            ((toScaledRegularity h).epsilon n) ((toScaledRegularity h).delta n))

/--
Variant of the Theorem 20.1 input with compactness data and kernel convergence
kept as separate pieces.
-/
structure BookScaledRegularityKernelConvergenceInput (f : ℝ → ℝ) where
  /-- Simon Ch.3 [simon2019]: produce scaled regularity from strict positivity. -/
  toScaledRegularity :
    GlobalStrictPosDef f → BookScaledRegularityFamilyInput f
  /-- Simon Ch.3 [simon2019]: provide kernel convergence for the approximants. -/
  kernelConvergence :
    ∀ h : GlobalStrictPosDef f,
      BookRouteKernelConvergenceInput f
        (fun n : ℕ =>
          bookSmoothApprox f
            ((toScaledRegularity h).epsilon n) ((toScaledRegularity h).delta n))

/--
Variant of the Theorem 20.1 input with only measure compactness data on the
measure side.  Kernel convergence is supplied by the general weak-convergence
kernel theorem below.
-/
structure BookScaledRegularityMeasureCompactnessInput (f : ℝ → ℝ) where
  /-- Simon Ch.3 [simon2019]: produce scaled regularity from strict positivity. -/
  toScaledRegularity :
    GlobalStrictPosDef f → BookScaledRegularityFamilyInput f
  /-- Simon Ch.3 [simon2019]: provide compactness for representing measures. -/
  measureCompactness :
    ∀ h : GlobalStrictPosDef f,
      BookRouteMeasureCompactnessInput f
        (fun n : ℕ =>
          bookSmoothApprox f
            ((toScaledRegularity h).epsilon n) ((toScaledRegularity h).delta n))

/--
Variant of the Theorem 20.1 input with only a mass-bound producer on the measure
side.  Weak compactness on `[-1,1]` supplies the corresponding measure
compactness data.
-/
structure BookScaledRegularityMassBoundInput (f : ℝ → ℝ) where
  /-- Simon Ch.3 [simon2019]: produce scaled regularity from strict positivity. -/
  toScaledRegularity :
    GlobalStrictPosDef f → BookScaledRegularityFamilyInput f
  /-- Simon Ch.3 [simon2019]: provide uniform mass bounds for the measures. -/
  massBound :
    ∀ h : GlobalStrictPosDef f,
      BookRouteMassBoundInput f
        (fun n : ℕ =>
          bookSmoothApprox f
            ((toScaledRegularity h).epsilon n) ((toScaledRegularity h).delta n))

/--
Variant of the Theorem 20.1 input where the measure side is reduced to the
derivative-style uniform mass-bound output of book equation (20.5).
-/
structure BookScaledRegularityDerivativeMassBoundInput (f : ℝ → ℝ) where
  /-- Simon Ch.3 [simon2019]: produce scaled regularity from strict positivity. -/
  toScaledRegularity :
    GlobalStrictPosDef f → BookScaledRegularityFamilyInput f
  /-- Simon Ch.3 [simon2019]: provide derivative-style mass bounds. -/
  derivativeMassBound :
    ∀ h : GlobalStrictPosDef f,
      BookRouteDerivativeMassBoundInput f
        (fun n : ℕ =>
          bookSmoothApprox f
            ((toScaledRegularity h).epsilon n) ((toScaledRegularity h).delta n))

/--
Regularity-only part of the concrete Theorem 20.1 approximation family.

Strict positivity is supplied separately by the algebraic strictification
theorem using `g₀`.
-/
structure BookSmoothApproxRegularityFamilyInput (f : ℝ → ℝ) where
  /-- Simon Ch.3 [simon2019]: the positive regularization scales `ε_n`. -/
  epsilon : ℕ → ℝ
  /-- Simon Ch.3 [simon2019]: the interval shrink parameters `δ_n`. -/
  delta : ℕ → ℝ
  /-- Simon Ch.3 [simon2019]: every regularization scale is positive. -/
  epsilon_pos : ∀ n : ℕ, 0 < epsilon n
  /-- Simon Ch.3 [simon2019]: every shrink parameter lies in `(0,1)`. -/
  delta_mem_Ioo : ∀ n : ℕ, delta n ∈ Set.Ioo (0 : ℝ) 1
  /-- Simon Ch.3 [simon2019]: the scales `ε_n` tend to zero. -/
  epsilon_tendsto_zero : Tendsto epsilon atTop (𝓝 0)
  /-- Simon Ch.3 [simon2019]: the shrink parameters `δ_n` tend to zero. -/
  delta_tendsto_zero : Tendsto delta atTop (𝓝 0)
  /-- Simon Ch.3 [simon2019]: derivative bounds for the full approximants. -/
  K : ℕ → ℝ≥0
  /-- Simon Ch.3 [simon2019]: approximants are smooth near `[-1,1]`. -/
  smooth_neighborhood :
    ∀ n : ℕ, ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (-1 : ℝ) 1 ⊆ U ∧
      ContDiffOn ℝ loewnerBookSmoothOrder (bookSmoothApprox f (epsilon n) (delta n)) U
  /-- Simon Ch.3 [simon2019]: approximant derivatives are bounded on `[-1,1]`. -/
  deriv_bound_on_Icc :
    ∀ n : ℕ, ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ENNReal.ofReal (deriv (bookSmoothApprox f (epsilon n) (delta n)) x) ≤
        (K n : ENNReal)

end

end Quantum.TraceInequality.Loewner
