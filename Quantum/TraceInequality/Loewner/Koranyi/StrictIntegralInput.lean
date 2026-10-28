import Quantum.TraceInequality.Loewner.UnitInterval.KernelPositivity
import Quantum.TraceInequality.Loewner.Koranyi.WeakLimit

/-!
# Chapter 27 book-route input contract

This file records the explicit input needed by the book-route Theorem 27.5
consumer.  The upstream extraction of this package from `GlobalStrictPosDef`
is intentionally left to a later node.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory
open AugmentedLoewnerLocalConstruction

open scoped NNReal
open scoped Topology

noncomputable section

/--
Explicit book-route input for the strict Chapter 27 path.

It bundles the local Prop. 27.3 constructions, a uniform dyadic derivative
bound, and continuity on the open unit interval.

Theorem 27.5 of [simon2019].
-/
structure StrictBookIntegralRouteInput (f : ℝ → ℝ) where
  localConstruction : (m : ℕ) → AugmentedLoewnerLocalConstruction f m
  K : ℝ≥0
  uniform_deriv_bound :
    ∀ (m : ℕ) (i : Fin (nonzeroInteriorDyadicPointCount m + 1)),
      ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) ≤ (K : ENNReal)
  continuousOn : ContinuousOn f (Set.Ioo (-1 : ℝ) 1)

/--
Book-style smooth strict input for the Chapter 27 route.

The smooth-neighborhood field records the `C^\infty` hypothesis from the book.
The derivative bound is kept explicit because it is the exact input consumed by
the implemented dyadic estimates.

Theorem 27.5 of [simon2019].
-/
structure SmoothStrictBookRouteInput (f : ℝ → ℝ) where
  strict : GlobalStrictPosDef f
  smooth_neighborhood :
    ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (-1 : ℝ) 1 ⊆ U ∧ ContDiffOn ℝ loewnerBookSmoothOrder f U
  K : ℝ≥0
  deriv_bound_on_Icc :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, ENNReal.ofReal (deriv f x) ≤ (K : ENNReal)

/-- Strict global positivity supplies continuity on the open unit interval. -/
theorem continuousOn_of_globalStrictPosDef
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) :
    ContinuousOn f (Set.Ioo (-1 : ℝ) 1) := by
  intro x hx
  exact (continuousAt_of_globalStrictPosDef h hx).continuousWithinAt

/--
The explicit book-route input directly yields the public interval integral
representation by applying the implemented Theorem 27.5 compactness package.

Theorem 27.5 of [simon2019].
-/
noncomputable def integralRepOnUnitInterval_of_strictBookRouteInput
    {f : ℝ → ℝ} (h : StrictBookIntegralRouteInput f) :
    IntegralRepOnUnitInterval f :=
  bookWeakLimit_integralRepPackage_of_uniform_deriv_bound_compactness
    h.localConstruction h.K h.uniform_deriv_bound h.continuousOn

/--
Conditional producer for the book-route input from strict global positivity and
the uniform dyadic derivative bound supplied by the smooth Chapter 20/27 stage.

Theorem 27.5 of [simon2019].
-/
noncomputable def strictBookRouteInput_of_globalStrictPosDef_of_uniform_deriv_bound
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) (K : ℝ≥0)
    (hK :
      ∀ (m : ℕ) (i : Fin (nonzeroInteriorDyadicPointCount m + 1)),
        ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) ≤ (K : ENNReal)) :
    StrictBookIntegralRouteInput f where
  localConstruction := augmentedLoewnerLocalConstruction_of_globalStrictPosDef h
  K := K
  uniform_deriv_bound := hK
  continuousOn := continuousOn_of_globalStrictPosDef h

/--
Conditional strict hard-direction consumer along the book route: once the
uniform dyadic derivative bound is supplied, the implemented Theorem 27.5
package gives the interval integral representation.
-/
noncomputable def integralRepOnUnitInterval_of_globalStrictPosDef_of_uniform_deriv_bound
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) (K : ℝ≥0)
    (hK :
      ∀ (m : ℕ) (i : Fin (nonzeroInteriorDyadicPointCount m + 1)),
        ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) ≤ (K : ENNReal)) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_strictBookRouteInput
    (strictBookRouteInput_of_globalStrictPosDef_of_uniform_deriv_bound h K hK)

/--
The smooth strict input gives the uniform dyadic derivative bound required by
the book-route local constructions.

Theorem 27.5 of [simon2019].
-/
theorem uniformDyadicDerivBound_of_smoothStrictBookRouteInput
    {f : ℝ → ℝ} (h : SmoothStrictBookRouteInput f) :
    ∀ (m : ℕ) (i : Fin (nonzeroInteriorDyadicPointCount m + 1)),
      ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) ≤ (h.K : ENNReal) := by
  intro m i
  have hmemIoo : zeroAnchoredDyadicPointFamily m i ∈ Set.Ioo (-1 : ℝ) 1 :=
    zeroAnchoredDyadicPointFamily_mem_Ioo m i
  have hmemIcc : zeroAnchoredDyadicPointFamily m i ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨le_of_lt hmemIoo.1, le_of_lt hmemIoo.2⟩
  exact h.deriv_bound_on_Icc (zeroAnchoredDyadicPointFamily m i) hmemIcc

/--
The book-style smooth strict input supplies the full explicit book-route input
package for Theorem 27.5.

Theorem 27.5 of [simon2019].
-/
noncomputable def strictBookRouteInput_of_smoothStrictBookRouteInput
    {f : ℝ → ℝ} (h : SmoothStrictBookRouteInput f) :
    StrictBookIntegralRouteInput f :=
  strictBookRouteInput_of_globalStrictPosDef_of_uniform_deriv_bound
    h.strict h.K (uniformDyadicDerivBound_of_smoothStrictBookRouteInput h)

/--
Book-route integral representation for the smooth strict case.  This is the
Lean counterpart of applying Chapter 27 after the Theorem 20.1 reduction.

Theorem 27.5 of [simon2019].
-/
noncomputable def integralRepOnUnitInterval_of_smoothStrictBookRouteInput
    {f : ℝ → ℝ} (h : SmoothStrictBookRouteInput f) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_strictBookRouteInput
    (strictBookRouteInput_of_smoothStrictBookRouteInput h)

end

end Quantum.TraceInequality.Loewner
