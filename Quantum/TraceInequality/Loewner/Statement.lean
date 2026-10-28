import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Quantum.TraceInequality.Loewner.Kernel.FiniteMatrixData

namespace Quantum.TraceInequality.Loewner

open Set MeasureTheory Filter

open scoped ComplexOrder
open scoped MatrixOrder
open scoped Topology
open scoped UpperHalfPlane

noncomputable section

/--
Book smoothness order used in the Chapter 20 strictification route.

Mathlib's `⊤ : WithTop ℕ∞` is the stronger `ω` order.  The book's
`C^\infty` hypothesis is represented by `(⊤ : ℕ∞)` embedded in
`WithTop ℕ∞`.
-/
abbrev loewnerBookSmoothOrder : WithTop ℕ∞ :=
  ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The stronger Mathlib `ω` order implies the book `C^\infty` order. -/
theorem contDiffOn_loewnerBookSmoothOrder_of_omega
    {f : ℝ → ℝ} {s : Set ℝ} (h : ContDiffOn ℝ ⊤ f s) :
    ContDiffOn ℝ loewnerBookSmoothOrder f s :=
  h.of_le le_top

/-- Internal strict hypothesis matching the current finite-matrix hard-direction engine. -/
def GlobalStrictPosDef (f : ℝ → ℝ) : Prop :=
  ∀ n : ℕ,
    ∀ y : Fin (n + 1) → ℝ,
      pointsHyp (n := n) y →
        (loewnerMatrix (n := n) f y).PosDef

/--
Strengthened book-route input for the public hard-direction layer.

The current `GlobalStrictPosDef` hypothesis records strict Löwner positivity
only; the Chapter 20 book-route approximation also needs explicit smoothness on
the open interval.
-/
structure GlobalStrictInteriorSmoothInput (f : ℝ → ℝ) where
  strict : GlobalStrictPosDef f
  interiorSmooth : ContDiffOn ℝ loewnerBookSmoothOrder f (Set.Ioo (-1 : ℝ) 1)

/--
Book-style strict smooth input matching the `\widetilde M_\infty(-1,1)`
hypothesis in Chapter 20.

This records strict Löwner positivity together with `C^\infty` regularity on a
neighborhood of `[-1,1]`, rather than deriving regularity from positivity alone.
-/
structure GlobalStrictSmoothNeighborhoodInput (f : ℝ → ℝ) where
  strict : GlobalStrictPosDef f
  smooth_neighborhood :
    ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (-1 : ℝ) 1 ⊆ U ∧
      ContDiffOn ℝ loewnerBookSmoothOrder f U

/--
The book-style smooth-neighborhood input supplies the weaker interior-smooth
input used by the conditional public adapter.
-/
theorem globalStrictInteriorSmoothInput_of_globalStrictSmoothNeighborhoodInput
    {f : ℝ → ℝ} (h : GlobalStrictSmoothNeighborhoodInput f) :
    GlobalStrictInteriorSmoothInput f := by
  refine ⟨h.strict, ?_⟩
  rcases h.smooth_neighborhood with ⟨U, _hUopen, hUsub, hUsmooth⟩
  exact hUsmooth.mono (fun x hx => hUsub ⟨le_of_lt hx.1, le_of_lt hx.2⟩)

/-- Public midpoint for the rebuilt hard direction on the normalized interval `(-1, 1)`. -/
structure IntegralRepOnUnitInterval (f : ℝ → ℝ) where
  ν : FiniteMeasure ℝ
  support :
    (ν : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0
  formula :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (-1 : ℝ) 1 →
      (f x : ℂ) =
        (f 0 : ℂ) +
          ∫ t : ℝ, ((x : ℂ) / (1 + (t : ℂ) * x)) ∂(ν : Measure ℝ)

/--
Public operator-monotonicity predicate on the normalized interval.

The book route uses the continuous functional calculus form: for every
non-unital C*-algebra with an order compatible with the star structure,
`cfcₙ (fun x => f x - f 0)` is monotone on self-adjoint elements whose real
quasispectrum lies in `(-1,1)`.  The subtraction is the book's harmless
constant normalization, and is necessary because non-unital `cfcₙ` only has a
non-junk value for functions sending `0` to `0`.
-/
structure OperatorMonotoneOnUnitInterval (f : ℝ → ℝ) : Prop where
  cfc_monotone :
    ∀ {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A],
      MonotoneOn (fun a : A => cfcₙ (fun x : ℝ => f x - f 0) a)
        {a : A | IsSelfAdjoint a ∧ quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1}

/--
The book Theorem 3.8 Pick domain
`(ℂ \ ℝ) ∪ (-1, 1)`.

We encode it as all non-real points together with real points whose real part
lies in the normalized interval.
-/
def unitIntervalPickDomain : Set ℂ :=
  {z : ℂ | z.im ≠ 0 ∨ z.re ∈ Set.Ioo (-1 : ℝ) 1}

/--
Pick-type analytic extension on the normalized interval.

This is the public analytic side of the book Theorem 3.8 correspondence.  It is
kept separate from `IntegralRepOnUnitInterval`; the equivalence between the two
is built in the Chapter 3 correspondence files.
-/
structure PickExtensionOnUnitInterval (f : ℝ → ℝ) where
  F : ℂ → ℂ
  analyticOn : AnalyticOn ℂ F unitIntervalPickDomain
  agreesOnReal :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (-1 : ℝ) 1 → F (x : ℂ) = (f x : ℂ)
  mapsUpper :
    ∀ ⦃z : ℂ⦄, 0 < z.im → 0 ≤ (F z).im

/-- Public Löwner positivity condition on the normalized interval `(-1, 1)`. This is distinct from
the internal strict hypothesis `GlobalStrictPosDef`. For bookkeeping, differentiability is bundled
on the whole open interval instead of pointwise. Only differentiability is assumed, not continuous
differentiability. -/
structure LoewnerPosOnUnitInterval (f : ℝ → ℝ) : Prop where
  differentiable : DifferentiableOn ℝ f (Set.Ioo (-1 : ℝ) 1)
  posSemidef :
    ∀ n : ℕ, ∀ x : Fin n → ℝ,
      (∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) →
        Function.Injective x →
          (Matrix.of
            (fun i j : Fin n => (loewnerKernel f (x i) (x j) : ℂ))).PosSemidef

/--
Book-route public hard-direction input currently closed by the Chapter 20
strictification pipeline.

This keeps the smoothness required by the book route explicit; it does not
derive interior smoothness from public Löwner positivity alone.
-/
structure LoewnerPosInteriorSmoothInput (f : ℝ → ℝ) where
  pos : LoewnerPosOnUnitInterval f
  interiorSmooth : ContDiffOn ℝ loewnerBookSmoothOrder f (Set.Ioo (-1 : ℝ) 1)

end

end Loewner
end TraceInequality
end Quantum
