/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order


namespace GeneralizedPerspectiveFunction

universe u

section Convexity

variable {E F G : Type*}
variable [AddCommMonoid E] [Module ℝ E]
variable [AddCommMonoid F] [Module ℝ F]
variable [Preorder G] [AddCommMonoid G] [Module ℝ G]

/-- Joint convexity of a two-variable map on prescribed domains in each argument. -/
def JointlyConvexOn (s : Set E) (t : Set F) (Φ : E → F → G) : Prop :=
  ∀ ⦃A₁ A₂ : E⦄ ⦃B₁ B₂ : F⦄ ⦃θ : ℝ⦄,
    A₁ ∈ s → A₂ ∈ s → B₁ ∈ t → B₂ ∈ t →
    0 ≤ θ → θ ≤ 1 →
    Φ ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂)
      ≤ (1 - θ) • Φ A₁ B₁ + θ • Φ A₂ B₂

/-- Joint concavity of a two-variable map on prescribed domains in each argument. -/
def JointlyConcaveOn (s : Set E) (t : Set F) (Φ : E → F → G) : Prop :=
  ∀ ⦃A₁ A₂ : E⦄ ⦃B₁ B₂ : F⦄ ⦃θ : ℝ⦄,
    A₁ ∈ s → A₂ ∈ s → B₁ ∈ t → B₂ ∈ t →
    0 ≤ θ → θ ≤ 1 →
    (1 - θ) • Φ A₁ B₁ + θ • Φ A₂ B₂
      ≤ Φ ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂)

end Convexity

section Theorem25Forward

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

/-- Positive semidefinite operators. -/
def psdSet : Set (ℋ →L[ℂ] ℋ) :=
  {A | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ Set.Ici (0 : ℝ)}

/-- Strictly positive operators. -/
def pdSet : Set (ℋ →L[ℂ] ℋ) :=
  {A | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)}

end Theorem25Forward

-- Ebadian--Nikoufar--Eshaghi Gordji (2011), Perspectives of matrix convex functions,
-- page 1, DOI https://www.pnas.org/doi/10.1073/pnas.1102518108
-- For any qudit ℋ, any A ∈ Herm(ℋ), any B ∈ Pd(ℋ),
-- any real-valued continuous function f, any positive-valued continuous function h>0,
-- (fΔh)(A,B) := h(B)^{1/2} f(h(B)^{-1/2} A h(B)^{-1/2}) h(B)^{1/2}

-- Ebadian--Nikoufar--Eshaghi Gordji (2011), Theorem 2.5,
-- DOI https://www.pnas.org/doi/10.1073/pnas.1102518108
-- Suppose that f is a continuous function with f(0) ≤ 0, and h is a continuous function with h > 0.
-- If f is operator convex and h is operator concave,
-- then fΔh is jointly convex

end GeneralizedPerspectiveFunction
