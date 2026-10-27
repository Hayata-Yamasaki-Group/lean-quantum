/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.Normed.Operator.CompleteCodomain
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Basic definitions for the Hansen--Pedersen chapter

This file fixes the local language used throughout the Hansen--Pedersen
development: bounded operators on a complex Hilbert space, real continuous
functional calculus and interval-based predicates for operator convexity.

## Main results

* `OperatorConvexOnInterval`: book-faithful interval predicate on a fixed
  Hilbert space.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1.
-/

namespace HansenPedersen

universe u

open CFC
open scoped Topology CStarAlgebra

/-- The algebra of bounded complex-linear operators on a complex Hilbert space. -/
abbrev L (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] : Type u :=
  ℋ →L[ℂ] ℋ

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

/-- Real continuous functional calculus for self-adjoint bounded operators. -/
noncomputable abbrev cfcR (f : ℝ → ℝ) (A : L ℋ) : L ℋ :=
  cfc (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint) f A





/--
Jensen-style operator convexity on an arbitrary interval `J ⊆ ℝ`.
This interval predicate is written directly in terms of `cfcR` so that the
lightweight definition layer does not depend on `LownerHeinzTheorem`.
Source: the Hansen--Pedersen chapter; Hiai--Yanagi (2021), Section 5.1.
-/
def OperatorConvexOnInterval (J : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : L ℋ⦄ ⦃t : ℝ⦄,
    IsSelfAdjoint A → IsSelfAdjoint B →
    0 ≤ t → t ≤ 1 →
    spectrum ℝ A ⊆ J → spectrum ℝ B ⊆ J →
    cfcR (ℋ := ℋ) f ((1 - t) • A + t • B) ≤
      (1 - t) • cfcR (ℋ := ℋ) f A + t • cfcR (ℋ := ℋ) f B













open scoped MatrixOrder





end HansenPedersen

open scoped MatrixOrder





namespace HansenPedersen

universe u

open CFC
open scoped Topology CStarAlgebra MatrixOrder

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]











namespace MatrixOperatorConvexOnInterval



end MatrixOperatorConvexOnInterval





omit [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Jensen-style `H`-operator convexity on an interval for a given complex Hilbert space `K`. -/
def HOperatorConvexOnInterval (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    (J : Set ℝ) (f : ℝ → ℝ) : Prop :=
  OperatorConvexOnInterval (ℋ := K) J f

















namespace AllHOperatorMonotoneOnInterval



end AllHOperatorMonotoneOnInterval

namespace AllHOperatorConvexOnInterval



end AllHOperatorConvexOnInterval

namespace AllHOperatorConcaveOnInterval



end AllHOperatorConcaveOnInterval





















end HansenPedersen
