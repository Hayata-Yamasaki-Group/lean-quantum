/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.Core
import Quantum.TraceInequality.HiaiPetzTheorem.Core
import Quantum.TraceInequality.HiaiPetz.OperatorCore
import Quantum.TraceInequality.HansenPedersen.Basic
import Quantum.TraceInequality.HiaiPetzTheorem.Basic
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Conditions for the Hansen-Pedersen compression equivalence

This file names the five conditions in Hiai–Yanagi Theorem 5.1.7.  They are
kept as transparent predicates so the proof files can focus on one implication
at a time: operator convexity, contraction Jensen, two-variable Jensen,
projection compression, and monotonicity of the divided-difference ratio.

## Main results

* `ConvexityCharacterization.ConditionI`: operator convexity on the
  Hiai–Yanagi half-open interval, with `f 0 ≤ 0`.
* `ConvexityCharacterization.ConditionII` through
  `ConvexityCharacterization.ConditionV`: the compression, two-variable,
  projection, and ratio-monotonicity conditions of Theorem 5.1.7.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1, Theorem 5.1.7.
-/

namespace HansenPedersen

universe u

open CFC MeasureTheory
open scoped Topology
open Filter

section NormalCFC517

namespace ConvexityCharacterization

/-- Condition (i) in Theorem 5.1.7, written in the global `AllH` form. -/
def ConditionI (α : WithTop ℝ) (f : ℝ → ℝ) : Prop :=
  AllHOperatorConvexOnInterval.{u} (halfOpenRay α) f ∧ f 0 ≤ 0

/-- Condition (ii) in Theorem 5.1.7: compression by a contraction. -/
def ConditionII (α : WithTop ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {A C : L K},
      IsSelfAdjoint A →
      spectrum ℝ A ⊆ halfOpenRay α →
      ‖C‖ ≤ 1 →
      cfcR (ℋ := K) f (star C * A * C) ≤ star C * cfcR (ℋ := K) f A * C

/-- Condition (iii) in Theorem 5.1.7: the two-variable Jensen inequality under a contractive row. -/
def ConditionIII (α : WithTop ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {A B C D : L K},
      IsSelfAdjoint A →
      IsSelfAdjoint B →
      spectrum ℝ A ⊆ halfOpenRay α →
      spectrum ℝ B ⊆ halfOpenRay α →
      star C * C + star D * D ≤ (1 : L K) →
      cfcR (ℋ := K) f (star C * A * C + star D * B * D) ≤
        star C * cfcR (ℋ := K) f A * C + star D * cfcR (ℋ := K) f B * D

/-- Condition (iv) in Theorem 5.1.7: compression by a projection. -/
def ConditionIV (α : WithTop ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    {A P : L K},
      IsSelfAdjoint A →
      IsSelfAdjoint P →
      P * P = P →
      spectrum ℝ A ⊆ halfOpenRay α →
      cfcR (ℋ := K) f (P * A * P) ≤ P * cfcR (ℋ := K) f A * P

/-- Condition (v) in Theorem 5.1.7, in the global `AllH` form:
`t ↦ f t / t` is operator monotone on `(0, α)` for every complex Hilbert space. -/
def ConditionV (α : WithTop ℝ) (f : ℝ → ℝ) : Prop :=
  AllHOperatorMonotoneOnInterval.{u} (HansenPedersen.positiveOpenRay α)
    (fun t : ℝ ↦ f t / t)

end ConvexityCharacterization

end NormalCFC517

end HansenPedersen
