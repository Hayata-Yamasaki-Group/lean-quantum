/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.CompressionInequality.ConvexityToContraction
import Quantum.TraceInequality.HansenPedersen.CompressionInequality.ContractionToTwoVariable
import Quantum.TraceInequality.HansenPedersen.CompressionInequality.ContractionToRatioMonotone
import Quantum.TraceInequality.HansenPedersen.CompressionInequality.ProjectionToConvexity
import Quantum.TraceInequality.HansenPedersen.CompressionInequality.RatioMonotoneToProjection
import Quantum.TraceInequality.HansenPedersen.CompressionInequality.TwoVariableToProjection

/-!
# The Hansen-Pedersen compression equivalence

This file assembles the implication files for Hiai–Yanagi Theorem 5.1.7 into
the public equivalence theorem.  The proof closes the cycle among operator
convexity, Jensen contraction, two-variable compression, projection
compression, and ratio monotonicity.

## Main results

* `operatorConvexity_characterizations`: Theorem 5.1.7, stated for the
  Hiai–Yanagi half-open interval `[0, α)`.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1, Theorem 5.1.7.
-/

namespace HansenPedersen

universe u

/-- Theorem 5.1.7: Hansen--Pedersen style equivalent characterizations of operator convexity.
Source: Hiai–Yanagi, Theorem 5.1.7. -/
theorem operatorConvexity_characterizations (α : WithTop ℝ) (f : ℝ → ℝ) :
    (0 : WithTop ℝ) < α → ContinuousOn f (HansenPedersen.halfOpenRay α) →
      ((ConvexityCharacterization.ConditionI.{u} α f ↔
          ConvexityCharacterization.ConditionII.{u} α f) ∧
        (ConvexityCharacterization.ConditionI.{u} α f ↔
          ConvexityCharacterization.ConditionIII.{u} α f) ∧
        (ConvexityCharacterization.ConditionI.{u} α f ↔
          ConvexityCharacterization.ConditionIV.{u} α f) ∧
        (ConvexityCharacterization.ConditionI.{u} α f ↔
          ConvexityCharacterization.ConditionV.{u} α f)) := by
  intro hα hf
  have hIffII :
      ConvexityCharacterization.ConditionI.{u} α f ↔
        ConvexityCharacterization.ConditionII.{u} α f := by
    constructor
    · exact ConvexityCharacterization.conditionI_implies_conditionII hf hα
    · intro hII
      exact ConvexityCharacterization.conditionIV_implies_conditionI hf hα <|
        ConvexityCharacterization.conditionIII_implies_conditionIV hα <|
          ConvexityCharacterization.conditionII_implies_conditionIII hf hα hII
  have hIffIII :
      ConvexityCharacterization.ConditionI.{u} α f ↔
        ConvexityCharacterization.ConditionIII.{u} α f := by
    constructor
    · intro hI
      exact ConvexityCharacterization.conditionII_implies_conditionIII hf hα <|
        ConvexityCharacterization.conditionI_implies_conditionII hf hα hI
    · intro hIII
      exact ConvexityCharacterization.conditionIV_implies_conditionI hf hα <|
        ConvexityCharacterization.conditionIII_implies_conditionIV hα hIII
  have hIffIV :
      ConvexityCharacterization.ConditionI.{u} α f ↔
        ConvexityCharacterization.ConditionIV.{u} α f := by
    constructor
    · intro hI
      exact ConvexityCharacterization.conditionIII_implies_conditionIV hα <|
        ConvexityCharacterization.conditionII_implies_conditionIII hf hα <|
          ConvexityCharacterization.conditionI_implies_conditionII hf hα hI
    · exact ConvexityCharacterization.conditionIV_implies_conditionI hf hα
  have hIffV :
      ConvexityCharacterization.ConditionI.{u} α f ↔
        ConvexityCharacterization.ConditionV.{u} α f := by
    constructor
    · intro hI
      exact ConvexityCharacterization.conditionII_implies_conditionV hf <|
        ConvexityCharacterization.conditionI_implies_conditionII hf hα hI
    · intro hV
      exact ConvexityCharacterization.conditionIV_implies_conditionI hf hα <|
        ConvexityCharacterization.conditionV_implies_conditionIV hα hf hV
  exact ⟨hIffII, hIffIII, hIffIV, hIffV⟩

end HansenPedersen
