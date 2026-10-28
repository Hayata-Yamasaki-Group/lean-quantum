/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.CompressionInequality.Conditions

/-!
# From the two-variable Jensen inequality to projection compression

This file proves the `(iii) → (iv)` implication in the Hansen–Pedersen
characterization.  The proof specializes the two-variable inequality by
taking the second operator and second coefficient to be zero, while the first
coefficient is a projection.

## Main results

* `conditionIII_implies_conditionIV`: global `ConditionIII → ConditionIV`
  implication.

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

section TwoVariableToProjection

/-- The two-variable Jensen condition implies projection compression by
specializing to `B = 0`, `D = 0`, and using that a self-adjoint idempotent is
contractive.
Source: Hiai–Yanagi, Theorem 5.1.7. -/
theorem conditionIII_implies_conditionIV {α : WithTop ℝ} {f : ℝ → ℝ}
    (hα : (0 : WithTop ℝ) < α)
    (hIII : ConditionIII.{u} α f) :
    ConditionIV.{u} α f := by
  intro K _ _ _ _ _ A P hA hP hPP hσA
  have hPproj : IsStarProjection P := by
    rw [isStarProjection_iff']
    exact ⟨hPP, hP.star_eq⟩
  have hσ0 : spectrum ℝ (0 : L K) ⊆ halfOpenRay α := by
    intro x hx
    have hx0 : x = 0 := by
      simpa [spectrum.zero_eq] using hx
    subst hx0
    exact ⟨le_rfl, hα⟩
  have hcontract :
      star P * P + star (0 : L K) * (0 : L K) ≤ (1 : L K) := by
    simpa [hP.star_eq, hPP] using hPproj.le_one
  have hmain :=
    hIII K (A := A) (B := 0) (C := P) (D := 0)
      hA (IsSelfAdjoint.zero _) hσA hσ0 hcontract
  simpa [hP.star_eq] using hmain

end TwoVariableToProjection

end ConvexityCharacterization

end NormalCFC517

end HansenPedersen
