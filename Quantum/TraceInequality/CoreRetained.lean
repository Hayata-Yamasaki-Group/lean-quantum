/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.TraceFunctionMonotonicity.BasicTheorems
import Quantum.TraceInequality.HiaiPetz.BasicTheorems
import Quantum.TraceInequality.LownerHeinzSpectralRadius
import Quantum.TraceInequality.TraceFunctionMonotonicity.LownerHeinzTheorem

/-!
# Core lemmas for the Hansen–Pedersen development

Shared entry-level lemmas for the Hiai–Yanagi Chapter 5.1 formalization:
adapters between the foundational `LownerHeinzTheorem.OperatorMonotoneOn`
and the book-faithful `OperatorMonotoneOnInterval`, together with the
Löwner–Heinz power monotonicity `opRpow_le_opRpow` and spectrum-based
order bounds used throughout the chapter.

## Main results

* `opRpow_le_opRpow`: `0 ≤ A ≤ B` implies `A ^ p ≤ B ^ p` for `p ∈ [0, 1]`
  (Löwner–Heinz).
* `operatorMonotoneOnInterval_of_operatorMonotoneOn_Ici` /
  `..._Ioi`: hypothesis-order adapters from the foundational predicate.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1.
-/

namespace HansenPedersen

universe u

open CFC MeasureTheory
open scoped Topology CStarAlgebra
open Filter

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

omit [Nontrivial (L ℋ)] in
/-- Variant of `operatorMonotoneOnInterval_of_operatorMonotoneOn_Ici` on the open
half-line `Set.Ioi 0`. -/
lemma operatorMonotoneOnInterval_of_operatorMonotoneOn_Ioi {f : ℝ → ℝ}
    (hmono : LownerHeinzTheorem.OperatorMonotoneOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) f) :
    OperatorMonotoneOnInterval (ℋ := ℋ) (Set.Ioi (0 : ℝ)) f := by
  intro A B hA hB hAs hBs hAB
  simpa using hmono hB hA hAB hBs hAs

omit [Nontrivial (L ℋ)] in
/-- Löwner--Heinz monotonicity for operator real powers.
Source: Hiai–Yanagi, Theorem 5.1.1. -/
theorem opRpow_le_opRpow {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    {A B : L ℋ} (hA0 : 0 ≤ A) (hAB : A ≤ B) :
    opRpow (ℋ := ℋ) p A ≤ opRpow (ℋ := ℋ) p B := by
  by_cases hnt : Nontrivial (L ℋ)
  · letI := hnt
    exact HansenPedersen.lownerHeinz_of_spectralRadius (ℋ := ℋ) hp hA0 hAB
  · haveI : Subsingleton (L ℋ) := not_nontrivial_iff_subsingleton.mp hnt
    exact le_of_eq (Subsingleton.elim _ _)

attribute [gcongr] opRpow_le_opRpow

end HansenPedersen
