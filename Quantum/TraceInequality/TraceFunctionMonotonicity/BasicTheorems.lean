/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Basic
import Quantum.TraceInequality.TraceFunctionMonotonicity.LownerHeinzTheorem

/-!
# Shared theorems for interval operator-monotonicity predicates

These declarations retain their `HansenPedersen` namespace as shared vocabulary.
Source: the Hansen--Pedersen development.
-/

namespace HansenPedersen

universe u

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

omit [Nontrivial (L ℋ)] in
/-- Adapter from the foundational `LownerHeinzTheorem.OperatorMonotoneOn (Set.Ici 0)`
to the book-faithful `OperatorMonotoneOnInterval (Set.Ici 0)`; the two predicates
differ only in the order in which the hypotheses are received. -/
lemma operatorMonotoneOnInterval_of_operatorMonotoneOn_Ici {f : ℝ → ℝ}
    (hmono : LownerHeinzTheorem.OperatorMonotoneOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) f) :
    OperatorMonotoneOnInterval (ℋ := ℋ) (Set.Ici (0 : ℝ)) f := by
  intro A B hA hB hAs hBs hAB
  simpa using hmono hB hA hAB hBs hAs

end HansenPedersen
