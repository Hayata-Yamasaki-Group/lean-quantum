/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.TraceFunctionMonotonicity.LownerHeinz.Defs
import Quantum.TraceInequality.LownerHeinz.Defs
import Quantum.TraceInequality.LownerHeinz.Reciprocal

/-!
# Reciprocal inequalities and shifted reciprocals


-/

namespace LownerHeinzCore

universe u

open CFC

section Spectrum

variable {𝓐 : Type u}
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
variable [Nontrivial 𝓐]
variable [NonnegSpectrumClass ℝ 𝓐]

/-! ### Positive-cone restrictions and shifted reciprocals -/

omit [Nontrivial 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
/-- On a set `s ⊆ [0, ∞)` the self-adjointness hypotheses in `OperatorMonotoneOn` are
equivalent to the previous nonnegativity-based formulation, since for self-adjoint elements
`spectrum ℝ A ⊆ s ⊆ [0, ∞)` already forces `0 ≤ A`. -/
theorem operatorMonotoneOn_iff_of_subset_Ici {s : Set ℝ} (hs : s ⊆ Set.Ici (0 : ℝ))
    (f : ℝ → ℝ) :
    OperatorMonotoneOn (𝓐 := 𝓐) s f ↔
      ∀ ⦃A B : 𝓐⦄, 0 ≤ A → 0 ≤ B → B ≤ A →
        spectrum ℝ A ⊆ s → spectrum ℝ B ⊆ s → cfcR f B ≤ cfcR f A := by
  constructor
  · intro h A B hA0 hB0 hBA hsA hsB
    exact h (IsSelfAdjoint.of_nonneg hA0) (IsSelfAdjoint.of_nonneg hB0) hBA hsA hsB
  · intro h A B hA hB hBA hsA hsB
    exact h (nonneg_of_spectrum_subset_Ici hA (hsA.trans hs))
      (nonneg_of_spectrum_subset_Ici hB (hsB.trans hs)) hBA hsA hsB

end Spectrum

end LownerHeinzCore
