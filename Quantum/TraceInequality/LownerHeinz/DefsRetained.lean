/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Quantum.TraceInequality.LiebAndo.LownerHeinz.Defs
import Quantum.TraceInequality.LownerHeinz.Defs
import Quantum.TraceInequality.TraceFunctionMonotonicity.LownerHeinz.Defs

/-!
# Löwner-Heinz core definitions


Unrestricted operator convexity/concavity, in fixed-algebra and `All` forms,
degenerates to the zero function on nontrivial complex C*-algebras; see
`GlobalDegeneracy.lean`. Localized predicates use self-adjoint inputs with spectra
in an interval `I`: with continuity on `I` and a fixed ambient algebra, nonzero
examples exist, such as `x²` for convexity on `[0, ∞)`; `OnAll` quantifies over algebras.

References to Carlen 2009 (also written Carlen09) in the comments of these files are to the
lecture notes *Trace Inequalities and Quantum Entropy: An Introductory Course*, manuscript
version of May 3, 2009; the published version appeared in Contemporary Mathematics 529 (2010),
73–140.
-/

namespace LownerHeinzCore

universe u

open CFC

section Pure

variable {𝓐 : Type u}
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
variable [Nontrivial 𝓐]

omit [Nontrivial 𝓐] in
/-- `f` is operator antitone on `s` iff `-f` is operator monotone on `s`. -/
theorem operatorAntitoneOn_iff_operatorMonotoneOn_neg (s : Set ℝ) (f : ℝ → ℝ) :
    OperatorAntitoneOn (𝓐 := 𝓐) s f ↔ OperatorMonotoneOn (𝓐 := 𝓐) s (fun x ↦ -f x) := by
  constructor
  · intro h A B hA0 hB0 hBA hsA hsB
    simpa [cfcR, cfc_neg] using neg_le_neg (h hA0 hB0 hBA hsA hsB)
  · intro h A B hA0 hB0 hBA hsA hsB
    have h' : -cfcR f B ≤ -cfcR f A := by
      simpa [cfcR, cfc_neg] using h hA0 hB0 hBA hsA hsB
    exact neg_le_neg_iff.mp h'

end Pure

end LownerHeinzCore
