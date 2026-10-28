/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Quantum.TraceInequality.HiaiPetz.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinz.Defs
import Quantum.TraceInequality.LownerHeinz.Reciprocal
import Quantum.TraceInequality.LownerHeinzTheorem

namespace LownerHeinzTheorem

universe u v

open CFC

variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint]
variable [Nontrivial (ℋ →L[ℂ] ℋ)]

-- Cached `Algebra ℝ (ℋ →L[ℂ] ℋ)` keeps this deep superclass/instance search within
-- the default instance budget.
attribute [local instance] instNonnegSpectrumClassRealContinuousLinearMapComplexId_quantum

omit [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint] in
theorem one_div_operatorConvexOn_Ioi :
    OperatorConvexOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x) := by
  simpa using
    (LownerHeinzCore.one_div_operatorConvexOn_Ioi (𝓐 := (ℋ →L[ℂ] ℋ)))

end LownerHeinzTheorem
