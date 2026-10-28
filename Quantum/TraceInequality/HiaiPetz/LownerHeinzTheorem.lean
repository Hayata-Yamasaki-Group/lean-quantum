/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

namespace LownerHeinzTheorem

universe u v

open CFC

variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint]
variable [Nontrivial (ℋ →L[ℂ] ℋ)]

-- Cached `Algebra ℝ (ℋ →L[ℂ] ℋ)` keeps this deep superclass/instance search within
-- the default instance budget.
noncomputable local instance : NonnegSpectrumClass ℝ (ℋ →L[ℂ] ℋ) := inferInstance

end LownerHeinzTheorem
