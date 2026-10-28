/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Basic
import Quantum.TraceInequality.HiaiPetz.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheorem

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

namespace Internal

/-- The scalar tower `ℝ ℂ (L ℋ)` obtained by restricting the complex scalar
action on `L ℋ` to the reals. -/
instance instIsScalarTowerRealComplexL :
    IsScalarTower ℝ ℂ (L ℋ) := RestrictScalars.isScalarTower ℝ ℂ (L ℋ)

end Internal

end HansenPedersen
