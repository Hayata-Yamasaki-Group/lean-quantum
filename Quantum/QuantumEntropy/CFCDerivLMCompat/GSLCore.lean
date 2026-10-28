/-
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.CFCDeriv
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCoreGeneralizedStein
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCore
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.RCLike.Basic

/-!
# Continuity of the trace pairing on linear maps

`continuous_re_trace_lm`: the map `X ↦ Re Tr (ρ * X)` is continuous on linear maps.
-/

namespace CFC

open QuantumState
open scoped Topology

universe u

variable {ℋ : Type u} [Qudit ℋ]

end CFC

namespace QuantumState

universe v

variable {ℋ : Type v} [Qudit ℋ]

/-- `X ↦ Re Tr X` is continuous on `L ℋ` (finite dimension). -/
lemma continuous_re_trace_lm : Continuous (fun X : L ℋ => (Tr X).re) :=
  Complex.continuous_re.comp (LinearMap.continuous_of_finiteDimensional (Tr : L ℋ →ₗ[ℂ] ℂ))

end QuantumState
