/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.TraceRe
import Quantum.QuantumMechanics.Channel.Basic

/-! General CPTP nonzero preservation, independent of the selected DPI route. -/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel MeasureTheory TensorProduct
open scoped ComplexOrder NNReal Topology

universe u

/-- A CPTP map cannot send a non-zero non-negative state to zero. -/
lemma cptp_toFun_ne_zero
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦)
    {ρ : L ℋ} (hρ : 0 ≤ ρ) (hρ0 : ρ ≠ 0) :
    E.toFun ρ ≠ 0 := by
  intro hzero
  have htrace := E.trace_map ρ
  have htr : (Tr ρ).re = 0 := by
    rw [htrace, hzero]
    simp
  exact absurd htr (ne_of_gt (by
    simpa using QuantumEntropy.trace_re_pos_of_ne_zero hρ hρ0))

end SandwichedRenyiRelativeEntropy
