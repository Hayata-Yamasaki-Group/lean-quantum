/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.RenyiDPI.Petz.TracePower
import Quantum.QuantumEntropy.SandwichedRenyiBase.Defs

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

theorem petzTracePower_eq_liebTrace_one :
∀ {H : Type u} [Qudit H] [Nontrivial H]
  {α : ℝ} {ρ σ : L H}, α ∈ Set.Ioo (0 : ℝ) 1 → 0 ≤ ρ → 0 ≤ σ →
  petzTracePower α ρ σ = liebTraceMapLM α (1 : L H) ρ σ := by
  intro H _ _ α ρ σ _ _ _
  unfold petzTracePower liebTraceMapLM LiebAndoTrace.liebTraceMap
  have hone : (1 : L H).toContinuousLinearMap = (1 : B H) := rfl
  simp only [hone, star_one, mul_one]
  rfl

theorem petzTracePower_continuousOn_nonneg :
∀ {H : Type u} [Qudit H] [Nontrivial H] {α : ℝ},
  α ∈ Set.Ioo (0 : ℝ) 1 →
  ContinuousOn (Function.uncurry (petzTracePower (ℋ := H) α))
    ({A : L H | 0 ≤ A} ×ˢ {A : L H | 0 ≤ A}) := by
  intro H _ _ α hα p hp
  exact tendsto_petzTracePower_nonneg hα hp.1 hp.2
    continuousWithinAt_fst continuousWithinAt_snd
    (Filter.mem_of_superset self_mem_nhdsWithin fun _ hq => hq.1)
    (Filter.mem_of_superset self_mem_nhdsWithin fun _ hq => hq.2)

end RenyiDPI
