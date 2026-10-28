/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Interface
import Quantum.QuantumEntropy.SandwichedRenyiBase.Umegaki.AlphaOne

/-! # The positive-definite order-one right limit of sandwiched Rényi divergence -/

namespace RenyiDPI

open QuantumState SandwichedRenyiRelativeEntropy

universe u

/-- Positive definiteness of the second input ensures support inclusion. -/
theorem sandwichedDivNN_eq_coe_of_posDef
    {H : Type u} [Qudit H] [Nontrivial H] {α : ℝ} {ρ σ : L H}
    (hα : 1 < α) (_hρ : ρ ∈ pdSetLM (ℋ := H)) (hσ : σ ∈ pdSetLM (ℋ := H)) :
    sandwichedRenyiDivNN α ρ σ = (sandwichedRenyiDiv α ρ σ : EReal) := by
  have hsupp : SupportLE ρ σ := suppLE_of_pdSetLM_right ρ hσ
  unfold sandwichedRenyiDivNN
  rw [if_neg]
  rintro (⟨_, h⟩ | ⟨h, _⟩)
  · exact h hsupp
  · linarith

end RenyiDPI
