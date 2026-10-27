/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.TracePositiveDefinite

/-!
# Support inclusion for non-negative quantum divergences

This lightweight module owns the support predicate used by the route-neutral
Umegaki interface.  It deliberately does not import finite-`α` monotonicity or
the max-relative entropy endpoint.
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState

universe u

/-! ### Support condition `SupportLE` -/

/-- **Support condition**: `ker σ ≤ ker ρ`, equivalent to `supp ρ ⊆ supp σ`. -/
def SupportLE {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (ρ σ : L ℋ) : Prop :=
  LinearMap.ker σ ≤ LinearMap.ker ρ

/-- The support condition `SupportLE ρ σ` holds trivially when `σ ∈ pdSetLM`. -/
lemma suppLE_of_pdSetLM_right
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (ρ : L ℋ) {σ : L ℋ} (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    SupportLE ρ σ := by
  intro x hx
  have hker : LinearMap.ker σ = ⊥ := by
    obtain ⟨u, hu⟩ := isUnit_of_pdSetLM hσ
    rw [LinearMap.ker_eq_bot]
    intro y z hyz
    have h_invσ : (u.inv : L ℋ) * σ = 1 := by rw [← hu]; exact u.inv_val
    have h_apply : ∀ w : ℋ, (u.inv : L ℋ) (σ w) = w := fun w => by
      have : ((u.inv : L ℋ) * σ) w = w := by rw [h_invσ]; rfl
      exact this
    rw [← h_apply y, ← h_apply z, hyz]
  rw [hker, Submodule.mem_bot] at hx
  simp [hx]

end SandwichedRenyiRelativeEntropy
