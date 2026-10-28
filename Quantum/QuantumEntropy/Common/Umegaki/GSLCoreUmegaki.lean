/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.Support
import Quantum.QuantumEntropy.CFCTransport
import Quantum.QuantumEntropy.Common.Umegaki.GSLCore

/-! # Normalized Umegaki relative entropy

Definitions and the trace representation of normalized Umegaki relative entropy.
-/

namespace SandwichedRenyiRelativeEntropy

open GeneralizedPerspectiveFunction QuantumState QuantumChannel MeasureTheory
open scoped ComplexOrder NNReal Topology

universe u

section Umegaki

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

/-- **Umegaki relative entropy** for non-negative `ρ, σ` (the `α → 1` boundary of
    the Frank–Lieb extension), as an `EReal`: value `⊤` on the support-mismatch
    region `¬ SupportLE ρ σ`, and `umegakiNorm ρ σ` otherwise. -/
noncomputable def umegakiRelEntropyNN (ρ σ : L ℋ) : EReal :=
  letI : Decidable (SupportLE ρ σ) := Classical.propDecidable _
  if SupportLE ρ σ
    then ((umegakiNorm ρ σ : ℝ) : EReal) else (⊤ : EReal)

/-- Under support inclusion, the extended entropy is the real-valued entropy. -/
theorem umegakiRelEntropyNN_of_supportLE {ρ σ : L ℋ} (h : SupportLE ρ σ) :
    umegakiRelEntropyNN ρ σ = (umegakiNorm ρ σ : EReal) := by
  unfold umegakiRelEntropyNN
  rw [if_pos h]

/-- When support inclusion fails, the extended entropy is infinite. -/
theorem umegakiRelEntropyNN_of_not_supportLE {ρ σ : L ℋ} (h : ¬ SupportLE ρ σ) :
    umegakiRelEntropyNN ρ σ = ⊤ := by
  unfold umegakiRelEntropyNN
  rw [if_neg h]

end Umegaki

end SandwichedRenyiRelativeEntropy
