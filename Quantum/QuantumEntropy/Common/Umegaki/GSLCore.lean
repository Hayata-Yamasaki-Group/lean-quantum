/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.Support
import Quantum.QuantumEntropy.CFCTransport

/-! # Normalized Umegaki relative entropy

Definitions and the trace representation of normalized Umegaki relative entropy.
-/

namespace SandwichedRenyiRelativeEntropy

open GeneralizedPerspectiveFunction QuantumState QuantumChannel MeasureTheory
open scoped ComplexOrder NNReal Topology

universe u

section Umegaki

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

/-- **Normalised Umegaki relative entropy**
    `(Tr ρ)⁻¹ · Re Tr(ρ (log ρ − log σ))`. -/
noncomputable def umegakiNorm (ρ σ : L ℋ) : ℝ :=
  (Tr (ρ * (CFC.log ρ - CFC.log σ))).re / (Tr ρ).re

theorem umegakiNorm_eq_toContinuousLinearMap
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (ρ σ : L ℋ) :
    umegakiNorm ρ σ =
      (Tr (((ρ.toContinuousLinearMap *
        (CFC.log ρ.toContinuousLinearMap - CFC.log σ.toContinuousLinearMap) : B ℋ) :
          L ℋ))).re / (Tr ρ).re := by
  rw [umegakiNorm, ← CFCTransport.cfc_log_toCLM ρ,
    ← CFCTransport.cfc_log_toCLM σ]
  rfl

end Umegaki

end SandwichedRenyiRelativeEntropy
