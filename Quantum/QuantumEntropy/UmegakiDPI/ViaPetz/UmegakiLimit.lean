/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.UmegakiDPI.ViaPetz.FromRenyi.GSLCore

import Quantum.QuantumEntropy.RenyiDPI.Petz.SelectedProvider


/-!
# Umegaki data processing via the selected Petz provider (via2)

This module derives positive-definite Umegaki data processing
from the selected Petz provider: its nonnegative DPI and logarithmic left limit.
-/

namespace UmegakiDPI

open QuantumState QuantumChannel QuantumEntropy
open SandwichedRenyiRelativeEntropy
open scoped QuantumEntropy
open scoped ComplexOrder MatrixOrder Topology

noncomputable section

universe u

variable {ℋ : Type u} [Qudit ℋ]

variable [Nontrivial ℋ]

/-- Positive-definite Umegaki data processing obtained from the selected Petz provider (via2).
The name is historical: the proof uses `RenyiDPI.selectedPetzProvider`, whichever Petz
provider is selected. -/
theorem umegakiNorm_monotone_via_hiaiPetz
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ))
    (hEρ : E.toFun ρ ∈ pdSetLM (ℋ := 𝒦))
    (hEσ : E.toFun σ ∈ pdSetLM (ℋ := 𝒦)) :
    umegakiNorm (E.toFun ρ) (E.toFun σ) ≤ umegakiNorm ρ σ :=
  monotoneOnPosDef_of_petz RenyiDPI.selectedPetzProvider E hρ hσ hEρ hEσ

end

end UmegakiDPI
