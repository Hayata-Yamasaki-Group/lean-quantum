/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.PositiveDefiniteSet
import Quantum.QuantumEntropy.Common.Umegaki.GSLCore
import Quantum.QuantumMechanics.Channel.Basic
import Quantum.QuantumMechanics.OperatorInstances
import Quantum.QuantumMechanics.QuantumState

namespace UmegakiDPI

open GeneralizedPerspectiveFunction QuantumState QuantumChannel
open SandwichedRenyiRelativeEntropy

universe u

/-- Positive-definite Umegaki data processing. -/
def MonotoneOnPosDef : Prop :=
  ∀ {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {ρ σ : L ℋ},
    ρ ∈ pdSetLM (ℋ := ℋ) → σ ∈ pdSetLM (ℋ := ℋ) →
    E.toFun ρ ∈ pdSetLM (ℋ := 𝒦) → E.toFun σ ∈ pdSetLM (ℋ := 𝒦) →
    umegakiNorm (E.toFun ρ) (E.toFun σ) ≤ umegakiNorm ρ σ

/-- Available proof routes for positive-definite Umegaki data processing. -/
inductive ProviderRoute
  | sandwichedRenyi
  | hiaiPetz

/-- The positive-definite Umegaki data-processing inequality.

The route is metadata for display and probes; the proof is carried by the value itself. -/
structure Provider where
  route : ProviderRoute
  monotoneOnPosDef : MonotoneOnPosDef.{u}

end UmegakiDPI
