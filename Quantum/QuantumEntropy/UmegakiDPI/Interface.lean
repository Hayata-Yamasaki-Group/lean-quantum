/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneDefinitions

namespace UmegakiDPI

open GeneralizedPerspectiveFunction QuantumState QuantumChannel
open SandwichedRenyiRelativeEntropy

universe u

/-- Provider-neutral statement of positive-definite Umegaki data processing. -/
def MonotoneOnPosDef : Prop :=
  ∀ {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦) {ρ σ : L ℋ},
    ρ ∈ pdSetLM (ℋ := ℋ) → σ ∈ pdSetLM (ℋ := ℋ) →
    Φ.toFun ρ ∈ pdSetLM (ℋ := 𝒦) → Φ.toFun σ ∈ pdSetLM (ℋ := 𝒦) →
    umegakiNorm (Φ.toFun ρ) (Φ.toFun σ) ≤ umegakiNorm ρ σ

/-- Route labels for positive-definite Umegaki data processing.
This repository supplies a provider for `sandwichedRenyi` only. -/
inductive ProviderRoute
  | sandwichedRenyi
  | hiaiPetz

/-- A proof provider for positive-definite Umegaki data processing.

The route is metadata for display and probes; the proof is carried by the value itself. -/
structure Provider where
  route : ProviderRoute
  monotoneOnPosDef : MonotoneOnPosDef.{u}

@[deprecated MonotoneOnPosDef (since := "2026-09-02")]
abbrev MonotonePdStmt : Prop := MonotoneOnPosDef.{u}

end UmegakiDPI
