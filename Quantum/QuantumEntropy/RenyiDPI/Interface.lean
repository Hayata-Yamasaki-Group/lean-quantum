/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Defs
import Quantum.QuantumEntropy.Common.Umegaki.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiBase.NonNeg.Defs
import Quantum.QuantumMechanics.Channel.Basic


/-! # Laws for fixed Rényi divergences

Petz orders lie in `(0, 1)` and sandwiched orders in `(1, ∞)`.
Data processing concerns arbitrary nonnegative inputs and takes values in `EReal`.
Tensor additivity concerns four density operators. The one-sided order-one limits
are real-valued, trace-normalized Umegaki limits on positive-definite inputs.
All logarithms are natural.
-/

namespace RenyiDPI

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder Topology TensorProduct

universe u v

/-- Nonnegative Petz DPI, with source and target in the same universe. -/
def PetzMonotoneOnNonNeg : Prop :=
  ∀ {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ} {ρ σ : L ℋ},
    α ∈ Set.Ioo (0 : ℝ) 1 → 0 ≤ ρ → 0 ≤ σ →
    petzDivNN α (E.toFun ρ) (E.toFun σ) ≤ petzDivNN α ρ σ

/-- Nonnegative sandwiched DPI for orders strictly greater than one. -/
def SandwichedMonotoneOnNonNeg : Prop :=
  ∀ {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ} {ρ σ : L ℋ},
    1 < α → 0 ≤ ρ → 0 ≤ σ →
    sandwichedRenyiDivNN α (E.toFun ρ) (E.toFun σ) ≤ sandwichedRenyiDivNN α ρ σ

/-- Petz additivity on density pairs, allowing different tensor universes. -/
def PetzTensorAdditiveOnDensity : Prop :=
  ∀ {ℋ : Type u} {𝒦 : Type v} [Qudit ℋ] [Qudit 𝒦]
    [Nontrivial ℋ] [Nontrivial 𝒦] [Nontrivial (ℋ ⊗[ℂ] 𝒦)]
    {α : ℝ} (ρ₁ σ₁ : L ℋ) (ρ₂ σ₂ : L 𝒦),
    α ∈ Set.Ioo (0 : ℝ) 1 →
    IsDensity ρ₁ → IsDensity σ₁ → IsDensity ρ₂ → IsDensity σ₂ →
    petzDivNN α (TensorProduct.map ρ₁ ρ₂) (TensorProduct.map σ₁ σ₂) =
      petzDivNN α ρ₁ σ₁ + petzDivNN α ρ₂ σ₂

/-- Sandwiched additivity on density pairs; zero factors are excluded by density. -/
def SandwichedTensorAdditiveOnDensity : Prop :=
  ∀ {ℋ : Type u} {𝒦 : Type v} [Qudit ℋ] [Qudit 𝒦]
    [Nontrivial ℋ] [Nontrivial 𝒦] [Nontrivial (ℋ ⊗[ℂ] 𝒦)]
    {α : ℝ} (ρ₁ σ₁ : L ℋ) (ρ₂ σ₂ : L 𝒦),
    1 < α →
    IsDensity ρ₁ → IsDensity σ₁ → IsDensity ρ₂ → IsDensity σ₂ →
    sandwichedRenyiDivNN α (TensorProduct.map ρ₁ ρ₂) (TensorProduct.map σ₁ σ₂) =
      sandwichedRenyiDivNN α ρ₁ σ₁ + sandwichedRenyiDivNN α ρ₂ σ₂

/-- The real, trace-normalized Petz left limit on positive-definite inputs. -/
def PetzLimitAtOneOnPosDef : Prop :=
  ∀ {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] {ρ σ : L ℋ},
    ρ ∈ pdSetLM (ℋ := ℋ) → σ ∈ pdSetLM (ℋ := ℋ) →
    Filter.Tendsto (fun α : ℝ => petzDiv α ρ σ)
      (𝓝[<] (1 : ℝ)) (𝓝 (umegakiNorm ρ σ))

/-- The existing real sandwiched right limit on positive-definite inputs. -/
def SandwichedLimitAtOneOnPosDef : Prop :=
  ∀ {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] {ρ σ : L ℋ},
    ρ ∈ pdSetLM (ℋ := ℋ) → σ ∈ pdSetLM (ℋ := ℋ) →
    Filter.Tendsto (fun α : ℝ => sandwichedRenyiDiv α ρ σ)
      (𝓝[>] (1 : ℝ)) (𝓝 (umegakiNorm ρ σ))

/-- Data processing, tensor additivity and the order-one limit for Petz divergence. -/
structure PetzSide where
  route : Lean.Name
  monotoneOnNonNeg : PetzMonotoneOnNonNeg.{u}
  tensorAdditivity : PetzTensorAdditiveOnDensity.{u, v}
  limitAtOne : PetzLimitAtOneOnPosDef.{u}

/-- Data processing, tensor additivity and the order-one limit for sandwiched divergence. -/
structure SandwichedSide where
  route : Lean.Name
  monotoneOnNonNeg : SandwichedMonotoneOnNonNeg.{u}
  tensorAdditivity : SandwichedTensorAdditiveOnDensity.{u, v}
  limitAtOne : SandwichedLimitAtOneOnPosDef.{u}

end RenyiDPI
