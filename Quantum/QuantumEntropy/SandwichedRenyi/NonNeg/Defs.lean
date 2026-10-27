import Quantum.QuantumEntropy.Common.SupportOrder
/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.SandwichedRenyi.NonNeg.Support
import Quantum.QuantumEntropy.SandwichedRenyi.QuasiJensen.ConcavityLinear
import Quantum.QuantumMechanics.OperatorBridge

/-!
# Non-negative sandwiched Rényi divergence: definitions

Support inclusion, the Frank-Lieb explicit EReal formula, and spectral/order lemmas
used by the non-negative data-processing proof.
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel MeasureTheory TensorProduct
open scoped ComplexOrder NNReal Topology

universe u

/-! ### Frank–Lieb explicit formula -/

/-- **Frank–Lieb extended sandwiched Rényi divergence** for non-negative `ρ, σ`.

    For `α > 0`, `α ≠ 1`, the value is `⊤ : EReal` exactly on the region where the
    true divergence is `+∞`, and the real-valued `sandwichedRenyiDiv α ρ σ`
    (coerced to `EReal`) otherwise:

    * `α > 1` and `supp(ρ) ⊄ supp(σ)` (i.e. `¬ SupportLE ρ σ`): value `⊤`.
      (`CFC.rpow σ ((1−α)/(2α))` would need the genuine inverse, divergent on `ker σ`.)
    * `α < 1` and `ρ ≠ 0` and `Q_α(ρ‖σ) = 0` (i.e. `ρ ⊥ σ`, orthogonal supports):
      value `⊤`. Here `Real.log 0 = 0` would otherwise give the *wrong* value `0`,
      whereas the true divergence is `+∞` (since `1/(α−1) < 0`).
    * otherwise: value `sandwichedRenyiDiv α ρ σ`.

    When the inverse-bridge images of `ρ, σ` belong to `pdSetLM`, the kernel of `σ` is
    trivial and `Q_α > 0`, so the formula agrees with the standard divergence in `EReal`. -/
noncomputable def sandwichedRenyiDivNN
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (α : ℝ)
    (ρ σ : L ℋ) : EReal :=
  letI : Decidable ((1 < α ∧ ¬ SupportLE ρ σ) ∨
      (α < 1 ∧ ρ ≠ 0 ∧ (sandwichedQuasi α ρ σ).re = 0)) := Classical.propDecidable _
  if (1 < α ∧ ¬ SupportLE ρ σ) ∨
      (α < 1 ∧ ρ ≠ 0 ∧ (sandwichedQuasi α ρ σ).re = 0)
    then (⊤ : EReal)
  else ((sandwichedRenyiDiv α ρ σ : ℝ) : EReal)

end SandwichedRenyiRelativeEntropy
