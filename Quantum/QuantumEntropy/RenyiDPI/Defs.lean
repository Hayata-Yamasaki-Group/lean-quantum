/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumMechanics.OperatorBridge
import Quantum.QuantumEntropy.Common.TraceRe
import Mathlib.Data.EReal.Basic

/-!
# Fixed Petz Rényi quantities

The intended domain is `0 < α < 1` and nonnegative inputs. The logarithm
is natural and the first input's trace normalizes the trace power.
These definitions are total: zero first input has value zero, while a
nonzero first input with zero trace power has extended value `⊤`.
Finite negative values are retained in `EReal`.

The sandwiched side uses the existing
`SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv` and
`SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN` without redefining them.
-/

namespace RenyiDPI

open QuantumState QuantumEntropy

universe u

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

-- Fixed quantities need only the canonical CFC proof, not the HP scalar
-- compatibility instances imported by Common.OperatorCFC.
private local instance : ContinuousFunctionalCalculus ℝ (B ℋ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- Petz trace power in the continuous-linear-map CFC model. -/
noncomputable def petzTracePower (α : ℝ) (ρ σ : L ℋ) : ℝ :=
  realTrace (CFC.rpow ρ.toContinuousLinearMap α *
    CFC.rpow σ.toContinuousLinearMap (1 - α))

/-- Trace-normalized Petz divergence, with natural logarithm. -/
noncomputable def petzDiv (α : ℝ) (ρ σ : L ℋ) : ℝ :=
  Real.log (petzTracePower α ρ σ / (Tr ρ).re) / (α - 1)

/-- Extended Petz divergence for nonnegative inputs and `0 < α < 1`.
No support-inclusion assumption is imposed in its finite branch. -/
noncomputable def petzDivNN (α : ℝ) (ρ σ : L ℋ) : EReal :=
  letI : Decidable (ρ ≠ 0 ∧ petzTracePower α ρ σ = 0) := Classical.propDecidable _
  if ρ ≠ 0 ∧ petzTracePower α ρ σ = 0 then ⊤ else (petzDiv α ρ σ : EReal)

omit [Nontrivial ℋ] in
/-- The trace-normalization convention sends a zero first input to zero. -/
@[simp] theorem petzDiv_zero_left (α : ℝ) (σ : L ℋ) :
    petzDiv α 0 σ = 0 := by
  simp [petzDiv]

omit [Nontrivial ℋ] in
/-- The extended divergence has the same zero-input convention. -/
@[simp] theorem petzDivNN_zero_left (α : ℝ) (σ : L ℋ) :
    petzDivNN α 0 σ = 0 := by
  simp [petzDivNN]

end RenyiDPI
