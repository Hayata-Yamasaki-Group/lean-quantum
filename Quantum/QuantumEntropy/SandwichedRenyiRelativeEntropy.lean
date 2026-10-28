/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.SandwichedRenyi.Stinespring

/-!
# Sandwiched Rényi relative entropy: positive-definite core

Importing this module (through `Quantum.QuantumEntropy.SandwichedRenyi.Stinespring`) makes
available the positive-definite sandwiched Rényi development: definitions and the Frank-Lieb
variational representation, conjugated-power variational formulas, joint convexity with
unitary/tensor laws, and Stinespring/continuity helpers.  The module itself adds one
attainment lemma.
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState GeneralizedPerspectiveFunction
open scoped ComplexOrder
universe u
variable {ℋ : Type u} [Qudit ℋ]

/-- On a positive-definite input pair and below order one, `quasiVarOpt` is a
positive-definite variational witness and attains the raw sandwiched quasi
functional.  This is an attainment lemma provided for use with variational formulas. -/
lemma quasiVarOpt_attains_quasi_lt_pd {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    quasiVarOpt α ρ σ ∈ pdSetLM (ℋ := ℋ) ∧
      quasiVar α ρ σ (quasiVarOpt α ρ σ) = sandwichedQuasi α ρ σ := by
  exact ⟨quasiVarOpt_pdSetLM hα0 (ne_of_lt hα1) hρ hσ,
    quasiVarOpt_eq_quasi_lt hα0 hα1
      ((LinearMap.nonneg_iff_isPositive ρ).mp (nonneg_of_pdSetLM hρ))
      ((LinearMap.nonneg_iff_isPositive σ).mp (nonneg_of_pdSetLM hσ))
      (isUnit_of_pdSetLM hσ) (isUnit_of_pdSetLM hρ)⟩

end SandwichedRenyiRelativeEntropy
