/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.UmegakiDPI.Interface
import Quantum.QuantumEntropy.RenyiDPI.Interface
import Quantum.QuantumEntropy.UmegakiDPI.ViaSandwiched.AlphaOne

/-! # Positive-definite Umegaki data processing from Rényi limits

The nonnegative Rényi data-processing inequality and its one-sided order-one
limit imply the positive-definite Umegaki data-processing inequality.
-/

namespace UmegakiDPI

open QuantumState QuantumChannel QuantumEntropy SandwichedRenyiRelativeEntropy
open scoped ComplexOrder Topology

universe u

/-- Sandwiched Rényi data processing and its order-one limit imply positive-definite Umegaki data
processing. -/
theorem monotoneOnPosDef_of_sandwiched (p : RenyiDPI.SandwichedSide.{u, u}) :
    MonotoneOnPosDef.{u} := by
  intro H _ _ K _ _ E ρ σ hρ hσ hEρ hEσ
  have hTarget := p.limitAtOne hEρ hEσ
  have hSource := p.limitAtOne hρ hσ
  refine le_of_tendsto_of_tendsto hTarget hSource ?_
  filter_upwards [self_mem_nhdsWithin] with α hα
  have hDPI := p.monotoneOnNonNeg E hα (nonneg_of_pdSetLM hρ) (nonneg_of_pdSetLM hσ)
  rw [RenyiDPI.sandwichedDivNN_eq_coe_of_posDef hα hEρ hEσ,
    RenyiDPI.sandwichedDivNN_eq_coe_of_posDef hα hρ hσ] at hDPI
  exact_mod_cast hDPI

end UmegakiDPI
