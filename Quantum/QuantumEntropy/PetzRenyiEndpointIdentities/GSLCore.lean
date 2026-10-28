/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.PetzRenyiRelativeEntropyLaws.GSLCore

/-!
# The order-zero endpoint of the Petz Rényi divergence

The min quantum relative entropy `quantumMinRelativeEntropy`, and the vanishing of the order-zero
support trace power exactly when `rho * sigma = 0`
(`petzSupportTracePower_zero_eq_zero_iff_mul_eq_zero`).
-/

namespace OPT

open Filter QuantumState SandwichedRenyiRelativeEntropy
open scoped BigOperators ENNReal Topology

universe u

/-- At order zero, vanishing support overlap is equivalent to a vanishing
product of the two density operators. -/
theorem petzSupportTracePower_zero_eq_zero_iff_mul_eq_zero
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    petzSupportTracePower 0 rho sigma = 0 ↔ rho * sigma = 0 := by
  constructor
  · intro htrace
    by_contra hmul
    exact (petzSupportTracePower_pos_of_lt_one_of_mul_ne_zero
      0 rho sigma hrho hsigma (by norm_num) hmul).ne' htrace
  · intro hmul
    exact (petzTraceExpression_eq_some_zero_of_lt_one_of_mul_eq_zero
      0 rho sigma (by norm_num) hrho hsigma (by norm_num) hmul).2.1

/-- The min quantum relative entropy in bits. -/
noncomputable def quantumMinRelativeEntropy
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : L H) (_hrho : IsDensity rho) (_hsigma : IsDensity sigma) : EReal := by
  classical
  exact if rho * sigma = 0 then
      ⊤
    else
      ((-Real.logb 2 (petzSupportTracePower 0 rho sigma) : ℝ) : EReal)

end OPT
