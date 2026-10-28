/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.Gour.Sandwiched.PinchingAndIsometry.GSLCore
import Quantum.QuantumEntropy.GourQuantumMaxRelativeEntropy.GSLCore

/-!
# All-order sandwiched Rényi divergence in bits

`gourSandwichedRenyiBits` is the all-order sandwiched Rényi divergence in bits, following Gour's
convention.
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel OPT
open scoped ComplexOrder ENNReal NNReal


universe u v w

/-! ## all-order Gour wrapper -/

/-- Gour's all-order sandwiched Rényi relative entropy in bits.

The endpoint orders `0`, `1`, and `infinity` are dispatched before
`ENNReal.toReal` is inspected.  Below order one half, orthogonality is tested
before the reversed finite divergence is evaluated, and the reversed value
is multiplied by the source coefficient `alpha / (1 - alpha)`. -/
noncomputable def gourSandwichedRenyiBits
    {H : Type u} [Qudit H] [Nontrivial H]
    (alpha : ENNReal) (rho sigma : L H)
    (hrho : IsDensity rho) (hsigma : IsDensity sigma) : EReal := by
  classical
  exact if hzero : alpha = 0 then
      petzQuantumRenyiDivergenceFinite ⟨0, by norm_num⟩
        rho sigma hrho hsigma
    else if hone : alpha = 1 then
      petzQuantumRenyiDivergenceFinite ⟨1, by norm_num⟩
        rho sigma hrho hsigma
    else if htop : alpha = ⊤ then
      quantumMaxRelativeEntropyBits ⟨rho, hrho⟩ ⟨sigma, hsigma⟩
    else if alpha.toReal < 1 / 2 then
      if rho * sigma = 0 then ⊤
      else
        (((alpha.toReal / (1 - alpha.toReal) : ℝ) : EReal) *
          standardSandwichedRenyiBitsFinite
            (1 - alpha.toReal) sigma rho)
    else
      standardSandwichedRenyiBitsFinite alpha.toReal rho sigma

end SandwichedRenyiRelativeEntropy
