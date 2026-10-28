/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.Gour.Sandwiched.Definitions.GSLCore

/-! # Endpoint classification for the all-order Gour wrapper -/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel OPT
open scoped ComplexOrder ENNReal NNReal


universe u v w
theorem gourSandwichedRenyiBits_standard_order
    {H : Type u} [Qudit H] [Nontrivial H]
    {alpha : ENNReal} (hzero : alpha ≠ 0) (hone : alpha ≠ 1)
    (htop : alpha ≠ ⊤) (halpha : 1 / 2 ≤ alpha.toReal)
    (rho sigma : L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    gourSandwichedRenyiBits alpha rho sigma hrho hsigma =
      standardSandwichedRenyiBitsFinite alpha.toReal rho sigma := by
  rw [gourSandwichedRenyiBits, dif_neg hzero, dif_neg hone, dif_neg htop,
    if_neg (not_lt.mpr halpha)]

end SandwichedRenyiRelativeEntropy
