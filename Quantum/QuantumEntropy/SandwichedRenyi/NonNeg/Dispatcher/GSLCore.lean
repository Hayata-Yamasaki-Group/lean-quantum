/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.SandwichedRenyi.NonNeg.LowAlpha.GSLCore
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.Provider
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificatesGeneralizedStein
import Quantum.QuantumEntropy.Common.TensorDensitySupport.GSLCoreGeneralizedStein
import Quantum.QuantumEntropy.Common.TraceReGeneralizedStein
import Quantum.QuantumEntropy.SandwichedRenyi.Internal.BridgeCertificates
import Quantum.QuantumEntropy.SandwichedRenyiRelativeEntropy
import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneCore
import Quantum.QuantumEntropy.UmegakiDPI.ViaSandwiched.AlphaOne
import Quantum.QuantumMechanics.Channel.ChoiKrausGeneralizedStein
import Quantum.QuantumMechanics.QuantumChannel
import Quantum.TraceInequality.GeneralizedPerspectiveFunctionRetained
import Quantum.TraceInequality.HansenPedersen.LownerHeinzTheorem
import Quantum.TraceInequality.LiebTrace.MonotonicityRetained
import Quantum.TraceInequality.LownerHeinz.ReciprocalRetained

/-! Full-order consumer dispatcher: fixed low-order DPI and selected high-order DPI. -/

namespace RenyiDPI
open SandwichedRenyiRelativeEntropy QuantumState QuantumChannel
open scoped ComplexOrder
universe u

/-- Data processing for the non-negative sandwiched Rényi divergence for all orders
`α ≥ 1/2`, `α ≠ 1`: below order one it uses the fixed low-order proof, above order one the
selected sandwiched provider. -/
theorem sandwichedRenyiDivNN_monotone
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    sandwichedRenyiDivNN α (E.toFun ρ)
      (E.toFun σ) ≤ sandwichedRenyiDivNN α ρ σ := by
  rcases lt_or_gt_of_ne hα_ne1 with hα_lt | hα_gt
  · exact sandwichedRenyiDivNN_monotone_low E hα_ge hα_lt hρ hσ
  · exact sandwichedMonotoneOnNonNeg E hα_gt hρ hσ

end RenyiDPI
