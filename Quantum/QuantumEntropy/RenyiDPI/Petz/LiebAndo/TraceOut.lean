/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Petz.LiebAndo.Haar
import Quantum.QuantumEntropy.RenyiDPI.Petz.LiebAndo.Tensor
import Quantum.QuantumMechanics.Channel.ChoiKraus

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

theorem petzTracePower_le_traceOutRight :
∀ {K E : Type u} [Qudit K] [Qudit E]
  [Nontrivial K] [Nontrivial E] [Nontrivial (K ⊗[ℂ] E)]
  {α : ℝ} {X Y : L (K ⊗[ℂ] E)},
  α ∈ Set.Ioo (0 : ℝ) 1 → 0 ≤ X → 0 ≤ Y →
  petzTracePower α X Y ≤
    petzTracePower α (traceOutRight X) (traceOutRight Y) := by
  intro K E _ _ _ _ _ α X Y hα hX hY
  have htrace_nonneg (Z : L (K ⊗[ℂ] E)) (hZ : 0 ≤ Z) :
      0 ≤ traceOutRight Z := by
    simpa only [map_zero] using (traceOutRight_le_traceOutRight hZ)
  have htwirl (Z : L (K ⊗[ℂ] E)) :
      (∫ U, rightOrbit Z U ∂(HaarUnitary.haarUnitary E)) =
        TensorProduct.map (traceOutRight Z)
          ((Module.finrank ℂ E : ℂ)⁻¹ • (1 : L E)) :=
    HaarUnitary.twirl_eq_partialTrace_right_smul_id Z
  have h := petzTracePower_le_haar_average hα hX hY
  rw [htwirl X, htwirl Y,
    petzTracePower_tensor_maxmixed (H := K) (K := E) hα (htrace_nonneg X hX)
      (htrace_nonneg Y hY)] at h
  exact h

end RenyiDPI
