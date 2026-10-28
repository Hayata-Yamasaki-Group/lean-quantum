/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Common.Cone
import Quantum.QuantumEntropy.RenyiDPI.Common.Haar
import Quantum.QuantumEntropy.RenyiDPI.Petz.LiebAndo.Concavity
import Quantum.QuantumEntropy.RenyiDPI.Petz.LiebAndo.Isometry
import Quantum.QuantumEntropy.RenyiDPI.Petz.LiebAndo.HaarUnitaryLM.GSLCore

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

theorem petzTracePower_le_haar_average :
∀ {K E : Type u} [Qudit K] [Qudit E]
  [Nontrivial K] [Nontrivial E] [Nontrivial (K ⊗[ℂ] E)]
  {α : ℝ} {X Y : L (K ⊗[ℂ] E)},
  α ∈ Set.Ioo (0 : ℝ) 1 → 0 ≤ X → 0 ≤ Y →
  petzTracePower α X Y ≤
    petzTracePower α
      (∫ U, rightOrbit X U ∂(HaarUnitary.haarUnitary E))
      (∫ U, rightOrbit Y U ∂(HaarUnitary.haarUnitary E)) := by
  intro K E _ _ _ _ _ α X Y hα hX hY
  have hinv (U : unitary (L E)) :
      petzTracePower α (rightOrbit X U) (rightOrbit Y U) = petzTracePower α X Y := by
    let V : L (K ⊗[ℂ] E) := TensorProduct.map (1 : L K) (U : L E)
    have hs : LinearMap.adjoint V = TensorProduct.map (1 : L K) (star (U : L E)) := by
      dsimp [V]
      rw [TensorProduct.adjoint_map, ← LinearMap.star_eq_adjoint,
        ← LinearMap.star_eq_adjoint, star_one]
    have hv : (LinearMap.adjoint V).comp V = (1 : L (K ⊗[ℂ] E)) := by
      rw [hs]
      change TensorProduct.map (1 : L K) (star (U : L E)) *
        TensorProduct.map (1 : L K) (U : L E) = 1
      rw [← TensorProduct.map_mul, one_mul, (Unitary.mem_iff.mp U.property).1]
      exact TensorProduct.map_one
    have ho (Z : L (K ⊗[ℂ] E)) :
        rightOrbit Z U = (V.comp Z).comp (LinearMap.adjoint V) := by
      rw [hs]
      rfl
    rw [ho X, ho Y]
    exact petzTracePower_isometric_conj V hv hα hX hY
  have hxmem : ∀ᵐ U ∂(HaarUnitary.haarUnitary E),
      rightOrbit X U ∈ {A : L (K ⊗[ℂ] E) | 0 ≤ A} :=
    Filter.Eventually.of_forall (rightOrbit_nonneg hX)
  have hymem : ∀ᵐ U ∂(HaarUnitary.haarUnitary E),
      rightOrbit Y U ∈ {A : L (K ⊗[ℂ] E) | 0 ≤ A} :=
    Filter.Eventually.of_forall (rightOrbit_nonneg hY)
  have hxi := rightOrbit_integrable X
  have hyi := rightOrbit_integrable Y
  have hfi : MeasureTheory.Integrable (fun U => petzTracePower α (rightOrbit X U) (rightOrbit Y U))
      (HaarUnitary.haarUnitary E) := by
    simp_rw [hinv]
    exact MeasureTheory.integrable_const _
  have hxavg := (nonnegCone_convex (H := K ⊗[ℂ] E)).integral_mem nonnegCone_isClosed hxmem hxi
  have hyavg := (nonnegCone_convex (H := K ⊗[ℂ] E)).integral_mem nonnegCone_isClosed hymem hyi
  have hj := HaarUnitary.jointly_concave_le_integral (μ := HaarUnitary.haarUnitary E)
    nonnegCone_convex nonnegCone_convex nonnegCone_isClosed nonnegCone_isClosed
    (petzTracePower_jointlyConcave_nonneg_liebAndo hα) (petzTracePower_continuousOn_nonneg hα)
    hxmem hymem hxi hyi hfi hxavg hyavg
  simpa only [hinv, MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul] using hj

end RenyiDPI
