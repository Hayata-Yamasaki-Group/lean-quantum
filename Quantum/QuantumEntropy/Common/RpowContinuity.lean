/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.OperatorScalarTower
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-!
# Continuity of non-negative operator powers

Canonical continuous functional calculus on the non-negative cone.
-/

open QuantumState
open scoped ComplexOrder NNReal Topology

namespace SandwichedRenyiRelativeEntropy

universe u

/-- For `0 ≤ p`, the map `A ↦ CFC.rpow A p` is continuous on the cone of non-negative
    operators. (A positive power `x ↦ x^p` is continuous up to `0` in `ℝ≥0`, so unlike the
    positive-definite version no spectral gap away from `0` is required.) -/
lemma continuousOn_rpow_nonneg
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] {p : ℝ} (hp : 0 ≤ p) :
    ContinuousOn (fun A : B 𝒦 => CFC.rpow A p)
      {A : B 𝒦 | (0 : B 𝒦) ≤ A} :=
  (continuousOn_id (s := {A : B 𝒦 | (0 : B 𝒦) ≤ A}))
    |>.cfc_nnreal_of_mem_nhdsSet (s := Set.univ) (f := (· ^ p)) Filter.univ_mem
      (ha' := fun _ hA => hA) (hf := (NNReal.continuous_rpow_const hp).continuousOn)

end SandwichedRenyiRelativeEntropy

