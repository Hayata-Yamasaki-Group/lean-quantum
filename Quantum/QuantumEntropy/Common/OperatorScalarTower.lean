/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.PositiveDefiniteSet
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel MeasureTheory TensorProduct
open GeneralizedPerspectiveFunction
open scoped ComplexOrder NNReal Topology

universe u

/-- The real scalars act on continuous endomorphisms compatibly through `ℂ`. This `Prop`-valued
    instance is needed by the `ℝ`-valued (non-unital) functional-calculus
    naturality lemma `NonUnitalStarAlgHomClass.map_cfcₙ`. -/
instance instIsScalarTowerRealComplexL {ℋ : Type u} [Qudit ℋ] :
    IsScalarTower ℝ ℂ (B ℋ) where
  smul_assoc r c x := by
    change (algebraMap ℝ ℂ r * c) • x = (algebraMap ℝ ℂ r) • (c • x)
    rw [mul_smul]

end SandwichedRenyiRelativeEntropy
