/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.NativeNoCloning.GSLCore
import Quantum.OperationalProbabilistic.Framework.ExactCompression.GSLCore
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Quantum.QuantumEntropy.SandwichedRenyiNonNegKWExtra.GSLCore

/-!
# Pure density matrices

`pureOfUnitVector`: the pure density matrix of a unit vector.
-/

noncomputable section

namespace QuantumModel

open CategoryTheory
open QuantumState
open scoped ComplexOrder

namespace DensityMatrix

/-- The pure density matrix associated with a unit Hilbert-space vector. -/
def pureOfUnitVector {A : Sys} (v : Space A) (hv : ‖v‖ = 1) : DensityMatrix A where
  operator := QuantumChannel.outer_product v v
  nonneg := QuantumChannel.outer_product_self_nonneg v
  trace_one := by
    rw [QuantumChannel.trace_outer_product]
    simp [inner_self_eq_norm_sq_to_K, hv]

end DensityMatrix

end QuantumModel
