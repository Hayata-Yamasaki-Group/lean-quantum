import Quantum.QuantumMechanics.QuantumChannelKWCompat.GSLCore
import Quantum.QuantumModel.DirectInstances.GSLCore
import Quantum.QuantumModel.Purification.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiUmegakiKWExtra.GSLCore
import Quantum.OperationalProbabilistic.Framework.ExactCompression.GSLCore
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Mathlib.Analysis.Matrix.Order

/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

/-!
# Finite-dimensional quantum-model interfaces

Instances for deterministic-family completion and raw effect extensionality (through rank-one
preparations), and the bridge from Hilbert-space bipartite vectors to categorical states and
their left marginals.
-/

noncomputable section

namespace QuantumModel

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped ComplexOrder
open scoped MatrixOrder
open scoped Matrix.Norms.L2Operator

variable {A B : Sys}

/-- A finite family of quantum transformations whose total preserves trace is
already a quantum instrument.  This is the finite-family form of the
instrument-completion boundary used by the higher OPT producers. -/
instance instFiniteDeterministicFamilyCompletionTheory :
    OPT.FiniteDeterministicFamilyCompletionTheory Sys where
  completes_to_test := by
    intro A B ι _ T hT htotal
    change IsQuantumTest T
    constructor
    · intro i
      exact (hT i).1
    · apply isChannel_of_isEvent_comp_traceEffect
      · exact isEvent_sum T (fun i => (hT i).1)
      · simpa using htotal

end QuantumModel
