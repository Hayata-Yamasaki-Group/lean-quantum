/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.VonNeumann.StateTensor
import Quantum.QuantumEntropy.VonNeumann.PartialTraceThirdCPTPKWCompat.GSLCore
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCoreGeneralizedStein
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCore
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Quantum.OperationalProbabilistic.Decomposition.ConditionedStates.GSLCore
import Mathlib.LinearAlgebra.Matrix.Trace
import Quantum.OperationalProbabilistic.Framework.ExactCompression.GSLCore
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Quantum.OperationalProbabilistic.Framework.NormalizedEffects.GSLCore
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Instances.Matrix
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Logic.Equiv.Bool
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Quantum.OperationalProbabilistic.DistinguishableStates.Core.GSLCore
import Quantum.OperationalProbabilistic.Framework.StateNorms.GSLCore
import Quantum.QuantumModel.MatrixHockeyStick.GSLCore
import Quantum.OperationalProbabilistic.Framework.MeasurementStatistics.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestingRegionHockeyStick.GSLCore
import Mathlib.RingTheory.MatrixAlgebra

/-!
# Range inclusion under unitary conjugation

`unitaryConjugateEnd_range_le_iff`: range inclusion between operators is preserved and
reflected by conjugation with a unitary.
-/

open Matrix QuantumState
open scoped TensorProduct

namespace OPT
namespace Decomposition

noncomputable section

universe u v

section ProductCarrier

variable {ι : Type u} {κ : Type v}
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

variable [Nonempty ι] [Nonempty κ]

end ProductCarrier

section UnitaryDensity

/-- Unitary conjugation preserves and reflects inclusion of operator ranges. -/
theorem unitaryConjugateEnd_range_le_iff
    {E F : Type*} [Qudit E] [Qudit F]
    (U : E ≃ₗᵢ[ℂ] F) (X Y : L E) :
    LinearMap.range (QuantumChannel.conjugateEnd U.toLinearEquiv X) ≤
        LinearMap.range (QuantumChannel.conjugateEnd U.toLinearEquiv Y) ↔
      LinearMap.range X ≤ LinearMap.range Y := by
  constructor
  · intro h x hx
    obtain ⟨z, rfl⟩ := hx
    have hz : U (X z) ∈ LinearMap.range
        (QuantumChannel.conjugateEnd U.toLinearEquiv X) := by
      refine ⟨U z, ?_⟩
      simp [QuantumChannel.conjugateEnd]
    obtain ⟨w, hw⟩ := h hz
    refine ⟨U.symm w, ?_⟩
    have := congrArg U.symm hw
    simpa [QuantumChannel.conjugateEnd] using this
  · intro h x hx
    obtain ⟨z, rfl⟩ := hx
    obtain ⟨w, hw⟩ := h ⟨U.symm z, rfl⟩
    refine ⟨U w, ?_⟩
    simp [QuantumChannel.conjugateEnd, hw]

end UnitaryDensity

section TripleCarrier

variable {ι : Type u} {κ : Type v} {ν : Type*}
variable [Fintype ι] [Fintype κ] [Fintype ν]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]
variable [Nonempty ι] [Nonempty κ] [Nonempty ν]

end TripleCarrier

section ThirdTraceCarrier

variable {ι κ ν : Type u}
variable [Fintype ι] [Fintype κ] [Fintype ν]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]
variable [Nonempty ι] [Nonempty κ] [Nonempty ν]

end ThirdTraceCarrier

end

end Decomposition
end OPT
