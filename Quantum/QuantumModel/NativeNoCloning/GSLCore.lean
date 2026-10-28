/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.EffectsAndPreparations.GSLCore
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Quantum.QuantumModel.NativeEffectStateDefinitions.GSLCore
import Quantum.QuantumModel.HighInterfaces.GSLCore
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformConvergence
import Quantum.OperationalProbabilistic.Framework.OrderedConeMaxRelativeEntropy.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestOutcomes.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiOrder.GSLCore
import Quantum.OperationalProbabilistic.Framework.MeasurementEntropy.GSLCore
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Probability.Distributions.Uniform
import Quantum.OperationalProbabilistic.Framework.QuantumRelativeEntropyLaws.GSLCore
import Mathlib.Geometry.Convex.Cone.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Topology
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.IsLUB
import Quantum.OperationalProbabilistic.Framework.LosslessConditioning.GSLCore
import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Quantum.OperationalProbabilistic.Framework.FiniteIIDPMF.GSLCore
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.Convex.Independent
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Quantum.OperationalProbabilistic.Framework.StateNorms.GSLCore
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Matrix.ToLin
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivConcrete.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivergence.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiDivergence.GSLCore
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import Quantum.OperationalProbabilistic.Framework.Core.GSLCore
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Quantum.OperationalProbabilistic.Framework.TestingRegionDecisionDefinitions.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestsCore.GSLCore
import Quantum.OperationalProbabilistic.MeasuredRelativeEntropy.GSLCore
import Mathlib.Analysis.Convex.Strict

/-!
# Native superoperators and categorical states

The type `Superoperator` of native superoperators and the conversion `toState` of a normalized
density matrix to a categorical state, with its basic properties.
-/

noncomputable section

namespace QuantumModel
namespace NativeNoCloning

open QuantumState
open scoped Kronecker

/-- Native Hermiticity-preserving superoperators.  Complete positivity and
trace preservation are imposed separately by `QuantumModel.IsChannel`. -/
abbrev Superoperator (A B : Sys) := HPHom A B

end NativeNoCloning

namespace DensityMatrix

open QuantumState

@[ext]
theorem ext {A : Sys} {rho sigma : DensityMatrix A}
    (h : rho.operator = sigma.operator) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl

/-- A density matrix regarded as its canonical normalized preparation.  The
construction purifies spectrally and then discards the purifying system. -/
def toState {A : Sys} (rho : DensityMatrix A) :
    OPT.State (Sys := Sys) A :=
  OPT.marginalLeft (Sys := Sys)
    (rankOnePreparation
      (jointSpaceEquiv A (canonicalPurifier A)
        (spectralPurification rho).vector))

/-- State/preparation dictionary: the output of `toState` is the original
density operator. -/
theorem toState_apply_id {A : Sys} (rho : DensityMatrix A) :
    HPHom.toRawSuperoperator rho.toState
        (LinearMap.id : Operator tensorUnitSystem) = rho.operator := by
  rw [toState, marginalLeft_rankOnePreparation_joint]
  exact spectralPurification_purifies rho

/-- Every density matrix determines a normalized quantum preparation. -/
theorem toState_isNormalizedState {A : Sys} (rho : DensityMatrix A) :
    OPT.IsNormalizedState (Sys := Sys) rho.toState := by
  let psi := (spectralPurification rho).vector
  let v := jointSpaceEquiv A (canonicalPurifier A) psi
  have hv : ‖v‖ = 1 := by
    simpa [v, psi] using
      (jointSpaceEquiv A (canonicalPurifier A)).norm_map psi |>.trans
        (spectralPurification rho).norm_one
  have hpreparation :
      OPT.IsNormalizedState (Sys := Sys) (rankOnePreparation v) :=
    rankOnePreparation_isNormalizedState v hv
  exact marginalLeft_isNormalizedState_of_normalized hpreparation

/-- The two directions of the state/density dictionary are inverse on
normalized preparations. -/
theorem toState_ofNormalizedState {A : Sys}
    (rho : OPT.State (Sys := Sys) A)
    (hrho : OPT.IsNormalizedState (Sys := Sys) rho) :
    (ofNormalizedState rho hrho).toState = rho := by
  apply state_eq_of_apply_id_eq
  rw [toState_apply_id]
  rfl

end DensityMatrix

namespace NativeNoCloning

open CategoryTheory
open QuantumState

end NativeNoCloning
end QuantumModel
