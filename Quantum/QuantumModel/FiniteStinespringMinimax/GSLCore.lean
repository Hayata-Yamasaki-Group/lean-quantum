/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.NativeTraceDistance.GSLCore
import Quantum.QuantumModel.HighInterfaces.GSLCore
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
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
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.IsLUB
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Quantum.OperationalProbabilistic.Framework.LosslessConditioning.GSLCore
import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Analysis.Convex.Integral
import Quantum.OperationalProbabilistic.Framework.EffectsAndPreparations.GSLCore
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
import Quantum.QuantumModel.NativeNoCloning.GSLCore
import Quantum.QuantumModel.NativeMeasuredRelativeEntropy.GSLCore
import Mathlib.Analysis.InnerProductSpace.PiL2
import Quantum.QuantumModel.NativeFidelity.GSLCore


/-!
# Compactness of the set of density operators

`densityOperatorSet` is closed, bounded and compact.
-/

noncomputable section

namespace QuantumModel

open CategoryTheory
open QuantumState
open Set
open scoped BigOperators MonoidalCategory TensorProduct

/-! ## Compact convex carriers -/

/-- The ambient operator carrier of finite-dimensional density matrices. -/
def densityOperatorSet (A : Sys) : Set (Operator A) :=
  {X | 0 ≤ X ∧ Tr X = 1}

/-- The density-operator carrier is closed in the operator-norm topology. -/
theorem densityOperatorSet_isClosed (A : Sys) :
    IsClosed (densityOperatorSet A) := by
  have hnonneg : IsClosed {X : Operator A | 0 ≤ X} :=
    isClosed_le continuous_const continuous_id
  have htrace : Continuous (fun X : Operator A => Tr X) :=
    LinearMap.continuous_of_finiteDimensional _
  change IsClosed
    ({X : Operator A | 0 ≤ X} ∩ {X : Operator A | Tr X = 1})
  exact hnonneg.inter (isClosed_eq htrace continuous_const)

/-- The density-operator carrier is norm bounded. -/
theorem densityOperatorSet_isBounded (A : Sys) :
    Bornology.IsBounded (densityOperatorSet A) := by
  letI : Nontrivial (Space A) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by simpa using A.dim_pos)
  apply Bornology.IsBounded.subset
    (Metric.isBounded_closedBall : Bornology.IsBounded
      (Metric.closedBall (0 : Operator A) 1))
  intro X hX
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnorm := SandwichedRenyiRelativeEntropy.norm_le_re_trace_lm hX.1
  simpa [hX.2] using hnorm

/-- The density-operator carrier is compact in finite dimension. -/
theorem densityOperatorSet_isCompact (A : Sys) :
    IsCompact (densityOperatorSet A) := by
  letI : FiniteDimensional ℂ (Operator A) := by infer_instance
  letI : ProperSpace (Operator A) :=
    FiniteDimensional.proper ℂ (Operator A)
  exact Metric.isCompact_of_isClosed_isBounded
    (densityOperatorSet_isClosed A) (densityOperatorSet_isBounded A)

end QuantumModel
