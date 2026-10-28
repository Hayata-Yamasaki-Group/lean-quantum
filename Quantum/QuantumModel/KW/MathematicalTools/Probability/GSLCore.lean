/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.MeasurementEntropy.GSLCore
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
import Quantum.QuantumEntropy.TensorCFCLMCompat.GSLCore
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Topology.Defs.Filter
import Quantum.QuantumEntropy.YoungInequalityLMCompat.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiNonNegExtra.GSLCore
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCoreGeneralizedStein
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCore
import Mathlib.Algebra.Order.Rearrangement
import Quantum.OperationalProbabilistic.Decomposition.ConditionedStates.GSLCore
import Quantum.OperationalProbabilistic.Framework.ExactCompression.GSLCore
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Intrinsic
import Quantum.OperationalProbabilistic.Framework.NormalizedEffects.GSLCore
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Quantum.OperationalProbabilistic.DistinguishableStates.Core.GSLCore
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.GroupTheory.Perm.Fin
import Quantum.TraceInequality.LiebAndo.BlockDiagonal
import Quantum.QuantumModel.NativeTraceDistance.GSLCore
import Quantum.QuantumModel.NativeTraceDistance.GSLCoreRetained
import Quantum.QuantumModel.NativeMeasuredRelativeEntropy.GSLCore
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Quantum.OperationalProbabilistic.Framework.QuantumRelativeEntropyLaws.GSLCoreRetained
import Quantum.OperationalProbabilistic.Framework.TestingRegionHockeyStick.GSLCore
import Quantum.OperationalProbabilistic.OperationalFidelity.GSLCore
import Quantum.QuantumEntropy.Common.TensorDensitySupport.GSLCoreGeneralizedStein
import Quantum.QuantumEntropy.SandwichedRenyiBase.MaxRelativeEntropy.Monotonicity
import Quantum.QuantumEntropy.SandwichedRenyiRelativeEntropy
import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneCore
import Quantum.QuantumEntropy.UmegakiDPI.ViaPetz.FromRenyi.GSLCore
import Quantum.QuantumModel.HighInterfaces.GSLCoreRetained
import Quantum.QuantumModel.NativeFidelity.GSLCoreRetained

/-!
# A `Qudit` instance on `ℂ`

This module keeps a `Qudit` instance on `ℂ` whose name `complexQudit` is private; the instance
itself is not local and is found by instance search in every module that imports this one.
-/

noncomputable section

namespace QuantumModel

open MeasureTheory Set
open QuantumState
open scoped BigOperators

universe u

/-- `ℂ` as a `Qudit`. The name is private, but the instance is global: instance search finds it
in every module that imports this file. -/
private noncomputable instance complexQudit : Qudit ℂ where
  toNormedAddCommGroup := inferInstance
  toInnerProductSpace := inferInstance
  toCompleteSpace := inferInstance
  fg_top := Module.Finite.fg_top

end QuantumModel
