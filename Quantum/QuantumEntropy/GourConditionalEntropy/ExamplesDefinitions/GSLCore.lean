import Quantum.QuantumEntropy.GourConditionalEntropy.Definitions.GSLCore
import Quantum.QuantumEntropy.GourQuantumRelativeEntropyBasicProperties.GSLCore
import Quantum.QuantumEntropy.Gour.Sandwiched.EndpointClassification.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiNonNegExtra.GSLCore
import Quantum.QuantumMechanics.DiagonalDensity.GSLCore
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.Provider
import Quantum.QuantumMechanics.DensityOperator.GSLCore
import Mathlib.Topology.Order.AtTopBotIxx
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
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
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Analysis.Convex.Function
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivDPI.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivConcrete.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiOrder.GSLCore
import Quantum.OperationalProbabilistic.Framework.MeasurementEntropy.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiDivergence.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiRelativeEntropyLimits.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiPowerFDivBridge.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiRelativeEntropy.GSLCore
import Quantum.OperationalProbabilistic.Framework.OrderedConeMaxRelativeEntropy.GSLCore
import Quantum.QuantumEntropy.PetzTraceClassification.GSLCore
import Quantum.QuantumEntropy.GourShortedOperator.GSLCore
import Quantum.QuantumEntropy.PetzSupportRpowContinuity.GSLCore
import Quantum.QuantumEntropy.Common.Umegaki.GSLCoreUmegaki

open QuantumState QuantumChannel GourChoi GourSemiCausal
open scoped TensorProduct ComplexOrder BigOperators ENNReal

universe u

namespace GourConditionalEntropy

/-- The von Neumann entropy in bits, `-Re Tr (ρ log ρ) / log 2`. It is defined for every
operator; entropy statements assume that `ρ` is a density operator. The same quantity in
nats is `VonNeumann.vonNeumannEntropy`. -/
noncomputable def vonNeumannEntropy {A : Type u} [Qudit A] (ρ : L A) : ℝ :=
  -(Tr (ρ * CFC.log ρ)).re / Real.log 2

/-- The Umegaki relative entropy in bits: `umegakiRelEntropyNN ρ σ / log 2`. It is `⊤` when the
support of `ρ` is not contained in that of `σ`. The density hypotheses of
`OPT.GourMatrixStateDivergence` are not used by the formula. -/
noncomputable def umegakiBits : OPT.GourMatrixStateDivergence.{u} :=
  fun ρ σ _ _ => ((1 / Real.log 2 : ℝ) : EReal) *
    SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN ρ σ

end GourConditionalEntropy
