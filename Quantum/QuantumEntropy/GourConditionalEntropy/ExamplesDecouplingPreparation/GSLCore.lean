/-
This module retains the imports and generates equation lemmas for
`QuantumState.Tr` and `GourConditionalEntropy.w40Q`.
-/

import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesCollisionDefinitions.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.Definitions.GSLCore
import Quantum.QuantumEntropy.GourSemiCausalMemory.GSLCore
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Fin.Tuple.Sort
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
import Mathlib.Analysis.Convex.Jensen
import Quantum.QuantumEntropy.GourQuantumMaxRelativeEntropy.GSLCore
import Quantum.QuantumMechanics.DiagonalDensity.GSLCore
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
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
import Quantum.OperationalProbabilistic.Framework.MeasuredLift.GSLCore
import Quantum.QuantumMechanics.SpectralPinching.GSLCore
import Quantum.OperationalProbabilistic.Framework.OrderedConeMaxRelativeEntropyDensity.GSLCore
import Quantum.OperationalProbabilistic.Framework.QuantumRelativeEntropyLaws.GSLCoreRetained
import Quantum.OperationalProbabilistic.Framework.TestingRegion.GSLCore
import Quantum.QuantumEntropy.Gour.Sandwiched.CyclicTrace.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesDecouplingDefinitions.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyi.Internal.BridgeCertificates
import Quantum.QuantumEntropy.SandwichedRenyiRelativeEntropy
import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneCore
import Quantum.QuantumEntropy.UmegakiDPI.ViaPetz.FromRenyi.GSLCore
import Quantum.QuantumMechanics.Channel.ChoiKrausGeneralizedStein
import Quantum.QuantumMechanics.QuantumChannel
import Quantum.TraceInequality.GeneralizedPerspectiveFunctionRetained
import Quantum.TraceInequality.HansenPedersen.LownerHeinzTheorem
import Quantum.TraceInequality.LiebTrace.MonotonicityRetained
import Quantum.TraceInequality.LownerHeinz.ReciprocalRetained

namespace GourConditionalEntropy

section

open QuantumState QuantumChannel GourConditionalEntropy MeasureTheory
open scoped TensorProduct ComplexOrder ENNReal
universe u

set_option autoImplicit false

end

section

open QuantumState QuantumChannel GourConditionalEntropy MeasureTheory
open scoped TensorProduct ComplexOrder ENNReal
universe u

set_option autoImplicit false

end

section

open QuantumState QuantumChannel GourConditionalEntropy MeasureTheory
open scoped TensorProduct ComplexOrder ENNReal
universe u

set_option autoImplicit false

end

section

open QuantumState QuantumChannel GourConditionalEntropy MeasureTheory
open scoped TensorProduct ComplexOrder ENNReal
universe u

set_option autoImplicit false

end

section

open QuantumState QuantumChannel GourConditionalEntropy MeasureTheory
open scoped TensorProduct ComplexOrder ENNReal
universe u

set_option autoImplicit false

end

section

open QuantumState QuantumChannel GourConditionalEntropy MeasureTheory
open scoped TensorProduct ComplexOrder ENNReal
universe u

set_option autoImplicit false

end

section

open QuantumState QuantumChannel GourConditionalEntropy MeasureTheory
open scoped TensorProduct ComplexOrder ENNReal
universe u

set_option autoImplicit false

end

section

open QuantumState QuantumChannel GourConditionalEntropy MeasureTheory
open scoped TensorProduct ComplexOrder ENNReal
universe u

set_option autoImplicit false

end

section

open QuantumState QuantumChannel GourConditionalEntropy MeasureTheory
open scoped TensorProduct ComplexOrder ENNReal
universe u

set_option autoImplicit false

end

section

open QuantumState QuantumChannel GourConditionalEntropy MeasureTheory
open scoped TensorProduct ComplexOrder ENNReal
universe u

set_option autoImplicit false

end

section

open QuantumState QuantumChannel GourConditionalEntropy MeasureTheory
open scoped TensorProduct ComplexOrder ENNReal
universe u

set_option autoImplicit false

end

section

open QuantumState QuantumChannel GourConditionalEntropy MeasureTheory
open scoped TensorProduct ComplexOrder ENNReal
universe u

set_option autoImplicit false

end

section

open QuantumState QuantumChannel GourConditionalEntropy MeasureTheory
open scoped TensorProduct ComplexOrder ENNReal
universe u

set_option autoImplicit false

end

end GourConditionalEntropy
