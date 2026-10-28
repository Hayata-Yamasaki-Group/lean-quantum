
import Quantum.QuantumEntropy.Common.RealComplexOrder
import Quantum.QuantumMechanics.OperatorInstances
import Quantum.QuantumMechanics.QuantumState
import Mathlib.Algebra.Central.End
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Topology.Algebra.Star.Unitary

open scoped Quantum.TraceInequality.Loewner
open QuantumState QuantumChannel
open scoped ComplexOrder Topology TensorProduct
universe u
namespace RenyiDPI
namespace Sym
scoped instance realSelfModule : Module ℝ ℝ := Semiring.toModule
noncomputable scoped instance lmRealCFC {H : Type u} [Qudit H] :
    ContinuousFunctionalCalculus ℝ (L H) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus
end Sym
open scoped RenyiDPI.Sym
noncomputable def rightOrbit
    {K E : Type u} [Qudit K] [Qudit E]
    (X : L (K ⊗[ℂ] E)) (U : unitary (L E)) : L (K ⊗[ℂ] E) :=
  TensorProduct.map (1 : L K) (U : L E) * X *
    TensorProduct.map (1 : L K) (star (U : L E))
end RenyiDPI
