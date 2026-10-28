
import Quantum.QuantumEntropy.Common.PositiveDefiniteSet
import Quantum.QuantumEntropy.Common.RealComplexOrder
import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.SandwichedRenyiBase.Defs
import Quantum.QuantumMechanics.Channel.Basic
import Quantum.QuantumMechanics.Channel.Representations
import Quantum.QuantumMechanics.OperatorInstances
import Quantum.QuantumMechanics.QuantumState
import Quantum.TraceInequality.GeneralizedPerspectiveFunction
import Mathlib.Algebra.Central.End
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Topology.Algebra.Star.Unitary

open scoped Quantum.TraceInequality.Loewner
open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct
universe u
namespace RenyiDPI
open scoped RenyiDPI.Sym
noncomputable def rightAverage
    {K E : Type u} [Qudit K] [Qudit E]
    (X : L (K ⊗[ℂ] E)) : L (K ⊗[ℂ] E) :=
  TensorProduct.map (traceOutRight X)
    ((Module.finrank ℂ E : ℂ)⁻¹ • (1 : L E))
def LiebConcavityPD : Prop :=
  ∀ {H : Type u} [Qudit H] [Nontrivial H] {p : ℝ},
    0 < p → p < 1 → ∀ K : L H,
      JointlyConcaveOn (pdSetLM (ℋ := H)) (pdSetLM (ℋ := H))
        (liebTraceMapLM p K)
def SandwichedMonotoneOnPosDefGt : Prop :=
  ∀ {H K : Type u} [Qudit H] [Nontrivial H] [Qudit K] [Nontrivial K]
    (E : CPTP H K) {α : ℝ} {ρ σ : L H},
    1 < α →
    ρ ∈ pdSetLM (ℋ := H) → σ ∈ pdSetLM (ℋ := H) →
    E.toFun ρ ∈ pdSetLM (ℋ := K) → E.toFun σ ∈ pdSetLM (ℋ := K) →
    sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) ≤
      sandwichedRenyiDiv α ρ σ
end RenyiDPI
