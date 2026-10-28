import Quantum.QuantumEntropy.Common.TraceRe
import Quantum.QuantumEntropy.Common.PositiveDefiniteSet

namespace SandwichedRenyiRelativeEntropy

open GeneralizedPerspectiveFunction QuantumState QuantumChannel MeasureTheory TensorProduct
open scoped ComplexOrder NNReal Topology

universe u

/-- Strict positivity of the LM-native trace at the canonical CLM boundary. -/
lemma trace_re_pos_of_ne_zero_clm
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] {ρ : B ℋ}
    (hρ : 0 ≤ ρ) (hne : ρ ≠ 0) :
    0 < (traceCLM ρ).re := by
  have hρ_pos : ρ.IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive ρ).mp hρ
  have hA : (0 : L ℋ) ≤ (ρ : L ℋ) :=
    (LinearMap.nonneg_iff_isPositive (ρ : L ℋ)).mpr hρ_pos.toLinearMap
  have hA0 : (ρ : L ℋ) ≠ 0 := by
    intro hzero
    apply hne
    ext x
    simpa using congrArg (fun A : L ℋ => A x) hzero
  simpa [traceCLM] using QuantumEntropy.trace_re_pos_of_ne_zero hA hA0

end SandwichedRenyiRelativeEntropy
