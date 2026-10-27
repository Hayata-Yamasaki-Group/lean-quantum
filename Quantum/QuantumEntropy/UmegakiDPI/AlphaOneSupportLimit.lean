import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneSupportContinuity
import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneSupportCompression

open QuantumState QuantumChannel GeneralizedPerspectiveFunction
open scoped ComplexOrder NNReal Topology
namespace SandwichedRenyiRelativeEntropy.AlphaOneSupport
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
attribute [local instance] subspaceQudit

/-- Use `quasi_derivative_psd_pd`, `compression_domain`, and `compression_invariance`
to differentiate the logarithm; the trace is positive. -/
lemma log_quasi_derivative_support {ρ σ : L H} (hρ : 0 ≤ ρ) (hρ0 : ρ ≠ 0)
    (hσ : 0 ≤ σ) (hsupp : SupportLE ρ σ) :
    HasDerivAt (fun α => Real.log (sandwichedQuasi α ρ σ).re)
      (umegakiNorm ρ σ) 1 := by
  obtain ⟨hS, hρc, _, hσc⟩ := compression_domain hρ hρ0 hσ hsupp
  letI := hS
  obtain ⟨hTr, hQ, _, hU⟩ := compression_invariance hρ hσ hsupp
  have hQ1 : (sandwichedQuasi 1 (compress σ ρ) (compress σ σ)).re =
      (Tr (compress σ ρ)).re :=
    sandwichedQuasi_one_re (compress σ ρ).toContinuousLinearMap
      (compress σ σ).toContinuousLinearMap (nonneg_of_pdSetLM hσc) hρc
  have hpos : 0 < (Tr (compress σ ρ)).re := by
    rw [hTr]
    exact QuantumEntropy.trace_re_pos_of_ne_zero hρ hρ0
  have hd : HasDerivAt
      (fun α => Real.log (sandwichedQuasi α (compress σ ρ) (compress σ σ)).re)
      (umegakiNorm (compress σ ρ) (compress σ σ)) 1 := by
    convert (quasi_derivative_psd_pd hρc hσc).log (hQ1 ▸ ne_of_gt hpos) using 1
    rw [hQ1]
    rfl
  rw [hU] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with α hα
  exact congrArg (fun z : ℂ => Real.log z.re) (hQ α hα).symm



end SandwichedRenyiRelativeEntropy.AlphaOneSupport

namespace SandwichedRenyiRelativeEntropy
open AlphaOneSupport
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]

/-- The two-sided alpha-one limit on the full nonzero PSD support domain. -/
theorem tendsto_sandwichedRenyiDiv_umegakiNorm_of_supportLE {ρ σ : L H}
    (hρ : 0 ≤ ρ) (hρ0 : ρ ≠ 0) (hσ : 0 ≤ σ) (hsupp : SupportLE ρ σ) :
    Filter.Tendsto (fun α => sandwichedRenyiDiv α ρ σ) (𝓝[≠] (1 : ℝ))
      (𝓝 (umegakiNorm ρ σ)) := by
  exact tendsto_of_log_derivative hρ hρ0 hσ
    (log_quasi_derivative_support hρ hρ0 hσ hsupp)


end SandwichedRenyiRelativeEntropy

