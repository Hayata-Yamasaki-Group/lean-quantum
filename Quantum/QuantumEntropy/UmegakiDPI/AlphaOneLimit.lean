import Quantum.QuantumEntropy.SandwichedRenyiBase.Umegaki.AlphaOne
import Quantum.QuantumEntropy.UmegakiDPI.ViaPetz.UmegakiLimit
import Quantum.QuantumEntropy.Common.TensorDensitySupport.GSLCoreGeneralizedStein
import Quantum.QuantumEntropy.Common.TraceReGeneralizedStein
import Quantum.QuantumEntropy.RenyiDPI.Petz.Provider
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.NonNeg.Continuity
import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneCore
import Quantum.QuantumEntropy.UmegakiDPI.ViaSandwiched.FromRenyi.GSLCore
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.HilbertSchmidt.Adjoint
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.Main
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.OutputSupport.Reduction
import
  Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagOrthogonalTransport.OrthogonalConjugation
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagProjection
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagSpectralTransportRetained
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule
import Quantum.TraceInequality.HiaiPetz.HilbertSchmidt.Order
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.SharedStages
import Quantum.TraceInequality.HiaiPetz.TraceMonotonicity.StrictlyPositiveRetained
import Quantum.TraceInequality.Loewner.RealComplexOrder

/-!
# Two-sided alpha-one limit on the positive-definite domain

Source: arXiv:2607.05492v1, main.tex:219.
The existing tracePower quotient is a Petz-type left difference quotient, and
`sandwichedRenyiDiv_tendsto_umegaki` is a right limit for positive-definite inputs.
This module establishes the two-sided punctured limit on that same domain.
It does not establish the nonzero, support-included singular-input limit.

Original source: Müller-Lennert, Dupuis, Szehr, Fehr and Tomamichel,
“On quantum Rényi entropies: a new generalization and some properties”,
J. Math. Phys. 54, 122203 (2013), arXiv:1306.3142v4, alpha-one analysis.
The source anchor is at section level, without a numbered-theorem match.
-/

open QuantumState QuantumChannel GeneralizedPerspectiveFunction
open scoped ComplexOrder Topology

/-! Register the existing supporting declaration without redeclaring its type or proof. -/

namespace SandwichedRenyiRelativeEntropy
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]

/-- The two-sided punctured alpha-one limit, for positive-definite inputs only.
Source: main.tex:219; Müller-Lennert et al. (2013), alpha-one analysis.
This restricted result does not cover the singular-input support-domain alpha-one limit
(arXiv:2607.05492v1, Section 1.5). -/
theorem sandwichedRenyi_tendsto_umegaki_of_pd {ρ σ : L H} (hρ : ρ ∈ pdSetLM) (hσ : σ ∈ pdSetLM) :
    Filter.Tendsto (fun α => sandwichedRenyiDiv α ρ σ) (𝓝[≠] (1 : ℝ))
      (𝓝 (umegakiNorm ρ σ)) := by
  have hTr : 0 < (Tr ρ).re := trace_re_pos_of_pdSetLM hρ
  have hQ1 : (sandwichedQuasi 1 ρ σ).re = (Tr ρ).re :=
    sandwichedQuasi_one_re ρ.toContinuousLinearMap σ.toContinuousLinearMap
      (show 0 ≤ σ.toContinuousLinearMap from nonneg_of_pdSetLM hσ)
      (show 0 ≤ ρ.toContinuousLinearMap from nonneg_of_pdSetLM hρ)
  have hQ1ne : (sandwichedQuasi 1 ρ σ).re ≠ 0 := hQ1 ▸ ne_of_gt hTr
  have hd : HasDerivAt (fun α => Real.log (sandwichedQuasi α ρ σ).re)
      (umegakiNorm ρ σ) 1 := by
    convert (hasDerivAt_sandwichedQuasi_re_one hρ hσ).log hQ1ne using 1
    rw [hQ1, umegakiNorm_eq_toContinuousLinearMap]
  refine hd.tendsto_slope.congr' ?_
  have hαpos : ∀ᶠ α : ℝ in 𝓝[≠] (1 : ℝ), 0 < α :=
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hαpos] with α hα
  have hQne := sandwichedQuasi_re_ne_zero_of_pdSetLM hα hρ hσ
  rw [slope_def_field, hQ1, sandwichedRenyiDiv, Real.log_div hQne (ne_of_gt hTr)]
  ring

end SandwichedRenyiRelativeEntropy
