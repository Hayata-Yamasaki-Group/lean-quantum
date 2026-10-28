/-
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.TensorCFCLMCompat.GSLCore
import Quantum.QuantumEntropy.Common.Umegaki.GSLCoreUmegaki
import Quantum.QuantumEntropy.SandwichedRenyiBase.NonNeg.Defs
import Quantum.QuantumEntropy.SandwichedRenyiUmegakiKWExtra.GSLCore
import Quantum.QuantumModel.KW.Distances.HypothesisTestingBounds.RelativeEntropy.GSLCore
import Quantum.QuantumModel.NativeMeasuredRelativeEntropy.GSLCore
import Quantum.QuantumModel.RegularizationCarrier.GSLCore
import Quantum.QuantumModel.Skeleton.GSLCore
import Quantum.QuantumModel.SupportCompression.GSLCore

/-!
# Rényi analysis for native quantum-model carriers

This module supplies the support-sensitive binary tensor laws and the two
one-sided order-one limits used by the Stein prerequisites.
-/

noncomputable section

open QuantumState QuantumChannel TensorProduct Filter Set
open scoped ComplexOrder MatrixOrder Topology TensorProduct ENNReal NNReal

namespace QuantumModel.NativeHypothesisTesting

open SandwichedRenyiRelativeEntropy

local instance operatorSelfAdjointUnitalCFCRenyiAnalysis (A : Sys) :
    ContinuousFunctionalCalculus ℝ (Operator A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

local instance operatorNonnegSpectrumRenyiAnalysis (A : Sys) :
    NonnegSpectrumClass ℝ (Operator A) :=
  CStarAlgebra.instNonnegSpectrumClass

/-- The support-sensitive sandwiched Rényi divergence in bits converges from
above to native Umegaki relative entropy for every positive second argument.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:2174--2257` (`prop-sand_ren_ent_lim`,
`eq:QEI:sandwiched-Renyi-to-Umegaki`). -/
theorem sandwichedRenyiDivBits_tendsto_umegaki_of_nonneg
    {A : Sys} (rho : DensityMatrix A) (sigma : Operator A)
    (hsigma : 0 ≤ sigma) :
    Tendsto (fun alpha => sandwichedRenyiDivBits alpha rho sigma)
      (𝓝[>] (1 : ℝ)) (𝓝 (umegakiRelEntropyBits rho sigma)) := by
  have h := SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN_tendsto_umegaki
    rho.operator sigma rho.nonneg hsigma rho.operator_ne_zero
  unfold sandwichedRenyiDivBits umegakiRelEntropyBits
  simpa only [EReal.div_eq_inv_mul] using EReal.Tendsto.const_mul h
    (Or.inl (by rw [← EReal.coe_inv]; exact EReal.coe_ne_bot _))
    (Or.inl (by rw [← EReal.coe_inv]; exact EReal.coe_ne_top _))

end QuantumModel.NativeHypothesisTesting
