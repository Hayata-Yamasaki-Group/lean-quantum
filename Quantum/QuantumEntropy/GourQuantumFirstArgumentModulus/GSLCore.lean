/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.GourQuantumThompsonDistance.GSLCore
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Quantum.OperationalProbabilistic.Framework.OrderedConeMaxRelativeEntropyDensity.GSLCore
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Quantum.QuantumEntropy.SandwichedRenyiUmegaki
import Mathlib.Topology.Semicontinuity.Basic
import Quantum.OperationalProbabilistic.Framework.QuantumRelativeEntropyLaws.GSLCoreRetained
import Quantum.OperationalProbabilistic.Framework.TestingRegion.GSLCore
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificatesGeneralizedStein
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

open scoped ComplexOrder

namespace OPT

noncomputable section

universe u

open QuantumState QuantumChannel
open SandwichedRenyiRelativeEntropy

/-- A finite real sublevel of quantum max-relative entropy is exactly the
corresponding closed operator-domination sublevel. -/
theorem quantumMaxRelativeEntropyBits_le_coe_iff_domination
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (r : ℝ) :
    quantumMaxRelativeEntropyBits ⟨rho, hrho⟩ ⟨sigma, hsigma⟩ ≤ (r : EReal) ↔
      rho ≤ (((2 : ℝ) ^ r : ℝ) : ℂ) • sigma := by
  constructor
  · intro hle
    have hfinite : quantumMaxRelativeEntropyBits ⟨rho, hrho⟩ ⟨sigma, hsigma⟩ ≠ ⊤ := by
      intro htop
      rw [htop] at hle
      exact (not_le_of_gt (EReal.coe_lt_top r)) hle
    obtain ⟨lam, hlam, hdom⟩ :=
      OrderedCone.maxRelEntropy_attained_of_isDensity
        rho sigma hrho hsigma hfinite
    have hlamQ :
        quantumMaxRelativeEntropyBits ⟨rho, hrho⟩ ⟨sigma, hsigma⟩ =
          (lam : EReal) := by
      simpa only [quantumMaxRelativeEntropyBits] using hlam
    have hlamLe : lam ≤ r := by
      rw [hlamQ] at hle
      exact_mod_cast hle
    have hpowLe : (2 : ℝ) ^ lam ≤ (2 : ℝ) ^ r :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hlamLe
    have hsigmaNonneg : (0 : L H) ≤ sigma :=
      (LinearMap.nonneg_iff_isPositive _).mpr hsigma.1
    have hpowLeComplex :
        (((2 : ℝ) ^ lam : ℝ) : ℂ) ≤ (((2 : ℝ) ^ r : ℝ) : ℂ) := by
      exact_mod_cast hpowLe
    exact hdom.trans (smul_le_smul_of_nonneg_right
      hpowLeComplex hsigmaNonneg)
  · intro hdom
    exact OrderedCone.maxRelEntropy_le_of_domination (by
      simpa only [Complex.coe_smul] using hdom)

end

end OPT
