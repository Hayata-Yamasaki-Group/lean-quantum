/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.OrderedConeMaxRelativeEntropy.GSLCore
import Quantum.QuantumMechanics.DensityOperator.GSLCore
import Quantum.QuantumMechanics.OperatorInstances
import Quantum.QuantumMechanics.QuantumState

/-!
# Max-relative entropy for density operators

The density-operator specialization of ordered-cone max-relative entropy.
-/

open scoped ComplexOrder

namespace OPT.OrderedCone

open QuantumState

universe u

/-- On density operators, a finite max-relative entropy has an attained
domination exponent. -/
theorem maxRelEntropy_attained_of_isDensity
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (hfinite : maxRelEntropy rho sigma ≠ ⊤) :
    ∃ lam : ℝ,
      maxRelEntropy rho sigma = (lam : EReal) ∧
        rho ≤ (((2 : ℝ) ^ lam : ℝ) : ℂ) • sigma := by
  have hne : {lam : ℝ | rho ≤ ((2 : ℝ) ^ lam) • sigma}.Nonempty := by
    by_contra hempty
    apply hfinite
    apply maxRelEntropy_eq_top_of_dominationSet_empty
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    obtain ⟨lam, _, hlam⟩ := hz
    exact hempty ⟨lam, hlam⟩
  have hbdd : BddBelow {lam : ℝ |
      rho ≤ ((2 : ℝ) ^ lam) • sigma} := by
    refine ⟨0, ?_⟩
    intro lam hlam
    have hdom : rho ≤ (((2 : ℝ) ^ lam : ℝ) : ℂ) • sigma := by
      simpa only [Complex.coe_smul] using hlam
    have hdiff : 0 ≤
        (((2 : ℝ) ^ lam : ℝ) : ℂ) • sigma - rho :=
      sub_nonneg.mpr hdom
    have htrace := ((LinearMap.nonneg_iff_isPositive _).mp hdiff).trace_nonneg
    have hre := (Complex.nonneg_iff.mp htrace).1
    rw [map_sub, map_smul, hsigma.2, hrho.2, smul_eq_mul, mul_one,
      Complex.sub_re, Complex.ofReal_re, Complex.one_re] at hre
    by_contra hlamNonneg
    have hlamNeg : lam < 0 := lt_of_not_ge hlamNonneg
    have hpowLt : (2 : ℝ) ^ lam < 1 := by
      simpa only [Real.rpow_zero] using
        ((Real.strictMono_rpow_of_base_gt_one (b := 2) (by norm_num)).lt_iff_lt.mpr
          hlamNeg)
    linarith
  obtain ⟨lam, hlam, hdom⟩ := maxRelEntropy_attained rho sigma hne hbdd
  exact ⟨lam, hlam, by simpa only [Complex.coe_smul] using hdom⟩

end OPT.OrderedCone
