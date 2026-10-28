/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.KW.Entropies.RenyiAnalysis.GSLCoreRetained
import Quantum.QuantumEntropy.SandwichedRenyiNonNegKWExtra.GSLCore
import Quantum.QuantumModel.FixedOutcomePOVM.GSLCore
import Quantum.QuantumModel.NativeMeasuredRelativeEntropy.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiOrder.GSLCore
import Quantum.QuantumModel.RegularizationCarrier.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiUmegakiKWExtra.GSLCore
import Quantum.QuantumModel.KW.Entropies.SteinPrerequisites

/-!
# Khatri--Wilde Stein protocols and rates

This file defines binary testing protocols and the predicates for achievable
and strong-converse rates used by the quantum Stein lemma in Khatri--Wilde,
arXiv:2011.04672v2, `entropies.tex:7178--7387`. Tensor copies use `systemPow`
and `densityTensorPow`. The remaining lemmas establish Petz and sandwiched
Rényi divergence identities on the tensor unit, tensor-power additivity,
and convergence to Umegaki relative entropy as the order tends to one.
-/

noncomputable section

open QuantumState
open scoped ENNReal NNReal ComplexOrder MatrixOrder Topology

namespace QuantumModel
namespace NativeStein

open NativeHypothesisTesting
open Filter

attribute [local instance] operatorSelfAdjointUnitalCFCStein

attribute [local instance] operatorNonnegSpectrumStein

/-! ## Rényi divergences on the tensor unit and tensor powers, and the order-one limit -/

private theorem petzRenyiDivBits_tensorUnit_self
    (alpha : ℝ) :
    petzRenyiDivBits alpha tensorUnitDensity
      tensorUnitDensity.operator = 0 := by
  have hq : petzQuasi alpha tensorUnitDensity tensorUnitDensity.operator = 1 := by
    unfold petzQuasi tensorUnitDensity
    change (Tr (CFC.rpow (1 : Operator tensorUnitSystem) alpha *
      CFC.rpow (1 : Operator tensorUnitSystem) (1 - alpha))).re = 1
    simp only [CFC.rpow_eq_pow, CFC.one_rpow, one_mul]
    change (Tr tensorUnitDensity.operator).re = 1
    rw [tensorUnitDensity.trace_one]
    norm_num
  unfold petzRenyiDivBits
  rw [hq, if_neg one_ne_zero, Real.logb_one]
  norm_num

private theorem sandwichedRenyiDivBits_tensorUnit_self
    (alpha : ℝ) (halpha : 1 < alpha) :
    sandwichedRenyiDivBits alpha tensorUnitDensity
      tensorUnitDensity.operator = 0 := by
  have hsupp : SandwichedRenyiRelativeEntropy.suppLE
      tensorUnitDensity.operator tensorUnitDensity.operator := le_rfl
  have hq : SandwichedRenyiRelativeEntropy.sandwichedQuasi alpha
      tensorUnitDensity.operator tensorUnitDensity.operator = 1 := by
    unfold SandwichedRenyiRelativeEntropy.sandwichedQuasi tensorUnitDensity
    change Tr (CFC.rpow
      (CFC.rpow (1 : Operator tensorUnitSystem) ((1 - alpha) / (2 * alpha)) *
        (1 : Operator tensorUnitSystem) *
        CFC.rpow (1 : Operator tensorUnitSystem) ((1 - alpha) / (2 * alpha))) alpha) = 1
    simp only [CFC.rpow_eq_pow, CFC.one_rpow, mul_one]
    change Tr tensorUnitDensity.operator = 1
    exact tensorUnitDensity.trace_one
  unfold sandwichedRenyiDivBits
  unfold SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN
  rw [if_neg]
  · unfold SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv
    rw [hq]
    rw [show Tr tensorUnitDensity.operator = 1 from tensorUnitDensity.trace_one]
    norm_num
  · push_neg
    exact ⟨fun _ => hsupp, fun h => absurd halpha (not_lt_of_ge h.le)⟩

/-- Petz Rényi additivity on every positive tensor power.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:1653--1754,7286--7289` (`prop-Petz_rel_ent`,
`eq:stein-lower`), where binary tensor additivity is iterated over the copies
used in the Stein lower bound. -/
theorem petzRenyiDivBits_densityTensorPow
    {A : Sys} (alpha : ℝ) (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (rho sigma : DensityMatrix A) (n : ℕ) :
    petzRenyiDivBits alpha (densityTensorPow rho (n + 1))
        (densityTensorPow sigma (n + 1)).operator =
      (((n + 1 : ℕ) : ℝ) : EReal) *
        petzRenyiDivBits alpha rho sigma.operator := by
  rw [EReal.coe_natCast, ← EReal.nsmul_eq_mul]
  induction n with
  | zero =>
      change petzRenyiDivBits alpha
          (densityTensor rho tensorUnitDensity)
          (densityTensor sigma tensorUnitDensity).operator = _
      rw [petzRenyiDivBits_densityTensor alpha halpha0 halpha1,
        petzRenyiDivBits_tensorUnit_self]
      simp
  | succ n ih =>
      change petzRenyiDivBits alpha
          (densityTensor rho (densityTensorPow rho (n + 1)))
          (densityTensor sigma (densityTensorPow sigma (n + 1))).operator = _
      rw [petzRenyiDivBits_densityTensor alpha halpha0 halpha1, ih]
      calc
        petzRenyiDivBits alpha rho sigma.operator +
              (n + 1) • petzRenyiDivBits alpha rho sigma.operator =
            (n + 1) • petzRenyiDivBits alpha rho sigma.operator +
              petzRenyiDivBits alpha rho sigma.operator := add_comm _ _
        _ = (Nat.succ n + 1) • petzRenyiDivBits alpha rho sigma.operator := by
          rw [show Nat.succ n + 1 = Nat.succ (n + 1) by omega]
          exact (succ_nsmul (petzRenyiDivBits alpha rho sigma.operator) (n + 1)).symm

/-- Sandwiched Rényi additivity on every positive tensor power, including
the extended-value support-mismatch branch.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:2261--2272,2419--2437,7320--7326`
(`prop-sand_rel_ent_properties`, `eq-sand_ren_rel_ent_additive`,
`eq:stein-upper`), where binary additivity is iterated over the copies used
in the Stein upper bound. -/
theorem sandwichedRenyiDivBits_densityTensorPow
    {A : Sys} (alpha : ℝ) (halpha : 1 < alpha)
    (rho sigma : DensityMatrix A) (n : ℕ) :
    sandwichedRenyiDivBits alpha (densityTensorPow rho (n + 1))
        (densityTensorPow sigma (n + 1)).operator =
      (((n + 1 : ℕ) : ℝ) : EReal) *
        sandwichedRenyiDivBits alpha rho sigma.operator := by
  rw [EReal.coe_natCast, ← EReal.nsmul_eq_mul]
  induction n with
  | zero =>
      change sandwichedRenyiDivBits alpha
          (densityTensor rho tensorUnitDensity)
          (densityTensor sigma tensorUnitDensity).operator = _
      rw [sandwichedRenyiDivBits_densityTensor alpha halpha,
        sandwichedRenyiDivBits_tensorUnit_self alpha halpha]
      simp
  | succ n ih =>
      change sandwichedRenyiDivBits alpha
          (densityTensor rho (densityTensorPow rho (n + 1)))
          (densityTensor sigma (densityTensorPow sigma (n + 1))).operator = _
      rw [sandwichedRenyiDivBits_densityTensor alpha halpha, ih]
      calc
        sandwichedRenyiDivBits alpha rho sigma.operator +
              (n + 1) • sandwichedRenyiDivBits alpha rho sigma.operator =
            (n + 1) • sandwichedRenyiDivBits alpha rho sigma.operator +
              sandwichedRenyiDivBits alpha rho sigma.operator := add_comm _ _
        _ = (Nat.succ n + 1) • sandwichedRenyiDivBits alpha rho sigma.operator := by
          rw [show Nat.succ n + 1 = Nat.succ (n + 1) by omega]
          exact (succ_nsmul
            (sandwichedRenyiDivBits alpha rho sigma.operator) (n + 1)).symm

/-- Density-pair Petz Rényi divergence converges from below to Umegaki
relative entropy.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:1566--1651,7269--7273` (`prop-petz_rel_ent_lim_1`), whose
order-one limit is invoked in the achievable-rate half of Stein's lemma. -/
theorem petzRenyiDivBits_tendsto_umegaki
    {A : Sys} (rho sigma : DensityMatrix A) :
    Tendsto (fun alpha : ℝ => petzRenyiDivBits alpha rho sigma.operator)
      (𝓝[<] (1 : ℝ)) (𝓝 (umegakiRelEntropyBits rho sigma.operator)) :=
  petzRenyiDivBits_tendsto_umegaki_of_nonneg rho sigma.operator sigma.nonneg

end NativeStein
end QuantumModel
