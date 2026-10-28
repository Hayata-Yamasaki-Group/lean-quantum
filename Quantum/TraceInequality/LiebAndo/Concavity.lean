/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LiebAndo.PowerMean
import Quantum.TraceInequality.LiebTrace.Monotonicity
import Quantum.TraceInequality.LiebAndo.OperatorGeometricMean

namespace LiebAndoTrace

universe u

open LownerHeinzTheorem
open GeneralizedPerspectiveFunction
open HilbertSchmidtOperatorSpace
open OperatorGeometricMean
open Module.End Polynomial

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [FiniteDimensional ℂ ℋ] [Nontrivial ℋ]

/-! ### Lieb trace concavity and convexity -/
-- The `HSOp`-valued `operatorPowerMean` terms are large enough
-- that the skeleton itself is expensive.
/--
Source: I. Nikoufar, A. Ebadian, M. Eshaghi Gordji, "The simplest proof of Lieb concavity
theorem", Advances in Mathematics 248 (2013), 531--533, Theorem 1.2(b) (from Theorem 1.1).
Version using the real part of the trace with the power mean on the Hilbert–Schmidt operator space.
This declaration is about the real part of the trace; its identification with the complex trace
needs a separate argument, which is not formalized here.
Source: arXiv:2607.05492v1, §3.
-/
theorem liebTrace_jointlyConcaveOn_pdSet
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (K : (ℋ →L[ℂ] ℋ)) :
    JointlyConcaveOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (liebTraceMap (ℋ := ℋ) s K) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hleft_combo :
      (1 - θ) • leftMulHS (ℋ := ℋ) A₁ + θ • leftMulHS (ℋ := ℋ) A₂ =
        leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂) := by
    ext T
    change ((1 - θ) • (A₁ * toOp T) + θ • (A₂ * toOp T) : (ℋ →L[ℂ] ℋ)) =
      ((1 - θ) • A₁ + θ • A₂) * toOp T
    rw [add_mul, smul_mul_assoc, smul_mul_assoc]
  have hright_combo :
      (1 - θ) • rightMulHS (ℋ := ℋ) B₁ + θ • rightMulHS (ℋ := ℋ) B₂ =
        rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂) := by
    ext T
    change ((1 - θ) • (toOp T * B₁) + θ • (toOp T * B₂) : (ℋ →L[ℂ] ℋ)) =
      toOp T * ((1 - θ) • B₁ + θ • B₂)
    rw [mul_add, mul_smul_comm, mul_smul_comm]
  have hA_combo := pdSet_convexCombo (ℋ := ℋ) hA₁ hA₂ hθ0 hθ1
  have hB_combo := pdSet_convexCombo (ℋ := ℋ) hB₁ hB₂ hθ0 hθ1
  letI : Nontrivial (HSOp ℋ) := by
    delta HSOp
    infer_instance
  letI : Nontrivial (HSOp ℋ →L[ℂ] HSOp ℋ) := inferInstance
  have hphi_mono := phiK_mono (ℋ := ℋ) K (by
    simpa [hleft_combo, hright_combo] using
      operatorPowerMean_jointlyConcaveOn_pdSet
        (ℋ := HSOp ℋ) (α := s) (β := 1)
        ⟨le_of_lt hs0, hs1.le⟩ ⟨by norm_num, by norm_num⟩
        (A₁ := leftMulHS (ℋ := ℋ) A₁) (A₂ := leftMulHS (ℋ := ℋ) A₂)
        (B₁ := rightMulHS (ℋ := ℋ) B₁) (B₂ := rightMulHS (ℋ := ℋ) B₂) (θ := θ)
        (leftMulHS_pdSet (ℋ := ℋ) hA₁) (leftMulHS_pdSet (ℋ := ℋ) hA₂)
        (rightMulHS_pdSet (ℋ := ℋ) hB₁) (rightMulHS_pdSet (ℋ := ℋ) hB₂)
        hθ0 hθ1)
  rw [phiK_weightedSum_operatorPowerMean_eq (ℋ := ℋ) (s := s) (θ := θ) K A₁ A₂ B₁ B₂
      hA₁ hA₂ hB₁ hB₂] at hphi_mono
  rw [phiK_operatorPowerMean_eq_liebTraceMap (ℋ := ℋ) (s := s) K
      ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂) hA_combo hB_combo] at hphi_mono
  simpa [add_comm, add_left_comm, add_assoc] using hphi_mono

end LiebAndoTrace
