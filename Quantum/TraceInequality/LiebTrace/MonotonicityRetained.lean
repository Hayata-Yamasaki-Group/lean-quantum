/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LiebAndo.LiebTrace.Bridge
import Quantum.TraceInequality.LiebTrace.Bridge
import Quantum.TraceInequality.LiebTrace.Monotonicity
import Quantum.TraceInequality.LownerHeinz.NegPow
import Quantum.TraceInequality.TraceFunctionMonotonicity.LownerHeinz.RpowZeroOne

namespace LiebAndoTrace

universe u

open LownerHeinzTheorem
open GeneralizedPerspectiveFunction
open HilbertSchmidtOperatorSpace
open Module.End Polynomial

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [FiniteDimensional ℂ ℋ] [Nontrivial ℋ]

-- Under transparency-respecting defeq, synthesizing `NonnegSpectrumClass ℝ (ℋ →L[ℂ] ℋ)`
-- from scratch exceeds the default typeclass budget and is re-run at every
-- `nonneg_iff_spectrum_nonneg`-style step (it is not cached across tactic steps).
-- Register the C⋆-algebra instance once so each search is a direct hit.
attribute [local instance] instNonnegSpectrumClassRealContinuousLinearMapComplexId_quantum_1

omit [Nontrivial ℋ] in
private lemma phiK_leftMul_rightMul_eq_traceRe (K C D : (ℋ →L[ℂ] ℋ)) :
    phiK (ℋ := ℋ) K
        (leftMulHS (ℋ := ℋ) C * rightMulHS (ℋ := ℋ) D) =
      traceRe (ℋ := ℋ) (C * star K * D * K) := by
  calc
    phiK (ℋ := ℋ) K
        (leftMulHS (ℋ := ℋ) C * rightMulHS (ℋ := ℋ) D)
      = Complex.re
          (inner ℂ (ofOp (star K))
            ((leftMulHS (ℋ := ℋ) C * rightMulHS (ℋ := ℋ) D) (ofOp (star K)))) := by
            simp [phiK]
    _ = Complex.re
          (inner ℂ (ofOp (star K))
            (ofOp (C * star K * D))) := by
            simp [leftMulHS_apply, rightMulHS_apply, mul_assoc]
    _ = traceRe (ℋ := ℋ) (C * star K * D * K) := by
          rw [traceRe]
          set X : (ℋ →L[ℂ] ℋ) := C * star K * D
          have htrace :=
            re_hsInner_eq_traceRe (ℋ := ℋ) (X := star K) (Y := X)
          have htrace' :
              Complex.re (inner ℂ (ofOp (star K)) (ofOp X)) =
                Complex.re (LinearMap.trace ℂ ℋ ((K * X).toLinearMap)) := by
            simpa [X, mul_assoc] using htrace
          have hcycle :
              Complex.re (LinearMap.trace ℂ ℋ ((K * X).toLinearMap)) =
                Complex.re (LinearMap.trace ℂ ℋ ((X * K).toLinearMap)) := by
            simpa using
              congrArg Complex.re
                (LinearMap.trace_mul_comm (R := ℂ) (M := ℋ) K.toLinearMap X.toLinearMap)
          simpa [X, mul_assoc] using htrace'.trans hcycle

/-! ### Right-variable monotonicity and weighted sums -/
omit [Nontrivial ℋ] in
lemma liebTraceMap_mono_right
    {s : ℝ} (hs : 1 - s ∈ Set.Icc (0 : ℝ) 1)
    (K A B₁ B₂ : (ℋ →L[ℂ] ℋ))
    (hA : A ∈ pdSet (ℋ := ℋ)) (hB₁ : B₁ ∈ pdSet (ℋ := ℋ)) (hB₂ : B₂ ∈ pdSet (ℋ := ℋ))
    (hB : B₁ ≤ B₂) :
    liebTraceMap (ℋ := ℋ) s K A B₁ ≤ liebTraceMap (ℋ := ℋ) s K A B₂ := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  rcases hB₁ with ⟨hB₁_sa, hB₁_spec⟩
  rcases hB₂ with ⟨hB₂_sa, hB₂_spec⟩
  have hB₁0 : 0 ≤ B₁ :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₁ (ha := hB₁_sa)).2
      fun x hx => (hB₁_spec hx).le
  have hB₂0 : 0 ≤ B₂ :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₂ (ha := hB₂_sa)).2
      fun x hx => (hB₂_spec hx).le
  have hcfc :=
    LownerHeinzCore.power_Icc_zero_one_operatorMonotoneOn_Ici
      (𝓐 := (ℋ →L[ℂ] ℋ)) (1 - s) hs
      (A := B₂) (B := B₁) hB₂_sa hB₁_sa hB
      (fun x hx => by simpa [Set.Ici] using (hB₂_spec hx).le)
      (fun x hx => by simpa [Set.Ici] using (hB₁_spec hx).le)
  have hpow :
      B₁ ^ (1 - s) ≤ B₂ ^ (1 - s) := by
    simpa [cfcR, LownerHeinzCore.cfcR,
      CFC.rpow_eq_cfc_real (A := (ℋ →L[ℂ] ℋ)) (a := B₁) (y := 1 - s) (ha := hB₁0),
      CFC.rpow_eq_cfc_real (A := (ℋ →L[ℂ] ℋ)) (a := B₂) (y := 1 - s) (ha := hB₂0)] using hcfc
  have hprod0 :
      0 ≤ leftMulHS (ℋ := ℋ) (A ^ s) *
          rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s) - B₁ ^ (1 - s)) := by
    exact (leftMulHS_rightMulHS_commute (ℋ := ℋ) (A ^ s)
        (B₂ ^ (1 - s) - B₁ ^ (1 - s))).mul_nonneg
      (leftMulHS_nonneg (ℋ := ℋ) (by simp))
      (rightMulHS_nonneg (ℋ := ℋ) (sub_nonneg.mpr hpow))
  have hphi := phiK_nonneg (ℋ := ℋ) K hprod0
  have hsplit :
      leftMulHS (ℋ := ℋ) (A ^ s) *
          rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s) - B₁ ^ (1 - s)) =
        leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s)) -
          leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s)) := by
    ext T
    change (A ^ s * (toOp T * (B₂ ^ (1 - s) - B₁ ^ (1 - s))) : (ℋ →L[ℂ] ℋ)) =
      A ^ s * (toOp T * B₂ ^ (1 - s)) - A ^ s * (toOp T * B₁ ^ (1 - s))
    simp [mul_sub]
  have hrewrite :
      phiK (ℋ := ℋ) K
          (leftMulHS (ℋ := ℋ) (A ^ s) *
            rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s) - B₁ ^ (1 - s))) =
        liebTraceMap (ℋ := ℋ) s K A B₂ - liebTraceMap (ℋ := ℋ) s K A B₁ := by
    rw [hsplit, sub_eq_add_neg, phiK_add]
    rw [show -(leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s))) =
        (-1 : ℝ) • (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s))) by simp,
      phiK_smul]
    simp [phiK_leftMul_rightMul_eq_traceRe, liebTraceMap, mul_assoc, sub_eq_add_neg]
  linarith [hrewrite ▸ hphi]

attribute [gcongr] liebTraceMap_mono_right

omit [Nontrivial ℋ] in
lemma liebTraceMap_antitone_right
    {s : ℝ} (hs : 1 - s ∈ Set.Icc (-1 : ℝ) 0)
    (K A B₁ B₂ : (ℋ →L[ℂ] ℋ))
    (hA : A ∈ pdSet (ℋ := ℋ)) (hB₁ : B₁ ∈ pdSet (ℋ := ℋ)) (hB₂ : B₂ ∈ pdSet (ℋ := ℋ))
    (hB : B₁ ≤ B₂) :
    liebTraceMap (ℋ := ℋ) s K A B₂ ≤ liebTraceMap (ℋ := ℋ) s K A B₁ := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  rcases hB₁ with ⟨hB₁_sa, hB₁_spec⟩
  rcases hB₂ with ⟨hB₂_sa, hB₂_spec⟩
  have hB₁0 : 0 ≤ B₁ :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₁ (ha := hB₁_sa)).2
      fun x hx => (hB₁_spec hx).le
  have hB₂0 : 0 ≤ B₂ :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₂ (ha := hB₂_sa)).2
      fun x hx => (hB₂_spec hx).le
  have hcfc :=
    LownerHeinzCore.power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi
      (𝓐 := (ℋ →L[ℂ] ℋ)) (1 - s) hs
      (A := B₂) (B := B₁) hB₂_sa hB₁_sa hB
      (fun x hx => hB₂_spec hx) (fun x hx => hB₁_spec hx)
  have hpow :
      B₂ ^ (1 - s) ≤ B₁ ^ (1 - s) := by
    have hnegpow : -(B₁ ^ (1 - s)) ≤ -(B₂ ^ (1 - s)) := by
      simpa [cfcR, LownerHeinzCore.cfcR, cfc_neg,
        CFC.rpow_eq_cfc_real (A := (ℋ →L[ℂ] ℋ)) (a := B₁) (y := 1 - s)
          (ha := hB₁0),
        CFC.rpow_eq_cfc_real (A := (ℋ →L[ℂ] ℋ)) (a := B₂) (y := 1 - s)
          (ha := hB₂0)] using hcfc
    simpa using (neg_le_neg_iff.mp hnegpow)
  have hprod0 :
      0 ≤ leftMulHS (ℋ := ℋ) (A ^ s) *
          rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s) - B₂ ^ (1 - s)) := by
    exact (leftMulHS_rightMulHS_commute (ℋ := ℋ) (A ^ s)
        (B₁ ^ (1 - s) - B₂ ^ (1 - s))).mul_nonneg
      (leftMulHS_nonneg (ℋ := ℋ) (by simp))
      (rightMulHS_nonneg (ℋ := ℋ) (sub_nonneg.mpr hpow))
  have hphi := phiK_nonneg (ℋ := ℋ) K hprod0
  have hsplit :
      leftMulHS (ℋ := ℋ) (A ^ s) *
          rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s) - B₂ ^ (1 - s)) =
        leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s)) -
          leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s)) := by
    ext T
    change (A ^ s * (toOp T * (B₁ ^ (1 - s) - B₂ ^ (1 - s))) : (ℋ →L[ℂ] ℋ)) =
      A ^ s * (toOp T * B₁ ^ (1 - s)) - A ^ s * (toOp T * B₂ ^ (1 - s))
    simp [mul_sub]
  have hrewrite :
      phiK (ℋ := ℋ) K
          (leftMulHS (ℋ := ℋ) (A ^ s) *
            rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s) - B₂ ^ (1 - s))) =
        liebTraceMap (ℋ := ℋ) s K A B₁ - liebTraceMap (ℋ := ℋ) s K A B₂ := by
    rw [hsplit, sub_eq_add_neg, phiK_add]
    rw [show -(leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s))) =
        (-1 : ℝ) • (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s))) by simp,
      phiK_smul]
    simp [phiK_leftMul_rightMul_eq_traceRe, liebTraceMap, mul_assoc, sub_eq_add_neg]
  linarith [hrewrite ▸ hphi]

attribute [gcongr] liebTraceMap_antitone_right

end LiebAndoTrace
