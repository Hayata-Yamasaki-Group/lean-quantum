/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LiebAndo.LinearMapsDirect

/-! # Lieb and Ando inequalities on the positive-definite cone of linear endomorphisms -/

open QuantumState LownerHeinzTheorem GeneralizedPerspectiveFunction
open HilbertSchmidtOperatorSpace OperatorGeometricMean SandwichedRenyiRelativeEntropy

namespace LiebAndoTrace

universe u

variable {ℋ : Type u} [Qudit ℋ]

private lemma toCLM_combo (A B : L ℋ) (θ : ℝ) :
    ((1 - θ) • A + θ • B).toContinuousLinearMap =
      (1 - θ) • A.toContinuousLinearMap + θ • B.toContinuousLinearMap := by
  ext x
  rfl

variable [Nontrivial ℋ]

/-- Joint concavity on the positive-definite cone for `0 < s < 1` of the real part
of the trace `Tr (A ^ s * star K * B ^ (1 - s) * K)`, for fixed `K : L ℋ`. -/
theorem jointlyConcaveOn_liebTraceMap_pdSetLM
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (K : L ℋ) :
    JointlyConcaveOn pdSetLM pdSetLM (liebTraceMap s K) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hleft_combo :
      (1 - θ) • leftMulHS A₁.toContinuousLinearMap +
        θ • leftMulHS A₂.toContinuousLinearMap =
      leftMulHS (((1 - θ) • A₁ + θ • A₂).toContinuousLinearMap) := by
    rw [toCLM_combo]
    ext T
    change (1 - θ) • (A₁.toContinuousLinearMap * toOp T) +
        θ • (A₂.toContinuousLinearMap * toOp T) =
      ((1 - θ) • A₁.toContinuousLinearMap + θ • A₂.toContinuousLinearMap) * toOp T
    rw [add_mul, smul_mul_assoc, smul_mul_assoc]
  have hright_combo :
      (1 - θ) • rightMulHS B₁.toContinuousLinearMap +
        θ • rightMulHS B₂.toContinuousLinearMap =
      rightMulHS (((1 - θ) • B₁ + θ • B₂).toContinuousLinearMap) := by
    rw [toCLM_combo]
    ext T
    change (1 - θ) • (toOp T * B₁.toContinuousLinearMap) +
        θ • (toOp T * B₂.toContinuousLinearMap) =
      toOp T * ((1 - θ) • B₁.toContinuousLinearMap + θ • B₂.toContinuousLinearMap)
    rw [mul_add, mul_smul_comm, mul_smul_comm]
  have hA_combo : ((1 - θ) • A₁ + θ • A₂) ∈
      SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ) := by
    change (((1 - θ) • A₁ + θ • A₂).toContinuousLinearMap) ∈ pdSet (ℋ := ℋ)
    rw [toCLM_combo]
    exact pdSet_convexCombo_transport hA₁ hA₂ hθ0 hθ1
  have hB_combo : ((1 - θ) • B₁ + θ • B₂) ∈
      SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ) := by
    change (((1 - θ) • B₁ + θ • B₂).toContinuousLinearMap) ∈ pdSet (ℋ := ℋ)
    rw [toCLM_combo]
    exact pdSet_convexCombo_transport hB₁ hB₂ hθ0 hθ1
  letI : Nontrivial (HSOp ℋ) := by
    delta HSOp
    infer_instance
  letI : Nontrivial (HSOp ℋ →L[ℂ] HSOp ℋ) := inferInstance
  have hphi_mono := phiK_mono K.toContinuousLinearMap (by
    simpa only [hleft_combo, hright_combo] using
      jointlyConcaveOn_operatorPowerMean_pdSet
        (ℋ := HSOp ℋ) (α := s) (β := 1)
        ⟨le_of_lt hs0, hs1.le⟩ ⟨by norm_num, by norm_num⟩
        (A₁ := leftMulHS A₁.toContinuousLinearMap)
        (A₂ := leftMulHS A₂.toContinuousLinearMap)
        (B₁ := rightMulHS B₁.toContinuousLinearMap)
        (B₂ := rightMulHS B₂.toContinuousLinearMap) (θ := θ)
        (leftMulHS_pdSet hA₁) (leftMulHS_pdSet hA₂)
        (rightMulHS_pdSet hB₁) (rightMulHS_pdSet hB₂) hθ0 hθ1)
  simpa only [phiK_add, phiK_smul,
    phiK_operatorPowerMean_eq_liebTraceMap_lm K A₁ B₁ hA₁ hB₁,
    phiK_operatorPowerMean_eq_liebTraceMap_lm K A₂ B₂ hA₂ hB₂,
    phiK_operatorPowerMean_eq_liebTraceMap_lm K
      ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂) hA_combo hB_combo,
    smul_eq_mul] using hphi_mono

/-- Joint convexity on the positive-definite cone for `1 ≤ s ≤ 2` of the real part
of the trace `Tr (A ^ s * star K * B ^ (1 - s) * K)`, for fixed `K : L ℋ`. -/
theorem jointlyConvexOn_liebTraceMap_pdSetLM
    {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (K : L ℋ) :
    JointlyConvexOn pdSetLM pdSetLM (liebTraceMap s K) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hleft_combo :
      (1 - θ) • leftMulHS A₁.toContinuousLinearMap +
        θ • leftMulHS A₂.toContinuousLinearMap =
      leftMulHS (((1 - θ) • A₁ + θ • A₂).toContinuousLinearMap) := by
    rw [toCLM_combo]
    ext T
    change (1 - θ) • (A₁.toContinuousLinearMap * toOp T) +
        θ • (A₂.toContinuousLinearMap * toOp T) =
      ((1 - θ) • A₁.toContinuousLinearMap + θ • A₂.toContinuousLinearMap) * toOp T
    rw [add_mul, smul_mul_assoc, smul_mul_assoc]
  have hright_combo :
      (1 - θ) • rightMulHS B₁.toContinuousLinearMap +
        θ • rightMulHS B₂.toContinuousLinearMap =
      rightMulHS (((1 - θ) • B₁ + θ • B₂).toContinuousLinearMap) := by
    rw [toCLM_combo]
    ext T
    change (1 - θ) • (toOp T * B₁.toContinuousLinearMap) +
        θ • (toOp T * B₂.toContinuousLinearMap) =
      toOp T * ((1 - θ) • B₁.toContinuousLinearMap + θ • B₂.toContinuousLinearMap)
    rw [mul_add, mul_smul_comm, mul_smul_comm]
  have hA_combo : ((1 - θ) • A₁ + θ • A₂) ∈
      SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ) := by
    change (((1 - θ) • A₁ + θ • A₂).toContinuousLinearMap) ∈ pdSet (ℋ := ℋ)
    rw [toCLM_combo]
    exact pdSet_convexCombo_transport hA₁ hA₂ hθ0 hθ1
  have hB_combo : ((1 - θ) • B₁ + θ • B₂) ∈
      SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ) := by
    change (((1 - θ) • B₁ + θ • B₂).toContinuousLinearMap) ∈ pdSet (ℋ := ℋ)
    rw [toCLM_combo]
    exact pdSet_convexCombo_transport hB₁ hB₂ hθ0 hθ1
  letI : Nontrivial (HSOp ℋ) := by
    delta HSOp
    infer_instance
  letI : Nontrivial (HSOp ℋ →L[ℂ] HSOp ℋ) := inferInstance
  have hphi_mono := phiK_mono K.toContinuousLinearMap (by
    simpa only [hleft_combo, hright_combo] using
      jointlyConvexOn_operatorPowerMean_pdSet
        (ℋ := HSOp ℋ) (α := s) (β := 1)
        ⟨hs1, hs2⟩ ⟨by norm_num, by norm_num⟩
        (A₁ := leftMulHS A₁.toContinuousLinearMap)
        (A₂ := leftMulHS A₂.toContinuousLinearMap)
        (B₁ := rightMulHS B₁.toContinuousLinearMap)
        (B₂ := rightMulHS B₂.toContinuousLinearMap) (θ := θ)
        (leftMulHS_pdSet hA₁) (leftMulHS_pdSet hA₂)
        (rightMulHS_pdSet hB₁) (rightMulHS_pdSet hB₂) hθ0 hθ1)
  simpa only [phiK_add, phiK_smul,
    phiK_operatorPowerMean_eq_liebTraceMap_lm K A₁ B₁ hA₁ hB₁,
    phiK_operatorPowerMean_eq_liebTraceMap_lm K A₂ B₂ hA₂ hB₂,
    phiK_operatorPowerMean_eq_liebTraceMap_lm K
      ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂) hA_combo hB_combo,
    smul_eq_mul] using hphi_mono

/-- Joint convexity on the positive-definite cone for `1 ≤ q ≤ 2`, `0 ≤ r ≤ 1`,
and `1 ≤ q - r` of the real part of `Tr (A ^ q * star K * B ^ (-r) * K)`,
for fixed `K : L ℋ`. -/
theorem jointlyConvexOn_andoTraceMap_pdSetLM
    {q r : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hqr : 1 ≤ q - r) (K : L ℋ) :
    JointlyConvexOn pdSetLM pdSetLM (andoTraceMap q r K) := by
  by_cases hqeq : q = 1
  · have hrzero : r = 0 := by linarith
    subst q
    subst r
    convert (jointlyConvexOn_liebTraceMap_pdSetLM
      (s := 1) (by norm_num) (by norm_num) K) using 1
    ext A B
    simp only [andoTraceMap, liebTraceMap, sub_self, neg_zero]
  · have hqpos : 0 < q - 1 := by
      have hqgt : 1 < q := lt_of_le_of_ne hq1 (Ne.symm hqeq)
      linarith
    let β : ℝ := r / (q - 1)
    have hβ : β ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg hr0 hqpos.le
      · exact (div_le_one hqpos).2 (by linarith [hr1])
    have hβmul : β * (1 - q) = -r := by
      dsimp [β]
      field_simp [hqpos.ne']
      ring
    intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
    have hleft_combo :
        (1 - θ) • leftMulHS A₁.toContinuousLinearMap +
          θ • leftMulHS A₂.toContinuousLinearMap =
        leftMulHS (((1 - θ) • A₁ + θ • A₂).toContinuousLinearMap) := by
      rw [toCLM_combo]
      ext T
      change (1 - θ) • (A₁.toContinuousLinearMap * toOp T) +
          θ • (A₂.toContinuousLinearMap * toOp T) =
        ((1 - θ) • A₁.toContinuousLinearMap + θ • A₂.toContinuousLinearMap) * toOp T
      rw [add_mul, smul_mul_assoc, smul_mul_assoc]
    have hright_combo :
        (1 - θ) • rightMulHS B₁.toContinuousLinearMap +
          θ • rightMulHS B₂.toContinuousLinearMap =
        rightMulHS (((1 - θ) • B₁ + θ • B₂).toContinuousLinearMap) := by
      rw [toCLM_combo]
      ext T
      change (1 - θ) • (toOp T * B₁.toContinuousLinearMap) +
          θ • (toOp T * B₂.toContinuousLinearMap) =
        toOp T * ((1 - θ) • B₁.toContinuousLinearMap + θ • B₂.toContinuousLinearMap)
      rw [mul_add, mul_smul_comm, mul_smul_comm]
    have hA_combo : ((1 - θ) • A₁ + θ • A₂) ∈
        SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ) := by
      change (((1 - θ) • A₁ + θ • A₂).toContinuousLinearMap) ∈ pdSet (ℋ := ℋ)
      rw [toCLM_combo]
      exact pdSet_convexCombo_transport hA₁ hA₂ hθ0 hθ1
    have hB_combo : ((1 - θ) • B₁ + θ • B₂) ∈
        SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ) := by
      change (((1 - θ) • B₁ + θ • B₂).toContinuousLinearMap) ∈ pdSet (ℋ := ℋ)
      rw [toCLM_combo]
      exact pdSet_convexCombo_transport hB₁ hB₂ hθ0 hθ1
    letI : Nontrivial (HSOp ℋ) := by
      delta HSOp
      infer_instance
    letI : Nontrivial (HSOp ℋ →L[ℂ] HSOp ℋ) := inferInstance
    have hphi_mono := phiK_mono K.toContinuousLinearMap (by
      simpa only [hleft_combo, hright_combo] using
        jointlyConvexOn_operatorPowerMean_pdSet
          (ℋ := HSOp ℋ) (α := q) (β := β)
          ⟨hq1, hq2⟩ hβ
          (A₁ := leftMulHS A₁.toContinuousLinearMap)
          (A₂ := leftMulHS A₂.toContinuousLinearMap)
          (B₁ := rightMulHS B₁.toContinuousLinearMap)
          (B₂ := rightMulHS B₂.toContinuousLinearMap) (θ := θ)
          (leftMulHS_pdSet hA₁) (leftMulHS_pdSet hA₂)
          (rightMulHS_pdSet hB₁) (rightMulHS_pdSet hB₂) hθ0 hθ1)
    simpa only [phiK_add, phiK_smul,
      phiK_operatorPowerMean_eq_liebTraceMap_rpow_lm hβ K A₁ B₁ hA₁ hB₁,
      phiK_operatorPowerMean_eq_liebTraceMap_rpow_lm hβ K A₂ B₂ hA₂ hB₂,
      phiK_operatorPowerMean_eq_liebTraceMap_rpow_lm hβ K
        ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂) hA_combo hB_combo,
      liebTraceMap_rpow_eq_andoTraceMap_lm hβmul K A₁ B₁ hB₁,
      liebTraceMap_rpow_eq_andoTraceMap_lm hβmul K A₂ B₂ hB₂,
      liebTraceMap_rpow_eq_andoTraceMap_lm hβmul K
        ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂) hB_combo,
      smul_eq_mul] using hphi_mono

end LiebAndoTrace

