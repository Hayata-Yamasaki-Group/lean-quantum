/-
Lower bound of the smoothed max-relative entropy by the hypothesis-testing relative entropy: dh(ε₂) + log₂(1−ε₁−ε₂) ≤ smoothMax(ε₁) for ε₁, ε₂ ∈ (0,1) with ε₁+ε₂ < 1 (gsl_c16).
Source context: Gour, Theorem 11.4.
-/
import Quantum.QuantumEntropy.GourResource.KWTestingBridge
import Quantum.QuantumEntropy.GourResource.SmoothMax

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem c16_acceptance_loss {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ τ : State.{u} A) (M : L.{u} A) (hM : effect M) :
    pairing ρ.1 M - pairing τ.1 M ≤ td ρ.1 τ.1 := by
  have hzero : (0 : L A) ≤ M := (LinearMap.nonneg_iff_isPositive M).mpr hM.1
  have hone : M ≤ 1 := sub_nonneg.mp
    ((LinearMap.nonneg_iff_isPositive (1 - M)).mpr hM.2)
  have hlow : -(1 : L A) ≤ M + M - 1 := by
    simpa only [zero_sub] using sub_le_sub_right (add_nonneg hzero hzero) (1 : L A)
  have hupp : M + M - 1 ≤ (1 : L A) := by
    simpa only [add_sub_cancel_right] using
      sub_le_sub_right (add_le_add hone hone) (1 : L A)
  have hsa : IsSelfAdjoint (M + M - 1) :=
    (hM.1.isSelfAdjoint.add hM.1.isSelfAdjoint).sub (IsSelfAdjoint.one _)
  have hbound := (w40_trace_norm_spectral_variational (ρ.1 - τ.1)
    (ρ.2.1.isSelfAdjoint.sub τ.2.1.isSelfAdjoint)).2.1 (M + M - 1) hsa hlow hupp
  have htrace : (Tr ((M + M - 1) * (ρ.1 - τ.1))).re =
      2 * (pairing ρ.1 M - pairing τ.1 M) := by
    simp only [sub_mul, add_mul, mul_sub, one_mul, map_sub, map_add, Complex.sub_re,
      Complex.add_re, ρ.2.2, τ.2.2, LinearMap.trace_mul_comm ℂ M ρ.1,
      LinearMap.trace_mul_comm ℂ M τ.1, pairing]
    ring
  rw [htrace] at hbound
  change pairing ρ.1 M - pairing τ.1 M ≤ w40T₁ (ρ.1 - τ.1) / 2
  linarith

private theorem c16_pairing_nonneg {A : Type u} [Qudit.{u} A]
    (X M : L.{u} A) (hX : 0 ≤ X) (hM : 0 ≤ M) : 0 ≤ pairing X M := by
  have hs : IsSelfAdjoint (CFC.sqrt M) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg M)
  have hp : 0 ≤ CFC.sqrt M * X * CFC.sqrt M := by
    simpa only [hs.star_eq] using star_left_conjugate_nonneg hX (CFC.sqrt M)
  have ht := (Complex.nonneg_iff.mp
    ((LinearMap.nonneg_iff_isPositive _).mp hp).trace_nonneg).1
  have he : Tr (CFC.sqrt M * X * CFC.sqrt M) = Tr (X * M) := by
    rw [mul_assoc, LinearMap.trace_mul_comm ℂ (CFC.sqrt M), mul_assoc,
      CFC.sqrt_mul_sqrt_self M hM]
  rwa [he] at ht

private theorem c16_pairing_mono {A : Type u} [Qudit.{u} A]
    (X Y M : L.{u} A) (hXY : X ≤ Y) (hM : M.IsPositive) :
    pairing X M ≤ pairing Y M := by
  have h := c16_pairing_nonneg (Y - X) M (sub_nonneg.mpr hXY)
    ((LinearMap.nonneg_iff_isPositive M).mpr hM)
  simp only [pairing, sub_mul, map_sub, Complex.sub_re] at h ⊢
  linarith

private theorem c16_log_bound (a b lam : ℝ) (ha : 0 < a)
    (hbound : a ≤ (2 : ℝ) ^ lam * b) :
    OPT.binaryNegLog2 (Real.toNNReal b) + ((Real.logb 2 a : ℝ) : EReal) ≤
      (lam : EReal) := by
  have hpow : 0 < (2 : ℝ) ^ lam := Real.rpow_pos_of_pos (by norm_num) _
  have hb : 0 < b := (mul_pos_iff_of_pos_left hpow).mp (ha.trans_le hbound)
  have hfinite : OPT.binaryNegLog2 (Real.toNNReal b) =
      ((-Real.logb 2 b : ℝ) : EReal) := by
    rw [OPT.binaryNegLog2, if_neg (ne_of_gt (Real.toNNReal_pos.mpr hb)),
      Real.coe_toNNReal b hb.le]
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) ha hbound
  rw [Real.logb_mul hpow.ne' hb.ne', Real.logb_rpow (by norm_num) (by norm_num)] at hlog
  rw [hfinite, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith

private theorem c16_testing_le_dm {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ σ τ : State.{u} A) (ε₁ ε₂ : ℝ) (hsum : ε₁ + ε₂ < 1)
    (hclose : td ρ.1 τ.1 ≤ ε₁) (M : L.{u} A) (hM : effect M)
    (haccept : 1 - ε₂ ≤ pairing ρ.1 M)
    (hopt : pairing σ.1 M = beta ρ.1 σ.1 ε₂) :
    dh ρ.1 σ.1 ε₂ + ((Real.logb 2 (1 - ε₁ - ε₂) : ℝ) : EReal) ≤ dm τ.1 σ.1 := by
  have hloss := c16_acceptance_loss ρ τ M hM
  have hacc : 1 - ε₁ - ε₂ ≤ pairing τ.1 M := by linarith
  change _ ≤ sInf (OPT.OrderedCone.dominationSet τ.1 σ.1)
  apply le_sInf
  rintro z ⟨lam, rfl, hdom⟩
  have hpair := c16_pairing_mono τ.1 (((2 : ℝ) ^ lam) • σ.1) M hdom hM.1
  have hscale : pairing (((2 : ℝ) ^ lam) • σ.1) M =
      (2 : ℝ) ^ lam * beta ρ.1 σ.1 ε₂ := by
    rw [← hopt]
    simp [pairing, ← Complex.coe_smul]
  rw [hscale] at hpair
  exact c16_log_bound (1 - ε₁ - ε₂) (beta ρ.1 σ.1 ε₂) lam (by linarith)
    (hacc.trans hpair)

theorem gsl_c16 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (ε₁ ε₂ : ℝ), ε₁ ∈ Set.Ioo 0 1 → ε₂
  ∈ Set.Ioo 0 1 → ε₁+ε₂<1 →
  dh.{u} ρ.1 σ.1 ε₂ + ((Real.logb 2 (1-ε₁-ε₂) : ℝ) : EReal) ≤ smoothMax.{u} ρ.1 σ.1 ε₁)
:= by
  intro A _ _ ρ σ ε₁ ε₂ hε₁ hε₂ hsum
  obtain ⟨τ, hclose, hattain⟩ := GourResource.gsl_c15.{u} ρ σ ε₁ hε₁
  obtain ⟨M, hM, haccept, hopt⟩ :=
    GourResource.gsl_b02.{u}.2.2.2.1 ρ σ ε₂ ⟨hε₂.1.le, hε₂.2⟩
  rw [← hattain]
  exact c16_testing_le_dm ρ σ τ ε₁ ε₂ hsum hclose M hM haccept hopt

end GourResource

