/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LiebAndo.AndoConvexity.Concavity
import Quantum.TraceInequality.LiebAndo.Concavity
import Quantum.TraceInequality.LiebAndo.AndoConvexity.LiebTrace.Bridge
import Quantum.TraceInequality.LiebTrace.MonotonicityRetained
import Quantum.QuantumMechanics.QuantumStateGeneralizedStein
import Quantum.TraceInequality.GeneralizedPerspectiveFunctionRetained
import Quantum.TraceInequality.HansenPedersen.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinz.ReciprocalRetained

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

/-! ### rpow writeback and Lieb extension -/
omit [FiniteDimensional ℂ ℋ] [Nontrivial ℋ] in
/-- An operator in the positive-definite cone `pdSet` is nonnegative: it is
self-adjoint with real spectrum contained in `(0, ∞)`. -/
private lemma nonneg_of_mem_pdSet {A : (ℋ →L[ℂ] ℋ)} (hA : A ∈ pdSet (ℋ := ℋ)) : 0 ≤ A :=
  (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA.1)).2
    fun _ hx => (hA.2 hx).le

omit [FiniteDimensional ℂ ℋ] in
/-- Operator concavity of the real power `x ↦ x ^ β` for `β ∈ [0, 1]`, transported to
the globalized real power on the positive-definite cone: the convex combination of the
powers is dominated by the power of the convex combination. -/
private lemma convexCombo_rpow_le_rpow_convexCombo
    {β θ : ℝ} (hβ : β ∈ Set.Icc (0 : ℝ) 1) {B₁ B₂ : (ℋ →L[ℂ] ℋ)}
    (hB₁ : B₁ ∈ pdSet (ℋ := ℋ)) (hB₂ : B₂ ∈ pdSet (ℋ := ℋ))
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) • (B₁ ^ β) + θ • (B₂ ^ β) ≤ ((1 - θ) • B₁ + θ • B₂) ^ β := by
  have hB_combo : ((1 - θ) • B₁ + θ • B₂) ∈ pdSet (ℋ := ℋ) :=
    pdSet_convexCombo (ℋ := ℋ) hB₁ hB₂ hθ0 hθ1
  have hB₁0 : 0 ≤ B₁ := nonneg_of_mem_pdSet (ℋ := ℋ) hB₁
  have hB₂0 : 0 ≤ B₂ := nonneg_of_mem_pdSet (ℋ := ℋ) hB₂
  have hBcombo0 : 0 ≤ ((1 - θ) • B₁ + θ • B₂) := nonneg_of_mem_pdSet (ℋ := ℋ) hB_combo
  have hpow_conc :=
    LownerHeinzCore.power_Icc_zero_one_operatorConcaveOn_Ici
      (𝓐 := (ℋ →L[ℂ] ℋ)) β hβ
      (A := B₁) (B := B₂) (t := θ) hB₁.1 hB₂.1 hθ0 hθ1
      (by intro x hx; exact (Set.mem_Ioi.mp (hB₁.2 hx)).le)
      (by intro x hx; exact (Set.mem_Ioi.mp (hB₂.2 hx)).le)
  have hpow_conc' :
      cfc (fun x : ℝ ↦ -x ^ β) ((1 - θ) • B₁ + θ • B₂) ≤
        (1 - θ) • cfc (fun x : ℝ ↦ -x ^ β) B₁ + θ • cfc (fun x : ℝ ↦ -x ^ β) B₂ :=
    hpow_conc
  have hcfc : ∀ {a : (ℋ →L[ℂ] ℋ)}, 0 ≤ a → cfc (fun x : ℝ ↦ -x ^ β) a = -(a ^ β) := by
    intro a ha
    rw [cfc_neg (fun x : ℝ ↦ x ^ β) a, ← CFC.rpow_eq_cfc_real (ha := ha)]
  rw [hcfc hBcombo0, hcfc hB₁0, hcfc hB₂0, smul_neg, smul_neg, ← neg_add] at hpow_conc'
  exact neg_le_neg_iff.mp hpow_conc'

omit [FiniteDimensional ℂ ℋ] [Nontrivial ℋ] in
/-- Rewriting rule sending the Lieb trace functional evaluated at a real power back to
the extension trace functional: for `B` in the positive-definite cone and exponents with
`β ≥ 0`, `1 - q ≥ 0` and `β * (1 - q) = p`, the real-power composition formula
`(B ^ β) ^ (1 - q) = B ^ p` yields `F_{q,K}(A, B ^ β) = G_{q,p,K}(A, B)`. -/
private lemma liebTraceMap_rpow_eq_liebExtensionTraceMap
    {p q β : ℝ} (hβ0 : 0 ≤ β) (h1q : 0 ≤ 1 - q) (hβmul : β * (1 - q) = p)
    (K A : (ℋ →L[ℂ] ℋ)) {B : (ℋ →L[ℂ] ℋ)} (hB : B ∈ pdSet (ℋ := ℋ)) :
    liebTraceMap (ℋ := ℋ) q K A (B ^ β) = liebExtensionTraceMap (ℋ := ℋ) q p K A B := by
  have hB0 : 0 ≤ B := nonneg_of_mem_pdSet (ℋ := ℋ) hB
  have hpow :
      (B ^ β) ^ (1 - q) = B ^ p := by
    calc
      (B ^ β) ^ (1 - q) = B ^ (β * (1 - q)) := by
          simpa using
            (CFC.rpow_rpow_of_exponent_nonneg (A := (ℋ →L[ℂ] ℋ)) (a := B) (x := β)
                (y := 1 - q)
              hβ0 h1q (ha₂ := hB0))
      _ = B ^ p := by rw [hβmul]
  simp [liebTraceMap, liebExtensionTraceMap, hpow, mul_assoc]

omit [FiniteDimensional ℂ ℋ] [Nontrivial ℋ] in
/-- Rewriting rule sending the Lieb trace functional evaluated at a real power back to
the Ando trace functional: for `B` in the positive-definite cone and exponents with
`β * (1 - q) = -r`, the real-power composition formula `(B ^ β) ^ (1 - q) = B ^ (-r)`
(with the degenerate case `β = 0` handled through `B ^ 0 = 1`) yields
`F_{q,K}(A, B ^ β) = H_{q,r,K}(A, B)`. -/
private lemma liebTraceMap_rpow_eq_andoTraceMap
    {q r β : ℝ} (hβmul : β * (1 - q) = -r)
    (K A : (ℋ →L[ℂ] ℋ)) {B : (ℋ →L[ℂ] ℋ)} (hB : B ∈ pdSet (ℋ := ℋ)) :
    liebTraceMap (ℋ := ℋ) q K A (B ^ β) = andoTraceMap (ℋ := ℋ) q r K A B := by
  have hB0 : 0 ≤ B := nonneg_of_mem_pdSet (ℋ := ℋ) hB
  have hBunit : IsUnit B := by
    refine spectrum.isUnit_of_zero_notMem (R := ℝ) ?_
    intro h0
    exact (lt_irrefl (0 : ℝ)) (by simpa [Set.Ioi] using hB.2 h0)
  have hpow :
      (B ^ β) ^ (1 - q) = B ^ (-r) := by
    by_cases hβzero : β = 0
    · have hrz : r = 0 := by
        rw [hβzero] at hβmul
        linarith
      have hBzero : B ^ (0 : ℝ) = (1 : (ℋ →L[ℂ] ℋ)) := by
        simpa using (CFC.rpow_zero (a := B))
      calc
        (B ^ β) ^ (1 - q) = (B ^ (0 : ℝ)) ^ (1 - q) := by simp [hβzero]
        _ = (1 : (ℋ →L[ℂ] ℋ)) ^ (1 - q) := by rw [hBzero]
        _ = (1 : (ℋ →L[ℂ] ℋ)) := by simp
        _ = B ^ (0 : ℝ) := by rw [hBzero]
        _ = B ^ (-r) := by simp [hrz]
    · calc
        (B ^ β) ^ (1 - q) = B ^ (β * (1 - q)) := by
            simpa [mul_comm] using
              (CFC.rpow_rpow (a := B) (x := β) (y := 1 - q) hBunit hβzero hB0)
        _ = B ^ (-r) := by rw [hβmul]
  simp [liebTraceMap, andoTraceMap, hpow, mul_assoc]

/--
Source: I. Nikoufar, A. Ebadian, M. Eshaghi Gordji, "The simplest proof of Lieb concavity
theorem", Advances in Mathematics 248 (2013), 531--533, Theorem 1.2(b). Correspondence via α=q,
β=p/(1−q). Version using the real part of the trace on the positive definite cone, assuming p,q>0.
-/
theorem liebExtensionTrace_jointlyConcaveOn_pdSet
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + q ≤ 1) (K : (ℋ →L[ℂ] ℋ)) :
    JointlyConcaveOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (liebExtensionTraceMap (ℋ := ℋ) q p K) := by
  have hq1 : q < 1 := by linarith
  let β : ℝ := p / (1 - q)
  have h1q : 0 < 1 - q := by linarith
  have hβ0 : 0 ≤ β := by
    dsimp [β]
    positivity
  have hβ1 : β ≤ 1 := by
    dsimp [β]
    field_simp [h1q.ne']
    linarith
  have hβ : β ∈ Set.Icc (0 : ℝ) 1 := ⟨hβ0, hβ1⟩
  have hβmul : β * (1 - q) = p := by
    dsimp [β]
    field_simp [h1q.ne']
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hA_combo := pdSet_convexCombo (ℋ := ℋ) hA₁ hA₂ hθ0 hθ1
  have hB_combo := pdSet_convexCombo (ℋ := ℋ) hB₁ hB₂ hθ0 hθ1
  have hB₁β :=
    pdSet_rpow_of_mem_Icc_zero_one (ℋ := ℋ) hβ hB₁
  have hB₂β :=
    pdSet_rpow_of_mem_Icc_zero_one (ℋ := ℋ) hβ hB₂
  have hB_comboβ :=
    pdSet_rpow_of_mem_Icc_zero_one (ℋ := ℋ) hβ hB_combo
  have hBpow_combo := pdSet_convexCombo (ℋ := ℋ) hB₁β hB₂β hθ0 hθ1
  have hBpow_le :=
    convexCombo_rpow_le_rpow_convexCombo (ℋ := ℋ) hβ hB₁ hB₂ hθ0 hθ1
  have hmono := liebTraceMap_mono_right (ℋ := ℋ) (s := q)
      (by constructor <;> linarith) K
      ((1 - θ) • A₁ + θ • A₂)
      ((1 - θ) • (B₁ ^ β) + θ • (B₂ ^ β))
      (((1 - θ) • B₁ + θ • B₂) ^ β)
      hA_combo hBpow_combo hB_comboβ hBpow_le
  have hconc :=
    liebTrace_jointlyConcaveOn_pdSet (ℋ := ℋ) (s := q) hq hq1 K
      (A₁ := A₁) (A₂ := A₂) (B₁ := B₁ ^ β) (B₂ := B₂ ^ β)
      (θ := θ) hA₁ hA₂ hB₁β hB₂β hθ0 hθ1
  have hpow_rewrite :
      ∀ {A B : (ℋ →L[ℂ] ℋ)}, B ∈ pdSet (ℋ := ℋ) →
        liebTraceMap (ℋ := ℋ) q K A (B ^ β) =
          liebExtensionTraceMap (ℋ := ℋ) q p K A B :=
    fun {A B} hB =>
      liebTraceMap_rpow_eq_liebExtensionTraceMap (ℋ := ℋ) hβ0 (by linarith) hβmul K A hB
  simpa [hpow_rewrite hB₁, hpow_rewrite hB₂, hpow_rewrite hB_combo] using
    (le_trans hconc hmono)

/-! ### Ando convexity and the Lieb corollary -/
/--
Source: I. Nikoufar, A. Ebadian, M. Eshaghi Gordji, "The simplest proof of Lieb concavity
theorem", Advances in Mathematics 248 (2013), 531--533, Theorem 1.4 (from Theorem 1.1).
Version using the real part of the trace on the positive definite cone. This declaration is about
the real part of the trace; its identification with the complex trace needs a separate argument,
which is not formalized here. Includes the closed boundary q=1,r=0 in a separate branch.
Source: arXiv:2607.05492v1, formalization of the main results in §3 (no individual paper theorem
number is assigned).
-/
theorem andoTrace_jointlyConvexOn_pdSet
    {q r : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hqr : 1 ≤ q - r) (K : (ℋ →L[ℂ] ℋ)) :
    JointlyConvexOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (andoTraceMap (ℋ := ℋ) q r K) := by
  by_cases hqeq : q = 1
  · have hrz : r = 0 := by linarith
    subst hqeq
    subst hrz
    convert (liebTrace_jointlyConvexOn_pdSet (ℋ := ℋ)
      (s := 1) (by norm_num) (by norm_num) K) using 1
    ext A B
    simp [andoTraceMap, liebTraceMap]
  · have hqgt : 1 < q := lt_of_le_of_ne hq1 (Ne.symm hqeq)
    let β : ℝ := r / (q - 1)
    have hq1pos : 0 < q - 1 := by linarith
    have hβ0 : 0 ≤ β := by
      dsimp [β]
      positivity
    have hβ1 : β ≤ 1 := by
      dsimp [β]
      field_simp [hq1pos.ne']
      linarith
    have hβ : β ∈ Set.Icc (0 : ℝ) 1 := ⟨hβ0, hβ1⟩
    have hβmul : β * (1 - q) = -r := by
      dsimp [β]
      field_simp [hq1pos.ne']
      ring
    intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
    have hA_combo := pdSet_convexCombo (ℋ := ℋ) hA₁ hA₂ hθ0 hθ1
    have hB_combo := pdSet_convexCombo (ℋ := ℋ) hB₁ hB₂ hθ0 hθ1
    have hB₁β :=
      pdSet_rpow_of_mem_Icc_zero_one (ℋ := ℋ) hβ hB₁
    have hB₂β :=
      pdSet_rpow_of_mem_Icc_zero_one (ℋ := ℋ) hβ hB₂
    have hB_comboβ :=
      pdSet_rpow_of_mem_Icc_zero_one (ℋ := ℋ) hβ hB_combo
    have hBpow_combo := pdSet_convexCombo (ℋ := ℋ) hB₁β hB₂β hθ0 hθ1
    have hBpow_le :=
      convexCombo_rpow_le_rpow_convexCombo (ℋ := ℋ) hβ hB₁ hB₂ hθ0 hθ1
    have hmono := liebTraceMap_antitone_right (ℋ := ℋ) (s := q)
        (by constructor <;> linarith) K
        ((1 - θ) • A₁ + θ • A₂)
        ((1 - θ) • (B₁ ^ β) + θ • (B₂ ^ β))
        (((1 - θ) • B₁ + θ • B₂) ^ β)
        hA_combo hBpow_combo hB_comboβ hBpow_le
    have hconv :=
      liebTrace_jointlyConvexOn_pdSet (ℋ := ℋ) (s := q) hq1 hq2 K
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁ ^ β) (B₂ := B₂ ^ β)
        (θ := θ) hA₁ hA₂ hB₁β hB₂β hθ0 hθ1
    have hpow_rewrite :
        ∀ {A B : (ℋ →L[ℂ] ℋ)}, B ∈ pdSet (ℋ := ℋ) →
          liebTraceMap (ℋ := ℋ) q K A (B ^ β) =
            andoTraceMap (ℋ := ℋ) q r K A B :=
      fun {A B} hB => liebTraceMap_rpow_eq_andoTraceMap (ℋ := ℋ) hβmul K A hB
    simpa [hpow_rewrite hB₁, hpow_rewrite hB₂, hpow_rewrite hB_combo] using
      (le_trans hmono hconv)

/--
Source: I. Nikoufar, A. Ebadian, M. Eshaghi Gordji, "The simplest proof of Lieb concavity
theorem", Advances in Mathematics 248 (2013), 531--533, Corollary 1.3. Partial correspondence to the
representation using the real part of the trace for 1<r≤q≤2.
This declaration is about the real part of the trace; its identification with the complex trace
needs a separate argument, which is not formalized here. The Hilbert–Schmidt operator space is used.
-/
theorem liebCorollaryTrace_jointlyConvexOn_pdSet
    {q r : ℝ} (hr1 : 1 < r) (hrq : r ≤ q) (hq2 : q ≤ 2) (K : (ℋ →L[ℂ] ℋ)) :
    JointlyConvexOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (liebCorollaryTraceMap (ℋ := ℋ) q r K) := by
  have hq1 : 1 ≤ q := by linarith
  have hr0 : 0 ≤ r - 1 := by linarith
  have hr1' : r - 1 ≤ 1 := by linarith
  have hqr' : 1 ≤ q - (r - 1) := by linarith
  convert
    (andoTrace_jointlyConvexOn_pdSet (ℋ := ℋ) (q := q) (r := r - 1)
      hq1 hq2 hr0 hr1' hqr' K) using 1
  ext A B
  simp [liebCorollaryTraceMap, andoTraceMap]


end LiebAndoTrace
