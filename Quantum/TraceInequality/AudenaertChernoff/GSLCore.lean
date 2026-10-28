/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCoreGeneralizedStein
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCore
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# The Audenaert--Chernoff spectral inequality

This file proves the finite-dimensional noncommutative spectral inequality
used in the quantum Chernoff bound.  The proof is the direct Ozawa route:
with `Delta = (A - B)_+`, Loewner--Heinz monotonicity is applied along
`A <= B + Delta`, and positivity of trace pairings closes the estimate.

Source: K. M. R. Audenaert et al., "Discriminating States: The Quantum
Chernoff Bound", Physical Review Letters 98, 160501 (2007), Lemma 1;
Khatri--Wilde, arXiv:2011.04672v2, `QM_protocols.tex:746--821`.
-/

noncomputable section

open QuantumState
open scoped ComplexOrder NNReal

namespace AudenaertChernoff

private theorem trace_mul_re_nonneg
    {ℋ : Type*} [Qudit ℋ] (P Q : L ℋ)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    0 ≤ (Tr (P * Q)).re := by
  let S : L ℋ := CFC.sqrt P
  have hSadj : LinearMap.adjoint S = S := by
    rw [← LinearMap.star_eq_adjoint]
    exact (CFC.sqrt_nonneg P).isSelfAdjoint
  have hSsq : S * S = P := CFC.sqrt_mul_sqrt_self P hP
  have hQpos : Q.IsPositive := (LinearMap.nonneg_iff_isPositive Q).mp hQ
  have hconj : ((LinearMap.adjoint S) * (Q * S)).IsPositive :=
    hQpos.adjoint_conj S
  have htrace : Tr (P * Q) = Tr ((LinearMap.adjoint S) * (Q * S)) := by
    calc
      Tr (P * Q) = Tr (Q * P) :=
        (LinearMap.trace_comp_comm' P Q).symm
      _ = Tr (Q * (S * S)) := by rw [hSsq]
      _ = Tr ((Q * S) * S) := by rw [mul_assoc]
      _ = Tr (S * (Q * S)) := LinearMap.trace_comp_comm' S (Q * S)
      _ = Tr ((LinearMap.adjoint S) * (Q * S)) := by rw [hSadj]
  rw [htrace]
  exact (Complex.nonneg_iff.mp hconj.trace_nonneg).1

private theorem trace_mul_re_mono_right
    {ℋ : Type*} [Qudit ℋ] {P Q R : L ℋ}
    (hP : 0 ≤ P) (hQR : Q ≤ R) :
    (Tr (P * Q)).re ≤ (Tr (P * R)).re := by
  have h := trace_mul_re_nonneg P (R - Q) hP (sub_nonneg.mpr hQR)
  rw [mul_sub, map_sub, Complex.sub_re] at h
  linarith

private theorem trace_mul_re_mono_left
    {ℋ : Type*} [Qudit ℋ] {P Q R : L ℋ}
    (hR : 0 ≤ R) (hPQ : P ≤ Q) :
    (Tr (P * R)).re ≤ (Tr (Q * R)).re := by
  have h := trace_mul_re_nonneg (Q - P) R (sub_nonneg.mpr hPQ) hR
  rw [sub_mul, map_sub, Complex.sub_re] at h
  linarith

private theorem rpow_mul_rpow_one
    {ℋ : Type*} [Qudit ℋ] (X : L ℋ) (hX : 0 ≤ X)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    CFC.rpow X s * CFC.rpow X (1 - s) = X := by
  let a : ℝ≥0 := ⟨s, hs0.le⟩
  let b : ℝ≥0 := ⟨1 - s, sub_pos.mpr hs1 |>.le⟩
  have ha : 0 < a := by exact_mod_cast hs0
  have hb : 0 < b := by
    exact_mod_cast sub_pos.mpr hs1
  have hab : a + b = 1 := by
    apply Subtype.ext
    dsimp only [a, b]
    norm_num
  have haReal : CFC.nnrpow X a = CFC.rpow X s := by
    simpa only [a] using (CFC.nnrpow_eq_rpow (a := X) (x := a) ha)
  have hbReal : CFC.nnrpow X b = CFC.rpow X (1 - s) := by
    simpa only [b] using (CFC.nnrpow_eq_rpow (a := X) (x := b) hb)
  rw [← haReal, ← hbReal]
  calc
    CFC.nnrpow X a * CFC.nnrpow X b = CFC.nnrpow X (a + b) :=
      (CFC.nnrpow_add ha hb).symm
    _ = CFC.nnrpow X 1 := by rw [hab]
    _ = X := CFC.nnrpow_one X hX

/-- The Audenaert--Chernoff noncommutative spectral inequality.

For positive semidefinite `A` and `B` and `0 < s < 1`, the optimal binary
Holevo--Helstrom overlap is bounded by the Petz trace-power overlap.
-/
theorem spectral_inequality
    {ℋ : Type*} [Qudit ℋ]
    (A B : L ℋ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (1 / 2 : ℝ) *
        ((Tr (A + B)).re - (Tr (CFC.abs (A - B))).re) ≤
      (Tr (CFC.rpow A s * CFC.rpow B (1 - s))).re := by
  let Delta : L ℋ := (A - B)⁺
  let Gamma : L ℋ := (A - B)⁻
  let C : L ℋ := B + Delta
  have hAB : IsSelfAdjoint (A - B) :=
    (IsSelfAdjoint.of_nonneg hA).sub (IsSelfAdjoint.of_nonneg hB)
  have hDelta : 0 ≤ Delta := by
    simpa only [Delta] using CFC.posPart_nonneg (A - B)
  have hGamma : 0 ≤ Gamma := by
    simpa only [Gamma] using CFC.negPart_nonneg (A - B)
  have hdecomp : Delta - Gamma = A - B := by
    simpa only [Delta, Gamma] using CFC.posPart_sub_negPart (A - B) hAB
  have hAC : A ≤ C := by
    rw [← sub_nonneg]
    have : C - A = Gamma := by
      calc
        C - A = (Delta - Gamma) - (A - B) + Gamma := by
          dsimp only [C]
          abel
        _ = Gamma := by rw [hdecomp, sub_self, zero_add]
    rw [this]
    exact hGamma
  have hBC : B ≤ C := by
    dsimp only [C]
    exact le_add_of_nonneg_right hDelta
  have hC : 0 ≤ C := hB.trans hBC
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs0.le, hs1.le⟩
  have hOneSub : 1 - s ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith
  have hpowS : CFC.rpow A s ≤ CFC.rpow C s :=
    CFC.rpow_le_rpow hs hAC
  have hpowOneSubAC : CFC.rpow A (1 - s) ≤ CFC.rpow C (1 - s) :=
    CFC.rpow_le_rpow hOneSub hAC
  have hpowOneSubBC : CFC.rpow B (1 - s) ≤ CFC.rpow C (1 - s) :=
    CFC.rpow_le_rpow hOneSub hBC
  have hfirst :
      (Tr (CFC.rpow A s *
          (CFC.rpow A (1 - s) - CFC.rpow B (1 - s)))).re ≤
        (Tr (CFC.rpow C s *
          (CFC.rpow C (1 - s) - CFC.rpow B (1 - s)))).re := by
    calc
      (Tr (CFC.rpow A s *
          (CFC.rpow A (1 - s) - CFC.rpow B (1 - s)))).re ≤
          (Tr (CFC.rpow A s *
            (CFC.rpow C (1 - s) - CFC.rpow B (1 - s)))).re := by
        apply trace_mul_re_mono_right CFC.rpow_nonneg
        exact sub_le_sub_right hpowOneSubAC _
      _ ≤ (Tr (CFC.rpow C s *
          (CFC.rpow C (1 - s) - CFC.rpow B (1 - s)))).re := by
        apply trace_mul_re_mono_left (sub_nonneg.mpr hpowOneSubBC)
        exact hpowS
  have hpowSB : CFC.rpow B s ≤ CFC.rpow C s :=
    CFC.rpow_le_rpow hs hBC
  have hcross :
      (Tr B).re ≤
        (Tr (CFC.rpow C s * CFC.rpow B (1 - s))).re := by
    calc
      (Tr B).re =
          (Tr (CFC.rpow B s * CFC.rpow B (1 - s))).re := by
        rw [rpow_mul_rpow_one B hB s hs0 hs1]
      _ ≤ (Tr (CFC.rpow C s * CFC.rpow B (1 - s))).re :=
        trace_mul_re_mono_left CFC.rpow_nonneg hpowSB
  have hdefect :
      (Tr A).re -
          (Tr (CFC.rpow A s * CFC.rpow B (1 - s))).re ≤
        (Tr Delta).re := by
    have hfirst' :
        (Tr A).re -
            (Tr (CFC.rpow A s * CFC.rpow B (1 - s))).re ≤
          (Tr C).re -
            (Tr (CFC.rpow C s * CFC.rpow B (1 - s))).re := by
      simpa only [mul_sub, map_sub, Complex.sub_re,
        rpow_mul_rpow_one A hA s hs0 hs1,
        rpow_mul_rpow_one C hC s hs0 hs1] using hfirst
    have htraceC : (Tr C).re = (Tr B).re + (Tr Delta).re := by
      simp only [C, map_add, Complex.add_re]
    linarith
  have habs : CFC.abs (A - B) = Delta + Gamma := by
    simpa only [Delta, Gamma] using (CFC.posPart_add_negPart (A - B) hAB).symm
  have htraceDecomp :
      (Tr Delta).re - (Tr Gamma).re = (Tr A).re - (Tr B).re := by
    have := congrArg (fun X : L ℋ => (Tr X).re) hdecomp
    simpa only [map_sub, Complex.sub_re] using this
  have htraceAbs :
      (Tr (CFC.abs (A - B))).re = (Tr Delta).re + (Tr Gamma).re := by
    rw [habs, map_add, Complex.add_re]
  have hleft :
      (1 / 2 : ℝ) *
          ((Tr (A + B)).re - (Tr (CFC.abs (A - B))).re) =
        (Tr A).re - (Tr Delta).re := by
    rw [map_add, Complex.add_re, htraceAbs]
    linarith
  rw [hleft]
  linarith

end AudenaertChernoff
