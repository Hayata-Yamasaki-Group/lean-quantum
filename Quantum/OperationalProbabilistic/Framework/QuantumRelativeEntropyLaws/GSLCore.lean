/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiOrder.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivConcrete.GSLCore
import Quantum.OperationalProbabilistic.Framework.OrderedConeMaxRelativeEntropy.GSLCore
import Mathlib.Analysis.SpecialFunctions.Log.Base

open CategoryTheory Set
open scoped MonoidalCategory ENNReal NNReal

/-!
# Binary calibration for relative-entropy laws

The type `ERealStateDivergence` of extended-real state divergences, the base-two negative
logarithm `binaryNegLog2` of binary exponent probabilities, and the uniqueness of monotone
additive functions on `ℝ≥0`, which identifies a binary calibration with `binaryNegLog2`
(`binaryCalibration_eq_negLog2`).  This is the analytic step of Lemma 1.1 in M. Tomamichel,
*Quantum Relative Entropy: An Axiomatic Approach*, QMath Masterclass notes, Copenhagen,
August 2022.
-/

namespace OPT

noncomputable section

universe u v w

/-- The calibrated binary divergence value, including the zero boundary.

This is the conclusion of Tomamichel Lemma 1.1: for `0 < p ≤ 1` the value
is `-log₂ p`, while `p = 0` has the extended-real value `top`. -/
noncomputable def binaryNegLog2 (p : ℝ≥0) : EReal :=
  if p = 0 then ⊤ else ((-Real.logb 2 (p : ℝ) : ℝ) : EReal)

/-- The zero-probability endpoint of Tomamichel Lemma 1.1 is positive
infinity in `EReal`. -/
@[simp]
theorem binaryNegLog2_zero : binaryNegLog2 0 = ⊤ := by
  simp [binaryNegLog2]

/-- The binary probability corresponding to a nonnegative base-two
domination exponent in the preparation proof of Tomamichel Property 6. -/
noncomputable def binaryExponentProbability (lam : ℝ) : ℝ≥0 :=
  (2 : ℝ≥0) ^ (-lam)

/-- A nonnegative domination exponent gives a binary probability at most
one.  This is the finite side of the `p = 0`/`+∞` boundary in Tomamichel
Lemma 1.1. -/
theorem binaryExponentProbability_le_one {lam : ℝ} (hlam : 0 ≤ lam) :
    binaryExponentProbability lam ≤ 1 := by
  exact NNReal.rpow_le_one_of_one_le_of_nonpos
    (by norm_num) (neg_nonpos.mpr hlam)

/-- Calibrating `p = 2⁻ˡᵃᵐ` recovers the finite base-two exponent `lam`.

Together with `binaryNegLog2_zero`, this records both the finite and the
`+∞` branches of Tomamichel Lemma 1.1. -/
theorem binaryNegLog2_binaryExponentProbability (lam : ℝ) :
    binaryNegLog2 (binaryExponentProbability lam) = (lam : EReal) := by
  rw [binaryNegLog2, if_neg]
  · congr 1
    simp [binaryExponentProbability, NNReal.coe_rpow, Real.logb_rpow]
  · exact ne_of_gt (NNReal.rpow_pos (by norm_num))

private lemma monotoneAdditiveNNReal_eq
    (g : ℝ≥0 → ℝ)
    (hadd : ∀ x y, g (x + y) = g x + g y)
    (hmono : Monotone g) (hone : g 1 = 1) (x : ℝ≥0) :
    g x = (x : ℝ) := by
  have hzero : g 0 = 0 := by
    have h := hadd 0 0
    simp only [zero_add] at h
    linarith
  let G : ℝ≥0 →+ ℝ :=
    { toFun := g
      map_zero' := hzero
      map_add' := hadd }
  have hG (y : ℝ≥0) : G y = g y := rfl
  have hrat (q : ℚ≥0) : g (q : ℝ≥0) = (q : ℝ) := by
    have h := map_nnrat_smul G q (1 : ℝ≥0)
    rw [hG, hG] at h
    simpa only [NNRat.smul_def, mul_one, hone] using h
  apply le_antisymm
  · by_contra hnot
    have hlt : (x : ℝ) < g x := lt_of_not_ge hnot
    obtain ⟨q, hxq, hqg⟩ := exists_rat_btwn hlt
    let qnn : ℚ≥0 := ⟨q, by
      exact_mod_cast
        (le_trans x.property (le_of_lt hxq) : (0 : ℝ) ≤ (q : ℝ))⟩
    have hxqnn : x ≤ (qnn : ℝ≥0) := by
      exact_mod_cast le_of_lt hxq
    have hle := hmono hxqnn
    rw [hrat qnn] at hle
    exact (not_le_of_gt hqg) hle
  · by_contra hnot
    have hlt : g x < (x : ℝ) := lt_of_not_ge hnot
    have hg_nonneg : 0 ≤ g x := by
      rw [← hzero]
      exact hmono bot_le
    obtain ⟨q, hgq, hqx⟩ := exists_rat_btwn hlt
    let qnn : ℚ≥0 := ⟨q, by
      exact_mod_cast
        (le_trans hg_nonneg (le_of_lt hgq) : (0 : ℝ) ≤ (q : ℝ))⟩
    have hqnnx : (qnn : ℝ≥0) ≤ x := by
      exact_mod_cast le_of_lt hqx
    have hle := hmono hqnnx
    rw [hrat qnn] at hle
    exact (not_le_of_gt hgq) hle

/-- Multiplicative additivity, monotonicity, and the fair-bit normalization
force the binary negative logarithm.

This discharges the analytic hard point of Tomamichel Lemma 1.1.  Unlike a
finite-real-only proof, the statement and proof include `p = 0`, where
repeated multiplicative additivity forces the value `top`; the positive
branch is reduced to a monotone additive function on `NNReal`. -/
lemma binaryCalibration_eq_negLog2
    (f : ℝ≥0 → EReal)
    (hmul : ∀ p q : ℝ≥0, p ≤ 1 → q ≤ 1 →
      f (p * q) = f p + f q)
    (hanti : AntitoneOn f (Icc 0 1))
    (hnorm : f ((2 : ℝ≥0)⁻¹) = 1)
    (p : ℝ≥0) (hp : p ≤ 1) :
    f p = binaryNegLog2 p := by
  let half : ℝ≥0 := (2 : ℝ≥0)⁻¹
  have hhalf_mem : half ∈ Icc (0 : ℝ≥0) 1 := by
    constructor <;> norm_num [half]
  have hone_mem : (1 : ℝ≥0) ∈ Icc 0 1 := by simp
  have hzero_mem : (0 : ℝ≥0) ∈ Icc 0 1 := by simp
  have hf_one : f 1 = 0 := by
    have h := hmul half 1 hhalf_mem.2 (le_refl 1)
    rw [mul_one, hnorm] at h
    calc
      f 1 = (1 : EReal) + f 1 - (1 : ℝ) :=
        EReal.add_sub_cancel_left.symm
      _ = (1 : EReal) - (1 : ℝ) :=
        congrArg (fun z : EReal => z - (1 : ℝ)) h.symm
      _ = 0 := by
        rw [← EReal.coe_one, ← EReal.coe_sub]
        norm_num
  have hf_half_pow : ∀ n : ℕ, f (half ^ n) = (n : EReal) := by
    intro n
    induction n with
    | zero => simp [hf_one]
    | succ n ih =>
        rw [pow_succ,
          hmul (half ^ n) half
            (pow_le_one₀ (by positivity) hhalf_mem.2)
            hhalf_mem.2,
          ih, hnorm]
        norm_num
  have hfinite {q : ℝ≥0} (hq0 : 0 < q) (hq1 : q ≤ 1) :
      f q ≠ ⊤ ∧ f q ≠ ⊥ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hq0
      (by norm_num [half] : half < 1)
    have hq_mem : q ∈ Icc (0 : ℝ≥0) 1 := ⟨hq0.le, hq1⟩
    have hpow_mem : half ^ n ∈ Icc (0 : ℝ≥0) 1 :=
      ⟨bot_le, pow_le_one₀ (by positivity) hhalf_mem.2⟩
    have hupper : f q ≤ (n : EReal) := by
      calc
        f q ≤ f (half ^ n) := hanti hpow_mem hq_mem (le_of_lt hn)
        _ = (n : EReal) := hf_half_pow n
    have hlower : 0 ≤ f q := by
      calc
        0 = f 1 := hf_one.symm
        _ ≤ f q := hanti hq_mem hone_mem hq1
    exact ⟨ne_top_of_lt (hupper.trans_lt (EReal.coe_lt_top (n : ℝ))),
      ne_bot_of_gt (EReal.bot_lt_zero.trans_le hlower)⟩
  by_cases hp0 : p = 0
  · subst p
    rw [binaryNegLog2, if_pos rfl]
    have hrec := hmul (0 : ℝ≥0) 0 (by norm_num) (by norm_num)
    simp only [zero_mul] at hrec
    have hone_le : (1 : EReal) ≤ f 0 := by
      rw [← hnorm]
      exact hanti hzero_mem hhalf_mem (by norm_num [half])
    have hf0_ne_bot : f 0 ≠ ⊥ :=
      ne_bot_of_gt ((EReal.bot_lt_zero.trans (by norm_num : (0 : EReal) < 1)).trans_le hone_le)
    by_contra hf0_ne_top
    have hreal := congrArg EReal.toReal hrec
    rw [EReal.toReal_add hf0_ne_top hf0_ne_bot hf0_ne_top hf0_ne_bot] at hreal
    have hone_real : (1 : ℝ) ≤ (f 0).toReal := by
      have h := hone_le
      rw [← EReal.coe_toReal hf0_ne_top hf0_ne_bot] at h
      exact_mod_cast h
    linarith
  · have hp_pos : 0 < p := pos_iff_ne_zero.mpr hp0
    let pOf : ℝ≥0 → ℝ≥0 :=
      fun x => (2 : ℝ≥0) ^ (-(x : ℝ))
    have hpOf_pos (x : ℝ≥0) : 0 < pOf x := by
      exact NNReal.rpow_pos (by norm_num)
    have hpOf_le_one (x : ℝ≥0) : pOf x ≤ 1 := by
      exact NNReal.rpow_le_one_of_one_le_of_nonpos
        (by norm_num) (neg_nonpos.mpr x.property)
    let g : ℝ≥0 → ℝ := fun x => (f (pOf x)).toReal
    have hg_add (x y : ℝ≥0) : g (x + y) = g x + g y := by
      have hpOf_add : pOf (x + y) = pOf x * pOf y := by
        simp only [pOf]
        rw [show -((x + y : ℝ≥0) : ℝ) =
            -(x : ℝ) + -(y : ℝ) by push_cast; ring,
          NNReal.rpow_add (by norm_num)]
      have hmul' := hmul (pOf x) (pOf y) (hpOf_le_one x) (hpOf_le_one y)
      have hxfin := hfinite (hpOf_pos x) (hpOf_le_one x)
      have hyfin := hfinite (hpOf_pos y) (hpOf_le_one y)
      simp only [g, hpOf_add, hmul']
      exact EReal.toReal_add hxfin.1 hxfin.2 hyfin.1 hyfin.2
    have hg_mono : Monotone g := by
      intro x y hxy
      have hpOf_yx : pOf y ≤ pOf x := by
        exact NNReal.rpow_le_rpow_of_exponent_le (by norm_num)
          (neg_le_neg (by exact_mod_cast hxy))
      have hfxfy : f (pOf x) ≤ f (pOf y) :=
        hanti ⟨bot_le, hpOf_le_one y⟩ ⟨bot_le, hpOf_le_one x⟩ hpOf_yx
      have hxfin := hfinite (hpOf_pos x) (hpOf_le_one x)
      have hyfin := hfinite (hpOf_pos y) (hpOf_le_one y)
      rw [← EReal.coe_toReal hxfin.1 hxfin.2,
        ← EReal.coe_toReal hyfin.1 hyfin.2] at hfxfy
      exact_mod_cast hfxfy
    have hpOf_one : pOf 1 = half := by
      simp [pOf, half, NNReal.rpow_neg_one]
    have hg_one : g 1 = 1 := by
      change (f (pOf 1)).toReal = 1
      rw [hpOf_one]
      rw [hnorm]
      norm_num
    let x : ℝ≥0 :=
      ⟨-Real.logb 2 (p : ℝ),
        neg_nonneg.mpr
          (Real.logb_nonpos (by norm_num) p.property (by exact_mod_cast hp))⟩
    have hpOf_x : pOf x = p := by
      apply NNReal.eq
      change (2 : ℝ) ^ (-(-Real.logb 2 (p : ℝ))) = (p : ℝ)
      rw [neg_neg, Real.rpow_logb (by norm_num) (by norm_num)
        (by exact_mod_cast hp_pos)]
    have hg_x : g x = (x : ℝ) :=
      monotoneAdditiveNNReal_eq g hg_add hg_mono hg_one x
    have hpfin := hfinite hp_pos hp
    have hto : (f p).toReal = (x : ℝ) := by
      rw [← hpOf_x]
      exact hg_x
    rw [binaryNegLog2, if_neg hp0]
    calc
      f p = ((f p).toReal : EReal) :=
        (EReal.coe_toReal hpfin.1 hpfin.2).symm
      _ = ((x : ℝ) : EReal) := congrArg (fun z : ℝ => (z : EReal)) hto
      _ = ((-Real.logb 2 (p : ℝ) : ℝ) : EReal) := rfl

end

end OPT
