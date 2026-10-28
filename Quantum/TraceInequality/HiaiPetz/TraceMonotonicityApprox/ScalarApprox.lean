/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Topology.UniformSpace.Dini

/-!
# Scalar truncated approximation for `x ^ p` (Hiai--Petz Theorem 6.3(3))

The scalar approximants `f_n = a_n * x - ψ_n(x)` from the truncated
operator-monotone integral representation of `x ^ p` for `1 < p < 2`:
integral forms, nonnegativity, monotonicity in the cutoff, and the pointwise
limit `powerApprox_tendsto_rpow`.
-/

namespace HiaiPetz

namespace TraceMonotonicity

open scoped Topology Interval

noncomputable section ScalarApproximation

/-- The coefficient `sin((p - 1)π) / π` in the PDF proof of Theorem 6.3(3).
Source: Hiai, proof of Theorem 6.3. -/
noncomputable def sinCoeff (p : ℝ) : ℝ :=
  Real.sin ((p - 1) * Real.pi) / Real.pi

/-- Lean's `k : ℕ` encodes the book cutoff `n = k + 1 ≥ 1`.
Source: Hiai, proof of Theorem 6.3. -/
def cutoff (k : ℕ) : ℝ :=
  (k : ℝ) + 1

/-- The scalar kernel `x ↦ x / (x + t)` used in the truncated integral.
Source: Hiai, proof of Theorem 6.3. -/
def mobiusKernel (t : ℝ) : ℝ → ℝ :=
  fun x : ℝ => x / (x + t)

/-- The scalar coefficient `a_n`, with `n = k + 1`, from the PDF proof.
Source: Hiai, proof of Theorem 6.3. -/
noncomputable def approxCoeff (p : ℝ) (k : ℕ) : ℝ :=
  sinCoeff p * ∫ t in (cutoff k)⁻¹..cutoff k, t ^ (p - 2)

/-- The truncated operator-monotone integral `ψ_n`, with `n = k + 1`, from the PDF proof.
Source: Hiai, proof of Theorem 6.3. -/
noncomputable def psiApprox (p : ℝ) (k : ℕ) : ℝ → ℝ :=
  fun x : ℝ =>
    sinCoeff p *
      ∫ t in (cutoff k)⁻¹..cutoff k, x * t ^ (p - 1) / (x + t)

/-- The truncated approximation `f_n = a_n x - ψ_n(x)`, with `n = k + 1`.
Source: Hiai, proof of Theorem 6.3. -/
noncomputable def powerApprox (p : ℝ) (k : ℕ) : ℝ → ℝ :=
  fun x : ℝ => approxCoeff p k * x - psiApprox p k x

/-- The cutoff `k + 1` is positive.
Local API: auxiliary positivity fact; used in Hiai, proof of Theorem 6.3. -/
theorem cutoff_pos (k : ℕ) :
    0 < cutoff k := by
  dsimp [cutoff]
  positivity

/-- The reciprocal cutoff is positive.
Local API: auxiliary positivity fact; used in Hiai, proof of Theorem 6.3. -/
theorem cutoff_inv_pos (k : ℕ) :
    0 < (cutoff k)⁻¹ := by
  exact inv_pos.mpr (cutoff_pos k)

/-- The truncated interval is nonempty: `(cutoff k)⁻¹ ≤ cutoff k`.  (The strict,
positive-length statement for `k ≠ 0` is supplied by the next theorem.)
Source: Hiai, proof of Theorem 6.3. -/
theorem cutoff_inv_le (k : ℕ) :
    (cutoff k)⁻¹ ≤ cutoff k := by
  have h1 : (1 : ℝ) ≤ cutoff k := by
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
    dsimp [cutoff]
    linarith
  exact (inv_le_one_of_one_le₀ h1).trans h1

/-- For nonzero `k`, the truncated interval has positive length.
Source: Hiai, proof of Theorem 6.3. -/
theorem cutoff_inv_lt_of_pos {k : ℕ} (hk : 0 < k) :
    (cutoff k)⁻¹ < cutoff k := by
  have h1 : (1 : ℝ) < cutoff k := by
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    dsimp [cutoff]
    linarith
  exact (inv_le_one_of_one_le₀ h1.le).trans_lt h1

/-- The sine coefficient in the PDF proof is positive for `1 < p < 2`.
Source: Hiai, proof of Theorem 6.3. -/
theorem sinCoeff_pos {p : ℝ} (hp : p ∈ Set.Ioo (1 : ℝ) 2) :
    0 < sinCoeff p := by
  have h0 : 0 < p - 1 := sub_pos.mpr hp.1
  have h1 : p - 1 < 1 := by linarith [hp.2]
  have hangle0 : 0 < (p - 1) * Real.pi := mul_pos h0 Real.pi_pos
  have hangle1 : (p - 1) * Real.pi < Real.pi := by
    simpa using (mul_lt_mul_of_pos_right h1 Real.pi_pos)
  have hsin : 0 < Real.sin ((p - 1) * Real.pi) :=
    Real.sin_pos_of_mem_Ioo ⟨hangle0, hangle1⟩
  exact div_pos hsin Real.pi_pos

private theorem sub_one_mem_Ioo {p : ℝ} (hp : p ∈ Set.Ioo (1 : ℝ) 2) :
    p - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
  exact ⟨sub_pos.mpr hp.1, by linarith [hp.2]⟩


@[fun_prop] private theorem rpowSubTwo_continuousOn_Icc {p a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => t ^ (p - 2)) (Set.Icc a b) := by
  refine continuousOn_id.rpow_const ?_
  intro t ht
  exact Or.inl (ne_of_gt (ha.trans_le ht.1))

private theorem rpowSubTwo_intervalIntegrable {p a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => t ^ (p - 2)) MeasureTheory.volume a b :=
  (rpowSubTwo_continuousOn_Icc (p := p) (a := a) (b := b) ha).intervalIntegrable_of_Icc
    hab

@[fun_prop] private theorem psiScalarIntegrand_continuousOn_Icc {p a b x : ℝ} (ha : 0 < a)
    (hx : 0 ≤ x) :
    ContinuousOn (fun t : ℝ => x * t ^ (p - 1) / (x + t)) (Set.Icc a b) := by
  have htpos : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => ha.trans_le ht.1
  have hden : ∀ t ∈ Set.Icc a b, x + t ≠ 0 := by
    intro t ht
    exact ne_of_gt (add_pos_of_nonneg_of_pos hx (htpos t ht))
  have hrpow :
      ContinuousOn (fun t : ℝ => t ^ (p - 1)) (Set.Icc a b) := by
    refine continuousOn_id.rpow_const ?_
    intro t ht
    exact Or.inl (ne_of_gt (htpos t ht))
  exact ((continuousOn_const.mul hrpow).div (continuousOn_const.add continuousOn_id) hden)

private theorem psiScalarIntegrand_intervalIntegrable {p a b x : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hx : 0 ≤ x) :
    IntervalIntegrable (fun t : ℝ => x * t ^ (p - 1) / (x + t))
      MeasureTheory.volume a b :=
  (psiScalarIntegrand_continuousOn_Icc (p := p) (a := a) (b := b) (x := x) ha hx)
    |>.intervalIntegrable_of_Icc hab

@[fun_prop] private theorem powerPositiveKernel_continuousOn_Icc {p a b x : ℝ} (ha : 0 < a)
    (hx : 0 ≤ x) :
    ContinuousOn (fun t : ℝ => x ^ 2 * t ^ (p - 2) / (x + t)) (Set.Icc a b) := by
  have htpos : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => ha.trans_le ht.1
  have hden : ∀ t ∈ Set.Icc a b, x + t ≠ 0 := by
    intro t ht
    exact ne_of_gt (add_pos_of_nonneg_of_pos hx (htpos t ht))
  have hrpow :
      ContinuousOn (fun t : ℝ => t ^ (p - 2)) (Set.Icc a b) :=
    rpowSubTwo_continuousOn_Icc (p := p) (a := a) (b := b) ha
  exact (((continuousOn_const.pow 2).mul hrpow).div
    (continuousOn_const.add continuousOn_id) hden)

private theorem powerPositiveKernel_intervalIntegrable {p a b x : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hx : 0 ≤ x) :
    IntervalIntegrable (fun t : ℝ => x ^ 2 * t ^ (p - 2) / (x + t))
      MeasureTheory.volume a b :=
  (powerPositiveKernel_continuousOn_Icc (p := p) (a := a) (b := b) (x := x) ha hx)
    |>.intervalIntegrable_of_Icc hab

/-- The truncated approximation has the positive-kernel integral form from the PDF proof.
Source: Hiai, proof of Theorem 6.3. -/
theorem powerApprox_eq_integral_positiveKernel (p : ℝ) (k : ℕ) {x : ℝ}
    (hx : 0 ≤ x) :
    powerApprox p k x =
      sinCoeff p *
        ∫ t in (cutoff k)⁻¹..cutoff k, x ^ 2 * t ^ (p - 2) / (x + t) := by
  let a : ℝ := (cutoff k)⁻¹
  let b : ℝ := cutoff k
  have ha : 0 < a := by
    simpa [a] using cutoff_inv_pos k
  have hab : a ≤ b := by
    simpa [a, b] using cutoff_inv_le k
  have hpowInt :
      IntervalIntegrable (fun t : ℝ => t ^ (p - 2)) MeasureTheory.volume a b :=
    rpowSubTwo_intervalIntegrable (p := p) ha hab
  have hleftInt :
      IntervalIntegrable (fun t : ℝ => t ^ (p - 2) * x) MeasureTheory.volume a b :=
    hpowInt.mul_const x
  have hpsiInt :
      IntervalIntegrable (fun t : ℝ => x * t ^ (p - 1) / (x + t))
        MeasureTheory.volume a b :=
    psiScalarIntegrand_intervalIntegrable (p := p) ha hab hx
  have hpoint :
      (∫ t in a..b, t ^ (p - 2) * x - x * t ^ (p - 1) / (x + t)) =
        ∫ t in a..b, x ^ 2 * t ^ (p - 2) / (x + t) := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    have htIcc : t ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using ht
    have htpos : 0 < t := ha.trans_le htIcc.1
    have hden : x + t ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos hx htpos)
    have hpow : t ^ (p - 1) = t ^ (p - 2) * t := by
      have h : p - 1 = (p - 2) + 1 := by ring
      rw [h, Real.rpow_add htpos (p - 2) 1]
      simp
    change t ^ (p - 2) * x - x * t ^ (p - 1) / (x + t) =
      x ^ 2 * t ^ (p - 2) / (x + t)
    rw [hpow]
    field_simp [hden]
    ring
  calc
    powerApprox p k x
        = sinCoeff p *
            ((∫ t in a..b, t ^ (p - 2)) * x -
              ∫ t in a..b, x * t ^ (p - 1) / (x + t)) := by
            dsimp [powerApprox, approxCoeff, psiApprox, a, b]
            ring
    _ = sinCoeff p *
            ((∫ t in a..b, t ^ (p - 2) * x) -
              ∫ t in a..b, x * t ^ (p - 1) / (x + t)) := by
            rw [intervalIntegral.integral_mul_const]
    _ = sinCoeff p *
            (∫ t in a..b, t ^ (p - 2) * x - x * t ^ (p - 1) / (x + t)) := by
            rw [intervalIntegral.integral_sub hleftInt hpsiInt]
    _ = sinCoeff p *
            (∫ t in a..b, x ^ 2 * t ^ (p - 2) / (x + t)) := by
            rw [hpoint]
    _ = sinCoeff p *
          ∫ t in (cutoff k)⁻¹..cutoff k, x ^ 2 * t ^ (p - 2) / (x + t) := by
          rfl

private theorem powerPositiveKernel_nonneg {p x t : ℝ} (hx : 0 ≤ x) (ht : 0 < t) :
    0 ≤ x ^ 2 * t ^ (p - 2) / (x + t) := by
  have hden : 0 ≤ x + t := le_of_lt (add_pos_of_nonneg_of_pos hx ht)
  exact div_nonneg (mul_nonneg (sq_nonneg x) (Real.rpow_nonneg (le_of_lt ht) _)) hden

/-- The positive-kernel form makes every truncated approximation nonnegative on `[0,∞)`.
Source: Hiai, proof of Theorem 6.3. -/
theorem powerApprox_nonneg_Ioi {p : ℝ} (hp : p ∈ Set.Ioo (1 : ℝ) 2)
    (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ powerApprox p k x := by
  rw [powerApprox_eq_integral_positiveKernel p k hx]
  refine mul_nonneg (le_of_lt (sinCoeff_pos hp)) ?_
  refine intervalIntegral.integral_nonneg (cutoff_inv_le k) ?_
  intro t ht
  exact powerPositiveKernel_nonneg (p := p) hx ((cutoff_inv_pos k).trans_le ht.1)

private theorem cutoff_mono :
    Monotone cutoff := by
  intro i j hij
  dsimp [cutoff]
  have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  linarith

private theorem cutoff_inv_antitone :
    Antitone fun k : ℕ => (cutoff k)⁻¹ := by
  intro i j hij
  exact inv_anti₀ (cutoff_pos i) (cutoff_mono hij)

/-- The truncated approximations are monotone increasing as the cutoff interval expands.
Source: Hiai, proof of Theorem 6.3. -/
theorem powerApprox_monotone_cutoff {p x : ℝ} (hp : p ∈ Set.Ioo (1 : ℝ) 2)
    (hx : 0 ≤ x) :
    Monotone fun k : ℕ => powerApprox p k x := by
  intro i j hij
  change powerApprox p i x ≤ powerApprox p j x
  rw [powerApprox_eq_integral_positiveKernel p i hx,
    powerApprox_eq_integral_positiveKernel p j hx]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (sinCoeff_pos hp))
  refine intervalIntegral.integral_mono_interval (μ := MeasureTheory.volume)
    (f := fun t : ℝ => x ^ 2 * t ^ (p - 2) / (x + t))
    (cutoff_inv_antitone hij) (cutoff_inv_le i) (cutoff_mono hij) ?_ ?_
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
    exact Filter.Eventually.of_forall fun t ht =>
      powerPositiveKernel_nonneg (p := p) hx ((cutoff_inv_pos j).trans ht.1)
  · exact powerPositiveKernel_intervalIntegrable (p := p)
      (a := (cutoff j)⁻¹) (b := cutoff j) (x := x)
      (cutoff_inv_pos j) (cutoff_inv_le j) hx

private def cutoffSet (k : ℕ) : Set ℝ :=
  Set.Ioc ((cutoff k)⁻¹) (cutoff k)

private theorem cutoffSet_mono :
    Monotone cutoffSet := by
  intro i j hij t ht
  exact ⟨lt_of_le_of_lt (cutoff_inv_antitone hij) ht.1,
    (cutoff_mono hij).trans' ht.2⟩

private theorem iUnion_cutoffSet :
    (Set.iUnion fun k : ℕ => cutoffSet k) = Set.Ioi (0 : ℝ) := by
  ext t
  simp only [Set.mem_iUnion, cutoffSet, Set.mem_Ioc, Set.mem_Ioi]
  constructor
  · rintro ⟨k, ht⟩
    exact (cutoff_inv_pos k).trans ht.1
  · intro ht
    obtain ⟨k, hk⟩ := exists_nat_gt (max t t⁻¹)
    refine ⟨k, ?_⟩
    have hcut_gt_max : max t t⁻¹ < cutoff k := by
      dsimp [cutoff]
      have hk' : max t t⁻¹ < (k : ℝ) := hk
      linarith
    exact ⟨(inv_lt_comm₀ (cutoff_pos k) ht).mpr
        ((le_max_right t t⁻¹).trans_lt hcut_gt_max),
      (le_max_left t t⁻¹).trans hcut_gt_max.le⟩

private theorem powerApprox_eq_setIntegral_rpowIntegrand {p : ℝ}
    (hp : p ∈ Set.Ioo (1 : ℝ) 2) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    powerApprox p k x =
      sinCoeff p *
        ∫ t in cutoffSet k, x * Real.rpowIntegrand₀₁ (p - 1) t x := by
  rw [powerApprox_eq_integral_positiveKernel p k hx,
    intervalIntegral.integral_of_le (cutoff_inv_le k)]
  congr 1
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
  intro t ht
  have htpos : 0 < t := (cutoff_inv_pos k).trans ht.1
  symm
  change x * Real.rpowIntegrand₀₁ (p - 1) t x =
    x ^ 2 * t ^ (p - 2) / (x + t)
  rw [Real.rpowIntegrand₀₁_eq_pow_div (sub_one_mem_Ioo hp) (le_of_lt htpos) hx]
  have hpow : p - 1 - 1 = p - 2 := by ring
  rw [hpow]
  ring_nf

private theorem rpowIntegrand_cutoff_tendsto {p x : ℝ}
    (hp : p ∈ Set.Ioo (1 : ℝ) 2) (hx : 0 ≤ x) :
    Filter.Tendsto
      (fun k : ℕ => ∫ t in cutoffSet k, x * Real.rpowIntegrand₀₁ (p - 1) t x)
      Filter.atTop
      (𝓝 (∫ t in Set.Ioi (0 : ℝ), x * Real.rpowIntegrand₀₁ (p - 1) t x)) := by
  have hint :
      MeasureTheory.IntegrableOn
        (fun t : ℝ => x * Real.rpowIntegrand₀₁ (p - 1) t x)
        (Set.iUnion fun k : ℕ => cutoffSet k) := by
    rw [iUnion_cutoffSet]
    exact (Real.integrableOn_rpowIntegrand₀₁_Ioi (sub_one_mem_Ioo hp) hx).const_mul x
  simpa [iUnion_cutoffSet] using
    (MeasureTheory.tendsto_setIntegral_of_monotone
      (μ := MeasureTheory.volume)
      (f := fun t : ℝ => x * Real.rpowIntegrand₀₁ (p - 1) t x)
      (s := cutoffSet) (fun _ => measurableSet_Ioc) cutoffSet_mono hint)

private theorem betaPoint {q y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    y ^ (q - 1) * (1 - y) ^ (-q) =
      RCLike.re ((y : ℂ) ^ ((q : ℂ) - 1) *
        (1 - (y : ℂ)) ^ ((1 - q : ℂ) - 1)) := by
  have h1y : 0 ≤ 1 - y := by linarith
  rw [show ((q : ℂ) - 1) = ((q - 1 : ℝ) : ℂ) by norm_num,
    show ((1 - q : ℂ) - 1) = ((-q : ℝ) : ℂ) by norm_num,
    show (1 - (y : ℂ)) = ((1 - y : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_cpow hy0.le (q - 1), ← Complex.ofReal_cpow h1y (-q)]
  norm_num

private theorem betaRealIntegral {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ y in Set.Ioo (0 : ℝ) 1, y ^ (q - 1) * (1 - y) ^ (-q)) =
      (Complex.betaIntegral (q : ℂ) (1 - q : ℂ)).re := by
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  change (∫ y in Set.Ioo (0 : ℝ) 1, y ^ (q - 1) * (1 - y) ^ (-q)) =
      RCLike.re (∫ x in Set.Ioc (0 : ℝ) 1,
        (x : ℂ) ^ ((q : ℂ) - 1) * (1 - (x : ℂ)) ^ ((1 - q : ℂ) - 1))
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hint : MeasureTheory.Integrable (fun x : ℝ =>
      (x : ℂ) ^ ((q : ℂ) - 1) * (1 - (x : ℂ)) ^ ((1 - q : ℂ) - 1))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    convert Complex.betaIntegral_convergent (u := (q : ℂ)) (v := (1 - q : ℂ))
      (by simpa using hq.1) (by simpa using sub_pos.mpr hq.2)
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1),
      MeasureTheory.IntegrableOn]
  calc
    (∫ y in Set.Ioo (0 : ℝ) 1, y ^ (q - 1) * (1 - y) ^ (-q))
        = ∫ y in Set.Ioo (0 : ℝ) 1,
            RCLike.re ((y : ℂ) ^ ((q : ℂ) - 1) *
              (1 - (y : ℂ)) ^ ((1 - q : ℂ) - 1)) := by
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo ?_
            intro y hy
            exact betaPoint hy.1 hy.2
    _ = RCLike.re (∫ x in Set.Ioo (0 : ℝ) 1,
        (x : ℂ) ^ ((q : ℂ) - 1) * (1 - (x : ℂ)) ^ ((1 - q : ℂ) - 1)) :=
        integral_re hint

private theorem fracMap_image_Ioo :
    (fun y : ℝ => y / (1 - y)) '' Set.Ioo (0 : ℝ) 1 = Set.Ioi (0 : ℝ) := by
  ext t
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact div_pos hy.1 (sub_pos.mpr hy.2)
  · intro ht
    refine ⟨t / (1 + t), ?_, ?_⟩
    · constructor
      · exact div_pos ht (add_pos zero_lt_one ht)
      · exact (div_lt_one (add_pos zero_lt_one ht)).mpr (by linarith)
    · have hden : 1 + t ≠ 0 := ne_of_gt (add_pos zero_lt_one ht)
      field_simp [hden]
      ring

private theorem fracMap_monoOn :
    MonotoneOn (fun y : ℝ => y / (1 - y)) (Set.Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hxden : 0 < 1 - x := sub_pos.mpr hx.2
  have hyden : 0 < 1 - y := sub_pos.mpr hy.2
  rw [div_le_div_iff₀ hxden hyden]
  nlinarith

private def fracDeriv (y : ℝ) : ℝ :=
  (1 * (1 - y) - y * (0 - 1)) / (1 - y) ^ 2

private theorem fracMap_hasDerivWithinAt :
    ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun y : ℝ => y / (1 - y)) (fracDeriv y)
        (Set.Ioo (0 : ℝ) 1) y := by
  intro y hy
  have hden : 1 - y ≠ 0 := by linarith [hy.2]
  simpa [fracDeriv] using
    (((hasDerivAt_id y).div
      ((hasDerivAt_const (c := (1 : ℝ)) y).sub (hasDerivAt_id y)) hden).hasDerivWithinAt)

private theorem fracIntegrand_point {q y : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    (1 - y) ^ (-2 : ℝ) * Real.rpowIntegrand₀₁ q (y / (1 - y)) 1 =
      y ^ (q - 1) * (1 - y) ^ (-q) := by
  have hy0 : 0 < y := hy.1
  have hy1 : y < 1 := hy.2
  have hdenpos : 0 < 1 - y := sub_pos.mpr hy1
  have hfrac_nonneg : 0 ≤ y / (1 - y) := le_of_lt (div_pos hy0 hdenpos)
  rw [Real.rpowIntegrand₀₁_eq_pow_div hq hfrac_nonneg zero_le_one]
  have hfracpow : (y / (1 - y)) ^ (q - 1) =
      y ^ (q - 1) / (1 - y) ^ (q - 1) := by
    rw [Real.div_rpow hy0.le hdenpos.le]
  rw [hfracpow]
  change (1 - y) ^ (-(2 : ℝ)) *
      (y ^ (q - 1) / (1 - y) ^ (q - 1) * 1 / (y / (1 - y) + 1)) =
    y ^ (q - 1) * (1 - y) ^ (-q)
  rw [Real.rpow_neg hdenpos.le 2]
  field_simp [ne_of_gt hdenpos]
  have hyadd : y + (1 - y) = 1 := by ring
  rw [hyadd, mul_one]
  symm
  change (1 - y) ^ (2 : ℝ) * (1 - y) ^ (q - 1) * (1 - y) ^ (-q) = 1 - y
  rw [← Real.rpow_add hdenpos]
  rw [← Real.rpow_add hdenpos]
  have hsum : (2 : ℝ) + (q - 1) + -q = 1 := by ring
  rw [hsum, Real.rpow_one]

private theorem rpowIntegrandIntegral_eq_betaReal {q : ℝ}
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ t in Set.Ioi (0 : ℝ), Real.rpowIntegrand₀₁ q t 1) =
      ∫ y in Set.Ioo (0 : ℝ) 1, y ^ (q - 1) * (1 - y) ^ (-q) := by
  rw [← fracMap_image_Ioo]
  rw [MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
    (s := Set.Ioo (0 : ℝ) 1) (f := fun y : ℝ => y / (1 - y))
    (f' := fracDeriv) measurableSet_Ioo fracMap_hasDerivWithinAt fracMap_monoOn]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo ?_
  intro y hy
  have hdenpos : 0 < 1 - y := sub_pos.mpr hy.2
  have hderiv_eq : fracDeriv y = (1 - y) ^ (-2 : ℝ) := by
    calc
      fracDeriv y = 1 / (1 - y) ^ 2 := by
        dsimp [fracDeriv]
        ring
      _ = ((1 - y) ^ 2)⁻¹ := by rw [one_div]
      _ = (1 - y) ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg hdenpos.le 2]
        simp
  change fracDeriv y * Real.rpowIntegrand₀₁ q (y / (1 - y)) 1 =
    y ^ (q - 1) * (1 - y) ^ (-q)
  rw [hderiv_eq]
  exact fracIntegrand_point hq hy

private theorem rpowIntegrandIntegral_closed {q : ℝ}
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ t in Set.Ioi (0 : ℝ), Real.rpowIntegrand₀₁ q t 1) =
      Real.pi / Real.sin (Real.pi * q) := by
  rw [rpowIntegrandIntegral_eq_betaReal hq, betaRealIntegral hq]
  rw [Complex.betaIntegral_eq_Gamma_mul_div (q : ℂ) (1 - q : ℂ)]
  · rw [show ((q : ℂ) + (1 - q : ℂ)) = 1 by norm_num]
    rw [Complex.Gamma_one, div_one, Complex.Gamma_ofReal q]
    rw [show (1 - (q : ℂ)) = ((1 - q : ℝ) : ℂ) by norm_num,
      Complex.Gamma_ofReal (1 - q)]
    norm_num
    rw [Real.Gamma_mul_Gamma_one_sub]
  · simpa using hq.1
  · simpa using sub_pos.mpr hq.2

private theorem sinCoeff_mul_rpowIntegrand_const {p : ℝ}
    (hp : p ∈ Set.Ioo (1 : ℝ) 2) :
    sinCoeff p *
      ∫ t in Set.Ioi (0 : ℝ), Real.rpowIntegrand₀₁ (p - 1) t 1 = 1 := by
  have hq : p - 1 ∈ Set.Ioo (0 : ℝ) 1 := sub_one_mem_Ioo hp
  rw [rpowIntegrandIntegral_closed hq]
  have hsinpos : 0 < Real.sin (Real.pi * (p - 1)) := by
    have hangle0 : 0 < Real.pi * (p - 1) := mul_pos Real.pi_pos hq.1
    have hangle1 : Real.pi * (p - 1) < Real.pi := by
      simpa using (mul_lt_mul_of_pos_left hq.2 Real.pi_pos)
    exact Real.sin_pos_of_mem_Ioo ⟨hangle0, hangle1⟩
  have hsin_eq : Real.sin ((p - 1) * Real.pi) = Real.sin (Real.pi * (p - 1)) := by
    rw [mul_comm]
  dsimp [sinCoeff]
  rw [hsin_eq]
  field_simp [Real.pi_ne_zero, ne_of_gt hsinpos]

private theorem rpowIntegrand_integral_eq_const_mul_rpow {p x : ℝ}
    (hp : p ∈ Set.Ioo (1 : ℝ) 2) (hx : 0 ≤ x) :
    ∫ t in Set.Ioi (0 : ℝ), x * Real.rpowIntegrand₀₁ (p - 1) t x =
      (∫ t in Set.Ioi (0 : ℝ), Real.rpowIntegrand₀₁ (p - 1) t 1) * x ^ p := by
  rw [MeasureTheory.integral_const_mul]
  rw [Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const (sub_one_mem_Ioo hp) hx]
  have hpow : x * x ^ (p - 1) = x ^ p := by
    rcases eq_or_lt_of_le hx with rfl | hxpos
    · have hp_pos : 0 < p := by linarith [hp.1]
      simp [Real.zero_rpow hp_pos.ne']
    · calc
        x * x ^ (p - 1) = x ^ (1 : ℝ) * x ^ (p - 1) := by rw [Real.rpow_one]
        _ = x ^ (1 + (p - 1)) := by rw [Real.rpow_add hxpos]
        _ = x ^ p := by ring_nf
  rw [← mul_assoc, hpow]
  ring

/-- The scalar truncated approximation `f_n` converges to `x^p` for `1 < p < 2`
and `0 ≤ x`.
Source: Hiai, proof of Theorem 6.3. -/
theorem powerApprox_tendsto_rpow {p x : ℝ} (hp : p ∈ Set.Ioo (1 : ℝ) 2)
    (hx : 0 ≤ x) :
    Filter.Tendsto (fun k : ℕ => powerApprox p k x) Filter.atTop (𝓝 (x ^ p)) := by
  have hbase := rpowIntegrand_cutoff_tendsto hp hx
  have hscaled :
      Filter.Tendsto
        (fun k : ℕ =>
          sinCoeff p *
            ∫ t in cutoffSet k, x * Real.rpowIntegrand₀₁ (p - 1) t x)
        Filter.atTop
        (𝓝 (sinCoeff p *
          ∫ t in Set.Ioi (0 : ℝ), x * Real.rpowIntegrand₀₁ (p - 1) t x)) :=
    tendsto_const_nhds.mul hbase
  have hmain :=
    hscaled.congr' (Filter.Eventually.of_forall fun k =>
      (powerApprox_eq_setIntegral_rpowIntegrand hp k hx).symm)
  have hlim :
      sinCoeff p *
          ∫ t in Set.Ioi (0 : ℝ), x * Real.rpowIntegrand₀₁ (p - 1) t x =
        x ^ p := by
    rw [rpowIntegrand_integral_eq_const_mul_rpow hp hx]
    calc
      sinCoeff p *
          ((∫ t in Set.Ioi (0 : ℝ), Real.rpowIntegrand₀₁ (p - 1) t 1) * x ^ p)
          = (sinCoeff p *
              ∫ t in Set.Ioi (0 : ℝ), Real.rpowIntegrand₀₁ (p - 1) t 1) * x ^ p := by ring
      _ = x ^ p := by rw [sinCoeff_mul_rpowIntegrand_const hp, one_mul]
  simpa [hlim] using hmain

end ScalarApproximation

end TraceMonotonicity

end HiaiPetz
