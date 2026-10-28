import Quantum.TraceInequality.Loewner.Koranyi.DyadicCover

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


namespace Quantum.TraceInequality.Loewner

noncomputable section

/-!
Step 48 (utility): algebraic identities for the support-elimination transform.

These are elementary identities that are convenient when rewriting Stieltjes-type kernels
after an inversion change of variables.
-/

section

/-- A nonreal complex number cannot equal a real scalar. -/
lemma complex_sub_ne_of_im_ne_zero (r : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (r : ℂ) - z ≠ 0 := by
  intro h
  have : ((r : ℂ) - z).im = 0 := congrArg Complex.im h
  have h_im : -z.im = 0 := by
    simpa using this
  exact hz (neg_eq_zero.mp h_im)

/-- Algebraic kernel rewrite used after evaluation at an inverse point. -/
lemma neg_inv_mul_one_div_sub_eq_one_div_one_sub_mul {x t : ℂ} (hx : x ≠ 0) :
    (-(1 / x)) * (1 / (t - (1 / x))) = (1 / (1 - x * t)) := by
  by_cases ht : (t - (1 / x)) = 0
  · have ht' : t = 1 / x := sub_eq_zero.mp ht
    simp [ht', hx]
  · have hden : (1 - x * t) ≠ 0 := by
      intro hden
      have hxteq : x * t = (1 : ℂ) := (sub_eq_zero.mp hden).symm
      have ht' : t = 1 / x := by
        calc
          t = x⁻¹ * (x * t) := by
                simpa [mul_assoc] using (inv_mul_cancel_left₀ hx t).symm
          _ = x⁻¹ * 1 := by simp [hxteq]
          _ = 1 / x := by simp [div_eq_mul_inv]
      exact ht (by simp [ht'])
    field_simp [hx, ht, hden]
    have hden' : x * t - 1 ≠ 0 := by
      intro h0
      apply hden
      have : - (1 - x * t) = 0 := by
        calc
          - (1 - x * t) = x * t - 1 := by ring
          _ = 0 := h0
      simpa using (neg_eq_zero.mp this)
    have hrel : - (1 - x * t) = x * t - 1 := by ring
    calc
      -((1 - x * t) / (x * t - 1)) = -((1 - x * t) * (x * t - 1)⁻¹) := by
          simp [div_eq_mul_inv]
      _ = (- (1 - x * t)) * (x * t - 1)⁻¹ := by
            simpa using (neg_mul (1 - x * t) ((x * t - 1)⁻¹)).symm
      _ = (x * t - 1) * (x * t - 1)⁻¹ := by
            simp [hrel]
      _ = 1 := by simp [hden']

/-- Points outside `[-1, 1]` have absolute value at least one. -/
theorem one_le_abs_of_mem_Icc_compl {y : ℝ}
    (hy : y ∈ (Set.Icc (-1 : ℝ) 1)ᶜ) :
    (1 : ℝ) ≤ |y| := by
  have hnot : ¬ ((-1 : ℝ) ≤ y ∧ y ≤ 1) := by
    simpa [Set.mem_Icc] using hy
  by_cases hle : y ≤ 1
  · have hylt : y < -1 := by
      by_contra hneg
      have hge : (-1 : ℝ) ≤ y := le_of_not_gt hneg
      exact hnot ⟨hge, hle⟩
    have habs : |y| = -y := abs_of_neg (by linarith)
    rw [habs]
    linarith
  · have hygt : 1 < y := lt_of_not_ge hle
    have habs : |y| = y := abs_of_nonneg (by linarith)
    rw [habs]
    linarith

/-- The inverse-square density is the inverse-square distance kernel at zero. -/
theorem ofReal_inv_sq_eq_sqInvDist_zero {y : ℝ} (hy : y ≠ 0) :
    ENNReal.ofReal ((y ^ (2 : ℕ))⁻¹) =
      _root_.Quantum.TraceInequality.Loewner.sqInvDist (0 : ℝ) y := by
  have hpos : 0 < |y| := abs_pos.mpr hy
  have hnonneg_inv : 0 ≤ |y|⁻¹ := inv_nonneg.mpr hpos.le
  have hreal : (y ^ (2 : ℕ))⁻¹ = |y|⁻¹ ^ (2 : ℕ) := by
    rw [← inv_pow]
    calc
      y⁻¹ ^ (2 : ℕ) = |y⁻¹| ^ (2 : ℕ) := by rw [sq_abs]
      _ = |y|⁻¹ ^ (2 : ℕ) := by rw [abs_inv]
  calc
    ENNReal.ofReal ((y ^ (2 : ℕ))⁻¹) =
        ENNReal.ofReal (|y|⁻¹ ^ (2 : ℕ)) := by rw [hreal]
    _ = (ENNReal.ofReal |y|⁻¹) ^ (2 : ℕ) := by
          rw [ENNReal.ofReal_pow hnonneg_inv]
    _ = ((ENNReal.ofReal |y|)⁻¹) ^ (2 : ℕ) := by
          rw [ENNReal.ofReal_inv_of_pos hpos]
    _ = _root_.Quantum.TraceInequality.Loewner.sqInvDist (0 : ℝ) y := by
          simp [_root_.Quantum.TraceInequality.Loewner.sqInvDist]

section

variable (x y : ℝ)

/-- The elementary identity `1/(y - x) - 1/y = x/(y(y - x))`. -/
lemma one_div_sub_one_div_eq (hy0 : y ≠ 0) (hyx : y ≠ x) :
    (1 / (y - x) : ℝ) - 1 / y = x / (y * (y - x)) := by
  field_simp [hy0, sub_ne_zero.mpr hyx]
  ring

/-- Rewriting `1/(y - x) - 1/y` after the inversion change of variables: it equals
`(x/(1 + (-y⁻¹)x)) · (y²)⁻¹`. -/
lemma one_div_sub_one_div_eq_mul_inv_sq
    (hy0 : y ≠ 0) (hyx : y ≠ x) :
    (1 / (y - x) : ℝ) - 1 / y = (x / (1 + (-y⁻¹) * x)) * (y ^ (2 : ℕ))⁻¹ := by
  have hyx' : y - x ≠ 0 := sub_ne_zero.mpr hyx
  -- Start from the basic identity and rewrite the denominator.
  calc
    (1 / (y - x) : ℝ) - 1 / y = x / (y * (y - x)) :=
      one_div_sub_one_div_eq (x := x) (y := y) hy0 hyx
    _ = x / (y * (y * (1 + (-y⁻¹) * x))) := by
          -- `y - x = y * (1 - x/y) = y * (1 + (-1/y)*x)`.
          have : y - x = y * (1 + (-y⁻¹) * x) := by
            field_simp [hy0]
            ring
          simp [this]
    _ = x / (y ^ (2 : ℕ) * (1 + (-y⁻¹) * x)) := by
          simp [pow_two, mul_assoc, mul_comm]
    _ = (x / (1 + (-y⁻¹) * x)) * (y ^ (2 : ℕ))⁻¹ := by
          field_simp [hy0]

end

end

end

end Quantum.TraceInequality.Loewner
