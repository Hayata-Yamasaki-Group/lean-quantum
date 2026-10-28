import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

namespace Quantum.TraceInequality.Loewner

noncomputable section

/-!
Step 34 (utility): dyadic grid approximation on `[-1,1]`.

This is a basic geometric ingredient used in the "support elimination" route: every point in `ℝ`
can be approximated by a dyadic rational with denominator `2^m`, with an explicit error bound.
-/

/-- Every real number has a dyadic approximation with error at most `2^{-m}`. -/
theorem exists_int_abs_sub_le_div_pow_two (m : ℕ) (y : ℝ) :
    ∃ k : ℤ, |y - (k : ℝ) / ((2 : ℝ) ^ m)| ≤ 1 / ((2 : ℝ) ^ m) := by
  classical
  let d : ℝ := (2 : ℝ) ^ m
  have hdpos : 0 < d := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    simp [d]
  have hdne : d ≠ 0 := ne_of_gt hdpos
  let a : ℝ := y * d
  let k : ℤ := Int.floor a
  refine ⟨k, ?_⟩
  have hk0 : (k : ℝ) ≤ a := by
    simpa [k] using (Int.floor_le a)
  have hk1 : a < (k : ℝ) + 1 := by
    simp [k]
  have hk_div : (k : ℝ) / d ≤ y := by
    -- `k ≤ y*d` implies `k/d ≤ y`.
    have : (k : ℝ) ≤ y * d := by
      simpa [a] using hk0
    have := mul_le_mul_of_nonneg_right this (le_of_lt (inv_pos.2 hdpos))
    -- simplify `(y * d) * d⁻¹ = y`
    simpa [div_eq_mul_inv, mul_assoc, hdne] using this
  have hy_lt : y < ((k : ℝ) + 1) / d := by
    have : y * d < (k : ℝ) + 1 := by
      simpa [a] using hk1
    have := mul_lt_mul_of_pos_right this (inv_pos.2 hdpos)
    simpa [div_eq_mul_inv, mul_assoc, hdne] using this
  have hdiff0 : 0 ≤ y - (k : ℝ) / d := sub_nonneg.mpr hk_div
  have hdiff_lt : y - (k : ℝ) / d < 1 / d := by
    have hsub :
        y - (k : ℝ) / d < (((k : ℝ) + 1) / d) - (k : ℝ) / d :=
      sub_lt_sub_right hy_lt ((k : ℝ) / d)
    have hright : (((k : ℝ) + 1) / d) - (k : ℝ) / d = 1 / d := by
      field_simp [hdne]
      ring
    simpa [hright, d] using hsub
  have hdiff_le : y - (k : ℝ) / d ≤ 1 / d := le_of_lt hdiff_lt
  -- Since the difference is nonnegative, `abs` can be removed.
  simpa [d, abs_of_nonneg hdiff0] using hdiff_le

end

end Quantum.TraceInequality.Loewner
