import Quantum.TraceInequality.Loewner.Koranyi.DyadicCoverBounds

import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set

noncomputable section

/-!
Step 43 (utility): simplify the Step42 dyadic cover estimate.

This file rewrites the prefactor from Step42 into a more explicit `2^{-m}`-type decay:

`(2^(m+3)) * (dyadicRadius m)^2 = 8 * dyadicRadius m`.

It does not yet provide the *quadratic estimate* needed to bound the inverse-distance `lintegral`;
that estimate is handled in later steps.
-/

/-- The Step 42 dyadic prefactor simplifies to `8 * dyadicRadius m`. -/
lemma pow_mul_dyadicRadius_sq (m : ℕ) :
    ((2 : ℝ) ^ (m + 3)) * (dyadicRadius m) ^ (2 : ℕ) = 8 * dyadicRadius m := by
  -- This is a direct algebraic simplification using `dyadicRadius m = 1 / 2^m`.
  simp [dyadicRadius, one_div, pow_succ, mul_assoc, mul_comm]
  ring

/-- The dyadic prefactor identity after coercing the nonnegative terms to `ENNReal`. -/
lemma ennreal_prefactor_eq (m : ℕ) :
    ((2 : ℕ) ^ (m + 3) : ENNReal) * ((ENNReal.ofReal (dyadicRadius m)) ^ (2 : ℕ)) =
      ENNReal.ofReal (8 * dyadicRadius m) := by
  have hr : 0 ≤ dyadicRadius m := le_of_lt (dyadicRadius_pos m)
  have hpow : 0 ≤ (2 : ℝ) ^ (m + 3) := by positivity
  -- Convert the natural power to an `ofReal` and use `ofReal_mul`/`ofReal_pow`.
  calc
    ((2 : ℕ) ^ (m + 3) : ENNReal) * (ENNReal.ofReal (dyadicRadius m) ^ (2 : ℕ))
        = ENNReal.ofReal ((2 : ℝ) ^ (m + 3)) * ENNReal.ofReal (dyadicRadius m) ^ (2 : ℕ) := by
            simp
    _ = ENNReal.ofReal (((2 : ℝ) ^ (m + 3)) * (dyadicRadius m) ^ (2 : ℕ)) := by
          -- Use `ofReal_pow` then `ofReal_mul`.
          simp [ENNReal.ofReal_pow hr, ENNReal.ofReal_mul hpow]
    _ = ENNReal.ofReal (8 * dyadicRadius m) := by
          simp [pow_mul_dyadicRadius_sq (m := m)]

/-- A uniform inverse-square integral bound gives the simplified inside-mass bound. -/
theorem measure_Icc_le_of_uniform_sqInvDist_bound (μ : Measure ℝ) (m : ℕ) (K : ENNReal)
    (hK : ∀ k ∈ dyadicCenters m, (∫⁻ y, sqInvDist (dyadicCenter m k) y ∂μ) ≤ K) :
    μ (Set.Icc (-1 : ℝ) 1) ≤ ENNReal.ofReal (8 * dyadicRadius m) * K := by
  have h42 :
      μ (Set.Icc (-1 : ℝ) 1) ≤
        ((2 : ℕ) ^ (m + 3) : ENNReal) * ((ENNReal.ofReal (dyadicRadius m)) ^ (2 : ℕ)) * K :=
    measure_Icc_le_pow_mul_lintegral_sqInvDist_of_uniform_bound (μ := μ) (m := m) (K := K) hK
  have hpref :
      ((2 : ℕ) ^ (m + 3) : ENNReal) * (ENNReal.ofReal (dyadicRadius m) ^ (2 : ℕ)) =
        ENNReal.ofReal (8 * dyadicRadius m) := by
    simpa using (ennreal_prefactor_eq (m := m))
  -- Replace the prefactor (avoid `simp` re-associating products).
  have h42' :
      μ (Set.Icc (-1 : ℝ) 1) ≤
        (((2 : ℕ) ^ (m + 3) : ENNReal) * (ENNReal.ofReal (dyadicRadius m) ^ (2 : ℕ))) * K := by
    simpa [mul_assoc] using h42
  calc
    μ (Set.Icc (-1 : ℝ) 1) ≤
        (((2 : ℕ) ^ (m + 3) : ENNReal) * (ENNReal.ofReal (dyadicRadius m) ^ (2 : ℕ))) * K := h42'
    _ = ENNReal.ofReal (8 * dyadicRadius m) * K := by
          rw [hpref]

end

end Quantum.TraceInequality.Loewner
