import Quantum.TraceInequality.Loewner.Koranyi.DyadicCover

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set

noncomputable section

open scoped NNReal

/-!
Step 42 (utility): simple bounds for the dyadic cover constants from Step 41.

These lemmas are used to simplify the prefactor

`(dyadicCenters m).card * (dyadicRadius m)^2`

appearing in Step 41, by bounding the cardinality in a way that is convenient for later
limit arguments.
-/

/-- The dyadic center count is bounded by the simpler power `2^(m+3)`. -/
lemma dyadicCenters_card_le_pow (m : ℕ) :
    (dyadicCenters m).card ≤ (2 : ℕ) ^ (m + 3) := by
  have hcard : (dyadicCenters m).card = (2 : ℕ) ^ (m + 2) + 1 :=
    dyadicCenters_card_nat (m := m)
  -- `2^(m+2) + 1 ≤ 2^(m+2) + 2^(m+2) = 2^(m+3)`.
  have hone : (1 : ℕ) ≤ (2 : ℕ) ^ (m + 2) := by
    simpa using (Nat.one_le_pow (n := m + 2) (m := 2) (by decide : 0 < (2 : ℕ)))
  have hle :
      (2 : ℕ) ^ (m + 2) + 1 ≤ (2 : ℕ) ^ (m + 2) + (2 : ℕ) ^ (m + 2) :=
    by
      -- `add_le_add_left` gives `1 + a ≤ a + a`; commute the left sum.
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_left hone ((2 : ℕ) ^ (m + 2)))
  -- Rewrite the right-hand side as `2^(m+3)`.
  have hpow :
      (2 : ℕ) ^ (m + 2) + (2 : ℕ) ^ (m + 2) = (2 : ℕ) ^ (m + 3) := by
    -- `a + a = a * 2` and `2^(m+3) = 2^(m+2) * 2`.
    calc
      (2 : ℕ) ^ (m + 2) + (2 : ℕ) ^ (m + 2) = (2 : ℕ) ^ (m + 2) * 2 := by
          simp [Nat.mul_two]
      _ = (2 : ℕ) ^ (m + 3) := by
          simp [pow_succ, Nat.mul_assoc]
  -- Conclude.
  simpa [hcard, hpow] using hle

/--
The Step 41 mass bound with the dyadic center count replaced by `2^(m+3)`.
-/
theorem measure_Icc_le_pow_mul_lintegral_sqInvDist_of_uniform_bound (μ : Measure ℝ) (m : ℕ)
    (K : ENNReal)
    (hK :
      ∀ k ∈ dyadicCenters m, (∫⁻ y, sqInvDist (dyadicCenter m k) y ∂μ) ≤ K) :
    μ (Set.Icc (-1 : ℝ) 1) ≤
      ((2 : ℕ) ^ (m + 3) : ENNReal) * ((ENNReal.ofReal (dyadicRadius m)) ^ (2 : ℕ)) * K := by
  have h41 :=
    measure_Icc_le_mul_lintegral_sqInvDist_of_uniform_bound (μ := μ) (m := m) (K := K) hK
  have hcard_le : (dyadicCenters m).card ≤ (2 : ℕ) ^ (m + 3) :=
    dyadicCenters_card_le_pow (m := m)
  have hcard_le' : ((dyadicCenters m).card : ENNReal) ≤ ((2 : ℕ) ^ (m + 3) : ENNReal) := by
    exact_mod_cast hcard_le
  -- Enlarge the prefactor by monotonicity.
  have hpref :
      (dyadicCenters m).card * ((ENNReal.ofReal (dyadicRadius m)) ^ (2 : ℕ)) * K ≤
        ((2 : ℕ) ^ (m + 3) : ENNReal) * ((ENNReal.ofReal (dyadicRadius m)) ^ (2 : ℕ)) * K := by
    gcongr
  exact h41.trans hpref

end

end Quantum.TraceInequality.Loewner
