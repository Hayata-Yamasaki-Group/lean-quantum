import Quantum.TraceInequality.Loewner.Kernel.FiniteMatrixData


namespace Quantum.TraceInequality.Loewner

open Set

open scoped BigOperators

noncomputable section

/-!
Step 60 (variant): an explicit point family in `(-1,1)` containing both positive and negative
entries.

This is used to instantiate the "for_points" global packages while avoiding the weakness of the
canonical points (which lie in `[0,1)` only).
-/

/-- Signed grid points `± k/(n+2)` (with alternating sign), in `(-1,1)` and with `0` at
index `0`. -/
def signedPoints (n : ℕ) : Fin (n + 1) → ℝ :=
  fun i => ((-1 : ℝ) ^ (i.1) * (i.1 : ℝ)) / ((n + 2 : ℕ) : ℝ)

@[simp] lemma signedPoints_zero (n : ℕ) : signedPoints n 0 = 0 := by
  simp [signedPoints]

private lemma abs_signedPoints (n : ℕ) (i : Fin (n + 1)) :
    |signedPoints n i| = (i.1 : ℝ) / ((n + 2 : ℕ) : ℝ) := by
  have hnpos : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
  have hden_abs : |((n + 2 : ℕ) : ℝ)| = ((n + 2 : ℕ) : ℝ) := by
    simpa using (abs_of_nonneg (le_of_lt hnpos))
  have habs_pow : |((-1 : ℝ) ^ (i.1))| = 1 := by
    simp
  have habs_mul : |((-1 : ℝ) ^ (i.1) * (i.1 : ℝ))| = |(i.1 : ℝ)| := by
    calc
      |((-1 : ℝ) ^ (i.1) * (i.1 : ℝ))| = |((-1 : ℝ) ^ (i.1))| * |(i.1 : ℝ)| := by
        simp [abs_mul]
      _ = 1 * |(i.1 : ℝ)| := by simp [habs_pow]
      _ = |(i.1 : ℝ)| := by simp
  have hi0 : 0 ≤ (i.1 : ℝ) := by exact_mod_cast (Nat.zero_le i.1)
  have habs_i : |(i.1 : ℝ)| = (i.1 : ℝ) := abs_of_nonneg hi0
  -- Combine.
  have hden : ((n + 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (n + 1))
  calc
    |signedPoints n i|
        = |((-1 : ℝ) ^ (i.1) * (i.1 : ℝ)) / ((n + 2 : ℕ) : ℝ)| := by
            simp [signedPoints]
    _ = |((-1 : ℝ) ^ (i.1) * (i.1 : ℝ))| / |((n + 2 : ℕ) : ℝ)| := by
          simp [abs_div]
    _ = |((-1 : ℝ) ^ (i.1) * (i.1 : ℝ))| / ((n + 2 : ℕ) : ℝ) := by
          rw [hden_abs]
    _ = |(i.1 : ℝ)| / ((n + 2 : ℕ) : ℝ) := by simp [habs_mul]
    _ = (i.1 : ℝ) / ((n + 2 : ℕ) : ℝ) := by simp [habs_i]

/-- The signed grid points `± k/(n+2)` satisfy the interpolation-point hypothesis `pointsHyp`:
distinct points in `(-1, 1)` with `0` at index `0`. -/
lemma pointsHyp_signedPoints (n : ℕ) : pointsHyp (n := n) (signedPoints n) := by
  classical
  refine ⟨signedPoints_zero n, ?_, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    set d : ℝ := ((n + 2 : ℕ) : ℝ)
    have hd : d ≠ 0 := by
      dsimp [d]
      exact_mod_cast (Nat.succ_ne_zero (n + 1))
    have habs : |signedPoints n i| = |signedPoints n j| := by
      simpa using congrArg abs hij
    have habs' : (i.1 : ℝ) / d = (j.1 : ℝ) / d := by
      simpa [abs_signedPoints, d] using habs
    have hij_nat : (i.1 : ℝ) = (j.1 : ℝ) := by
      have habs'' := habs'
      field_simp [d, hd] at habs''
      exact habs''
    exact_mod_cast hij_nat
  · intro i
    -- Use `|signedPoints n i| < 1`.
    have hnpos : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
    have hlt : (i.1 : ℝ) < ((n + 2 : ℕ) : ℝ) := by
      have hi : i.1 < n + 1 := i.2
      have : i.1 < n + 2 := lt_trans hi (Nat.lt_succ_self (n + 1))
      exact_mod_cast this
    have habs_lt : |signedPoints n i| < 1 := by
      have habs_eq := abs_signedPoints n i
      -- Reduce to `i/(n+2) < 1`.
      have : (i.1 : ℝ) / ((n + 2 : ℕ) : ℝ) < 1 := (div_lt_one hnpos).2 hlt
      simpa [habs_eq] using this
    have : - (1 : ℝ) < signedPoints n i ∧ signedPoints n i < 1 := by
      simpa [abs_lt] using habs_lt
    exact this
  · intro i hi0
    have hd : ((n + 2 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero (n + 1))
    have hival : i.1 ≠ 0 := by
      intro h0
      apply hi0
      apply Fin.ext
      simp [h0]
    have hnum : ((-1 : ℝ) ^ (i.1) * (i.1 : ℝ)) ≠ 0 := by
      have hiC : (i.1 : ℝ) ≠ 0 := by exact_mod_cast hival
      exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)) hiC
    exact div_ne_zero hnum hd

end

end Quantum.TraceInequality.Loewner
