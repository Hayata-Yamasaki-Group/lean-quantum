import Quantum.TraceInequality.Loewner.Koranyi.SupportElimFromPosDef
import Quantum.TraceInequality.Loewner.Koranyi.SupportElimKoranyiKernel

import Mathlib.Algebra.Order.Field.Basic


namespace Quantum.TraceInequality.Loewner

open scoped ComplexOrder
open scoped MatrixOrder
open scoped Topology
open scoped UpperHalfPlane

open Set MeasureTheory Filter

noncomputable section

/-!
Step 60 (bridge): turn a global `PosDef` hypothesis (for all finite point families) into the
`y : ∀ n, Fin (n+1) → ℝ` form required by Step 58/59, by choosing an explicit point family.
-/

/-- Canonical finite point family `i / (n + 2)` used to instantiate global positivity. -/
def canonicalPoints (n : ℕ) : Fin (n + 1) → ℝ :=
  fun i => (i.1 : ℝ) / ((n + 2 : ℕ) : ℝ)

/-- The canonical point family is admissible for the finite Koranyi construction. -/
lemma pointsHyp_canonicalPoints (n : ℕ) : pointsHyp (n := n) (canonicalPoints n) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [canonicalPoints]
  · intro i j hij
    apply Fin.ext
    set d : ℝ := ((n + 2 : ℕ) : ℝ)
    have hd : d ≠ 0 := by
      dsimp [d]
      exact_mod_cast (Nat.succ_ne_zero (n + 1))
    have hij' : (i.1 : ℝ) = (j.1 : ℝ) := by
      -- Clear the denominator by multiplying both sides.
      have hijmul := congrArg (fun x => x * d) hij
      have hijmul' : (i.1 : ℝ) = (j.1 : ℝ) ∨ d = 0 := by
        simpa [canonicalPoints, d, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hijmul
      rcases hijmul' with h | h
      · exact h
      · exfalso
        exact hd h
    exact_mod_cast hij'
  · intro i
    have hd0 : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
    have hnum0 : 0 ≤ (i.1 : ℝ) := by exact_mod_cast (Nat.zero_le _)
    have hge0 : 0 ≤ canonicalPoints n i := by
      exact div_nonneg hnum0 (le_of_lt hd0)
    have hlt1 : canonicalPoints n i < 1 := by
      have hlt : (i.1 : ℝ) < ((n + 2 : ℕ) : ℝ) := by
        have hi : i.1 < n + 1 := i.2
        have : i.1 < n + 2 := lt_trans hi (Nat.lt_succ_self (n + 1))
        exact_mod_cast this
      -- `a / d < 1` is equivalent to `a < d` when `d > 0`.
      exact (div_lt_one hd0).2 (by simpa using hlt)
    have hgtm1 : (-1 : ℝ) < canonicalPoints n i := lt_of_lt_of_le (by linarith) hge0
    exact ⟨hgtm1, hlt1⟩
  · intro i hi0
    have hival : i.1 ≠ 0 := by
      intro h0
      apply hi0
      apply Fin.ext
      simp [h0]
    have hd : ((n + 2 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero (n + 1))
    have hnum : (i.1 : ℝ) ≠ 0 := by
      exact_mod_cast hival
    exact div_ne_zero hnum hd

/-- Canonical points instantiate the full support-elimination and Stieltjes-difference package. -/
theorem exists_subseq_supportElim_stieltjesDiff_full_of_global_loewnerMatrix_posDef_canonicalPoints
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef) :
    Nonempty (Loewner.StrictApproxFullPackage f) := by
  let y : ∀ n : ℕ, Fin (n + 1) → ℝ := fun n => canonicalPoints n
  have hy : ∀ n : ℕ, pointsHyp (n := n) (y n) := by
    intro n
    simpa [y] using pointsHyp_canonicalPoints n
  have hL' : ∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef := by
    intro n
    exact hL n (y n) (hy n)
  simpa [y] using
    exists_subseq_supportElim_stieltjesDiff_full_of_loewnerMatrix_posDef (f := f) (y := y) hy hL'

/-- Canonical points instantiate the Koranyi-kernel support-elimination limit package. -/
theorem
exists_subseq_koranyiKernel_supportElim_with_tendsto_of_global_loewnerMatrix_posDef_canonicalPoints
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef) :
    Nonempty (Loewner.KoranyiLimitPackage f) := by
  let y : ∀ n : ℕ, Fin (n + 1) → ℝ := fun n => canonicalPoints n
  have hy : ∀ n : ℕ, pointsHyp (n := n) (y n) := by
    intro n
    simpa [y] using pointsHyp_canonicalPoints n
  have hL' : ∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef := by
    intro n
    exact hL n (y n) (hy n)
  simpa [y] using
    exists_subseq_koranyiKernel_supportElim_with_tendsto_of_loewnerMatrix_posDef
      (f := f) (y := y) hy hL'

end

end Quantum.TraceInequality.Loewner
