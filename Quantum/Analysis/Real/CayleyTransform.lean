import Mathlib.Tactic

namespace Quantum.TraceInequality.Loewner

open Set

noncomputable section

/-!
Step 12 (utility): Cayley transform between `(-1,1)` and `(0,∞)`.

We use the standard change of variables

* `cayley x = (1 + x) / (1 - x)` mapping `x ∈ (-1,1)` to `(0,∞)`,
* `invCayley y = (y - 1) / (y + 1)` mapping `y ∈ (0,∞)` back to `(-1,1)`.
-/

/-- The Cayley transform from `(-1,1)` to `(0,∞)`. -/
def cayley (x : ℝ) : ℝ :=
  (1 + x) / (1 - x)

/-- The inverse Cayley transform from `(0,∞)` to `(-1,1)`. -/
def invCayley (y : ℝ) : ℝ :=
  (y - 1) / (y + 1)

/-- Definitional rewrite for the Cayley transform. -/
@[simp] lemma cayley_def (x : ℝ) : cayley x = (1 + x) / (1 - x) := rfl
/-- Definitional rewrite for the inverse Cayley transform. -/
@[simp] lemma invCayley_def (y : ℝ) : invCayley y = (y - 1) / (y + 1) := rfl

/-- The Cayley transform sends points of `(-1,1)` to positive real numbers. -/
lemma cayley_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    0 < cayley x := by
  have hx1 : x < 1 := hx.2
  have hx2 : -1 < x := hx.1
  have hpos_num : 0 < 1 + x := by linarith
  have hpos_den : 0 < 1 - x := by linarith
  have : 0 < (1 + x) / (1 - x) := div_pos hpos_num hpos_den
  simpa [cayley] using this

/-- The inverse Cayley transform sends positive real numbers into `(-1,1)`. -/
lemma invCayley_mem_Ioo_of_pos {y : ℝ} (hy : 0 < y) :
    invCayley y ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hy1 : 0 < y + 1 := by linarith
  constructor
  · -- `-1 < (y - 1)/(y + 1)`
    have : (-1 : ℝ) < (y - 1) / (y + 1) := by
      have hmul : (-1 : ℝ) * (y + 1) < (y - 1) := by
        -- `-(y+1) < y-1` ⇔ `0 < 2*y`.
        nlinarith
      -- `a < b/c` with `c>0` ↔ `a*c < b`.
      exact (lt_div_iff₀ hy1).2 hmul
    simpa [invCayley] using this
  · -- `(y - 1)/(y + 1) < 1`
    have : (y - 1) / (y + 1) < (1 : ℝ) := by
      have hmul : y - 1 < (1 : ℝ) * (y + 1) := by nlinarith
      exact (div_lt_iff₀ hy1).2 hmul
    simpa [invCayley] using this

/-- The inverse Cayley transform is a left inverse of `cayley` away from `1`. -/
lemma invCayley_cayley {x : ℝ} (hx : x ≠ 1) :
    invCayley (cayley x) = x := by
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr hx.symm
  unfold invCayley cayley
  field_simp [hden]
  ring

/-- The Cayley transform is a left inverse of `invCayley` away from `-1`. -/
lemma cayley_invCayley {y : ℝ} (hy : y ≠ -1) :
    cayley (invCayley y) = y := by
  have hden : y + 1 ≠ 0 := by
    intro h
    apply hy
    -- `y + 1 = 0` implies `y = -1`.
    simpa using (add_eq_zero_iff_eq_neg.1 h)
  unfold invCayley cayley
  field_simp [hden, hy]
  ring

end

end Quantum.TraceInequality.Loewner
