import Mathlib.Tactic

namespace Quantum.TraceInequality.Loewner

noncomputable section

/-- Inverse Cayley map `(-1,1) → (0,∞)`. -/
def unitToPositiveCayley (y : ℝ) : ℝ :=
  (1 + y) / (1 - y)

/-- Pull back a positive-half-line function to the normalized interval. -/
def positiveCayleyPullback (h : ℝ → ℝ) : ℝ → ℝ :=
  fun y => h (unitToPositiveCayley y)

/-- The unit-to-positive Cayley map sends `(-1,1)` into `(0,∞)`. -/
theorem unitToPositiveCayley_mem_Ioi {y : ℝ}
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    unitToPositiveCayley y ∈ Set.Ioi (0 : ℝ) := by
  have hnum : 0 < 1 + y := by linarith [hy.1]
  have hden : 0 < 1 - y := by linarith [hy.2]
  exact div_pos hnum hden

end

end Quantum.TraceInequality.Loewner
