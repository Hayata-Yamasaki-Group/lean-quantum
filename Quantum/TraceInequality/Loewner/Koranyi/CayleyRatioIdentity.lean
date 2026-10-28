import Quantum.Analysis.Real.CayleyTransform

namespace Quantum.TraceInequality.Loewner

open Set

noncomputable section

/-!
Step 15 (utility): an algebraic identity relating the ratio kernel on `(0,∞)` to the
Korányi-type kernel on `(-1,1)` via the Cayley transform.

This is intended as a bridge between the `ENNReal` ratio-kernel route and the finite-step
construction on `(-1,1)`.
-/

/-- Algebraic Cayley identity converting the ratio kernel to the Koranyi kernel. -/
lemma cayley_div_cayley_add_cayley_eq (x t : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    cayley x / (cayley x + cayley t) = ((1 + x) * (1 - t)) / (2 * (1 - x * t)) := by
  have hxden : 1 - x ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr hx.2)
  have htden : 1 - t ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr ht.2)
  unfold cayley
  calc
    (1 + x) / (1 - x) / ((1 + x) / (1 - x) + (1 + t) / (1 - t)) =
        ((1 + x) * (1 - t)) / ((1 + x) * (1 - t) + (1 + t) * (1 - x)) := by
          field_simp [hxden, htden]
    _ = ((1 + x) * (1 - t)) / (2 * (1 - x * t)) := by
          have h :
              (1 + x) * (1 - t) + (1 + t) * (1 - x) = 2 * (1 - x * t) := by
            ring
          simp [h]

end

end Quantum.TraceInequality.Loewner
