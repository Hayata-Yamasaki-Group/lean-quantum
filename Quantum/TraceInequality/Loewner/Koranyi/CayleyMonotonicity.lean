import Quantum.Analysis.Real.CayleyTransform
import Quantum.TraceInequality.Loewner.Koranyi.RatioFunctional

import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

namespace Quantum.TraceInequality.Loewner

open MeasureTheory
open Set

noncomputable section

/-!
Step 62 (utility): monotonicity facts for the Cayley transform and the ratio-functional.

This is a small helper step towards turning the `ENNReal` ratio-kernel representation into
monotonicity statements on `(-1,1)`.
-/

/-- The Cayley transform is strictly increasing on `(-1,1)`. -/
lemma strictMonoOn_cayley : StrictMonoOn cayley (Set.Ioo (-1 : ℝ) 1) := by
  intro x hx y hy hxy
  have hxden : 0 < (1 : ℝ) - x := by linarith [hx.2]
  have hyden : 0 < (1 : ℝ) - y := by linarith [hy.2]
  have hmul : (1 + x) * ((1 : ℝ) - y) < (1 + y) * ((1 : ℝ) - x) := by
    nlinarith
  have hdiv : (1 + x) / ((1 : ℝ) - x) < (1 + y) / ((1 : ℝ) - y) :=
    (div_lt_div_iff₀ hxden hyden).2 hmul
  simpa [cayley] using hdiv

/-- The Cayley transform is monotone on `(-1,1)`. -/
lemma monotoneOn_cayley : MonotoneOn cayley (Set.Ioo (-1 : ℝ) 1) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · exact (strictMonoOn_cayley hx hy hlt).le

/--
Composing the ratio functional with the Cayley transform gives a monotone
function on the Koranyi interval `(-1,1)`.
-/
theorem monotoneOn_ratioFunctional_cayley (μ : FiniteMeasure ENNReal) :
    MonotoneOn (fun x : ℝ => (ratioFunctional μ (Real.toNNReal (cayley x)) : ENNReal))
      (Set.Ioo (-1 : ℝ) 1) := by
  intro x hx y hy hxy
  have hcayley : cayley x ≤ cayley y := monotoneOn_cayley hx hy hxy
  have hnn : Real.toNNReal (cayley x) ≤ Real.toNNReal (cayley y) :=
    Real.toNNReal_monotone hcayley
  have hμ :
      ratioFunctional μ (Real.toNNReal (cayley x)) ≤
        ratioFunctional μ (Real.toNNReal (cayley y)) :=
    _root_.Quantum.TraceInequality.Loewner.monotone_ratioFunctional (μ := μ) hnn
  have hμ' :
      (ratioFunctional μ (Real.toNNReal (cayley x)) : ENNReal) ≤
        (ratioFunctional μ (Real.toNNReal (cayley y)) : ENNReal) := by
    exact_mod_cast hμ
  simpa using hμ'

end

end Quantum.TraceInequality.Loewner
