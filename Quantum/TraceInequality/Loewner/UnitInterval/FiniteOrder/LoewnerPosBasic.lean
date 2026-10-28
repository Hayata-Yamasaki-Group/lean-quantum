import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.Basic
import Quantum.TraceInequality.Loewner.UnitInterval.SharedSlopeCore

/-!
# Basic consequences of public Löwner positivity

This file contains scalar differentiability, monotonicity, and slope/kernel
normalization lemmas used throughout the Chapter 20 finite-order regularity
proof.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped Interval
open scoped ComplexOrder
open scoped MatrixOrder
open scoped NNReal
open scoped ENNReal

noncomputable section

/-- Public Löwner positivity gives differentiability at each interior point. -/
theorem differentiableAt_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (h : LoewnerPosOnUnitInterval f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    DifferentiableAt ℝ f x :=
  h.differentiable.differentiableAt (isOpen_Ioo.mem_nhds hx)

/-- Public Löwner positivity gives continuity on the normalized interval. -/
theorem continuousAt_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (h : LoewnerPosOnUnitInterval f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ContinuousAt f x :=
  (differentiableAt_of_loewnerPosOnUnitInterval h hx).continuousAt

/-- Public Löwner positivity makes the derivative nonnegative on `(-1,1)`. -/
theorem deriv_nonneg_on_Ioo_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (h : LoewnerPosOnUnitInterval f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    0 ≤ deriv f x := by
  have hL :=
    h.posSemidef 1 (fun _ : Fin 1 => x)
      (by
        intro i
        fin_cases i
        exact hx)
      (by
        intro i j _hij
        fin_cases i
        fin_cases j
        rfl)
  have hdiag := hL.diag_nonneg (i := (0 : Fin 1))
  simpa [loewnerKernel] using hdiag

/-- Public Löwner positivity gives scalar monotonicity on the normalized interval. -/
theorem scalarMonotoneOn_Ioo_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (h : LoewnerPosOnUnitInterval f) :
    MonotoneOn f (Set.Ioo (-1 : ℝ) 1) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioo (-1 : ℝ) 1) ?_ ?_ ?_
  · exact h.differentiable.continuousOn
  · simpa using h.differentiable
  · intro x hx
    exact deriv_nonneg_on_Ioo_of_loewnerPosOnUnitInterval h (by simpa using hx)

end

end Quantum.TraceInequality.Loewner
