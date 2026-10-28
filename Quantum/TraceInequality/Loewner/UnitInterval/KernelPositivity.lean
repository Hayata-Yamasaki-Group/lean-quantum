import Quantum.TraceInequality.Loewner.Statement
import Quantum.TraceInequality.Loewner.Kernel.FiniteMatrixData

/-!
# Löwner-kernel positivity consequences

This module extracts scalar and finite-matrix consequences of normalized
interval Löwner positivity and connects them to the Korányi finite construction.
-/

namespace Quantum.TraceInequality.Loewner

open Set

open scoped ComplexOrder
open scoped MatrixOrder

noncomputable section

private lemma pointsHyp_zero_family :
    pointsHyp (n := 0) (fun _ : Fin (0 + 1) => (0 : ℝ)) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro i j _
    fin_cases i
    fin_cases j
    rfl
  · intro i
    fin_cases i
    simp
  · intro i hi
    fin_cases i
    exact (hi rfl).elim

private lemma pointsHyp_pair_zero_left {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    pointsHyp (n := 1) (fun i : Fin (1 + 1) => if i = 0 then (0 : ℝ) else x) := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso
      exact hx0 (by simpa [eq_comm] using hij)
    · exfalso
      exact hx0 (by simpa using hij)
    · rfl
  · intro i
    fin_cases i <;> simp [hx]
  · intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · simp [hx0]

/-- The diagonal entries of the strict Löwner matrices force `f'` to be strictly
positive on the normalized interval. -/
theorem deriv_pos_of_globalStrictPosDef
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    0 < deriv f x := by
  classical
  by_cases hx0 : x = 0
  · subst hx0
    have hL :=
      h 0 (fun _ : Fin (0 + 1) => (0 : ℝ)) pointsHyp_zero_family
    have hdiag := hL.diag_pos (i := (0 : Fin (0 + 1)))
    simpa [loewnerMatrix] using hdiag
  · let y : Fin (1 + 1) → ℝ := fun i => if i = 0 then (0 : ℝ) else x
    have hy : pointsHyp (n := 1) y := pointsHyp_pair_zero_left hx hx0
    have hL := h 1 y hy
    let i1 : Fin (1 + 1) := ⟨1, by decide⟩
    have hdiag := hL.diag_pos (i := i1)
    simpa [loewnerMatrix, y, i1] using hdiag

/-- The strict Löwner matrices force differentiability on the normalized
interval. -/
theorem differentiableAt_of_globalStrictPosDef
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    DifferentiableAt ℝ f x :=
  differentiableAt_of_deriv_ne_zero (deriv_pos_of_globalStrictPosDef h hx).ne'

/-- The strict Löwner matrices force continuity on the normalized interval. -/
theorem continuousAt_of_globalStrictPosDef
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ContinuousAt f x :=
  (differentiableAt_of_globalStrictPosDef h hx).continuousAt

/-- The strict matrix hypothesis makes `f` strictly increasing on `(-1, 1)`. -/
theorem strictMonoOn_of_globalStrictPosDef
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) :
    StrictMonoOn f (Set.Ioo (-1 : ℝ) 1) := by
  have hderiv : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, 0 < deriv f x := fun x hx =>
    deriv_pos_of_globalStrictPosDef h hx
  refine strictMonoOn_of_deriv_pos (convex_Ioo (-1 : ℝ) 1) ?_ ?_
  · intro x hx
    exact (differentiableAt_of_globalStrictPosDef h hx).differentiableWithinAt
      |>.continuousWithinAt
  · simpa [interior_Ioo] using hderiv

/-- The strict matrix hypothesis makes the Löwner kernel against the anchor `0`
strictly positive away from the anchor. -/
theorem loewnerKernel_zero_pos_of_globalStrictPosDef
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    0 < loewnerKernel f x 0 := by
  have hmono := strictMonoOn_of_globalStrictPosDef h
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  by_cases hpos : 0 < x
  · have hfx : f 0 < f x := hmono h0mem hx hpos
    have hnum : 0 < f x - f 0 := sub_pos.mpr hfx
    have hdiv : 0 < (f x - f 0) / x := div_pos hnum hpos
    simpa [loewnerKernel_zero_right (f := f) hx0] using hdiv
  · have hneg : x < 0 := lt_of_le_of_ne (not_lt.mp hpos) hx0
    have hfx : f x < f 0 := hmono hx h0mem hneg
    have hnum : f x - f 0 < 0 := sub_neg.mpr hfx
    have hdiv : 0 < (f x - f 0) / x := div_pos_of_neg_of_neg hnum hneg
    simpa [loewnerKernel_zero_right (f := f) hx0] using hdiv

/-- Nonnegative version of `loewnerKernel_zero_pos_of_globalStrictPosDef`. -/
theorem loewnerKernel_zero_nonneg_of_globalStrictPosDef
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    0 ≤ loewnerKernel f x 0 :=
  (loewnerKernel_zero_pos_of_globalStrictPosDef h hx hx0).le

end

end Loewner
end TraceInequality
end Quantum
