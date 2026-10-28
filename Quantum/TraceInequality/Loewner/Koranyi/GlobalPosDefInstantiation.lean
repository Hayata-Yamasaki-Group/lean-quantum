import Quantum.TraceInequality.Loewner.Koranyi.SupportElimFromPosDef
import Quantum.TraceInequality.Loewner.Koranyi.SupportElimKoranyiKernel


namespace Quantum.TraceInequality.Loewner

open scoped ComplexOrder
open scoped MatrixOrder
open scoped Topology
open scoped UpperHalfPlane

open Set MeasureTheory Filter

noncomputable section

/-!
Step 61 (utility): instantiate Step 58/59 from a *global* `PosDef` hypothesis.

The global hypothesis assumes `PosDef` for every admissible finite point family. Step 58/59 are
formulated for a fixed sequence `y : ∀ n, Fin (n+1) → ℝ`. This file provides a thin
wrapper that derives the required `PosDef` assumption for the chosen `y`.
-/

/-- Instantiate the full support-elimination package for an arbitrary admissible point family. -/
theorem exists_subseq_supportElim_stieltjesDiff_full_of_global_loewnerMatrix_posDef_for_points
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef)
    (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hy : ∀ n : ℕ, pointsHyp (n := n) (y n)) :
    Nonempty (Loewner.StrictApproxFullPackage f) := by
  have hL' : ∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef := by
    intro n
    exact hL n (y n) (hy n)
  exact
    exists_subseq_supportElim_stieltjesDiff_full_of_loewnerMatrix_posDef (f := f) (y := y) hy hL'

/-- Instantiate the Koranyi-kernel support-elimination limit for chosen admissible points. -/
theorem
    exists_subseq_koranyiKernel_supportElim_with_tendsto_of_global_loewnerMatrix_posDef_for_points
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef)
    (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hy : ∀ n : ℕ, pointsHyp (n := n) (y n)) :
    Nonempty (Loewner.KoranyiLimitPackage f) := by
  have hL' : ∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef := by
    intro n
    exact hL n (y n) (hy n)
  exact
    exists_subseq_koranyiKernel_supportElim_with_tendsto_of_loewnerMatrix_posDef
      (f := f) (y := y) hy hL'

end

end Quantum.TraceInequality.Loewner
