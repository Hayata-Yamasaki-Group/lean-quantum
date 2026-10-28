import Quantum.TraceInequality.Loewner.Koranyi.SupportElimFromPosDefAtInv


namespace Quantum.TraceInequality.Loewner

open scoped ComplexOrder
open scoped MatrixOrder
open scoped Topology
open scoped UpperHalfPlane

open Set MeasureTheory Filter

noncomputable section

/-!
Step 61' (utility): instantiate the strengthened Step 58' package from a *global* `PosDef`
hypothesis, for an arbitrary chosen point family `y`.
-/

/-- Chosen admissible points inherit the inverse-evaluation support-elimination package. -/
theorem exists_supportElimStieltjesDiffSubseq_of_pointsGlobalPosDef_evalInv
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef)
    (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hy : ∀ n : ℕ, pointsHyp (n := n) (y n)) :
    Nonempty (Loewner.FullEvalInvPackage f y) := by
  have hL' : ∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef := by
    intro n
    exact hL n (y n) (hy n)
  exact
    exists_subseq_supportElim_stieltjesDiff_full_of_loewnerMatrix_posDef_with_eval_at_inv
      (f := f) (y := y) hy hL'

end

end Quantum.TraceInequality.Loewner

namespace Quantum.TraceInequality.Loewner

open scoped ComplexOrder
open scoped MatrixOrder
open scoped Topology
open scoped UpperHalfPlane

open Set MeasureTheory Filter

noncomputable section

/-- Chosen admissible points inherit the `1 - y * t` form of inverse evaluation. -/
theorem exists_supportElimStieltjesDiffSubseq_of_pointsGlobalPosDef_evalInv_oneSubMul
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef)
    (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hy : ∀ n : ℕ, pointsHyp (n := n) (y n)) :
    Nonempty (Loewner.FullOneSubMulPackage f y) := by
  have hL' : ∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef := by
    intro n
    exact hL n (y n) (hy n)
  exact
    exists_supportElimStieltjesDiffSubseq_of_posDef_evalInv_oneSubMul
      (f := f) (y := y) hy hL'

/-- Chosen admissible points inherit inverse evaluation and kernel integrability. -/
theorem exists_supportElimStieltjesDiffSubseq_of_pointsGlobalPosDef_evalInv_kernelIntegrable
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef)
    (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hy : ∀ n : ℕ, pointsHyp (n := n) (y n)) :
    Nonempty (Loewner.FullOneSubMulKernelIntegrablePackage f y) := by
  have hL' : ∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef := by
    intro n
    exact hL n (y n) (hy n)
  exact
    exists_supportElimStieltjesDiffSubseq_of_posDef_evalInv_oneSubMul_kernelIntegrable
      (f := f) (y := y) hy hL'

end

end Quantum.TraceInequality.Loewner
