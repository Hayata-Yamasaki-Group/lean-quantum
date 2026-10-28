import Quantum.TraceInequality.Loewner.Koranyi.GlobalPosDefInstantiation
import Quantum.TraceInequality.Loewner.Koranyi.CayleyMonotonicity


namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter Set

open scoped ComplexOrder
open scoped MatrixOrder
open scoped Topology
open scoped UpperHalfPlane
open scoped NNReal

noncomputable section

/-!
Step 64 (bridge): a monotone Korányi-kernel limit package, for an arbitrary point family `y`.

This is the `y : ∀ n, Fin (n+1) → ℝ`-generalization of Step 63, obtained by combining:

* Step 61: instantiate the Step 59 package from a global `PosDef` hypothesis for a chosen `y`,
* Step 62: monotonicity of `x ↦ ratioFunctional ν (cayley x)` on `(-1,1)`.
-/

/-- Monotone Korányi-kernel limit package for an arbitrary point family: from a global
positive-definiteness hypothesis on the Löwner matrices, extract a subsequence of support-eliminated
measures whose Stieltjes transforms converge uniformly on compacts and are monotone. [simon2019] -/
theorem
    exists_subseq_koranyiKernel_supportElim_with_tendsto_and_monotone_of_global_loewnerMatrix_posDef
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef)
    (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hy : ∀ n : ℕ, pointsHyp (n := n) (y n)) :
    Nonempty (Loewner.KoranyiLimitMonotonePackage f) := by
  rcases
      exists_subseq_koranyiKernel_supportElim_with_tendsto_of_global_loewnerMatrix_posDef_for_points
        (f := f) (hL := hL) (y := y) hy with
    ⟨p⟩
  refine ⟨⟨p, ?_⟩⟩
  simpa using monotoneOn_ratioFunctional_cayley (μ := p.ν)

end

end Quantum.TraceInequality.Loewner
