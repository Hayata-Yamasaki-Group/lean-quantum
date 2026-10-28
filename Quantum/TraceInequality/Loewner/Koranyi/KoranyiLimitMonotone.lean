import Quantum.TraceInequality.Loewner.Koranyi.GlobalPosDefBridge
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
Step 63 (bridge): the limiting `ratioFunctional` obtained from the global `PosDef` hypothesis
is monotone (after composing with the Cayley transform).
-/

/-- Global positivity yields a Koranyi-kernel limit whose Cayley ratio functional is monotone. -/
theorem exists_koranyiKernelSupportElimSubseq_monotone_of_globalPosDef
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef) :
    Nonempty (Loewner.KoranyiLimitMonotonePackage f) := by
  rcases
 exists_subseq_koranyiKernel_supportElim_with_tendsto_of_global_loewnerMatrix_posDef_canonicalPoints
      (f := f) hL with
    ⟨p⟩
  refine ⟨⟨p, ?_⟩⟩
  simpa using monotoneOn_ratioFunctional_cayley (μ := p.ν)

end

end Quantum.TraceInequality.Loewner
