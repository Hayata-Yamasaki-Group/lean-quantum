import Quantum.TraceInequality.Loewner.Koranyi.EvalAtInvRewrite
import Quantum.TraceInequality.Loewner.Koranyi.EvalAtInvKernelLimit

namespace Quantum.TraceInequality.Loewner

open Set MeasureTheory Filter

open scoped ComplexOrder
open scoped MatrixOrder
open scoped Topology
open scoped UpperHalfPlane

noncomputable section

/-!
Step 80 (convenience): extend the Step 67'' "eval-at-inv / one-sub-mul" full package with the
kernel-difference convergence statement from Step 78.
-/

/-- The eval-at-inv one-sub-mul package also carries kernel-difference convergence. -/
theorem exists_supportElimStieltjesDiffSubseq_of_globalPosDef_evalInv_oneSubMul_kernelLimit
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef) :
    Nonempty (Loewner.FullOneSubMulSubseqKernelLimitPackage f canonicalPoints) := by
  rcases
      exists_supportElimStieltjesDiffSubseq_of_globalPosDef_evalInv_oneSubMulSubseq
        (f := f) hL with
    ⟨p⟩
  have hKernel :
      ∀ z w : ℍ,
        Tendsto
            (fun n =>
              (∫ t, (z : ℂ) * (1 / (1 - (z : ℂ) * (t : ℂ)))
                  ∂((p.μn (p.φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) -
                ∫ t, (w : ℂ) * (1 / (1 - (w : ℂ) * (t : ℂ)))
                  ∂((p.μn (p.φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ))
            atTop (𝓝 (p.F z - p.F w)) := by
    intro z w
    exact
      tendsto_integral_one_sub_mul_diff_of_tendsto_stieltjes
        (μn := p.μn) (φ := p.φ) (F := p.F) (M0 := p.M0) p.hM0 p.hμle
        p.hStieltjesTendsto z w
  exact ⟨⟨p, hKernel⟩⟩

end

end Quantum.TraceInequality.Loewner
