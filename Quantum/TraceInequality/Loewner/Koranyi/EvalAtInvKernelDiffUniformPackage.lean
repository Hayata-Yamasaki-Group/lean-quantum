import Quantum.TraceInequality.Loewner.Koranyi.EvalAtInvKernelDiffPackage
import Quantum.TraceInequality.Loewner.Koranyi.EvalAtInvKernelLimit

namespace Quantum.TraceInequality.Loewner

open Set MeasureTheory Filter

open scoped ComplexOrder
open scoped MatrixOrder
open scoped Topology
open scoped UpperHalfPlane

noncomputable section

/-!
Step 82 (convenience): starting from the Step 80 full package (global `PosDef` at canonical points),
add the uniform-on-`KmHT m` convergence for the restricted `(1 - z*t)` kernel **differences**.
-/

/-- The eval-at-inv package also carries uniform restricted kernel-difference convergence. -/
theorem exists_supportElimStieltjesDiffSubseq_of_globalPosDef_evalInv_oneSubMul_uniformKernelLimit
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef) :
    Nonempty (Loewner.FullOneSubMulSubseqUniformKernelLimitPackage f canonicalPoints) := by
  rcases
      exists_supportElimStieltjesDiffSubseq_of_globalPosDef_evalInv_oneSubMul_kernelLimit
        (f := f) hL with
    ⟨p⟩
  have hKernelU :
      ∀ w : ℍ,
        ∀ m : ℕ,
          TendstoUniformly
              (fun n (z : KmHT m) =>
                (∫ t, (z.1 : ℂ) * (1 / (1 - (z.1 : ℂ) * (t : ℂ)))
                    ∂((p.μn (p.φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) -
                  ∫ t, (w : ℂ) * (1 / (1 - (w : ℂ) * (t : ℂ)))
                    ∂((p.μn (p.φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ))
              (fun z => p.F z.1 - p.F w) atTop := by
    intro w m
    exact
      tendstoUniformly_integral_mul_one_div_one_sub_mul_sub_of_tendstoUniformly_stieltjes
        (μn := p.μn) (φ := p.φ) (F := p.F) (M0 := p.M0) p.hM0 p.hμle
        p.hStieltjes p.hStieltjesTendsto w m
  exact ⟨⟨p, hKernelU⟩⟩

end

end Quantum.TraceInequality.Loewner
