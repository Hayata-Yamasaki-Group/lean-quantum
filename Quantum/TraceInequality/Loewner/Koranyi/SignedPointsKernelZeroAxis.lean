import Quantum.TraceInequality.Loewner.Koranyi.GlobalPosDefInstantiationAtInv
import Quantum.TraceInequality.Loewner.Koranyi.LoewnerKernelZeroAxis
import Quantum.TraceInequality.Loewner.Koranyi.SignedPoints


namespace Quantum.TraceInequality.Loewner

open Set MeasureTheory Filter

open scoped ComplexOrder
open scoped MatrixOrder
open scoped Topology
open scoped UpperHalfPlane

noncomputable section

/-!
Step 86 (signed points): instantiate the global `for_points` package using `signedPoints`,
and additionally rewrite the evaluation identity into an explicit formula for
`loewnerKernel f (signedPoints ...) 0`.
-/


/-- As the signed-points support-elimination package, additionally recording integrability of the
`1/(1 - y t)` kernel against each measure. [simon2019] -/
theorem exists_supportElimStieltjesDiffSubseq_of_signedGlobalPosDef_zeroAxis_kernelIntegrable
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef) :
    Nonempty (Loewner.FullSignedZeroAxisKernelIntegrablePackage f) := by
  rcases
      exists_supportElimStieltjesDiffSubseq_of_pointsGlobalPosDef_evalInv_kernelIntegrable
        (f := f) (hL := hL) (y := signedPoints)
        (hy := fun n => pointsHyp_signedPoints (n := n)) with
    ⟨p⟩
  refine
    ⟨⟨p.toFullOneSubMulPackage.toStrictApproxFullPackage, p.hKernelIntegrableSubseq, ?_⟩⟩
  intro n i hi0
  have hy0 : signedPoints (p.φ n) i ≠ 0 :=
    (pointsHyp_signedPoints (n := p.φ n)).2.2.2 i hi0
  have hEval' := p.toFullOneSubMulPackage.hOneSubMul (p.φ n) i hi0
  simpa using
    loewnerKernel_zero_eq_integral_one_div_one_sub_mul_of_eval
      (f := f) (μ := p.μn (p.φ n)) (y := signedPoints (p.φ n) i) hy0 hEval'

end

end Quantum.TraceInequality.Loewner
