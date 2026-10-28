import Quantum.TraceInequality.Loewner.Koranyi.SignedPointsKernelZeroAxis
import Quantum.TraceInequality.Loewner.Koranyi.SplitFullMeasure

namespace Quantum.TraceInequality.Loewner

open Set MeasureTheory Filter

noncomputable section

/-!
Helper for route B.

From a single signedPoints package (the `loewnerKernel = ∫ ...` identity plus
an `Integrable` field on the same subsequence), apply the signed-points split
lemma to obtain the exact outside+inside decomposition.

This lemma is the signed-points consumer of the full-measure split package.
-/

/-- From a single signed-points package (the kernel-integral identity plus integrability of the
integrand), derive the outside + `[-1, 1]` correction decomposition of the Löwner kernel at `0`. -/
lemma signedPoints_split_eq_from_single_package
    {f : ℝ → ℝ} {μn : ℕ → Measure ℝ} {φ : ℕ → ℕ}
    (hLK :
      ∀ n : ℕ,
        ∀ i : Fin (φ n + 1),
          i ≠ 0 →
            (loewnerKernel f (signedPoints (φ n) i) 0 : ℂ) =
              ∫ t, (1 / (1 - (signedPoints (φ n) i : ℂ) * (t : ℂ))) ∂(μn (φ n)))
    (hIntSubseq :
      ∀ n : ℕ,
        ∀ x : ℝ,
          Integrable (fun t : ℝ => oneSubMulKernelC x t) (μn (φ n))) :
    ∀ n : ℕ,
      ∀ i : Fin (φ n + 1),
        i ≠ 0 →
          (loewnerKernel f (signedPoints (φ n) i) 0 : ℂ) =
            outIccC (μn (φ n)) (signedPoints (φ n) i) +
              corrIccC (μn (φ n)) (signedPoints (φ n) i) := by
  have hLK' :
      ∀ n : ℕ,
        ∀ i : Fin (φ n + 1),
          i ≠ 0 →
            (loewnerKernel f (signedPoints (φ n) i) 0 : ℂ) =
              ∫ t, oneSubMulKernelC (signedPoints (φ n) i) t ∂(μn (φ n)) := by
    intro n i hi0
    simpa [oneSubMulKernelC] using hLK n i hi0
  have hIntSigned :
      ∀ n : ℕ,
        ∀ i : Fin (φ n + 1),
          i ≠ 0 →
            Integrable (fun t : ℝ => oneSubMulKernelC (signedPoints (φ n) i) t) (μn (φ n)) :=
    fun n i _hi0 => hIntSubseq n (signedPoints (φ n) i)
  exact signedPoints_loewnerKernel_zero_eq_outsideC_add_corrC_of_integrable
    (f := f) (μn := μn) (φ := φ) hLK' hIntSigned

/-- Real-valued version of the signed-points split decomposition of the Löwner kernel at `0`. -/
lemma signedPoints_split_eq_from_single_package_R
    {f : ℝ → ℝ} {μn : ℕ → Measure ℝ} {φ : ℕ → ℕ}
    (hLK :
      ∀ n : ℕ,
        ∀ i : Fin (φ n + 1),
          i ≠ 0 →
            (loewnerKernel f (signedPoints (φ n) i) 0 : ℂ) =
              ∫ t, (1 / (1 - (signedPoints (φ n) i : ℂ) * (t : ℂ))) ∂(μn (φ n)))
    (hIntSubseq :
      ∀ n : ℕ,
        ∀ x : ℝ,
          Integrable (fun t : ℝ => oneSubMulKernelC x t) (μn (φ n))) :
    ∀ n : ℕ,
      ∀ i : Fin (φ n + 1),
        i ≠ 0 →
          loewnerKernel f (signedPoints (φ n) i) 0 =
            outIccR (μn (φ n)) (signedPoints (φ n) i) +
              corrIccR (μn (φ n)) (signedPoints (φ n) i) := by
  intro n i hi0
  have hC :=
    signedPoints_split_eq_from_single_package (f := f) (μn := μn) (φ := φ) hLK hIntSubseq n i hi0
  have hR := congrArg Complex.re hC
  -- Left side is real by construction; rewrite the right side using `outIccC/corrIccC` realness.
  have hout : (outIccC (μn (φ n)) (signedPoints (φ n) i)).re =
      outIccR (μn (φ n)) (signedPoints (φ n) i) := by
    simpa using congrArg Complex.re
      (outIccC_eq_ofReal_outIccR (μ := μn (φ n)) (x := signedPoints (φ n) i))
  have hcorr : (corrIccC (μn (φ n)) (signedPoints (φ n) i)).re =
      corrIccR (μn (φ n)) (signedPoints (φ n) i) := by
    simpa using congrArg Complex.re
      (corrIccC_eq_ofReal_corrIccR (μ := μn (φ n)) (x := signedPoints (φ n) i))
  -- Finish.
  simpa [hout, hcorr] using hR

end

end Quantum.TraceInequality.Loewner
