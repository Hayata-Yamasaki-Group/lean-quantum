import Quantum.TraceInequality.Loewner.Koranyi.SignedPointsKernelZeroAxis
import Quantum.TraceInequality.Loewner.Koranyi.OneSubMulKernel

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap


namespace Quantum.TraceInequality.Loewner

open Set MeasureTheory Filter

noncomputable section

/-!
Step 87f (route B): split the full-measure kernel integral into its `[-1,1]` part and its
complement part, tracking the `[-1,1]` contribution as an explicit correction term.

This file is intentionally lightweight: it does not attempt to show that the correction term
vanishes.  Downstream files can use this split together with limits on each term.
-/

/-- The closed interval `[-1, 1]`. -/
def closedUnitInterval : Set ℝ :=
  Set.Icc (-1 : ℝ) 1

/-- The `[-1, 1]` correction term: the complex `1/(1 - x t)` kernel integrated against `μ`
restricted to `[-1, 1]`. -/
def corrIccC (μ : Measure ℝ) (x : ℝ) : ℂ :=
  ∫ t, oneSubMulKernelC x t ∂(μ.restrict closedUnitInterval)

/-- The complement (outside `[-1, 1]`) part: the complex `1/(1 - x t)` kernel integrated against
`μ` restricted to `[-1, 1]ᶜ`. -/
def outIccC (μ : Measure ℝ) (x : ℝ) : ℂ :=
  ∫ t, oneSubMulKernelC x t ∂(μ.restrict closedUnitIntervalᶜ)

/-- The real reciprocal kernel `1/(1 - x t)`. -/
def oneSubMulKernelR (x : ℝ) (t : ℝ) : ℝ :=
  1 / (1 - x * t)

/-- The real `[-1, 1]` correction term: the real reciprocal kernel integrated against `μ`
restricted to `[-1, 1]`. -/
def corrIccR (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ t, oneSubMulKernelR x t ∂(μ.restrict closedUnitInterval)

/-- The real complement (outside `[-1, 1]`) part: the real reciprocal kernel integrated against
`μ` restricted to `[-1, 1]ᶜ`. -/
def outIccR (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ t, oneSubMulKernelR x t ∂(μ.restrict closedUnitIntervalᶜ)

/-- The complex reciprocal kernel is the `ℝ → ℂ` coercion of the real reciprocal kernel. -/
lemma oneSubMulKernelC_eq_ofReal_oneSubMulKernelR (x t : ℝ) :
    oneSubMulKernelC x t = (oneSubMulKernelR x t : ℂ) := by
  -- Both sides are the same rational function of real variables, viewed in `ℂ`.
  simp [oneSubMulKernelC, oneSubMulKernelR]

/-- The complex `[-1, 1]` correction term is the coercion of the real correction term. -/
lemma corrIccC_eq_ofReal_corrIccR (μ : Measure ℝ) (x : ℝ) :
    corrIccC μ x = Complex.ofReal (corrIccR μ x) := by
  -- Rewrite the integrand as an `ofReal`, then use `integral_complex_ofReal`.
  simpa [corrIccC, corrIccR, oneSubMulKernelC_eq_ofReal_oneSubMulKernelR] using
    (integral_complex_ofReal (μ := μ.restrict closedUnitInterval)
      (f := fun t : ℝ => oneSubMulKernelR x t))

/-- The complex complement term is the coercion of the real complement term. -/
lemma outIccC_eq_ofReal_outIccR (μ : Measure ℝ) (x : ℝ) :
    outIccC μ x = Complex.ofReal (outIccR μ x) := by
  -- Rewrite the integrand as an `ofReal`, then use `integral_complex_ofReal`.
  simpa [outIccC, outIccR, oneSubMulKernelC_eq_ofReal_oneSubMulKernelR] using
    (integral_complex_ofReal (μ := μ.restrict closedUnitIntervalᶜ)
      (f := fun t : ℝ => oneSubMulKernelR x t))

/-- For `x ∈ (-1, 1)` and `t ∈ [-1, 1]`, the reciprocal kernel `1/(1 - x t)` is nonnegative, since
the denominator is positive. -/
lemma oneSubMulKernelR_nonneg_of_mem_Ioo_Icc {x t : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (ht : t ∈ closedUnitInterval) :
    0 ≤ oneSubMulKernelR x t := by
  have ht_abs : |t| ≤ 1 := by
    -- `t ∈ [-1,1]` implies `|t| ≤ 1`.
    exact abs_le.2 ht
  have hx_abs_lt : |x| < 1 := by
    exact abs_lt.2 hx
  have hxt_abs_lt : |x * t| < 1 := by
    have hmul_le : |x| * |t| ≤ |x| := by
      have : |x| * |t| ≤ |x| * 1 := by
        exact mul_le_mul_of_nonneg_left ht_abs (abs_nonneg x)
      simpa [mul_one] using this
    have hmul_lt : |x| * |t| < 1 := lt_of_le_of_lt hmul_le hx_abs_lt
    simpa [abs_mul] using hmul_lt
  have hxt_lt : x * t < 1 := lt_of_le_of_lt (le_abs_self _) hxt_abs_lt
  have hden_pos : 0 < 1 - x * t := sub_pos.mpr hxt_lt
  -- `1 / (1 - x*t) ≥ 0`.
  have : 0 ≤ 1 / (1 - x * t) := by
    exact one_div_nonneg.mpr (le_of_lt hden_pos)
  simpa [oneSubMulKernelR] using this


/-- Split the full kernel integral into its complement (`[-1, 1]ᶜ`) part and its `[-1, 1]`
correction part. -/
lemma integral_oneSubMulKernelC_split_Icc
    {μ : Measure ℝ} {x : ℝ}
    (hInt : Integrable (fun t : ℝ => oneSubMulKernelC x t) μ) :
    (∫ t, oneSubMulKernelC x t ∂μ) =
        (∫ t, oneSubMulKernelC x t ∂(μ.restrict closedUnitIntervalᶜ)) +
        (∫ t, oneSubMulKernelC x t ∂(μ.restrict closedUnitInterval)) := by
  have hs : MeasurableSet closedUnitInterval := isClosed_Icc.measurableSet
  -- `integral_add_compl` is stated using set integrals; rewrite them as integrals against
  -- restricted measures.
  have h :
      (∫ t, oneSubMulKernelC x t ∂μ) =
        (∫ t in closedUnitInterval, oneSubMulKernelC x t ∂μ) +
          (∫ t in closedUnitIntervalᶜ, oneSubMulKernelC x t ∂μ) :=
    (MeasureTheory.integral_add_compl
      (μ := μ) (s := closedUnitInterval) (f := fun t : ℝ => oneSubMulKernelC x t) hs hInt).symm
  -- Swap the order and unfold the set integrals.
  simpa [corrIccC, outIccC, add_comm, add_left_comm, add_assoc] using h

/-- At the signed interpolation points, the Löwner kernel evaluated at `0` decomposes as the
outside term plus the `[-1, 1]` correction term, given the pointwise kernel-integral formula and
integrability of the integrand. [simon2019] -/
lemma signedPoints_loewnerKernel_zero_eq_outsideC_add_corrC_of_integrable
    {f : ℝ → ℝ} {μn : ℕ → Measure ℝ} {φ : ℕ → ℕ}
    (hLK :
      ∀ n : ℕ,
        ∀ i : Fin (φ n + 1),
          i ≠ 0 →
            (loewnerKernel f (signedPoints (φ n) i) 0 : ℂ) =
              ∫ t, oneSubMulKernelC (signedPoints (φ n) i) t ∂(μn (φ n)))
    (hInt :
      ∀ n : ℕ,
        ∀ i : Fin (φ n + 1),
          i ≠ 0 →
            Integrable (fun t : ℝ => oneSubMulKernelC (signedPoints (φ n) i) t) (μn (φ n))) :
    ∀ n : ℕ,
      ∀ i : Fin (φ n + 1),
        i ≠ 0 →
          (loewnerKernel f (signedPoints (φ n) i) 0 : ℂ) =
            outIccC (μn (φ n)) (signedPoints (φ n) i) +
              corrIccC (μn (φ n)) (signedPoints (φ n) i) := by
  intro n i hi0
  have hsplit :=
    integral_oneSubMulKernelC_split_Icc
      (μ := μn (φ n)) (x := signedPoints (φ n) i) (hInt n i hi0)
  -- Rewrite the right-hand side using `outIccC`/`corrIccC`.
  have hsplit' :
      (∫ t, oneSubMulKernelC (signedPoints (φ n) i) t ∂(μn (φ n))) =
        outIccC (μn (φ n)) (signedPoints (φ n) i) +
          corrIccC (μn (φ n)) (signedPoints (φ n) i) := by
    simpa [outIccC, corrIccC] using hsplit
  exact (hLK n i hi0).trans hsplit'

end

end Quantum.TraceInequality.Loewner
