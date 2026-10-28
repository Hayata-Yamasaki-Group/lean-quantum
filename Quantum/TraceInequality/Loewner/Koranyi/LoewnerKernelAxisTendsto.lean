import Quantum.TraceInequality.Loewner.Koranyi.SignedIndexSequence
import Quantum.TraceInequality.Loewner.Koranyi.FiniteConstruction
import Mathlib.Data.ENNReal.Real

namespace Quantum.TraceInequality.Loewner

open Set Filter

open scoped Topology

noncomputable section

/-!
Step 87h1 (route B, utility): an `axis Tendsto` lemma for `loewnerKernel f x 0`.

This file is intentionally small: it provides a generic convergence statement for
`loewnerKernel f (xSeq n) 0` along a real sequence `xSeq n → x ≠ 0`, assuming the
corresponding convergence of `f (xSeq n)`.

Downstream, `xSeq` will be `signedPoints (φ n) (i n)`, and the hypothesis on `f` can be discharged
from an appropriate continuity statement (proved elsewhere).
-/

/-- Convergence of `xSeq` and `f ∘ xSeq` gives convergence of `loewnerKernel f xSeq 0`. -/
lemma tendsto_loewnerKernel_zero_of_tendsto
    {f : ℝ → ℝ} {xSeq : ℕ → ℝ} {x : ℝ} (hx0 : x ≠ 0)
    (hx : Tendsto xSeq atTop (𝓝 x))
    (hf : Tendsto (fun n : ℕ => f (xSeq n)) atTop (𝓝 (f x))) :
    Tendsto (fun n : ℕ => loewnerKernel f (xSeq n) 0) atTop (𝓝 (loewnerKernel f x 0)) := by
  have hne : ∀ᶠ n in atTop, xSeq n ≠ 0 :=
    hx.eventually (isOpen_ne.mem_nhds hx0)
  have hRewrite :
    (fun n : ℕ => loewnerKernel f (xSeq n) 0) =ᶠ[atTop]
      fun n : ℕ => (f (xSeq n) - f 0) / (xSeq n) := by
    filter_upwards [hne] with n hn
    simp [loewnerKernel_zero_right (f := f) (x := xSeq n) hn]
  have hRewrite0 : loewnerKernel f x 0 = (f x - f 0) / x :=
    loewnerKernel_zero_right (f := f) (x := x) hx0
  have hnum : Tendsto (fun n : ℕ => f (xSeq n) - f 0) atTop (𝓝 (f x - f 0)) := by
    simpa using hf.sub tendsto_const_nhds
  have hinv : Tendsto (fun n : ℕ => (xSeq n)⁻¹) atTop (𝓝 x⁻¹) :=
    (tendsto_inv₀ (x := x) hx0).comp hx
  have hdiv :
      Tendsto (fun n : ℕ => (f (xSeq n) - f 0) / (xSeq n)) atTop (𝓝 ((f x - f 0) / x)) := by
    have hmul :
        Tendsto (fun n : ℕ => (f (xSeq n) - f 0) * (xSeq n)⁻¹) atTop
          (𝓝 ((f x - f 0) * x⁻¹)) :=
      hnum.mul hinv
    simpa [div_eq_mul_inv] using hmul
  -- Transport through the definitional rewrite, and rewrite the limit point as well.
  simpa [hRewrite0] using hdiv.congr' hRewrite.symm

/-- Continuity of `f` at a nonzero limit point gives axis convergence of the Loewner kernel. -/
theorem tendsto_loewnerKernel_zero_of_continuousAt
    {f : ℝ → ℝ} {xSeq : ℕ → ℝ} {x : ℝ} (hx0 : x ≠ 0)
    (hx : Tendsto xSeq atTop (𝓝 x)) (hf : ContinuousAt f x) :
    Tendsto (fun n : ℕ => loewnerKernel f (xSeq n) 0) atTop (𝓝 (loewnerKernel f x 0)) :=
  tendsto_loewnerKernel_zero_of_tendsto (f := f) (xSeq := xSeq) (x := x) hx0 hx
    (hf := (hf.tendsto.comp hx))

/-- Choose signed-point indices along a subsequence so the zero-axis Loewner kernel converges. -/
theorem exists_indexSeq_axis_tendsto_of_continuousAt
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {f : ℝ → ℝ} {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) (hf : ContinuousAt f x) :
    ∃ i : ∀ n : ℕ, Fin (φ n + 1),
      (∀ᶠ n : ℕ in atTop, i n ≠ 0) ∧
        Tendsto (fun n : ℕ => signedPoints (φ n) (i n)) atTop (𝓝 x) ∧
        Tendsto (fun n : ℕ => loewnerKernel f (signedPoints (φ n) (i n)) 0) atTop
          (𝓝 (loewnerKernel f x 0)) := by
  rcases
      exists_signedPoints_indexSeq_tendsto_along_subseq (φ := φ) hφ (x := x) hx hx0 with
    ⟨i, hi0, hxT⟩
  refine ⟨i, hi0, hxT, ?_⟩
  exact
    tendsto_loewnerKernel_zero_of_continuousAt (f := f) (xSeq := fun n => signedPoints (φ n) (i n))
      (x := x) hx0 hxT hf

/-- The zero-axis Loewner-kernel convergence also holds after applying `ENNReal.ofReal`. -/
theorem tendsto_ofReal_loewnerKernel_zero_of_continuousAt
    {f : ℝ → ℝ} {xSeq : ℕ → ℝ} {x : ℝ} (hx0 : x ≠ 0)
    (hx : Tendsto xSeq atTop (𝓝 x)) (hf : ContinuousAt f x) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (loewnerKernel f (xSeq n) 0)) atTop
      (𝓝 (ENNReal.ofReal (loewnerKernel f x 0))) := by
  have hreal :
      Tendsto (fun n : ℕ => loewnerKernel f (xSeq n) 0) atTop (𝓝 (loewnerKernel f x 0)) :=
    tendsto_loewnerKernel_zero_of_continuousAt (f := f) (xSeq := xSeq) (x := x) hx0 hx hf
  exact (ENNReal.continuous_ofReal.tendsto _).comp hreal

end

end Quantum.TraceInequality.Loewner
