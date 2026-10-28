import Quantum.TraceInequality.Loewner.Koranyi.EvalAtInvKernel
import Quantum.TraceInequality.Loewner.Koranyi.PickLimit

/-!
# Limits of the restricted kernel differences

Steps of the Korányi construction: convergence, and uniform convergence, of the Stieltjes
transforms give the corresponding convergence of the restricted `(1 - z * t)` kernel
differences.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set Filter

open scoped Topology
open scoped UpperHalfPlane

noncomputable section



/-- Stieltjes convergence implies convergence of restricted `(1 - z * t)` kernel differences. -/
theorem tendsto_integral_one_sub_mul_diff_of_tendsto_stieltjes
    {μn : ℕ → Measure ℝ} {φ : ℕ → ℕ} {F : ℍ → ℂ} {M0 : ENNReal}
    (hM0 : M0 < ⊤) (hμle : ∀ n : ℕ, μn n Set.univ ≤ M0)
    (htSt :
      ∀ z : ℍ,
        Tendsto (fun n => stieltjes (supportElimMeasure (μn (φ n))) z) atTop
          (𝓝 (F z)))
    (z w : ℍ) :
    Tendsto
        (fun n =>
          (∫ t, (z : ℂ) * (1 / (1 - (z : ℂ) * (t : ℂ)))
              ∂((μn (φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) -
            ∫ t, (w : ℂ) * (1 / (1 - (w : ℂ) * (t : ℂ)))
              ∂((μn (φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ))
        atTop (𝓝 (F z - F w)) := by
  have hμfin : ∀ n : ℕ, (μn (φ n)) Set.univ < ⊤ := by
    intro n
    exact lt_of_le_of_lt (hμle (φ n)) hM0
  have hz : Tendsto (fun n => stieltjes (supportElimMeasure (μn (φ n))) z) atTop (𝓝 (F z)) :=
    htSt z
  have hw : Tendsto (fun n => stieltjes (supportElimMeasure (μn (φ n))) w) atTop (𝓝 (F w)) :=
    htSt w
  have hsub :
      Tendsto
          (fun n =>
            stieltjes (supportElimMeasure (μn (φ n))) z -
              stieltjes (supportElimMeasure (μn (φ n))) w)
          atTop (𝓝 (F z - F w)) :=
    hz.sub hw
  refine hsub.congr' ?_
  refine Filter.Eventually.of_forall (fun n => ?_)
  simpa using
    (integral_mul_one_div_one_sub_mul_sub_eq_stieltjes_sub
      (μ := μn (φ n)) (hμ := hμfin n) (z := z) (w := w)).symm

end

end Quantum.TraceInequality.Loewner

namespace Quantum.TraceInequality.Loewner

open Set MeasureTheory Filter

open scoped ComplexOrder
open scoped MatrixOrder
open scoped Topology
open scoped UpperHalfPlane

noncomputable section



/-- Uniform Stieltjes convergence gives uniform convergence of restricted kernel differences. -/
theorem tendstoUniformly_integral_mul_one_div_one_sub_mul_sub_of_tendstoUniformly_stieltjes
    (μn : ℕ → Measure ℝ) (φ : ℕ → ℕ) (F : ℍ → ℂ) (M0 : ENNReal) (hM0 : M0 < ⊤)
    (hμle : ∀ n : ℕ, μn n Set.univ ≤ M0)
    (hconvSt :
      ∀ m : ℕ,
        TendstoUniformly
          (fun n (z : KmHT m) => stieltjes (supportElimMeasure (μn (φ n))) z.1)
          (fun z => F z.1) atTop)
    (htSt :
      ∀ z : ℍ,
        Tendsto (fun n => stieltjes (supportElimMeasure (μn (φ n))) z) atTop (𝓝 (F z)))
    (w : ℍ) :
    ∀ m : ℕ,
      TendstoUniformly
          (fun n (z : KmHT m) =>
            (∫ t, (z.1 : ℂ) * (1 / (1 - (z.1 : ℂ) * (t : ℂ)))
                ∂((μn (φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) -
              ∫ t, (w : ℂ) * (1 / (1 - (w : ℂ) * (t : ℂ)))
                ∂((μn (φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ))
          (fun z => F z.1 - F w) atTop := by
  intro m
  have hμfin : ∀ n : ℕ, (μn (φ n)) Set.univ < ⊤ := by
    intro n
    exact lt_of_le_of_lt (hμle (φ n)) hM0
  -- First show uniform convergence for the Stieltjes differences `z ↦ stieltjes(z) - stieltjes(w)`.
  have hStDiff :
      TendstoUniformly
          (fun n (z : KmHT m) =>
            stieltjes (supportElimMeasure (μn (φ n))) z.1 -
              stieltjes (supportElimMeasure (μn (φ n))) w)
          (fun z => F z.1 - F w) atTop := by
    -- Build uniform convergence of the pair `(stieltjes(z), stieltjes(w))`.
    have hpair :
        TendstoUniformly
            (fun n (z : KmHT m) =>
              (stieltjes (supportElimMeasure (μn (φ n))) z.1,
                stieltjes (supportElimMeasure (μn (φ n))) w))
            (fun z => (F z.1, F w)) atTop := by
      intro u hu
      rcases entourageProd_subset (α := ℂ) (β := ℂ) hu with ⟨u₁, hu₁, u₂, hu₂, hsub⟩
      have h₁ := hconvSt m u₁ hu₁
      have h₂ : ∀ᶠ n in atTop,
          (F w, stieltjes (supportElimMeasure (μn (φ n))) w) ∈ u₂ := by
        exact (tendsto_def.1 (Uniform.tendsto_nhds_right.1 (htSt w))) u₂ hu₂
      filter_upwards [h₁, h₂] with n hn₁ hn₂
      intro z
      have : ((F z.1, F w),
              (stieltjes (supportElimMeasure (μn (φ n))) z.1,
                stieltjes (supportElimMeasure (μn (φ n))) w)) ∈ entourageProd u₁ u₂ := by
        exact ⟨hn₁ z, hn₂⟩
      exact hsub this
    -- Apply uniform continuity of subtraction on `ℂ × ℂ`.
    have hsub : UniformContinuous fun p : ℂ × ℂ => p.1 - p.2 := uniformContinuous_sub
    have h := hsub.comp_tendstoUniformly hpair
    simpa [Function.comp] using h
  -- Replace the Stieltjes differences by kernel differences using Step 77.
  have hcongr :
      (fun n => fun z : KmHT m =>
            (∫ t, (z.1 : ℂ) * (1 / (1 - (z.1 : ℂ) * (t : ℂ)))
                ∂((μn (φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) -
              ∫ t, (w : ℂ) * (1 / (1 - (w : ℂ) * (t : ℂ)))
                ∂((μn (φ n)).restrict (Set.Icc (-1 : ℝ) 1)ᶜ)) =ᶠ[atTop]
        fun n => fun z : KmHT m =>
          stieltjes (supportElimMeasure (μn (φ n))) z.1 -
            stieltjes (supportElimMeasure (μn (φ n))) w := by
    refine Filter.Eventually.of_forall (fun n => ?_)
    funext z
    simpa using
      integral_mul_one_div_one_sub_mul_sub_eq_stieltjes_sub (μ := μn (φ n)) (hμ := hμfin n)
        (z := z.1) (w := w)
  exact (tendstoUniformly_congr hcongr).2 hStDiff

end

end Quantum.TraceInequality.Loewner
