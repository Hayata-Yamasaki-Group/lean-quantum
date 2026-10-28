import Quantum.TraceInequality.Loewner.UnitInterval.IntegralToOperatorMonotone

/-!
# Hiai's sign convention for the normalized interval representation

Hiai's interval formula uses the kernel `x / (1 - t * x)`.  The Loewner integral representation
uses the equivalent convention `x / (1 + lambda * x)`.  The two are
identified by the sign change `lambda = -t`.
-/

namespace Quantum
namespace TraceInequality
namespace Loewner

open Set MeasureTheory

noncomputable section

/-- Hiai's normalized interval kernel `x / (1 - t x)`. -/
def hiaiUnitIntervalKernel (t x : ℝ) : ℝ :=
  x / (1 - t * x)

/-- Hiai's kernel is the project kernel after the sign change `lambda = -t`. -/
theorem hiaiUnitIntervalKernel_eq_unitIntervalOperatorKernel_neg (t x : ℝ) :
    hiaiUnitIntervalKernel t x = unitIntervalOperatorKernel (-t) x := by
  simp [hiaiUnitIntervalKernel, unitIntervalOperatorKernel, sub_eq_add_neg, mul_comm]

/--
Hiai's normalized interval integral representation.

The measure is represented as a finite Borel measure on `ℝ` supported on
`[-1,1]`; the displayed formula follows Hiai's sign convention.
-/
structure HiaiUnitIntervalIntegralRep (f : ℝ → ℝ) where
  /-- Simon Ch.3 [simon2019]: Hiai's finite representing measure. -/
  μ : FiniteMeasure ℝ
  /-- Simon Ch.3 [simon2019]: the representing measure is supported on `[-1,1]`. -/
  support : (μ : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0
  /-- Simon Ch.3 [simon2019]: Hiai's signed-kernel interval formula. -/
  formula :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (-1 : ℝ) 1 →
      (f x : ℂ) =
        (f 0 : ℂ) +
          ∫ t : ℝ, ((x : ℂ) / (1 - (t : ℂ) * x)) ∂(μ : Measure ℝ)

private def reflectedIntervalMeasure (μ : FiniteMeasure ℝ) : FiniteMeasure ℝ :=
  μ.map fun t : ℝ => -t

private theorem reflectedIntervalMeasure_support_Icc
    (μ : FiniteMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0) :
    (reflectedIntervalMeasure μ : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
  have hS : MeasurableSet ((Set.Icc (-1 : ℝ) 1)ᶜ) :=
    isClosed_Icc.measurableSet.compl
  have hpre :
      (fun t : ℝ => -t) ⁻¹' (Set.Icc (-1 : ℝ) 1)ᶜ =
        (Set.Icc (-1 : ℝ) 1)ᶜ := by
    ext t
    constructor
    · intro ht hmem
      exact ht ⟨by linarith [hmem.2], by linarith [hmem.1]⟩
    · intro ht hmem
      exact ht ⟨by linarith [hmem.2], by linarith [hmem.1]⟩
  rw [reflectedIntervalMeasure, FiniteMeasure.toMeasure_map,
    Measure.map_apply measurable_neg hS, hpre, hμ]

private theorem reflectedIntervalMeasure_integral_hiai_kernel
    (μ : FiniteMeasure ℝ) (x : ℝ) :
    (∫ t : ℝ, ((x : ℂ) / (1 - (t : ℂ) * x))
        ∂(reflectedIntervalMeasure μ : Measure ℝ)) =
      ∫ t : ℝ, ((x : ℂ) / (1 + (t : ℂ) * x)) ∂(μ : Measure ℝ) := by
  have hmeas :
      AEStronglyMeasurable
        (fun t : ℝ => ((x : ℂ) / (1 - (t : ℂ) * x)))
        (Measure.map (fun t : ℝ => -t) (μ : Measure ℝ)) := by
    have h : Measurable fun t : ℝ => ((x : ℂ) / (1 - (t : ℂ) * x)) := by
      measurability
    exact h.aestronglyMeasurable
  have hmap :=
    MeasureTheory.integral_map (μ := (μ : Measure ℝ))
      (φ := fun t : ℝ => -t) measurable_neg.aemeasurable
      (f := fun t : ℝ => ((x : ℂ) / (1 - (t : ℂ) * x))) hmeas
  calc
    (∫ t : ℝ, ((x : ℂ) / (1 - (t : ℂ) * x))
        ∂(reflectedIntervalMeasure μ : Measure ℝ)) =
        ∫ t : ℝ, ((x : ℂ) / (1 - ((-t : ℝ) : ℂ) * x))
          ∂(μ : Measure ℝ) := by
          simpa [reflectedIntervalMeasure] using hmap
    _ = ∫ t : ℝ, ((x : ℂ) / (1 + (t : ℂ) * x)) ∂(μ : Measure ℝ) := by
          refine integral_congr_ae ?_
          filter_upwards with t
          simp [sub_eq_add_neg, mul_comm]

/-- Convert the project convention to Hiai's sign convention. -/
def hiaiUnitIntervalIntegralRep_of_integralRepOnUnitInterval
    {f : ℝ → ℝ} (rep : IntegralRepOnUnitInterval f) :
    HiaiUnitIntervalIntegralRep f where
  μ := reflectedIntervalMeasure rep.ν
  support := reflectedIntervalMeasure_support_Icc rep.ν rep.support
  formula := by
    intro x hx
    rw [reflectedIntervalMeasure_integral_hiai_kernel rep.ν x]
    exact rep.formula hx

/-- Convert Hiai's sign convention back to the project convention. -/
def integralRepOnUnitInterval_of_hiaiUnitIntervalIntegralRep
    {f : ℝ → ℝ} (rep : HiaiUnitIntervalIntegralRep f) :
    IntegralRepOnUnitInterval f where
  ν := reflectedIntervalMeasure rep.μ
  support := reflectedIntervalMeasure_support_Icc rep.μ rep.support
  formula := by
    intro x hx
    have h :=
      reflectedIntervalMeasure_integral_hiai_kernel
        (reflectedIntervalMeasure rep.μ) x
    have hmap :
        (∫ t : ℝ, ((x : ℂ) / (1 - (t : ℂ) * x))
            ∂(reflectedIntervalMeasure (reflectedIntervalMeasure rep.μ) :
              Measure ℝ)) =
          ∫ t : ℝ, ((x : ℂ) / (1 + (t : ℂ) * x))
            ∂(reflectedIntervalMeasure rep.μ : Measure ℝ) := h
    have hdouble :
        reflectedIntervalMeasure (reflectedIntervalMeasure rep.μ) = rep.μ := by
      apply FiniteMeasure.toMeasure_injective
      change Measure.map (fun t : ℝ => -t)
          (Measure.map (fun t : ℝ => -t) (rep.μ : Measure ℝ)) =
        (rep.μ : Measure ℝ)
      rw [Measure.map_map measurable_neg measurable_neg]
      simp
    rw [← hmap, hdouble]
    exact rep.formula hx

/-- Hiai's interval representation is equivalent to the project convention. -/
theorem hiaiUnitIntervalIntegralRep_iff_integralRepOnUnitInterval
    {f : ℝ → ℝ} :
    Nonempty (HiaiUnitIntervalIntegralRep f) ↔
      Nonempty (IntegralRepOnUnitInterval f) := by
  constructor
  · rintro ⟨rep⟩
    exact ⟨integralRepOnUnitInterval_of_hiaiUnitIntervalIntegralRep rep⟩
  · rintro ⟨rep⟩
    exact ⟨hiaiUnitIntervalIntegralRep_of_integralRepOnUnitInterval rep⟩

end

end Loewner
end TraceInequality
end Quantum
