import Quantum.TraceInequality.Loewner.Koranyi.KoranyiKernelCayley
import Quantum.TraceInequality.Loewner.Koranyi.RatioFunctional

import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set Filter

open scoped NNReal
open scoped Topology

noncomputable section

/-!
Step 18 (bridge): pushing forward finite measures on `ℝ` to `ENNReal` via the Cayley transform.

This file packages a basic change-of-variables identity for the ratio-kernel functional after
mapping a finite measure `μ` on `ℝ` by the (measurable) map `t ↦ ENNReal.ofReal (cayley t)`.

The main use case is when `μ` is supported on `(-1,1)`, so that the pointwise identity from
`KoranyiKernelCayley` applies almost everywhere.
-/

/-- Cayley transform followed by coercion to `ENNReal`. -/
def cayleyENNReal (t : ℝ) : ENNReal :=
  ENNReal.ofReal (cayley t)

/-- The `ENNReal`-valued Cayley map is measurable. -/
lemma measurable_cayleyENNReal : Measurable cayleyENNReal := by
  -- `cayley` is a rational function, hence measurable; `ENNReal.ofReal` is measurable as well.
  have hnum : Measurable fun t : ℝ => (1 : ℝ) + t :=
    measurable_const.add measurable_id
  have hden : Measurable fun t : ℝ => (1 : ℝ) - t :=
    measurable_const.sub measurable_id
  have hc : Measurable fun t : ℝ => ((1 : ℝ) + t) / ((1 : ℝ) - t) :=
    hnum.div hden
  simpa [cayleyENNReal, cayley] using (ENNReal.measurable_ofReal.comp hc)

/-- Push forward a finite real measure by the `ENNReal`-valued Cayley map. -/
abbrev cayleyPushforward (μ : FiniteMeasure ℝ) : FiniteMeasure ENNReal :=
  μ.map cayleyENNReal

/-- The Cayley push-forward preserves total mass. -/
@[simp] lemma cayleyPushforward_mass (μ : FiniteMeasure ℝ) :
    (cayleyPushforward μ).mass = μ.mass := by
  -- `map` preserves total mass for measurable functions.
  -- Unfold `mass` and use the push-forward formula on `univ`.
  change (μ.map cayleyENNReal) univ = μ univ
  simpa using
    (MeasureTheory.FiniteMeasure.map_apply μ (measurable_cayleyENNReal)
      (A := Set.univ) (A_mble := MeasurableSet.univ))

/--
For measures supported on `(-1,1)`, the Cayley push-forward ratio functional is
the Koranyi-kernel `lintegral`.
-/
theorem ratioFunctional_cayleyPushforward_eq_lintegral_koranyiKernel
    (μ : FiniteMeasure ℝ) (hμ : (μ : Measure ℝ) (Set.Ioo (-1 : ℝ) 1)ᶜ = 0)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ((ratioFunctional (cayleyPushforward μ) (Real.toNNReal (cayley x))) : ENNReal) =
      ∫⁻ t, (Real.toNNReal (koranyiKernel x t) : ENNReal) ∂(μ : Measure ℝ) := by
  -- Expand `ratioFunctional` and change variables along the map `t ↦ ofReal (cayley t)`.
  have h_support : ∀ᵐ t ∂(μ : Measure ℝ), t ∈ Set.Ioo (-1 : ℝ) 1 :=
    MeasureTheory.mem_ae_iff.2 hμ
  -- Unfold `testAgainstNN` to a `lintegral` without rewriting `cayley` itself.
  let ν : FiniteMeasure ENNReal := cayleyPushforward μ
  let fKer : ENNReal → ENNReal :=
    fun l =>
      (ratioKernelBCNN ((Real.toNNReal (cayley x) : ℝ≥0) : ENNReal) (by simp) l : ENNReal)
  have hLHS :
      ((ratioFunctional ν (Real.toNNReal (cayley x))) : ENNReal) =
        ∫⁻ l, fKer l ∂(ν : Measure ENNReal) := by
    -- `ratioFunctional` is defined via `testAgainstNN`, which is a `lintegral` in `ENNReal`.
    -- Avoid `simp` on `cayley` (`cayley_def` is a simp lemma).
    simp only [ratioFunctional, fKer, MeasureTheory.FiniteMeasure.testAgainstNN_coe_eq]
  -- Pull back the `lintegral` along the map.
  have hfKer : Measurable fKer := by
    -- `ratioKernelBCNN` is continuous, hence measurable, and the coercion to `ENNReal`
    -- is continuous.
    exact
      (ENNReal.continuous_coe.comp
          (ratioKernelBCNN
            ((Real.toNNReal (cayley x) : ℝ≥0) : ENNReal)
            (by simp)).continuous).measurable
  have hmap :
      (∫⁻ l, fKer l ∂(ν : Measure ENNReal)) =
        ∫⁻ t, fKer (cayleyENNReal t) ∂(μ : Measure ℝ) := by
    -- `ν` is the push-forward measure by `cayleyENNReal`.
    simpa [ν, cayleyPushforward, MeasureTheory.FiniteMeasure.map, cayleyENNReal] using
      (MeasureTheory.lintegral_map (μ := (μ : Measure ℝ)) (f := fKer) (g := cayleyENNReal) hfKer
        measurable_cayleyENNReal)
  -- Replace the integrand using the pointwise identity from Step 16, on the support of `μ`.
  have hEq_ae :
      (fun t : ℝ => fKer (cayleyENNReal t)) =ᵐ[(μ : Measure ℝ)]
        fun t : ℝ => (Real.toNNReal (koranyiKernel x t) : ENNReal) := by
    filter_upwards [h_support] with t ht
    have h :=
      ratioKernelBCNN_ofReal_cayley_apply (x := x) (t := t) hx ht
    -- `cayleyENNReal t` is definitionaly `ENNReal.ofReal (cayley t)`, and `ENNReal.ofReal`
    -- is `Real.toNNReal` followed by coercion.
    have : fKer (cayleyENNReal t) = (Real.toNNReal (koranyiKernel x t) : ENNReal) := by
      -- Turn the Step16 identity into an equality in `ENNReal`.
      simpa [fKer, cayleyENNReal, ENNReal.ofReal] using
        congrArg (fun r : ℝ≥0 => (r : ENNReal)) h
    simpa using this
  -- Combine the map change-of-variables with the a.e. replacement.
  calc
    ((ratioFunctional ν (Real.toNNReal (cayley x))) : ENNReal) =
        ∫⁻ l, fKer l ∂(ν : Measure ENNReal) :=
      hLHS
    _ = ∫⁻ t, fKer (cayleyENNReal t) ∂(μ : Measure ℝ) := hmap
    _ = ∫⁻ t, (Real.toNNReal (koranyiKernel x t) : ENNReal) ∂(μ : Measure ℝ) :=
        MeasureTheory.lintegral_congr_ae hEq_ae


end

end Quantum.TraceInequality.Loewner
