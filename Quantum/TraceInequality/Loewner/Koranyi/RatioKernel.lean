import Quantum.TraceInequality.Loewner.Koranyi.PickLimit

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Instances.ENNReal.Lemmas


namespace Quantum.TraceInequality.Loewner

open scoped BigOperators
open scoped Topology
open scoped BoundedContinuousFunction
open scoped NNReal

open MeasureTheory Set Filter

noncomputable section

/-!
Step 8 (setup): ratio kernel on `ENNReal` (`[0,∞]`) for the integral representation route.

We isolate basic facts about the kernel
`ratioKernel x λ = x / (x + λ)` on `ENNReal`, namely boundedness and continuity in `λ`.

These lemmas are intended to be used with weak convergence of finite measures on a compact
space (here `ENNReal`) to pass to the limit under integrals of bounded continuous kernels.
-/

/-- The ratio kernel `x/(x+λ)` on `ENNReal`. -/
def ratioKernel (x l : ENNReal) : ENNReal :=
  x / (x + l)

lemma ratioKernel_def (x l : ENNReal) : ratioKernel x l = x / (x + l) := rfl

/-- The ratio kernel `x/(x+λ)` is bounded above by `1` on `ENNReal`. -/
lemma ratioKernel_le_one (x l : ENNReal) : ratioKernel x l ≤ 1 := by
  have hle : x ≤ x + l := le_add_of_nonneg_right (zero_le _)
  calc
    ratioKernel x l = x / (x + l) := rfl
    _ ≤ (x + l) / (x + l) := ENNReal.div_le_div_right hle _
    _ ≤ 1 := by
          simp


/-- For finite `x`, the ratio kernel is continuous in `λ` on `ENNReal`. -/
lemma continuous_ratioKernel (x : ENNReal) (hx : x ≠ ⊤) :
    Continuous fun l : ENNReal => ratioKernel x l := by
  -- Use `ENNReal.Tendsto.const_div` pointwise; multiplication is not globally continuous on
  -- `ENNReal`.
  refine continuous_iff_continuousAt.2 ?_
  intro l0
  have hden :
      Tendsto (fun l : ENNReal => x + l) (𝓝 l0) (𝓝 (x + l0)) :=
    (continuous_const.add continuous_id).tendsto l0
  -- `b ≠ ⊤ ∨ a ≠ ⊤` holds since `a = x ≠ ⊤`.
  simpa [ratioKernel] using
    (ENNReal.Tendsto.const_div (a := x) (m := fun l : ENNReal => x + l) hden (Or.inr hx))

/-- The Lebesgue integral of the ratio kernel is bounded by the total mass `μ univ`. -/
lemma lintegral_ratioKernel_le (μ : Measure ENNReal) (x : ENNReal) :
    ∫⁻ l, ratioKernel x l ∂μ ≤ μ univ := by
  have hle : (fun l => ratioKernel x l) ≤ fun _ => (1 : ENNReal) :=
    fun l => ratioKernel_le_one x l
  calc
    ∫⁻ l, ratioKernel x l ∂μ ≤ ∫⁻ _l, (1 : ENNReal) ∂μ := lintegral_mono hle
    _ = μ univ := by simp


/-- The ratio kernel never takes the value `⊤`. -/
lemma ratioKernel_ne_top (x l : ENNReal) : ratioKernel x l ≠ ⊤ := by
  exact ne_top_of_le_ne_top (by simp) (ratioKernel_le_one x l)

/-- For finite `x`, the `ℝ≥0`-valued ratio kernel is continuous in `λ`. -/
lemma continuous_ratioKernel_toNNReal (x : ENNReal) (hx : x ≠ ⊤) :
    Continuous fun l : ENNReal => (ratioKernel x l).toNNReal := by
  refine continuous_iff_continuousAt.2 ?_
  intro l0
  have h0 : ratioKernel x l0 ≠ ⊤ := ratioKernel_ne_top x l0
  have ht_toNN :
      Tendsto ENNReal.toNNReal (𝓝 (ratioKernel x l0))
        (𝓝 (ratioKernel x l0).toNNReal) :=
    ENNReal.tendsto_toNNReal h0
  have ht_ratio :
      Tendsto (fun l : ENNReal => ratioKernel x l) (𝓝 l0)
        (𝓝 (ratioKernel x l0)) :=
    (continuous_ratioKernel x hx).tendsto l0
  exact ht_toNN.comp ht_ratio

/-- The ratio kernel as a bounded continuous nonnegative function on the compact space `ENNReal`. -/
def ratioKernelBCNN (x : ENNReal) (hx : x ≠ ⊤) : ENNReal →ᵇ ℝ≥0 :=
  (ContinuousMap.equivBoundedOfCompact ENNReal ℝ≥0)
    ⟨fun l => (ratioKernel x l).toNNReal, continuous_ratioKernel_toNNReal x hx⟩

@[simp] lemma ratioKernelBCNN_apply (x : ENNReal) (hx : x ≠ ⊤) (l : ENNReal) :
    ratioKernelBCNN x hx l = (ratioKernel x l).toNNReal := rfl

/-- Weak convergence of finite measures on `ENNReal` yields convergence of the integrals of the
bounded continuous ratio kernel. -/
theorem tendsto_testAgainstNN_ratioKernelBCNN {μs : ℕ → MeasureTheory.FiniteMeasure ENNReal}
    {μ : MeasureTheory.FiniteMeasure ENNReal} (ht : Tendsto μs atTop (𝓝 μ)) (x : ENNReal)
    (hx : x ≠ ⊤) :
    Tendsto (fun n => (μs n).testAgainstNN (ratioKernelBCNN x hx)) atTop
      (𝓝 (μ.testAgainstNN (ratioKernelBCNN x hx))) := by
  -- This is part of the definition of weak convergence of finite measures.
  have hall :=
    (MeasureTheory.FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto
      (μs := μs) (μ := μ)).1 ht
  exact hall (ratioKernelBCNN x hx)

end

end Quantum.TraceInequality.Loewner
