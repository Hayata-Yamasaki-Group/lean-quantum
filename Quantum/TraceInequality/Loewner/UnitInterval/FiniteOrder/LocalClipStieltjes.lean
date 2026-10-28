import Quantum.Analysis.Measure.Stieltjes
import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.LoewnerPosBasic
import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.ScaledWeight
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Chapter 20 local clip and Stieltjes absolutely-continuous comparison

This file contains the local clipped monotone extension and the Stieltjes
absolutely-continuous comparison lemmas used by the Hiai regularization route.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped Interval
open scoped ComplexOrder
open scoped MatrixOrder
open scoped NNReal
open scoped ENNReal

noncomputable section

/--
Clip a function to the interval `[a,b]`.  This is the local-to-global
monotone extension used to feed Mathlib's Stieltjes machinery, which expects a
globally monotone function.
-/
noncomputable def hiaiLocalClip (f : ℝ → ℝ) (a b y : ℝ) : ℝ :=
  f (min b (max a y))

/-- The clipped argument always lies in `[a,b]` when `a ≤ b`. -/
theorem hiaiLocalClip_arg_mem_Icc {a b y : ℝ} (hab : a ≤ b) :
    min b (max a y) ∈ Set.Icc a b := by
  exact ⟨le_min hab (le_max_left a y), min_le_left b (max a y)⟩

/-- The scalar clipping map is monotone. -/
theorem hiaiLocalClip_arg_mono {a b : ℝ} :
    Monotone (fun y : ℝ => min b (max a y)) := by
  intro y z hyz
  exact min_le_min le_rfl (max_le_max le_rfl hyz)

/-- A function monotone on `[a,b]` gives a globally monotone clipped extension. -/
theorem hiaiLocalClip_mono {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : MonotoneOn f (Set.Icc a b)) :
    Monotone (hiaiLocalClip f a b) := by
  intro y z hyz
  exact hf
    (hiaiLocalClip_arg_mem_Icc (a := a) (b := b) (y := y) hab)
    (hiaiLocalClip_arg_mem_Icc (a := a) (b := b) (y := z) hab)
    (hiaiLocalClip_arg_mono (a := a) (b := b) hyz)

/--
The clipped extension is uniformly bounded by the two endpoint values whenever
`f` is monotone on the clipped interval.  This is the domination input needed
for the scaled-weight differentiation-under-integral step.
-/
theorem hiaiLocalClip_abs_le_endpoint_max
    {f : ℝ → ℝ} {a b y : ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Set.Icc a b)) :
    |hiaiLocalClip f a b y| ≤ max |f a| |f b| := by
  let z := min b (max a y)
  have hz : z ∈ Set.Icc a b :=
    hiaiLocalClip_arg_mem_Icc (a := a) (b := b) (y := y) hab
  have hfa : f a ≤ f z := by
    exact hf ⟨le_rfl, hab⟩ hz hz.1
  have hfb : f z ≤ f b := by
    exact hf hz ⟨hab, le_rfl⟩ hz.2
  have hleft : -max |f a| |f b| ≤ f z := by
    have hmax : |f a| ≤ max |f a| |f b| := le_max_left _ _
    have hneg : -max |f a| |f b| ≤ -|f a| := neg_le_neg hmax
    exact hneg.trans ((neg_abs_le (f a)).trans hfa)
  have hright : f z ≤ max |f a| |f b| := by
    have hmax : |f b| ≤ max |f a| |f b| := le_max_right _ _
    exact hfb.trans ((le_abs_self (f b)).trans hmax)
  simpa [hiaiLocalClip, z] using abs_le.mpr ⟨hleft, hright⟩

/-- Inside the clipping interval, the clipped extension agrees with `f`. -/
theorem hiaiLocalClip_eq_on_Icc {f : ℝ → ℝ} {a b y : ℝ}
    (hy : y ∈ Set.Icc a b) :
    hiaiLocalClip f a b y = f y := by
  simp [hiaiLocalClip, max_eq_right hy.1, min_eq_right hy.2]

/-- On the open clipping interval, the clipped extension is eventually equal to `f`. -/
theorem hiaiLocalClip_eventuallyEq_nhds {f : ℝ → ℝ} {a b y : ℝ}
    (hy : y ∈ Set.Ioo a b) :
    hiaiLocalClip f a b =ᶠ[𝓝 y] f := by
  filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
  exact hiaiLocalClip_eq_on_Icc
    (f := f) (a := a) (b := b) (y := z) ⟨le_of_lt hz.1, le_of_lt hz.2⟩

/-- On the open clipping interval, the derivative of the clip equals `deriv f`. -/
theorem hiaiLocalClip_deriv_eq_on_Ioo {f : ℝ → ℝ} {a b y : ℝ}
    (hy : y ∈ Set.Ioo a b) :
    deriv (hiaiLocalClip f a b) y = deriv f y :=
  (hiaiLocalClip_eventuallyEq_nhds (f := f) (a := a) (b := b) hy).deriv_eq

/-- The clipped derivative agrees a.e. with `deriv f` on the open interval. -/
theorem hiaiLocalClip_deriv_ae_eq_on_open {f : ℝ → ℝ} {a b : ℝ} :
    deriv (hiaiLocalClip f a b) =ᵐ[volume.restrict (Set.Ioo a b)] deriv f := by
  filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume) measurableSet_Ioo] with y hy
  exact hiaiLocalClip_deriv_eq_on_Ioo (f := f) (a := a) (b := b) hy

/--
Integral form of `stieltjes_acPart_measure_le`: a nonnegative test
weight integrates no larger against the absolutely continuous derivative
measure than against the full Stieltjes measure.
-/
theorem stieltjes_acPart_integral_le_measure_integral {g w : ℝ → ℝ}
    (hg : Monotone g)
    (hw_nonneg : 0 ≤ᵐ[hg.stieltjesFunction.measure] w)
    (hw_int : Integrable w hg.stieltjesFunction.measure) :
    (∫ y, w y ∂(volume.withDensity (fun y : ℝ => ENNReal.ofReal (deriv g y)))) ≤
      ∫ y, w y ∂hg.stieltjesFunction.measure :=
  integral_mono_measure (stieltjes_acPart_measure_le hg) hw_nonneg hw_int

/--
The local clip associated to the Hiai regularization interval is globally
monotone under public Löwner positivity.
-/
theorem hiaiLocalClip_mono_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} {ε x : ℝ} (hε : 0 ≤ ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    Monotone (hiaiLocalClip f (x - ε) (x + ε)) := by
  have hab : x - ε ≤ x + ε := by linarith
  have hmono : MonotoneOn f (Set.Ioo (-1 : ℝ) 1) :=
    scalarMonotoneOn_Ioo_of_loewnerPosOnUnitInterval hpos
  have hsub : Set.Icc (x - ε) (x + ε) ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro y hy
    have hxleft : -1 + ε < x := hx.1
    have hxright : x < 1 - ε := hx.2
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  exact hiaiLocalClip_mono hab (hmono.mono hsub)

/--
Public Löwner positivity supplies the endpoint bound for the clipped function
on the regularization window.
-/
theorem hiaiLocalClip_abs_le_endpoint_max_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} {ε x y : ℝ} (hε : 0 ≤ ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    |hiaiLocalClip f (x - ε) (x + ε) y| ≤
      max |f (x - ε)| |f (x + ε)| := by
  have hab : x - ε ≤ x + ε := by linarith
  have hmono : MonotoneOn f (Set.Ioo (-1 : ℝ) 1) :=
    scalarMonotoneOn_Ioo_of_loewnerPosOnUnitInterval hpos
  have hsub : Set.Icc (x - ε) (x + ε) ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro z hz
    have hxleft : -1 + ε < x := hx.1
    have hxright : x < 1 - ε := hx.2
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  exact hiaiLocalClip_abs_le_endpoint_max
    (f := f) (a := x - ε) (b := x + ε) (y := y)
    hab (hmono.mono hsub)

/--
The public Löwner regularity already available in the definition gives
continuity of the clipped extension used in the Hiai regularization layer.
-/
theorem hiaiLocalClip_continuous_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} {ε x : ℝ} (hε : 0 ≤ ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    Continuous (hiaiLocalClip f (x - ε) (x + ε)) := by
  have hfIoo : ContinuousOn f (Set.Ioo (-1 : ℝ) 1) :=
    hpos.differentiable.continuousOn
  have hsub : Set.Icc (x - ε) (x + ε) ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro y hy
    exact ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩
  have hfIcc : ContinuousOn f (Set.Icc (x - ε) (x + ε)) :=
    hfIoo.mono hsub
  have hclip_arg :
      Continuous (fun y : ℝ => min (x + ε) (max (x - ε) y)) := by
    fun_prop
  have hmaps :
      ∀ y : ℝ, min (x + ε) (max (x - ε) y) ∈ Set.Icc (x - ε) (x + ε) := by
    intro y
    exact hiaiLocalClip_arg_mem_Icc (a := x - ε) (b := x + ε) (y := y)
      (by linarith)
  simpa [hiaiLocalClip, Function.comp_def] using
    hfIcc.comp_continuous hclip_arg hmaps

/-- The clipped extension is a.e. strongly measurable under public Löwner positivity. -/
theorem hiaiLocalClip_aestronglyMeasurable_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} {ε x : ℝ} (hε : 0 ≤ ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    AEStronglyMeasurable (hiaiLocalClip f (x - ε) (x + ε)) volume :=
  (hiaiLocalClip_continuous_of_loewnerPosOnUnitInterval
    (f := f) hε hx hpos).aestronglyMeasurable

end

end Quantum.TraceInequality.Loewner
