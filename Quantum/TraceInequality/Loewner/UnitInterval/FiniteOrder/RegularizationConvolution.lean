import Quantum.Analysis.Calculus.EquicontinuousFamily
import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.IocUniformStep

/-!
# Chapter 20 Hiai regularization convolution layer

This file contains the value and derivative formulas that rewrite Hiai
regularization in the scaled-mollifier volume variables before the subsequent
Stieltjes comparison and kernel PSD arguments.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped Interval
open scoped ComplexOrder
open scoped MatrixOrder
open scoped NNReal
open scoped ENNReal
open scoped Convolution

noncomputable section

/--
Affine change of variables for the scaled mollifier weight:
`y = x - ε t` transforms the window integral back to the mollifier variable.
-/
theorem hiaiScaledMollifierWeight_volume_integral_comp_eq_intervalIntegral
    {φ g : ℝ → ℝ} {ε x : ℝ} (hε : 0 < ε) :
    (∫ y in x - ε..x + ε, hiaiScaledMollifierWeight φ ε x y * g y) =
      ∫ t in (-1 : ℝ)..1, φ t * g (x - ε * t) := by
  have hcomp :=
    intervalIntegral.integral_comp_sub_mul
      (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y * g y)
      hε.ne' x (a := (-1 : ℝ)) (b := 1)
  have hcomp_simp :
      (∫ t in (-1 : ℝ)..1,
          hiaiScaledMollifierWeight φ ε x (x - ε * t) * g (x - ε * t)) =
        ε⁻¹ * ∫ y in x - ε..x + ε,
          hiaiScaledMollifierWeight φ ε x y * g y := by
    simpa [one_mul, mul_neg, sub_neg_eq_add] using hcomp
  calc
    (∫ y in x - ε..x + ε, hiaiScaledMollifierWeight φ ε x y * g y)
        = ε * (∫ t in (-1 : ℝ)..1,
          hiaiScaledMollifierWeight φ ε x (x - ε * t) * g (x - ε * t)) := by
          rw [hcomp_simp]
          field_simp [hε.ne']
    _ = ∫ t in (-1 : ℝ)..1,
          ε * (hiaiScaledMollifierWeight φ ε x (x - ε * t) * g (x - ε * t)) := by
          simp
    _ = ∫ t in (-1 : ℝ)..1, φ t * g (x - ε * t) := by
          refine intervalIntegral.integral_congr ?_
          intro t ht
          change ε * (hiaiScaledMollifierWeight φ ε x (x - ε * t) *
              g (x - ε * t)) =
            φ t * g (x - ε * t)
          rw [hiaiScaledMollifierWeight_eq_shift
            (φ := φ) (ε := ε) (x := x) hε.ne']
          field_simp [hε.ne']

/--
The regularized value can be written as a Lebesgue convolution against the
scaled mollifier weight.  This is the value-side normal form needed before the
Stieltjes integration-by-parts step
(`hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_closed`).
-/
theorem hiaiRegularization_eq_scaledWeight_volume_integral
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) :
    hiaiRegularization φ ε f x =
      ∫ y, hiaiScaledMollifierWeight φ ε x y * f y := by
  calc
    hiaiRegularization φ ε f x
        = ∫ t in (-1 : ℝ)..1, φ t * f (x - ε * t) := rfl
    _ = ∫ y in x - ε..x + ε,
          hiaiScaledMollifierWeight φ ε x y * f y := by
          exact (hiaiScaledMollifierWeight_volume_integral_comp_eq_intervalIntegral
            (φ := φ) (g := f) (ε := ε) (x := x) hε).symm
    _ = ∫ y, hiaiScaledMollifierWeight φ ε x y * f y := by
          exact (hiaiScaledMollifierWeight_volume_integral_eq_window
            (φ := φ) (g := f) hφ hε).symm

/--
If the scaled-weight convolution is differentiable in the center variable, then
the same derivative is the derivative of the Hiai regularization.
-/
theorem hiaiRegularization_hasDerivAt_from_scaledWeight
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x D : ℝ} (hε : 0 < ε)
    (hderiv :
      HasDerivAt
        (fun z : ℝ => ∫ y, hiaiScaledMollifierWeight φ ε z y * f y)
        D x) :
    HasDerivAt (fun z : ℝ => hiaiRegularization φ ε f z) D x := by
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards with z
  exact (hiaiRegularization_eq_scaledWeight_volume_integral
    (φ := φ) (f := f) (x := z) hφ hε)

/--
The same scaled-weight value formula for the clipped extension used by the
Stieltjes measure.  This keeps the final integration-by-parts comparison in the
same variables as the clipped monotone function.
-/
theorem hiaiRegularization_localClip_eq_scaledWeight_volume_integral
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) :
    hiaiRegularization φ ε (hiaiLocalClip f (x - ε) (x + ε)) x =
      ∫ y, hiaiScaledMollifierWeight φ ε x y *
        hiaiLocalClip f (x - ε) (x + ε) y :=
  hiaiRegularization_eq_scaledWeight_volume_integral
    (φ := φ) (f := hiaiLocalClip f (x - ε) (x + ε)) hφ hε

/--
If the scaled-weight convolution of the clipped function is differentiable in
the center variable, then the same derivative is the derivative of the Hiai
regularization of the clipped function.  This is only a congruence wrapper around
the closed scaled-weight value formula.
-/
theorem hiaiRegularization_localClip_hasDerivAt_from_scaledWeight
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x D : ℝ} (hε : 0 < ε)
    (hderiv :
      HasDerivAt
        (fun z : ℝ =>
          ∫ y, hiaiScaledMollifierWeight φ ε z y *
            hiaiLocalClip f (x - ε) (x + ε) y)
        D x) :
    HasDerivAt
      (fun z : ℝ =>
        hiaiRegularization φ ε (hiaiLocalClip f (x - ε) (x + ε)) z)
      D x := by
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards with z
  exact (hiaiRegularization_eq_scaledWeight_volume_integral
    (φ := φ) (f := hiaiLocalClip f (x - ε) (x + ε))
    (x := z) hφ hε)

/--
Standard dominated-differentiation input for the scaled-weight convolution of
the clipped function.  This replaces the opaque `hderiv` hypothesis by the
usual Mathlib measurable/integrable/bound package; the genuine public task is
to supply these domination assumptions from the Hiai mollifier and the clipped
monotone function.
-/
theorem hiaiRegularization_localClip_hasDerivAt_scaledWeight_of_dominated
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 x)
    {bound : ℝ → ℝ}
    (hF_meas : ∀ᶠ z in 𝓝 x,
      AEStronglyMeasurable
        (fun y : ℝ =>
          hiaiScaledMollifierWeight φ ε z y *
            hiaiLocalClip f (x - ε) (x + ε) y) volume)
    (hF_int :
      Integrable
        (fun y : ℝ =>
          hiaiScaledMollifierWeight φ ε x y *
            hiaiLocalClip f (x - ε) (x + ε) y) volume)
    (hF'_meas :
      AEStronglyMeasurable
        (fun y : ℝ =>
          deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x *
            hiaiLocalClip f (x - ε) (x + ε) y) volume)
    (h_bound :
      ∀ᵐ y ∂volume, ∀ z ∈ s,
        ‖deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) z *
            hiaiLocalClip f (x - ε) (x + ε) y‖ ≤ bound y)
    (bound_integrable : Integrable bound volume) :
    HasDerivAt
      (fun z : ℝ =>
        ∫ y, hiaiScaledMollifierWeight φ ε z y *
          hiaiLocalClip f (x - ε) (x + ε) y)
      (∫ y,
        deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x *
          hiaiLocalClip f (x - ε) (x + ε) y)
      x := by
  have h_diff :
      ∀ᵐ y ∂volume, ∀ z ∈ s,
        HasDerivAt
          (fun z : ℝ =>
            hiaiScaledMollifierWeight φ ε z y *
              hiaiLocalClip f (x - ε) (x + ε) y)
          (deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) z *
            hiaiLocalClip f (x - ε) (x + ε) y)
          z := by
    filter_upwards with y z _hz
    have hW :=
      hiaiScaledMollifierWeight_hasDerivAt_x
        (φ := φ) (ε := ε) (x := z) (y := y) hφ
    simpa [hiaiScaledMollifierWeight_deriv_x (φ := φ) hφ] using
      hW.mul_const (hiaiLocalClip f (x - ε) (x + ε) y)
  exact
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume)
      (F := fun z y : ℝ =>
        hiaiScaledMollifierWeight φ ε z y *
          hiaiLocalClip f (x - ε) (x + ε) y)
      (F' := fun z y : ℝ =>
        deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) z *
          hiaiLocalClip f (x - ε) (x + ε) y)
      (x₀ := x) (s := s) (bound := bound)
      hs hF_meas hF_int hF'_meas h_bound bound_integrable h_diff).2

/--
Derivative formula for the regularization of the clipped function, conditional
on the corresponding differentiation-under-the-scaled-weight-integral
statement.  This keeps the analytic domination assumptions explicit; under
public Löwner positivity they are supplied in
`hiaiRegularization_clippedStieltjesConvolution_le_diagKernel_of_publicDomination`
(`ClippedComparison.lean`).
-/
theorem hiaiRegularization_localClip_deriv_eq_scaledWeight_xDeriv_integral
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hderiv :
      HasDerivAt
        (fun z : ℝ =>
          ∫ y, hiaiScaledMollifierWeight φ ε z y *
            hiaiLocalClip f (x - ε) (x + ε) y)
        (∫ y,
          deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x *
            hiaiLocalClip f (x - ε) (x + ε) y)
        x) :
    deriv
      (fun z : ℝ =>
        hiaiRegularization φ ε (hiaiLocalClip f (x - ε) (x + ε)) z)
      x =
      ∫ y,
        deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x *
          hiaiLocalClip f (x - ε) (x + ε) y :=
  (hiaiRegularization_localClip_hasDerivAt_from_scaledWeight
    (φ := φ) (f := f) hφ hε hderiv).deriv

/--
Derivative formula for the clipped regularization obtained from the standard
dominated-differentiation package.  This is the same conclusion as the
previous conditional formula, but the analytic input is now measurable /
integrable domination rather than a prepackaged derivative of the integral.
-/
theorem
    hiaiRegularization_localClip_deriv_eq_scaledWeight_xDeriv_integral_of_dominated
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) {s : Set ℝ} (hs : s ∈ 𝓝 x)
    {bound : ℝ → ℝ}
    (hF_meas : ∀ᶠ z in 𝓝 x,
      AEStronglyMeasurable
        (fun y : ℝ =>
          hiaiScaledMollifierWeight φ ε z y *
            hiaiLocalClip f (x - ε) (x + ε) y) volume)
    (hF_int :
      Integrable
        (fun y : ℝ =>
          hiaiScaledMollifierWeight φ ε x y *
            hiaiLocalClip f (x - ε) (x + ε) y) volume)
    (hF'_meas :
      AEStronglyMeasurable
        (fun y : ℝ =>
          deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x *
            hiaiLocalClip f (x - ε) (x + ε) y) volume)
    (h_bound :
      ∀ᵐ y ∂volume, ∀ z ∈ s,
        ‖deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) z *
            hiaiLocalClip f (x - ε) (x + ε) y‖ ≤ bound y)
    (bound_integrable : Integrable bound volume) :
    deriv
      (fun z : ℝ =>
        hiaiRegularization φ ε (hiaiLocalClip f (x - ε) (x + ε)) z)
      x =
      ∫ y,
        deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x *
          hiaiLocalClip f (x - ε) (x + ε) y := by
  exact hiaiRegularization_localClip_deriv_eq_scaledWeight_xDeriv_integral
    (φ := φ) (f := f) hφ hε
    (hiaiRegularization_localClip_hasDerivAt_scaledWeight_of_dominated
      (φ := φ) (f := f) hφ hs hF_meas hF_int hF'_meas h_bound bound_integrable)

/-- Under Löwner positivity of `f`, the Chapter-20 Hiai regularization of `f` is differentiable at
interior points, with derivative the integral of the center-derivative of the scaled mollifier
weight against `f`. [simon2019] -/
theorem
    regularization_original_hasDerivAt_scaledWeight_of_loewnerPos
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    HasDerivAt
      (fun z : ℝ => hiaiRegularization φ ε f z)
      (∫ y,
        deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x * f y)
      x := by
  obtain ⟨s, bound, hs, hssub, h_bound, bound_integrable⟩ :=
    hiaiRegularization_original_xDeriv_publicBoundData
      (φ := φ) (f := f) hφ hε hx hpos
  have hscaled :
      HasDerivAt
        (fun z : ℝ => ∫ y, hiaiScaledMollifierWeight φ ε z y * f y)
        (∫ y,
          deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x * f y)
        x := by
    have hF_meas : ∀ᶠ z in 𝓝 x,
        AEStronglyMeasurable
          (fun y : ℝ => hiaiScaledMollifierWeight φ ε z y * f y) volume := by
      filter_upwards [hs] with z hz
      exact
        hiaiScaledMollifierWeight_original_aestronglyMeasurable_of_loewnerPosOnUnitInterval
          (φ := φ) (f := f) hφ hε (hssub hz) hpos
    have hF_int :
        Integrable
          (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y * f y) volume :=
      hiaiScaledMollifierWeight_original_integrable_of_loewnerPosOnUnitInterval
        (φ := φ) (f := f) hφ hε hx hpos
    have hF'_meas :
        AEStronglyMeasurable
          (fun y : ℝ =>
            deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x *
              f y) volume :=
      scaledMollifierWeight_xDeriv_original_aestronglyMeasurable_of_loewnerPos
        (φ := φ) (f := f) hφ hε hx hpos
    have h_diff :
        ∀ᵐ y ∂volume, ∀ z ∈ s,
          HasDerivAt
            (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y * f y)
            (deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) z *
              f y)
            z := by
      filter_upwards with y z _hz
      have hW :=
        hiaiScaledMollifierWeight_hasDerivAt_x
          (φ := φ) (ε := ε) (x := z) (y := y) hφ
      simpa [hiaiScaledMollifierWeight_deriv_x (φ := φ) hφ] using
        hW.mul_const (f y)
    exact
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (μ := volume)
        (F := fun z y : ℝ => hiaiScaledMollifierWeight φ ε z y * f y)
        (F' := fun z y : ℝ =>
          deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) z *
            f y)
        (x₀ := x) (s := s) (bound := bound)
        hs hF_meas hF_int hF'_meas h_bound bound_integrable h_diff).2
  exact hiaiRegularization_hasDerivAt_from_scaledWeight
    (φ := φ) (f := f) hφ hε hscaled

/-- The derivative of the Chapter-20 Hiai regularization of a Löwner-positive `f` at an interior
point equals the integral of the center-derivative of the scaled mollifier weight against `f`.
[simon2019] -/
theorem
    hiaiRegularization_original_deriv_eq_scaledWeight_xDeriv_integral
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    deriv (fun z : ℝ => hiaiRegularization φ ε f z) x =
      ∫ y,
        deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x * f y :=
  (regularization_original_hasDerivAt_scaledWeight_of_loewnerPos
    (φ := φ) (f := f) hφ hε hx hpos).deriv

/--
Affine change of variables for the center-derivative of the scaled weight.
The extra `ε⁻¹` is the derivative of the scaled kernel in the center variable.
-/
theorem hiaiScaledMollifierWeight_xDeriv_volume_integral_comp_eq_intervalIntegral
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) :
    (∫ y in x - ε..x + ε,
        deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x * g y) =
      ∫ t in (-1 : ℝ)..1, deriv φ t * (g (x - ε * t) / ε) := by
  let F : ℝ → ℝ := fun y =>
    deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x * g y
  have hcomp :=
    intervalIntegral.integral_comp_sub_mul
      F hε.ne' x (a := (-1 : ℝ)) (b := 1)
  have hcomp_simp :
      (∫ t in (-1 : ℝ)..1, F (x - ε * t)) =
        ε⁻¹ * ∫ y in x - ε..x + ε, F y := by
    simpa [F, one_mul, mul_neg, sub_neg_eq_add] using hcomp
  calc
    (∫ y in x - ε..x + ε,
        deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x * g y)
        = ∫ y in x - ε..x + ε, F y := rfl
    _ = ε * (∫ t in (-1 : ℝ)..1, F (x - ε * t)) := by
          rw [hcomp_simp]
          field_simp [hε.ne']
    _ = ∫ t in (-1 : ℝ)..1, ε * F (x - ε * t) := by
          simp
    _ = ∫ t in (-1 : ℝ)..1, deriv φ t * (g (x - ε * t) / ε) := by
          refine intervalIntegral.integral_congr ?_
          intro t _ht
          have harg : (x - (x - ε * t)) / ε = t := by
            field_simp [hε.ne']
            ring
          dsimp [F]
          rw [hiaiScaledMollifierWeight_deriv_x
            (φ := φ) (ε := ε) (x := x) (y := x - ε * t) hφ, harg]
          field_simp [hε.ne']

/--
The regularized derivative in mollifier variables, normalized as an integral of
the difference quotient at the base point.
-/
theorem hiaiRegularization_deriv_eq_deriv_mollifier_diffQuot_integral
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    deriv (fun z : ℝ => hiaiRegularization φ ε f z) x =
      ∫ t in (-1 : ℝ)..1,
        deriv φ t * ((f (x - ε * t) - f x) / ε) := by
  have hraw :
      deriv (fun z : ℝ => hiaiRegularization φ ε f z) x =
        ∫ t in (-1 : ℝ)..1, deriv φ t * (f (x - ε * t) / ε) := by
    calc
      deriv (fun z : ℝ => hiaiRegularization φ ε f z) x
          = ∫ y,
              deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x *
                f y :=
            hiaiRegularization_original_deriv_eq_scaledWeight_xDeriv_integral
              (φ := φ) (f := f) hφ hε hx hpos
      _ = ∫ y in x - ε..x + ε,
              deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x *
                f y :=
            hiaiScaledMollifierWeight_xDeriv_volume_integral_eq_window
              (φ := φ) (g := f) hφ hε
      _ = ∫ t in (-1 : ℝ)..1, deriv φ t * (f (x - ε * t) / ε) :=
            hiaiScaledMollifierWeight_xDeriv_volume_integral_comp_eq_intervalIntegral
              (φ := φ) (g := f) hφ hε
  have hmap :
      Set.MapsTo (fun t : ℝ => x - ε * t) (Set.Icc (-1 : ℝ) 1)
        (Set.Ioo (-1 : ℝ) 1) := by
    intro t ht
    have hlow_mul : -ε ≤ ε * t := by
      have h := mul_le_mul_of_nonneg_left ht.1 hε.le
      simpa using h
    have hhigh_mul : ε * t ≤ ε := by
      have h := mul_le_mul_of_nonneg_left ht.2 hε.le
      simpa using h
    dsimp [hiaiRegularizedInterior] at hx
    constructor
    · linarith [hx.1, hhigh_mul]
    · linarith [hx.2, hlow_mul]
  have harg_cont :
      ContinuousOn (fun t : ℝ => x - ε * t) (Set.Icc (-1 : ℝ) 1) := by
    fun_prop
  have hfcomp_cont :
      ContinuousOn (fun t : ℝ => f (x - ε * t)) (Set.Icc (-1 : ℝ) 1) :=
    hpos.differentiable.continuousOn.comp harg_cont hmap
  have hderivφ_cont : Continuous (deriv φ) :=
    hφ.smooth.continuous_deriv (by simp [loewnerBookSmoothOrder])
  have hInt_main :
      IntervalIntegrable
        (fun t : ℝ => deriv φ t * (f (x - ε * t) / ε))
        volume (-1 : ℝ) 1 :=
    by
      have hcont :
          ContinuousOn
            (fun t : ℝ => deriv φ t * (f (x - ε * t) / ε))
            [[(-1 : ℝ), 1]] := by
        simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using
          (hderivφ_cont.continuousOn.mul (hfcomp_cont.div_const ε))
      exact hcont.intervalIntegrable
  have hInt_const :
      IntervalIntegrable
        (fun t : ℝ => deriv φ t * (f x / ε))
        volume (-1 : ℝ) 1 :=
    by
      have hcont :
          ContinuousOn
            (fun t : ℝ => deriv φ t * (f x / ε))
            [[(-1 : ℝ), 1]] := by
        simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using
          (hderivφ_cont.continuousOn.mul continuous_const.continuousOn)
      exact hcont.intervalIntegrable
  rw [hraw]
  calc
    (∫ t in (-1 : ℝ)..1, deriv φ t * (f (x - ε * t) / ε))
        = (∫ t in (-1 : ℝ)..1,
            deriv φ t * (f (x - ε * t) / ε) -
              deriv φ t * (f x / ε)) := by
          rw [intervalIntegral.integral_sub hInt_main hInt_const]
          rw [intervalIntegral.integral_mul_const,
            hiaiMollifier_integral_deriv_eq_zero hφ]
          ring
    _ = ∫ t in (-1 : ℝ)..1,
          deriv φ t * ((f (x - ε * t) - f x) / ε) := by
          refine intervalIntegral.integral_congr ?_
          intro t _ht
          ring

/--
Pointwise convergence of the derivatives of the Hiai regularizations.  The
proof uses the scaled-weight derivative formula only after rewriting it as a
fixed-interval integral of difference quotients.
-/
theorem regularized_deriv_tendsto_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      Tendsto
        (fun ε : ℝ =>
          deriv (fun z : ℝ => hiaiRegularization φ ε f z) x)
        (𝓝[>] (0 : ℝ)) (𝓝 (deriv f x)) := by
  intro x hx
  let F : ℝ → ℝ → ℝ := fun ε t =>
    deriv φ t * ((f (x - ε * t) - f x) / ε)
  let limitF : ℝ → ℝ := fun t => deriv φ t * ((-t) * deriv f x)
  let bound : ℝ → ℝ := fun t => |deriv φ t| * (|deriv f x| + 1)
  let ρ : ℝ := min (x + 1) (1 - x) / 2
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    have hleft : 0 < x + 1 := by linarith [hx.1]
    have hright : 0 < 1 - x := by linarith [hx.2]
    positivity
  have hsmallρ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ρ :=
    (eventually_lt_nhds hρpos).filter_mono nhdsWithin_le_nhds
  have hderivφ_cont : Continuous (deriv φ) :=
    hφ.smooth.continuous_deriv (by simp [loewnerBookSmoothOrder])
  have hAt : HasDerivAt f (deriv f x) x :=
    (differentiableAt_of_loewnerPosOnUnitInterval hpos hx).hasDerivAt
  rcases diffQuot_abs_le_eventually_uniform_Icc hAt with
    ⟨δ, hδpos, hδbound⟩
  have hsmallδ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < δ :=
    (eventually_lt_nhds hδpos).filter_mono nhdsWithin_le_nhds
  have hbound_int : IntervalIntegrable bound volume (-1 : ℝ) 1 := by
    have hcont : Continuous bound := by
      dsimp [bound]
      fun_prop
    exact hcont.continuousOn.intervalIntegrable
  have hF_meas :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        AEStronglyMeasurable (F ε) (volume.restrict (Ι (-1 : ℝ) 1)) := by
    filter_upwards [self_mem_nhdsWithin, hsmallρ] with ε hεpos_mem hερ
    have hεpos : 0 < ε := hεpos_mem
    have hmap :
        Set.MapsTo (fun t : ℝ => x - ε * t) (Set.Icc (-1 : ℝ) 1)
          (Set.Ioo (-1 : ℝ) 1) := by
      intro t ht
      have hlow_mul : -ε ≤ ε * t := by
        have h := mul_le_mul_of_nonneg_left ht.1 hεpos.le
        simpa using h
      have hhigh_mul : ε * t ≤ ε := by
        have h := mul_le_mul_of_nonneg_left ht.2 hεpos.le
        simpa using h
      have hρ_le_left : ρ ≤ x + 1 := by
        dsimp [ρ]
        have hhalf : min (x + 1) (1 - x) / 2 ≤ (x + 1) / 2 := by
          exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
        have hleft_pos : 0 < x + 1 := by linarith [hx.1]
        linarith
      have hρ_le_right : ρ ≤ 1 - x := by
        dsimp [ρ]
        have hhalf : min (x + 1) (1 - x) / 2 ≤ (1 - x) / 2 := by
          exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
        have hright_pos : 0 < 1 - x := by linarith [hx.2]
        linarith
      constructor
      · linarith
      · linarith
    have harg_cont :
        ContinuousOn (fun t : ℝ => x - ε * t) (Set.Icc (-1 : ℝ) 1) := by
      fun_prop
    have hfcomp_cont :
        ContinuousOn (fun t : ℝ => f (x - ε * t)) (Set.Icc (-1 : ℝ) 1) :=
      hpos.differentiable.continuousOn.comp harg_cont hmap
    have hcontIcc : ContinuousOn (F ε) (Set.Icc (-1 : ℝ) 1) := by
      dsimp [F]
      exact hderivφ_cont.continuousOn.mul
        ((hfcomp_cont.sub continuous_const.continuousOn).div_const ε)
    have hcontIoc : ContinuousOn (F ε) (Ι (-1 : ℝ) 1) := by
      refine hcontIcc.mono ?_
      intro t ht
      have htIoc : t ∈ Set.Ioc (-1 : ℝ) 1 := by
        simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
      exact ⟨le_of_lt htIoc.1, htIoc.2⟩
    exact hcontIoc.aestronglyMeasurable
      (by
        rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        exact measurableSet_Ioc)
  have h_bound :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ∀ᵐ t ∂volume, t ∈ Ι (-1 : ℝ) 1 → ‖F ε t‖ ≤ bound t := by
    filter_upwards [self_mem_nhdsWithin, hsmallδ] with ε hεpos_mem hεδ
    have hεpos : 0 < ε := hεpos_mem
    filter_upwards with t ht
    have htIoc : t ∈ Set.Ioc (-1 : ℝ) 1 := by
      simpa [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt htIoc.1, htIoc.2⟩
    have hq := hδbound hεpos hεδ htIcc
    dsimp [F, bound]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hq (abs_nonneg _)
  have h_lim :
      ∀ᵐ t ∂volume, t ∈ Ι (-1 : ℝ) 1 →
        Tendsto (fun ε : ℝ => F ε t) (𝓝[>] (0 : ℝ)) (𝓝 (limitF t)) := by
    filter_upwards with t _ht
    dsimp [F, limitF]
    exact (diffQuot_tendsto_deriv_mul_neg
      (f := f) (x := x) (D := deriv f x) (t := t) hAt).const_mul (deriv φ t)
  have hDCT :
      Tendsto
        (fun ε : ℝ => ∫ t in (-1 : ℝ)..1, F ε t)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ t in (-1 : ℝ)..1, limitF t)) := by
    exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := (-1 : ℝ)) (b := 1)
      (F := F) (f := limitF) bound hF_meas h_bound hbound_int h_lim
  have hlimit_eval :
      (∫ t in (-1 : ℝ)..1, limitF t) = deriv f x := by
    calc
      (∫ t in (-1 : ℝ)..1, limitF t)
          = ∫ t in (-1 : ℝ)..1, (deriv φ t * (-t)) * deriv f x := by
              refine intervalIntegral.integral_congr ?_
              intro t _ht
              dsimp [limitF]
              ring
      _ = (∫ t in (-1 : ℝ)..1, deriv φ t * (-t)) * deriv f x := by
              rw [intervalIntegral.integral_mul_const]
      _ = deriv f x := by
              rw [hiaiMollifier_integral_deriv_mul_neg_id_eq_one hφ]
              ring
  have hDCT' :
      Tendsto
        (fun ε : ℝ => ∫ t in (-1 : ℝ)..1, F ε t)
        (𝓝[>] (0 : ℝ)) (𝓝 (deriv f x)) := by
    simpa [hlimit_eval] using hDCT
  have heq :
      (fun ε : ℝ =>
        deriv (fun z : ℝ => hiaiRegularization φ ε f z) x) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun ε : ℝ => ∫ t in (-1 : ℝ)..1, F ε t) := by
    filter_upwards [self_mem_nhdsWithin, hsmallρ] with ε hεpos_mem hερ
    have hεpos : 0 < ε := hεpos_mem
    have hxreg : x ∈ hiaiRegularizedInterior ε := by
      have hρ_le_left : ρ ≤ x + 1 := by
        dsimp [ρ]
        have hhalf : min (x + 1) (1 - x) / 2 ≤ (x + 1) / 2 := by
          exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
        have hleft_pos : 0 < x + 1 := by linarith [hx.1]
        linarith
      have hρ_le_right : ρ ≤ 1 - x := by
        dsimp [ρ]
        have hhalf : min (x + 1) (1 - x) / 2 ≤ (1 - x) / 2 := by
          exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
        have hright_pos : 0 < 1 - x := by linarith [hx.2]
        linarith
      dsimp [hiaiRegularizedInterior]
      constructor <;> linarith
    exact hiaiRegularization_deriv_eq_deriv_mollifier_diffQuot_integral
      (φ := φ) (f := f) hφ hεpos hxreg hpos
  exact Filter.Tendsto.congr' heq.symm hDCT'

/--
Inside the support window, replacing `f` by its local clip does not change the
scaled-weight `x`-derivative integrand, up to a.e. equality.
-/
theorem hiaiScaledMollifierWeight_xDeriv_localClip_eq_original_ae
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) :
    (fun y : ℝ =>
        deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x *
          hiaiLocalClip f (x - ε) (x + ε) y) =ᵐ[volume]
      fun y : ℝ =>
        deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x * f y := by
  filter_upwards with y
  by_cases hy : y ∈ Set.Icc (x - ε) (x + ε)
  · rw [hiaiLocalClip_eq_on_Icc (f := f) hy]
  · have hdx :=
      hiaiScaledMollifierWeight_deriv_x_eq_zero_off_window
        (φ := φ) hφ hε hy
    simp [hdx]

/--
The derivative of the regularization of the local clip equals the derivative
of the original regularization at the center point.
-/
theorem hiaiRegularization_localClip_deriv_eq_original
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    deriv
        (fun z : ℝ =>
          hiaiRegularization φ ε
            (hiaiLocalClip f (x - ε) (x + ε)) z)
        x =
      deriv (fun z : ℝ => hiaiRegularization φ ε f z) x := by
  obtain ⟨s, bound, hs, h_bound_core, bound_integrable⟩ :=
    hiaiScaledMollifierWeight_xDeriv_publicBoundData
      (φ := φ) (f := f) hφ hε
  have h_bound :
      ∀ᵐ y ∂volume, ∀ z ∈ s,
        ‖deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) z *
            hiaiLocalClip f (x - ε) (x + ε) y‖ ≤ bound y := by
    filter_upwards [h_bound_core] with y hy z hz
    exact
      (hiaiScaledMollifierWeight_xDeriv_bound_on_window
        (φ := φ) (f := f) hφ hε.le hx hpos).trans (hy z hz)
  have hclip :=
    hiaiRegularization_localClip_deriv_eq_scaledWeight_xDeriv_integral_of_dominated
      (φ := φ) (f := f) hφ hε hs
      (by
        filter_upwards with z
        exact hiaiScaledMollifierWeight_localClip_aestronglyMeasurable
          (φ := φ) (f := f) hφ hε hx hpos)
      (hiaiScaledMollifierWeight_localClip_integrable
        (φ := φ) (f := f) hφ hε hx hpos)
      (hiaiScaledMollifierWeight_xDeriv_localClip_aestronglyMeasurable
        (φ := φ) (f := f) hφ hε hx hpos)
      h_bound bound_integrable
  have horig :=
    hiaiRegularization_original_deriv_eq_scaledWeight_xDeriv_integral
      (φ := φ) (f := f) hφ hε hx hpos
  have hae :=
    hiaiScaledMollifierWeight_xDeriv_localClip_eq_original_ae
      (φ := φ) (f := f) (x := x) hφ hε
  calc
    deriv
        (fun z : ℝ =>
          hiaiRegularization φ ε
            (hiaiLocalClip f (x - ε) (x + ε)) z)
        x
        = ∫ y,
            deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x *
              hiaiLocalClip f (x - ε) (x + ε) y := hclip
    _ = ∫ y,
            deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x *
              f y := integral_congr_ae hae
    _ = deriv (fun z : ℝ => hiaiRegularization φ ε f z) x := horig.symm

/--
Public Löwner positivity supplies the clipped-function bound in the
dominated-differentiation package.  The other domination input is only the
smooth scalar bound on the derivative of the scaled mollifier weight, supplied
by `hiaiScaledMollifierWeight_xDeriv_publicBoundData`.
-/
theorem hiaiRegularization_localClip_dominatedData_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f)
    {s : Set ℝ} (hs : s ∈ 𝓝 x) {bound : ℝ → ℝ}
    (hF_meas : ∀ᶠ z in 𝓝 x,
      AEStronglyMeasurable
        (fun y : ℝ =>
          hiaiScaledMollifierWeight φ ε z y *
            hiaiLocalClip f (x - ε) (x + ε) y) volume)
    (hF_int :
      Integrable
        (fun y : ℝ =>
          hiaiScaledMollifierWeight φ ε x y *
            hiaiLocalClip f (x - ε) (x + ε) y) volume)
    (hF'_meas :
      AEStronglyMeasurable
        (fun y : ℝ =>
          deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x *
            hiaiLocalClip f (x - ε) (x + ε) y) volume)
    (h_bound_core :
      ∀ᵐ y ∂volume, ∀ z ∈ s,
        |ε⁻¹ * (deriv φ ((z - y) / ε) * ε⁻¹)| *
            max |f (x - ε)| |f (x + ε)| ≤ bound y)
    (bound_integrable : Integrable bound volume) :
    HasDerivAt
      (fun z : ℝ =>
        ∫ y, hiaiScaledMollifierWeight φ ε z y *
          hiaiLocalClip f (x - ε) (x + ε) y)
      (∫ y,
        deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x *
          hiaiLocalClip f (x - ε) (x + ε) y)
      x := by
  have h_bound :
      ∀ᵐ y ∂volume, ∀ z ∈ s,
        ‖deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) z *
            hiaiLocalClip f (x - ε) (x + ε) y‖ ≤ bound y := by
    filter_upwards [h_bound_core] with y hy
    intro z hz
    exact
      (hiaiScaledMollifierWeight_xDeriv_bound_on_window
        (φ := φ) (f := f) hφ hε.le hx hpos).trans (hy z hz)
  exact hiaiRegularization_localClip_hasDerivAt_scaledWeight_of_dominated
    (φ := φ) (f := f) hφ hs hF_meas hF_int hF'_meas h_bound bound_integrable

end

end Quantum.TraceInequality.Loewner
