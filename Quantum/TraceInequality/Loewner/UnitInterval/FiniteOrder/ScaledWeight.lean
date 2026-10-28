import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.Mollifier
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Chapter 20 scaled mollifier weight

This file contains the regularized interval, Hiai regularization kernel, scaled
mollifier weight, and the first integration-by-parts identities used by the
finite-order regularity proof.
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

/-- The interior interval on which the ε-regularization samples only `(-1,1)`. -/
def hiaiRegularizedInterior (ε : ℝ) : Set ℝ :=
  Set.Ioo ((-1 : ℝ) + ε) ((1 : ℝ) - ε)

/--
Hiai's one-variable regularization
`fε(x) = ∫_{-1}^{1} φ(t) f(x - ε t) dt`.
-/
noncomputable def hiaiRegularization
    (φ : ℝ → ℝ) (ε : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1, φ t * f (x - ε * t)

/--
Scaled mollifier weight on the original variable.  For `0 < ε`, the change of
variables `y = x - ε t` sends this to `ε⁻¹ φ(t)`.
-/
noncomputable def hiaiScaledMollifierWeight
    (φ : ℝ → ℝ) (ε x y : ℝ) : ℝ :=
  ε⁻¹ * φ ((x - y) / ε)

/-- The scaled Hiai mollifier weight is nonnegative when the scale is positive. -/
theorem hiaiScaledMollifierWeight_nonneg
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x y : ℝ} (hε : 0 < ε) :
    0 ≤ hiaiScaledMollifierWeight φ ε x y := by
  exact mul_nonneg (inv_nonneg.mpr hε.le) (hφ.nonneg ((x - y) / ε))

/--
Under the substitution `y = x - ε * t`, the scaled weight becomes
`ε⁻¹ * φ t`.
-/
theorem hiaiScaledMollifierWeight_eq_shift
    {φ : ℝ → ℝ} {ε x t : ℝ} (hε : ε ≠ 0) :
    hiaiScaledMollifierWeight φ ε x (x - ε * t) =
      ε⁻¹ * φ t := by
  have harg : (x - (x - ε * t)) / ε = t := by
    field_simp [hε]
    ring
  rw [hiaiScaledMollifierWeight, harg]

/--
The scaled weight vanishes at the left endpoint of its support window.  This is
the boundary term used by the Stieltjes integration-by-parts reduction.
-/
theorem hiaiScaledMollifierWeight_boundary_left_zero
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) :
    hiaiScaledMollifierWeight φ ε x (x - ε) = 0 := by
  rw [show x - ε = x - ε * (1 : ℝ) by ring,
    hiaiScaledMollifierWeight_eq_shift
      (φ := φ) (ε := ε) (x := x) (t := 1) hε.ne']
  simp [hiaiMollifier_right_endpoint_zero hφ]

/--
The scaled weight vanishes at the right endpoint of its support window.
-/
theorem hiaiScaledMollifierWeight_boundary_right_zero
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) :
    hiaiScaledMollifierWeight φ ε x (x + ε) = 0 := by
  rw [show x + ε = x - ε * (-1 : ℝ) by ring,
    hiaiScaledMollifierWeight_eq_shift
      (φ := φ) (ε := ε) (x := x) (t := -1) hε.ne']
  simp [hiaiMollifier_left_endpoint_zero hφ]

/--
Differentiating the scaled weight in the regularization center.  This is the
smooth-kernel side of the Stieltjes integration-by-parts step
(`hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_closed`).
-/
theorem hiaiScaledMollifierWeight_hasDerivAt_x
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x y : ℝ} :
    HasDerivAt (fun x : ℝ => hiaiScaledMollifierWeight φ ε x y)
      (ε⁻¹ * (deriv φ ((x - y) / ε) * ε⁻¹)) x := by
  have hdiffφ : DifferentiableAt ℝ φ ((x - y) / ε) := by
    exact (hφ.smooth.differentiable (by simp [loewnerBookSmoothOrder])).differentiableAt
  have harg : HasDerivAt (fun x : ℝ => (x - y) / ε) ε⁻¹ x := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).sub_const y).mul_const ε⁻¹)
  have hcomp := hdiffφ.hasDerivAt.comp x harg
  simpa [hiaiScaledMollifierWeight, Function.comp,
    mul_assoc, mul_comm, mul_left_comm] using
    HasDerivAt.const_mul ε⁻¹ hcomp

/--
Differentiating the scaled weight in the integration variable.  It is the
opposite derivative to the center derivative before the final Stieltjes
integration-by-parts comparison.
-/
theorem hiaiScaledMollifierWeight_hasDerivAt_y
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x y : ℝ} :
    HasDerivAt (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y)
      (ε⁻¹ * (deriv φ ((x - y) / ε) * (-ε⁻¹))) y := by
  have hdiffφ : DifferentiableAt ℝ φ ((x - y) / ε) := by
    exact (hφ.smooth.differentiable (by simp [loewnerBookSmoothOrder])).differentiableAt
  have harg : HasDerivAt (fun y : ℝ => (x - y) / ε) (-ε⁻¹) y := by
    have hsub : HasDerivAt (fun y : ℝ => x - y) (-1) y := by
      simpa using (hasDerivAt_const y x).sub (hasDerivAt_id y)
    simpa [div_eq_mul_inv, mul_assoc] using hsub.mul_const ε⁻¹
  have hcomp := hdiffφ.hasDerivAt.comp y harg
  simpa [hiaiScaledMollifierWeight, Function.comp,
    mul_assoc, mul_comm, mul_left_comm] using
    HasDerivAt.const_mul ε⁻¹ hcomp

/-- Formula for the center derivative of the scaled Hiai weight. -/
theorem hiaiScaledMollifierWeight_deriv_x
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x y : ℝ} :
    deriv (fun x : ℝ => hiaiScaledMollifierWeight φ ε x y) x =
      ε⁻¹ * (deriv φ ((x - y) / ε) * ε⁻¹) :=
  (hiaiScaledMollifierWeight_hasDerivAt_x
    (φ := φ) (ε := ε) (x := x) (y := y) hφ).deriv

/-- Formula for the integration-variable derivative of the scaled Hiai weight. -/
theorem hiaiScaledMollifierWeight_deriv_y
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x y : ℝ} :
    deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y =
      ε⁻¹ * (deriv φ ((x - y) / ε) * (-ε⁻¹)) :=
  (hiaiScaledMollifierWeight_hasDerivAt_y
    (φ := φ) (ε := ε) (x := x) (y := y) hφ).deriv

/-- The `y`-derivative of the scaled Hiai weight is the negative `x`-derivative. -/
theorem hiaiScaledMollifierWeight_deriv_y_eq_neg_deriv_x
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x y : ℝ} :
    deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y =
      - deriv (fun x : ℝ => hiaiScaledMollifierWeight φ ε x y) x := by
  rw [hiaiScaledMollifierWeight_deriv_y
      (φ := φ) (ε := ε) (x := x) (y := y) hφ,
    hiaiScaledMollifierWeight_deriv_x
      (φ := φ) (ε := ε) (x := x) (y := y) hφ]
  ring

/--
Outside the support window, the derivative in the integration variable is zero.
This isolates the compact-support hypothesis needed by the Stieltjes
integration-by-parts step.
-/
theorem hiaiScaledMollifierWeight_deriv_y_eq_zero_off_window
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x y : ℝ} (hε : 0 < ε)
    (hy : y ∉ Set.Icc (x - ε) (x + ε)) :
    deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y = 0 := by
  rw [hiaiScaledMollifierWeight_deriv_y
    (φ := φ) (ε := ε) (x := x) (y := y) hφ]
  have harg_not : (x - y) / ε ∉ Set.Icc (-1 : ℝ) 1 := by
    intro harg
    have hlow : -ε ≤ x - y := by
      have h := (le_div_iff₀ hε).1 harg.1
      simpa using h
    have hhigh : x - y ≤ ε := by
      have h := (div_le_iff₀ hε).1 harg.2
      simpa using h
    exact hy ⟨by linarith, by linarith⟩
  have htsupp : tsupport φ ⊆ Set.Icc (-1 : ℝ) 1 := by
    rw [tsupport]
    exact closure_minimal hφ.support_subset isClosed_Icc
  have hnot_supp_deriv : (x - y) / ε ∉ Function.support (deriv φ) := by
    intro hsupp
    exact harg_not (htsupp (support_deriv_subset hsupp))
  have hderiv : deriv φ ((x - y) / ε) = 0 := by
    by_contra hne
    exact hnot_supp_deriv hne
  simp [hderiv]

/--
Outside the support window, the derivative in the center variable is also zero.
This follows from `deriv_y W = - deriv_x W` and the previous support lemma.
-/
theorem hiaiScaledMollifierWeight_deriv_x_eq_zero_off_window
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x y : ℝ} (hε : 0 < ε)
    (hy : y ∉ Set.Icc (x - ε) (x + ε)) :
    deriv (fun x : ℝ => hiaiScaledMollifierWeight φ ε x y) x = 0 := by
  have hy_zero :=
    hiaiScaledMollifierWeight_deriv_y_eq_zero_off_window
      (φ := φ) hφ hε hy
  have hrel :=
    hiaiScaledMollifierWeight_deriv_y_eq_neg_deriv_x
      (φ := φ) (ε := ε) (x := x) (y := y) hφ
  linarith

/-- A nonzero scaled Hiai weight forces the integration point into its support window. -/
theorem hiaiScaledMollifierWeight_mem_window_of_ne_zero
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x y : ℝ} (hε : 0 < ε)
    (hW : hiaiScaledMollifierWeight φ ε x y ≠ 0) :
    y ∈ Set.Icc (x - ε) (x + ε) := by
  have hφne : φ ((x - y) / ε) ≠ 0 := by
    have hmul := (mul_ne_zero_iff.mp hW).2
    simpa [hiaiScaledMollifierWeight] using hmul
  have harg : (x - y) / ε ∈ Set.Icc (-1 : ℝ) 1 :=
    hφ.support_subset hφne
  have hlow : -ε ≤ x - y := by
    have h := (le_div_iff₀ hε).1 harg.1
    simpa using h
  have hhigh : x - y ≤ ε := by
    have h := (div_le_iff₀ hε).1 harg.2
    simpa using h
  exact ⟨by linarith, by linarith⟩

/--
The scaled mollifier weight is integrable against any Stieltjes measure coming
from a monotone function.  The proof uses its compact support in
`[x - ε, x + ε]`, continuity of the mollifier, and the explicit finite
Stieltjes mass of compact intervals.
-/
theorem hiaiScaledMollifierWeight_integrable_stieltjes
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g) :
    Integrable (hiaiScaledMollifierWeight φ ε x)
      hg.stieltjesFunction.measure := by
  have hlin : Continuous (fun y : ℝ => (x - y) / ε) :=
    (continuous_const.sub continuous_id).div_const ε
  have hcont : Continuous (hiaiScaledMollifierWeight φ ε x) := by
    simpa [hiaiScaledMollifierWeight] using
      (continuous_const.mul (hφ.smooth.continuous.comp hlin))
  have hsupp : Function.support (hiaiScaledMollifierWeight φ ε x) ⊆
      Set.Icc (x - ε) (x + ε) := by
    intro y hy
    exact hiaiScaledMollifierWeight_mem_window_of_ne_zero
      (φ := φ) hφ hε hy
  have hfinite : hg.stieltjesFunction.measure (Set.Icc (x - ε) (x + ε)) ≠ ⊤ := by
    rw [StieltjesFunction.measure_Icc]
    exact ENNReal.ofReal_ne_top
  have hIntOn : IntegrableOn (hiaiScaledMollifierWeight φ ε x)
      (Set.Icc (x - ε) (x + ε)) hg.stieltjesFunction.measure := by
    exact hcont.continuousOn.integrableOn_of_subset_isCompact isCompact_Icc measurableSet_Icc
      subset_rfl hfinite
  exact (MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp).mp hIntOn

/--
The center-derivative integrand is supported on the same compact window as the
scaled mollifier weight, so its ordinary integral may be restricted to that
window.
-/
theorem hiaiScaledMollifierWeight_xDeriv_volume_integral_eq_window
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) :
    (∫ y,
        deriv (fun x : ℝ => hiaiScaledMollifierWeight φ ε x y) x * g y) =
      ∫ y in x - ε..x + ε,
        deriv (fun x : ℝ => hiaiScaledMollifierWeight φ ε x y) x * g y := by
  let F : ℝ → ℝ := fun y =>
    deriv (fun x : ℝ => hiaiScaledMollifierWeight φ ε x y) x * g y
  have hzero : ∀ y : ℝ, y ∉ Set.Icc (x - ε) (x + ε) → F y = 0 := by
    intro y hy
    have hdx :=
      hiaiScaledMollifierWeight_deriv_x_eq_zero_off_window
        (φ := φ) hφ hε hy
    simp [F, hdx]
  have hset : (∫ y in Set.Icc (x - ε) (x + ε), F y) = ∫ y, F y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := volume) (s := Set.Icc (x - ε) (x + ε)) (f := F) hzero
  have hle : x - ε ≤ x + ε := by linarith
  calc
    (∫ y,
        deriv (fun x : ℝ => hiaiScaledMollifierWeight φ ε x y) x * g y)
        = ∫ y, F y := rfl
    _ = ∫ y in Set.Icc (x - ε) (x + ε), F y := hset.symm
    _ = ∫ y in Set.Ioc (x - ε) (x + ε), F y := by
          exact integral_Icc_eq_integral_Ioc
    _ = ∫ y in x - ε..x + ε, F y := by
          rw [intervalIntegral.integral_of_le hle]
    _ = ∫ y in x - ε..x + ε,
        deriv (fun x : ℝ => hiaiScaledMollifierWeight φ ε x y) x * g y := rfl

/--
Conditional Stieltjes integration-by-parts normal form for the scaled mollifier
weight.  The actual Stieltjes integration-by-parts identity is kept as the
explicit hypothesis `hibp`; this lemma closes the already established
boundary/support/derivative algebra and rewrites the result in center-derivative
variables.
-/
theorem hiaiScaledMollifierWeight_stieltjesIntegrationByParts
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g)
    (hibp :
      (∫ y, hiaiScaledMollifierWeight φ ε x y ∂hg.stieltjesFunction.measure) =
        -∫ y in x - ε..x + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y * g y) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y ∂hg.stieltjesFunction.measure) =
      ∫ y,
        deriv (fun x : ℝ => hiaiScaledMollifierWeight φ ε x y) x * g y := by
  calc
    (∫ y, hiaiScaledMollifierWeight φ ε x y ∂hg.stieltjesFunction.measure)
        = -∫ y in x - ε..x + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y * g y := hibp
    _ = - ∫ y in x - ε..x + ε,
          (- deriv (fun x : ℝ => hiaiScaledMollifierWeight φ ε x y) x) * g y := by
          congr 1
          refine intervalIntegral.integral_congr ?_
          intro y _hy
          simpa using congrArg (fun r : ℝ => r * g y)
            (hiaiScaledMollifierWeight_deriv_y_eq_neg_deriv_x
              (φ := φ) (ε := ε) (x := x) (y := y) hφ)
    _ = ∫ y in x - ε..x + ε,
          deriv (fun x : ℝ => hiaiScaledMollifierWeight φ ε x y) x * g y := by
          rw [← intervalIntegral.integral_neg]
          refine intervalIntegral.integral_congr ?_
          intro y _hy
          ring
    _ = ∫ y,
          deriv (fun x : ℝ => hiaiScaledMollifierWeight φ ε x y) x * g y := by
          exact (hiaiScaledMollifierWeight_xDeriv_volume_integral_eq_window
            (φ := φ) (g := g) hφ hε).symm

/--
Lebesgue-volume integration by parts for the scaled mollifier weight.  This is
the smooth part of the Stieltjes integration-by-parts frontier: if the
Stieltjes integral has already been identified with the corresponding volume
integral against `deriv g`, then the endpoint/support algebra is closed by
ordinary interval integration by parts.
-/
theorem hiaiScaledMollifierWeight_volumeIntegrationByParts_identity
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hg_deriv : ∀ y ∈ [[x - ε, x + ε]], HasDerivAt g (deriv g y) y)
    (hW_int : IntervalIntegrable
      (fun y : ℝ => deriv (fun y : ℝ =>
        hiaiScaledMollifierWeight φ ε x y) y)
      volume (x - ε) (x + ε))
    (hg_int : IntervalIntegrable (deriv g) volume (x - ε) (x + ε)) :
    (∫ y in x - ε..x + ε,
        hiaiScaledMollifierWeight φ ε x y * deriv g y) =
      -∫ y in x - ε..x + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y * g y := by
  let W : ℝ → ℝ := fun y => hiaiScaledMollifierWeight φ ε x y
  let W' : ℝ → ℝ := fun y =>
    deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y
  have hW_deriv : ∀ y ∈ [[x - ε, x + ε]], HasDerivAt W (W' y) y := by
    intro y _hy
    have h :=
      hiaiScaledMollifierWeight_hasDerivAt_y
        (φ := φ) (ε := ε) (x := x) (y := y) hφ
    simpa [W, W',
      hiaiScaledMollifierWeight_deriv_y
        (φ := φ) (ε := ε) (x := x) (y := y) hφ] using h
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := x - ε) (b := x + ε)
      (u := W) (v := g) (u' := W') (v' := deriv g)
      hW_deriv hg_deriv (by simpa [W'] using hW_int) hg_int
  have hleft : W (x - ε) = 0 := by
    exact hiaiScaledMollifierWeight_boundary_left_zero
      (φ := φ) hφ hε
  have hright : W (x + ε) = 0 := by
    exact hiaiScaledMollifierWeight_boundary_right_zero
      (φ := φ) hφ hε
  rw [hleft, hright, zero_mul, zero_mul, sub_zero] at hparts
  simpa [W, W'] using hparts

/--
Conditional Stieltjes integration-by-parts identity obtained once the
Stieltjes integral of the scaled weight is identified with its absolutely
continuous volume contribution.  The public monotone case needs the genuine
Stieltjes/BV integration-by-parts step, proved as
`hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_closed`
(`IocUniformStep.lean`); this lemma isolates the part already handled by
Mathlib's ordinary interval integration by parts.
-/
theorem
    hiaiScaledMollifierWeight_stieltjesIntegrationByParts_identity_of_volumeFormula
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g)
    (hg_deriv : ∀ y ∈ [[x - ε, x + ε]], HasDerivAt g (deriv g y) y)
    (hW_int : IntervalIntegrable
      (fun y : ℝ => deriv (fun y : ℝ =>
        hiaiScaledMollifierWeight φ ε x y) y)
      volume (x - ε) (x + ε))
    (hg_int : IntervalIntegrable (deriv g) volume (x - ε) (x + ε))
    (hstieltjes_volume :
      (∫ y, hiaiScaledMollifierWeight φ ε x y
          ∂hg.stieltjesFunction.measure) =
        ∫ y in x - ε..x + ε,
          hiaiScaledMollifierWeight φ ε x y * deriv g y) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂hg.stieltjesFunction.measure) =
      -∫ y in x - ε..x + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y * g y := by
  rw [hstieltjes_volume]
  exact hiaiScaledMollifierWeight_volumeIntegrationByParts_identity
    (φ := φ) (g := g) hφ hε hg_deriv hW_int hg_int

end

end Quantum.TraceInequality.Loewner
