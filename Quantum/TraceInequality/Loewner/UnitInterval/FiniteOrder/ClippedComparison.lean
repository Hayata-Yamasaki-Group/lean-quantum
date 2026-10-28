import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.RegularizationConvolution

/-!
# Chapter 20 clipped Stieltjes comparison layer

This file contains the diagonal comparison between the clipped Stieltjes
convolution and the Hiai regularized Löwner kernel, before the shifted-node
kernel PSD arguments.
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
Conditional comparison between the clipped Stieltjes convolution and the
diagonal kernel of the Hiai regularization of the clipped function.  The only
open analytic inputs are the genuine Stieltjes integration-by-parts identity
and the differentiation-under-integral formula for the scaled-weight
convolution.
-/
theorem hiaiRegularization_clippedStieltjesConvolution_le_localClipDiagKernel
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hg : Monotone (hiaiLocalClip f (x - ε) (x + ε)))
    (hibp :
      (∫ y, hiaiScaledMollifierWeight φ ε x y ∂hg.stieltjesFunction.measure) =
        -∫ y in x - ε..x + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y *
            hiaiLocalClip f (x - ε) (x + ε) y)
    (hderiv :
      HasDerivAt
        (fun z : ℝ =>
          ∫ y, hiaiScaledMollifierWeight φ ε z y *
            hiaiLocalClip f (x - ε) (x + ε) y)
        (∫ y,
          deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x *
            hiaiLocalClip f (x - ε) (x + ε) y)
        x) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y ∂hg.stieltjesFunction.measure) ≤
      loewnerKernel
        (hiaiRegularization φ ε
          (hiaiLocalClip f (x - ε) (x + ε)))
        x x := by
  have hcenter :=
    hiaiScaledMollifierWeight_stieltjesIntegrationByParts
      (φ := φ) (g := hiaiLocalClip f (x - ε) (x + ε))
      hφ hε hg hibp
  have hderiv_eq :=
    hiaiRegularization_localClip_deriv_eq_scaledWeight_xDeriv_integral
      (φ := φ) (f := f) hφ hε hderiv
  rw [loewnerKernel_self, hderiv_eq]
  exact le_of_eq hcenter

/--
The same clipped Stieltjes-to-diagonal comparison with the
differentiation-under-integral input expanded into Mathlib's dominated
differentiation hypotheses.  The book step `hibp` is the case
`g = hiaiLocalClip f (x - ε) (x + ε)` of
`hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_closed`
(`IocUniformStep.lean`).
-/
theorem
    hiaiRegularization_clippedStieltjesConvolution_le_localClipDiagKernel_of_dominated
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hg : Monotone (hiaiLocalClip f (x - ε) (x + ε)))
    (hibp :
      (∫ y, hiaiScaledMollifierWeight φ ε x y ∂hg.stieltjesFunction.measure) =
        -∫ y in x - ε..x + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y *
            hiaiLocalClip f (x - ε) (x + ε) y)
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
    (h_bound :
      ∀ᵐ y ∂volume, ∀ z ∈ s,
        ‖deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) z *
            hiaiLocalClip f (x - ε) (x + ε) y‖ ≤ bound y)
    (bound_integrable : Integrable bound volume) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y ∂hg.stieltjesFunction.measure) ≤
      loewnerKernel
        (hiaiRegularization φ ε
          (hiaiLocalClip f (x - ε) (x + ε)))
        x x := by
  exact hiaiRegularization_clippedStieltjesConvolution_le_localClipDiagKernel
    (φ := φ) (f := f) hφ hε hg hibp
    (hiaiRegularization_localClip_hasDerivAt_scaledWeight_of_dominated
      (φ := φ) (f := f) hφ hs hF_meas hF_int hF'_meas h_bound bound_integrable)

/--
Conditional comparison with the original regularized function.  The
book-regularization analytic input is isolated as the final diagonal comparison
from the clipped regularization to the original one, which is
`hiaiRegularization_localClip_diagKernel_le_original_of_loewnerPosOnUnitInterval`
below.
-/
theorem hiaiRegularization_clippedStieltjesConvolution_le_diagKernel_of_localClip
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hg : Monotone (hiaiLocalClip f (x - ε) (x + ε)))
    (hibp :
      (∫ y, hiaiScaledMollifierWeight φ ε x y ∂hg.stieltjesFunction.measure) =
        -∫ y in x - ε..x + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y *
            hiaiLocalClip f (x - ε) (x + ε) y)
    (hderiv :
      HasDerivAt
        (fun z : ℝ =>
          ∫ y, hiaiScaledMollifierWeight φ ε z y *
            hiaiLocalClip f (x - ε) (x + ε) y)
        (∫ y,
          deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) x *
            hiaiLocalClip f (x - ε) (x + ε) y)
        x)
    (hdiag_le :
      loewnerKernel
          (hiaiRegularization φ ε
            (hiaiLocalClip f (x - ε) (x + ε)))
          x x ≤
        loewnerKernel (hiaiRegularization φ ε f) x x) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y ∂hg.stieltjesFunction.measure) ≤
      loewnerKernel (hiaiRegularization φ ε f) x x :=
  (hiaiRegularization_clippedStieltjesConvolution_le_localClipDiagKernel
    (φ := φ) (f := f) hφ hε hg hibp hderiv).trans hdiag_le

/--
Original-diagonal comparison with the derivative-under-integral input expanded
into dominated-differentiation data.  After this bridge, the other inputs are
the Stieltjes integration-by-parts identity and the local clipped-to-original
diagonal comparison, supplied by
`hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_closed`
(`IocUniformStep.lean`) and
`hiaiRegularization_localClip_diagKernel_le_original_of_loewnerPosOnUnitInterval`
below.
-/
theorem
    hiaiRegularization_clippedStieltjesConvolution_le_diagKernel_of_localClip_dominated
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hg : Monotone (hiaiLocalClip f (x - ε) (x + ε)))
    (hibp :
      (∫ y, hiaiScaledMollifierWeight φ ε x y ∂hg.stieltjesFunction.measure) =
        -∫ y in x - ε..x + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y *
            hiaiLocalClip f (x - ε) (x + ε) y)
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
    (h_bound :
      ∀ᵐ y ∂volume, ∀ z ∈ s,
        ‖deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) z *
            hiaiLocalClip f (x - ε) (x + ε) y‖ ≤ bound y)
    (bound_integrable : Integrable bound volume)
    (hdiag_le :
      loewnerKernel
          (hiaiRegularization φ ε
            (hiaiLocalClip f (x - ε) (x + ε)))
          x x ≤
        loewnerKernel (hiaiRegularization φ ε f) x x) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y ∂hg.stieltjesFunction.measure) ≤
      loewnerKernel (hiaiRegularization φ ε f) x x :=
  (hiaiRegularization_clippedStieltjesConvolution_le_localClipDiagKernel_of_dominated
    (φ := φ) (f := f) hφ hε hg hibp hs hF_meas hF_int hF'_meas h_bound
    bound_integrable).trans hdiag_le

/--
Public-data version of the conditional clipped Stieltjes convolution bound.
This theorem deliberately keeps the genuine analytic inputs explicit:
Stieltjes integration by parts, dominated differentiation under the scaled
weight, and the final comparison from the clipped regularization back to the
original regularization.
-/
theorem
    hiaiRegularization_clippedStieltjesConvolution_le_diagKernel_of_publicData
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f)
    (hibp :
      (∫ y, hiaiScaledMollifierWeight φ ε x y
          ∂(hiaiLocalClip_mono_of_loewnerPosOnUnitInterval
            (f := f) hε.le hx hpos).stieltjesFunction.measure) =
        -∫ y in x - ε..x + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y *
            hiaiLocalClip f (x - ε) (x + ε) y)
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
    (h_bound :
      ∀ᵐ y ∂volume, ∀ z ∈ s,
        ‖deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) z *
            hiaiLocalClip f (x - ε) (x + ε) y‖ ≤ bound y)
    (bound_integrable : Integrable bound volume)
    (hdiag_le :
      loewnerKernel
          (hiaiRegularization φ ε
            (hiaiLocalClip f (x - ε) (x + ε)))
          x x ≤
        loewnerKernel (hiaiRegularization φ ε f) x x) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂(hiaiLocalClip_mono_of_loewnerPosOnUnitInterval
          (f := f) hε.le hx hpos).stieltjesFunction.measure) ≤
      loewnerKernel (hiaiRegularization φ ε f) x x :=
  hiaiRegularization_clippedStieltjesConvolution_le_diagKernel_of_localClip_dominated
    (φ := φ) (f := f) hφ hε
    (hiaiLocalClip_mono_of_loewnerPosOnUnitInterval
      (f := f) hε.le hx hpos)
    hibp hs hF_meas hF_int hF'_meas h_bound bound_integrable hdiag_le

/--
The clipped-to-original diagonal comparison reduced to the corresponding
derivative inequality.  This keeps the final local comparison separated from
the Stieltjes integration-by-parts and dominated-differentiation inputs.
-/
theorem hiaiRegularization_localClip_diagKernel_le_original
    {φ f : ℝ → ℝ} {ε x : ℝ}
    (hderiv_le :
      deriv
          (fun z : ℝ =>
            hiaiRegularization φ ε
              (hiaiLocalClip f (x - ε) (x + ε)) z)
          x ≤
        deriv (fun z : ℝ => hiaiRegularization φ ε f z) x) :
    loewnerKernel
        (hiaiRegularization φ ε
          (hiaiLocalClip f (x - ε) (x + ε)))
        x x ≤
      loewnerKernel (hiaiRegularization φ ε f) x x := by
  simpa [loewnerKernel_self] using hderiv_le

/--
For a public Löwner-positive input, the clipped diagonal kernel comparison
follows from equality of the local-clip and original regularization derivatives.
-/
theorem
    hiaiRegularization_localClip_diagKernel_le_original_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    loewnerKernel
        (hiaiRegularization φ ε
          (hiaiLocalClip f (x - ε) (x + ε)))
        x x ≤
      loewnerKernel (hiaiRegularization φ ε f) x x :=
  hiaiRegularization_localClip_diagKernel_le_original
    (φ := φ) (f := f) (ε := ε) (x := x)
    (le_of_eq
      (hiaiRegularization_localClip_deriv_eq_original
        (φ := φ) (f := f) hφ hε hx hpos))

/--
Single-node public-data handoff in which the genuine Stieltjes
integration-by-parts identity is an explicit input, while the
dominated-differentiation bound is reduced to a scalar smooth-mollifier bound.
The identity is supplied by
`hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_closed`
(`IocUniformStep.lean`) in the theorems below.
-/
theorem
    hiaiRegularization_clippedStieltjesConvolution_le_diagKernel_of_publicIBP
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f)
    (hibp :
      (∫ y, hiaiScaledMollifierWeight φ ε x y
          ∂(hiaiLocalClip_mono_of_loewnerPosOnUnitInterval
            (f := f) hε.le hx hpos).stieltjesFunction.measure) =
        -∫ y in x - ε..x + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y *
            hiaiLocalClip f (x - ε) (x + ε) y)
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
    (bound_integrable : Integrable bound volume)
    (hderiv_le :
      deriv
          (fun z : ℝ =>
            hiaiRegularization φ ε
              (hiaiLocalClip f (x - ε) (x + ε)) z)
          x ≤
        deriv (fun z : ℝ => hiaiRegularization φ ε f z) x) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂(hiaiLocalClip_mono_of_loewnerPosOnUnitInterval
          (f := f) hε.le hx hpos).stieltjesFunction.measure) ≤
      loewnerKernel (hiaiRegularization φ ε f) x x := by
  have hderiv :=
    hiaiRegularization_localClip_dominatedData_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hε hx hpos hs hF_meas hF_int hF'_meas
      h_bound_core bound_integrable
  have hdiag_le :=
    hiaiRegularization_localClip_diagKernel_le_original
      (φ := φ) (f := f) (ε := ε) (x := x) hderiv_le
  exact hiaiRegularization_clippedStieltjesConvolution_le_diagKernel_of_localClip
    (φ := φ) (f := f) hφ hε
    (hiaiLocalClip_mono_of_loewnerPosOnUnitInterval
      (f := f) hε.le hx hpos)
    hibp hderiv hdiag_le

/--
Single-node handoff after the Stieltjes/BV integration-by-parts input has been
closed by the uniform half-open step approximation.  The other inputs are the
dominated-differentiation data for the scaled weight and the final comparison
from the clipped regularization back to the original one; both are supplied
under public Löwner positivity, in the next theorem and in
`regularization_clippedStieltjesConvolution_le_diagKernel_of_loewnerPos` below.
-/
theorem
    hiaiRegularization_clippedStieltjesConvolution_le_diagKernel_of_iocUniformSteps
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
    (bound_integrable : Integrable bound volume)
    (hderiv_le :
      deriv
          (fun z : ℝ =>
            hiaiRegularization φ ε
              (hiaiLocalClip f (x - ε) (x + ε)) z)
          x ≤
        deriv (fun z : ℝ => hiaiRegularization φ ε f z) x) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂(hiaiLocalClip_mono_of_loewnerPosOnUnitInterval
          (f := f) hε.le hx hpos).stieltjesFunction.measure) ≤
      loewnerKernel (hiaiRegularization φ ε f) x x := by
  exact hiaiRegularization_clippedStieltjesConvolution_le_diagKernel_of_publicIBP
    (φ := φ) (f := f) hφ hε hx hpos
    (hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_closed
      (φ := φ)
      (g := hiaiLocalClip f (x - ε) (x + ε))
      hφ hε
      (hiaiLocalClip_mono_of_loewnerPosOnUnitInterval
        (f := f) hε.le hx hpos))
    hs hF_meas hF_int hF'_meas h_bound_core bound_integrable hderiv_le

/--
Single-node handoff after both the Stieltjes/BV integration-by-parts input and
the smooth scaled-weight dominated-differentiation data have been supplied from
the public Löwner hypotheses.  The only analytic input is the final comparison
from the clipped regularization back to the original regularization, supplied by
`hiaiRegularization_localClip_deriv_eq_original` in
`regularization_clippedStieltjesConvolution_le_diagKernel_of_loewnerPos` below.
-/
theorem
    hiaiRegularization_clippedStieltjesConvolution_le_diagKernel_of_publicDomination
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f)
    (hderiv_le :
      deriv
          (fun z : ℝ =>
            hiaiRegularization φ ε
              (hiaiLocalClip f (x - ε) (x + ε)) z)
          x ≤
        deriv (fun z : ℝ => hiaiRegularization φ ε f z) x) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂(hiaiLocalClip_mono_of_loewnerPosOnUnitInterval
          (f := f) hε.le hx hpos).stieltjesFunction.measure) ≤
      loewnerKernel (hiaiRegularization φ ε f) x x := by
  obtain ⟨s, bound, hs, h_bound_core, bound_integrable⟩ :=
    hiaiScaledMollifierWeight_xDeriv_publicBoundData
      (φ := φ) (f := f) hφ hε
  exact hiaiRegularization_clippedStieltjesConvolution_le_diagKernel_of_iocUniformSteps
    (φ := φ) (f := f) hφ hε hx hpos hs
    (by
      filter_upwards with z
      exact hiaiScaledMollifierWeight_localClip_aestronglyMeasurable
        (φ := φ) (f := f) hφ hε hx hpos)
    (hiaiScaledMollifierWeight_localClip_integrable
      (φ := φ) (f := f) hφ hε hx hpos)
    (hiaiScaledMollifierWeight_xDeriv_localClip_aestronglyMeasurable
      (φ := φ) (f := f) hφ hε hx hpos)
    h_bound_core bound_integrable hderiv_le

/--
The clipped Stieltjes convolution is bounded by the original regularized
diagonal kernel under the public Löwner-positive input.
-/
theorem
    regularization_clippedStieltjesConvolution_le_diagKernel_of_loewnerPos
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂(hiaiLocalClip_mono_of_loewnerPosOnUnitInterval
          (f := f) hε.le hx hpos).stieltjesFunction.measure) ≤
      loewnerKernel (hiaiRegularization φ ε f) x x :=
  hiaiRegularization_clippedStieltjesConvolution_le_diagKernel_of_publicDomination
    (φ := φ) (f := f) hφ hε hx hpos
    (le_of_eq
      (hiaiRegularization_localClip_deriv_eq_original
        (φ := φ) (f := f) hφ hε hx hpos))

/--
The full with-density and affine change-of-variables identity for the clipped
a.c. derivative measure.  This removes the explicit `hac_deriv` hypothesis
from the previous conditional bridge.
-/
theorem hiaiLocalClip_acPart_integral_eq_diag_intervalIntegral
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hg : Monotone (hiaiLocalClip f (x - ε) (x + ε))) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂(volume.withDensity
          (fun y : ℝ =>
            ENNReal.ofReal
              (deriv (hiaiLocalClip f (x - ε) (x + ε)) y)))) =
      ∫ t in (-1 : ℝ)..1,
        φ t * loewnerKernel f (x - ε * t) (x - ε * t) := by
  calc
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂(volume.withDensity
          (fun y : ℝ =>
            ENNReal.ofReal
              (deriv (hiaiLocalClip f (x - ε) (x + ε)) y))))
        = ∫ y, hiaiScaledMollifierWeight φ ε x y *
            deriv (hiaiLocalClip f (x - ε) (x + ε)) y :=
          hiaiLocalClip_acPart_integral_eq_scaledWeight_volume_integral
            (φ := φ) (ε := ε) (x := x) hg
    _ = ∫ y in x - ε..x + ε,
          hiaiScaledMollifierWeight φ ε x y *
            deriv (hiaiLocalClip f (x - ε) (x + ε)) y :=
          hiaiScaledMollifierWeight_volume_integral_eq_window
            (φ := φ)
            (g := fun y => deriv (hiaiLocalClip f (x - ε) (x + ε)) y)
            hφ hε
    _ = ∫ t in (-1 : ℝ)..1,
          φ t * deriv (hiaiLocalClip f (x - ε) (x + ε)) (x - ε * t) :=
          hiaiScaledMollifierWeight_volume_integral_comp_eq_intervalIntegral
            (φ := φ)
            (g := fun y => deriv (hiaiLocalClip f (x - ε) (x + ε)) y)
            hε
    _ = ∫ t in (-1 : ℝ)..1,
          φ t * loewnerKernel f (x - ε * t) (x - ε * t) := by
          exact (hiaiLocalClip_diagKernel_intervalIntegral_eq
            (φ := φ) (f := f) (ε := ε) (x := x) hε).symm

/--
First connection from the clipped a.c. derivative measure to the averaged
diagonal kernel.  The analytic input is the change-of-variables /
with-density identity on the left; once supplied, the diagonal averaged kernel
is exactly the a.c. part integral.  The version with this identity proved is
`hiaiLocalClip_acPart_integral_eq_diag_intervalIntegral` above.
-/
theorem hiaiLocalClip_acPart_integral_eq_diag_intervalIntegral_of_deriv_comp
    {φ f : ℝ → ℝ} {ε x : ℝ} (hε : 0 < ε)
    (hac_deriv :
      (∫ y, hiaiScaledMollifierWeight φ ε x y
          ∂(volume.withDensity
            (fun y : ℝ =>
              ENNReal.ofReal
                (deriv (hiaiLocalClip f (x - ε) (x + ε)) y)))) =
        ∫ t in (-1 : ℝ)..1,
          φ t * deriv (hiaiLocalClip f (x - ε) (x + ε)) (x - ε * t)) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂(volume.withDensity
          (fun y : ℝ =>
            ENNReal.ofReal
              (deriv (hiaiLocalClip f (x - ε) (x + ε)) y)))) =
      ∫ t in (-1 : ℝ)..1,
        φ t * loewnerKernel f (x - ε * t) (x - ε * t) := by
  calc
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂(volume.withDensity
          (fun y : ℝ =>
            ENNReal.ofReal
              (deriv (hiaiLocalClip f (x - ε) (x + ε)) y))))
        = ∫ t in (-1 : ℝ)..1,
            φ t * deriv (hiaiLocalClip f (x - ε) (x + ε)) (x - ε * t) :=
          hac_deriv
    _ = ∫ t in (-1 : ℝ)..1,
          φ t * loewnerKernel f (x - ε * t) (x - ε * t) := by
          exact (hiaiLocalClip_diagKernel_intervalIntegral_eq
            (φ := φ) (f := f) (ε := ε) (x := x) hε).symm

/--
Stieltjes domination composed with the previous a.c. identity.  This proves the
averaged diagonal kernel is below the clipped Stieltjes convolution, leaving
only the final comparison between that convolution and the diagonal derivative
of the Hiai regularization.
-/
theorem hiaiRegularization_diagIntegral_le_clippedStieltjesConvolution_of_acPart_eq
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hg : Monotone (hiaiLocalClip f (x - ε) (x + ε)))
    (hw_int :
      Integrable (hiaiScaledMollifierWeight φ ε x)
        hg.stieltjesFunction.measure)
    (hac_eq :
      (∫ y, hiaiScaledMollifierWeight φ ε x y
          ∂(volume.withDensity
            (fun y : ℝ =>
              ENNReal.ofReal
                (deriv (hiaiLocalClip f (x - ε) (x + ε)) y)))) =
        ∫ t in (-1 : ℝ)..1,
          φ t * loewnerKernel f (x - ε * t) (x - ε * t)) :
    (∫ t in (-1 : ℝ)..1,
        φ t * loewnerKernel f (x - ε * t) (x - ε * t)) ≤
      ∫ y, hiaiScaledMollifierWeight φ ε x y ∂hg.stieltjesFunction.measure := by
  have hw_nonneg :
      0 ≤ᵐ[hg.stieltjesFunction.measure] hiaiScaledMollifierWeight φ ε x := by
    filter_upwards with y
    exact hiaiScaledMollifierWeight_nonneg (φ := φ) hφ hε
  calc
    (∫ t in (-1 : ℝ)..1,
        φ t * loewnerKernel f (x - ε * t) (x - ε * t))
        = ∫ y, hiaiScaledMollifierWeight φ ε x y
            ∂(volume.withDensity
              (fun y : ℝ =>
                ENNReal.ofReal
                  (deriv (hiaiLocalClip f (x - ε) (x + ε)) y))) := hac_eq.symm
    _ ≤ ∫ y, hiaiScaledMollifierWeight φ ε x y ∂hg.stieltjesFunction.measure :=
        stieltjes_acPart_integral_le_measure_integral
          (g := hiaiLocalClip f (x - ε) (x + ε))
          (w := hiaiScaledMollifierWeight φ ε x)
          hg hw_nonneg hw_int

/--
Stieltjes domination after closing the with-density and affine
change-of-variables identity.  The diagonal lower bound then also needs the
comparison between this clipped Stieltjes convolution and `K_{fε}(x,x)`, which is
`regularization_clippedStieltjesConvolution_le_diagKernel_of_loewnerPos` above.
-/
theorem hiaiRegularization_diagIntegral_le_clippedStieltjesConvolution
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hg : Monotone (hiaiLocalClip f (x - ε) (x + ε)))
    (hw_int :
      Integrable (hiaiScaledMollifierWeight φ ε x)
        hg.stieltjesFunction.measure) :
    (∫ t in (-1 : ℝ)..1,
        φ t * loewnerKernel f (x - ε * t) (x - ε * t)) ≤
      ∫ y, hiaiScaledMollifierWeight φ ε x y ∂hg.stieltjesFunction.measure :=
  hiaiRegularization_diagIntegral_le_clippedStieltjesConvolution_of_acPart_eq
    (φ := φ) (f := f) hφ hε hg hw_int
    (hiaiLocalClip_acPart_integral_eq_diag_intervalIntegral
      (φ := φ) (f := f) hφ hε hg)

end

end Quantum.TraceInequality.Loewner
