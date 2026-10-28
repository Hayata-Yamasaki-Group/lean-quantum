/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.UpperHalfPlane.Nevanlinna
import Quantum.TraceInequality.Loewner.UnitInterval.Pick.CauchyApproxIdentity
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Finite-boundary API for upper-half-plane Poisson boundary data

Source correspondence: the Poisson boundary measure-theory stage, including
finite weighted boundary measures, finite Poisson kernels, Nevanlinna and
Stieltjes transforms, and conversion to Poisson boundary data.
-/

namespace Quantum
namespace TraceInequality
namespace Loewner

open MeasureTheory Set
open Filter
open scoped UpperHalfPlane Topology Manifold ContDiff
open scoped NNReal
open scoped ENNReal

noncomputable section

/-! ### Finite Nevanlinna data as Poisson boundary data -/

/-- The integral of the upper-half-plane Poisson kernel against the Nevanlinna-weighted measure
equals `y` times the integral of `(1 + t²)/((t - x)² + y²)` against `ν`. [simon2019] -/
theorem nevanlinnaWeightedMeasure_integral_poissonKernel
    (ν : FiniteMeasure ℝ) (x y : ℝ) :
    (∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂nevanlinnaWeightedMeasure ν) =
      (∫ t : ℝ,
        (1 + t ^ (2 : ℕ)) / ((t - x) ^ (2 : ℕ) + y ^ (2 : ℕ))
        ∂(ν : Measure ℝ)) * y := by
  have hwd :
      (∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂nevanlinnaWeightedMeasure ν) =
        ∫ t : ℝ,
          (nevanlinnaWeightedMeasureDensity t).toReal •
            upperHalfPlanePoissonKernel t x y
          ∂(ν : Measure ℝ) := by
    have htop :
        ∀ᵐ t ∂(ν : Measure ℝ),
          nevanlinnaWeightedMeasureDensity t < (⊤ : ENNReal) := by
      exact ae_of_all _ (fun t => by simp [nevanlinnaWeightedMeasureDensity])
    exact integral_withDensity_eq_integral_toReal_smul
      measurable_nevanlinnaWeightedMeasureDensity htop
      (fun t : ℝ => upperHalfPlanePoissonKernel t x y)
  rw [hwd]
  rw [← integral_mul_const]
  refine integral_congr_ae ?_
  filter_upwards with t
  unfold upperHalfPlanePoissonKernel nevanlinnaWeightedMeasureDensity
  rw [ENNReal.toReal_ofReal]
  · simp only [smul_eq_mul]
    ring_nf
  · nlinarith [sq_nonneg t]

/--
The finite-boundary Poisson kernel obtained after absorbing the Nevanlinna
weight into a finite boundary measure.
-/
def finiteBoundaryPoissonKernel (t x y : ℝ) : ℝ :=
  (nevanlinnaWeightedMeasureDensity t).toReal *
    upperHalfPlanePoissonKernel t x y

/-- The finite-boundary Poisson kernel is measurable in `t`. -/
theorem measurable_finiteBoundaryPoissonKernel (x y : ℝ) :
    Measurable fun t : ℝ => finiteBoundaryPoissonKernel t x y := by
  unfold finiteBoundaryPoissonKernel
  exact measurable_nevanlinnaWeightedMeasureDensity.ennreal_toReal.mul
    (measurable_upperHalfPlanePoissonKernel x y)

/--
The finite-boundary Poisson kernel is the imaginary part of the finite-measure
Nevanlinna kernel at the corresponding upper-half-plane point.
-/
theorem finiteBoundaryPoissonKernel_eq_nevanlinnaKernel_im (t : ℝ) (z : ℍ) :
    finiteBoundaryPoissonKernel t (z : ℂ).re (z : ℂ).im =
      (nevanlinnaKernel t z).im := by
  rw [nevanlinnaKernel_im_eq]
  have hnorm : ‖(t : ℂ) - (z : ℂ)‖ ^ (2 : ℕ) =
      Complex.normSq ((t : ℂ) - (z : ℂ)) := by
    rw [← Complex.normSq_eq_norm_sq]
  rw [hnorm]
  unfold finiteBoundaryPoissonKernel upperHalfPlanePoissonKernel
  rw [nevanlinnaWeightedMeasureDensity, ENNReal.toReal_ofReal]
  · simp [Complex.normSq_apply]
    ring_nf
  · nlinarith [sq_nonneg t]

/--
Integral form of `finiteBoundaryPoissonKernel_eq_nevanlinnaKernel_im`.
It rewrites finite-boundary Poisson integral data as the imaginary part of the
complex Nevanlinna transform.
-/
theorem finiteBoundaryPoissonKernel_integral_eq_nevanlinnaKernel_integral_im
    (ν : FiniteMeasure ℝ) (z : ℍ) :
    (∫ t : ℝ, finiteBoundaryPoissonKernel t (z : ℂ).re (z : ℂ).im
        ∂(ν : Measure ℝ)) =
      (∫ t : ℝ, nevanlinnaKernel t z ∂(ν : Measure ℝ)).im := by
  calc
    (∫ t : ℝ, finiteBoundaryPoissonKernel t (z : ℂ).re (z : ℂ).im
        ∂(ν : Measure ℝ)) =
        ∫ t : ℝ, (nevanlinnaKernel t z).im ∂(ν : Measure ℝ) := by
          refine integral_congr_ae ?_
          exact ae_of_all _ fun t => finiteBoundaryPoissonKernel_eq_nevanlinnaKernel_im t z
    _ = (∫ t : ℝ, nevanlinnaKernel t z ∂(ν : Measure ℝ)).im := by
          exact integral_im (nevanlinnaKernel_integrable ν z)

/-! ### Finite Nevanlinna transforms from boundary kernels -/

/-- The finite-measure Nevanlinna transform attached to `ν`. -/
def nevanlinnaKernelIntegral (ν : FiniteMeasure ℝ) (z : ℍ) : ℂ :=
  ∫ t : ℝ, nevanlinnaKernel t z ∂(ν : Measure ℝ)

/-- The finite-measure Nevanlinna transform is holomorphic on the upper half-plane. -/
theorem nevanlinnaKernelIntegral_mdiff (ν : FiniteMeasure ℝ) :
    MDiff (nevanlinnaKernelIntegral ν) := by
  let rep : NevanlinnaRep (nevanlinnaKernelIntegral ν) := {
    alpha := 0
    beta := 0
    ν := ν
    formula := by
      intro z
      simp [nevanlinnaKernelIntegral]
  }
  exact rep.mdifferentiable

/--
A holomorphic upper-half-plane function with constant imaginary part is
constant.  This is the upper-half-plane wrapper around Mathlib's open mapping
theorem.
-/
theorem upperHalfPlane_mdiff_eq_const_of_im_eq_const
    {f : ℍ → ℂ} (hf : MDiff f) {c₀ : ℝ}
    (him : ∀ z : ℍ, (f z).im = c₀) :
    ∃ c : ℂ, ∀ z : ℍ, f z = c := by
  have hdiff :
      DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hf
  have han :
      AnalyticOnNhd ℂ (f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    hdiff.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  have him_comp :
      ∀ x ∈ {z : ℂ | 0 < z.im}, ((f ∘ UpperHalfPlane.ofComplex) x).im = c₀ := by
    intro x _hx
    exact him (UpperHalfPlane.ofComplex x)
  have hconn : IsConnected ({z : ℂ | 0 < z.im} : Set ℂ) := by
    exact Complex.isConnected_of_upperHalfPlane subset_rfl
      (by intro z hz; exact le_of_lt (show 0 < z.im from hz))
  rcases AnalyticOnNhd.eq_const_of_im_eq_const han him_comp
      UpperHalfPlane.isOpen_upperHalfPlaneSet hconn with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro z
  have hz : (z : ℂ) ∈ {w : ℂ | 0 < w.im} := z.coe_im_pos
  have h := hc (z : ℂ) hz
  simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using h

/-- Difference of two finite-measure Nevanlinna transforms is holomorphic. -/
theorem nevanlinnaKernelIntegral_sub_mdiff (ν₁ ν₂ : FiniteMeasure ℝ) :
    MDiff (fun z : ℍ => nevanlinnaKernelIntegral ν₁ z - nevanlinnaKernelIntegral ν₂ z) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h₁ := UpperHalfPlane.mdifferentiable_iff.mp (nevanlinnaKernelIntegral_mdiff ν₁)
  have h₂ := UpperHalfPlane.mdifferentiable_iff.mp (nevanlinnaKernelIntegral_mdiff ν₂)
  exact h₁.sub h₂

/-- At `z = i`, the finite-measure Nevanlinna transform is purely imaginary. -/
theorem nevanlinnaKernelIntegral_apply_upperHalfPlane_I_re
    (ν : FiniteMeasure ℝ) :
    (nevanlinnaKernelIntegral ν UpperHalfPlane.I).re = 0 := by
  dsimp [nevanlinnaKernelIntegral]
  have hInt := nevanlinnaKernel_integrable ν UpperHalfPlane.I
  have hre :
      (∫ t : ℝ, nevanlinnaKernel t UpperHalfPlane.I ∂(ν : Measure ℝ)).re =
        ∫ t : ℝ, (nevanlinnaKernel t UpperHalfPlane.I).re ∂(ν : Measure ℝ) := by
    simpa using (integral_re hInt).symm
  rw [hre]
  calc
    (∫ t : ℝ, (nevanlinnaKernel t UpperHalfPlane.I).re ∂(ν : Measure ℝ)) =
        ∫ _t : ℝ, (0 : ℝ) ∂(ν : Measure ℝ) := by
          refine integral_congr_ae ?_
          exact ae_of_all _ fun t => by
            simp [nevanlinnaKernel_apply_upperHalfPlane_I t]
    _ = 0 := by simp

/--
Equality of imaginary parts of all finite-measure Nevanlinna transforms implies
equality of the complex transforms.  The difference is holomorphic, has
constant imaginary part, and vanishes at `i`.
-/
theorem nevanlinnaKernelIntegral_eq_of_im_eq
    {ν₁ ν₂ : FiniteMeasure ℝ}
    (hIm : ∀ z : ℍ,
      (nevanlinnaKernelIntegral ν₁ z).im =
        (nevanlinnaKernelIntegral ν₂ z).im) :
    ∀ z : ℍ, nevanlinnaKernelIntegral ν₁ z = nevanlinnaKernelIntegral ν₂ z := by
  let G : ℍ → ℂ :=
    fun z => nevanlinnaKernelIntegral ν₁ z - nevanlinnaKernelIntegral ν₂ z
  have hG_mdiff : MDiff G := by
    dsimp [G]
    exact nevanlinnaKernelIntegral_sub_mdiff ν₁ ν₂
  have hG_im : ∀ z : ℍ, (G z).im = 0 := by
    intro z
    dsimp [G]
    simp [hIm z]
  rcases upperHalfPlane_mdiff_eq_const_of_im_eq_const hG_mdiff hG_im with ⟨c, hc⟩
  have hGI_zero : G UpperHalfPlane.I = 0 := by
    have hre : (G UpperHalfPlane.I).re = 0 := by
      dsimp [G]
      simp [nevanlinnaKernelIntegral_apply_upperHalfPlane_I_re]
    have him : (G UpperHalfPlane.I).im = 0 := hG_im UpperHalfPlane.I
    exact Complex.ext hre him
  intro z
  have hz := hc z
  have hI := hc UpperHalfPlane.I
  calc
    nevanlinnaKernelIntegral ν₁ z = nevanlinnaKernelIntegral ν₂ z + G z := by
      dsimp [G]
      abel
    _ = nevanlinnaKernelIntegral ν₂ z + G UpperHalfPlane.I := by
      rw [hz, hI]
    _ = nevanlinnaKernelIntegral ν₂ z := by rw [hGI_zero, add_zero]

/-! ### Stieltjes kernels and Poisson imaginary parts -/

/-- The upper-half-plane Stieltjes kernel `1 / (t - z)`. -/
def upperHalfPlaneStieltjesKernel (t : ℝ) (z : ℍ) : ℂ :=
  (((t : ℂ) - (z : ℂ))⁻¹)

/-- The finite-measure Stieltjes transform attached to `ν`. -/
def upperHalfPlaneStieltjesKernelIntegral (ν : FiniteMeasure ℝ) (z : ℍ) : ℂ :=
  ∫ t : ℝ, upperHalfPlaneStieltjesKernel t z ∂(ν : Measure ℝ)

/-- The Stieltjes kernel is continuous in the boundary variable. -/
theorem continuous_upperHalfPlaneStieltjesKernel (z : ℍ) :
    Continuous fun t : ℝ => upperHalfPlaneStieltjesKernel t z := by
  unfold upperHalfPlaneStieltjesKernel
  exact ((Complex.continuous_ofReal.comp continuous_id).sub continuous_const).inv₀
    (fun t => nevanlinna_den_ne_zero t z)

/-- The Stieltjes kernel is uniformly bounded by the inverse height of `z`. -/
theorem upperHalfPlaneStieltjesKernel_norm_bound (t : ℝ) (z : ℍ) :
    ‖upperHalfPlaneStieltjesKernel t z‖ ≤ ((z : ℂ).im)⁻¹ := by
  have hsq : ((z : ℂ).im) ^ (2 : ℕ) ≤
      ‖(t : ℂ) - (z : ℂ)‖ ^ (2 : ℕ) := by
    rw [← Complex.normSq_eq_norm_sq]
    have him : (((t : ℂ) - (z : ℂ))).im = -((z : ℂ).im) := by simp
    have h := Complex.im_sq_le_normSq ((t : ℂ) - (z : ℂ))
    rw [him] at h
    nlinarith
  have habs := sq_le_sq.mp hsq
  have hle : (z : ℂ).im ≤ ‖(t : ℂ) - (z : ℂ)‖ := by
    rwa [abs_of_pos z.coe_im_pos, abs_of_nonneg (norm_nonneg _)] at habs
  have hden_pos : 0 < ‖(t : ℂ) - (z : ℂ)‖ :=
    lt_of_lt_of_le z.coe_im_pos hle
  unfold upperHalfPlaneStieltjesKernel
  rw [norm_inv]
  exact (inv_le_inv₀ hden_pos z.coe_im_pos).2 hle

/-- The Stieltjes kernel is integrable against any finite measure. -/
theorem upperHalfPlaneStieltjesKernel_integrable
    (ν : FiniteMeasure ℝ) (z : ℍ) :
    Integrable (fun t : ℝ => upperHalfPlaneStieltjesKernel t z) (ν : Measure ℝ) := by
  refine Integrable.of_bound (continuous_upperHalfPlaneStieltjesKernel z).aestronglyMeasurable
    ((z : ℂ).im)⁻¹ ?_
  exact ae_of_all _ fun t => upperHalfPlaneStieltjesKernel_norm_bound t z

/-- The imaginary part of the Stieltjes kernel is the upper-half-plane Poisson kernel. -/
theorem upperHalfPlaneStieltjesKernel_im_eq_upperHalfPlanePoissonKernel
    (t : ℝ) (z : ℍ) :
    (upperHalfPlaneStieltjesKernel t z).im =
      upperHalfPlanePoissonKernel t (z : ℂ).re (z : ℂ).im := by
  unfold upperHalfPlaneStieltjesKernel upperHalfPlanePoissonKernel
  rw [Complex.inv_im]
  have him : (((t : ℂ) - (z : ℂ))).im = -((z : ℂ).im) := by simp
  have hnorm :
      Complex.normSq ((t : ℂ) - (z : ℂ)) =
        (t - (z : ℂ).re) ^ (2 : ℕ) + (z : ℂ).im ^ (2 : ℕ) := by
    simp [Complex.normSq_apply, pow_two]
  rw [him, hnorm]
  ring

/-- Integral form of the Stieltjes-kernel imaginary-part formula. -/
theorem upperHalfPlaneStieltjesKernelIntegral_im_eq_poissonKernel_integral
    (ν : FiniteMeasure ℝ) (z : ℍ) :
    (upperHalfPlaneStieltjesKernelIntegral ν z).im =
      ∫ t : ℝ, upperHalfPlanePoissonKernel t (z : ℂ).re (z : ℂ).im
        ∂(ν : Measure ℝ) := by
  have hInt : Integrable (fun t : ℝ => upperHalfPlaneStieltjesKernel t z)
      (ν : Measure ℝ) :=
    upperHalfPlaneStieltjesKernel_integrable ν z
  calc
    (upperHalfPlaneStieltjesKernelIntegral ν z).im =
        ∫ t : ℝ, (upperHalfPlaneStieltjesKernel t z).im ∂(ν : Measure ℝ) := by
          simpa [upperHalfPlaneStieltjesKernelIntegral] using (integral_im hInt).symm
    _ = ∫ t : ℝ, upperHalfPlanePoissonKernel t (z : ℂ).re (z : ℂ).im
        ∂(ν : Measure ℝ) := by
          refine integral_congr_ae ?_
          exact ae_of_all _ fun t =>
            upperHalfPlaneStieltjesKernel_im_eq_upperHalfPlanePoissonKernel t z

/--
Equality of Stieltjes transforms gives equality of the corresponding Poisson
kernel integrals, after taking imaginary parts.
-/
theorem poissonKernel_integral_eq_of_stieltjesKernelIntegral_eq
    {ν₁ ν₂ : FiniteMeasure ℝ}
    (hS :
      ∀ z : ℍ, z ≠ UpperHalfPlane.I →
        upperHalfPlaneStieltjesKernelIntegral ν₁ z =
          upperHalfPlaneStieltjesKernelIntegral ν₂ z)
    {z : ℍ} (hz : z ≠ UpperHalfPlane.I) :
    (∫ t : ℝ, upperHalfPlanePoissonKernel t (z : ℂ).re (z : ℂ).im
        ∂(ν₁ : Measure ℝ)) =
      ∫ t : ℝ, upperHalfPlanePoissonKernel t (z : ℂ).re (z : ℂ).im
        ∂(ν₂ : Measure ℝ) := by
  have hIm := congrArg Complex.im (hS z hz)
  simpa [upperHalfPlaneStieltjesKernelIntegral_im_eq_poissonKernel_integral] using hIm

/-! ### Cauchy scales and Poisson kernels -/

/-- The fixed Cauchy-approximation scale used to avoid the exceptional point `i`. -/
def stieltjesUniqScale (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 2)

/-- The Cauchy-approximation scale `1/(n + 2)` is positive. -/
theorem stieltjesUniqScale_pos (n : ℕ) :
    0 < stieltjesUniqScale n := by
  unfold stieltjesUniqScale
  positivity

/-- The Cauchy-approximation scale `1/(n + 2)` is less than `1`. -/
theorem stieltjesUniqScale_lt_one (n : ℕ) :
    stieltjesUniqScale n < 1 := by
  unfold stieltjesUniqScale
  have hden : 1 < (n : ℝ) + 2 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  simpa [one_div] using inv_lt_one_of_one_lt₀ hden

/-- A point `x + iy` with `0 < y < 1` is not the upper-half-plane point `i`, since its imaginary
part is less than `1`. -/
theorem upperHalfPlane_ofComplex_ne_I_of_im_lt_one
    {x y : ℝ} (hy : 0 < y) (hy_lt : y < 1) :
    UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I) ≠
      UpperHalfPlane.I := by
  intro h
  have him := congrArg (fun z : ℍ => (z : ℂ).im) h
  have hzpos : 0 < (((x : ℂ) + (y : ℂ) * Complex.I).im) := by
    simpa using hy
  have hleft :
      ((UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I) : ℂ).im) =
        y := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hzpos]
    simp
  have hright : ((UpperHalfPlane.I : ℍ) : ℂ).im = 1 := by
    simp [UpperHalfPlane.coe_I]
  change
    ((UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I) : ℍ) : ℂ).im =
      ((UpperHalfPlane.I : ℍ) : ℂ).im at him
  rw [hleft, hright] at him
  linarith

/-- The real Cauchy density equals `π⁻¹` times the upper-half-plane Poisson kernel. [simon2019] -/
theorem cauchyPDFReal_eq_pi_inv_mul_upperHalfPlanePoissonKernel
    (x t : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    ProbabilityTheory.cauchyPDFReal x ⟨ε, hε⟩ t =
      Real.pi⁻¹ * upperHalfPlanePoissonKernel t x ε := by
  unfold upperHalfPlanePoissonKernel
  rw [ProbabilityTheory.cauchyPDFReal_def]
  simp only [NNReal.coe_mk]
  ring

/-- If two finite measures yield equal Poisson-kernel integrals at `(x, ε)`, they yield equal
Cauchy-density integrals. -/
theorem cauchyPDF_integral_eq_of_poissonKernel_integral_eq
    {ν₁ ν₂ : FiniteMeasure ℝ}
    {x ε : ℝ} (hε : 0 ≤ ε)
    (hP :
      (∫ t : ℝ, upperHalfPlanePoissonKernel t x ε ∂(ν₁ : Measure ℝ)) =
        ∫ t : ℝ, upperHalfPlanePoissonKernel t x ε ∂(ν₂ : Measure ℝ)) :
    (∫ t : ℝ, ProbabilityTheory.cauchyPDFReal x ⟨ε, hε⟩ t
        ∂(ν₁ : Measure ℝ)) =
      ∫ t : ℝ, ProbabilityTheory.cauchyPDFReal x ⟨ε, hε⟩ t
        ∂(ν₂ : Measure ℝ) := by
  calc
    (∫ t : ℝ, ProbabilityTheory.cauchyPDFReal x ⟨ε, hε⟩ t
        ∂(ν₁ : Measure ℝ)) =
        ∫ t : ℝ, Real.pi⁻¹ * upperHalfPlanePoissonKernel t x ε
          ∂(ν₁ : Measure ℝ) := by
          refine integral_congr_ae ?_
          exact ae_of_all _ fun t =>
            cauchyPDFReal_eq_pi_inv_mul_upperHalfPlanePoissonKernel x t hε
    _ = Real.pi⁻¹ *
        ∫ t : ℝ, upperHalfPlanePoissonKernel t x ε ∂(ν₁ : Measure ℝ) := by
          exact integral_const_mul (r := Real.pi⁻¹)
            (f := fun t : ℝ => upperHalfPlanePoissonKernel t x ε)
    _ = Real.pi⁻¹ *
        ∫ t : ℝ, upperHalfPlanePoissonKernel t x ε ∂(ν₂ : Measure ℝ) := by
          rw [hP]
    _ = ∫ t : ℝ, Real.pi⁻¹ * upperHalfPlanePoissonKernel t x ε
        ∂(ν₂ : Measure ℝ) := by
          exact (integral_const_mul (r := Real.pi⁻¹)
            (f := fun t : ℝ => upperHalfPlanePoissonKernel t x ε)).symm
    _ = ∫ t : ℝ, ProbabilityTheory.cauchyPDFReal x ⟨ε, hε⟩ t
        ∂(ν₂ : Measure ℝ) := by
          refine integral_congr_ae ?_
          exact ae_of_all _ fun t =>
            (cauchyPDFReal_eq_pi_inv_mul_upperHalfPlanePoissonKernel x t hε).symm

/-! ### Nevanlinna-to-Stieltjes algebra -/

/--
Pointwise decomposition of the Nevanlinna kernel into an affine term and the
Stieltjes kernel.
-/
theorem nevanlinnaKernel_eq_add_sq_mul_stieltjesKernel (t : ℝ) (z : ℍ) :
    nevanlinnaKernel t z =
      (z : ℂ) + (1 + (z : ℂ) ^ (2 : ℕ)) *
        upperHalfPlaneStieltjesKernel t z := by
  have htz := nevanlinna_den_ne_zero t z
  unfold nevanlinnaKernel upperHalfPlaneStieltjesKernel
  field_simp [htz]
  ring

/--
Integral decomposition of the finite-measure Nevanlinna transform into total
mass, height variable, and the Stieltjes transform.
-/
theorem nevanlinnaKernelIntegral_eq_mass_smul_add_stieltjesKernelIntegral
    (ν : FiniteMeasure ℝ) (z : ℍ) :
    nevanlinnaKernelIntegral ν z =
      (ν : Measure ℝ).real Set.univ • (z : ℂ) +
        (1 + (z : ℂ) ^ (2 : ℕ)) *
          upperHalfPlaneStieltjesKernelIntegral ν z := by
  have hS : Integrable (fun t : ℝ => upperHalfPlaneStieltjesKernel t z)
      (ν : Measure ℝ) :=
    upperHalfPlaneStieltjesKernel_integrable ν z
  have hC : Integrable (fun _t : ℝ => (z : ℂ)) (ν : Measure ℝ) := integrable_const _
  have hMul : Integrable
      (fun t : ℝ => (1 + (z : ℂ) ^ (2 : ℕ)) * upperHalfPlaneStieltjesKernel t z)
      (ν : Measure ℝ) := by
    exact hS.const_mul (1 + (z : ℂ) ^ (2 : ℕ))
  have hMulInt :
      (∫ t : ℝ, (1 + (z : ℂ) ^ (2 : ℕ)) *
          upperHalfPlaneStieltjesKernel t z ∂(ν : Measure ℝ)) =
        (1 + (z : ℂ) ^ (2 : ℕ)) *
          upperHalfPlaneStieltjesKernelIntegral ν z := by
    simpa [upperHalfPlaneStieltjesKernelIntegral] using
      (MeasureTheory.integral_const_mul (μ := (ν : Measure ℝ))
        (1 + (z : ℂ) ^ (2 : ℕ)) (fun t : ℝ => upperHalfPlaneStieltjesKernel t z))
  calc
    nevanlinnaKernelIntegral ν z =
        ∫ t : ℝ,
          ((z : ℂ) + (1 + (z : ℂ) ^ (2 : ℕ)) *
            upperHalfPlaneStieltjesKernel t z) ∂(ν : Measure ℝ) := by
          unfold nevanlinnaKernelIntegral
          refine integral_congr_ae ?_
          exact ae_of_all _ fun t => nevanlinnaKernel_eq_add_sq_mul_stieltjesKernel t z
    _ = (∫ _t : ℝ, (z : ℂ) ∂(ν : Measure ℝ)) +
          ∫ t : ℝ, (1 + (z : ℂ) ^ (2 : ℕ)) *
            upperHalfPlaneStieltjesKernel t z ∂(ν : Measure ℝ) := by
          exact integral_add hC hMul
    _ = (ν : Measure ℝ).real Set.univ • (z : ℂ) +
          (1 + (z : ℂ) ^ (2 : ℕ)) *
            upperHalfPlaneStieltjesKernelIntegral ν z := by
          rw [integral_const, hMulInt]
          rfl

/-- At `z = i`, the finite-measure Nevanlinna transform reads the total mass. -/
theorem nevanlinnaKernelIntegral_apply_upperHalfPlane_I
    (ν : FiniteMeasure ℝ) :
    nevanlinnaKernelIntegral ν UpperHalfPlane.I =
      (ν : Measure ℝ).real Set.univ • Complex.I := by
  dsimp [nevanlinnaKernelIntegral]
  calc
    (∫ t : ℝ, nevanlinnaKernel t UpperHalfPlane.I ∂(ν : Measure ℝ)) =
        ∫ _t : ℝ, Complex.I ∂(ν : Measure ℝ) := by
          refine integral_congr_ae ?_
          exact ae_of_all _ fun t => nevanlinnaKernel_apply_upperHalfPlane_I t
    _ = (ν : Measure ℝ).real Set.univ • Complex.I := by
          rw [integral_const]
          rfl

/-- Equality of Nevanlinna transforms at `i` implies equality of total masses. -/
theorem measureReal_univ_eq_of_nevanlinnaKernelIntegral_eq
    {ν₁ ν₂ : FiniteMeasure ℝ}
    (h : nevanlinnaKernelIntegral ν₁ UpperHalfPlane.I =
      nevanlinnaKernelIntegral ν₂ UpperHalfPlane.I) :
    (ν₁ : Measure ℝ).real Set.univ = (ν₂ : Measure ℝ).real Set.univ := by
  have him := congrArg Complex.im h
  rw [nevanlinnaKernelIntegral_apply_upperHalfPlane_I,
    nevanlinnaKernelIntegral_apply_upperHalfPlane_I] at him
  simpa using him

/-- The coefficient `1 + z^2` only vanishes at `z = i` on the upper half-plane. -/
theorem one_add_sq_ne_zero_of_ne_upperHalfPlane_I {z : ℍ}
    (hz : z ≠ UpperHalfPlane.I) :
    1 + (z : ℂ) ^ (2 : ℕ) ≠ 0 := by
  have hfactor : 1 + (z : ℂ) ^ (2 : ℕ) =
      ((z : ℂ) + Complex.I) * ((z : ℂ) - Complex.I) := by
    rw [show ((z : ℂ) + Complex.I) * ((z : ℂ) - Complex.I) =
        (z : ℂ) ^ (2 : ℕ) - Complex.I ^ (2 : ℕ) by ring]
    rw [Complex.I_sq]
    ring
  rw [hfactor]
  apply mul_ne_zero
  · intro hzneg
    have him := congrArg Complex.im hzneg
    simp at him
    have hzpos : 0 < z.im := z.im_pos
    linarith
  · intro hzi
    apply hz
    apply UpperHalfPlane.coe_injective
    have hcoe : (z : ℂ) = (UpperHalfPlane.I : ℂ) := by
      simpa [UpperHalfPlane.coe_I] using sub_eq_zero.mp hzi
    exact hcoe

/--
Complex Nevanlinna-transform equality determines the Stieltjes transform away
from the point `i`, after reading off total mass at `i`.
-/
theorem upperHalfPlaneStieltjesKernelIntegral_eq_of_nevanlinnaKernelIntegral_eq
    {ν₁ ν₂ : FiniteMeasure ℝ}
    (hN : ∀ z : ℍ, nevanlinnaKernelIntegral ν₁ z = nevanlinnaKernelIntegral ν₂ z)
    {z : ℍ} (hz : z ≠ UpperHalfPlane.I) :
    upperHalfPlaneStieltjesKernelIntegral ν₁ z =
      upperHalfPlaneStieltjesKernelIntegral ν₂ z := by
  have hmass : (ν₁ : Measure ℝ).real Set.univ = (ν₂ : Measure ℝ).real Set.univ :=
    measureReal_univ_eq_of_nevanlinnaKernelIntegral_eq (hN UpperHalfPlane.I)
  have h := hN z
  rw [nevanlinnaKernelIntegral_eq_mass_smul_add_stieltjesKernelIntegral,
    nevanlinnaKernelIntegral_eq_mass_smul_add_stieltjesKernelIntegral] at h
  have hcommon :
      (1 + (z : ℂ) ^ (2 : ℕ)) * upperHalfPlaneStieltjesKernelIntegral ν₁ z =
        (1 + (z : ℂ) ^ (2 : ℕ)) * upperHalfPlaneStieltjesKernelIntegral ν₂ z := by
    simpa [hmass] using h
  exact mul_left_cancel₀ (one_add_sq_ne_zero_of_ne_upperHalfPlane_I hz) hcommon

/-! ### Finiteized Poisson boundary data -/

/--
Integrating the upper-half-plane Poisson kernel against the non-finite
weighted boundary measure is the same as integrating `finiteBoundaryPoissonKernel`
against the corresponding finite measure.
-/
theorem poissonKernel_integral_nevanlinnaWeightedMeasure_eq_finiteBoundaryPoissonKernel
    (ν : FiniteMeasure ℝ) (x y : ℝ) :
    (∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂nevanlinnaWeightedMeasure ν) =
      ∫ t : ℝ, finiteBoundaryPoissonKernel t x y ∂(ν : Measure ℝ) := by
  have hwd :
      (∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂nevanlinnaWeightedMeasure ν) =
        ∫ t : ℝ,
          (nevanlinnaWeightedMeasureDensity t).toReal •
            upperHalfPlanePoissonKernel t x y
          ∂(ν : Measure ℝ) := by
    have htop :
        ∀ᵐ t ∂(ν : Measure ℝ),
          nevanlinnaWeightedMeasureDensity t < (⊤ : ENNReal) := by
      exact ae_of_all _ (fun t => by simp [nevanlinnaWeightedMeasureDensity])
    exact integral_withDensity_eq_integral_toReal_smul
      measurable_nevanlinnaWeightedMeasureDensity htop
      (fun t : ℝ => upperHalfPlanePoissonKernel t x y)
  calc
    (∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂nevanlinnaWeightedMeasure ν) =
        ∫ t : ℝ,
          (nevanlinnaWeightedMeasureDensity t).toReal •
            upperHalfPlanePoissonKernel t x y
          ∂(ν : Measure ℝ) := hwd
    _ = ∫ t : ℝ, finiteBoundaryPoissonKernel t x y ∂(ν : Measure ℝ) := by
          refine integral_congr_ae ?_
          exact ae_of_all _ fun t => by
            simp [finiteBoundaryPoissonKernel, smul_eq_mul]

/-- The Poisson boundary data obtained from any finite-measure Nevanlinna representation. -/
def poissonBoundaryMeasureData_of_nevanlinnaRep
    {F : ℍ → ℂ} (rep : NevanlinnaRep F) :
    PoissonBoundaryMeasureData
      (fun z : ℂ => (F (UpperHalfPlane.ofComplex z)).im) where
  boundaryMeasure := nevanlinnaWeightedMeasure rep.ν
  slope := rep.beta
  weight_lintegral_lt_top := nevanlinnaWeightedMeasure_weight_lintegral_lt_top rep.ν
  poisson_formula := by
    intro x y hy
    let zc : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
    have hz : 0 < zc.im := by
      simp [zc, hy]
    let z : ℍ := UpperHalfPlane.ofComplex zc
    have hzcoe : (z : ℂ) = zc := by
      dsimp [z]
      exact congrArg UpperHalfPlane.coe (UpperHalfPlane.ofComplex_apply_of_im_pos hz)
    have hz_im : (z : ℂ).im = y := by
      rw [hzcoe]
      simp [zc]
    have hz_im_upper : z.im = y := by
      simpa [UpperHalfPlane.coe_im] using hz_im
    have hnorm_int :
        (∫ t : ℝ,
          (1 + t ^ (2 : ℕ)) /
            ‖(t : ℂ) - (z : ℂ)‖ ^ (2 : ℕ)
          ∂(rep.ν : Measure ℝ)) =
        ∫ t : ℝ,
          (1 + t ^ (2 : ℕ)) / ((t - x) ^ (2 : ℕ) + y ^ (2 : ℕ))
          ∂(rep.ν : Measure ℝ) := by
      refine integral_congr_ae ?_
      filter_upwards with t
      rw [hzcoe]
      have hden :
          ‖(t : ℂ) - zc‖ ^ (2 : ℕ) =
            (t - x) ^ (2 : ℕ) + y ^ (2 : ℕ) := by
        rw [show zc = (x : ℂ) + (y : ℂ) * Complex.I by rfl]
        rw [← Complex.normSq_eq_norm_sq]
        simp [Complex.normSq_apply, pow_two]
      rw [hden]
    have hfinite :
        (∫ t : ℝ,
          (1 + t ^ (2 : ℕ)) /
            ‖(t : ℂ) - (z : ℂ)‖ ^ (2 : ℕ)
          ∂(rep.ν : Measure ℝ)) * z.im =
        ∫ t : ℝ, upperHalfPlanePoissonKernel t x y
          ∂nevanlinnaWeightedMeasure rep.ν := by
      rw [hnorm_int, hz_im_upper]
      exact (nevanlinnaWeightedMeasure_integral_poissonKernel rep.ν x y).symm
    have hfinite_y :
        (∫ t : ℝ,
          (1 + t ^ (2 : ℕ)) /
            ‖(t : ℂ) - (z : ℂ)‖ ^ (2 : ℕ)
          ∂(rep.ν : Measure ℝ)) * y =
        ∫ t : ℝ, upperHalfPlanePoissonKernel t x y
          ∂nevanlinnaWeightedMeasure rep.ν := by
      simpa [hz_im_upper] using hfinite
    have him := rep.im_eq z
    calc
      (F (UpperHalfPlane.ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))).im =
          (F z).im := by rfl
      _ = ((rep.beta : ℝ) +
            ∫ t : ℝ,
              (1 + t ^ (2 : ℕ)) /
                ‖(t : ℂ) - (z : ℂ)‖ ^ (2 : ℕ)
              ∂(rep.ν : Measure ℝ)) * (z : ℂ).im := him
      _ = (rep.beta : ℝ) * y +
            ∫ t : ℝ, upperHalfPlanePoissonKernel t x y
              ∂nevanlinnaWeightedMeasure rep.ν := by
          rw [UpperHalfPlane.coe_im, add_mul, hz_im_upper, hfinite_y]

end

end Loewner
end TraceInequality
end Quantum
