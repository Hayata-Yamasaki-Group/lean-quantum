import Quantum.TraceInequality.Loewner.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Nevanlinna representations on the upper half-plane

This file records the representation-level interface for Hiai's Theorem 2.24.
It does not prove the full Pick/Nevanlinna equivalence or uniqueness theorem.
-/

namespace Quantum
namespace TraceInequality
namespace Loewner

open Set MeasureTheory Filter
open scoped UpperHalfPlane Topology Manifold ContDiff

noncomputable section

/-- The finite-measure Nevanlinna kernel `(1 + t z) / (t - z)`. -/
def nevanlinnaKernel (t : ℝ) (z : ℍ) : ℂ :=
  (1 + (t : ℂ) * (z : ℂ)) / ((t : ℂ) - (z : ℂ))

/-- The weighted-measure Nevanlinna kernel `1 / (t - z) - t / (1 + t^2)`. -/
def nevanlinnaWeightedKernel (t : ℝ) (z : ℍ) : ℂ :=
  (1 / ((t : ℂ) - (z : ℂ))) - ((t : ℂ) / (1 + (t : ℂ) ^ (2 : ℕ)))

/-- The upper-half-plane Poisson kernel `y / ((t - x)^2 + y^2)`. -/
def upperHalfPlanePoissonKernel (t x y : ℝ) : ℝ :=
  y / ((t - x) ^ (2 : ℕ) + y ^ (2 : ℕ))

/-- The upper-half-plane Poisson kernel is measurable in the boundary variable. -/
theorem measurable_upperHalfPlanePoissonKernel (x y : ℝ) :
    Measurable (fun t : ℝ => upperHalfPlanePoissonKernel t x y) := by
  unfold upperHalfPlanePoissonKernel
  fun_prop

/-- The upper-half-plane Poisson kernel is nonnegative at nonnegative height. -/
theorem upperHalfPlanePoissonKernel_nonneg {t x y : ℝ} (hy : 0 ≤ y) :
    0 ≤ upperHalfPlanePoissonKernel t x y := by
  unfold upperHalfPlanePoissonKernel
  exact div_nonneg hy (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The imaginary part of the weighted Nevanlinna kernel is the Poisson kernel. -/
theorem nevanlinnaWeightedKernel_im_eq_upperHalfPlanePoissonKernel (t : ℝ) (z : ℍ) :
    (nevanlinnaWeightedKernel t z).im =
      upperHalfPlanePoissonKernel t (z : ℂ).re (z : ℂ).im := by
  unfold nevanlinnaWeightedKernel upperHalfPlanePoissonKernel
  have hreal : (((t : ℂ) / (1 + (t : ℂ) ^ (2 : ℕ))).im = 0) := by
    norm_num [Complex.div_im, Complex.normSq_apply, pow_two]
  rw [Complex.sub_im, hreal, sub_zero]
  rw [show (1 / ((t : ℂ) - (z : ℂ)) : ℂ) = ((t : ℂ) - (z : ℂ))⁻¹ by ring]
  rw [Complex.inv_im]
  have him : (((t : ℂ) - (z : ℂ))).im = -((z : ℂ).im) := by simp
  have hnorm : Complex.normSq ((t : ℂ) - (z : ℂ)) =
      (t - (z : ℂ).re) ^ (2 : ℕ) + (z : ℂ).im ^ (2 : ℕ) := by
    simp [Complex.normSq_apply, pow_two]
  rw [him, hnorm]
  ring

/-- The weight appearing in the non-finite Nevanlinna measure formulation. -/
def nevanlinnaWeight (t : ℝ) : ENNReal :=
  ENNReal.ofReal ((1 + t ^ (2 : ℕ))⁻¹)

/-- The Nevanlinna weight is measurable. -/
theorem measurable_nevanlinnaWeight :
    Measurable nevanlinnaWeight := by
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

/-- Density used to pass from the finite measure in (2.13) to the weighted measure in (2.14). -/
def nevanlinnaWeightedMeasureDensity (t : ℝ) : ENNReal :=
  ENNReal.ofReal (1 + t ^ (2 : ℕ))

/-- The Nevanlinna weighted-measure density is measurable. -/
theorem measurable_nevanlinnaWeightedMeasureDensity :
    Measurable nevanlinnaWeightedMeasureDensity := by
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

/-- The weighted measure `d\tildeν(t) = (1+t^2) dν(t)`. -/
def nevanlinnaWeightedMeasure (ν : FiniteMeasure ℝ) : Measure ℝ :=
  (ν : Measure ℝ).withDensity nevanlinnaWeightedMeasureDensity

/-- The weighted-measure density and Nevanlinna weight multiply to one. -/
theorem nevanlinnaWeightedMeasureDensity_mul_weight_eq_one (t : ℝ) :
    nevanlinnaWeightedMeasureDensity t * nevanlinnaWeight t = 1 := by
  have hnonneg : 0 ≤ 1 + t ^ (2 : ℕ) := by nlinarith [sq_nonneg t]
  have hpos : 0 < 1 + t ^ (2 : ℕ) := by nlinarith [sq_nonneg t]
  have hreal : (1 + t ^ (2 : ℕ)) * (1 + t ^ (2 : ℕ))⁻¹ = 1 := by
    field_simp [hpos.ne']
  calc
    nevanlinnaWeightedMeasureDensity t * nevanlinnaWeight t =
        ENNReal.ofReal (1 + t ^ (2 : ℕ)) *
          ENNReal.ofReal ((1 + t ^ (2 : ℕ))⁻¹) := by
          rfl
    _ = ENNReal.ofReal ((1 + t ^ (2 : ℕ)) * (1 + t ^ (2 : ℕ))⁻¹) := by
          rw [ENNReal.ofReal_mul hnonneg]
    _ = 1 := by rw [hreal, ENNReal.ofReal_one]

/-- The Nevanlinna weight and weighted-measure density multiply to one. -/
theorem nevanlinnaWeight_mul_density_eq_one (t : ℝ) :
    nevanlinnaWeight t * nevanlinnaWeightedMeasureDensity t = 1 := by
  rw [mul_comm, nevanlinnaWeightedMeasureDensity_mul_weight_eq_one t]

private theorem nevanlinna_weighted_density_mul_weight_le_one (t : ℝ) :
    nevanlinnaWeightedMeasureDensity t * nevanlinnaWeight t ≤ 1 := by
  rw [nevanlinnaWeightedMeasureDensity_mul_weight_eq_one t]

/-- The Nevanlinna weight is integrable against the weighted measure. -/
theorem nevanlinnaWeightedMeasure_weight_lintegral_lt_top
    (ν : FiniteMeasure ℝ) :
    (∫⁻ t : ℝ, nevanlinnaWeight t ∂nevanlinnaWeightedMeasure ν) < ⊤ := by
  have hrewrite :
      (∫⁻ t : ℝ, nevanlinnaWeight t ∂nevanlinnaWeightedMeasure ν) =
        ∫⁻ t : ℝ,
          nevanlinnaWeightedMeasureDensity t * nevanlinnaWeight t
            ∂(ν : Measure ℝ) := by
    have h :=
      MeasureTheory.lintegral_withDensity_eq_lintegral_mul
        (ν : Measure ℝ)
        measurable_nevanlinnaWeightedMeasureDensity
        measurable_nevanlinnaWeight
    simpa [nevanlinnaWeightedMeasure, nevanlinnaWeightedMeasureDensity,
      nevanlinnaWeight] using h
  have hbound :
      ∀ᵐ t ∂(ν : Measure ℝ),
        nevanlinnaWeightedMeasureDensity t * nevanlinnaWeight t ≤ 1 := by
    exact ae_of_all _ nevanlinna_weighted_density_mul_weight_le_one
  rw [hrewrite]
  calc
    (∫⁻ t : ℝ,
        nevanlinnaWeightedMeasureDensity t * nevanlinnaWeight t
          ∂(ν : Measure ℝ)) ≤
        ∫⁻ _t : ℝ, (1 : ENNReal) ∂(ν : Measure ℝ) :=
          lintegral_mono_ae hbound
    _ = (ν : Measure ℝ) Set.univ := by simp
    _ < ⊤ := measure_lt_top (ν : Measure ℝ) Set.univ

/-- The finite measure `dν(t) = (1+t^2)⁻¹ dμ(t)` attached to a weighted measure. -/
def nevanlinnaFiniteMeasureOfWeighted
    (μ : Measure ℝ) (hμ : (∫⁻ t : ℝ, nevanlinnaWeight t ∂μ) < ⊤) :
    FiniteMeasure ℝ :=
  ⟨μ.withDensity nevanlinnaWeight, by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hμ⟩

/-- Weighting a weighted Nevanlinna measure back by `nevanlinnaWeight` recovers `ν`. -/
theorem nevanlinnaWeightedMeasure_withDensity_weight
    (ν : FiniteMeasure ℝ) :
    (nevanlinnaWeightedMeasure ν).withDensity nevanlinnaWeight =
      (ν : Measure ℝ) := by
  calc
    (nevanlinnaWeightedMeasure ν).withDensity nevanlinnaWeight =
        (ν : Measure ℝ).withDensity
          (fun t => nevanlinnaWeightedMeasureDensity t * nevanlinnaWeight t) := by
          simpa [nevanlinnaWeightedMeasure] using
            (withDensity_mul (ν : Measure ℝ)
              measurable_nevanlinnaWeightedMeasureDensity
              measurable_nevanlinnaWeight).symm
    _ = (ν : Measure ℝ).withDensity (fun _ : ℝ => (1 : ENNReal)) := by
          exact withDensity_congr_ae (μ := (ν : Measure ℝ))
            (ae_of_all _ fun t =>
              nevanlinnaWeightedMeasureDensity_mul_weight_eq_one t)
    _ = (ν : Measure ℝ) := by
          simp

/-- Converting a finite measure to weighted form and back recovers the finite measure. -/
theorem nevanlinnaFiniteMeasureOfWeighted_nevanlinnaWeightedMeasure
    (ν : FiniteMeasure ℝ) :
    nevanlinnaFiniteMeasureOfWeighted
        (nevanlinnaWeightedMeasure ν)
        (nevanlinnaWeightedMeasure_weight_lintegral_lt_top ν) = ν := by
  apply FiniteMeasure.toMeasure_injective
  change (nevanlinnaWeightedMeasure ν).withDensity nevanlinnaWeight =
    (ν : Measure ℝ)
  exact nevanlinnaWeightedMeasure_withDensity_weight ν

/-- Converting a weighted measure to finite form and back recovers the weighted measure. -/
theorem nevanlinnaWeightedMeasure_nevanlinnaFiniteMeasureOfWeighted
    (μ : Measure ℝ) (hμ : (∫⁻ t : ℝ, nevanlinnaWeight t ∂μ) < ⊤) :
    nevanlinnaWeightedMeasure (nevanlinnaFiniteMeasureOfWeighted μ hμ) = μ := by
  change (μ.withDensity nevanlinnaWeight).withDensity
    nevanlinnaWeightedMeasureDensity = μ
  calc
    (μ.withDensity nevanlinnaWeight).withDensity nevanlinnaWeightedMeasureDensity =
        μ.withDensity (fun t => nevanlinnaWeight t * nevanlinnaWeightedMeasureDensity t) := by
          simpa using
            (withDensity_mul μ measurable_nevanlinnaWeight
              measurable_nevanlinnaWeightedMeasureDensity).symm
    _ = μ.withDensity (fun _ : ℝ => (1 : ENNReal)) := by
          exact withDensity_congr_ae (μ := μ)
            (ae_of_all _ fun t => nevanlinnaWeight_mul_density_eq_one t)
    _ = μ := by
          simp

/-- Equality of weighted measures implies equality of the original finite measures. -/
theorem nevanlinnaFiniteMeasure_eq_of_weightedMeasure_eq
    {ν₁ ν₂ : FiniteMeasure ℝ}
    (hν : nevanlinnaWeightedMeasure ν₁ = nevanlinnaWeightedMeasure ν₂) :
    ν₁ = ν₂ := by
  apply FiniteMeasure.toMeasure_injective
  calc
    (ν₁ : Measure ℝ) =
        (nevanlinnaWeightedMeasure ν₁).withDensity nevanlinnaWeight := by
          exact (nevanlinnaWeightedMeasure_withDensity_weight ν₁).symm
    _ = (nevanlinnaWeightedMeasure ν₂).withDensity nevanlinnaWeight := by
          rw [hν]
    _ = (ν₂ : Measure ℝ) :=
          nevanlinnaWeightedMeasure_withDensity_weight ν₂

/-- If the finite measure vanishes on a set, so does the weighted measure. -/
theorem nevanlinnaWeightedMeasure_zero_of_finiteMeasure_zero
    {ν : FiniteMeasure ℝ} {s : Set ℝ}
    (hν : (ν : Measure ℝ) s = 0) :
    nevanlinnaWeightedMeasure ν s = 0 := by
  exact MeasureTheory.withDensity_absolutelyContinuous _ _ hν

/-- If the weighted measure vanishes on a set, so does the finite measure. -/
theorem nevanlinnaFiniteMeasure_zero_of_weightedMeasure_zero
    {ν : FiniteMeasure ℝ} {s : Set ℝ}
    (hν : nevanlinnaWeightedMeasure ν s = 0) :
    (ν : Measure ℝ) s = 0 := by
  rw [← nevanlinnaWeightedMeasure_withDensity_weight ν]
  exact MeasureTheory.withDensity_absolutelyContinuous _ _ hν

/-- Vanishing of the weighted and finite Nevanlinna measures are equivalent. -/
theorem nevanlinnaWeightedMeasure_zero_iff_finiteMeasure_zero
    {ν : FiniteMeasure ℝ} {s : Set ℝ} :
    nevanlinnaWeightedMeasure ν s = 0 ↔ (ν : Measure ℝ) s = 0 := by
  constructor
  · exact nevanlinnaFiniteMeasure_zero_of_weightedMeasure_zero
  · exact nevanlinnaWeightedMeasure_zero_of_finiteMeasure_zero

/-- A real boundary point never equals an upper-half-plane point. -/
theorem nevanlinna_den_ne_zero (t : ℝ) (z : ℍ) :
    ((t : ℂ) - (z : ℂ)) ≠ 0 := by
  intro h
  have him : (((t : ℂ) - (z : ℂ))).im = 0 := by simp [h]
  have hcalc : (((t : ℂ) - (z : ℂ))).im = -((z : ℂ).im) := by simp
  have hzpos : 0 < (z : ℂ).im := by
    simpa using z.coe_im_pos
  linarith

/-- Imaginary part of the finite-measure Nevanlinna kernel. -/
theorem nevanlinnaKernel_im_eq (t : ℝ) (z : ℍ) :
    (nevanlinnaKernel t z).im =
      (1 + t ^ (2 : ℕ)) * (z : ℂ).im /
        ‖(t : ℂ) - (z : ℂ)‖ ^ (2 : ℕ) := by
  have htz := nevanlinna_den_ne_zero t z
  have hnorm : ‖(t : ℂ) - (z : ℂ)‖ ^ (2 : ℕ) =
      Complex.normSq ((t : ℂ) - (z : ℂ)) := by
    rw [Complex.normSq_eq_norm_sq]
  rw [hnorm]
  unfold nevanlinnaKernel
  rw [Complex.div_im]
  simp [Complex.normSq_apply]
  field_simp [Complex.normSq_pos.mpr htz]
  ring_nf

/-- The finite-measure Nevanlinna kernel has nonnegative imaginary part on `ℍ`. -/
theorem nevanlinnaKernel_im_nonneg (t : ℝ) (z : ℍ) :
    0 ≤ (nevanlinnaKernel t z).im := by
  rw [nevanlinnaKernel_im_eq]
  exact div_nonneg
    (mul_nonneg (by nlinarith [sq_nonneg t]) (le_of_lt z.coe_im_pos))
    (sq_nonneg _)

private theorem nevanlinna_den_norm_ge_im (t : ℝ) (z : ℍ) :
    (z : ℂ).im ≤ ‖(t : ℂ) - (z : ℂ)‖ := by
  have hsq : ((z : ℂ).im) ^ (2 : ℕ) ≤
      ‖(t : ℂ) - (z : ℂ)‖ ^ (2 : ℕ) := by
    rw [← Complex.normSq_eq_norm_sq]
    have him : (((t : ℂ) - (z : ℂ))).im = -((z : ℂ).im) := by simp
    have h := Complex.im_sq_le_normSq ((t : ℂ) - (z : ℂ))
    rw [him] at h
    nlinarith
  have habs := sq_le_sq.mp hsq
  rwa [abs_of_pos z.coe_im_pos, abs_of_nonneg (norm_nonneg _)] at habs

private theorem nevanlinnaKernel_norm_bound (t : ℝ) (z : ℍ) :
    ‖nevanlinnaKernel t z‖ ≤
      ‖(z : ℂ)‖ + ‖1 + (z : ℂ) ^ (2 : ℕ)‖ / (z : ℂ).im := by
  have hdeq :
      nevanlinnaKernel t z =
        (z : ℂ) + (1 + (z : ℂ) ^ (2 : ℕ)) / ((t : ℂ) - (z : ℂ)) := by
    have htz := nevanlinna_den_ne_zero t z
    unfold nevanlinnaKernel
    field_simp [htz]
    ring
  rw [hdeq]
  refine (norm_add_le _ _).trans ?_
  gcongr
  rw [norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) z.coe_im_pos
    (nevanlinna_den_norm_ge_im t z)

private theorem continuous_nevanlinnaKernel (z : ℍ) :
    Continuous fun t : ℝ => nevanlinnaKernel t z := by
  unfold nevanlinnaKernel
  refine Continuous.div ?num ?den ?hden
  · exact continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
  · exact (Complex.continuous_ofReal.comp continuous_id).sub continuous_const
  · intro t
    exact nevanlinna_den_ne_zero t z

/-- The finite-measure Nevanlinna kernel is integrable against any finite measure. -/
theorem nevanlinnaKernel_integrable
    (ν : FiniteMeasure ℝ) (z : ℍ) :
    Integrable (fun t : ℝ => nevanlinnaKernel t z) (ν : Measure ℝ) := by
  refine Integrable.of_bound (continuous_nevanlinnaKernel z).aestronglyMeasurable
    (‖(z : ℂ)‖ + ‖1 + (z : ℂ) ^ (2 : ℕ)‖ / (z : ℂ).im) ?_
  exact ae_of_all _ fun t => nevanlinnaKernel_norm_bound t z

/-- Complex-plane version of the finite-measure Nevanlinna kernel. -/
def nevanlinnaKernelC (t : ℝ) (z : ℂ) : ℂ :=
  (1 + (t : ℂ) * z) / ((t : ℂ) - z)

/-- Complex derivative of the complex-plane Nevanlinna kernel. -/
def nevanlinnaKernelCDeriv (t : ℝ) (z : ℂ) : ℂ :=
  (1 + (t : ℂ) ^ (2 : ℕ)) / (((t : ℂ) - z) ^ (2 : ℕ))

/-- On the upper half-plane, the complex-plane kernel agrees with the bundled one. -/
theorem nevanlinnaKernelC_eq_ofComplex (t : ℝ) {z : ℂ} (hz : 0 < z.im) :
    nevanlinnaKernelC t z = nevanlinnaKernel t (UpperHalfPlane.ofComplex z) := by
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  rfl

/-- The complex-plane kernel denominator is nonzero in the upper half-plane. -/
theorem nevanlinnaKernelC_den_ne_zero {t : ℝ} {z : ℂ} (hz : 0 < z.im) :
    ((t : ℂ) - z) ≠ 0 := by
  intro h
  have him : (((t : ℂ) - z)).im = 0 := by simp [h]
  have hcalc : (((t : ℂ) - z)).im = -z.im := by simp
  linarith

/-- Away from the pole, the complex-plane Nevanlinna kernel has the stated derivative. -/
theorem hasDerivAt_nevanlinnaKernelC_of_den_ne_zero {t : ℝ} {z : ℂ}
    (hden_ne : ((t : ℂ) - z) ≠ 0) :
    HasDerivAt (fun w : ℂ => nevanlinnaKernelC t w) (nevanlinnaKernelCDeriv t z) z := by
  have hnum : HasDerivAt (fun w : ℂ => 1 + (t : ℂ) * w) (t : ℂ) z := by
    have hsum :=
      (hasDerivAt_const z (1 : ℂ)).add ((hasDerivAt_id z).const_mul (t : ℂ))
    convert hsum using 1
    simp
  have hden : HasDerivAt (fun w : ℂ => (t : ℂ) - w) (-1 : ℂ) z := by
    simpa using (hasDerivAt_const z (t : ℂ)).sub (hasDerivAt_id z)
  have h := hnum.div hden hden_ne
  convert h using 1
  unfold nevanlinnaKernelCDeriv
  field_simp [hden_ne]
  ring

/-- In the upper half-plane, the complex-plane kernel has the stated derivative. -/
theorem hasDerivAt_nevanlinnaKernelC {t : ℝ} {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (fun w : ℂ => nevanlinnaKernelC t w) (nevanlinnaKernelCDeriv t z) z :=
  hasDerivAt_nevanlinnaKernelC_of_den_ne_zero (nevanlinnaKernelC_den_ne_zero hz)

private theorem continuous_nevanlinnaKernelC {z : ℂ} (hz : 0 < z.im) :
    Continuous fun t : ℝ => nevanlinnaKernelC t z := by
  unfold nevanlinnaKernelC
  refine Continuous.div ?num ?den ?hden
  · exact continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_id).mul continuous_const)
  · exact (Complex.continuous_ofReal.comp continuous_id).sub continuous_const
  · intro t
    exact nevanlinnaKernelC_den_ne_zero hz

private theorem continuous_nevanlinnaKernelCDeriv {z : ℂ} (hz : 0 < z.im) :
    Continuous fun t : ℝ => nevanlinnaKernelCDeriv t z := by
  unfold nevanlinnaKernelCDeriv
  refine Continuous.div ?num ?den ?hden
  · exact continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_id).pow (2 : ℕ))
  · exact (((Complex.continuous_ofReal.comp continuous_id).sub continuous_const).pow (2 : ℕ))
  · intro t
    exact pow_ne_zero _ (nevanlinnaKernelC_den_ne_zero hz)

/-- Algebraic decomposition of the derivative kernel away from the pole. -/
theorem nevanlinnaKernelCDeriv_eq_decomp {t : ℝ} {z : ℂ}
    (hden : ((t : ℂ) - z) ≠ 0) :
    nevanlinnaKernelCDeriv t z =
      1 + (2 : ℂ) * z / ((t : ℂ) - z) +
        (1 + z ^ (2 : ℕ)) / (((t : ℂ) - z) ^ (2 : ℕ)) := by
  unfold nevanlinnaKernelCDeriv
  field_simp [hden]
  ring

/-- A denominator lower bound and a norm bound give a derivative-kernel bound. -/
theorem nevanlinnaKernelCDeriv_norm_bound
    {t : ℝ} {z : ℂ} {δ R : ℝ}
    (hδ : 0 < δ) (hden : δ ≤ ‖(t : ℂ) - z‖) (hR : ‖z‖ ≤ R) :
    ‖nevanlinnaKernelCDeriv t z‖ ≤
      1 + (2 * R) / δ + (1 + R ^ (2 : ℕ)) / δ ^ (2 : ℕ) := by
  have hden_ne : ((t : ℂ) - z) ≠ 0 := by
    intro h
    have : ‖(t : ℂ) - z‖ = 0 := by simp [h]
    linarith
  have hR_nonneg : 0 ≤ R := le_trans (norm_nonneg z) hR
  rw [nevanlinnaKernelCDeriv_eq_decomp hden_ne]
  calc
    ‖1 + (2 : ℂ) * z / ((t : ℂ) - z) +
        (1 + z ^ (2 : ℕ)) / (((t : ℂ) - z) ^ (2 : ℕ))‖ ≤
        ‖(1 : ℂ)‖ + ‖(2 : ℂ) * z / ((t : ℂ) - z)‖ +
          ‖(1 + z ^ (2 : ℕ)) / (((t : ℂ) - z) ^ (2 : ℕ))‖ := by
          exact (norm_add_le _ _).trans (by
            gcongr
            exact norm_add_le _ _)
    _ ≤ 1 + (2 * R) / δ + (1 + R ^ (2 : ℕ)) / δ ^ (2 : ℕ) := by
          rw [norm_one]
          gcongr
          · rw [norm_div, norm_mul, Complex.norm_ofNat]
            exact div_le_div₀ (mul_nonneg (by norm_num) hR_nonneg)
              (mul_le_mul_of_nonneg_left hR (by norm_num)) hδ hden
          · rw [norm_div, norm_pow]
            refine div_le_div₀ ?num ?numle (sq_pos_of_pos hδ) ?denle
            · nlinarith [sq_nonneg R]
            · refine (norm_add_le (1 : ℂ) (z ^ (2 : ℕ))).trans ?_
              rw [norm_one, norm_pow]
              gcongr
            · rw [pow_two, pow_two]
              exact mul_le_mul hden hden hδ.le (norm_nonneg _)

private theorem nevanlinnaKernelC_integrable
    (ν : FiniteMeasure ℝ) {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun t : ℝ => nevanlinnaKernelC t z) (ν : Measure ℝ) := by
  have h_eq :
      (fun t : ℝ => nevanlinnaKernelC t z) =
        fun t : ℝ => nevanlinnaKernel t (UpperHalfPlane.ofComplex z) := by
    ext t
    exact nevanlinnaKernelC_eq_ofComplex t hz
  rw [h_eq]
  exact nevanlinnaKernel_integrable ν (UpperHalfPlane.ofComplex z)

private theorem nevanlinnaKernelC_ball_im_lower
    {z w : ℂ} {δ : ℝ} (hδ : δ = z.im / 2) (hz : 0 < z.im)
    (hw : w ∈ Metric.ball z δ) :
    δ ≤ w.im := by
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hdist : ‖w - z‖ < δ := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hw
  have him_abs : |w.im - z.im| ≤ ‖w - z‖ := by
    simpa using Complex.abs_im_le_norm (w - z)
  have him_lt : |w.im - z.im| < δ := lt_of_le_of_lt him_abs hdist
  have hdiff_lt : z.im - w.im < δ := by
    have hneg : z.im - w.im = -(w.im - z.im) := by ring
    rw [hneg]
    exact lt_of_le_of_lt (neg_le_abs _) him_lt
  rw [hδ] at hdiff_lt ⊢
  linarith

private theorem nevanlinnaKernelC_integral_hasDerivAt
    (ν : FiniteMeasure ℝ) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt
      (fun w : ℂ => ∫ t : ℝ, nevanlinnaKernelC t w ∂(ν : Measure ℝ))
      (∫ t : ℝ, nevanlinnaKernelCDeriv t z ∂(ν : Measure ℝ)) z := by
  let δ : ℝ := z.im / 2
  let R : ℝ := ‖z‖ + δ
  let C : ℝ := 1 + (2 * R) / δ + (1 + R ^ (2 : ℕ)) / δ ^ (2 : ℕ)
  have hδ_def : δ = z.im / 2 := rfl
  have hδ_pos : 0 < δ := by dsimp [δ]; positivity
  have hball : Metric.ball z δ ∈ 𝓝 z := Metric.ball_mem_nhds z hδ_pos
  have h_meas :
      ∀ᶠ w : ℂ in 𝓝 z,
        AEStronglyMeasurable (fun t : ℝ => nevanlinnaKernelC t w) (ν : Measure ℝ) := by
    filter_upwards [hball] with w hw
    have hwim : 0 < w.im := lt_of_lt_of_le hδ_pos
      (nevanlinnaKernelC_ball_im_lower hδ_def hz hw)
    exact (continuous_nevanlinnaKernelC hwim).aestronglyMeasurable
  have h_int : Integrable (fun t : ℝ => nevanlinnaKernelC t z) (ν : Measure ℝ) :=
    nevanlinnaKernelC_integrable ν hz
  have h_deriv_meas :
      AEStronglyMeasurable (fun t : ℝ => nevanlinnaKernelCDeriv t z)
        (ν : Measure ℝ) :=
    (continuous_nevanlinnaKernelCDeriv hz).aestronglyMeasurable
  have h_bound :
      ∀ᵐ t : ℝ ∂(ν : Measure ℝ),
        ∀ w : ℂ, w ∈ Metric.ball z δ →
          ‖nevanlinnaKernelCDeriv t w‖ ≤ C := by
    refine ae_of_all _ ?_
    intro t w hw
    have hwim_lower : δ ≤ w.im := nevanlinnaKernelC_ball_im_lower hδ_def hz hw
    have hden_lower : δ ≤ ‖(t : ℂ) - w‖ := by
      have hsq : w.im ^ (2 : ℕ) ≤ ‖(t : ℂ) - w‖ ^ (2 : ℕ) := by
        rw [← Complex.normSq_eq_norm_sq]
        have him : (((t : ℂ) - w)).im = -w.im := by simp
        have h := Complex.im_sq_le_normSq ((t : ℂ) - w)
        rw [him] at h
        nlinarith
      have habs := sq_le_sq.mp hsq
      have hwim_pos : 0 < w.im := lt_of_lt_of_le hδ_pos hwim_lower
      have : w.im ≤ ‖(t : ℂ) - w‖ := by
        rwa [abs_of_pos hwim_pos, abs_of_nonneg (norm_nonneg _)] at habs
      exact le_trans hwim_lower this
    have hR : ‖w‖ ≤ R := by
      have hdist : ‖w - z‖ < δ := by
        simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hw
      calc
        ‖w‖ = ‖z + (w - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        _ ≤ R := by
          dsimp [R]
          linarith
    exact nevanlinnaKernelCDeriv_norm_bound hδ_pos hden_lower hR
  have h_bound_int : Integrable (fun _t : ℝ => C) (ν : Measure ℝ) := by
    exact integrable_const _
  have h_deriv :
      ∀ᵐ t : ℝ ∂(ν : Measure ℝ),
        ∀ w : ℂ, w ∈ Metric.ball z δ →
          HasDerivAt (fun w : ℂ => nevanlinnaKernelC t w)
            (nevanlinnaKernelCDeriv t w) w := by
    refine ae_of_all _ ?_
    intro t w hw
    have hwim : 0 < w.im := lt_of_lt_of_le hδ_pos
      (nevanlinnaKernelC_ball_im_lower hδ_def hz hw)
    exact hasDerivAt_nevanlinnaKernelC hwim
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (ν : Measure ℝ))
    (bound := fun _t : ℝ => C)
    (F := fun w t => nevanlinnaKernelC t w)
    (F' := fun w t => nevanlinnaKernelCDeriv t w)
    hball h_meas h_int h_deriv_meas h_bound h_bound_int h_deriv).2

private theorem nevanlinna_real_square_den_ne_zero (t : ℝ) :
    ((1 : ℂ) + (t : ℂ) ^ (2 : ℕ)) ≠ 0 := by
  intro h
  have hre : (((1 : ℂ) + (t : ℂ) ^ (2 : ℕ))).re = 0 := by simp [h]
  have hcalc : (((1 : ℂ) + (t : ℂ) ^ (2 : ℕ))).re = 1 + t ^ (2 : ℕ) := by
    norm_num [pow_two]
  have hpos : 0 < 1 + t ^ (2 : ℕ) := by nlinarith [sq_nonneg t]
  linarith

/-- Algebraic equivalence between Hiai's formulas (2.13) and (2.14). -/
theorem nevanlinnaWeightedKernel_mul_density_eq_kernel (t : ℝ) (z : ℍ) :
    nevanlinnaWeightedKernel t z * ((1 + t ^ (2 : ℕ) : ℝ) : ℂ) =
      nevanlinnaKernel t z := by
  have htz := nevanlinna_den_ne_zero t z
  have ht2 := nevanlinna_real_square_den_ne_zero t
  unfold nevanlinnaWeightedKernel nevanlinnaKernel
  field_simp [htz, ht2]
  norm_num [pow_two]
  ring_nf

/-- Multiplying the finite kernel by the real weight gives the weighted kernel. -/
theorem nevanlinnaWeight_toReal_mul_kernel_eq_weightedKernel (t : ℝ) (z : ℍ) :
    (nevanlinnaWeight t).toReal * nevanlinnaKernel t z =
      nevanlinnaWeightedKernel t z := by
  have hweight : (nevanlinnaWeight t).toReal = (1 + t ^ (2 : ℕ))⁻¹ := by
    rw [nevanlinnaWeight, ENNReal.toReal_ofReal]
    positivity
  rw [hweight]
  rw [← nevanlinnaWeightedKernel_mul_density_eq_kernel t z]
  have hmul :
      (1 + (t : ℂ) ^ (2 : ℕ))⁻¹ * (1 + (t : ℂ) ^ (2 : ℕ)) = 1 := by
    exact inv_mul_cancel₀ (nevanlinna_real_square_den_ne_zero t)
  calc
    (((1 + t ^ (2 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) *
        (nevanlinnaWeightedKernel t z * ((1 + t ^ (2 : ℕ) : ℝ) : ℂ)) =
        ((((1 + t ^ (2 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) *
          ((1 + t ^ (2 : ℕ) : ℝ) : ℂ)) *
            nevanlinnaWeightedKernel t z := by ring
    _ = nevanlinnaWeightedKernel t z := by
          simpa using congrArg (fun c : ℂ => c * nevanlinnaWeightedKernel t z) hmul

private theorem nevanlinna_weighted_density_toReal (t : ℝ) :
    (nevanlinnaWeightedMeasureDensity t).toReal = 1 + t ^ (2 : ℕ) := by
  rw [nevanlinnaWeightedMeasureDensity, ENNReal.toReal_ofReal]
  nlinarith [sq_nonneg t]

private theorem nevanlinnaWeightedMeasure_integral_weightedKernel
    (ν : FiniteMeasure ℝ) (z : ℍ) :
    (∫ t : ℝ, nevanlinnaWeightedKernel t z ∂nevanlinnaWeightedMeasure ν) =
      ∫ t : ℝ, nevanlinnaKernel t z ∂(ν : Measure ℝ) := by
  have hwd :
      (∫ t : ℝ, nevanlinnaWeightedKernel t z ∂nevanlinnaWeightedMeasure ν) =
        ∫ t : ℝ,
          (nevanlinnaWeightedMeasureDensity t).toReal •
            nevanlinnaWeightedKernel t z
          ∂(ν : Measure ℝ) := by
    have htop :
        ∀ᵐ t ∂(ν : Measure ℝ),
          nevanlinnaWeightedMeasureDensity t < (⊤ : ENNReal) := by
      exact ae_of_all _ (fun t => by simp [nevanlinnaWeightedMeasureDensity])
    exact integral_withDensity_eq_integral_toReal_smul
      measurable_nevanlinnaWeightedMeasureDensity htop
      (fun t : ℝ => nevanlinnaWeightedKernel t z)
  have hkernel :
      (fun t : ℝ =>
          (nevanlinnaWeightedMeasureDensity t).toReal •
            nevanlinnaWeightedKernel t z)
        =ᵐ[(ν : Measure ℝ)]
        fun t : ℝ => nevanlinnaKernel t z := by
    filter_upwards with t
    rw [nevanlinna_weighted_density_toReal]
    change ((1 + t ^ (2 : ℕ) : ℝ) : ℂ) *
        nevanlinnaWeightedKernel t z = nevanlinnaKernel t z
    rw [mul_comm]
    exact nevanlinnaWeightedKernel_mul_density_eq_kernel t z
  calc
    (∫ t : ℝ, nevanlinnaWeightedKernel t z ∂nevanlinnaWeightedMeasure ν) =
        ∫ t : ℝ,
          (nevanlinnaWeightedMeasureDensity t).toReal •
            nevanlinnaWeightedKernel t z
          ∂(ν : Measure ℝ) := hwd
    _ = ∫ t : ℝ, nevanlinnaKernel t z ∂(ν : Measure ℝ) :=
          integral_congr_ae hkernel

private theorem nevanlinnaFiniteMeasureOfWeighted_integral_kernel
    (μ : Measure ℝ) (hμ : (∫⁻ t : ℝ, nevanlinnaWeight t ∂μ) < ⊤)
    (z : ℍ) :
    (∫ t : ℝ, nevanlinnaKernel t z
        ∂(nevanlinnaFiniteMeasureOfWeighted μ hμ : Measure ℝ)) =
      ∫ t : ℝ, nevanlinnaWeightedKernel t z ∂μ := by
  have hwd :
      (∫ t : ℝ, nevanlinnaKernel t z
          ∂(nevanlinnaFiniteMeasureOfWeighted μ hμ : Measure ℝ)) =
        ∫ t : ℝ, (nevanlinnaWeight t).toReal • nevanlinnaKernel t z ∂μ := by
    have htop : ∀ᵐ t ∂μ, nevanlinnaWeight t < (⊤ : ENNReal) := by
      exact ae_of_all _ (fun t => by simp [nevanlinnaWeight])
    exact integral_withDensity_eq_integral_toReal_smul
      measurable_nevanlinnaWeight htop (fun t : ℝ => nevanlinnaKernel t z)
  have hkernel :
      (fun t : ℝ => (nevanlinnaWeight t).toReal • nevanlinnaKernel t z)
        =ᵐ[μ] fun t : ℝ => nevanlinnaWeightedKernel t z := by
    filter_upwards with t
    simpa [smul_eq_mul] using nevanlinnaWeight_toReal_mul_kernel_eq_weightedKernel t z
  calc
    (∫ t : ℝ, nevanlinnaKernel t z
        ∂(nevanlinnaFiniteMeasureOfWeighted μ hμ : Measure ℝ)) =
        ∫ t : ℝ, (nevanlinnaWeight t).toReal • nevanlinnaKernel t z ∂μ := hwd
    _ = ∫ t : ℝ, nevanlinnaWeightedKernel t z ∂μ :=
          integral_congr_ae hkernel

/-- At `i`, the finite-measure Nevanlinna kernel is the constant `i`. -/
theorem nevanlinnaKernel_apply_upperHalfPlane_I (t : ℝ) :
    nevanlinnaKernel t UpperHalfPlane.I = Complex.I := by
  have hden : ((t : ℂ) - Complex.I) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  unfold nevanlinnaKernel
  change (1 + (t : ℂ) * Complex.I) / ((t : ℂ) - Complex.I) = Complex.I
  field_simp [hden]
  rw [mul_sub, Complex.I_mul_I]
  ring

/-- The finite-measure Nevanlinna representation (Hiai (2.13)). -/
structure NevanlinnaRep (F : ℍ → ℂ) where
  alpha : ℝ
  beta : NNReal
  ν : FiniteMeasure ℝ
  formula :
    ∀ z : ℍ,
      F z =
        (alpha : ℂ) + (beta : ℝ) * (z : ℂ) +
          ∫ t : ℝ, nevanlinnaKernel t z ∂(ν : Measure ℝ)

namespace NevanlinnaRep

/-- At `z = i`, the Nevanlinna kernel contributes no real part. -/
theorem integral_kernel_apply_upperHalfPlane_I_re
    {F : ℍ → ℂ} (rep : NevanlinnaRep F) :
    ((∫ t : ℝ, nevanlinnaKernel t UpperHalfPlane.I
        ∂(rep.ν : Measure ℝ)).re) = 0 := by
  have hker_int :
      Integrable (fun t : ℝ => nevanlinnaKernel t UpperHalfPlane.I)
        (rep.ν : Measure ℝ) :=
    nevanlinnaKernel_integrable rep.ν UpperHalfPlane.I
  have hkernel_re :
      (fun t : ℝ => (nevanlinnaKernel t UpperHalfPlane.I).re) =
        fun _t : ℝ => 0 := by
    funext t
    rw [nevanlinnaKernel_apply_upperHalfPlane_I t]
    simp
  have hre :
      (∫ t : ℝ, nevanlinnaKernel t UpperHalfPlane.I
          ∂(rep.ν : Measure ℝ)).re =
        ∫ t : ℝ, (nevanlinnaKernel t UpperHalfPlane.I).re
          ∂(rep.ν : Measure ℝ) := by
    simpa using (integral_re hker_int).symm
  rw [hre, hkernel_re]
  simp

/-- The real constant in a Nevanlinna representation is read off at `z = i`. -/
theorem alpha_eq_re_apply_upperHalfPlane_I
    {F : ℍ → ℂ} (rep : NevanlinnaRep F) :
    rep.alpha = (F UpperHalfPlane.I).re := by
  have hF : (F UpperHalfPlane.I).re = rep.alpha := by
    calc
      (F UpperHalfPlane.I).re =
          ((rep.alpha : ℂ) + (rep.beta : ℝ) * (UpperHalfPlane.I : ℂ) +
            ∫ t : ℝ, nevanlinnaKernel t UpperHalfPlane.I
              ∂(rep.ν : Measure ℝ)).re := by
            rw [rep.formula UpperHalfPlane.I]
      _ = rep.alpha := by
            rw [Complex.add_re, Complex.add_re,
              rep.integral_kernel_apply_upperHalfPlane_I_re]
            simp [UpperHalfPlane.I]
  exact hF.symm

/-- Two representations of the same function have the same real constant. -/
theorem alpha_eq_of_same_function
    {F : ℍ → ℂ} (rep₁ rep₂ : NevanlinnaRep F) :
    rep₁.alpha = rep₂.alpha := by
  calc
    rep₁.alpha = (F UpperHalfPlane.I).re :=
      rep₁.alpha_eq_re_apply_upperHalfPlane_I
    _ = rep₂.alpha :=
      (rep₂.alpha_eq_re_apply_upperHalfPlane_I).symm

/--
Once the finite representing measures agree, the linear coefficient is recovered
by comparing the imaginary parts of the two formulas at `z = i`.
-/
theorem beta_eq_of_same_function_of_measure_eq
    {F : ℍ → ℂ} (rep₁ rep₂ : NevanlinnaRep F)
    (hν : rep₁.ν = rep₂.ν) :
    rep₁.beta = rep₂.beta := by
  apply NNReal.coe_injective
  have hcomplex :
      (rep₁.alpha : ℂ) + (rep₁.beta : ℝ) * (UpperHalfPlane.I : ℂ) +
          ∫ t : ℝ, nevanlinnaKernel t UpperHalfPlane.I
            ∂(rep₁.ν : Measure ℝ) =
        (rep₂.alpha : ℂ) + (rep₂.beta : ℝ) * (UpperHalfPlane.I : ℂ) +
          ∫ t : ℝ, nevanlinnaKernel t UpperHalfPlane.I
            ∂(rep₂.ν : Measure ℝ) := by
    rw [← rep₁.formula UpperHalfPlane.I, ← rep₂.formula UpperHalfPlane.I]
  have him := congrArg Complex.im hcomplex
  have halpha : rep₁.alpha = rep₂.alpha :=
    alpha_eq_of_same_function rep₁ rep₂
  have hintegral :
      (∫ t : ℝ, nevanlinnaKernel t UpperHalfPlane.I
          ∂(rep₁.ν : Measure ℝ)) =
        ∫ t : ℝ, nevanlinnaKernel t UpperHalfPlane.I
          ∂(rep₂.ν : Measure ℝ) := by
    rw [hν]
  rw [halpha, hintegral] at him
  have hbeta_real : (rep₁.beta : ℝ) = (rep₂.beta : ℝ) := by
    simpa [UpperHalfPlane.I, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im] using him
  exact hbeta_real

/-- Imaginary-part formula for the finite-measure Nevanlinna representation. -/
theorem im_eq
    {F : ℍ → ℂ} (rep : NevanlinnaRep F) (z : ℍ) :
    (F z).im =
      ((rep.beta : ℝ) +
        ∫ t : ℝ,
          (1 + t ^ (2 : ℕ)) /
            ‖(t : ℂ) - (z : ℂ)‖ ^ (2 : ℕ)
          ∂(rep.ν : Measure ℝ)) * (z : ℂ).im := by
  have hker_int :
      Integrable (fun t : ℝ => nevanlinnaKernel t z) (rep.ν : Measure ℝ) :=
    nevanlinnaKernel_integrable rep.ν z
  have himint :
      (∫ t : ℝ, (nevanlinnaKernel t z).im ∂(rep.ν : Measure ℝ)) =
        ∫ t : ℝ,
          (1 + t ^ (2 : ℕ)) * (z : ℂ).im /
            ‖(t : ℂ) - (z : ℂ)‖ ^ (2 : ℕ)
          ∂(rep.ν : Measure ℝ) := by
    refine integral_congr_ae ?_
    exact ae_of_all _ fun t => nevanlinnaKernel_im_eq t z
  have hfactor :
      (∫ t : ℝ,
          (1 + t ^ (2 : ℕ)) * (z : ℂ).im /
            ‖(t : ℂ) - (z : ℂ)‖ ^ (2 : ℕ)
          ∂(rep.ν : Measure ℝ)) =
        (∫ t : ℝ,
          (1 + t ^ (2 : ℕ)) /
            ‖(t : ℂ) - (z : ℂ)‖ ^ (2 : ℕ)
          ∂(rep.ν : Measure ℝ)) * (z : ℂ).im := by
    rw [← integral_mul_const]
    refine integral_congr_ae ?_
    exact ae_of_all _ fun t => by ring
  have him_integral :
      (∫ t : ℝ, nevanlinnaKernel t z ∂(rep.ν : Measure ℝ)).im =
        ∫ t : ℝ, (nevanlinnaKernel t z).im ∂(rep.ν : Measure ℝ) := by
    simpa using (integral_im hker_int).symm
  have hformula := congrArg Complex.im (rep.formula z)
  rw [hformula]
  simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im,
    Complex.ofReal_re, zero_mul]
  rw [him_integral, himint, hfactor]
  ring

/-- A finite-measure Nevanlinna representation has nonnegative imaginary part on `ℍ`. -/
theorem im_nonneg
    {F : ℍ → ℂ} (rep : NevanlinnaRep F) (z : ℍ) :
    0 ≤ (F z).im := by
  rw [rep.im_eq z]
  refine mul_nonneg ?_ (le_of_lt z.coe_im_pos)
  refine add_nonneg (NNReal.coe_nonneg _) ?_
  refine integral_nonneg_of_ae ?_
  exact ae_of_all _ fun t =>
    div_nonneg (by nlinarith [sq_nonneg t])
      (sq_nonneg (‖(t : ℂ) - (z : ℂ)‖))

/-- The theorem-facing Pick nonnegativity supplied by a finite-measure Nevanlinna representation. -/
theorem pick_nonnegative
    {F : ℍ → ℂ} (rep : NevanlinnaRep F) :
    ∀ z : ℍ, 0 ≤ (F z).im := by
  intro z
  exact rep.im_nonneg z

/-- A finite-measure Nevanlinna representation is holomorphic on the upper half-plane. -/
theorem mdifferentiable
    {F : ℍ → ℂ} (rep : NevanlinnaRep F) :
    MDiff F := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  let G : ℂ → ℂ := fun w =>
    (rep.alpha : ℂ) + ((rep.beta : ℝ) : ℂ) * w +
      ∫ t : ℝ, nevanlinnaKernelC t w ∂(rep.ν : Measure ℝ)
  have hG : DifferentiableAt ℂ G z := by
    have hconst : HasDerivAt (fun _w : ℂ => (rep.alpha : ℂ)) 0 z :=
      hasDerivAt_const z (rep.alpha : ℂ)
    have hlin : HasDerivAt (fun w : ℂ => ((rep.beta : ℝ) : ℂ) * w)
        ((rep.beta : ℝ) : ℂ) z := by
      convert (hasDerivAt_id z).const_mul (((rep.beta : ℝ) : ℂ)) using 1
      simp
    have hint := nevanlinnaKernelC_integral_hasDerivAt rep.ν hz
    exact ((hconst.add hlin).add hint).differentiableAt
  have h_event : (F ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 z] G := by
    let δ : ℝ := z.im / 2
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      exact half_pos hz
    filter_upwards [Metric.ball_mem_nhds z hδ_pos] with w hw
    have hδ_def : δ = z.im / 2 := rfl
    have hwim : 0 < w.im := lt_of_lt_of_le hδ_pos
      (nevanlinnaKernelC_ball_im_lower hδ_def hz hw)
    rw [Function.comp_apply, rep.formula (UpperHalfPlane.ofComplex w)]
    have hker :
        (∫ t : ℝ, nevanlinnaKernel t (UpperHalfPlane.ofComplex w) ∂(rep.ν : Measure ℝ)) =
          ∫ t : ℝ, nevanlinnaKernelC t w ∂(rep.ν : Measure ℝ) := by
      refine integral_congr_ae ?_
      exact ae_of_all _ fun t => by
        change nevanlinnaKernel t (UpperHalfPlane.ofComplex w) = nevanlinnaKernelC t w
        exact (nevanlinnaKernelC_eq_ofComplex t hwim).symm
    rw [hker]
    simp [G, UpperHalfPlane.ofComplex_apply_of_im_pos hwim]
  exact hG.congr_of_eventuallyEq h_event |>.differentiableWithinAt

/-- The finite-measure Nevanlinna representation supplies the Pick-function conditions. -/
theorem pick_of_rep
    {F : ℍ → ℂ} (rep : NevanlinnaRep F) :
    MDiff F ∧ ∀ z : ℍ, 0 ≤ (F z).im := by
  exact ⟨rep.mdifferentiable, rep.pick_nonnegative⟩

/-- Two Nevanlinna representations are equal once their data fields agree. -/
theorem eq_of_fields_eq
    {F : ℍ → ℂ} {rep₁ rep₂ : NevanlinnaRep F}
    (halpha : rep₁.alpha = rep₂.alpha)
    (hbeta : rep₁.beta = rep₂.beta)
    (hν : rep₁.ν = rep₂.ν) :
    rep₁ = rep₂ := by
  cases rep₁
  cases rep₂
  simp_all

end NevanlinnaRep

/--
Producer interface for the uniqueness part of Hiai's Nevanlinna representation.

The analytic core is the recovery of the constants and representing measure
from the represented function.  This contract isolates those ingredients while
allowing downstream theorem-facing wrappers to be typechecked without the full
Poisson/Stieltjes inversion proof.
-/
structure NevanlinnaRepUniquenessProducer where
  weightedMeasure_eq_of_same_function :
    ∀ {F : ℍ → ℂ} (rep₁ rep₂ : NevanlinnaRep F),
      nevanlinnaWeightedMeasure rep₁.ν = nevanlinnaWeightedMeasure rep₂.ν

/--
The imaginary part of a holomorphic upper-half-plane function is harmonic.

This theorem proves the harmonicity supplied by holomorphicity.
Nonnegativity of the imaginary part is a separate condition for Pick functions.
-/
theorem pick_im_harmonic
    {F : ℍ → ℂ} (hF : MDiff F) :
    InnerProductSpace.HarmonicOnNhd
      (fun z : ℂ => (F (UpperHalfPlane.ofComplex z)).im)
      {z : ℂ | 0 < z.im} := by
  have hdiff :
      DifferentiableOn ℂ (F ∘ UpperHalfPlane.ofComplex)
        {z : ℂ | 0 < z.im} := by
    exact UpperHalfPlane.mdifferentiable_iff.mp hF
  intro z hz
  have han : AnalyticAt ℂ (F ∘ UpperHalfPlane.ofComplex) z :=
    hdiff.analyticAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)
  simpa [Function.comp_apply] using han.harmonicAt_im

/--
The theorem-facing form of the previous result for Pick-type hypotheses:
holomorphicity gives harmonicity, while imaginary-part nonnegativity is the
second Pick condition.
-/
theorem pick_im_harmonic_nonnegative
    {F : ℍ → ℂ} (hF : MDiff F)
    (hF_nonneg : ∀ z : ℍ, 0 ≤ (F z).im) :
    InnerProductSpace.HarmonicOnNhd
        (fun z : ℂ => (F (UpperHalfPlane.ofComplex z)).im)
        {z : ℂ | 0 < z.im} ∧
      ∀ z : ℍ, 0 ≤ (F z).im := by
  exact ⟨pick_im_harmonic hF, hF_nonneg⟩

/--
Boundary-measure data supplied by the upper-half-plane Poisson representation
for a nonnegative harmonic function.

This is an interface for the analytic frontier: it records the measure, the
linear term at infinity, the weighted integrability needed for the Nevanlinna
weighted kernel, and the Poisson formula itself.
-/
structure PoissonBoundaryMeasureData (u : ℂ → ℝ) where
  boundaryMeasure : Measure ℝ
  slope : NNReal
  weight_lintegral_lt_top :
    (∫⁻ t : ℝ, nevanlinnaWeight t ∂boundaryMeasure) < ⊤
  poisson_formula :
    ∀ (x y : ℝ), 0 < y →
      u ((x : ℂ) + (y : ℂ) * Complex.I) =
        (slope : ℝ) * y +
          ∫ t : ℝ, upperHalfPlanePoissonKernel t x y ∂boundaryMeasure

/--
Producer interface for the upper-half-plane Poisson boundary-measure theorem.

The existence proof is not in Mathlib as a ready-made theorem.  Downstream
nodes can depend on this producer while the analytic construction remains a
separate frontier.
-/
structure UpperHalfPlanePoissonBoundaryProducer where
  produce :
    ∀ {u : ℂ → ℝ},
      InnerProductSpace.HarmonicOnNhd u {z : ℂ | 0 < z.im} →
      (∀ z : ℂ, 0 < z.im → 0 ≤ u z) →
        PoissonBoundaryMeasureData u

/--
Pick-facing adapter for a supplied upper-half-plane Poisson boundary producer.

This is not the bare existence theorem `poissonBoundaryMeasure_of_pick`; it only
packages the already proved harmonicity/nonnegativity of the Pick imaginary
part into the producer contract.
-/
def poissonBoundaryMeasure_of_pick_of_producer
    (producer : UpperHalfPlanePoissonBoundaryProducer)
    {F : ℍ → ℂ} (hF : MDiff F)
    (hF_nonneg : ∀ z : ℍ, 0 ≤ (F z).im) :
    PoissonBoundaryMeasureData
      (fun z : ℂ => (F (UpperHalfPlane.ofComplex z)).im) :=
  producer.produce (pick_im_harmonic hF) (by
    intro z _hz
    exact hF_nonneg (UpperHalfPlane.ofComplex z))

/-- The weighted-measure Nevanlinna representation (Hiai (2.14)). -/
structure WeightedNevanlinnaRep (F : ℍ → ℂ) where
  alpha : ℝ
  beta : NNReal
  μ : Measure ℝ
  weight_lintegral_lt_top : (∫⁻ t : ℝ, nevanlinnaWeight t ∂μ) < ⊤
  formula :
    ∀ z : ℍ,
      F z =
        (alpha : ℂ) + (beta : ℝ) * (z : ℂ) +
          ∫ t : ℝ, nevanlinnaWeightedKernel t z ∂μ

/--
Nevanlinna representation whose finite measure is supported on the complement
of the real interval `(a,b)`.
-/
structure NevanlinnaRepOnComplement (a b : ℝ) (F : ℍ → ℂ) extends NevanlinnaRep F where
  support_complement : (ν : Measure ℝ) (Set.Ioo a b) = 0

/-- A complement-supported finite Nevanlinna representation has no weighted mass on `(a,b)`. -/
theorem NevanlinnaRepOnComplement.weightedMeasure_zero
    {a b : ℝ} {F : ℍ → ℂ} (rep : NevanlinnaRepOnComplement a b F) :
    nevanlinnaWeightedMeasure rep.ν (Set.Ioo a b) = 0 :=
  nevanlinnaWeightedMeasure_zero_of_finiteMeasure_zero rep.support_complement

/--
Recover the finite-measure support condition from vanishing of the weighted
measure on `(a,b)`.
-/
def nevanlinnaRepOnComplement_of_weightedMeasure_zero
    {a b : ℝ} {F : ℍ → ℂ} (rep : NevanlinnaRep F)
    (hν : nevanlinnaWeightedMeasure rep.ν (Set.Ioo a b) = 0) :
    NevanlinnaRepOnComplement a b F where
  toNevanlinnaRep := rep
  support_complement :=
    nevanlinnaFiniteMeasure_zero_of_weightedMeasure_zero hν

/--
The upper-half-plane Pick domain that crosses the real interval `(a,b)`.

It consists of the non-real plane together with the real interval where the
Pick function is required to have real boundary values.
-/
def upperHalfPlanePickIntervalDomain (a b : ℝ) : Set ℂ :=
  {z : ℂ | z.im ≠ 0 ∨ z.re ∈ Set.Ioo a b}

/--
Pick-type analytic continuation across the real interval `(a,b)`.

This is the upper-half-plane analogue of `PickExtensionOnUnitInterval`, adapted
to an already-defined Pick function `F : ℍ → ℂ`.
-/
structure PickExtensionOnInterval (a b : ℝ) (F : ℍ → ℂ) where
  G : ℂ → ℂ
  analyticOn : AnalyticOn ℂ G (upperHalfPlanePickIntervalDomain a b)
  agreesOnUpper : ∀ z : ℍ, G (z : ℂ) = F z
  real_im_zero : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo a b → (G (x : ℂ)).im = 0
  mapsUpper : ∀ ⦃z : ℂ⦄, 0 < z.im → 0 ≤ (G z).im

/-- A Pick function belongs to the interval Pick class when it has such an extension. -/
def MemPickInterval (a b : ℝ) (F : ℍ → ℂ) : Prop :=
  Nonempty (PickExtensionOnInterval a b F)

/--
Producer interface for the interval-support part of Hiai Theorem 2.24.

The analytic core is the equivalence between continuation through `(a,b)` and
absence of representing mass on `(a,b)`.  This contract lets downstream theorem
wrappers typecheck while that analytic continuation theorem is developed.
-/
structure UpperHalfPlanePickIntervalSupportProducer where
  mem_pickInterval_of_nevanlinnaRepOnComplement :
    ∀ {a b : ℝ} {F : ℍ → ℂ},
      NevanlinnaRepOnComplement a b F → MemPickInterval a b F
  nevanlinnaRepOnComplement_of_mem_pickInterval :
    ∀ {a b : ℝ} {F : ℍ → ℂ},
      NevanlinnaRep F → MemPickInterval a b F → NevanlinnaRepOnComplement a b F

/--
Weighted-support producer for the interval-support part of Hiai Theorem 2.24.

The reverse direction now only has to show that the weighted boundary measure
has no mass on `(a,b)`.  The conversion back to the finite measure is proved
algebraically by `nevanlinnaFiniteMeasure_zero_of_weightedMeasure_zero`.
-/
structure UpperHalfPlanePickIntervalWeightedSupportProducer where
  mem_pickInterval_of_nevanlinnaRepOnComplement :
    ∀ {a b : ℝ} {F : ℍ → ℂ},
      NevanlinnaRepOnComplement a b F → MemPickInterval a b F
  weightedMeasure_zero_of_mem_pickInterval :
    ∀ {a b : ℝ} {F : ℍ → ℂ} (rep : NevanlinnaRep F),
      MemPickInterval a b F →
        nevanlinnaWeightedMeasure rep.ν (Set.Ioo a b) = 0

/-- A weighted-support producer supplies the older finite-support producer contract. -/
def upperHalfPlanePickIntervalSupportProducer_of_weightedSupportProducer
    (producer : UpperHalfPlanePickIntervalWeightedSupportProducer) :
    UpperHalfPlanePickIntervalSupportProducer where
  mem_pickInterval_of_nevanlinnaRepOnComplement := by
    intro a b F rep
    exact producer.mem_pickInterval_of_nevanlinnaRepOnComplement rep
  nevanlinnaRepOnComplement_of_mem_pickInterval := by
    intro a b F rep hF
    exact nevanlinnaRepOnComplement_of_weightedMeasure_zero rep
      (producer.weightedMeasure_zero_of_mem_pickInterval rep hF)

/-- Convert Hiai's finite-measure form (2.13) into the weighted form (2.14). -/
def weightedNevanlinnaRep_of_nevanlinnaRep
    {F : ℍ → ℂ} (rep : NevanlinnaRep F) :
    WeightedNevanlinnaRep F where
  alpha := rep.alpha
  beta := rep.beta
  μ := nevanlinnaWeightedMeasure rep.ν
  weight_lintegral_lt_top := nevanlinnaWeightedMeasure_weight_lintegral_lt_top rep.ν
  formula := by
    intro z
    rw [nevanlinnaWeightedMeasure_integral_weightedKernel rep.ν z]
    exact rep.formula z

/-- Convert Hiai's weighted form (2.14) back into the finite-measure form (2.13). -/
def nevanlinnaRep_of_weightedNevanlinnaRep
    {F : ℍ → ℂ} (rep : WeightedNevanlinnaRep F) :
    NevanlinnaRep F where
  alpha := rep.alpha
  beta := rep.beta
  ν := nevanlinnaFiniteMeasureOfWeighted rep.μ rep.weight_lintegral_lt_top
  formula := by
    intro z
    rw [nevanlinnaFiniteMeasureOfWeighted_integral_kernel
      rep.μ rep.weight_lintegral_lt_top z]
    exact rep.formula z

end

end Loewner
end TraceInequality
end Quantum
