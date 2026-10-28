import Quantum.TraceInequality.Loewner.HalfLine.KuboAndo

/-!
# Positive-ray operator convex representation kernels

This module records the representation-level part of Hiai Proposition 2.29.
It does not define operator convexity itself; it only packages the quadratic
kernel representation obtained by multiplying a half-line monotone
representation by `x - 1`.
-/

namespace Quantum.TraceInequality.Loewner

open Set MeasureTheory

open scoped NNReal

noncomputable section

/-- Quadratic kernel in the positive-ray operator convex representation. -/
def positiveRayOperatorConvexKernel (x t : ℝ) : ℝ :=
  (x - 1)^2 / (x + t)

private theorem measurable_positiveRayOperatorConvexKernel_right (x : ℝ) :
    Measurable fun t : ℝ => positiveRayOperatorConvexKernel x t := by
  unfold positiveRayOperatorConvexKernel
  measurability

/--
Representation-level form of Hiai Proposition 2.29 on `(0,∞)`.

The measure is supported on `[0,∞)` and satisfies the same weighted mass
condition as `HalfLineIntegralRep`.
-/
structure PositiveRayOperatorConvexRepBasic (f : ℝ → ℝ) where
  a : ℝ
  b : NNReal
  μ : Measure ℝ
  support : μ (Set.Ici (0 : ℝ))ᶜ = 0
  weight_lintegral_lt_top :
    (∫⁻ t : ℝ, halfLineWeight t ∂μ) < ⊤
  formula :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
      f x =
        f 1 + a * (x - 1) + (b : ℝ) * (x - 1)^2 +
          ∫ t : ℝ, positiveRayOperatorConvexKernel x t ∂μ

private theorem halfLineWeight_toReal_integrable_of_rep
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h) :
    Integrable (fun t : ℝ => (halfLineWeight t).toReal) rep.μ :=
  integrable_toReal_of_lintegral_ne_top measurable_halfLineWeight.aemeasurable
    rep.weight_lintegral_lt_top.ne

private theorem halfLineKernel_norm_le_const_mul_weight
    {x t : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) (ht : t ∈ Set.Ici (0 : ℝ)) :
    ‖halfLineKernel x t‖ ≤
      (max (‖x - 1‖ * x⁻¹) ‖x - 1‖) * (halfLineWeight t).toReal := by
  have hx0 : 0 < x := by simpa using hx
  have ht0 : 0 ≤ t := by simpa using ht
  have hden_pos : 0 < x + t := by linarith
  have hweight : (halfLineWeight t).toReal = (1 + t)⁻¹ := by
    rw [halfLineWeight, ENNReal.toReal_ofReal]
    exact inv_nonneg.mpr (by linarith)
  have hnonneg_weight : 0 ≤ (halfLineWeight t).toReal := ENNReal.toReal_nonneg
  have hratio :
      (x + t)⁻¹ ≤ (max x⁻¹ (1 : ℝ)) * (1 + t)⁻¹ := by
    have hden_one : 0 < 1 + t := by linarith
    have hxinv_nonneg : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
    by_cases hxle : x ≤ 1
    · have hxt_le : x * (1 + t) ≤ x + t := by
        nlinarith [mul_le_mul_of_nonneg_right hxle ht0]
      have hprod_pos : 0 < x * (1 + t) := mul_pos hx0 hden_one
      have hle_inv : (x + t)⁻¹ ≤ (x * (1 + t))⁻¹ :=
        (inv_le_inv₀ hden_pos hprod_pos).2 hxt_le
      have hmax : max x⁻¹ (1 : ℝ) = x⁻¹ := by
        rw [max_eq_left]
        exact (one_le_inv₀ hx0).2 hxle
      calc
        (x + t)⁻¹ ≤ (x * (1 + t))⁻¹ := hle_inv
        _ = x⁻¹ * (1 + t)⁻¹ := by rw [mul_inv]
        _ = (max x⁻¹ (1 : ℝ)) * (1 + t)⁻¹ := by rw [hmax]
    · have hxge : 1 ≤ x := le_of_not_ge hxle
      have hle_inv : (x + t)⁻¹ ≤ (1 + t)⁻¹ :=
        (inv_le_inv₀ hden_pos hden_one).2 (by linarith)
      have hmax : max x⁻¹ (1 : ℝ) = 1 := by
        rw [max_eq_right]
        exact inv_le_one_of_one_le₀ hxge
      calc
        (x + t)⁻¹ ≤ (1 + t)⁻¹ := hle_inv
        _ = (max x⁻¹ (1 : ℝ)) * (1 + t)⁻¹ := by rw [hmax, one_mul]
  have hconst :
      ‖x - 1‖ * max x⁻¹ (1 : ℝ) =
        max (‖x - 1‖ * x⁻¹) ‖x - 1‖ := by
    rw [mul_max_of_nonneg x⁻¹ (1 : ℝ) (norm_nonneg (x - 1)), mul_one]
  unfold halfLineKernel
  rw [hweight]
  calc
    ‖(x - 1) / (x + t)‖ =
        ‖x - 1‖ * ‖(x + t)⁻¹‖ := by
          rw [div_eq_mul_inv, norm_mul]
    _ = ‖x - 1‖ * (x + t)⁻¹ := by
          rw [Real.norm_of_nonneg (inv_nonneg.mpr hden_pos.le)]
    _ ≤ ‖x - 1‖ * (max x⁻¹ (1 : ℝ) * (1 + t)⁻¹) :=
          mul_le_mul_of_nonneg_left hratio (norm_nonneg _)
    _ = (max (‖x - 1‖ * x⁻¹) ‖x - 1‖) * (1 + t)⁻¹ := by
          rw [← mul_assoc, hconst]

private theorem halfLineKernel_integrable_of_rep
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Integrable (fun t : ℝ => halfLineKernel x t) rep.μ := by
  have hweight_int := halfLineWeight_toReal_integrable_of_rep rep
  have hbound_int :
      Integrable
        (fun t : ℝ =>
          (max (‖x - 1‖ * x⁻¹) ‖x - 1‖) * (halfLineWeight t).toReal)
        rep.μ :=
    hweight_int.const_mul (max (‖x - 1‖ * x⁻¹) ‖x - 1‖)
  refine Integrable.mono hbound_int
    (by
      have hmeas : Measurable fun t : ℝ => halfLineKernel x t := by
        unfold halfLineKernel
        measurability
      exact hmeas.aestronglyMeasurable)
    ?_
  filter_upwards [rep.ae_mem_Ici] with t ht
  have hC_nonneg : 0 ≤ max (‖x - 1‖ * x⁻¹) ‖x - 1‖ :=
    le_trans (norm_nonneg (x - 1))
      (le_max_right (‖x - 1‖ * x⁻¹) ‖x - 1‖)
  have hnonneg :
      0 ≤ (max (‖x - 1‖ * x⁻¹) ‖x - 1‖) *
          (halfLineWeight t).toReal := by
    exact mul_nonneg hC_nonneg ENNReal.toReal_nonneg
  rw [Real.norm_of_nonneg hnonneg]
  exact halfLineKernel_norm_le_const_mul_weight hx ht

private theorem positiveRayOperatorConvexKernel_eq_mul_halfLineKernel
    (x t : ℝ) :
    positiveRayOperatorConvexKernel x t =
      (x - 1) * halfLineKernel x t := by
  unfold positiveRayOperatorConvexKernel halfLineKernel
  ring

private theorem positiveRayOperatorConvexKernel_integrable_of_rep
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Integrable (fun t : ℝ => positiveRayOperatorConvexKernel x t) rep.μ := by
  have hhalf := halfLineKernel_integrable_of_rep rep hx
  refine hhalf.const_mul (x - 1) |>.congr ?_
  exact ae_of_all _ fun t => by
    exact (positiveRayOperatorConvexKernel_eq_mul_halfLineKernel x t).symm

private theorem positiveRayOperatorConvexKernel_integral_eq
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h)
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    (∫ t : ℝ, positiveRayOperatorConvexKernel x t ∂rep.μ) =
      (x - 1) * ∫ t : ℝ, halfLineKernel x t ∂rep.μ := by
  have hhalf := halfLineKernel_integrable_of_rep rep hx
  calc
    (∫ t : ℝ, positiveRayOperatorConvexKernel x t ∂rep.μ) =
        ∫ t : ℝ, (x - 1) * halfLineKernel x t ∂rep.μ := by
          refine integral_congr_ae ?_
          exact ae_of_all _ fun t => by
            rw [positiveRayOperatorConvexKernel_eq_mul_halfLineKernel]
    _ = (x - 1) * ∫ t : ℝ, halfLineKernel x t ∂rep.μ := by
          rw [integral_const_mul]

/--
Build the quadratic-kernel representation from a half-line integral
representation of the slope function `h` in `f x = f 1 + (x - 1) * h x`.
-/
noncomputable def positiveRayOperatorConvexRepBasic_of_halfLineIntegralRep
    {f h : ℝ → ℝ}
    (hf : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
      f x = f 1 + (x - 1) * h x)
    (rep : HalfLineIntegralRep h) :
    PositiveRayOperatorConvexRepBasic f where
  a := h 1
  b := rep.b
  μ := rep.μ
  support := rep.support
  weight_lintegral_lt_top := rep.weight_lintegral_lt_top
  formula := by
    intro x hx
    have hrep := rep.formula hx
    have hquad := positiveRayOperatorConvexKernel_integral_eq rep hx
    calc
      f x = f 1 + (x - 1) * h x := hf hx
      _ = f 1 + (h 1) * (x - 1) + (rep.b : ℝ) * (x - 1)^2 +
          ∫ t : ℝ, positiveRayOperatorConvexKernel x t ∂rep.μ := by
            rw [hrep, hquad]
            ring

/--
The basic positive-ray operator convex representation is equivalent to a
half-line integral representation of the slope `h` in
`f x = f 1 + (x - 1) * h x` on `(0,∞)`.
-/
theorem nonempty_positiveRayOperatorConvexRepBasic_iff_exists_halfLineIntegralRep
    {f : ℝ → ℝ} :
    Nonempty (PositiveRayOperatorConvexRepBasic f) ↔
      ∃ h : ℝ → ℝ,
        (∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
          f x = f 1 + (x - 1) * h x) ∧
        Nonempty (HalfLineIntegralRep h) := by
  constructor
  · rintro ⟨rep⟩
    let h : ℝ → ℝ :=
      fun x : ℝ =>
        rep.a + (rep.b : ℝ) * (x - 1) +
          ∫ t : ℝ, halfLineKernel x t ∂rep.μ
    have hrep : HalfLineIntegralRep h := by
      refine
        { b := rep.b
          μ := rep.μ
          support := rep.support
          weight_lintegral_lt_top := rep.weight_lintegral_lt_top
          formula := ?_ }
      intro x hx
      have h1 : h 1 = rep.a := by
        simp [h, halfLineKernel]
      calc
        h x =
            rep.a + (rep.b : ℝ) * (x - 1) +
              ∫ t : ℝ, halfLineKernel x t ∂rep.μ := rfl
        _ = h 1 + (rep.b : ℝ) * (x - 1) +
            ∫ t : ℝ, halfLineKernel x t ∂rep.μ := by
              rw [h1]
    refine ⟨h, ?_, ⟨hrep⟩⟩
    · intro x hx
      have hformula := rep.formula hx
      have hquad :
          (∫ t : ℝ, positiveRayOperatorConvexKernel x t ∂rep.μ) =
            (x - 1) * ∫ t : ℝ, halfLineKernel x t ∂rep.μ := by
        calc
          (∫ t : ℝ, positiveRayOperatorConvexKernel x t ∂rep.μ) =
              ∫ t : ℝ, (x - 1) * halfLineKernel x t ∂rep.μ := by
                refine integral_congr_ae ?_
                exact ae_of_all _ fun t => by
                  rw [positiveRayOperatorConvexKernel_eq_mul_halfLineKernel]
          _ = (x - 1) * ∫ t : ℝ, halfLineKernel x t ∂rep.μ := by
                rw [integral_const_mul]
      calc
        f x =
            f 1 + rep.a * (x - 1) + (rep.b : ℝ) * (x - 1)^2 +
              ∫ t : ℝ, positiveRayOperatorConvexKernel x t ∂rep.μ := hformula
        _ = f 1 + (x - 1) * h x := by
              rw [hquad]
              simp [h]
              ring
  · rintro ⟨h, hf, ⟨rep⟩⟩
    exact ⟨positiveRayOperatorConvexRepBasic_of_halfLineIntegralRep hf rep⟩

/-- Normalized kernel in Hiai Proposition 2.30. -/
def positiveRayOperatorConvexNormalizedKernel (x t : ℝ) : ℝ :=
  x / (1 + t) - x / (x + t)

/-- Weighted-mass integrand for the normalized operator convex representation. -/
def positiveRayOperatorConvexNormalizedWeight (t : ℝ) : ENNReal :=
  ENNReal.ofReal (((1 + t)^2)⁻¹)

private theorem measurable_positiveRayOperatorConvexNormalizedKernel_right (x : ℝ) :
    Measurable fun t : ℝ => positiveRayOperatorConvexNormalizedKernel x t := by
  unfold positiveRayOperatorConvexNormalizedKernel
  measurability

private theorem measurable_positiveRayOperatorConvexNormalizedWeight :
    Measurable positiveRayOperatorConvexNormalizedWeight := by
  have hmeas : Measurable fun t : ℝ => ((1 + t)^2)⁻¹ :=
    ((measurable_const.add measurable_id).pow_const 2).inv
  simpa [positiveRayOperatorConvexNormalizedWeight] using
    ENNReal.measurable_ofReal.comp hmeas

/--
Representation-level form of Hiai Proposition 2.30.

The representing measure is supported on `(0,∞)` and is controlled by the
square weight `(1+t)^{-2}`.
-/
structure PositiveRayOperatorConvexRepNormalized (f : ℝ → ℝ) where
  a : ℝ
  b : NNReal
  ν : Measure ℝ
  support : ν (Set.Ioi (0 : ℝ))ᶜ = 0
  square_weight_lintegral_lt_top :
    (∫⁻ t : ℝ, positiveRayOperatorConvexNormalizedWeight t ∂ν) < ⊤
  formula :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ici (0 : ℝ) →
      f x =
        f 0 + a * x + (b : ℝ) * x^2 +
          ∫ t : ℝ, positiveRayOperatorConvexNormalizedKernel x t ∂ν

private def positiveRayOperatorConvexNormalizedDensity (t : ℝ) : ENNReal :=
  ENNReal.ofReal ((1 + t)^2)

private theorem measurable_positiveRayOperatorConvexNormalizedDensity :
    Measurable positiveRayOperatorConvexNormalizedDensity := by
  have hmeas : Measurable fun t : ℝ => (1 + t)^2 :=
    (measurable_const.add measurable_id).pow_const 2
  simpa [positiveRayOperatorConvexNormalizedDensity] using
    ENNReal.measurable_ofReal.comp hmeas

private theorem positiveRayOperatorConvexNormalizedDensity_ne_top_ae
    (μ : Measure ℝ) :
    ∀ᵐ t ∂μ, positiveRayOperatorConvexNormalizedDensity t < (⊤ : ENNReal) := by
  exact ae_of_all _ fun t => by
    rw [positiveRayOperatorConvexNormalizedDensity]
    exact ENNReal.ofReal_lt_top

private def positiveRayOperatorConvexNormalizedMeasure
    (ν : FiniteMeasure ℝ) : Measure ℝ :=
  (ν : Measure ℝ).withDensity positiveRayOperatorConvexNormalizedDensity

private theorem positiveRayOperatorConvexNormalizedMeasure_support
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) :
    positiveRayOperatorConvexNormalizedMeasure rep.ν (Set.Ioi (0 : ℝ))ᶜ = 0 := by
  have hac :
      positiveRayOperatorConvexNormalizedMeasure rep.ν ≪ (rep.ν : Measure ℝ) := by
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  exact hac rep.support

private theorem positiveRayOperatorConvexNormalized_density_mul_weight_le_one
    {t : ℝ} (ht : t ∈ Set.Ioi (0 : ℝ)) :
    positiveRayOperatorConvexNormalizedDensity t *
        positiveRayOperatorConvexNormalizedWeight t ≤ 1 := by
  have htpos : 0 < t := by simpa using ht
  have hden_pos : 0 < 1 + t := by linarith
  have hsquare_nonneg : 0 ≤ (1 + t)^2 := sq_nonneg (1 + t)
  have hinv_nonneg : 0 ≤ ((1 + t)^2)⁻¹ := inv_nonneg.mpr hsquare_nonneg
  have hreal : (1 + t)^2 * ((1 + t)^2)⁻¹ = 1 := by
    field_simp [hden_pos.ne']
  calc
    positiveRayOperatorConvexNormalizedDensity t *
        positiveRayOperatorConvexNormalizedWeight t =
        ENNReal.ofReal ((1 + t)^2) *
          ENNReal.ofReal (((1 + t)^2)⁻¹) := by
            rfl
    _ = ENNReal.ofReal ((1 + t)^2 * ((1 + t)^2)⁻¹) := by
          rw [ENNReal.ofReal_mul hsquare_nonneg]
    _ = 1 := by rw [hreal, ENNReal.ofReal_one]
    _ ≤ 1 := le_rfl

private theorem positiveRayOperatorConvexNormalizedMeasure_weight_lintegral_lt_top
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) :
    (∫⁻ t : ℝ, positiveRayOperatorConvexNormalizedWeight t
        ∂positiveRayOperatorConvexNormalizedMeasure rep.ν) < ⊤ := by
  have hrewrite :
      (∫⁻ t : ℝ, positiveRayOperatorConvexNormalizedWeight t
          ∂positiveRayOperatorConvexNormalizedMeasure rep.ν) =
        ∫⁻ t : ℝ,
          positiveRayOperatorConvexNormalizedDensity t *
            positiveRayOperatorConvexNormalizedWeight t
            ∂(rep.ν : Measure ℝ) := by
    have h :=
      MeasureTheory.lintegral_withDensity_eq_lintegral_mul
        (rep.ν : Measure ℝ)
        measurable_positiveRayOperatorConvexNormalizedDensity
        measurable_positiveRayOperatorConvexNormalizedWeight
    simpa [positiveRayOperatorConvexNormalizedMeasure,
      positiveRayOperatorConvexNormalizedDensity,
      positiveRayOperatorConvexNormalizedWeight] using h
  have hbound :
      ∀ᵐ t ∂(rep.ν : Measure ℝ),
        positiveRayOperatorConvexNormalizedDensity t *
          positiveRayOperatorConvexNormalizedWeight t ≤ 1 := by
    filter_upwards [(mem_ae_iff).mpr rep.support] with t ht
    exact positiveRayOperatorConvexNormalized_density_mul_weight_le_one ht
  rw [hrewrite]
  calc
    (∫⁻ t : ℝ,
        positiveRayOperatorConvexNormalizedDensity t *
          positiveRayOperatorConvexNormalizedWeight t
          ∂(rep.ν : Measure ℝ)) ≤
        ∫⁻ _t : ℝ, (1 : ENNReal) ∂(rep.ν : Measure ℝ) :=
          lintegral_mono_ae hbound
    _ = (rep.ν : Measure ℝ) Set.univ := by simp
    _ < ⊤ := measure_lt_top (rep.ν : Measure ℝ) Set.univ

private theorem positiveRayOperatorConvexNormalizedKernel_density_eq
    {x t : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) (ht : t ∈ Set.Ioi (0 : ℝ)) :
    (positiveRayOperatorConvexNormalizedDensity t).toReal *
        positiveRayOperatorConvexNormalizedKernel x t =
      (x - 1) * positiveRayKuboAndoKernel x t := by
  have hxpos : 0 < x := by simpa using hx
  have htpos : 0 < t := by simpa using ht
  have h1t_pos : 0 < 1 + t := by linarith
  have hxt_pos : 0 < x + t := by linarith
  have hdensity :
      (positiveRayOperatorConvexNormalizedDensity t).toReal = (1 + t)^2 := by
    rw [positiveRayOperatorConvexNormalizedDensity, ENNReal.toReal_ofReal]
    exact sq_nonneg (1 + t)
  rw [hdensity]
  unfold positiveRayOperatorConvexNormalizedKernel positiveRayKuboAndoKernel
  field_simp [h1t_pos.ne', hxt_pos.ne']
  ring

private theorem positiveRayOperatorConvexNormalizedMeasure_integral_kernel
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h)
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    (∫ t : ℝ, positiveRayOperatorConvexNormalizedKernel x t
        ∂positiveRayOperatorConvexNormalizedMeasure rep.ν) =
      (x - 1) *
        ∫ t : ℝ, positiveRayKuboAndoKernel x t ∂(rep.ν : Measure ℝ) := by
  have hwd :
      (∫ t : ℝ, positiveRayOperatorConvexNormalizedKernel x t
          ∂positiveRayOperatorConvexNormalizedMeasure rep.ν) =
        ∫ t : ℝ,
          (positiveRayOperatorConvexNormalizedDensity t).toReal •
            positiveRayOperatorConvexNormalizedKernel x t
          ∂(rep.ν : Measure ℝ) := by
    exact integral_withDensity_eq_integral_toReal_smul
      measurable_positiveRayOperatorConvexNormalizedDensity
      (positiveRayOperatorConvexNormalizedDensity_ne_top_ae (rep.ν : Measure ℝ))
      (fun t : ℝ => positiveRayOperatorConvexNormalizedKernel x t)
  have hkernel :
      (fun t : ℝ =>
          (positiveRayOperatorConvexNormalizedDensity t).toReal •
            positiveRayOperatorConvexNormalizedKernel x t)
        =ᵐ[(rep.ν : Measure ℝ)]
        fun t : ℝ => (x - 1) * positiveRayKuboAndoKernel x t := by
    filter_upwards [(mem_ae_iff).mpr rep.support] with t ht
    simpa [smul_eq_mul] using
      positiveRayOperatorConvexNormalizedKernel_density_eq hx ht
  calc
    (∫ t : ℝ, positiveRayOperatorConvexNormalizedKernel x t
        ∂positiveRayOperatorConvexNormalizedMeasure rep.ν) =
        ∫ t : ℝ,
          (positiveRayOperatorConvexNormalizedDensity t).toReal •
            positiveRayOperatorConvexNormalizedKernel x t
          ∂(rep.ν : Measure ℝ) := hwd
    _ = ∫ t : ℝ, (x - 1) * positiveRayKuboAndoKernel x t
          ∂(rep.ν : Measure ℝ) := integral_congr_ae hkernel
    _ = (x - 1) *
        ∫ t : ℝ, positiveRayKuboAndoKernel x t ∂(rep.ν : Measure ℝ) := by
          rw [integral_const_mul]

private theorem positiveRayOperatorConvexNormalizedKernel_zero :
    (fun t : ℝ => positiveRayOperatorConvexNormalizedKernel 0 t) = fun _t : ℝ => 0 := by
  funext t
  simp [positiveRayOperatorConvexNormalizedKernel]

/--
Build the endpoint-normalized quadratic-kernel representation from a
Kubo--Ando representation of the slope function in
`f x = f 1 + (x - 1) * h x`.
-/
noncomputable def positiveRayOperatorConvexRepNormalized_of_positiveRayKuboAndoRep
    {f h : ℝ → ℝ}
    (hf : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
      f x = f 1 + (x - 1) * h x)
    (hf0 : f 0 = f 1 - h 0)
    (rep : PositiveRayKuboAndoRep h) :
    PositiveRayOperatorConvexRepNormalized f where
  a := h 0 - (rep.b : ℝ)
  b := rep.b
  ν := positiveRayOperatorConvexNormalizedMeasure rep.ν
  support := positiveRayOperatorConvexNormalizedMeasure_support rep
  square_weight_lintegral_lt_top :=
    positiveRayOperatorConvexNormalizedMeasure_weight_lintegral_lt_top rep
  formula := by
    intro x hx
    have hxle : 0 ≤ x := by simpa using hx
    rcases lt_or_eq_of_le hxle with hxpos | hzero
    · have hxIoi : x ∈ Set.Ioi (0 : ℝ) := by simpa using hxpos
      have hrep := rep.formula hx
      have hint :=
        positiveRayOperatorConvexNormalizedMeasure_integral_kernel rep hxIoi
      calc
        f x = f 1 + (x - 1) * h x := hf hxIoi
        _ = f 0 + (h 0 - (rep.b : ℝ)) * x + (rep.b : ℝ) * x^2 +
            ∫ t : ℝ, positiveRayOperatorConvexNormalizedKernel x t
              ∂positiveRayOperatorConvexNormalizedMeasure rep.ν := by
              rw [hrep, hint, hf0]
              ring
    · subst x
      simp [positiveRayOperatorConvexNormalizedKernel_zero, hf0]

/--
Finite-right-derivative kernel in Hiai Proposition 2.31.
-/
def positiveRayOperatorConvexFiniteRightDerivativeKernel (x t : ℝ) : ℝ :=
  x^2 * (1 + t) / (x + t)

/--
Representation-level form of Hiai Proposition 2.31.

The representing measure is finite and supported on `(0,∞)`.
-/
structure PositiveRayOperatorConvexRepFiniteRightDerivative (f : ℝ → ℝ) where
  a : ℝ
  b : NNReal
  ν : FiniteMeasure ℝ
  support : (ν : Measure ℝ) (Set.Ioi (0 : ℝ))ᶜ = 0
  formula :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ici (0 : ℝ) →
      f x =
        f 0 + a * x + (b : ℝ) * x^2 +
          ∫ t : ℝ, positiveRayOperatorConvexFiniteRightDerivativeKernel x t
            ∂(ν : Measure ℝ)

private theorem positiveRayOperatorConvexFiniteRightDerivativeKernel_eq_mul_kubo
    (x t : ℝ) :
    positiveRayOperatorConvexFiniteRightDerivativeKernel x t =
      x * positiveRayKuboAndoKernel x t := by
  unfold positiveRayOperatorConvexFiniteRightDerivativeKernel positiveRayKuboAndoKernel
  ring

private theorem positiveRayOperatorConvexFiniteRightDerivativeKernel_integral_eq
    {h : ℝ → ℝ} (rep : PositiveRayKuboAndoRep h) (x : ℝ) :
    (∫ t : ℝ, positiveRayOperatorConvexFiniteRightDerivativeKernel x t
        ∂(rep.ν : Measure ℝ)) =
      x * ∫ t : ℝ, positiveRayKuboAndoKernel x t ∂(rep.ν : Measure ℝ) := by
  calc
    (∫ t : ℝ, positiveRayOperatorConvexFiniteRightDerivativeKernel x t
        ∂(rep.ν : Measure ℝ)) =
        ∫ t : ℝ, x * positiveRayKuboAndoKernel x t
          ∂(rep.ν : Measure ℝ) := by
          refine integral_congr_ae ?_
          exact ae_of_all _ fun t =>
            positiveRayOperatorConvexFiniteRightDerivativeKernel_eq_mul_kubo x t
    _ = x * ∫ t : ℝ, positiveRayKuboAndoKernel x t
        ∂(rep.ν : Measure ℝ) := by
          rw [integral_const_mul]

private theorem positiveRayOperatorConvexFiniteRightDerivativeKernel_zero :
    (fun t : ℝ => positiveRayOperatorConvexFiniteRightDerivativeKernel 0 t) =
      fun _t : ℝ => 0 := by
  funext t
  simp [positiveRayOperatorConvexFiniteRightDerivativeKernel]

/--
Build the finite-right-derivative quadratic-kernel representation from a
Kubo--Ando representation of the slope function in `f x = f 0 + x * h x`.
-/
noncomputable def
    positiveRayOperatorConvexRepFiniteRightDerivative_of_positiveRayKuboAndoRep
    {f h : ℝ → ℝ}
    (hf : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
      f x = f 0 + x * h x)
    (rep : PositiveRayKuboAndoRep h) :
    PositiveRayOperatorConvexRepFiniteRightDerivative f where
  a := h 0
  b := rep.b
  ν := rep.ν
  support := rep.support
  formula := by
    intro x hx
    have hxle : 0 ≤ x := by simpa using hx
    rcases lt_or_eq_of_le hxle with hxpos | hzero
    · have hxIoi : x ∈ Set.Ioi (0 : ℝ) := by simpa using hxpos
      have hrep := rep.formula hx
      have hint :=
        positiveRayOperatorConvexFiniteRightDerivativeKernel_integral_eq rep x
      calc
        f x = f 0 + x * h x := hf hxIoi
        _ = f 0 + h 0 * x + (rep.b : ℝ) * x^2 +
            ∫ t : ℝ, positiveRayOperatorConvexFiniteRightDerivativeKernel x t
              ∂(rep.ν : Measure ℝ) := by
              rw [hrep, hint]
              ring
    · subst x
      simp [positiveRayOperatorConvexFiniteRightDerivativeKernel_zero]

/--
The finite-right-derivative quadratic representation is equivalent to a
Kubo--Ando representation of the quotient slope `h` in
`f x = f 0 + x * h x` on `(0,∞)`.
-/
theorem nonempty_positiveRayOperatorConvexRepFiniteRightDerivative_iff_exists_kuboAndo_quotient
    {f : ℝ → ℝ} :
    Nonempty (PositiveRayOperatorConvexRepFiniteRightDerivative f) ↔
      ∃ h : ℝ → ℝ,
        (∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
          f x = f 0 + x * h x) ∧
        Nonempty (PositiveRayKuboAndoRep h) := by
  constructor
  · rintro ⟨rep⟩
    let h : ℝ → ℝ :=
      fun x : ℝ =>
        rep.a + (rep.b : ℝ) * x +
          ∫ t : ℝ, positiveRayKuboAndoKernel x t ∂(rep.ν : Measure ℝ)
    refine ⟨h, ?_, ?_⟩
    · intro x hx
      have hxIci : x ∈ Set.Ici (0 : ℝ) := by
        exact le_of_lt (by simpa using hx)
      have hformula := rep.formula hxIci
      have hint :
          (∫ t : ℝ, positiveRayOperatorConvexFiniteRightDerivativeKernel x t
              ∂(rep.ν : Measure ℝ)) =
            x * ∫ t : ℝ, positiveRayKuboAndoKernel x t
              ∂(rep.ν : Measure ℝ) := by
        calc
          (∫ t : ℝ, positiveRayOperatorConvexFiniteRightDerivativeKernel x t
              ∂(rep.ν : Measure ℝ)) =
              ∫ t : ℝ, x * positiveRayKuboAndoKernel x t
                ∂(rep.ν : Measure ℝ) := by
                refine integral_congr_ae ?_
                exact ae_of_all _ fun t =>
                  positiveRayOperatorConvexFiniteRightDerivativeKernel_eq_mul_kubo x t
          _ = x * ∫ t : ℝ, positiveRayKuboAndoKernel x t
              ∂(rep.ν : Measure ℝ) := by
                rw [integral_const_mul]
      calc
        f x =
            f 0 + rep.a * x + (rep.b : ℝ) * x^2 +
              ∫ t : ℝ, positiveRayOperatorConvexFiniteRightDerivativeKernel x t
                ∂(rep.ν : Measure ℝ) := hformula
        _ = f 0 + x * h x := by
              rw [hint]
              simp [h]
              ring
    · refine ⟨?_⟩
      exact
        { b := rep.b
          ν := rep.ν
          support := rep.support
          formula := by
            intro x hx
            simp [h, positiveRayKuboAndoKernel] }
  · rintro ⟨h, hf, ⟨rep⟩⟩
    exact
      ⟨positiveRayOperatorConvexRepFiniteRightDerivative_of_positiveRayKuboAndoRep
        hf rep⟩

/--
Extract the Kubo--Ando quotient from a finite-right-derivative operator-convex
representation, retaining the endpoint value of the quotient.
-/
theorem exists_kuboAndo_quotient_of_positiveRayOperatorConvexRepFiniteRightDerivative
    {f : ℝ → ℝ} (rep : PositiveRayOperatorConvexRepFiniteRightDerivative f) :
    ∃ h : ℝ → ℝ,
      (∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → f x = f 0 + x * h x) ∧
      Nonempty (PositiveRayKuboAndoRep h) ∧
      h 0 = rep.a := by
  let h : ℝ → ℝ :=
    fun x : ℝ =>
      rep.a + (rep.b : ℝ) * x +
        ∫ t : ℝ, positiveRayKuboAndoKernel x t ∂(rep.ν : Measure ℝ)
  refine ⟨h, ?_, ?_, ?_⟩
  · intro x hx
    have hxIci : x ∈ Set.Ici (0 : ℝ) := by
      exact le_of_lt (by simpa using hx)
    have hformula := rep.formula hxIci
    have hint :
        (∫ t : ℝ, positiveRayOperatorConvexFiniteRightDerivativeKernel x t
            ∂(rep.ν : Measure ℝ)) =
          x * ∫ t : ℝ, positiveRayKuboAndoKernel x t
            ∂(rep.ν : Measure ℝ) := by
      calc
        (∫ t : ℝ, positiveRayOperatorConvexFiniteRightDerivativeKernel x t
            ∂(rep.ν : Measure ℝ)) =
            ∫ t : ℝ, x * positiveRayKuboAndoKernel x t
              ∂(rep.ν : Measure ℝ) := by
              refine integral_congr_ae ?_
              exact ae_of_all _ fun t =>
                positiveRayOperatorConvexFiniteRightDerivativeKernel_eq_mul_kubo x t
        _ = x * ∫ t : ℝ, positiveRayKuboAndoKernel x t
            ∂(rep.ν : Measure ℝ) := by
              rw [integral_const_mul]
    calc
      f x =
          f 0 + rep.a * x + (rep.b : ℝ) * x^2 +
            ∫ t : ℝ, positiveRayOperatorConvexFiniteRightDerivativeKernel x t
              ∂(rep.ν : Measure ℝ) := hformula
      _ = f 0 + x * h x := by
            rw [hint]
            simp [h]
            ring
  · refine ⟨?_⟩
    exact
      { b := rep.b
        ν := rep.ν
        support := rep.support
        formula := by
          intro x hx
          simp [h, positiveRayKuboAndoKernel] }
  · simp [h, positiveRayKuboAndoKernel]

end

end Quantum.TraceInequality.Loewner
