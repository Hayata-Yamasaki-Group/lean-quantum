import Quantum.TraceInequality.Loewner.HalfLine.HalfLineToUnitInterval
import Quantum.TraceInequality.Loewner.UnitInterval.MeasureUniqueness

/-!
# Uniqueness package for half-line integral representations

This module contains the slope limit, coefficient uniqueness, measure
uniqueness, and the bundled Hiai--Matsumoto Theorem 2.26 equivalence package.
-/

namespace Quantum.TraceInequality.Loewner

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

private theorem halfLineWeight_toReal_integrable
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h) :
    Integrable (fun t : ℝ => (halfLineWeight t).toReal) rep.μ := by
  exact integrable_toReal_of_lintegral_ne_top measurable_halfLineWeight.aemeasurable
    rep.weight_lintegral_lt_top.ne

private theorem halfLineKernel_div_norm_le_weight_toReal
    {x t : ℝ} (hx : 1 ≤ x) (ht : t ∈ Set.Ici (0 : ℝ)) :
    ‖halfLineKernel x t / x‖ ≤ (halfLineWeight t).toReal := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have ht0 : 0 ≤ t := by simpa using ht
  have hxtpos : 0 < x + t := by linarith
  have hwtpos : 0 < 1 + t := by linarith
  have hnonneg : 0 ≤ halfLineKernel x t / x := by
    have hxminus : 0 ≤ x - 1 := by linarith
    unfold halfLineKernel
    exact div_nonneg (div_nonneg hxminus hxtpos.le) hxpos.le
  have hweight : (halfLineWeight t).toReal = (1 + t)⁻¹ := by
    rw [halfLineWeight, ENNReal.toReal_ofReal]
    exact inv_nonneg.mpr hwtpos.le
  rw [Real.norm_of_nonneg hnonneg, hweight]
  unfold halfLineKernel
  field_simp [hxpos.ne', hxtpos.ne', hwtpos.ne']
  nlinarith [sq_nonneg (x - 1)]

private theorem halfLineKernel_div_tendsto_zero_atTop
    (t : ℝ) :
    Tendsto (fun x : ℝ => halfLineKernel x t / x) atTop (𝓝 (0 : ℝ)) := by
  have hlim :
      Tendsto (fun x : ℝ => (1 - x⁻¹) * (x + t)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    have hleft :
        Tendsto (fun x : ℝ => 1 - x⁻¹) atTop (𝓝 (1 - (0 : ℝ))) :=
      tendsto_const_nhds.sub tendsto_inv_atTop_zero
    have hright :
        Tendsto (fun x : ℝ => (x + t)⁻¹) atTop (𝓝 (0 : ℝ)) := by
      exact (tendsto_atTop_add_const_right atTop t tendsto_id).inv_tendsto_atTop
    simpa using hleft.mul hright
  have heq :
      (fun x : ℝ => halfLineKernel x t / x) =ᶠ[atTop]
        fun x : ℝ => (1 - x⁻¹) * (x + t)⁻¹ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hxne : x ≠ 0 := hxpos.ne'
    unfold halfLineKernel
    field_simp [hxne]
  exact hlim.congr' heq.symm

private theorem halfLineKernel_div_integral_tendsto_zero
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h) :
    Tendsto (fun x : ℝ => ∫ t : ℝ, halfLineKernel x t / x ∂rep.μ)
      atTop (𝓝 (0 : ℝ)) := by
  have hbound_integrable := halfLineWeight_toReal_integrable rep
  have hF_meas :
      ∀ᶠ x in atTop,
        AEStronglyMeasurable (fun t : ℝ => halfLineKernel x t / x) rep.μ := by
    refine Eventually.of_forall ?_
    intro x
    have hmeas : Measurable fun t : ℝ => halfLineKernel x t / x := by
      unfold halfLineKernel
      measurability
    exact hmeas.aestronglyMeasurable
  have h_bound :
      ∀ᶠ x in atTop,
        ∀ᵐ t ∂rep.μ,
          ‖halfLineKernel x t / x‖ ≤ (halfLineWeight t).toReal := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    filter_upwards [rep.ae_mem_Ici] with t ht
    exact halfLineKernel_div_norm_le_weight_toReal hx ht
  have h_lim :
      ∀ᵐ t ∂rep.μ,
        Tendsto (fun x : ℝ => halfLineKernel x t / x) atTop (𝓝 (0 : ℝ)) := by
    exact Eventually.of_forall fun t => halfLineKernel_div_tendsto_zero_atTop t
  have h :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := rep.μ) (l := atTop)
      (F := fun x t : ℝ => halfLineKernel x t / x)
      (f := fun _t : ℝ => (0 : ℝ))
      (fun t : ℝ => (halfLineWeight t).toReal)
      hF_meas h_bound hbound_integrable h_lim
  simpa using h

/--
For a half-line integral representation, the linear coefficient is the slope
at infinity.
-/
theorem halfLineIntegralRep_slope_limit
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h) :
    Tendsto (fun x : ℝ => h x / x) atTop (𝓝 (rep.b : ℝ)) := by
  have h_integral := halfLineKernel_div_integral_tendsto_zero rep
  have h_formula :
      (fun x : ℝ => h x / x) =ᶠ[atTop]
        fun x : ℝ =>
          h 1 / x + (rep.b : ℝ) * ((x - 1) / x) +
            ∫ t : ℝ, halfLineKernel x t / x ∂rep.μ := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hxpos : x ∈ Set.Ioi (0 : ℝ) := by simpa using (lt_trans zero_lt_one hx)
    have hxne : x ≠ 0 := (lt_trans zero_lt_one hx).ne'
    calc
      h x / x =
          (h 1 + (rep.b : ℝ) * (x - 1) +
            ∫ t : ℝ, halfLineKernel x t ∂rep.μ) / x := by
            rw [rep.formula hxpos]
      _ =
          h 1 / x + (rep.b : ℝ) * ((x - 1) / x) +
            (∫ t : ℝ, halfLineKernel x t ∂rep.μ) / x := by
            field_simp [hxne]
      _ =
          h 1 / x + (rep.b : ℝ) * ((x - 1) / x) +
            ∫ t : ℝ, halfLineKernel x t / x ∂rep.μ := by
            rw [MeasureTheory.integral_div]
  have h_const :
      Tendsto (fun x : ℝ => h 1 / x) atTop (𝓝 (0 : ℝ)) :=
    Filter.Tendsto.const_div_atTop tendsto_id (h 1)
  have h_ratio :
      Tendsto (fun x : ℝ => (x - 1) / x) atTop (𝓝 (1 : ℝ)) := by
    have hlim :
        Tendsto (fun x : ℝ => 1 - x⁻¹) atTop (𝓝 (1 - (0 : ℝ))) :=
      tendsto_const_nhds.sub tendsto_inv_atTop_zero
    have heq :
        (fun x : ℝ => (x - 1) / x) =ᶠ[atTop] fun x : ℝ => 1 - x⁻¹ := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hxne : x ≠ 0 := (lt_of_lt_of_le zero_lt_one hx).ne'
      field_simp [hxne]
    simpa using (hlim.congr' heq.symm)
  have h_linear :
      Tendsto (fun x : ℝ => (rep.b : ℝ) * ((x - 1) / x))
        atTop (𝓝 (rep.b : ℝ)) := by
    simpa using (tendsto_const_nhds.mul h_ratio :
      Tendsto (fun x : ℝ => (rep.b : ℝ) * ((x - 1) / x))
        atTop (𝓝 ((rep.b : ℝ) * 1)))
  have h_sum :
      Tendsto
        (fun x : ℝ =>
          h 1 / x + (rep.b : ℝ) * ((x - 1) / x) +
            ∫ t : ℝ, halfLineKernel x t / x ∂rep.μ)
        atTop (𝓝 (rep.b : ℝ)) := by
    simpa using (h_const.add h_linear).add h_integral
  exact h_sum.congr' h_formula.symm

/-- The linear coefficient in a half-line integral representation is unique. -/
theorem halfLineIntegralRep_slope_unique
    {h : ℝ → ℝ} (rep₁ rep₂ : HalfLineIntegralRep h) :
    rep₁.b = rep₂.b := by
  apply Subtype.ext
  exact tendsto_nhds_unique
    (halfLineIntegralRep_slope_limit rep₁)
    (halfLineIntegralRep_slope_limit rep₂)

private theorem halfLineToUnit_withDensity_ae_mem_Ici
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h) :
    ∀ᵐ t ∂rep.μ.withDensity halfLineToUnitDensity, t ∈ Set.Ici (0 : ℝ) := by
  have hac : rep.μ.withDensity halfLineToUnitDensity ≪ rep.μ :=
    MeasureTheory.withDensity_absolutelyContinuous _ _
  exact (mem_ae_iff).mpr (hac rep.support)

private theorem halfLineToUnitDensity_ne_zero_ae
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h) :
    ∀ᵐ t ∂rep.μ, halfLineToUnitDensity t ≠ 0 := by
  filter_upwards [rep.ae_mem_Ici] with t ht
  have ht0 : 0 ≤ t := by simpa using ht
  have hden_pos : 0 < 1 + t := by linarith
  have hpos : 0 < 2 * (1 + t)⁻¹ := by positivity
  rw [halfLineToUnitDensity, ENNReal.ofReal_ne_zero_iff]
  exact hpos

private theorem halfLineToUnitDensity_ne_top_ae
    {h : ℝ → ℝ} (rep : HalfLineIntegralRep h) :
    ∀ᵐ t ∂rep.μ, halfLineToUnitDensity t ≠ ⊤ := by
  exact ae_of_all _ fun t => by
    rw [halfLineToUnitDensity]
    exact (ENNReal.ofReal_lt_top : ENNReal.ofReal (2 * (1 + t)⁻¹) < ⊤).ne

private theorem halfLineToUnit_withDensity_eq_of_unitIntervalMeasure_eq
    {h : ℝ → ℝ} (rep₁ rep₂ : HalfLineIntegralRep h)
    (hν : unitIntervalMeasureOfHalfLine rep₁ = unitIntervalMeasureOfHalfLine rep₂) :
    rep₁.μ.withDensity halfLineToUnitDensity =
      rep₂.μ.withDensity halfLineToUnitDensity := by
  let μd₁ : Measure ℝ := rep₁.μ.withDensity halfLineToUnitDensity
  let μd₂ : Measure ℝ := rep₂.μ.withDensity halfLineToUnitDensity
  let φ : ℝ → ℝ := halfLineToUnitParam
  let ψ : ℝ → ℝ := unitToHalfLineParam
  have hνm :
      (unitIntervalMeasureOfHalfLine rep₁ : Measure ℝ) =
        (unitIntervalMeasureOfHalfLine rep₂ : Measure ℝ) :=
    congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ)) hν
  have htail :
      μd₁.map φ = μd₂.map φ := by
    calc
      μd₁.map φ =
          (unitIntervalMeasureOfHalfLine rep₁ : Measure ℝ).restrict
            (Set.Ioi (-1 : ℝ)) := by
            simpa [μd₁, φ] using (unitIntervalMeasureOfHalfLine_restrict_Ioi rep₁).symm
      _ =
          (unitIntervalMeasureOfHalfLine rep₂ : Measure ℝ).restrict
            (Set.Ioi (-1 : ℝ)) := by rw [hνm]
      _ = μd₂.map φ := by
            simpa [μd₂, φ] using unitIntervalMeasureOfHalfLine_restrict_Ioi rep₂
  ext s hs
  let A : Set ℝ := ψ ⁻¹' s
  have hA : MeasurableSet A := measurable_unitToHalfLineParam hs
  have hpre₁ : μd₁ (φ ⁻¹' A) = μd₁ s := by
    apply measure_congr
    filter_upwards [halfLineToUnit_withDensity_ae_mem_Ici rep₁] with t ht
    apply propext
    change unitToHalfLineParam (halfLineToUnitParam t) ∈ s ↔ t ∈ s
    rw [unitToHalfLineParam_halfLineToUnitParam_of_Ici ht]
  have hpre₂ : μd₂ (φ ⁻¹' A) = μd₂ s := by
    apply measure_congr
    filter_upwards [halfLineToUnit_withDensity_ae_mem_Ici rep₂] with t ht
    apply propext
    change unitToHalfLineParam (halfLineToUnitParam t) ∈ s ↔ t ∈ s
    rw [unitToHalfLineParam_halfLineToUnitParam_of_Ici ht]
  calc
    μd₁ s = μd₁ (φ ⁻¹' A) := hpre₁.symm
    _ = μd₁.map φ A := by rw [Measure.map_apply measurable_halfLineToUnitParam hA]
    _ = μd₂.map φ A := by rw [htail]
    _ = μd₂ (φ ⁻¹' A) := by rw [Measure.map_apply measurable_halfLineToUnitParam hA]
    _ = μd₂ s := hpre₂

private theorem halfLineMeasure_eq_of_withDensity_eq
    {h : ℝ → ℝ} (rep₁ rep₂ : HalfLineIntegralRep h)
    (hwd :
      rep₁.μ.withDensity halfLineToUnitDensity =
        rep₂.μ.withDensity halfLineToUnitDensity) :
    rep₁.μ = rep₂.μ := by
  have hrestore₁ :
      (rep₁.μ.withDensity halfLineToUnitDensity).withDensity
          (fun t : ℝ => (halfLineToUnitDensity t)⁻¹) =
        rep₁.μ :=
    withDensity_inv_same measurable_halfLineToUnitDensity
      (halfLineToUnitDensity_ne_zero_ae rep₁)
      (halfLineToUnitDensity_ne_top_ae rep₁)
  have hrestore₂ :
      (rep₂.μ.withDensity halfLineToUnitDensity).withDensity
          (fun t : ℝ => (halfLineToUnitDensity t)⁻¹) =
        rep₂.μ :=
    withDensity_inv_same measurable_halfLineToUnitDensity
      (halfLineToUnitDensity_ne_zero_ae rep₂)
      (halfLineToUnitDensity_ne_top_ae rep₂)
  calc
    rep₁.μ =
        (rep₁.μ.withDensity halfLineToUnitDensity).withDensity
          (fun t : ℝ => (halfLineToUnitDensity t)⁻¹) := hrestore₁.symm
    _ =
        (rep₂.μ.withDensity halfLineToUnitDensity).withDensity
          (fun t : ℝ => (halfLineToUnitDensity t)⁻¹) := by rw [hwd]
    _ = rep₂.μ := hrestore₂

/-- The measure in a half-line integral representation is unique. -/
theorem halfLineIntegralRep_measure_unique
    {h : ℝ → ℝ} (rep₁ rep₂ : HalfLineIntegralRep h) :
    rep₁.μ = rep₂.μ := by
  have _hb : rep₁.b = rep₂.b := halfLineIntegralRep_slope_unique rep₁ rep₂
  have hν :
      unitIntervalMeasureOfHalfLine rep₁ = unitIntervalMeasureOfHalfLine rep₂ := by
    simpa using
      integralRepOnUnitInterval_measure_unique
        (unitIntervalIntegralRep_of_halfLineIntegralRep_cayley rep₁)
        (unitIntervalIntegralRep_of_halfLineIntegralRep_cayley rep₂)
  exact halfLineMeasure_eq_of_withDensity_eq rep₁ rep₂
    (halfLineToUnit_withDensity_eq_of_unitIntervalMeasure_eq rep₁ rep₂ hν)

/--
Hiai--Matsumoto Theorem 2.26 package: positive-half-line operator
monotonicity is equivalent to the existence of a half-line integral
representation with the slope at infinity and unique coefficients.
-/
theorem operatorMonotoneOnPositive_iff_exists_halfLineIntegralRep_unique
    {h : ℝ → ℝ} :
    OperatorMonotoneOnPositive h ↔
      ∃ rep : HalfLineIntegralRep h,
        Tendsto (fun x : ℝ => h x / x) atTop (𝓝 (rep.b : ℝ)) ∧
        (∀ rep' : HalfLineIntegralRep h, rep'.b = rep.b) ∧
        (∀ rep' : HalfLineIntegralRep h, rep'.μ = rep.μ) := by
  constructor
  · intro hh
    let rep : HalfLineIntegralRep h :=
      halfLineIntegralRep_of_operatorMonotoneOnPositive hh
    refine ⟨rep, halfLineIntegralRep_slope_limit rep, ?_, ?_⟩
    · intro rep'
      exact halfLineIntegralRep_slope_unique rep' rep
    · intro rep'
      exact halfLineIntegralRep_measure_unique rep' rep
  · rintro ⟨rep, _hlim, _hb, _hμ⟩
    exact operatorMonotoneOnPositive_of_halfLineIntegralRep rep

end

end Loewner
end TraceInequality
end Quantum
