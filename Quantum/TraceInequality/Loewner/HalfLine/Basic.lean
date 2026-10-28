import Quantum.Analysis.Real.PositiveCayley
import Quantum.TraceInequality.Loewner.Statement

/-!
# Half-line positive-ray basics

This module contains the positive-ray Cayley maps, half-line integral
representation predicates, and endpoint/direct CFC predicate packages.  The
closed-positive CFC bridge itself lives in `HalfLine.ClosedPositiveCFC`.
-/

namespace Quantum.TraceInequality.Loewner

universe u

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

/-- Cayley map `(0,∞) → (-1,1)`. -/
def positiveToUnitCayley (x : ℝ) : ℝ :=
  (x - 1) / (x + 1)

/-- Parameter map `u ∈ (-1,1] ↦ t ∈ [0,∞)`. -/
def unitToHalfLineParam (u : ℝ) : ℝ :=
  (1 - u) / (1 + u)

/-- Inverse parameter map `t ∈ [0,∞) ↦ u ∈ [-1,1]`. -/
def halfLineToUnitParam (t : ℝ) : ℝ :=
  (1 - t) / (1 + t)

/-- The half-line kernel in Hiai--Matsumoto Theorem 2.26. -/
def halfLineKernel (x t : ℝ) : ℝ :=
  (x - 1) / (x + t)

/-- The weighted-mass integrand in Hiai--Matsumoto Theorem 2.26. -/
def halfLineWeight (t : ℝ) : ENNReal :=
  ENNReal.ofReal ((1 + t)⁻¹)

/-- Density used before pushing the non-atom part of a normalized measure to `[0,∞)`. -/
def unitToHalfLineDensity (u : ℝ) : ENNReal :=
  ENNReal.ofReal ((1 + u)⁻¹)

/-- Density used before pushing a half-line measure back to the normalized interval. -/
def halfLineToUnitDensity (t : ℝ) : ENNReal :=
  ENNReal.ofReal (2 * (1 + t)⁻¹)

/-- Linear coefficient contributed by the `u = -1` atom of the normalized measure. -/
def halfLineSlopeOfUnitInterval (ν : FiniteMeasure ℝ) : NNReal :=
  ⟨(((ν : Measure ℝ) ({-1} : Set ℝ)).toReal / 2), by positivity⟩

/--
Push the non-atom part `u ∈ (-1, 1]` of a normalized interval measure to the
half-line parameter `t = (1-u)/(1+u)`, including the kernel-conversion density
`(1+u)⁻¹`.
-/
def halfLineMeasureOfUnitInterval (ν : FiniteMeasure ℝ) : Measure ℝ :=
  (((ν : Measure ℝ).restrict (Set.Ioi (-1 : ℝ))).withDensity unitToHalfLineDensity).map
    unitToHalfLineParam

/-- The map from normalized interval parameter to half-line parameter is measurable. -/
theorem measurable_unitToHalfLineParam :
    Measurable unitToHalfLineParam := by
  unfold unitToHalfLineParam
  exact (measurable_const.sub measurable_id).div (measurable_const.add measurable_id)

/-- The map from half-line parameter back to normalized interval parameter is measurable. -/
theorem measurable_halfLineToUnitParam :
    Measurable halfLineToUnitParam := by
  unfold halfLineToUnitParam
  exact (measurable_const.sub measurable_id).div (measurable_const.add measurable_id)

/-- The density used in the unit-interval-to-half-line pushforward is measurable. -/
theorem measurable_unitToHalfLineDensity :
    Measurable unitToHalfLineDensity := by
  have hmeas : Measurable fun u : ℝ => (1 + u)⁻¹ :=
    (measurable_const.add measurable_id).inv
  simpa [unitToHalfLineDensity] using ENNReal.measurable_ofReal.comp hmeas

/-- The density used in the half-line-to-unit-interval pushforward is measurable. -/
theorem measurable_halfLineToUnitDensity :
    Measurable halfLineToUnitDensity := by
  have hmeas : Measurable fun t : ℝ => 2 * (1 + t)⁻¹ :=
    measurable_const.mul (measurable_const.add measurable_id).inv
  simpa [halfLineToUnitDensity] using ENNReal.measurable_ofReal.comp hmeas

/-- The half-line weighted-mass integrand is measurable. -/
theorem measurable_halfLineWeight :
    Measurable halfLineWeight := by
  have hmeas : Measurable fun t : ℝ => (1 + t)⁻¹ :=
    (measurable_const.add measurable_id).inv
  simpa [halfLineWeight] using ENNReal.measurable_ofReal.comp hmeas

/--
Hiai--Matsumoto Chapter 2.4, Theorem 2.26 type half-line integral
representation.

The measure is a measure on `ℝ` supported on `[0,∞)`. It is not required to be
finite; instead the weighted mass `∫⁻ t, (1+t)⁻¹ ∂μ` is finite.
-/
structure HalfLineIntegralRep (h : ℝ → ℝ) where
  b : NNReal
  μ : Measure ℝ
  support : μ (Set.Ici (0 : ℝ))ᶜ = 0
  weight_lintegral_lt_top :
    (∫⁻ t : ℝ, halfLineWeight t ∂μ) < ⊤
  formula :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
      h x =
        h 1 + (b : ℝ) * (x - 1) +
          ∫ t : ℝ, halfLineKernel x t ∂μ

/--
Positive-half-line operator monotonicity, represented by Cayley pullback to the
already established normalized interval predicate.
-/
structure OperatorMonotoneOnPositive (h : ℝ → ℝ) : Prop where
  to_unitInterval :
    OperatorMonotoneOnUnitInterval.{u} (positiveCayleyPullback h)

/--
Closed-positive-half-line monotonicity package used for Hiai--Matsumoto
Theorem 2.27: open positive monotonicity plus right-continuity at `0`.
-/
structure OperatorMonotoneOnClosedPositive (h : ℝ → ℝ) : Prop where
  to_open : OperatorMonotoneOnPositive.{u} h
  right_continuous_at_zero :
    Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0))

/--
Direct CFC predicate for operator monotonicity on the closed positive half-line.

The function is normalized by subtracting `h 0`, matching non-unital CFC.
-/
structure OperatorMonotoneOnClosedPositiveCFC (h : ℝ → ℝ) : Prop where
  cfc_monotone :
    ∀ {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A],
      MonotoneOn (fun a : A => cfcₙ (fun x : ℝ => h x - h 0) a)
        {a : A | 0 ≤ a}

/--
Direct CFC monotonicity together with the endpoint condition from Hiai
Theorem 2.27.

The bare direct CFC predicate does not record right-continuity at `0`; this
package is the book-faithful closed-positive statement.
-/
structure OperatorMonotoneOnClosedPositiveCFCWithEndpoint (h : ℝ → ℝ) : Prop where
  to_cfc : OperatorMonotoneOnClosedPositiveCFC.{u} h
  right_continuous_at_zero :
    Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0))

/--
gcongr form of positive-ray monotonicity through the normalized Cayley pullback.
It is the `cfc_monotone` field of `OperatorMonotoneOnPositive`.
-/
@[gcongr]
theorem cfcn_posCayley_sub_le_cfcn_posCayley_sub_of_le_of_operatorMonotoneOnPositive
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnPositive.{u} h)
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (hab : a ≤ b)
    (ha : IsSelfAdjoint a) (hqa : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hb : IsSelfAdjoint b) (hqb : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1) :
    cfcₙ (fun x : ℝ => positiveCayleyPullback h x - positiveCayleyPullback h 0) a ≤
      cfcₙ (fun x : ℝ => positiveCayleyPullback h x - positiveCayleyPullback h 0) b :=
  hh.to_unitInterval.cfc_monotone ⟨ha, hqa⟩ ⟨hb, hqb⟩ hab

/--
gcongr form of closed-positive monotonicity through the open positive-ray field.
It delegates to `OperatorMonotoneOnClosedPositive.to_open.cfc_monotone`.
-/
@[gcongr]
theorem cfcn_posCayley_sub_le_cfcn_posCayley_sub_of_le_of_operatorMonotoneOnClosedPositive
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnClosedPositive.{u} h)
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (hab : a ≤ b)
    (ha : IsSelfAdjoint a) (hqa : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hb : IsSelfAdjoint b) (hqb : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1) :
    cfcₙ (fun x : ℝ => positiveCayleyPullback h x - positiveCayleyPullback h 0) a ≤
      cfcₙ (fun x : ℝ => positiveCayleyPullback h x - positiveCayleyPullback h 0) b :=
  hh.to_open.to_unitInterval.cfc_monotone ⟨ha, hqa⟩ ⟨hb, hqb⟩ hab

/--
gcongr form of direct closed-positive CFC monotonicity.
It is the `cfc_monotone` field of `OperatorMonotoneOnClosedPositiveCFC`.
-/
@[gcongr]
theorem cfcn_sub_le_cfcn_sub_of_le_of_operatorMonotoneOnClosedPositiveCFC
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnClosedPositiveCFC.{u} h)
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    cfcₙ (fun x : ℝ => h x - h 0) a ≤ cfcₙ (fun x : ℝ => h x - h 0) b :=
  hh.cfc_monotone ha hb hab

/--
gcongr form of the endpoint-refined direct closed-positive CFC predicate.
It delegates to the bundled `to_cfc` field.
-/
@[gcongr]
theorem cfcn_sub_le_cfcn_sub_of_le_of_operatorMonotoneOnClosedPositiveCFCWithEndpoint
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnClosedPositiveCFCWithEndpoint.{u} h)
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    cfcₙ (fun x : ℝ => h x - h 0) a ≤ cfcₙ (fun x : ℝ => h x - h 0) b :=
  hh.to_cfc.cfc_monotone ha hb hab

/-- The representing measure of a half-line integral representation is a.e. in `[0,∞)`. -/
theorem HalfLineIntegralRep.ae_mem_Ici {h : ℝ → ℝ}
    (rep : HalfLineIntegralRep h) :
    ∀ᵐ t ∂rep.μ, t ∈ Set.Ici (0 : ℝ) := by
  exact (mem_ae_iff).mpr rep.support

/-- Restricting a half-line representing measure to `[0,∞)` does not change it. -/
theorem HalfLineIntegralRep.restrict_Ici_eq_self {h : ℝ → ℝ}
    (rep : HalfLineIntegralRep h) :
    rep.μ.restrict (Set.Ici (0 : ℝ)) = rep.μ :=
  Measure.restrict_eq_self_of_ae_mem rep.ae_mem_Ici

/-- The positive-to-unit Cayley map sends `(0,∞)` into `(-1,1)`. -/
theorem positiveToUnitCayley_mem_Ioo {x : ℝ}
    (hx : x ∈ Set.Ioi (0 : ℝ)) :
    positiveToUnitCayley x ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hx0 : 0 < x := by simpa using hx
  have hden : 0 < x + 1 := by linarith
  constructor
  · rw [positiveToUnitCayley, lt_div_iff₀ hden]
    ring_nf
    linarith
  · rw [positiveToUnitCayley, div_lt_iff₀ hden]
    ring_nf
    linarith

/-- The unit-to-positive Cayley map is a left inverse on `(0,∞)`. -/
theorem unitToPositiveCayley_positiveToUnitCayley {x : ℝ}
    (hx : x ∈ Set.Ioi (0 : ℝ)) :
    unitToPositiveCayley (positiveToUnitCayley x) = x := by
  have hx0 : 0 < x := by simpa using hx
  have hxden : x + 1 ≠ 0 := by linarith
  have hunitden : 1 - positiveToUnitCayley x ≠ 0 := by
    have hy : positiveToUnitCayley x < 1 := (positiveToUnitCayley_mem_Ioo hx).2
    linarith
  unfold unitToPositiveCayley positiveToUnitCayley
  field_simp [hxden, hunitden]
  ring_nf

/-- The positive-to-unit Cayley map is a left inverse on `(-1,1)`. -/
theorem positiveToUnitCayley_unitToPositiveCayley {y : ℝ}
  (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    positiveToUnitCayley (unitToPositiveCayley y) = y := by
  have hyden : 1 - y ≠ 0 := by linarith [hy.2]
  have hxden : unitToPositiveCayley y + 1 ≠ 0 := by
    have hxpos : 0 < unitToPositiveCayley y :=
      unitToPositiveCayley_mem_Ioi hy
    linarith
  unfold positiveToUnitCayley unitToPositiveCayley
  field_simp [hyden, hxden]
  ring_nf

/-- The inverse Cayley map sends the midpoint `0` to `1`. -/
@[simp]
theorem unitToPositiveCayley_zero :
    unitToPositiveCayley 0 = 1 := by
  norm_num [unitToPositiveCayley]


end

end Loewner
end TraceInequality
end Quantum
