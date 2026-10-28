import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.Relevel
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.HalfLine.ClosedPositiveCFCReverse
import Quantum.TraceInequality.Loewner.HalfLine.ConvexRep
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# Positive-ray decreasing representations: basic predicates

This module is the first stage of the Simon-style half-line decreasing-function
theory: core predicates, the resolvent kernel, scalar antitonicity, and
normalized reciprocal pullbacks.
-/

namespace Quantum.TraceInequality.Loewner

universe u

open CFC

open Set MeasureTheory Filter

open scoped ComplexOrder Matrix MatrixOrder NNReal Topology

noncomputable section

/-! ### Core predicates and resolvent kernel -/

/-- Resolvent kernel in Hiai Proposition 2.28 on `(0,∞)`. -/
def positiveRayResolventKernel (x t : ℝ) : ℝ :=
  (1 + t) / (x + t)

/-- The positive-ray resolvent kernel is measurable in its measure variable. -/
theorem measurable_positiveRayResolventKernel_right (x : ℝ) :
    Measurable fun t : ℝ => positiveRayResolventKernel x t := by
  unfold positiveRayResolventKernel
  measurability

/--
Finite-measure representation for positive-ray operator monotone decreasing
functions in the form
`g x = a + ∫ (1 + t) / (x + t) dμ(t)`.

The finite measure is represented as a measure on `ℝ` supported on `[0,∞)`.
-/
structure PositiveRayOperatorMonotoneDecreasingRep (g : ℝ → ℝ) where
  a : NNReal
  μ : FiniteMeasure ℝ
  support : (μ : Measure ℝ) (Set.Ici (0 : ℝ))ᶜ = 0
  formula :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
      g x =
        (a : ℝ) +
          ∫ t : ℝ, positiveRayResolventKernel x t ∂(μ : Measure ℝ)

/--
Positive-ray operator monotone decreasing functions, represented by reciprocal
transport to the positive-ray operator monotone predicate.

This theorem-facing predicate keeps the direct CFC decreasing formulation
(`OperatorMonotoneDecreasingOnPositiveCFC` below) separate: it records
nonnegativity on `(0,∞)` and asks for a
positive-ray operator monotone `h` whose reciprocal pullback agrees with `g` on
`(0,∞)`.
-/
structure OperatorMonotoneDecreasingOnPositive (g : ℝ → ℝ) : Prop where
  nonneg : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → 0 ≤ g x
  reciprocal_witness :
    ∃ h : ℝ → ℝ,
      OperatorMonotoneOnPositive.{u} h ∧
        ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → g x = h x⁻¹

/--
Endpoint-refined reciprocal-transport predicate for positive-ray operator
monotone decreasing functions.

This is still not the direct CFC/book-facing decreasing predicate: it records
the reciprocal witness together with the endpoint data needed to feed the
closed-positive Kubo--Ando representation theorem.
-/
structure OperatorMonotoneDecreasingOnPositiveWithEndpoint (g : ℝ → ℝ) : Prop where
  nonneg : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → 0 ≤ g x
  reciprocal_witness :
    ∃ h : ℝ → ℝ,
      OperatorMonotoneOnPositive.{u} h ∧
        (∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → g x = h x⁻¹) ∧
          0 ≤ h 0 ∧ Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0))

/-! ### Scalar antitonicity and at-top limits -/

private theorem monotoneOn_Ioi_of_operatorMonotoneOnPositive
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnPositive.{u} h) :
    MonotoneOn h (Set.Ioi (0 : ℝ)) := by
  have hfinite :
      UnitIntervalFiniteMatrixMonotone.{0} (positiveCayleyPullback h) :=
    finiteMatrixMonotone_of_operatorMonotoneOnUnitInterval
      (operatorMonotoneOnUnitInterval_toZero hh.to_unitInterval)
  have hpullMono :
      MonotoneOn (positiveCayleyPullback h) (Set.Ioo (-1 : ℝ) 1) :=
    scalarMonotoneOn_Ioo_of_finiteMatrixMonotone
      (unitIntervalMatrixMonotone_of_finiteMatrixMonotone hfinite)
  intro x hx y hy hxy
  have hxI : positiveToUnitCayley x ∈ Set.Ioo (-1 : ℝ) 1 :=
    positiveToUnitCayley_mem_Ioo hx
  have hyI : positiveToUnitCayley y ∈ Set.Ioo (-1 : ℝ) 1 :=
    positiveToUnitCayley_mem_Ioo hy
  have hx0 : 0 < x := by simpa using hx
  have hy0 : 0 < y := by simpa using hy
  have hxden : 0 < x + 1 := by linarith
  have hyden : 0 < y + 1 := by linarith
  have hcayley : positiveToUnitCayley x ≤ positiveToUnitCayley y := by
    unfold positiveToUnitCayley
    rw [div_le_div_iff₀ hxden hyden]
    nlinarith
  have hpull_le := hpullMono hxI hyI hcayley
  simpa [positiveCayleyPullback,
    unitToPositiveCayley_positiveToUnitCayley hx,
    unitToPositiveCayley_positiveToUnitCayley hy] using hpull_le

private theorem antitoneOn_Ioi_of_operatorMonotoneDecreasingOnPositive
    {g : ℝ → ℝ} (hg : OperatorMonotoneDecreasingOnPositive.{u} g) :
    AntitoneOn g (Set.Ioi (0 : ℝ)) := by
  rcases hg.reciprocal_witness with ⟨h, hh, h_formula⟩
  have hmono : MonotoneOn h (Set.Ioi (0 : ℝ)) :=
    monotoneOn_Ioi_of_operatorMonotoneOnPositive hh
  intro x hx y hy hxy
  have hx0 : 0 < x := by simpa using hx
  have hy0 : 0 < y := by simpa using hy
  rw [h_formula x hx, h_formula y hy]
  exact hmono (inv_pos.mpr hy0) (inv_pos.mpr hx0)
    ((inv_le_inv₀ hy0 hx0).2 hxy)

private def positiveRayAtTopClamp (g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => g (max x 1)

private theorem positiveRayAtTopClamp_antitone_of_antitoneOn_Ioi
    {g : ℝ → ℝ} (hg : AntitoneOn g (Set.Ioi (0 : ℝ))) :
    Antitone (positiveRayAtTopClamp g) := by
  intro x y hxy
  unfold positiveRayAtTopClamp
  have hxmem : max x 1 ∈ Set.Ioi (0 : ℝ) := by
    simp [lt_of_lt_of_le zero_lt_one (le_max_right x 1)]
  have hymem : max y 1 ∈ Set.Ioi (0 : ℝ) := by
    simp [lt_of_lt_of_le zero_lt_one (le_max_right y 1)]
  exact hg hxmem hymem (max_le_max hxy le_rfl)

private theorem positiveRayAtTopClamp_bddBelow_of_nonneg
    {g : ℝ → ℝ} (hg : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → 0 ≤ g x) :
    BddBelow (range (positiveRayAtTopClamp g)) := by
  refine ⟨0, ?_⟩
  rintro y ⟨x, rfl⟩
  unfold positiveRayAtTopClamp
  exact hg (max x 1) (by
    simp [lt_of_lt_of_le zero_lt_one (le_max_right x 1)])

private theorem positiveRayAtTopClamp_ciInf_nonneg_of_nonneg
    {g : ℝ → ℝ} (hg : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → 0 ≤ g x) :
    0 ≤ ⨅ x : ℝ, positiveRayAtTopClamp g x := by
  refine le_ciInf ?_
  intro x
  unfold positiveRayAtTopClamp
  exact hg (max x 1) (by
    simp [lt_of_lt_of_le zero_lt_one (le_max_right x 1)])

theorem tendsto_atTop_of_antitoneOn_Ioi_nonneg
    {g : ℝ → ℝ} (hanti : AntitoneOn g (Set.Ioi (0 : ℝ)))
    (hnonneg : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → 0 ≤ g x) :
    ∃ c : ℝ, 0 ≤ c ∧ Tendsto g atTop (𝓝 c) := by
  let c : ℝ := ⨅ x : ℝ, positiveRayAtTopClamp g x
  have hclamp_anti : Antitone (positiveRayAtTopClamp g) :=
    positiveRayAtTopClamp_antitone_of_antitoneOn_Ioi hanti
  have hclamp_bdd : BddBelow (range (positiveRayAtTopClamp g)) :=
    positiveRayAtTopClamp_bddBelow_of_nonneg hnonneg
  have hclamp_tendsto : Tendsto (positiveRayAtTopClamp g) atTop (𝓝 c) := by
    simpa [c] using tendsto_atTop_ciInf hclamp_anti hclamp_bdd
  have heq : (fun x : ℝ => positiveRayAtTopClamp g x) =ᶠ[atTop] g := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    simp [positiveRayAtTopClamp, max_eq_left hx]
  refine ⟨c, ?_, ?_⟩
  · simpa [c] using positiveRayAtTopClamp_ciInf_nonneg_of_nonneg hnonneg
  · exact hclamp_tendsto.congr' heq

/--
The reciprocal-transport decreasing predicate has a finite nonnegative limit
at infinity.  This is the endpoint value at zero of its reciprocal witness.
-/
theorem positiveRayOperatorMonotoneDecreasingAtTopLimit
    {g : ℝ → ℝ} (hg : OperatorMonotoneDecreasingOnPositive.{u} g) :
    ∃ c : ℝ, 0 ≤ c ∧ Tendsto g atTop (𝓝 c) :=
  tendsto_atTop_of_antitoneOn_Ioi_nonneg
    (antitoneOn_Ioi_of_operatorMonotoneDecreasingOnPositive hg)
    hg.nonneg

/-! ### Reciprocal witnesses and normalized pullbacks -/

/-- Canonical reciprocal witness associated with a decreasing positive-ray function. -/
def positiveRayDecreasingReciprocalWitness (g : ℝ → ℝ) : ℝ → ℝ :=
  fun y => g y⁻¹

/-- The reciprocal witness recovers the original decreasing function on `(0,∞)`. -/
theorem positiveRayDecreasingReciprocalWitness_formula {g : ℝ → ℝ}
    {x : ℝ} (_hx : x ∈ Set.Ioi (0 : ℝ)) :
    g x = positiveRayDecreasingReciprocalWitness g x⁻¹ := by
  simp [positiveRayDecreasingReciprocalWitness]

/--
Reciprocal witness with an explicit endpoint value.  On the positive ray this
still agrees with `y ↦ g y⁻¹`, while the value at `0` is recorded separately.
-/
def positiveRayDecreasingReciprocalWitnessWithEndpoint
    (g : ℝ → ℝ) (c : ℝ) : ℝ → ℝ :=
  fun y => if y = 0 then c else g y⁻¹

/--
The endpoint-refined reciprocal witness still recovers the original function on
`(0,∞)`.
-/
theorem positiveRayDecreasingReciprocalWitnessWithEndpoint_formula
    {g : ℝ → ℝ} {c x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    g x = positiveRayDecreasingReciprocalWitnessWithEndpoint g c x⁻¹ := by
  have hxpos : 0 < x := by simpa using hx
  have hxinv_ne : x⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hxpos)
  simp [positiveRayDecreasingReciprocalWitnessWithEndpoint, hxinv_ne]

/-- The endpoint-refined reciprocal witness takes the supplied endpoint value at zero. -/
@[simp]
theorem positiveRayDecreasingReciprocalWitnessWithEndpoint_zero
    {g : ℝ → ℝ} {c : ℝ} :
    positiveRayDecreasingReciprocalWitnessWithEndpoint g c 0 = c := by
  simp [positiveRayDecreasingReciprocalWitnessWithEndpoint]

/--
If `g` has finite limit `c` at infinity, the endpoint-refined reciprocal
witness tends to `c` from the positive side at zero.
-/
theorem positiveRayDecreasingReciprocalWitnessWithEndpoint_tendsto_nhdsGT_of_tendsto_atTop
    {g : ℝ → ℝ} {c : ℝ} (hg : Tendsto g atTop (𝓝 c)) :
    Tendsto (positiveRayDecreasingReciprocalWitnessWithEndpoint g c)
      (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  refine (hg.comp (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy_ne : y ≠ 0 := ne_of_gt (by simpa using hy)
  simp [positiveRayDecreasingReciprocalWitnessWithEndpoint, hy_ne]

/--
Normalized reciprocal pullback of a direct decreasing function.

On the normalized interval this is the scalar function obtained from
`positiveCayleyPullback (positiveRayDecreasingReciprocalWitnessWithEndpoint g c)`;
the endpoint value `c` drops out because `unitToPositiveCayley y > 0`.
-/
def positiveRayDecreasingNormalizedReciprocalPullback
    (g : ℝ → ℝ) : ℝ → ℝ :=
  fun y => g (unitToHalfLineParam y)

/-- On `(-1,1)`, the inverse positive Cayley parameter is `unitToHalfLineParam`. -/
theorem unitToPositiveCayley_inv_eq_unitToHalfLineParam {y : ℝ}
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    (unitToPositiveCayley y)⁻¹ = unitToHalfLineParam y := by
  have hnum : 1 + y ≠ 0 := by linarith [hy.1]
  have hden : 1 - y ≠ 0 := by linarith [hy.2]
  unfold unitToPositiveCayley unitToHalfLineParam
  field_simp [hnum, hden]

/--
The Cayley pullback of the endpoint reciprocal witness equals the normalized
reciprocal pullback on the open normalized interval.
-/
theorem positiveCayleyPullback_endpointReciprocal_eq_normalizedReciprocalPullback_on_Ioo
    {g : ℝ → ℝ} {c y : ℝ} (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    positiveCayleyPullback
        (positiveRayDecreasingReciprocalWitnessWithEndpoint g c) y =
      positiveRayDecreasingNormalizedReciprocalPullback g y := by
  have hunit_ne : unitToPositiveCayley y ≠ 0 := by
    exact ne_of_gt (by simpa using unitToPositiveCayley_mem_Ioi hy)
  simp [positiveCayleyPullback,
    positiveRayDecreasingReciprocalWitnessWithEndpoint,
    positiveRayDecreasingNormalizedReciprocalPullback,
    hunit_ne, unitToPositiveCayley_inv_eq_unitToHalfLineParam hy]

/--
Unit-interval operator monotonicity is invariant under pointwise equality on
`(-1,1)`, the only region seen by the non-unital CFC.
-/
theorem OperatorMonotoneOnUnitInterval.congr_on_Ioo
    {f₁ f₂ : ℝ → ℝ} (hf : OperatorMonotoneOnUnitInterval.{0} f₁)
    (heq : ∀ y : ℝ, y ∈ Set.Ioo (-1 : ℝ) 1 → f₂ y = f₁ y) :
    OperatorMonotoneOnUnitInterval.{0} f₂ where
  cfc_monotone := by
    intro A _ _ _ a ha b hb hab
    have hzero : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
    have hca :
        cfcₙ (fun x : ℝ => f₂ x - f₂ 0) a =
          cfcₙ (fun x : ℝ => f₁ x - f₁ 0) a := by
      apply cfcₙ_congr
      intro x hx
      have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := ha.2 hx
      change f₂ x - f₂ 0 = f₁ x - f₁ 0
      rw [heq x hxI, heq 0 hzero]
    have hcb :
        cfcₙ (fun x : ℝ => f₂ x - f₂ 0) b =
          cfcₙ (fun x : ℝ => f₁ x - f₁ 0) b := by
      apply cfcₙ_congr
      intro x hx
      have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := hb.2 hx
      change f₂ x - f₂ 0 = f₁ x - f₁ 0
      rw [heq x hxI, heq 0 hzero]
    change cfcₙ (fun x : ℝ => f₂ x - f₂ 0) a ≤
      cfcₙ (fun x : ℝ => f₂ x - f₂ 0) b
    rw [hca, hcb]
    exact hf.cfc_monotone ha hb hab

end

end Quantum.TraceInequality.Loewner
