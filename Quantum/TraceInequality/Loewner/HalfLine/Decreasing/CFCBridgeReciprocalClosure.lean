import Quantum.TraceInequality.Loewner.LoewnerTheorem
import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.Relevel
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.HalfLine.Decreasing.CFCBridgeNormalized

/-!
# Positive-ray decreasing representations: reciprocal CFC closure

This module is the reciprocal CFC-closure stage of the Simon-style half-line
decreasing-function theory, deriving the reverse bridge and closing the
continuous and finite-matrix normalized pullback routes.
-/

namespace Quantum.TraceInequality.Loewner

universe u

open CFC

open Set MeasureTheory Filter

open scoped ComplexOrder Matrix MatrixOrder NNReal Topology

noncomputable section

private theorem operatorMonotoneOnPositive_pullback_continuousOn_decreasing
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnPositive.{u} h) :
    ContinuousOn (positiveCayleyPullback h) (Set.Ioo (-1 : ℝ) 1) := by
  have hpos : LoewnerPosOnUnitInterval (positiveCayleyPullback h) :=
    loewnerPosOnUnitInterval_of_operatorMonotone
      (operatorMonotoneOnUnitInterval_toZero hh.to_unitInterval)
  exact
    (publicFiniteOrderRegularity_of_loewnerPosOnUnitInterval
      1 hpos).continuousOn

-- LW2-D-PRIVATE-FIXTURE-BEGIN chk_d_priv_04
theorem _root_.LW2.Fixtures.DUni.chk_d_priv_04
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnPositive.{u} h) :
    ContinuousOn (positiveCayleyPullback h) (Set.Ioo (-1 : ℝ) 1) := by
  apply @operatorMonotoneOnPositive_pullback_continuousOn_decreasing
  all_goals assumption
-- LW2-D-PRIVATE-FIXTURE-END chk_d_priv_04

private theorem continuousAt_positiveToUnitCayley_of_pos_decreasing {x : ℝ}
    (hx : x ∈ Set.Ioi (0 : ℝ)) :
    ContinuousAt positiveToUnitCayley x := by
  have hx0 : 0 < x := by simpa using hx
  have hden : x + 1 ≠ 0 := by linarith
  unfold positiveToUnitCayley
  exact (continuousAt_id.sub continuousAt_const).div
    (continuousAt_id.add continuousAt_const) hden

private theorem operatorMonotoneOnPositive_continuousAt_decreasing
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnPositive.{u} h) {x : ℝ}
    (hx : x ∈ Set.Ioi (0 : ℝ)) :
    ContinuousAt h x := by
  have hgCont := operatorMonotoneOnPositive_pullback_continuousOn_decreasing hh
  have hy : positiveToUnitCayley x ∈ Set.Ioo (-1 : ℝ) 1 :=
    positiveToUnitCayley_mem_Ioo hx
  have hgAt :
      ContinuousAt (positiveCayleyPullback h) (positiveToUnitCayley x) :=
    hgCont.continuousAt (isOpen_Ioo.mem_nhds hy)
  have hcomp :
      ContinuousAt
        (fun z : ℝ => positiveCayleyPullback h (positiveToUnitCayley z)) x := by
    simpa [Function.comp_def] using
      hgAt.comp' (continuousAt_positiveToUnitCayley_of_pos_decreasing hx)
  have heq :
      (fun z : ℝ => positiveCayleyPullback h (positiveToUnitCayley z)) =ᶠ[𝓝 x]
        h := by
    have hx0 : 0 < x := by simpa using hx
    filter_upwards [Ioi_mem_nhds hx0] with z hz
    simp [positiveCayleyPullback,
      unitToPositiveCayley_positiveToUnitCayley (by simpa using hz)]
  exact hcomp.congr heq

-- LW2-D-PRIVATE-FIXTURE-BEGIN chk_d_priv_05
theorem _root_.LW2.Fixtures.DUni.chk_d_priv_05
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnPositive.{u} h) {x : ℝ}
    (hx : x ∈ Set.Ioi (0 : ℝ)) :
    ContinuousAt h x := by
  apply @operatorMonotoneOnPositive_continuousAt_decreasing
  all_goals assumption

theorem cfc_reciprocal_formula_eq
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    {g h : ℝ → ℝ} (hh : OperatorMonotoneOnPositive.{u} h)
    (h_formula : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → g x = h x⁻¹)
    {a : A} (ha_nonneg : 0 ≤ a)
    (ha_spec : spectrum ℝ a ⊆ Set.Ioi (0 : ℝ)) :
    LownerHeinzCore.cfcR g a =
      cfc (fun y : ℝ => h y - h 0)
          (LownerHeinzCore.cfcR (fun x : ℝ => 1 / x) a) +
        algebraMap ℝ A (h 0) := by
  have ha_sa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha_nonneg
  have hinv_cont :
      ContinuousOn (fun x : ℝ => 1 / x) (spectrum ℝ a) := by
    intro x hx
    have hxpos : 0 < x := by simpa using ha_spec hx
    simpa [one_div] using
      (continuousAt_inv₀ (ne_of_gt hxpos)).continuousWithinAt
  have hsub_cont :
      ContinuousOn (fun y : ℝ => h y - h 0)
        ((fun x : ℝ => 1 / x) '' spectrum ℝ a) := by
    rintro y ⟨x, hx, rfl⟩
    have hxpos : 0 < x := ha_spec hx
    have hypos : (1 / x) ∈ Set.Ioi (0 : ℝ) := by
      simpa using one_div_pos.mpr hxpos
    exact
      ((operatorMonotoneOnPositive_continuousAt_decreasing hh hypos).sub
        continuousAt_const).continuousWithinAt
  have hcomp :
      cfc (fun y : ℝ => h y - h 0)
          (LownerHeinzCore.cfcR (fun x : ℝ => 1 / x) a) =
        cfc (fun x : ℝ => h (1 / x) - h 0) a := by
    dsimp [LownerHeinzCore.cfcR]
    simpa [Function.comp_def] using
      (cfc_comp' (R := ℝ) (A := A) (p := IsSelfAdjoint)
        (g := fun y : ℝ => h y - h 0) (f := fun x : ℝ => 1 / x)
        (a := a) (hg := hsub_cont) (hf := hinv_cont) (ha := ha_sa)).symm
  have hcomp_cont :
      ContinuousOn (fun x : ℝ => h (1 / x) - h 0) (spectrum ℝ a) := by
    exact hsub_cont.comp hinv_cont (by
      intro x hx
      exact ⟨x, hx, rfl⟩)
  have hadd :
      cfc (fun x : ℝ => h (1 / x) - h 0) a + algebraMap ℝ A (h 0) =
        cfc (fun x : ℝ => h (1 / x)) a := by
    rw [← cfc_add_const (r := h 0)
      (f := fun x : ℝ => h (1 / x) - h 0) (a := a)
      (hf := hcomp_cont)]
    apply cfc_congr
    intro x hx
    ring
  calc
    LownerHeinzCore.cfcR g a =
        cfc (fun x : ℝ => h (1 / x)) a := by
          dsimp [LownerHeinzCore.cfcR]
          apply cfc_congr
          intro x hx
          have hxpos : x ∈ Set.Ioi (0 : ℝ) := ha_spec hx
          simpa [one_div] using h_formula x hxpos
    _ = cfc (fun y : ℝ => h y - h 0)
          (LownerHeinzCore.cfcR (fun x : ℝ => 1 / x) a) +
        algebraMap ℝ A (h 0) := by
          rw [← hadd, hcomp]

-- LW2-D-PRIVATE-FIXTURE-BEGIN chk_d_priv_06
theorem _root_.LW2.Fixtures.DUni.chk_d_priv_06
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    {g h : ℝ → ℝ} (hh : OperatorMonotoneOnPositive.{u} h)
    (h_formula : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → g x = h x⁻¹)
    {a : A} (ha_nonneg : 0 ≤ a)
    (ha_spec : spectrum ℝ a ⊆ Set.Ioi (0 : ℝ)) :
    LownerHeinzCore.cfcR g a =
      cfc (fun y : ℝ => h y - h 0)
          (LownerHeinzCore.cfcR (fun x : ℝ => 1 / x) a) +
        algebraMap ℝ A (h 0) := by
  apply @cfc_reciprocal_formula_eq
  all_goals assumption

/-! ### Continuity and finite-matrix closure of the CFC bridge -/

/--
Continuity on the whole positive ray supplies the local continuity hypothesis
needed by the normalized reciprocal CFC composition identity.
-/
theorem normalizedCFCCompositionContinuity_of_continuousOn_Ioi
    {g : ℝ → ℝ} {A : Type} [NonUnitalCStarAlgebra A] {a : A}
    (hg_cont : ContinuousOn g (Set.Ioi (0 : ℝ)))
    (_ha_sa : IsSelfAdjoint a)
    (ha : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1) :
    ContinuousOn g
      ((fun y : ℝ => (unitToPositiveCayley y)⁻¹) ''
        spectrum ℝ (a : Unitization ℂ A)) := by
  refine hg_cont.mono ?_
  rintro x ⟨y, hy, rfl⟩
  have hyI : y ∈ Set.Ioo (-1 : ℝ) 1 :=
    spectrum_unitization_inr_subset_of_quasispectrum_subset ha hy
  have hpos : 0 < unitToPositiveCayley y :=
    unitToPositiveCayley_mem_Ioi hyI
  exact inv_pos.mpr hpos

/-- The half-line-to-unit Cayley parameter sends positive inputs into `(-1,1)`. -/
theorem halfLineToUnitParam_mem_Ioo_of_Ioi_decreasing {x : ℝ}
    (hx : x ∈ Set.Ioi (0 : ℝ)) :
    halfLineToUnitParam x ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hx0 : 0 < x := by simpa using hx
  have hden : 0 < 1 + x := by linarith
  constructor
  · rw [halfLineToUnitParam, lt_div_iff₀ hden]
    ring_nf
    linarith
  · rw [halfLineToUnitParam, div_lt_iff₀ hden]
    ring_nf
    linarith

/--
After the positive-to-unit Cayley change of variables, the normalized
reciprocal pullback evaluates to `g x⁻¹`.
-/
theorem positiveRayDecreasingNormalizedReciprocalPullback_positiveToUnitCayley
    {g : ℝ → ℝ} {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    positiveRayDecreasingNormalizedReciprocalPullback g (positiveToUnitCayley x) =
      g x⁻¹ := by
  have hy : positiveToUnitCayley x ∈ Set.Ioo (-1 : ℝ) 1 :=
    positiveToUnitCayley_mem_Ioo hx
  have hunit :
      unitToHalfLineParam (positiveToUnitCayley x) = x⁻¹ := by
    rw [← unitToPositiveCayley_inv_eq_unitToHalfLineParam hy,
      unitToPositiveCayley_positiveToUnitCayley hx]
  simp [positiveRayDecreasingNormalizedReciprocalPullback, hunit]

/--
After the half-line-to-unit Cayley change of variables, the normalized
reciprocal pullback recovers `g x`.
-/
theorem positiveRayDecreasingNormalizedReciprocalPullback_halfLineToUnitParam
    {g : ℝ → ℝ} {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    positiveRayDecreasingNormalizedReciprocalPullback g (halfLineToUnitParam x) =
      g x := by
  have hxIci : x ∈ Set.Ici (0 : ℝ) := by
    exact le_of_lt (by simpa using hx)
  simp [positiveRayDecreasingNormalizedReciprocalPullback,
    unitToHalfLineParam_halfLineToUnitParam_of_Ici hxIci]

private theorem continuousAt_halfLineToUnitParam_of_pos_decreasing {x : ℝ}
    (hx : x ∈ Set.Ioi (0 : ℝ)) :
    ContinuousAt halfLineToUnitParam x := by
  have hden : 1 + x ≠ 0 := by
    have hx0 : 0 < x := by simpa using hx
    linarith
  unfold halfLineToUnitParam
  exact (continuousAt_const.sub continuousAt_id).div
    (continuousAt_const.add continuousAt_id) hden

/--
Continuity of the normalized reciprocal pullback on `(-1,1)` transfers back to
continuity of `g` on `(0,∞)`.
-/
theorem continuousOn_Ioi_of_normalizedReciprocalPullback_continuousOn
    {g : ℝ → ℝ}
    (hk : ContinuousOn (positiveRayDecreasingNormalizedReciprocalPullback g)
      (Set.Ioo (-1 : ℝ) 1)) :
    ContinuousOn g (Set.Ioi (0 : ℝ)) := by
  intro x hx
  have hy : halfLineToUnitParam x ∈ Set.Ioo (-1 : ℝ) 1 :=
    halfLineToUnitParam_mem_Ioo_of_Ioi_decreasing hx
  have hkAt :
      ContinuousAt (positiveRayDecreasingNormalizedReciprocalPullback g)
        (halfLineToUnitParam x) :=
    hk.continuousAt (isOpen_Ioo.mem_nhds hy)
  have hcomp :
      ContinuousAt
        (fun z : ℝ =>
          positiveRayDecreasingNormalizedReciprocalPullback g
            (halfLineToUnitParam z)) x := by
    simpa [Function.comp_def] using
      hkAt.comp' (continuousAt_halfLineToUnitParam_of_pos_decreasing hx)
  have heq :
      (fun z : ℝ =>
          positiveRayDecreasingNormalizedReciprocalPullback g
            (halfLineToUnitParam z)) =ᶠ[𝓝 x] g := by
    have hx0 : 0 < x := by simpa using hx
    filter_upwards [Ioi_mem_nhds hx0] with z hz
    exact
      positiveRayDecreasingNormalizedReciprocalPullback_halfLineToUnitParam
        (g := g) (x := z) (by simpa using hz)
  exact (hcomp.congr heq).continuousWithinAt

/--
Finite matrix monotonicity of the normalized reciprocal pullback gives its
continuity on the normalized interval by the Chapter 20 regularity package.
-/
theorem continuousOn_normalizedReciprocalPullback_of_finiteMatrixMonotone
    {g : ℝ → ℝ}
    (hfinite :
      UnitIntervalMatrixMonotone
        (positiveRayDecreasingNormalizedReciprocalPullback g)) :
    ContinuousOn (positiveRayDecreasingNormalizedReciprocalPullback g)
      (Set.Ioo (-1 : ℝ) 1) := by
  have hmono :
      OperatorMonotoneOnUnitInterval
        (positiveRayDecreasingNormalizedReciprocalPullback g) :=
    operatorMonotoneOnUnitInterval_of_finiteMatrixMonotone hfinite
  have hpos :
      LoewnerPosOnUnitInterval
        (positiveRayDecreasingNormalizedReciprocalPullback g) :=
    loewnerPosOnUnitInterval_of_operatorMonotone hmono
  exact
    (publicFiniteOrderRegularity_of_loewnerPosOnUnitInterval
      1 hpos).continuousOn

end

end Quantum.TraceInequality.Loewner
