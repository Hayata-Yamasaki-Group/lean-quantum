/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.HalfLine.Decreasing.Basic
import Quantum.TraceInequality.Loewner.HalfLine.CayleyCFCInternal

/-!
# Positive-ray decreasing representations: reciprocal transport

This module is the Cayley and reciprocal-transport stage of the Simon-style
half-line decreasing-function theory, passing through unitization and CFC
transport to positive-ray monotonicity.
-/

namespace Quantum.TraceInequality.Loewner

universe u

open CFC

open Set MeasureTheory Filter

open scoped ComplexOrder Matrix MatrixOrder NNReal Topology

noncomputable section

/-! ### Cayley transport through unitization -/

/-! ### Normalized positive-ray Cayley parameter -/

/--
The normalized positive-ray parameter used in the decreasing bridge: apply the
unit-to-positive Cayley transform and then invert by CFC in the unitization.
-/
noncomputable def positiveRayNormalizedCayleyParameter
    {A : Type*} [NonUnitalCStarAlgebra A] (a : A) : Unitization ℂ A :=
  cfc (fun x : ℝ => 1 / x)
    (cfc unitToPositiveCayley (a : Unitization ℂ A))

theorem spectrum_cfc_unitToPositiveCayley_subset_Ioi_decreasing
    {A : Type*} [NonUnitalCStarAlgebra A]
    {a : A} (ha_sa : IsSelfAdjoint a)
    (ha : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1) :
    spectrum ℝ (cfc unitToPositiveCayley (a : Unitization ℂ A)) ⊆
      Set.Ioi (0 : ℝ) := by
  have ha_inr : IsSelfAdjoint (a : Unitization ℂ A) :=
    (Unitization.isSelfAdjoint_inr (R := ℂ)).mpr ha_sa
  have hs :
      spectrum ℝ (a : Unitization ℂ A) ⊆ Set.Ioo (-1 : ℝ) 1 :=
    spectrum_unitization_inr_subset_of_quasispectrum_subset ha
  have hcont :
      ContinuousOn unitToPositiveCayley (spectrum ℝ (a : Unitization ℂ A)) :=
    continuousOn_unitToPositiveCayley_of_subset_Ioo hs
  have hspec :
      spectrum ℝ (cfc unitToPositiveCayley (a : Unitization ℂ A)) =
        unitToPositiveCayley '' spectrum ℝ (a : Unitization ℂ A) := by
    simpa using
      (cfc_map_spectrum (R := ℝ) (A := Unitization ℂ A)
        (p := IsSelfAdjoint) (f := unitToPositiveCayley)
        (a := (a : Unitization ℂ A)) (ha := ha_inr) (hf := hcont))
  intro y hy
  rw [hspec] at hy
  rcases hy with ⟨x, hx, rfl⟩
  exact unitToPositiveCayley_mem_Ioi (hs hx)

/--
The normalized positive-ray Cayley parameter is positive when the original
quasispectrum lies in `(-1,1)`.
-/
theorem positiveRayNormalizedCayleyParameter_nonneg
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha_sa : IsSelfAdjoint a)
    (ha : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1) :
    0 ≤ positiveRayNormalizedCayleyParameter a := by
  haveI : StarOrderedRing (Unitization ℂ A) := Unitization.instStarOrderedRing
  have hp_spec :
      spectrum ℝ (cfc unitToPositiveCayley (a : Unitization ℂ A)) ⊆
        Set.Ioi (0 : ℝ) :=
    spectrum_cfc_unitToPositiveCayley_subset_Ioi_decreasing ha_sa ha
  exact @cfc_nonneg ℝ (Unitization ℂ A) IsSelfAdjoint
    _ _ _ _ _ _ _ _ _ _ _ Unitization.instPartialOrder
    Unitization.instStarOrderedRing _ _
    (f := fun x : ℝ => 1 / x)
    (a := cfc unitToPositiveCayley (a : Unitization ℂ A)) fun x hx =>
      (one_div_pos.mpr (hp_spec hx)).le

/--
The spectrum of the normalized positive-ray Cayley parameter is contained in
the positive ray.
-/
theorem positiveRayNormalizedCayleyParameter_spectrum_subset_Ioi
    {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a : A} (ha_sa : IsSelfAdjoint a)
    (ha : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1) :
    spectrum ℝ (positiveRayNormalizedCayleyParameter a) ⊆
      Set.Ioi (0 : ℝ) := by
  let p : Unitization ℂ A :=
    cfc unitToPositiveCayley (a : Unitization ℂ A)
  have hp_sa : IsSelfAdjoint p := by
    change IsSelfAdjoint (cfc unitToPositiveCayley (a : Unitization ℂ A))
    exact cfc_predicate unitToPositiveCayley (a : Unitization ℂ A)
  have hp_spec :
      spectrum ℝ p ⊆ Set.Ioi (0 : ℝ) := by
    change spectrum ℝ (cfc unitToPositiveCayley (a : Unitization ℂ A)) ⊆
      Set.Ioi (0 : ℝ)
    exact spectrum_cfc_unitToPositiveCayley_subset_Ioi_decreasing
      (A := A) (a := a) ha_sa ha
  have hcont :
      ContinuousOn (fun x : ℝ => 1 / x) (spectrum ℝ p) := by
    intro x hx
    have hxpos : 0 < x := hp_spec hx
    simpa [one_div] using
      (continuousAt_inv₀ (ne_of_gt hxpos)).continuousWithinAt
  have hspec :
      spectrum ℝ (positiveRayNormalizedCayleyParameter a) =
        (fun x : ℝ => 1 / x) '' spectrum ℝ p := by
    change spectrum ℝ
        (cfc (fun x : ℝ => 1 / x)
          (cfc unitToPositiveCayley (a : Unitization ℂ A))) =
      (fun x : ℝ => 1 / x) ''
        spectrum ℝ (cfc unitToPositiveCayley (a : Unitization ℂ A))
    simpa using
      (cfc_map_spectrum (R := ℝ) (A := Unitization ℂ A)
        (p := IsSelfAdjoint) (f := fun x : ℝ => 1 / x)
        (a := p) (ha := hp_sa) (hf := hcont))
  intro y hy
  rw [hspec] at hy
  rcases hy with ⟨x, hx, rfl⟩
  exact one_div_pos.mpr (by simpa using hp_spec hx)

/-- Move a decreasing resolvent representation across equality on `(0,∞)`. -/
noncomputable def PositiveRayOperatorMonotoneDecreasingRep.congr_on_Ioi
    {g₁ g₂ : ℝ → ℝ} (rep : PositiveRayOperatorMonotoneDecreasingRep g₁)
    (h : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → g₂ x = g₁ x) :
    PositiveRayOperatorMonotoneDecreasingRep g₂ where
  a := rep.a
  μ := rep.μ
  support := rep.support
  formula := by
    intro x hx
    rw [h x hx]
    exact rep.formula hx

end

end Quantum.TraceInequality.Loewner
