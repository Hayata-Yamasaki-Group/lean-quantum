import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.Relevel
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.HalfLine.Decreasing.EndpointEquivalence
import Quantum.TraceInequality.Loewner.HalfLine.CayleyCFCInternal
import Quantum.TraceInequality.LownerHeinz.Defs

/-!
# Positive-ray decreasing representations: normalized CFC bridge

This module is the normalized CFC-bridge stage of the Simon-style half-line
decreasing-function theory, reducing endpoint production to normalized
reciprocal pullbacks and finite-dimensional CFC composition contracts.
-/

namespace Quantum.TraceInequality.Loewner

universe u

open CFC

open Set MeasureTheory Filter

open scoped ComplexOrder Matrix MatrixOrder NNReal Topology

noncomputable section

/--
Producer for the CFC composition identity in the normalized reciprocal
pullback.  It identifies the non-unital CFC of
`k_g(y) - k_g(0)`, where `k_g(y) = g((1 - y) / (1 + y))`, with the unital CFC
of `g` after the decreasing Cayley parameter, up to the harmless constant
`g 1`.
-/
structure PositiveRayOperatorMonotoneDecreasingNormalizedCFCCompositionProducer where
  normalized_cfc_eq :
    ∀ {g : ℝ → ℝ} {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A]
      [StarOrderedRing A] {a : A},
      IsSelfAdjoint a →
        quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1 →
          ((cfcₙ
              (fun y : ℝ =>
                positiveRayDecreasingNormalizedReciprocalPullback g y -
                  positiveRayDecreasingNormalizedReciprocalPullback g 0) a : A) :
            Unitization ℂ A) =
            LownerHeinzCore.cfcR g (positiveRayNormalizedCayleyParameter a) -
              algebraMap ℝ (Unitization ℂ A) (g 1)

/-! ### Normalized reciprocal pullback CFC composition -/

/--
The normalized reciprocal CFC composition identity follows from the local
continuity of the fixed outer function `g` on the spectral image where
`cfc_comp'` is applied.

This theorem deliberately exposes the continuity hypothesis: no CFC composition
formula is asserted for arbitrary discontinuous functions.
-/
theorem normalizedCFCComposition_of_continuousOn
    {g : ℝ → ℝ} {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {a : A}
    (ha_sa : IsSelfAdjoint a)
    (ha : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hg_cont :
      ContinuousOn g
        ((fun y : ℝ => (unitToPositiveCayley y)⁻¹) ''
          spectrum ℝ (a : Unitization ℂ A))) :
    ((cfcₙ
        (fun y : ℝ =>
          positiveRayDecreasingNormalizedReciprocalPullback g y -
            positiveRayDecreasingNormalizedReciprocalPullback g 0) a : A) :
      Unitization ℂ A) =
      LownerHeinzCore.cfcR g (positiveRayNormalizedCayleyParameter a) -
        algebraMap ℝ (Unitization ℂ A) (g 1) := by
  let ua : Unitization ℂ A := (a : Unitization ℂ A)
  have ha_inr : IsSelfAdjoint ua := by
    simpa [ua] using (Unitization.isSelfAdjoint_inr (R := ℂ)).mpr ha_sa
  have hs : spectrum ℝ ua ⊆ Set.Ioo (-1 : ℝ) 1 := by
    simpa [ua] using
      spectrum_unitization_inr_subset_of_quasispectrum_subset ha
  let φ : ℝ → ℝ := fun y => (unitToPositiveCayley y)⁻¹
  have hunit_cont : ContinuousOn unitToPositiveCayley (spectrum ℝ ua) :=
    continuousOn_unitToPositiveCayley_of_subset_Ioo hs
  have hφ_cont : ContinuousOn φ (spectrum ℝ ua) := by
    intro y hy
    have hyI : y ∈ Set.Ioo (-1 : ℝ) 1 := hs hy
    have hpos : 0 < unitToPositiveCayley y :=
      unitToPositiveCayley_mem_Ioi hyI
    simpa [φ] using
      (hunit_cont y hy).inv₀ (ne_of_gt hpos)
  have hgφ_cont :
      ContinuousOn (fun y : ℝ => g (φ y)) (spectrum ℝ ua) := by
    exact hg_cont.comp hφ_cont (by
      intro y hy
      exact ⟨y, hy, rfl⟩)
  have hφ_eq_unit :
      cfc φ ua =
        positiveRayNormalizedCayleyParameter a := by
    have hinv_cont :
        ContinuousOn (fun x : ℝ => 1 / x)
          (unitToPositiveCayley '' spectrum ℝ ua) := by
      rintro x ⟨y, hy, rfl⟩
      have hyI : y ∈ Set.Ioo (-1 : ℝ) 1 := hs hy
      have hpos : 0 < unitToPositiveCayley y :=
        unitToPositiveCayley_mem_Ioi hyI
      simpa [one_div] using
        (continuousAt_inv₀ (ne_of_gt hpos)).continuousWithinAt
    change cfc (fun y : ℝ => (unitToPositiveCayley y)⁻¹) ua =
      cfc (fun x : ℝ => 1 / x)
        (cfc unitToPositiveCayley ua)
    simpa [φ, one_div, ua, positiveRayNormalizedCayleyParameter] using
      (cfc_comp' (R := ℝ) (A := Unitization ℂ A) (p := IsSelfAdjoint)
        (g := fun x : ℝ => 1 / x) (f := unitToPositiveCayley)
        (a := ua) (hg := hinv_cont) (hf := hunit_cont) (ha := ha_inr))
  have hkg0 :
      positiveRayDecreasingNormalizedReciprocalPullback g 0 = g 1 := by
    simp [positiveRayDecreasingNormalizedReciprocalPullback,
      unitToHalfLineParam]
  have hsub_zero :
      (fun y : ℝ =>
          positiveRayDecreasingNormalizedReciprocalPullback g y -
            positiveRayDecreasingNormalizedReciprocalPullback g 0) 0 = 0 := by
    simp
  rw [Unitization.real_cfcₙ_eq_cfc_inr a
    (fun y : ℝ =>
      positiveRayDecreasingNormalizedReciprocalPullback g y -
        positiveRayDecreasingNormalizedReciprocalPullback g 0) hsub_zero]
  have hsub_congr :
      cfc
          (fun y : ℝ =>
            positiveRayDecreasingNormalizedReciprocalPullback g y -
              positiveRayDecreasingNormalizedReciprocalPullback g 0) ua =
        cfc (fun y : ℝ => g (φ y) - g 1) ua := by
    apply cfc_congr
    intro y hy
    have hyI : y ∈ Set.Ioo (-1 : ℝ) 1 := hs hy
    rw [hkg0]
    simp [positiveRayDecreasingNormalizedReciprocalPullback, φ,
      unitToPositiveCayley_inv_eq_unitToHalfLineParam hyI]
  change
    cfc
        (fun y : ℝ =>
          positiveRayDecreasingNormalizedReciprocalPullback g y -
            positiveRayDecreasingNormalizedReciprocalPullback g 0) ua =
      LownerHeinzCore.cfcR g (positiveRayNormalizedCayleyParameter a) -
        algebraMap ℝ (Unitization ℂ A) (g 1)
  rw [hsub_congr]
  calc
    cfc (fun y : ℝ => g (φ y) - g 1) ua =
        cfc (fun y : ℝ => g (φ y)) ua -
          algebraMap ℝ (Unitization ℂ A) (g 1) := by
          rw [cfc_sub (a := ua)
            (f := fun y : ℝ => g (φ y))
            (g := fun _ : ℝ => g 1)
            (hf := hgφ_cont) (hg := continuousOn_const)]
          rw [cfc_const (g 1) ua (ha := ha_inr)]
          rfl
    _ =
        LownerHeinzCore.cfcR g (positiveRayNormalizedCayleyParameter a) -
          algebraMap ℝ (Unitization ℂ A) (g 1) := by
          congr 1
          calc
            cfc (fun y : ℝ => g (φ y)) ua =
                cfc g (cfc φ ua) := by
                  rw [cfc_comp' (R := ℝ) (A := Unitization ℂ A)
                    (p := IsSelfAdjoint) (g := g) (f := φ) (a := ua)
                    (hg := hg_cont) (hf := hφ_cont) (ha := ha_inr)]
            _ = LownerHeinzCore.cfcR g
                (positiveRayNormalizedCayleyParameter a) := by
                  rw [hφ_eq_unit]

/--
In finite-dimensional algebras, the normalized reciprocal CFC composition
identity needs no global continuity hypothesis: the relevant real spectrum is
finite, so every scalar function is continuous on the spectral image.
-/
theorem normalizedCFCComposition_of_finiteDimensional
    {g : ℝ → ℝ} {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [FiniteDimensional ℂ A] {a : A}
    (ha_sa : IsSelfAdjoint a)
    (ha : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1) :
    ((cfcₙ
        (fun y : ℝ =>
          positiveRayDecreasingNormalizedReciprocalPullback g y -
            positiveRayDecreasingNormalizedReciprocalPullback g 0) a : A) :
      Unitization ℂ A) =
      LownerHeinzCore.cfcR g (positiveRayNormalizedCayleyParameter a) -
        algebraMap ℝ (Unitization ℂ A) (g 1) := by
  apply normalizedCFCComposition_of_continuousOn ha_sa ha
  have hfinite :
      (spectrum ℝ (a : Unitization ℂ A)).Finite :=
    spectrum_real_finite_of_finiteDimensional_complex
      (B := Unitization ℂ A) (a : Unitization ℂ A)
  exact (hfinite.image (fun y : ℝ => (unitToPositiveCayley y)⁻¹)).continuousOn _

end

end Quantum.TraceInequality.Loewner
