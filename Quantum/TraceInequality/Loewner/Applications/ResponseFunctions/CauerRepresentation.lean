import Quantum.TraceInequality.Loewner.Applications.ResponseFunctions.CauerBasic

/-!
# Cauer representations of positive-real response functions

The upper-half-plane Nevanlinna representation is reflected across the
imaginary axis.  Uniqueness then removes its real constant and forces symmetry
of its finite measure, after which the even Cauer kernel is obtained by
averaging.
-/

namespace Quantum.TraceInequality.Loewner.ResponseFunctions

open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff

noncomputable section

/-- Conjugating a reflected Nevanlinna kernel gives the sign-reversed kernel. -/
theorem neg_conj_nevanlinnaKernel_reflection (t : ℝ) (z : ℍ) :
    -(starRingEnd ℂ)
        (Loewner.nevanlinnaKernel t (upperHalfPlaneReflection z)) =
      Loewner.nevanlinnaKernel (-t) z := by
  unfold Loewner.nevanlinnaKernel
  rw [coe_upperHalfPlaneReflection]
  push_cast
  simp only [map_div₀, map_add, map_one, map_mul, map_neg, map_sub,
    Complex.conj_ofReal, starRingEnd_self_apply]
  have hplus := cauer_add_den_ne_zero t z
  have hnegplus : (-(t : ℂ) - (z : ℂ)) ≠ 0 := by
    rw [show -(t : ℂ) - (z : ℂ) = -((t : ℂ) + (z : ℂ)) by ring]
    exact neg_ne_zero.mpr hplus
  field_simp [hplus, hnegplus]
  ring

/-- Integrating against the reflected measure composes the kernel with negation. -/
theorem integral_nevanlinnaKernel_reflectedFiniteMeasure
    (ν : FiniteMeasure ℝ) (z : ℍ) :
    (∫ t : ℝ, Loewner.nevanlinnaKernel t z
        ∂(reflectedFiniteMeasure ν : Measure ℝ)) =
      ∫ t : ℝ, Loewner.nevanlinnaKernel (-t) z ∂(ν : Measure ℝ) := by
  have hInt := Loewner.nevanlinnaKernel_integrable
    (reflectedFiniteMeasure ν) z
  have hmap := MeasureTheory.integral_map
    (f := fun t : ℝ => Loewner.nevanlinnaKernel t z)
    (measurable_neg.aemeasurable) hInt.aestronglyMeasurable
  simpa only [reflectedFiniteMeasure_toMeasure, Function.comp_apply] using hmap

/-- The reflected integral is the negative conjugate of the original integral. -/
theorem neg_conj_integral_nevanlinnaKernel_reflection
    (ν : FiniteMeasure ℝ) (z : ℍ) :
    -(starRingEnd ℂ)
        (∫ t : ℝ, Loewner.nevanlinnaKernel t (upperHalfPlaneReflection z)
          ∂(ν : Measure ℝ)) =
      ∫ t : ℝ, Loewner.nevanlinnaKernel t z
        ∂(reflectedFiniteMeasure ν : Measure ℝ) := by
  calc
    -(starRingEnd ℂ)
        (∫ t : ℝ, Loewner.nevanlinnaKernel t (upperHalfPlaneReflection z)
          ∂(ν : Measure ℝ)) =
        -(∫ t : ℝ, (starRingEnd ℂ)
          (Loewner.nevanlinnaKernel t (upperHalfPlaneReflection z))
            ∂(ν : Measure ℝ)) := by
          congr 1
          exact (integral_conj
            (f := fun t : ℝ =>
              Loewner.nevanlinnaKernel t (upperHalfPlaneReflection z))).symm
    _ = ∫ t : ℝ, -(starRingEnd ℂ)
          (Loewner.nevanlinnaKernel t (upperHalfPlaneReflection z))
            ∂(ν : Measure ℝ) := by rw [integral_neg]
    _ = ∫ t : ℝ, Loewner.nevanlinnaKernel (-t) z
          ∂(ν : Measure ℝ) := by
          refine integral_congr_ae ?_
          exact ae_of_all _ fun t => neg_conj_nevanlinnaKernel_reflection t z
    _ = ∫ t : ℝ, Loewner.nevanlinnaKernel t z
          ∂(reflectedFiniteMeasure ν : Measure ℝ) :=
        (integral_nevanlinnaKernel_reflectedFiniteMeasure ν z).symm

/-- Reflect a positive-real Nevanlinna representation.

The represented function is unchanged; the real constant changes sign, the
linear coefficient is unchanged, and the finite measure is pushed forward by
`t ↦ -t`.
-/
def reflectedNevanlinnaRep
    {F : ℍ → ℂ} (rep : Loewner.NevanlinnaRep F) (hPR : IsPositiveReal F) :
    Loewner.NevanlinnaRep F where
  alpha := -rep.alpha
  beta := rep.beta
  ν := reflectedFiniteMeasure rep.ν
  formula := by
    intro z
    have hsym := hPR (upperHalfPlaneReflection z)
    rw [upperHalfPlaneReflection_involutive] at hsym
    rw [rep.formula (upperHalfPlaneReflection z)] at hsym
    calc
      F z = -(starRingEnd ℂ)
          ((rep.alpha : ℂ) + (rep.beta : ℝ) *
              (upperHalfPlaneReflection z : ℂ) +
            ∫ t : ℝ, Loewner.nevanlinnaKernel t
              (upperHalfPlaneReflection z) ∂(rep.ν : Measure ℝ)) := hsym
      _ = ((-rep.alpha : ℝ) : ℂ) + (rep.beta : ℝ) * (z : ℂ) +
          -(starRingEnd ℂ)
            (∫ t : ℝ, Loewner.nevanlinnaKernel t
              (upperHalfPlaneReflection z) ∂(rep.ν : Measure ℝ)) := by
            rw [coe_upperHalfPlaneReflection]
            push_cast
            simp only [map_add, map_mul, map_neg, Complex.conj_ofReal,
              starRingEnd_self_apply]
            ring
      _ = ((-rep.alpha : ℝ) : ℂ) + (rep.beta : ℝ) * (z : ℂ) +
          ∫ t : ℝ, Loewner.nevanlinnaKernel t z
            ∂(reflectedFiniteMeasure rep.ν : Measure ℝ) := by
            rw [neg_conj_integral_nevanlinnaKernel_reflection]

/-- Uniqueness identifies a representation with its positive-real reflection. -/
theorem nevanlinnaRep_eq_reflected_of_isPositiveReal
    {F : ℍ → ℂ} (rep : Loewner.NevanlinnaRep F) (hPR : IsPositiveReal F) :
    rep = reflectedNevanlinnaRep rep hPR :=
  Loewner.nevanlinnaRep_unique rep (reflectedNevanlinnaRep rep hPR)

/-- Positive-real symmetry forces the real Nevanlinna constant to vanish. -/
theorem nevanlinnaRep_alpha_eq_zero_of_isPositiveReal
    {F : ℍ → ℂ} (rep : Loewner.NevanlinnaRep F) (hPR : IsPositiveReal F) :
    rep.alpha = 0 := by
  have h := congrArg Loewner.NevanlinnaRep.alpha
    (nevanlinnaRep_eq_reflected_of_isPositiveReal rep hPR)
  change rep.alpha = -rep.alpha at h
  linarith

/-- Positive-real symmetry forces the representing measure to be even. -/
theorem nevanlinnaRep_measure_eq_reflection_of_isPositiveReal
    {F : ℍ → ℂ} (rep : Loewner.NevanlinnaRep F) (hPR : IsPositiveReal F) :
    rep.ν = reflectedFiniteMeasure rep.ν := by
  have h := congrArg Loewner.NevanlinnaRep.ν
    (nevanlinnaRep_eq_reflected_of_isPositiveReal rep hPR)
  exact h

/-- The linear Nevanlinna coefficient is unchanged by positive-real reflection. -/
@[simp]
theorem reflectedNevanlinnaRep_beta
    {F : ℍ → ℂ} (rep : Loewner.NevanlinnaRep F) (hPR : IsPositiveReal F) :
    (reflectedNevanlinnaRep rep hPR).beta = rep.beta :=
  rfl

/-- For an even measure, the Cauer and Nevanlinna kernel integrals agree. -/
theorem integral_cauerKernel_eq_nevanlinnaKernel_of_symmetric
    (ν : FiniteMeasure ℝ) (hν : ν = reflectedFiniteMeasure ν) (z : ℍ) :
    (∫ t : ℝ, cauerKernel t z ∂(ν : Measure ℝ)) =
      ∫ t : ℝ, Loewner.nevanlinnaKernel t z ∂(ν : Measure ℝ) := by
  have hK := Loewner.nevanlinnaKernel_integrable ν z
  have hKr := reflected_nevanlinnaKernel_integrable ν z
  calc
    (∫ t : ℝ, cauerKernel t z ∂(ν : Measure ℝ)) =
        ∫ t : ℝ, (2 : ℂ)⁻¹ *
          (Loewner.nevanlinnaKernel t z + Loewner.nevanlinnaKernel (-t) z)
            ∂(ν : Measure ℝ) := by
          refine integral_congr_ae ?_
          exact ae_of_all _ fun t => cauerKernel_eq_half_add_nevanlinnaKernel t z
    _ = (2 : ℂ)⁻¹ *
        ∫ t : ℝ,
          (Loewner.nevanlinnaKernel t z + Loewner.nevanlinnaKernel (-t) z)
            ∂(ν : Measure ℝ) := by
          exact integral_const_mul (2 : ℂ)⁻¹
            (fun t : ℝ =>
              Loewner.nevanlinnaKernel t z + Loewner.nevanlinnaKernel (-t) z)
    _ = (2 : ℂ)⁻¹ *
        ((∫ t : ℝ, Loewner.nevanlinnaKernel t z ∂(ν : Measure ℝ)) +
          ∫ t : ℝ, Loewner.nevanlinnaKernel (-t) z ∂(ν : Measure ℝ)) := by
          rw [integral_add hK hKr]
    _ = (2 : ℂ)⁻¹ *
        ((∫ t : ℝ, Loewner.nevanlinnaKernel t z ∂(ν : Measure ℝ)) +
          ∫ t : ℝ, Loewner.nevanlinnaKernel t z
            ∂(reflectedFiniteMeasure ν : Measure ℝ)) := by
          rw [integral_nevanlinnaKernel_reflectedFiniteMeasure]
    _ = ∫ t : ℝ, Loewner.nevanlinnaKernel t z ∂(ν : Measure ℝ) := by
          rw [← hν]
          ring

/-- A Cauer representation with an even finite measure. -/
structure CauerRep (F : ℍ → ℂ) where
  beta : NNReal
  ν : FiniteMeasure ℝ
  measure_symmetric : ν = reflectedFiniteMeasure ν
  formula :
    ∀ z : ℍ,
      F z = (beta : ℝ) * (z : ℂ) +
        ∫ t : ℝ, cauerKernel t z ∂(ν : Measure ℝ)

/--
**Cauer representation theorem for positive-real response functions.**

This is the classical Cauer representation of positive-real functions
(W. Cauer, Archiv für Elektrotechnik 17 (1926), 355–388; O. Brune,
J. Math. Phys. (MIT) 10 (1931), 191–236), obtained here through the
upper-half-plane Nevanlinna representation (Hiai, Theorem 2.24).
-/
theorem cauerRep_exists
    {F : ℍ → ℂ} (hPR : IsPositiveReal F)
    (hPick : MDiff F ∧ ∀ z : ℍ, 0 ≤ (F z).im) :
    Nonempty (CauerRep F) := by
  obtain ⟨rep⟩ := Loewner.upperHalfPlanePick_iff_nevanlinnaRep.mp hPick
  have halpha := nevanlinnaRep_alpha_eq_zero_of_isPositiveReal rep hPR
  have hν := nevanlinnaRep_measure_eq_reflection_of_isPositiveReal rep hPR
  refine ⟨{
    beta := rep.beta
    ν := rep.ν
    measure_symmetric := hν
    formula := ?_
  }⟩
  intro z
  rw [rep.formula z, halpha]
  simp only [Complex.ofReal_zero, zero_add]
  rw [integral_cauerKernel_eq_nevanlinnaKernel_of_symmetric rep.ν hν z]

end

end Quantum.TraceInequality.Loewner.ResponseFunctions
