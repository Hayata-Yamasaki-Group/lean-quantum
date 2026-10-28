/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LownerHeinzCore

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Quantum.TraceInequality.HiaiPetz.LownerHeinzTheorem
import Quantum.TraceInequality.LiebAndo.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheorem
import Quantum.TraceInequality.TraceFunctionMonotonicity.LownerHeinzTheorem

namespace LownerHeinzTheorem

universe u v

open CFC

variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint]
variable [Nontrivial (ℋ →L[ℂ] ℋ)]

attribute [local instance] instAlgebraRealContinuousLinearMapComplexId_quantum

-- Cached `Algebra ℝ (ℋ →L[ℂ] ℋ)` keeps this deep superclass/instance search within
-- the default instance budget.
attribute [local instance] instNonnegSpectrumClassRealContinuousLinearMapComplexId_quantum

theorem operatorConvex_convexOn_univ {f : ℝ → ℝ} (hf : OperatorConvex (ℋ := ℋ) f) :
    ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hb1 : b ≤ 1 := by
    linarith
  have halg_combo (u v r s : ℝ) :
      u • (algebraMap ℝ (ℋ →L[ℂ] ℋ) r) + v • (algebraMap ℝ (ℋ →L[ℂ] ℋ) s) =
        algebraMap ℝ (ℋ →L[ℂ] ℋ) (u * r + v * s) := by
    calc
      u • (algebraMap ℝ (ℋ →L[ℂ] ℋ) r) + v • (algebraMap ℝ (ℋ →L[ℂ] ℋ) s) =
          (algebraMap ℝ (ℋ →L[ℂ] ℋ) u) * (algebraMap ℝ (ℋ →L[ℂ] ℋ) r) +
            (algebraMap ℝ (ℋ →L[ℂ] ℋ) v) * (algebraMap ℝ (ℋ →L[ℂ] ℋ) s) := by
              rw [Algebra.smul_def, Algebra.smul_def]
      _ = algebraMap ℝ (ℋ →L[ℂ] ℋ) (u * r) + algebraMap ℝ (ℋ →L[ℂ] ℋ) (v * s) := by
            simp
      _ = algebraMap ℝ (ℋ →L[ℂ] ℋ) (u * r + v * s) := by
            simp
  have hop :
      cfcR (ℋ := ℋ) f
          ((1 - b) • (algebraMap ℝ (ℋ →L[ℂ] ℋ) x) + b • (algebraMap ℝ ((ℋ →L[ℂ] ℋ)) y)) ≤
        (1 - b) • cfcR (ℋ := ℋ) f (algebraMap ℝ (ℋ →L[ℂ] ℋ) x) +
          b • cfcR (ℋ := ℋ) f (algebraMap ℝ (ℋ →L[ℂ] ℋ) y) :=
    hf (A := algebraMap ℝ (ℋ →L[ℂ] ℋ) x) (B := algebraMap ℝ (ℋ →L[ℂ] ℋ) y) (t
        := b) hb hb1
  have hx :
      cfcR (ℋ := ℋ) f (algebraMap ℝ (ℋ →L[ℂ] ℋ) x) = algebraMap ℝ ((ℋ →L[ℂ] ℋ)) (f x) := by
    simp [cfcR, LownerHeinzCore.cfcR]
  have hy :
      cfcR (ℋ := ℋ) f (algebraMap ℝ (ℋ →L[ℂ] ℋ) y) = algebraMap ℝ ((ℋ →L[ℂ] ℋ)) (f y) := by
    simp [cfcR, LownerHeinzCore.cfcR]
  have hxy :
      cfcR (ℋ := ℋ) f (algebraMap ℝ (ℋ →L[ℂ] ℋ) ((1 - b) * x + b * y)) =
        algebraMap ℝ (ℋ →L[ℂ] ℋ) (f ((1 - b) * x + b * y)) := by
    simpa [cfcR, LownerHeinzCore.cfcR] using
      cfc_algebraMap (A := (ℋ →L[ℂ] ℋ)) (((1 - b) * x + b * y)) f
  rw [halg_combo (u := 1 - b) (v := b) (r := x) (s := y), hxy, hx, hy,
    halg_combo (u := 1 - b) (v := b) (r := f x) (s := f y)] at hop
  have hscalar :
      algebraMap ℝ (ℋ →L[ℂ] ℋ) (f ((1 - b) * x + b * y)) ≤
        algebraMap ℝ (ℋ →L[ℂ] ℋ) ((1 - b) * f x + b * f y) := by
    simpa [Algebra.smul_def] using hop
  have hspec_le :
      ∀ z ∈ spectrum ℝ (algebraMap ℝ (ℋ →L[ℂ] ℋ) (f ((1 - b) * x + b * y))),
        z ≤ (1 - b) * f x + b * f y := by
    simpa using
      (le_algebraMap_iff_spectrum_le
        (R := ℝ) (A := (ℋ →L[ℂ] ℋ))
        (a := algebraMap ℝ (ℋ →L[ℂ] ℋ) (f ((1 - b) * x + b * y)))
        (r := (1 - b) * f x + b * f y)
        (ha := cfc_predicate_algebraMap (A := (ℋ →L[ℂ] ℋ)) (f ((1 - b) * x + b *
            y)))).1 hscalar
  have ha' : a = 1 - b := by
    linarith
  have hscalar' : f ((1 - b) * x + b * y) ≤ (1 - b) * f x + b * f y := by
    obtain ⟨z, hz⟩ :=
      ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ)
        (algebraMap ℝ (ℋ →L[ℂ] ℋ) (f ((1 - b) * x + b * y)))
        (cfc_predicate_algebraMap (A := (ℋ →L[ℂ] ℋ)) (f ((1 - b) * x + b * y)))
    have hz_eq : z = f ((1 - b) * x + b * y) := by
      have hz_single :=
        CFC.spectrum_algebraMap_subset (R := ℝ) (A := (ℋ →L[ℂ] ℋ)) (f ((1 - b) * x
            + b * y)) hz
      simpa using hz_single
    simpa [hz_eq] using hspec_le z hz
  simpa [smul_eq_mul, ha'] using hscalar'

theorem operatorConvex_continuousOn_univ {f : ℝ → ℝ} (hf : OperatorConvex (ℋ := ℋ) f) :
    ContinuousOn f Set.univ :=
  ConvexOn.continuousOn isOpen_univ (operatorConvex_convexOn_univ (ℋ := ℋ) hf)

theorem operatorConvex_continuousOn_spectrum_union {f : ℝ → ℝ}
    (hf : OperatorConvex (ℋ := ℋ) f) (A B : (ℋ →L[ℂ] ℋ)) :
    ContinuousOn f (spectrum ℝ A ∪ spectrum ℝ B) :=
  (operatorConvex_continuousOn_univ (ℋ := ℋ) hf).mono (by intro x hx; simp)

omit [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint] in
theorem log_operatorMonotoneOn_Ioi :
    OperatorMonotoneOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) Real.log := by
  simpa using
    (LownerHeinzCore.log_operatorMonotoneOn_Ioi (𝓐 := (ℋ →L[ℂ] ℋ)))

omit [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint] in
theorem log_operatorConcaveOn_Ioi :
    OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) Real.log := by
  simpa using
    (LownerHeinzCore.log_operatorConcaveOn_Ioi (𝓐 := (ℋ →L[ℂ] ℋ)))

omit [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint] in
theorem mul_log_operatorConvexOn_Ioi :
    OperatorConvexOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ x * Real.log x) := by
  simpa using
    (LownerHeinzCore.mul_log_operatorConvexOn_Ioi (𝓐 := (ℋ →L[ℂ] ℋ)))

omit [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint] in
theorem one_div_add_t_operatorConvexOn_Ici : ∀ (t : ℝ), 0 < t →
    OperatorConvexOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ 1 / (x + t)) := by
  intro t ht
  simpa using
    (LownerHeinzCore.one_div_add_t_operatorConvexOn_Ici
      (𝓐 := (ℋ →L[ℂ] ℋ)) t ht)

omit [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint] [Nontrivial (ℋ →L[ℂ] ℋ)] in
theorem ratio_add_t_operatorMonotoneOn_Ici : ∀ (t : ℝ), 0 < t →
    OperatorMonotoneOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x / (x + t)) := by
  intro t ht
  simpa using
    (LownerHeinzCore.ratio_add_t_operatorMonotoneOn_Ici
      (𝓐 := (ℋ →L[ℂ] ℋ)) t ht)

omit [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint] [Nontrivial (ℋ →L[ℂ] ℋ)] in
/-- The ratio functional calculus `x / (x + t)` is monotone on the positive cone. -/
@[gcongr]
theorem cfcR_ratio_add_le_cfcR_ratio_add_of_le {t : ℝ} (ht : 0 < t)
    {A B : (ℋ →L[ℂ] ℋ)} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hBA : B ≤ A)
    (hspA : spectrum ℝ A ⊆ Set.Ici (0 : ℝ))
    (hspB : spectrum ℝ B ⊆ Set.Ici (0 : ℝ)) :
    cfcR (fun x : ℝ ↦ x / (x + t)) B ≤ cfcR (fun x : ℝ ↦ x / (x + t)) A :=
  LownerHeinzCore.ratio_add_t_operatorMonotoneOn_Ici
    (𝓐 := (ℋ →L[ℂ] ℋ)) t ht hA hB hBA hspA hspB

omit [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint] in
theorem ratio_add_t_operatorConcaveOn_Ici : ∀ (t : ℝ), 0 < t →
    OperatorConcaveOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x / (x + t)) := by
  intro t ht
  simpa using
    (LownerHeinzCore.ratio_add_t_operatorConcaveOn_Ici
      (𝓐 := (ℋ →L[ℂ] ℋ)) t ht)

omit [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint] [Nontrivial (ℋ →L[ℂ] ℋ)] in
/-- The real-power functional calculus is monotone for exponents in `[0, 1]`. -/
@[gcongr]
theorem cfcR_rpow_le_cfcR_rpow_of_le {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    {A B : (ℋ →L[ℂ] ℋ)} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hBA : B ≤ A)
    (hspA : spectrum ℝ A ⊆ Set.Ici (0 : ℝ))
    (hspB : spectrum ℝ B ⊆ Set.Ici (0 : ℝ)) :
    cfcR (fun x : ℝ ↦ x ^ p) B ≤ cfcR (fun x : ℝ ↦ x ^ p) A :=
  LownerHeinzCore.power_Icc_zero_one_operatorMonotoneOn_Ici
    (𝓐 := (ℋ →L[ℂ] ℋ)) p hp hA hB hBA hspA hspB

omit [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint] in
/-- Hilbert-space specialization of
`LownerHeinzCore.power_Icc_zero_one_operatorConcaveOn_Ici`
in `LownerHeinz/RpowZeroOne.lean`. See the Core theorem's docstring for sources. -/
theorem power_Icc_zero_one_operatorConcaveOn_Ici : ∀ p ∈ Set.Icc (0 : ℝ) 1,
    OperatorConcaveOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  simpa using
    (LownerHeinzCore.power_Icc_zero_one_operatorConcaveOn_Ici
      (𝓐 := (ℋ →L[ℂ] ℋ)) p hp)

omit [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint] in
/-- Hilbert-space specialization of
`LownerHeinzCore.power_Icc_one_two_operatorConvexOn_Ici`
in `LownerHeinz/RpowOneTwo.lean`. See the Core theorem's docstring for sources. -/
theorem power_Icc_one_two_operatorConvexOn_Ici : ∀ p ∈ Set.Icc (1 : ℝ) 2,
    OperatorConvexOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  simpa using
    (LownerHeinzCore.power_Icc_one_two_operatorConvexOn_Ici
      (𝓐 := (ℋ →L[ℂ] ℋ)) p hp)

omit [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint] [Nontrivial (ℋ →L[ℂ] ℋ)] in
/-- Hilbert-space specialization of
`LownerHeinzCore.power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi`
in `LownerHeinz/NegPow.lean`. See the Core theorem's docstring for sources. -/
theorem power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi : ∀ p ∈ Set.Icc (-1 : ℝ) 0,
    OperatorMonotoneOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (fun x ↦ -(x ^ p)) := by
  intro p hp
  simpa using
    (LownerHeinzCore.power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi
      (𝓐 := (ℋ →L[ℂ] ℋ)) p hp)

omit [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint] [Nontrivial (ℋ →L[ℂ] ℋ)] in
/-- The negative real-power functional calculus is monotone after negation. -/
@[gcongr]
theorem cfcR_neg_rpow_le_cfcR_neg_rpow_of_le {p : ℝ}
    (hp : p ∈ Set.Icc (-1 : ℝ) 0) {A B : (ℋ →L[ℂ] ℋ)}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hBA : B ≤ A)
    (hspA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hspB : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    cfcR (fun x : ℝ ↦ -(x ^ p)) B ≤ cfcR (fun x : ℝ ↦ -(x ^ p)) A :=
  LownerHeinzCore.power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi
    (𝓐 := (ℋ →L[ℂ] ℋ)) p hp hA hB hBA hspA hspB

omit [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint] in
/-- Hilbert-space specialization of
`LownerHeinzCore.power_Icc_neg_one_zero_neg_operatorConcaveOn_Ioi`
in `LownerHeinz/NegPow.lean`. See the Core theorem's docstring for sources. -/
theorem power_Icc_neg_one_zero_neg_operatorConcaveOn_Ioi : ∀ p ∈ Set.Icc (-1 : ℝ) 0,
    OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (fun x ↦ -(x ^ p)) := by
  intro p hp
  simpa using
    (LownerHeinzCore.power_Icc_neg_one_zero_neg_operatorConcaveOn_Ioi
      (𝓐 := (ℋ →L[ℂ] ℋ)) p hp)

end LownerHeinzTheorem
