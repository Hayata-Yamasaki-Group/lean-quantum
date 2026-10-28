/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Quantum.TraceInequality.LiebAndo.LownerHeinz.Defs
import Quantum.TraceInequality.LiebAndo.LownerHeinz.Reciprocal
import Quantum.TraceInequality.LownerHeinzTheorem

namespace LownerHeinzTheorem

universe u v

open CFC

variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint]
variable [Nontrivial (ℋ →L[ℂ] ℋ)]

noncomputable local instance : Algebra ℝ (ℋ →L[ℂ] ℋ) := by infer_instance

/-- Fixed-space operator monotonicity on the Hilbert space `ℋ`. -/
abbrev OperatorMonotone (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorMonotone (𝓐 := (ℋ →L[ℂ] ℋ)) f

/-- Fixed-space operator antitonicity on the Hilbert space `ℋ`. -/
abbrev OperatorAntitone (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorAntitone (𝓐 := (ℋ →L[ℂ] ℋ)) f

/-- Fixed-space operator antitonicity on `s` for the Hilbert space `ℋ`. -/
abbrev OperatorAntitoneOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorAntitoneOn (𝓐 := (ℋ →L[ℂ] ℋ)) s f

/-- Fixed-space operator convexity on the Hilbert space `ℋ`.

This is a helper predicate imposed on all elements, including non-self-adjoint inputs, under
totalized CFC; it is not standard operator convexity. Under the conventions of the pinned Mathlib
version, only the zero function satisfies it on a nontrivial algebra. See the degeneracy lemma
`LownerHeinzCore.OperatorConvex.eq_zero_of_nontrivial` (`LownerHeinz/GlobalDegeneracy.lean`).
-/
abbrev OperatorConvex (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConvex (𝓐 := (ℋ →L[ℂ] ℋ)) f

/-- Fixed-space operator concavity on the Hilbert space `ℋ`.

This is a helper predicate imposed on all elements, including non-self-adjoint inputs, under
totalized CFC; it is not standard operator concavity. Under the conventions of the pinned Mathlib
version, only the zero function satisfies it on a nontrivial algebra. See the degeneracy lemma
`LownerHeinzCore.OperatorConcave.eq_zero_of_nontrivial` (`LownerHeinz/GlobalDegeneracy.lean`).
-/
abbrev OperatorConcave (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConcave (𝓐 := (ℋ →L[ℂ] ℋ)) f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint]
    [Nontrivial (ℋ →L[ℂ] ℋ)] in
/-- Uniform operator monotonicity over all Hilbert spaces in universe `u`. -/
def OperatorMonotoneAll (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    letI : Nontrivial (K →L[ℂ] K) := inferInstance
    letI : ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint := inferInstance
    OperatorMonotone (ℋ := K) f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint]
    [Nontrivial (ℋ →L[ℂ] ℋ)] in
/-- Uniform operator antitonicity over all Hilbert spaces in universe `u`. -/
def OperatorAntitoneAll (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    letI : Nontrivial (K →L[ℂ] K) := inferInstance
    letI : ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint := inferInstance
    OperatorAntitone (ℋ := K) f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint]
    [Nontrivial (ℋ →L[ℂ] ℋ)] in
/-- Uniform operator antitonicity on `s` over all Hilbert spaces in universe `u`. -/
def OperatorAntitoneOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    letI : Nontrivial (K →L[ℂ] K) := inferInstance
    letI : ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint := inferInstance
    OperatorAntitoneOn (ℋ := K) s f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint]
    [Nontrivial (ℋ →L[ℂ] ℋ)] in
/-- Uniform operator convexity over all Hilbert spaces in universe `u`.

This is a helper predicate imposed on all elements, including non-self-adjoint inputs, under
totalized CFC; it is not standard operator convexity. Under the conventions of the pinned Mathlib
version, only the zero function satisfies it on a nontrivial algebra. See the degeneracy lemma
`LownerHeinzCore.OperatorConvex.eq_zero_of_nontrivial` (`LownerHeinz/GlobalDegeneracy.lean`).
-/
def OperatorConvexAll (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    letI : Nontrivial (K →L[ℂ] K) := inferInstance
    letI : ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint := inferInstance
    OperatorConvex (ℋ := K) f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint]
    [Nontrivial (ℋ →L[ℂ] ℋ)] in
/-- Uniform operator convexity on `s` over all Hilbert spaces in universe `u`.

This localized version requires self-adjoint inputs and spectrum ⊆ s. For the intervals s used in
this development, it corresponds to standard operator convexity. The quantification ranges of the
fixed-space version and the version uniform over all spaces are distinguished. The caveats
concerning general nonconvex sets continue to apply. -/
def OperatorConvexOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    letI : Nontrivial (K →L[ℂ] K) := inferInstance
    letI : ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint := inferInstance
    OperatorConvexOn (ℋ := K) s f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint]
    [Nontrivial (ℋ →L[ℂ] ℋ)] in
/-- Uniform operator concavity over all Hilbert spaces in universe `u`.

This is a helper predicate imposed on all elements, including non-self-adjoint inputs, under
totalized CFC; it is not standard operator concavity. Under the conventions of the pinned Mathlib
version, only the zero function satisfies it on a nontrivial algebra. See the degeneracy lemma
`LownerHeinzCore.OperatorConcave.eq_zero_of_nontrivial` (`LownerHeinz/GlobalDegeneracy.lean`).
-/
def OperatorConcaveAll (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    letI : Nontrivial (K →L[ℂ] K) := inferInstance
    letI : ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint := inferInstance
    OperatorConcave (ℋ := K) f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint]
    [Nontrivial (ℋ →L[ℂ] ℋ)] in
/-- Uniform operator concavity on `s` over all Hilbert spaces in universe `u`.

This localized version requires self-adjoint inputs and spectrum ⊆ s. For the intervals s used in
this development, it corresponds to standard operator concavity. The quantification ranges of the
fixed-space version and the version uniform over all spaces are distinguished. The caveats
concerning general nonconvex sets continue to apply. -/
def OperatorConcaveOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    letI : Nontrivial (K →L[ℂ] K) := inferInstance
    letI : ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint := inferInstance
    OperatorConcaveOn (ℋ := K) s f

omit [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint] [Nontrivial (ℋ →L[ℂ] ℋ)] in
theorem one_div_operatorAntitoneOn_Ioi :
    OperatorAntitoneOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x) := by
  simpa using
    (LownerHeinzCore.one_div_operatorAntitoneOn_Ioi (𝓐 := (ℋ →L[ℂ] ℋ)))

omit [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint] [Nontrivial (ℋ →L[ℂ] ℋ)] in
/-- The reciprocal functional calculus is antitone on the positive spectrum. -/
@[gcongr]
theorem cfcR_one_div_le_cfcR_one_div_of_le {A B : (ℋ →L[ℂ] ℋ)}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hBA : B ≤ A)
    (hspA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hspB : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    cfcR (fun x : ℝ ↦ 1 / x) A ≤ cfcR (fun x : ℝ ↦ 1 / x) B :=
  LownerHeinzCore.one_div_operatorAntitoneOn_Ioi
    (𝓐 := (ℋ →L[ℂ] ℋ)) hA hB hBA hspA hspB

omit [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint] [Nontrivial (ℋ →L[ℂ] ℋ)] in
theorem one_div_add_t_operatorAntitoneOn_Ici : ∀ (t : ℝ), 0 < t →
    OperatorAntitoneOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ 1 / (x + t)) := by
  intro t ht
  simpa using
    (LownerHeinzCore.one_div_add_t_operatorAntitoneOn_Ici
      (𝓐 := (ℋ →L[ℂ] ℋ)) t ht)

omit [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint] [Nontrivial (ℋ →L[ℂ] ℋ)] in
/-- The shifted reciprocal functional calculus is antitone on the positive cone. -/
@[gcongr]
theorem cfcR_one_div_add_le_cfcR_one_div_add_of_le {t : ℝ} (ht : 0 < t)
    {A B : (ℋ →L[ℂ] ℋ)} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hBA : B ≤ A)
    (hspA : spectrum ℝ A ⊆ Set.Ici (0 : ℝ))
    (hspB : spectrum ℝ B ⊆ Set.Ici (0 : ℝ)) :
    cfcR (fun x : ℝ ↦ 1 / (x + t)) A ≤ cfcR (fun x : ℝ ↦ 1 / (x + t)) B :=
  LownerHeinzCore.one_div_add_t_operatorAntitoneOn_Ici
    (𝓐 := (ℋ →L[ℂ] ℋ)) t ht hA hB hBA hspA hspB

end LownerHeinzTheorem
