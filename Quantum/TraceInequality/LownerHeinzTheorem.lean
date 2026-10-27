/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LownerHeinzCore

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Uniform forms of the Lowner-Heinz inequalities

This module states operator monotonicity, antitonicity, convexity and concavity
uniformly over complex Hilbert spaces. Spectral restrictions give the usual interval
notions; the auxiliary predicates on all inputs use Mathlib's total functional
calculus and have separate degeneracy results.
-/

namespace LownerHeinzTheorem

universe u v

open CFC

variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint]
variable [Nontrivial (ℋ →L[ℂ] ℋ)]

noncomputable local instance : Algebra ℝ (ℋ →L[ℂ] ℋ) := by infer_instance

-- Cached `Algebra ℝ (ℋ →L[ℂ] ℋ)` keeps this deep superclass/instance search within
-- the default instance budget.
noncomputable local instance : NonnegSpectrumClass ℝ (ℋ →L[ℂ] ℋ) := inferInstance

noncomputable abbrev cfcR (f : ℝ → ℝ) (A : (ℋ →L[ℂ] ℋ)) : (ℋ →L[ℂ] ℋ) :=
  LownerHeinzCore.cfcR (𝓐 := (ℋ →L[ℂ] ℋ)) f A

/-- Fixed-space operator monotonicity on the Hilbert space `ℋ`. -/
abbrev OperatorMonotone (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorMonotone (𝓐 := (ℋ →L[ℂ] ℋ)) f

/-- Fixed-space operator monotonicity on `s` for the Hilbert space `ℋ`. -/
abbrev OperatorMonotoneOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorMonotoneOn (𝓐 := (ℋ →L[ℂ] ℋ)) s f

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

/-- Fixed-space operator convexity on `s` for the Hilbert space `ℋ`.

This localized version requires self-adjoint inputs and spectrum ⊆ s. For the intervals s used in
this chapter, it corresponds to standard operator convexity. The quantification ranges of the
fixed-space version and the version uniform over all spaces are distinguished. The caveats
concerning general nonconvex sets continue to apply. -/
abbrev OperatorConvexOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConvexOn (𝓐 := (ℋ →L[ℂ] ℋ)) s f

/-- Fixed-space operator concavity on the Hilbert space `ℋ`.

This is a helper predicate imposed on all elements, including non-self-adjoint inputs, under
totalized CFC; it is not standard operator concavity. Under the conventions of the pinned Mathlib
version, only the zero function satisfies it on a nontrivial algebra. See the degeneracy lemma
`LownerHeinzCore.OperatorConcave.eq_zero_of_nontrivial` (`LownerHeinz/GlobalDegeneracy.lean`).
-/
abbrev OperatorConcave (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConcave (𝓐 := (ℋ →L[ℂ] ℋ)) f

/-- Fixed-space operator concavity on `s` for the Hilbert space `ℋ`.

This localized version requires self-adjoint inputs and spectrum ⊆ s. For the intervals s used in
this chapter, it corresponds to standard operator concavity. The quantification ranges of the
fixed-space version and the version uniform over all spaces are distinguished. The caveats
concerning general nonconvex sets continue to apply. -/
abbrev OperatorConcaveOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConcaveOn (𝓐 := (ℋ →L[ℂ] ℋ)) s f

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
/-- Uniform operator monotonicity on `s` over all Hilbert spaces in universe `u`. -/
def OperatorMonotoneOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    letI : Nontrivial (K →L[ℂ] K) := inferInstance
    letI : ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint := inferInstance
    OperatorMonotoneOn (ℋ := K) s f

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
this chapter, it corresponds to standard operator convexity. The quantification ranges of the
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
this chapter, it corresponds to standard operator concavity. The quantification ranges of the
fixed-space version and the version uniform over all spaces are distinguished. The caveats
concerning general nonconvex sets continue to apply. -/
def OperatorConcaveOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    letI : Nontrivial (K →L[ℂ] K) := inferInstance
    letI : ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint := inferInstance
    OperatorConcaveOn (ℋ := K) s f

omit [ContinuousFunctionalCalculus ℝ (ℋ →L[ℂ] ℋ) IsSelfAdjoint] in
/-- Hilbert-space specialization of
`LownerHeinzCore.operatorConvexOn_rpow_Ici`
in `LownerHeinz/RpowOneTwo.lean`. See the Core theorem's docstring for sources. -/
theorem operatorConvexOn_rpow_Ici : ∀ p ∈ Set.Icc (1 : ℝ) 2,
    OperatorConvexOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  simpa using
    (LownerHeinzCore.operatorConvexOn_rpow_Ici
      (𝓐 := (ℋ →L[ℂ] ℋ)) p hp)

end LownerHeinzTheorem
