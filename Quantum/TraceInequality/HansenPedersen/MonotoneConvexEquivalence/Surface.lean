/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/
import Quantum.TraceInequality.HansenPedersen.MonotoneConvexEquivalence.ConditionVIToII

/-!
# Surface theorems for the endpoint monotone-convex equivalence

This file assembles the fixed-Hilbert-space endpoint implications into the
public statements of Hiai–Yanagi Theorem 5.1.8 and its monotone-concave
corollary.  The heavy proofs live in `ConditionVIToII`; this surface layer
packages them in the `AllH` predicates and combines them with Theorem 5.1.7.

## Main results

* `ConvexityCharacterization.conditionI_implies_conditionVI`: the global
  `(i) → (vi)` implication at `α = ⊤`.
* `ConvexityCharacterization.conditionVI_implies_conditionII`: the global
  `(vi) → (ii)` implication at `α = ⊤`.
* `operatorConvexity_characterizations_top`: Theorem 5.1.8.
* `allHOperatorMonotone_iff_concave_of_nonneg`: Corollary 5.1.9.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1, Theorem 5.1.8 and
  Corollary 5.1.9.
-/

namespace HansenPedersen

universe u

open CFC MeasureTheory
open scoped Topology
open Filter

namespace ConvexityCharacterization

section ConditionItoVI

/-- Global `AllH` form of `(i) → (vi)` in Theorem 5.1.8.  It applies the
fixed-space endpoint proof on each Hilbert space to make `-f` operator monotone
on `[0, ∞)`.
Source: Hiai–Yanagi, Theorem 5.1.8. -/
theorem conditionI_implies_conditionVI {f : ℝ → ℝ}
    (hf : ContinuousOn f (halfOpenRay ⊤))
    (hneg : ∀ t ∈ halfOpenRay ⊤, f t ≤ 0)
    (hI : ConditionI.{u} ⊤ f) :
    ConditionVI.{u} f := by
  intro K _ _ _ _ _
  exact conditionI_implies_conditionVI_fixed (K := K) hf hneg hI
end ConditionItoVI

section ConditionVItoII

variable {K : Type u}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]

attribute [local instance]
  instModuleRealLKScopedVI2
  instPosSMulMonoRealLKScopedVI2
  instSMulPosMonoRealLKScopedVI2
  instContinuousSMulRealLKScopedVI2
  instStarModuleRealLKScopedVI2
  instAlgebraRealLKScopedVI2
  instSMulRealLKScopedVI2
  instMulActionRealLKScopedVI2
  instSMulZeroClassRealLKScopedVI2
  instAddRightMonoLKScopedVI2
  instAddLeftMonoLKScopedVI2
  instAddRightReflectLELKScopedVI2
  instStarMulLKScopedVI2
  instMonoidLKScopedVI2
  instStarMulLPairScopedVI2
  instMonoidLPairScopedVI2
  instModuleRealLPairScopedVI2
  instCFCRealLPairScopedVI2

/-- Global `AllH` form of `(vi) → (ii)` in Theorem 5.1.8.  From monotonicity of
`-f` on `[0, ∞)`, it obtains the Jensen contraction inequality on every
Hilbert space.
Source: Hiai–Yanagi, Theorem 5.1.8. -/
theorem conditionVI_implies_conditionII {f : ℝ → ℝ}
    (hf : ContinuousOn f (halfOpenRay ⊤))
    (hneg : ∀ t ∈ halfOpenRay ⊤, f t ≤ 0)
    (hVI : ConditionVI.{u} f) :
    ConditionII.{u} ⊤ f := by
  intro K _ _ _ _ _ A C hA hσA hC
  exact conditionVI_implies_conditionII_fixed (K := K) hf hneg hVI hA hσA hC
end ConditionVItoII
end ConvexityCharacterization
/-- **Theorem 5.1.8**: operator-convexity characterizations at `α = ⊤`.
The final equivalence with `ConvexityCharacterization.ConditionVI` is under the nonpositive
hypothesis `f ≤ 0`.
Source: Hiai–Yanagi, Theorem 5.1.8. -/
theorem operatorConvexity_characterizations_top (f : ℝ → ℝ) :
  ContinuousOn f (halfOpenRay ⊤) →
    ((ConvexityCharacterization.ConditionI.{u} ⊤ f ↔
        ConvexityCharacterization.ConditionII.{u} ⊤ f) ∧
      (ConvexityCharacterization.ConditionI.{u} ⊤ f ↔
        ConvexityCharacterization.ConditionIII.{u} ⊤ f) ∧
      (ConvexityCharacterization.ConditionI.{u} ⊤ f ↔
        ConvexityCharacterization.ConditionIV.{u} ⊤ f) ∧
      (ConvexityCharacterization.ConditionI.{u} ⊤ f ↔
        ConvexityCharacterization.ConditionV.{u} ⊤ f)) ∧
    ((∀ t ∈ halfOpenRay ⊤, f t ≤ 0) →
      (ConvexityCharacterization.ConditionI.{u} ⊤ f ↔
        ConvexityCharacterization.ConditionVI.{u} f)) := by
  intro hf
  have h57 := operatorConvexity_characterizations (α := ⊤) f (by simp) hf
  refine ⟨h57, ?_⟩
  intro hneg
  have hIffII :
      ConvexityCharacterization.ConditionI.{u} ⊤ f ↔
        ConvexityCharacterization.ConditionII.{u} ⊤ f := h57.1
  refine ⟨?_, ?_⟩
  · intro hI
    exact ConvexityCharacterization.conditionI_implies_conditionVI (hf := hf) (hneg := hneg) hI
  · intro hVI
    have hII : ConvexityCharacterization.ConditionII.{u} ⊤ f :=
      ConvexityCharacterization.conditionVI_implies_conditionII (hf := hf) (hneg := hneg) hVI
    exact hIffII.mpr hII
private lemma conditionVI_neg_iff_monotone {f : ℝ → ℝ} :
    ConvexityCharacterization.ConditionVI.{u} (fun t : ℝ ↦ -f t) ↔
      AllHOperatorMonotoneOnInterval.{u} (halfOpenRay ⊤) f := by
  simp [ConvexityCharacterization.ConditionVI]
private lemma conditionI_neg_iff_concave_and_nonneg_zero {f : ℝ → ℝ} :
    ConvexityCharacterization.ConditionI.{u} ⊤ (fun t : ℝ ↦ -f t) ↔
      (AllHOperatorConcaveOnInterval.{u} (halfOpenRay ⊤) f ∧ 0 ≤ f 0) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [ConvexityCharacterization.ConditionI, AllHOperatorConcaveOnInterval,
        HOperatorConcaveOnInterval,
        OperatorConcaveOnInterval, LownerHeinzTheorem.OperatorConcaveOn] using h.1
    · simpa [ConvexityCharacterization.ConditionI] using h.2
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [ConvexityCharacterization.ConditionI, AllHOperatorConcaveOnInterval,
        HOperatorConcaveOnInterval,
        OperatorConcaveOnInterval, LownerHeinzTheorem.OperatorConcaveOn] using h.1
    · simpa [ConvexityCharacterization.ConditionI] using h.2
/-- **Corollary 5.1.9**: nonnegative operator monotone functions on `[0,∞)` are exactly
operator concave functions.
Source: Hiai–Yanagi, Corollary 5.1.9. -/
theorem allHOperatorMonotone_iff_concave_of_nonneg {f : ℝ → ℝ}
    (hf : ContinuousOn f (halfOpenRay ⊤))
    (hnonneg : ∀ t ∈ halfOpenRay ⊤, 0 ≤ f t) :
    (AllHOperatorMonotoneOnInterval.{u} (halfOpenRay ⊤) f ↔
      AllHOperatorConcaveOnInterval.{u} (halfOpenRay ⊤) f) := by
  have hf_neg : ContinuousOn (fun t : ℝ ↦ -f t) (halfOpenRay ⊤) := hf.neg
  have hneg_neg : ∀ t ∈ halfOpenRay ⊤, -f t ≤ 0 := by
    intro t ht
    simpa using neg_nonpos.mpr (hnonneg t ht)
  have h0_nonneg : 0 ≤ f 0 := by
    have h0 : 0 ∈ halfOpenRay ⊤ := by
      simp [halfOpenRay_top]
    exact hnonneg 0 h0
  have h58 := operatorConvexity_characterizations_top (fun t : ℝ ↦ -f t)
  change
      ContinuousOn (fun t : ℝ ↦ -f t) (halfOpenRay ⊤) →
        ((ConvexityCharacterization.ConditionI.{u} ⊤ (fun t : ℝ ↦ -f t) ↔
            ConvexityCharacterization.ConditionII.{u} ⊤ (fun t : ℝ ↦ -f t)) ∧
          (ConvexityCharacterization.ConditionI.{u} ⊤ (fun t : ℝ ↦ -f t) ↔
            ConvexityCharacterization.ConditionIII.{u} ⊤ (fun t : ℝ ↦ -f t)) ∧
          (ConvexityCharacterization.ConditionI.{u} ⊤ (fun t : ℝ ↦ -f t) ↔
            ConvexityCharacterization.ConditionIV.{u} ⊤ (fun t : ℝ ↦ -f t)) ∧
          (ConvexityCharacterization.ConditionI.{u} ⊤ (fun t : ℝ ↦ -f t) ↔
            ConvexityCharacterization.ConditionV.{u} ⊤ (fun t : ℝ ↦ -f t))) ∧
        ((∀ t ∈ halfOpenRay ⊤, -f t ≤ 0) →
          (ConvexityCharacterization.ConditionI.{u} ⊤ (fun t : ℝ ↦ -f t) ↔
            ConvexityCharacterization.ConditionVI.{u} (fun t : ℝ ↦ -f t))) at h58
  have h58 := h58 hf_neg
  have hiff : ConvexityCharacterization.ConditionI.{u} ⊤ (fun t : ℝ ↦ -f t) ↔
      ConvexityCharacterization.ConditionVI.{u} (fun t : ℝ ↦ -f t) := h58.2 hneg_neg
  constructor
  · intro hmono
    have hVI : ConvexityCharacterization.ConditionVI.{u} (fun t : ℝ ↦ -f t) :=
      (conditionVI_neg_iff_monotone (f := f)).mpr hmono
    have hI : ConvexityCharacterization.ConditionI.{u} ⊤ (fun t : ℝ ↦ -f t) := hiff.mpr hVI
    exact ((conditionI_neg_iff_concave_and_nonneg_zero (f := f)).mp hI).1
  · intro hconc
    have hI : ConvexityCharacterization.ConditionI.{u} ⊤ (fun t : ℝ ↦ -f t) :=
      (conditionI_neg_iff_concave_and_nonneg_zero (f := f)).mpr ⟨hconc, h0_nonneg⟩
    have hVI : ConvexityCharacterization.ConditionVI.{u} (fun t : ℝ ↦ -f t) := hiff.mp hI
    exact (conditionVI_neg_iff_monotone (f := f)).mp hVI
end HansenPedersen
