/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.Normed.Operator.CompleteCodomain
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Quantum.TraceInequality.HiaiPetz.Core.MatrixType
import Quantum.TraceInequality.HiaiPetz.Basic
import Quantum.TraceInequality.HiaiPetzTheorem.Basic

/-!
# Basic definitions for the Hansen--Pedersen chapter

This file fixes the local language used throughout the Hansen--Pedersen
development: bounded operators on a complex Hilbert space, real continuous
functional calculus, operator powers, and interval-based predicates for
operator monotonicity, convexity, and concavity. It also records the
finite-dimensional matrix variants and the half-line sets used in the
Hiai--Yanagi Chapter 5.1 statements.

## Main results

* `OperatorMonotoneOnInterval`, `OperatorConvexOnInterval`, and
  `OperatorConcaveOnInterval`: book-faithful interval predicates on a fixed
  Hilbert space.
* `AllHOperatorMonotoneOnInterval`, `AllHOperatorConvexOnInterval`, and
  `AllHOperatorConcaveOnInterval`: all-Hilbert-space versions used by the
  equivalence theorems.
* `halfOpenRay` and `positiveOpenRay`: half-line notation allowing the
  endpoint `⊤`.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1.
-/

namespace HansenPedersen

universe u

open CFC
open scoped Topology CStarAlgebra

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

/-- Operator real powers, implemented by applying the real CFC to `x ↦ x ^ p`. -/
noncomputable abbrev opRpow (p : ℝ) (A : L ℋ) : L ℋ :=
  cfcR (ℋ := ℋ) (fun x : ℝ => x ^ p) A

omit [Nontrivial (L ℋ)] in
/-- Operator concavity is operator convexity of the negated function.
Local API: definitional unfolding; terminology from Hiai, Theorem 6.2. -/
theorem operatorConcaveOnInterval_iff_convexOnInterval_neg (J : Set ℝ) (f : ℝ → ℝ) :
    OperatorConcaveOnInterval (ℋ := ℋ) J f ↔
      OperatorConvexOnInterval (ℋ := ℋ) J (fun x : ℝ ↦ -f x) :=
  Iff.rfl

omit [Nontrivial (L ℋ)] in
/-- The identity function is operator monotone on every interval.
Sanity lemma: functional calculus for `id` returns the original operator. -/
theorem operatorMonotoneOnInterval_id (J : Set ℝ) :
    OperatorMonotoneOnInterval (ℋ := ℋ) J id := by
  intro A B hA hB _ _ hAB
  have hAid : cfcR (ℋ := ℋ) id A = A := by
    simpa [cfcR] using (cfc_id (R := ℝ) (a := A) (ha := hA))
  have hBid : cfcR (ℋ := ℋ) id B = B := by
    simpa [cfcR] using (cfc_id (R := ℝ) (a := B) (ha := hB))
  rw [hAid, hBid]
  exact hAB

omit [Nontrivial (L ℋ)] in
/-- Constant functions are operator monotone on every interval.
Sanity lemma: functional calculus for a constant function is constant. -/
theorem operatorMonotoneOnInterval_const (J : Set ℝ) (c : ℝ) :
    OperatorMonotoneOnInterval (ℋ := ℋ) J (fun _ : ℝ ↦ c) := by
  intro A B hA hB _ _ _
  have hAconst :
      cfcR (ℋ := ℋ) (fun _ : ℝ ↦ c) A = algebraMap ℝ (L ℋ) c := by
    simpa [cfcR] using
      (cfc_const (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint)
        (r := c) (a := A) (ha := hA))
  have hBconst :
      cfcR (ℋ := ℋ) (fun _ : ℝ ↦ c) B = algebraMap ℝ (L ℋ) c := by
    simpa [cfcR] using
      (cfc_const (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint)
        (r := c) (a := B) (ha := hB))
  rw [hAconst, hBconst]

end HansenPedersen

open scoped MatrixOrder

namespace HansenPedersen

universe u

open CFC
open scoped Topology CStarAlgebra MatrixOrder

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

/-- Finite-dimensional matrix midpoint concavity on an interval.
This compatibility predicate is retained verbatim from `OperatorClasses` so that
Loewner consumers remain valid after that duplicate module is removed. -/
def MatrixOperatorMidpointConcaveOnInterval (J : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {n : ℕ} {A B : Mₙ n},
    IsSelfAdjoint A →
    IsSelfAdjoint B →
    spectrum ℝ A ⊆ J →
    spectrum ℝ B ⊆ J →
    (1 / 2 : ℝ) • (matrixCfcR f A + matrixCfcR f B) ≤
      matrixCfcR f ((1 / 2 : ℝ) • (A + B))

/-- Finite-dimensional (matrix) Jensen-style operator convexity on an interval. -/
def MatrixOperatorConvexOnInterval (J : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {n : ℕ} {A B : Mₙ n} {t : ℝ},
    IsSelfAdjoint A →
    IsSelfAdjoint B →
    0 ≤ t →
    t ≤ 1 →
    spectrum ℝ A ⊆ J →
    spectrum ℝ B ⊆ J →
    matrixCfcR f ((1 - t) • A + t • B) ≤
      (1 - t) • matrixCfcR f A + t • matrixCfcR f B

namespace MatrixOperatorConvexOnInterval

/-- Jensen-style matrix operator convexity specializes to the midpoint inequality. -/
theorem midpoint {J : Set ℝ} {f : ℝ → ℝ}
    (h : MatrixOperatorConvexOnInterval J f) :
    MatrixOperatorMidpointConvexOnInterval J f := by
  intro n A B hA hB hσA hσB
  have hhalf :=
    h hA hB (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hσA hσB
  have harg :
      (1 - (1 / 2 : ℝ)) • A + (1 / 2 : ℝ) • B = (1 / 2 : ℝ) • (A + B) := by
    ext i j
    simp
    ring
  have hrhs :
      (1 - (1 / 2 : ℝ)) • matrixCfcR f A + (1 / 2 : ℝ) • matrixCfcR f B =
        (1 / 2 : ℝ) • (matrixCfcR f A + matrixCfcR f B) := by
    ext i j
    simp
    ring
  rw [harg, hrhs] at hhalf
  exact hhalf

end MatrixOperatorConvexOnInterval

/-- All-Hilbert-space operator concavity is All-Hilbert-space operator convexity of the
negated function.
Source: Hiai, Theorem 6.2. -/
theorem allHOperatorConcaveOnInterval_iff_convexOnInterval_neg.{v}
    (J : Set ℝ) (f : ℝ → ℝ) :
    AllHOperatorConcaveOnInterval.{v} J f ↔
      AllHOperatorConvexOnInterval.{v} J (fun x : ℝ ↦ -f x) := by
  constructor
  · intro h K _ _ _ _ _
    exact (operatorConcaveOnInterval_iff_convexOnInterval_neg (ℋ := K) J f).1 (h K)
  · intro h K _ _ _ _ _
    exact (operatorConcaveOnInterval_iff_convexOnInterval_neg (ℋ := K) J f).2 (h K)

omit [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- The identity function is operator monotone on every interval and every Hilbert space.
Sanity lemma: the AllH predicate contains the identity function. -/
theorem allHOperatorMonotoneOnInterval_id.{v} (J : Set ℝ) :
    AllHOperatorMonotoneOnInterval.{v} J id := by
  intro K _ _ _ _ _
  exact operatorMonotoneOnInterval_id (ℋ := K) J

omit [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Constant functions are operator monotone on every interval and every Hilbert space.
Sanity lemma: the AllH predicate contains constant functions. -/
theorem allHOperatorMonotoneOnInterval_const.{v} (J : Set ℝ) (c : ℝ) :
    AllHOperatorMonotoneOnInterval.{v} J (fun _ : ℝ ↦ c) := by
  intro K _ _ _ _ _
  exact operatorMonotoneOnInterval_const (ℋ := K) J c

namespace AllHOperatorMonotoneOnInterval

/-- Restrict the interval in an AllH operator-monotonicity hypothesis.
The interval inclusion transports the two spectral-containment hypotheses.
Source: the interval-predicate API developed in the Hansen--Pedersen chapter. -/
theorem mono.{v} {J J' : Set ℝ} {f : ℝ → ℝ}
    (hJ : J' ⊆ J) (h : AllHOperatorMonotoneOnInterval.{v} J f) :
    AllHOperatorMonotoneOnInterval.{v} J' f := by
  intro K _ _ _ _ _ A B hA hB hσA hσB hAB
  exact h K hA hB (fun x hx ↦ hJ (hσA hx)) (fun x hx ↦ hJ (hσB hx)) hAB

end AllHOperatorMonotoneOnInterval

namespace AllHOperatorConvexOnInterval

/-- Restrict the interval in an AllH operator-convexity hypothesis.
The interval inclusion transports the two spectral-containment hypotheses.
Source: the interval-predicate API developed in the Hansen--Pedersen chapter. -/
theorem mono.{v} {J J' : Set ℝ} {f : ℝ → ℝ}
    (hJ : J' ⊆ J) (h : AllHOperatorConvexOnInterval.{v} J f) :
    AllHOperatorConvexOnInterval.{v} J' f := by
  intro K _ _ _ _ _ A B t hA hB ht0 ht1 hσA hσB
  exact h K hA hB ht0 ht1 (fun x hx ↦ hJ (hσA hx)) (fun x hx ↦ hJ (hσB hx))

end AllHOperatorConvexOnInterval

namespace AllHOperatorConcaveOnInterval

/-- Restrict the interval in an AllH operator-concavity hypothesis.
The interval inclusion transports the two spectral-containment hypotheses.
Source: the interval-predicate API developed in the Hansen--Pedersen chapter. -/
theorem mono.{v} {J J' : Set ℝ} {f : ℝ → ℝ}
    (hJ : J' ⊆ J) (h : AllHOperatorConcaveOnInterval.{v} J f) :
    AllHOperatorConcaveOnInterval.{v} J' f := by
  intro K _ _ _ _ _ A B t hA hB ht0 ht1 hσA hσB
  exact h K hA hB ht0 ht1 (fun x hx ↦ hJ (hσA hx)) (fun x hx ↦ hJ (hσB hx))

end AllHOperatorConcaveOnInterval

/-- ` [0, α) ` encoded as a set, allowing `α = ⊤`. -/
def halfOpenRay (α : WithTop ℝ) : Set ℝ :=
  { t : ℝ | 0 ≤ t ∧ (t : WithTop ℝ) < α }

/-- `(0, α)` encoded as a set, allowing `α = ⊤`. -/
def positiveOpenRay (α : WithTop ℝ) : Set ℝ :=
  { t : ℝ | 0 < t ∧ (t : WithTop ℝ) < α }

/-- The positive half-open ray is the nonnegative half-open ray with the origin removed. -/
lemma positiveOpenRay_eq_halfOpenRay_diff_zero (α : WithTop ℝ) :
    positiveOpenRay α = halfOpenRay α \ ({0} : Set ℝ) := by
  ext t
  constructor
  · intro ht
    refine ⟨?_, ?_⟩
    · exact ⟨le_of_lt ht.1, ht.2⟩
    · simpa [Set.mem_singleton_iff] using ne_of_gt ht.1
  · intro ht
    refine ⟨lt_of_le_of_ne ht.1.1 ?_, ht.1.2⟩
    exact Ne.symm (by simpa [Set.mem_singleton_iff] using ht.2)

/-- At endpoint `⊤`, `halfOpenRay` is the closed nonnegative half-line. -/
lemma halfOpenRay_top :
    halfOpenRay ⊤ = Set.Ici (0 : ℝ) := by
  ext t
  simp [halfOpenRay, Set.mem_Ici]

/-- At endpoint `⊤`, `positiveOpenRay` is the open positive half-line. -/
lemma positiveOpenRay_top :
    positiveOpenRay ⊤ = Set.Ioi (0 : ℝ) := by
  ext t
  simp [positiveOpenRay, Set.mem_Ioi]

omit [Nontrivial (L ℋ)] in
/-- A self-adjoint operator whose real spectrum lies in `[0,∞)` is positive. -/
lemma nonneg_of_isSelfAdjoint_of_spectrum_subset_Ici {A : L ℋ}
    (hA : IsSelfAdjoint A) (hσ : spectrum ℝ A ⊆ Set.Ici (0 : ℝ)) : 0 ≤ A := by
  have h' : algebraMap ℝ (L ℋ) (0 : ℝ) ≤ A :=
    (algebraMap_le_iff_le_spectrum (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint)
        (r := (0 : ℝ)) (a := A) (ha := hA)).2 (by
          intro x hx
          simpa [Set.Ici] using hσ hx)
  simpa using h'

omit [Nontrivial (L ℋ)] in
/-- A self-adjoint operator with spectrum in `(0,∞)` is positive. -/
lemma nonneg_of_isSelfAdjoint_of_spectrum_subset_Ioi {A : L ℋ}
    (hA : IsSelfAdjoint A) (hσ : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)) : 0 ≤ A := by
  refine nonneg_of_isSelfAdjoint_of_spectrum_subset_Ici (ℋ := ℋ) hA ?_
  intro x hx
  have hx0 : (0 : ℝ) < x := by
    simpa [Set.Ioi] using hσ hx
  exact le_of_lt hx0

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Converse companion of `nonneg_of_isSelfAdjoint_of_spectrum_subset_Ici`: the
real spectrum of a positive operator lies in `[0,∞)`, phrased with the
half-open ray at endpoint `⊤`. -/
lemma spectrum_subset_halfOpenRay_top_of_nonneg {A : L ℋ} (hA0 : 0 ≤ A) :
    spectrum ℝ A ⊆ halfOpenRay ⊤ := by
  intro x hx
  simpa [halfOpenRay_top, Set.mem_Ici] using
    (spectrum_nonneg_of_nonneg (𝕜 := ℝ) (A := L ℋ) (a := A) hA0 hx)

end HansenPedersen
