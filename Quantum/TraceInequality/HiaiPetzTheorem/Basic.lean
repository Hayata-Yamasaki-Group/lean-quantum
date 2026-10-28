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

/--
Jensen-style operator convexity on an arbitrary interval `J ⊆ ℝ`.
This interval predicate is written directly in terms of `cfcR` so that the
lightweight definition layer does not depend on `LownerHeinzTheorem`.
Source: the Hansen--Pedersen chapter; Hiai--Yanagi (2021), Section 5.1.
-/
def OperatorConvexOnInterval (J : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : L ℋ⦄ ⦃t : ℝ⦄,
    IsSelfAdjoint A → IsSelfAdjoint B →
    0 ≤ t → t ≤ 1 →
    spectrum ℝ A ⊆ J → spectrum ℝ B ⊆ J →
    cfcR (ℋ := ℋ) f ((1 - t) • A + t • B) ≤
      (1 - t) • cfcR (ℋ := ℋ) f A + t • cfcR (ℋ := ℋ) f B

/-- Operator concavity on an interval, encoded as operator convexity of `-f`. -/
def OperatorConcaveOnInterval (J : Set ℝ) (f : ℝ → ℝ) : Prop :=
  OperatorConvexOnInterval (ℋ := ℋ) J (fun x : ℝ => -f x)

/-- Complex continuous functional calculus on normal operators, via the generic `cfc`. -/
noncomputable abbrev cfcNormal (f : ℂ → ℂ) (A : L ℋ) : L ℋ :=
  cfc f A

end HansenPedersen

open scoped MatrixOrder

namespace HansenPedersen

universe u

open CFC
open scoped Topology CStarAlgebra MatrixOrder

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

/-- Finite-dimensional (matrix) midpoint operator convexity on an interval. -/
def MatrixOperatorMidpointConvexOnInterval (J : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {n : ℕ} {A B : Mₙ n},
    IsSelfAdjoint A →
    IsSelfAdjoint B →
    spectrum ℝ A ⊆ J →
    spectrum ℝ B ⊆ J →
    matrixCfcR f ((1 / 2 : ℝ) • (A + B)) ≤
      (1 / 2 : ℝ) • (matrixCfcR f A + matrixCfcR f B)

/-- Book-faithful midpoint operator convexity on an arbitrary interval `J ⊆ ℝ`. -/
def OperatorMidpointConvexOnInterval (J : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : L ℋ⦄,
    IsSelfAdjoint A → IsSelfAdjoint B →
    spectrum ℝ A ⊆ J → spectrum ℝ B ⊆ J →
    cfcR (ℋ := ℋ) f ((1 / 2 : ℝ) • (A + B)) ≤
      (1 / 2 : ℝ) • (cfcR (ℋ := ℋ) f A + cfcR (ℋ := ℋ) f B)

omit [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Jensen-style `H`-operator convexity on an interval for a given complex Hilbert space `K`. -/
def HOperatorConvexOnInterval (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    (J : Set ℝ) (f : ℝ → ℝ) : Prop :=
  OperatorConvexOnInterval (ℋ := K) J f

omit [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- `H`-operator concavity on an interval for a given complex Hilbert space `K`. -/
def HOperatorConcaveOnInterval (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    (J : Set ℝ) (f : ℝ → ℝ) : Prop :=
  OperatorConcaveOnInterval (ℋ := K) J f

omit [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- `H`-midpoint operator convexity on an interval for a given complex Hilbert space `K`. -/
def HOperatorMidpointConvexOnInterval (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    (J : Set ℝ) (f : ℝ → ℝ) : Prop :=
  OperatorMidpointConvexOnInterval (ℋ := K) J f

omit [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Jensen-style operator convexity on an interval for every complex Hilbert space. -/
def AllHOperatorConvexOnInterval (J : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)],
      HOperatorConvexOnInterval K J f

omit [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Operator concavity on an interval for every complex Hilbert space. -/
def AllHOperatorConcaveOnInterval (J : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)],
      HOperatorConcaveOnInterval K J f

omit [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Midpoint operator convexity on an interval for every complex Hilbert space. -/
def AllHOperatorMidpointConvexOnInterval (J : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)],
      HOperatorMidpointConvexOnInterval K J f

end HansenPedersen
