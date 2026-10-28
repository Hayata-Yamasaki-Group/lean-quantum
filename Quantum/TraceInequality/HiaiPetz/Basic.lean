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

/-- The algebra of bounded complex-linear operators on a complex Hilbert space. -/
abbrev L (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] : Type u :=
  ℋ →L[ℂ] ℋ

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

/-- Real continuous functional calculus for self-adjoint bounded operators. -/
noncomputable abbrev cfcR (f : ℝ → ℝ) (A : L ℋ) : L ℋ :=
  cfc (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint) f A

/-- Book-faithful operator monotonicity on an arbitrary interval `J ⊆ ℝ`. -/
def OperatorMonotoneOnInterval (J : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : L ℋ⦄,
    IsSelfAdjoint A → IsSelfAdjoint B →
    spectrum ℝ A ⊆ J → spectrum ℝ B ⊆ J →
    A ≤ B →
    cfcR (ℋ := ℋ) f A ≤ cfcR (ℋ := ℋ) f B

open scoped MatrixOrder

/-- The finite-dimensional complex matrix algebra used for matrix-level predicates. -/
abbrev Mₙ (n : ℕ) := HiaiPetz.Mₙ n

/-- Matrix real CFC transported through the Euclidean-space operator equivalence. -/
noncomputable abbrev matrixCfcR {n : ℕ} (f : ℝ → ℝ) (A : Mₙ n) : Mₙ n :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm
    (cfc (R := ℝ) (A := EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
      (p := IsSelfAdjoint) f
      ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A))

end HansenPedersen

open scoped MatrixOrder

/-- Finite-dimensional (matrix) operator monotonicity on an interval. -/
def Quantum.TraceInequality.MatrixOperatorMonotoneOnInterval (J : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ},
    IsSelfAdjoint A →
    IsSelfAdjoint B →
    spectrum ℝ A ⊆ J →
    spectrum ℝ B ⊆ J →
    A ≤ B →
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm
        (cfc (R := ℝ)
          (A := EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
          (p := IsSelfAdjoint) f
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A)) ≤
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm
        (cfc (R := ℝ)
          (A := EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
          (p := IsSelfAdjoint) f
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) B))

namespace HansenPedersen

universe u

open CFC
open scoped Topology CStarAlgebra MatrixOrder

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

omit [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- `H`-operator monotonicity on an interval for a given complex Hilbert space `K`. -/
def HOperatorMonotoneOnInterval (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    (J : Set ℝ) (f : ℝ → ℝ) : Prop :=
  OperatorMonotoneOnInterval (ℋ := K) J f

omit [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
  [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- Operator monotonicity on an interval for every complex Hilbert space. -/
def AllHOperatorMonotoneOnInterval (J : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)],
      HOperatorMonotoneOnInterval K J f

end HansenPedersen
