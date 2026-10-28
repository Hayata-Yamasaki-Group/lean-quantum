/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.InnerProductSpace.StarOrder

namespace QuantumState

universe u v

-- Qudit
/--
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press, 2018)
chapter-level reference (no numbered correspondence).
-/
class Qudit (a : Type u) extends
  NormedAddCommGroup a,
  InnerProductSpace ℂ a,
  CompleteSpace a,
  FiniteDimensional ℂ a

/-- Linear operators on `ℋ`: complex-linear maps `ℋ →ₗ[ℂ] ℋ`. On a finite-dimensional
(`Qudit`) space every such map is bounded; `B ℋ` is the bounded version. -/
abbrev L (ℋ : Type u) [AddCommGroup ℋ] [Module ℂ ℋ] : Type u :=
  ℋ →ₗ[ℂ] ℋ

/-- Bounded (continuous) complex-linear operators on `ℋ`. -/
abbrev B (ℋ : Type u) [AddCommGroup ℋ] [Module ℂ ℋ] [TopologicalSpace ℋ] : Type u :=
  ℋ →L[ℂ] ℋ

-- Identity operator
abbrev I (ℋ : Type u) [AddCommGroup ℋ] [Module ℂ ℋ] : L ℋ :=
  LinearMap.id

-- Braket notation
notation "⟨" x "∣" y "⟩" => inner ℂ x y

-- Adjoint
notation X"†" => LinearMap.adjoint X

variable {ℋ : Type u} [Qudit ℋ]

/-- The trace of a linear operator on the finite-dimensional space `ℋ` (`LinearMap.trace`),
complex-valued and complex-linear. -/
noncomputable abbrev Tr : L ℋ →ₗ[ℂ] ℂ := LinearMap.trace ℂ ℋ

-- Normal operators are defined by IsStarNormal
example (X : L ℋ) : Prop := IsStarNormal X

-- Hermitian operators are defined by IsSelfAdjoint
example (X : L ℋ) : Prop := IsSelfAdjoint X

-- Positive semidefinite operators are defined by IsPositive
example (X : L ℋ) : Prop := X.IsPositive

/-- Density operators: positive semidefinite operators with trace one. -/
def IsDensity (X : L ℋ) : Prop :=
  X.IsPositive ∧ Tr X = 1

-- Unitary operators are defined by unitary
example (X : L ℋ) : Prop := X ∈ unitary (L ℋ)

-- Functions of normal operators, Watrous (1.145) of https://cs.uwaterloo.ca/~watrous/TQI/TQI1.pdf:
-- for a spectral decomposition A = ∑_{k=1,…,m} λₖ Πₖ, f(A) := ∑_{k=1,…,m} f(λₖ) Πₖ.
-- This file does not define this; the development uses Mathlib's continuous functional
-- calculus (`cfc`) instead.

end QuantumState
