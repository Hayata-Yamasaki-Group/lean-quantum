/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Quantum.QuantumMechanics.QuantumState

namespace QuantumState

universe u v

variable {ℋ : Type u} [Qudit ℋ]

/-- Positive definite operators: positive semidefinite with nonzero determinant, that is,
positive semidefinite and invertible on the finite-dimensional space `ℋ`. -/
def IsPositiveDefinite (X : L ℋ) : Prop :=
  X.IsPositive ∧ X.det ≠ 0

/-- Orthogonal projections: positive semidefinite idempotent operators. -/
def IsProjective (X : L ℋ) : Prop :=
  X.IsPositive ∧ IsIdempotentElem X

-- Functions of normal operators, Watrous (1.145) of https://cs.uwaterloo.ca/~watrous/TQI/TQI1.pdf:
-- for a spectral decomposition A = ∑_{k=1,…,m} λₖ Πₖ, f(A) := ∑_{k=1,…,m} f(λₖ) Πₖ.
-- This file does not define this; the development uses Mathlib's continuous functional
-- calculus (`cfc`) instead.

end QuantumState
