/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.Basic
import Mathlib.Algebra.DirectSum.LinearMap


/-!
# Neutral Hilbert--Schmidt matrix vocabulary
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

universe u

open Matrix
open scoped MatrixOrder CStarAlgebra Matrix.Norms.Frobenius ComplexOrder

noncomputable section

/-- Complex `n × n` matrices. -/
abbrev Mₙ (n : ℕ) := _root_.HiaiPetz.Mₙ n

/-- Compatibility name for the canonical Frobenius normed additive group.
Source: the Hiai--Petz matrix setup, `HiaiPetz.instMatrixNormedAddCommGroup`. -/
@[reducible, instance]
noncomputable def instMatrixNormedAddCommGroup {n : ℕ} : NormedAddCommGroup (Mₙ n) :=
  _root_.HiaiPetz.instMatrixNormedAddCommGroup

/-- Compatibility name for the canonical Frobenius normed space.
Source: the Hiai--Petz matrix setup, `HiaiPetz.instMatrixNormedSpace`. -/
@[reducible, instance]
noncomputable def instMatrixNormedSpace {n : ℕ} : NormedSpace ℂ (Mₙ n) :=
  _root_.HiaiPetz.instMatrixNormedSpace

/-- Compatibility name for the canonical Frobenius inner product.
Source: the Hiai--Petz matrix setup, `HiaiPetz.instMatrixInnerProductSpace`. -/
@[reducible, instance]
noncomputable def instMatrixInnerProductSpace {n : ℕ} : InnerProductSpace ℂ (Mₙ n) :=
  _root_.HiaiPetz.instMatrixInnerProductSpace

/-- Compatibility name for the canonical completeness instance.
Source: the Hiai--Petz matrix setup, `HiaiPetz.instMatrixCompleteSpace`. -/
@[reducible, instance]
noncomputable def instMatrixCompleteSpace {n : ℕ} : CompleteSpace (Mₙ n) :=
  _root_.HiaiPetz.instMatrixCompleteSpace


attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

/-- Hilbert--Schmidt linear maps between matrix spaces. -/
abbrev HSMap (n m : ℕ) := _root_.HiaiPetz.HSMap n m

/-- The Hilbert--Schmidt adjoint induced by the Frobenius inner product. -/
noncomputable def hsAdjoint {n m : ℕ} (Φ : HSMap n m) : HSMap m n :=
  (@ContinuousLinearMap.adjoint ℂ (Mₙ n) (Mₙ m)
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := n))
      (instMatrixNormedAddCommGroup (n := m))
      (instMatrixInnerProductSpace (n := n))
      (instMatrixInnerProductSpace (n := m))
      (instMatrixCompleteSpace (n := n))
      (instMatrixCompleteSpace (n := m))) Φ

end

end Quantum.TraceInequality.Loewner.HiaiPetz
