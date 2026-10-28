/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.MatrixHilbert
import Mathlib.Algebra.DirectSum.LinearMap

/-!
# Two-positive maps for the Carlen--Lieb--Ruskai route

This file introduces only the Loewner-side theorem-facing predicates needed to
state the Lieb--Ruskai layer of the Hiai--Petz application.  It does not import
the existing Hiai--Petz proof route or any vNentropy module.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder

noncomputable section

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

/--
Flatten a `2 × 2` block matrix with ordinary finite-dimensional matrix entries
to a single ordinary complex matrix.
-/
def twoBlockMatrixFlatten {n : ℕ} (M : Matrix (Fin 2) (Fin 2) (Mₙ n)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.fromBlocks
    (M (0 : Fin 2) (0 : Fin 2))
    (M (0 : Fin 2) (1 : Fin 2))
    (M (1 : Fin 2) (0 : Fin 2))
    (M (1 : Fin 2) (1 : Fin 2))

/--
Positive semidefiniteness for block matrices whose entries are ordinary
finite-dimensional complex matrices.

This is the theorem-facing matrix statement needed for the Carlen--Lieb--Ruskai
route.  It is stated by flattening the block matrix to an ordinary complex
matrix, so that Mathlib's Schur complement API for `Matrix.PosSemidef` applies.
-/
def BlockMatrixPosSemidef {n : ℕ} (M : Matrix (Fin 2) (Fin 2) (Mₙ n)) : Prop :=
  (twoBlockMatrixFlatten M).PosSemidef

/--
Finite-dimensional two-positivity for Hilbert--Schmidt linear maps.

The amplified map is the entrywise map on `2 × 2` block matrices.
-/
def IsTwoPositiveMap {n m : ℕ} (Ψ : HSMap n m) : Prop :=
  ∀ M : Matrix (Fin 2) (Fin 2) (Mₙ n),
    BlockMatrixPosSemidef M → BlockMatrixPosSemidef (M.map Ψ)

/-- Unitality for matrix-space maps. -/
def IsUnitalMap {n m : ℕ} (Ψ : HSMap n m) : Prop :=
  Ψ (1 : Mₙ n) = (1 : Mₙ m)

/-- The map hypothesis used by the Carlen--Lieb--Ruskai route. -/
def IsUnitalTwoPositiveMap {n m : ℕ} (Ψ : HSMap n m) : Prop :=
  IsUnitalMap Ψ ∧ IsTwoPositiveMap Ψ

/-- The `2 × 2` Schur block used in the Lieb--Ruskai argument. -/
def liebRuskaiBlock {n : ℕ} (C X : Mₙ n) : Matrix (Fin 2) (Fin 2) (Mₙ n) :=
  ![![C, X], ![Matrix.conjTranspose X, Matrix.conjTranspose X * C⁻¹ * X]]

/-- The Schur complement expression in the Lieb--Ruskai inequality. -/
def liebRuskaiSchur {n m : ℕ} (Ψ : HSMap n m) (C X : Mₙ n) : Mₙ m :=
  Ψ (Matrix.conjTranspose X * C⁻¹ * X) -
    Matrix.conjTranspose (Ψ X) * (Ψ C)⁻¹ * Ψ X

/-- The input Schur block is positive when `C` is positive definite. -/
theorem liebRuskaiBlock_posSemidef {n : ℕ} {C X : Mₙ n}
    (hC : C.PosDef) :
    BlockMatrixPosSemidef (liebRuskaiBlock C X) := by
  classical
  letI := hC.isUnit.invertible
  exact
    (Matrix.PosDef.fromBlocks₁₁
      (A := C) (B := X) (D := Matrix.conjTranspose X * C⁻¹ * X) hC).2 <| by
        simpa using (Matrix.PosSemidef.zero :
          (0 : Mₙ n).PosSemidef)

/--
Lieb--Ruskai inequality for a two-positive map, in Schur-complement form.

The positive-definiteness of `Ψ C` is kept explicit.  For `C = 1` it follows
from unitality (`kadisonChoi_schwarz_of_isUnitalTwoPositiveMap` below); the
Carlen fixed-kernel DPI `gKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef`
takes the corresponding positive-definiteness of the adjoint images as
hypotheses.
-/
theorem liebRuskai_inequality_of_isTwoPositiveMap {n m : ℕ}
    {Ψ : HSMap n m} {C X : Mₙ n}
    (hΨ : IsTwoPositiveMap Ψ)
    (hC : C.PosDef)
    (hΨC : (Ψ C).PosDef) :
    (liebRuskaiSchur Ψ C X).PosSemidef := by
  classical
  have hbase : BlockMatrixPosSemidef (liebRuskaiBlock C X) :=
    liebRuskaiBlock_posSemidef (C := C) (X := X) hC
  have hout : BlockMatrixPosSemidef ((liebRuskaiBlock C X).map Ψ) :=
    hΨ (liebRuskaiBlock C X) hbase
  have hstar : Ψ (Matrix.conjTranspose X) = Matrix.conjTranspose (Ψ X) := by
    ext i j
    have hentry :=
      hout.1.apply (Sum.inr i) (Sum.inl j)
    simpa [BlockMatrixPosSemidef, twoBlockMatrixFlatten, liebRuskaiBlock]
      using hentry.symm
  have hflat :
      twoBlockMatrixFlatten ((liebRuskaiBlock C X).map Ψ) =
        Matrix.fromBlocks (Ψ C) (Ψ X) (Matrix.conjTranspose (Ψ X))
          (Ψ (Matrix.conjTranspose X * C⁻¹ * X)) := by
    ext i j
    cases i <;> cases j <;>
      simp [twoBlockMatrixFlatten, liebRuskaiBlock, hstar]
  have hout' :
      (Matrix.fromBlocks (Ψ C) (Ψ X) (Matrix.conjTranspose (Ψ X))
        (Ψ (Matrix.conjTranspose X * C⁻¹ * X))).PosSemidef := by
    simpa [BlockMatrixPosSemidef, hflat] using hout
  letI := hΨC.isUnit.invertible
  have hschur :=
    (Matrix.PosDef.fromBlocks₁₁
      (A := Ψ C) (B := Ψ X)
      (D := Ψ (Matrix.conjTranspose X * C⁻¹ * X)) hΨC).1 hout'
  simpa [liebRuskaiSchur] using hschur

/--
Kadison--Choi Schwarz inequality for unital two-positive maps, obtained from
Lieb--Ruskai with `C = 1`.
-/
theorem kadisonChoi_schwarz_of_isUnitalTwoPositiveMap {n m : ℕ}
    {Ψ : HSMap n m} (hΨ : IsUnitalTwoPositiveMap Ψ) (Y : Mₙ n) :
    (Ψ (Matrix.conjTranspose Y * Y) -
      Matrix.conjTranspose (Ψ Y) * Ψ Y).PosSemidef := by
  classical
  have hC : (1 : Mₙ n).PosDef := Matrix.PosDef.one
  have hΨC : (Ψ (1 : Mₙ n)).PosDef := by
    simpa [IsUnitalMap] using (hΨ.1 ▸ (Matrix.PosDef.one : (1 : Mₙ m).PosDef))
  have hLR :=
    liebRuskai_inequality_of_isTwoPositiveMap
      (Ψ := Ψ) (C := (1 : Mₙ n)) (X := Y) hΨ.2 hC hΨC
  have hunit : Ψ (1 : Mₙ n) = (1 : Mₙ m) := hΨ.1
  simpa [liebRuskaiSchur, hunit] using hLR

end

end Quantum.TraceInequality.Loewner.HiaiPetz
