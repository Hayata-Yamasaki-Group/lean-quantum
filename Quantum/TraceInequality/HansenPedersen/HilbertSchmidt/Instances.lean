/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Core.Basic
import Mathlib.Analysis.Matrix.Order

/-!
# Named Hilbert-Schmidt instance witnesses

This file exposes the Frobenius matrix and Hilbert-Schmidt operator structures
as named reducible witnesses. Later files install these locally instead of
creating global instances, keeping typeclass search stable while preserving the
same mathematical structures fixed in the core Hiai-Petz setup.

## Main results

* `hsMatrixNormedAddCommGroup`, `hsMatrixNormedSpace`,
  `hsMatrixInnerProductSpace`, and `hsMatrixCompleteSpace`: named matrix-space
  Hilbert-Schmidt witnesses.
* `hsOpCStarAlgebra`, `hsOpComplexCFC`, and `hsOpRealCFC`: named C-star and
  continuous-functional-calculus witnesses for `HSOp n`.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Chapter 6, Hilbert-Schmidt matrix framework.
-/

namespace HiaiPetz

/-- Shared Hilbert--Schmidt matrix additive normed-group witness.

This is intentionally a named witness, not a global instance. Files that need it install it
locally, keeping the global typeclass environment unchanged. -/
@[reducible] noncomputable def hsMatrixNormedAddCommGroup {k : ℕ} :
    NormedAddCommGroup (Mₙ k) :=
  instMatrixNormedAddCommGroup (n := k)

/-- Shared Hilbert--Schmidt matrix complex normed-space witness. -/
@[reducible] noncomputable def hsMatrixNormedSpace {k : ℕ} : NormedSpace ℂ (Mₙ k) :=
  instMatrixNormedSpace (n := k)

/-- Shared Hilbert--Schmidt matrix inner-product witness. -/
@[reducible] noncomputable def hsMatrixInnerProductSpace {k : ℕ} :
    InnerProductSpace ℂ (Mₙ k) :=
  instMatrixInnerProductSpace (n := k)

/-- Shared Hilbert--Schmidt matrix completeness witness. -/
@[reducible] def hsMatrixCompleteSpace {k : ℕ} : CompleteSpace (Mₙ k) :=
  instMatrixCompleteSpace (n := k)

/-- Shared C-star algebra witness for Hilbert--Schmidt operators. -/
@[reducible] noncomputable def hsOpCStarAlgebra {n : ℕ} : CStarAlgebra (HSOp n) :=
  @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace (Mₙ n)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (instMatrixCompleteSpace (n := n))

/-- Shared complex CFC witness for Hilbert--Schmidt operators. -/
@[reducible] noncomputable def hsOpComplexCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℂ (HSOp n) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

/-- Shared real CFC witness for Hilbert--Schmidt operators. -/
@[reducible] def hsOpRealCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℝ (HSOp n) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

end HiaiPetz
