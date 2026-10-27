import Quantum.TraceInequality.Basic
/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.CompressionInequality.SpectralBounds
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Rotated block compressions for Hansen–Pedersen inequalities

This file isolates the block-rotation algebra used in the proof of
Hiai–Yanagi Theorem 5.1.7.

## Main results

* `unitaryConjStarAlgHom`: star-algebra homomorphism for unitary conjugation.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1, Theorem 5.1.7.
-/

namespace HansenPedersen

universe u

open CFC MeasureTheory
open scoped Topology
open Filter

section NormalCFC517

namespace ConvexityCharacterization

section RotatedBlockCompression

variable {K : Type*}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]

/-- Star-algebra homomorphism implementing conjugation by a unitary.  It is the
transport map used to move real CFC expressions through block rotations. -/
noncomputable def unitaryConjStarAlgHom (U : unitary (L K)) : L K →⋆ₐ[ℂ] L K :=
  StarAlgHomClass.toStarAlgHom (Unitary.conjStarAlgAut ℂ (L K) (star U))

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
/-- Evaluates `unitaryConjStarAlgHom` as the concrete conjugation
`A ↦ U* A U`. -/
@[simp] lemma unitaryConjStarAlgHom_apply (U : unitary (L K)) (A : L K) :
    unitaryConjStarAlgHom U A = star (↑U : L K) * A * (↑U : L K) := by
  simp [unitaryConjStarAlgHom]

-- The rotated compression identity expands a full `2 × 2` block conjugation.

end RotatedBlockCompression

end ConvexityCharacterization

end NormalCFC517

end HansenPedersen
