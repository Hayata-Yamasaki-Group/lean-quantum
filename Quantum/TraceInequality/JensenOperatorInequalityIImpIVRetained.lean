/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LiebAndo.BlockDiagonal
import Quantum.TraceInequality.LiebAndo.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheoremRetained
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Quantum.TraceInequality.LiebAndo.JensenOperatorInequalityIImpIV

namespace JensenOperatorInequality

universe u

open LownerHeinzTheorem

section Theorem252

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

-- Cached here once: repeating this search in every statement that mentions `CFC.sqrt`
-- on `(HSum ℋ →L[ℂ] HSum ℋ)` exceeds the default instance-search budget.
attribute [local instance] instAlgebraRealContinuousLinearMapComplexIdHSum
attribute [local instance] instNormedSpaceRealContinuousLinearMapComplexIdHSum
attribute [local instance] instModuleRealContinuousLinearMapComplexIdHSum

-- CStarAlgebra → NonnegSpectrumClass chain through WithLp is too deep for default heartbeats.
attribute [local instance] instNonnegSpectrumClassRealContinuousLinearMapComplexIdHSum

/--
Source: Fumio Hiai, "Matrix Analysis: Matrix Monotone Functions, Matrix Means, and
Majorization", Interdisciplinary Information Sciences 16 (2010), 139–248, Theorem 2.5.2.

On a nontrivial space only the zero function satisfies the hypothesis on `f` (see
`LownerHeinzCore.OperatorConvex.eq_zero_of_nontrivial` in `LownerHeinz/GlobalDegeneracy.lean`), so
this statement has no nonzero instances. For the standard statement, see the localized version
`JensenOperatorInequality.jensenContraction_of_opConvexIciAll`. -/
theorem jensen_of_opConvexAllNonposZero {f : ℝ → ℝ} (hf : OperatorConvexAllNonposAtZero.{u} f) :
    JensenContractionCondition (ℋ := ℋ) f := by
  rcases hf with ⟨hconvAll, hf0⟩
  intro A X hA hAs hX
  letI : Nontrivial (HSum ℋ →L[ℂ] HSum ℋ) := nontrivial_hsumL (ℋ := ℋ)
  have hconv₂ : OperatorConvex (ℋ := HSum ℋ) f := hconvAll (K := HSum ℋ)
  have hcont : ContinuousOn f (Set.Ici (0 : ℝ)) :=
    (operatorConvex_continuousOn_univ (ℋ := HSum ℋ) hconv₂).mono (Set.subset_univ _)
  refine cfcR_compression_le_of_midpoint (ℋ := ℋ) hcont hf0 ?_ hA hAs hX
  intro B₁ B₂ _ _ _ _
  have hhalf : (1 - (2⁻¹ : ℝ)) = (2⁻¹ : ℝ) := by norm_num
  simpa [hhalf] using
    (hconv₂ (A := B₁) (B := B₂) (t := (1 / 2 : ℝ)) (by positivity) (by norm_num))

end Theorem252

end JensenOperatorInequality
