/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LiebAndo.JensenOperatorInequalityIImpIV
import Quantum.TraceInequality.JensenOperatorInequalityIImpIVRetained
import Quantum.TraceInequality.LiebAndo.JensenOperatorInequality

namespace JensenOperatorInequality

universe u

open LownerHeinzTheorem

section Theorem252

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

attribute [local instance] instAlgebraRealContinuousLinearMapComplexIdHSum_1
attribute [local instance] instNormedSpaceRealContinuousLinearMapComplexIdHSum_1
attribute [local instance] instModuleRealContinuousLinearMapComplexIdHSum_1

-- CStarAlgebra → NonnegSpectrumClass chain through WithLp is too deep for default heartbeats.
attribute [local instance] instNonnegSpectrumClassRealContinuousLinearMapComplexIdHSum_1

/-- Uniform consequence of Theorem 2.5.2: `(i) → (v)` via `(iv)`.

Source: arXiv:2607.05492v1, §3.
Source: Fumio Hiai, "Matrix Analysis: Matrix Monotone Functions, Matrix Means, and
Majorization", Interdisciplinary Information Sciences 16 (2010), 139–248, Theorem 2.5.2.

On a nontrivial space only the zero function satisfies the hypothesis on `f` (see
`LownerHeinzCore.OperatorConvex.eq_zero_of_nontrivial` in `LownerHeinz/GlobalDegeneracy.lean`), so
this statement has no nonzero instances. For the standard statement, see the localized version
`JensenOperatorInequality.jensenColumn_of_opConvexIciAll`. -/
theorem jensenColumn_of_opConvexAllNonposZero {f : ℝ → ℝ}
    (hf : OperatorConvexAllNonposAtZero.{u} f) :
    JensenContractiveColumnCondition (ℋ := ℋ) f := by
  have hconv : OperatorConvex (ℋ := ℋ) f := by
    exact hf.1
  have hcont : ContinuousOn f Set.univ :=
    operatorConvex_continuousOn_univ (ℋ := ℋ) hconv
  refine jensenColumn_of_jensenContractionAll (ℋ := ℋ) ?_ hcont
  intro K _ _ _ _
  exact jensen_of_opConvexAllNonposZero (ℋ := K) (f := f) hf

end Theorem252

end JensenOperatorInequality
