/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.GeneralizedPerspectiveFunction
import Quantum.QuantumMechanics.QuantumState
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.LinearAlgebra.Lagrange

namespace LiebAndoTrace

universe u

open QuantumState
open GeneralizedPerspectiveFunction
open Module.End Polynomial

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [FiniteDimensional ℂ ℋ] [Nontrivial ℋ]

/-- The real part of the finite-dimensional trace on bounded operators. -/
noncomputable def traceRe (T : B ℋ) : ℝ :=
  Complex.re (LinearMap.trace ℂ ℋ (T : L ℋ))

/-- Trace functional `Re Tr (A ^ s K* B ^ (1 - s) K)` appearing in Lieb's concavity theorem
(the real part of the trace). -/
noncomputable def liebTraceMap (s : ℝ) (K : (ℋ →L[ℂ] ℋ)) (A B : (ℋ →L[ℂ] ℋ)) : ℝ :=
  traceRe (ℋ := ℋ) (A ^ s * star K * B ^ (1 - s) * K)

end LiebAndoTrace
