/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.Skeleton.GSLCore
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

/-!
# Dependency-minimal native trace-norm core

The trace norm is the real trace of the absolute value of an operator and
is nonnegative.

Source: Tomamichel, arXiv:1504.00233v5, §3.1.1, Definition 3.2 and
Eqs. (3.2)--(3.3). The only difference from this formalization is that the trace of the positive
operator `|X|` is written as `(Tr |X|).re` so that it is real-valued. Finite dimensionality agrees
with the restriction in §3.1 of the primary source, and since this is an operator norm without a
normalization condition for states, there is no difference in the treatment of subnormalization.
There are no other differences.
-/

noncomputable section

namespace QuantumModel

open CategoryTheory
open QuantumState

namespace NativeTraceDistance

/-- The trace norm `Tr |X|` of a finite-dimensional operator.

Source: Tomamichel, arXiv:1504.00233v5, §3.1.1, Definition 3.2 and
Eqs. (3.2)--(3.3). The only differences from this formalization are representational: `|X|` is
written as `CFC.abs X`, and the real part of the trace is returned. Finite dimensionality agrees
with the primary source, as does the absence of a subnormalization condition for states.
There are no other differences. -/
def traceNorm {A : Sys} (X : Operator A) : ℝ :=
  (Tr (CFC.abs X)).re

/-- The finite-dimensional trace norm is nonnegative.

Source: Tomamichel, arXiv:1504.00233v5, positive-definiteness in Definition 3.1 and
§3.1.1, Definition 3.2. The only difference from this formalization is the representation via the
real part of the trace. Finite dimensionality agrees with the primary source, and no
subnormalization condition for states is involved. There are no other differences. -/
theorem traceNorm_nonneg {A : Sys} (X : Operator A) : 0 ≤ traceNorm X := by
  unfold traceNorm
  exact (Complex.nonneg_iff.mp
    (((LinearMap.nonneg_iff_isPositive _).mp
      (CFC.abs_nonneg X)).trace_nonneg)).1

end NativeTraceDistance
end QuantumModel
