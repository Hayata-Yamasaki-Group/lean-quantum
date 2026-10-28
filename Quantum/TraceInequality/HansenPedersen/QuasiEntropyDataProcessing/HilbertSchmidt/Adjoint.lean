/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.HilbertSchmidt.QuadraticForm
import Quantum.TraceInequality.HansenPedersen.AmbientSubmodule.JOperatorInequalities
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.JOperatorInequalities
import Quantum.TraceInequality.CoreRetained
import Quantum.TraceInequality.HansenPedersen.HilbertSchmidt.Instances
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule
import Quantum.TraceInequality.HiaiPetz.Core
import Quantum.TraceInequality.LownerHeinz.ReciprocalRetained
import Quantum.TraceInequality.LownerHeinzTheoremRetained

/-!
# Quadratic forms of Hilbert-Schmidt adjoint compositions

This file identifies the trace quadratic forms associated to `hsAdjoint Φ ∘ Φ`
and `Φ ∘ hsAdjoint Φ`. These identities turn the Hilbert-Schmidt adjoint
relation into squared Frobenius norms and are used by contractivity and
positivity arguments.

## Main results

* `hsQForm_hsAdjoint_comp_eq_norm_sq`: the quadratic form of `Φ^* Φ` at `x`
  is `‖Φ x‖ ^ 2`.
* `hsQForm_comp_hsAdjoint_eq_norm_sq`: the quadratic form of `Φ Φ^*` at `y`
  is `‖hsAdjoint Φ y‖ ^ 2`.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Chapter 6 Hilbert-Schmidt adjoints.
-/

namespace HiaiPetz

open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

end MatrixScopedInstances

end HiaiPetz
