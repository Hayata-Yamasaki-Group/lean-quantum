/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.Transport
import Quantum.TraceInequality.HiaiPetz.MatrixPosDef
import Quantum.TraceInequality.HiaiPetz.Support.MatrixSupport
import Mathlib.LinearAlgebra.Lagrange

/-!
# Power trace expressions

Matrix powers and trace expressions used in the Hiai--Petz power-specialized
quasi-entropy arguments.  The file provides both the ordinary real-functional-
calculus powers and the book-facing support convention at zero eigenvalues,
then relates them to spectral sums, support projections, `J`-quadratic forms,
and semidefinite regularization limits.

## Main results

* `supportMatrixPower_eq_matrixCfcR_supportPowerCoeff_nonneg`: the
  support-convention power is real CFC with the support coefficient on
  nonnegative matrices.
* `supportLiebTracePower_eq_liebTracePower_of_nonneg_Ioo`: on the open
  parameter interval, support and ordinary trace powers agree for semidefinite
  inputs.
* `matrixPower_tendsto_of_tendsto_nonneg`: nonnegative matrix powers are
  continuous along filters for nonnegative exponents.

## References

* Hiai, Theorem 6.3.
-/

namespace HiaiPetz

open scoped ComplexOrder MatrixOrder

noncomputable section MatrixScopedInstances

variable {n : ℕ}

/-- Scalar power function used in Hiai--Petz Theorem 6.3. -/
noncomputable def powerFn (p : ℝ) : ℝ → ℝ :=
  fun x : ℝ => x ^ p

/-- Matrix power through the existing finite-dimensional real functional calculus. -/
noncomputable def matrixPower {n : ℕ} (p : ℝ) (A : Mₙ n) : Mₙ n :=
  HansenPedersen.matrixCfcR (powerFn p) A

/-- Trace expression `Tr X^* A^r X B^s`, read through the matrix functional calculus. -/
noncomputable def powerTrace (r s : ℝ) (A B X : Mₙ n) : ℝ :=
  Complex.re
    (Matrix.trace
      (Matrix.conjTranspose X * matrixPower r A * X * matrixPower s B))

/-- The expression `Tr X^* A^p X B^(1-p)` appearing in Theorem 6.3(1) and (3). -/
noncomputable def liebTracePower (p : ℝ) (A B X : Mₙ n) : ℝ :=
  powerTrace p (1 - p) A B X

/-- The `jOperator` quadratic form for the power function, used as the strict-output
intermediate form of Hiai-Petz Theorem 6.3. -/
noncomputable def jPowerTrace (p : ℝ) (A B X : Mₙ n) : ℝ :=
  Complex.re
    (Matrix.trace
      ((Matrix.conjTranspose X * hsCfcR (powerFn p) (jArg A B) X) * B))

end MatrixScopedInstances

end HiaiPetz
