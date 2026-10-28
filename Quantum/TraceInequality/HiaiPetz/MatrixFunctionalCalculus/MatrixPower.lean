/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.MatrixPower.Basic
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.MatrixPower.SupportPower
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.MatrixPower.Composition
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.MatrixPower.Order
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule

/-!
# Matrix-power functional calculus

This module is the public import aggregator for the Hiai-Petz matrix-power
development. It re-exports the basic transport lemmas, positivity of
support-convention powers, exponent-composition identities, and order results
for ordinary and support-sensitive matrix real powers.

## Main results

* `matrixPower_comp_nonneg`, `supportMatrixPower_comp_pos_nonneg`, and the
  positive-definite exponent laws from `MatrixPower.Composition`.
* `supportMatrixPower_nonneg` from `MatrixPower.SupportPower`.
* `matrixPower_concave_nonneg`, `matrixPower_monotone_nonneg`, and
  `matrixPower_antitone_neg_Icc_posDef` from `MatrixPower.Order`.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Chapter 6 matrix functional calculus.
-/
