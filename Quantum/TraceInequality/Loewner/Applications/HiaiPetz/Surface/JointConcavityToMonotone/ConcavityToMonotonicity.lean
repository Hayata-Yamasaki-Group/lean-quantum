/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetzTheorem.Basic
import Quantum.TraceInequality.HiaiPetz.Basic
import Quantum.TraceInequality.HiaiPetzTheorem.QuasiEntropyDataProcessing.JointToMonotone

/-!
# Positive operator concavity implies operator monotonicity

This file supplies the direct Hiai--Petz surface construction from positive
operator concavity on `(0, ∞)` to operator monotonicity there.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open Set Filter
open scoped Topology CStarAlgebra
open HansenPedersen

/--
A positive operator-concave function on the positive half-line is operator monotone there.

For `A ≤ B`, the proof interpolates through
`Cₜ = A + (1 - t)⁻¹ • (B - A)` and lets `t ↑ 1`.
-/
theorem allHOperatorMonotone_of_concave_pos_Ioi
    (f : ℝ → ℝ)
    (hpos : ∀ x : ℝ, x ∈ Ioi (0 : ℝ) → 0 < f x)
    (hconc : AllHOperatorConcaveOnInterval.{0} (Ioi (0 : ℝ)) f) :
    AllHOperatorMonotoneOnInterval.{0} (Ioi (0 : ℝ)) f := by
  exact _root_.HiaiPetz.QuasiEntropyDataProcessing.allHOperatorMonotone_of_positiveConcave
    f hpos hconc

end Quantum.TraceInequality.Loewner.HiaiPetz
