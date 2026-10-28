/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import
  Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.StrictlyPositive.PositiveCFC
import Quantum.TraceInequality.HiaiPetz.Core.Basic
import Quantum.TraceInequality.HiaiPetz.Core.MatrixType

/-!
# Rectangular transport operator

The rectangular transport operator `rectU` conjugates a Hilbert--Schmidt map by
the positive square roots of the input and output data.  It is the building block
for reducing the strict-output standard conditions to a rectangular contraction
inequality in the `StrictlyPositive` development.
-/

namespace HiaiPetz

open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius

noncomputable section MatrixScopedInstances

/-- The rectangular transport operator `√(TA) · V · TΦ^{-1/2}`, obtained by
composing `V : HSMap (l+1) (k+1)` with the positive square root `hsSqrtPos TA`
on the output side and the positive inverse square root `hsInvSqrtPos TΦ` on the
input side. -/
noncomputable abbrev rectU
    {k l : ℕ} (V : HSMap (Nat.succ l) (Nat.succ k))
    (TA : HSOp (Nat.succ k)) (TΦ : HSOp (Nat.succ l)) :
    HSMap (Nat.succ l) (Nat.succ k) :=
  (hsSqrtPos TA).comp (V.comp (hsInvSqrtPos TΦ))

end MatrixScopedInstances

end HiaiPetz
