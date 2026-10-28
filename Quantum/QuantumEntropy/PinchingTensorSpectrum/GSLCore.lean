/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumMechanics.SpectralPinching.GSLCore
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Concrete matrix tensor powers

Tensor powers are concrete matrices (`matrixTensorPower`): an entry of the `n`-fold Kronecker
power is the product of the corresponding `n` one-copy entries.
-/

namespace QuantumChannel

open QuantumState
open scoped BigOperators

universe u v

noncomputable section

variable {H : Type u} [Qudit H]

/-- The concrete index type for an `n`-fold matrix Kronecker power. -/
abbrev MatrixTensorPowerIndex (ι : Type v) (n : ℕ) := Fin n → ι

/-- The concrete `n`-fold Kronecker power of a square matrix.

Its `(i,j)` entry is `∏ k, A (i k) (j k)`.  In particular this is a matrix
construction, not iteration of an endofunction. -/
def matrixTensorPower {ι : Type v} [Fintype ι]
    (A : Matrix ι ι ℂ) (n : ℕ) :
    Matrix (MatrixTensorPowerIndex ι n) (MatrixTensorPowerIndex ι n) ℂ :=
  fun i j => ∏ k : Fin n, A (i k) (j k)

end

end QuantumChannel
