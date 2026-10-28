/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.OperatorBridge
import Quantum.QuantumEntropy.Common.RealComplexOrder

open scoped Quantum.TraceInequality.Loewner

/-! Opt-in canonical functional calculus for finite-dimensional operators. -/

namespace QuantumEntropy

open QuantumState

/-- Restore the canonical operator CFC instance after importing matrix
compatibility layers whose instance projections are not definitionally aligned. -/
noncomputable scoped instance operatorContinuousFunctionalCalculus
    {H : Type*} [Qudit H] :
    ContinuousFunctionalCalculus ℝ (B H) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

end QuantumEntropy
