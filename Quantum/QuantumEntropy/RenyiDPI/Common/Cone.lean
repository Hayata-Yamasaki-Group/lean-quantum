/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.Common.RealComplexOrder
import Quantum.QuantumMechanics.OperatorInstances
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCore
import Quantum.QuantumMechanics.QuantumState
import Mathlib.Algebra.Central.End
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Topology.Algebra.Star.Unitary

open scoped Quantum.TraceInequality.Loewner

open QuantumState QuantumChannel
open scoped ComplexOrder Topology TensorProduct RenyiDPI.Sym
universe u

namespace RenyiDPI

theorem nonnegCone_convex :
∀ {H : Type u} [Qudit H] [Nontrivial H],
  Convex ℝ {A : L H | 0 ≤ A} := by
  intro H _ _ A hA B hB c d hc hd _hcd
  simp only [Set.mem_setOf_eq] at hA hB ⊢
  exact add_nonneg (smul_nonneg hc hA) (smul_nonneg hd hB)

theorem nonnegCone_isClosed :
∀ {H : Type u} [Qudit H] [Nontrivial H],
  IsClosed {A : L H | 0 ≤ A} := by
  intro H _ _
  have hcontinuous : Continuous (fun A : L H ↦ A.toContinuousLinearMap) :=
    QuantumChannel.linear_isometry_equiv.continuous
  have heq : {A : L H | (0 : L H) ≤ A} =
      (fun A : L H ↦ A.toContinuousLinearMap) ⁻¹' Set.Ici 0 := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici]
    rw [LinearMap.nonneg_iff_isPositive,
      ContinuousLinearMap.nonneg_iff_isPositive,
      LinearMap.isPositive_toContinuousLinearMap_iff]
  rw [heq]
  exact isClosed_Ici.preimage hcontinuous

end RenyiDPI
