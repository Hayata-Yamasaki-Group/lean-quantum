/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.POVMObservationBridge.GSLCore
import Quantum.QuantumModel.NativeFidelity.GSLCoreRetained

/-!
# Operator square roots for the Fuchs--Caves argument

Positive square roots of density operators, and the operator root fidelity as the trace
norm of a product of positive square roots
(`operatorRootFidelity_eq_traceNorm_positiveSqrt`).
References: KNI, arXiv:0910.0994, § Fidelity in GPT (TeX lines 246--263);
Fuchs, quant-ph/9601020; Fuchs--Caves, quant-ph/9604001, Eq. (7).
-/

noncomputable section

namespace QuantumModel.NativeFidelity.FuchsCavesInternal

/-- The positive square root used internally by the regular Fuchs--Caves
construction (KNI source TeX lines 246--263). -/
def positiveSqrt {A : Sys} (X : Operator A) : Operator A :=
  CFC.sqrt X

/-- Positivity of the square-root factor used at KNI source TeX lines
246--263. -/
theorem positiveSqrt_nonneg {A : Sys} (X : Operator A) :
    0 ≤ positiveSqrt X := by
  exact CFC.sqrt_nonneg X

/-- Squaring the positive factor used at KNI source TeX lines 246--263
recovers the original operator. -/
theorem positiveSqrt_mul_self {A : Sys} (X : Operator A) (hX : 0 ≤ X) :
    positiveSqrt X * positiveSqrt X = X := by
  exact CFC.sqrt_mul_sqrt_self X hX

/-- Boundary form of the operator fidelity appearing in the Fuchs--Caves
identity, KNI source TeX lines 246--263. -/
theorem operatorRootFidelity_eq_traceNorm_positiveSqrt {A : Sys}
    (rho sigma : DensityMatrix A) :
    operatorRootFidelity rho sigma =
      NativeTraceDistance.traceNorm
        (positiveSqrt rho.operator * positiveSqrt sigma.operator) := by
  rfl

end QuantumModel.NativeFidelity.FuchsCavesInternal
