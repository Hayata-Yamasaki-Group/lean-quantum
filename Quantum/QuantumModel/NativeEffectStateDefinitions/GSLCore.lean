/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.OperationalInstances.GSLCore
import Quantum.QuantumModel.SupportCompression.GSLCore
import Quantum.OperationalProbabilistic.Framework.EffectsAndPreparations.GSLCore

/-!
# Native quantum effect, Born probability, and normalized-state definitions
-/

noncomputable section

namespace QuantumModel
namespace NativeNoCloning

open QuantumState

/-- A single POVM element, written only as the matrix interval `0 ≤ E ≤ I`. -/
def POVMElement {A : Sys} (E : Operator A) : Prop :=
  0 ≤ E ∧ E ≤ LinearMap.id

/-- Born probability of one POVM element on a density matrix. -/
def bornProbability {A : Sys} (E : Operator A) (rho : DensityMatrix A) : ℝ :=
  (Tr (E.comp rho.operator)).re

end NativeNoCloning

namespace DensityMatrix

open QuantumState

/-- The density operator carried by a normalized categorical preparation. -/
def ofNormalizedState {A : Sys}
    (rho : OPT.State (Sys := Sys) A)
    (hrho : OPT.IsNormalizedState (Sys := Sys) rho) : DensityMatrix A where
  operator := HPHom.toRawSuperoperator rho
    (LinearMap.id : Operator tensorUnitSystem)
  nonneg := QuantumChannel.completelyPositive_to_positiveMap
    (HPHom.toRawSuperoperator rho) hrho.1.1
    (LinearMap.id : Operator tensorUnitSystem)
    ((LinearMap.nonneg_iff_isPositive _).mpr LinearMap.isPositive_id)
  trace_one := by
    have hprob := hrho.2
    change (Tr
      (HPHom.toRawSuperoperator (traceEffect A)
        (HPHom.toRawSuperoperator rho
          (LinearMap.id : Operator tensorUnitSystem)))).re = 1 at hprob
    rw [traceEffect_apply, trace_operatorUnitEquiv] at hprob
    let Y := HPHom.toRawSuperoperator rho
      (LinearMap.id : Operator tensorUnitSystem)
    have hYnonneg : (0 : Operator A) ≤ Y := by
      exact QuantumChannel.completelyPositive_to_positiveMap
        (HPHom.toRawSuperoperator rho) hrho.1.1
        (LinearMap.id : Operator tensorUnitSystem)
        ((LinearMap.nonneg_iff_isPositive _).mpr LinearMap.isPositive_id)
    have him : (Tr Y).im = 0 :=
      (Complex.nonneg_iff.mp
        ((LinearMap.nonneg_iff_isPositive _).mp hYnonneg).trace_nonneg).2.symm
    apply Complex.ext
    · simpa [Y] using hprob
    · simpa [Y] using him

end DensityMatrix
end QuantumModel
