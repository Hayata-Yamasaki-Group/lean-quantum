/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.TraceMonotonicity.Basic
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.HilbertSchmidt.Adjoint
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.Main
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.OutputSupport.Reduction
import
  Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagOrthogonalTransport.OrthogonalConjugation
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagProjection
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagSpectralTransportRetained
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule
import Quantum.TraceInequality.HiaiPetz.HilbertSchmidt.Order
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.SharedStages
import Quantum.TraceInequality.LownerHeinz.ReciprocalRetained

/-!
# Frontier statements for positive-definite trace-power monotonicity

This module contains statement-only propositions that are intentionally absent
from the completed Hiai--Petz chapter aggregate.  They use the literal `matrixPower`
formulation.  The results proved in this development use support powers instead: see
`HiaiPetz.TraceMonotonicity.supportTracePowerMonotonicity` for the original output space, and
`Quantum.TraceInequality.HiaiPetz.TraceMonotonicity.StrictlyPositive` for the case `Φ(1) > 0`.
-/

namespace HiaiPetz

namespace Frontier

open scoped ComplexOrder MatrixOrder

noncomputable section

/-- Formalization-frontier statement for Hiai Theorem 6.3(1) in the
positive-definite regime.  This is only a statement and currently has no proof term. -/
def DirectTracePowerPosDefStatement : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B : Mₙ n} {X : Mₙ m},
    p ∈ Set.Icc (0 : ℝ) 1 →
    IsPositiveMap Φ →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    liebTracePower p (Φ A) (Φ B) X ≥
      liebTracePower p A B ((hsAdjoint Φ) X)

/-- Formalization-frontier statement for Hiai Theorem 6.3(2) in the
positive-definite regime.  This is only a statement and currently has no proof term. -/
def InverseTracePowerPosDefStatement : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B X : Mₙ n},
    p ∈ Set.Icc (0 : ℝ) 1 →
    IsPositiveMap Φ →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    inverseTracePower p (Φ A) (Φ B) (Φ X) ≤
      inverseTracePower p A B X

/-- Formalization-frontier statement for Hiai Theorem 6.3(3), including the
multiplicative-domain side condition.  This is only a statement and currently has no proof term. -/
def MultiplicativeDomainTracePowerPosDefStatement : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B : Mₙ n} {X : Mₙ m},
    (p ∈ Set.Icc (-1 : ℝ) 0 ∨ p ∈ Set.Icc (1 : ℝ) 2) →
    IsPositiveMap Φ →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    TraceMonotonicity.InAdjointMultiplicativeDomain Φ X →
    liebTracePower p (Φ A) (Φ B) X ≤
      liebTracePower p A B ((hsAdjoint Φ) X)

/-- Aggregate formalization-frontier statement for the three positive-definite
parts of Hiai Theorem 6.3.  This is only a statement and currently has no proof term. -/
def TracePowerMonotonicityPosDefStatement : Prop :=
  DirectTracePowerPosDefStatement ∧
    InverseTracePowerPosDefStatement ∧
      MultiplicativeDomainTracePowerPosDefStatement


end

end Frontier

end HiaiPetz
