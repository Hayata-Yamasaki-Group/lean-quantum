/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle
import Quantum.Analysis.CStar.FiniteDimensionalStructure.PrimitivesRetained
import Quantum.TraceInequality.HansenPedersen.Reduction.ReducedMap
import
  Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagOrthogonalTransport.OrthogonalConjugation
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagProjection
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagSpectralTransportRetained
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule
import Quantum.TraceInequality.JensenOperatorInequalityIImpIVRetained
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI
import Quantum.TraceInequality.Loewner.SharedDownstreamCompat.ConditionICompatCore

/-!
# Carlen kernel bridge statements

This module contains two auxiliary statement definitions for the Carlen fixed-kernel
bridge: that strict positivity is not automatically preserved by the Hilbert--Schmidt
adjoint of a unital two-positive map, and the (trivial) optional Moore--Penrose statement.
-/

namespace Quantum.TraceInequality.Loewner

attribute [local instance]
  HiaiPetz.instMatrixNormedAddCommGroup
  HiaiPetz.instMatrixNormedSpace
  HiaiPetz.instMatrixInnerProductSpace
  HiaiPetz.instMatrixCompleteSpace



/-- The proposition that strict positivity is not automatically preserved by the
Hilbert--Schmidt adjoint of a unital two-positive map: there are such a map `Φ` and a positive
definite `X` with `hsAdjoint Φ X` not positive definite. This is only the statement; it is not
proved in this development. -/
def HiaiPetz.carlenAdjointStrictnessNotAutomaticStatement : Prop :=
  ∃ (n m : ℕ) (Φ : HiaiPetz.HSMap n m) (X : HiaiPetz.Mₙ m),
    HiaiPetz.IsUnitalTwoPositiveMap Φ ∧
      HiaiPetz.MatrixPosDef X ∧
        ¬ HiaiPetz.MatrixPosDef (HiaiPetz.hsAdjoint Φ X)


/-- Placeholder proposition (`True`) recording that the choice of a Moore--Penrose inverse on
the support is optional. It carries no mathematical content. -/
def HiaiPetz.supportInverseMoorePenroseOptionalStatement : Prop :=
  True


end Quantum.TraceInequality.Loewner
