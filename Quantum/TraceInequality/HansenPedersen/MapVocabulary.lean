/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HansenPedersen.MatrixPosDef
import Quantum.TraceInequality.HiaiPetz.MatrixPosDef
import Quantum.TraceInequality.HansenPedersen.Core.Basic

/-!
Provider-independent map-hypothesis vocabulary shared by Hiai--Petz consumers.
-/

namespace HiaiPetz

open scoped MatrixOrder
open scoped ComplexOrder
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

/-- A positive trace-preserving map whose Hilbert--Schmidt adjoint satisfies Schwarz. -/
structure SchwarzTracePreservingMap {n m : ℕ} (Φ : HSMap n m) : Prop where
  positiveMap : IsPositiveMap Φ
  tracePreserving : TracePreserving Φ
  adjointSchwarz : HSAdjointSchwarz Φ

/-- A strict-output map: a Schwarz trace-preserving map with positive-definite output unit. -/
structure StrictlyPositiveSchwarzTracePreservingMap {n m : ℕ} (Φ : HSMap n m) : Prop
    extends SchwarzTracePreservingMap Φ where
  outputPosDef : Matrix.PosDef (Φ (1 : Mₙ n))

end HiaiPetz

namespace HiaiPetz

open scoped MatrixOrder
open scoped ComplexOrder
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

/-- The identity map is positive.
Sanity lemma: the identity channel preserves matrix positivity. -/
theorem MapVocabulary.isPositiveMap_id (n : ℕ) :
    IsPositiveMap (ContinuousLinearMap.id ℂ (Mₙ n) : HSMap n n) := by
  intro A hA
  simpa using hA

/-- The identity map preserves trace.
Sanity lemma: the identity channel preserves trace. -/
theorem MapVocabulary.tracePreserving_id (n : ℕ) :
    TracePreserving (ContinuousLinearMap.id ℂ (Mₙ n) : HSMap n n) := by
  intro A
  rfl

/-- The identity map satisfies the Hilbert-Schmidt adjoint Schwarz condition.
Sanity lemma: the identity channel satisfies Schwarz with equality. -/
theorem MapVocabulary.hsAdjointSchwarz_id (n : ℕ) :
    HSAdjointSchwarz (ContinuousLinearMap.id ℂ (Mₙ n) : HSMap n n) := by
  intro X
  rw [hsAdjoint_id]
  exact le_rfl

namespace StrictlyPositiveSchwarzTracePreservingMap

/-- The identity map is a strict-output Schwarz trace-preserving map.
Sanity lemma: the identity channel is strictly positive on the unit. -/
theorem id (n : ℕ) :
    StrictlyPositiveSchwarzTracePreservingMap
      (ContinuousLinearMap.id ℂ (Mₙ n) : HSMap n n) where
  toSchwarzTracePreservingMap := {
    positiveMap := HiaiPetz.MapVocabulary.isPositiveMap_id n
    tracePreserving := HiaiPetz.MapVocabulary.tracePreserving_id n
    adjointSchwarz := HiaiPetz.MapVocabulary.hsAdjointSchwarz_id n
  }
  outputPosDef := by
    simpa using Matrix.PosDef.one (R := ℂ) (n := Fin n)

end StrictlyPositiveSchwarzTracePreservingMap

end HiaiPetz
