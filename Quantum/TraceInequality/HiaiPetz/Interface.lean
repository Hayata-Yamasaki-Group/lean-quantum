/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Interface.Strict
import Quantum.TraceInequality.HiaiPetz.Interface.OutputSupport
import Mathlib.LinearAlgebra.Lagrange
import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
import Quantum.TraceInequality.HiaiPetz.HilbertSchmidt.QuadraticForm
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.Transport

/-!
# Provider-neutral Hiai--Petz 6.2 interface façade

This canonical root façade re-exports the strict-output and output-support
interface modules.  It intentionally declares no constants, so proof adapters
can share the complete former surface without pulling readiness proofs into the
interface closure.
-/
