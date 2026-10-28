/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.ResidualEquivalence
import Quantum.TraceInequality.HiaiPetz.Support.MatrixSupport

/-!
# Strict-output inverse/direct equivalence for Hiai--Petz quasi-entropy

This compatibility surface aggregates the content-named submodules
`StandardCompression`, `ShiftedCompressionInequality`, and `ResidualEquivalence`,
which together establish the equivalence between the inverse and direct forms of
the strict-output quasi-entropy inequality.  The old `ShiftedAmbient` module is
retained as a compatibility import.
-/
