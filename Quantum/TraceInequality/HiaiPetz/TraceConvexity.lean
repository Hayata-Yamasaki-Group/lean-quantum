/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.TraceConvexity.AndoConvexity
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.Main
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.OutputSupport.Reduction
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.SharedStages

/-!
# Hiai--Petz Theorem 6.4 trace convexity consequences

This compatibility surface aggregates the content-named submodules
`LiebConcavity`, `ThreeVariableConvexity`, and `AndoConvexity`, which package the
Lieb concavity, three-variable convexity, and Ando convexity consequences of
Hiai--Petz Theorem 6.4.
-/
