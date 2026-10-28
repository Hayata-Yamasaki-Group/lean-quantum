/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.TraceMonotonicity.Basic
import Quantum.TraceInequality.TraceFunctionMonotonicity.TraceMonotonicity.StrictlyPositive
import Quantum.TraceInequality.HiaiPetz.TraceMonotonicity.StrictlyPositiveRetained
import Quantum.TraceInequality.HiaiPetz.TraceMonotonicity.Semidefinite
import Quantum.TraceInequality.HiaiPetz.TraceMonotonicity.SupportPower
import Quantum.TraceInequality.HiaiPetz.TraceMonotonicityApprox.SupportTracePower
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.Main
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.OutputSupport.Reduction
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.SharedStages

/-!
# Trace monotonicity aggregate

This module preserves the original import surface after splitting
`TraceMonotonicity` and exports the completed support trace-power theorem.
-/
