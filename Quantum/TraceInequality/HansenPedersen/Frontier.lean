/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.Frontier.TraceMonotonicity
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

/-! # Hiai--Petz formalization-frontier aggregate -/
