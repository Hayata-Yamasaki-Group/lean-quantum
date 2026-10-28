/- 
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Core
import Quantum.TraceInequality.HansenPedersen.MatrixPosDef
import Quantum.TraceInequality.HiaiPetz.MatrixPosDef
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.Transport
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.MatrixPower
import Quantum.TraceInequality.HiaiPetz.Support
import Quantum.TraceInequality.HiaiPetz.Support.MatrixSupport
import Quantum.TraceInequality.HiaiPetz.Support.OutputSupport
import Quantum.TraceInequality.HiaiPetz.Support.Corner
import Quantum.TraceInequality.HiaiPetz.BlockSumBase
import Quantum.TraceInequality.HansenPedersen.MainEquivalence
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.OutputSupport.BookSurface
import Quantum.TraceInequality.HansenPedersen.HansenPedersen.Examples
import Quantum.TraceInequality.HansenPedersen.HansenPedersen.Frontier
import Quantum.TraceInequality.HansenPedersen.HansenPedersen.Frontier.IntegralRepresentation
import Quantum.TraceInequality.HansenPedersen.HansenPedersen.Frontier.LaterConsequences
import Quantum.TraceInequality.HansenPedersen.HansenPedersen.IntegralRepresentation
import Quantum.TraceInequality.HiaiPetz.TraceMonotonicity
import Quantum.TraceInequality.HiaiPetz.TraceMonotonicityApprox
import Quantum.TraceInequality.HiaiPetz.TraceConvexity
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
# Hansen--Pedersen route (H1)

Umbrella module aggregating the Hiai--Petz trace-inequality development supplied
by the Hansen--Pedersen route (H1), which uses Jensen's operator inequality.  Declarations
keep their namespaces; this module only collects the files of this route.

Primary provenance: Hiai, *Matrix analysis and its applications*,
SGC Library 200, Saiensu-sha, 2025, Section 6.1, together with Hiai--Yanagi,
Chapter 5.1.
-/
