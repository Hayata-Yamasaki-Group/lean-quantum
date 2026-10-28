/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.LoewnerEntry
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.ConditionIToLoewner
import Quantum.TraceInequality.TraceFunctionMonotonicity.Petz.LiebRuskai
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.PositiveInverse
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenKernel
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.BoundarySupport
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.Regularization
import Quantum.TraceInequality.Loewner.Applications.ResponseFunctions.CauerBasic
import Quantum.TraceInequality.Loewner.Applications.ResponseFunctions.CauerRepresentation
import Quantum.Analysis.CStar.FiniteDimensionalStructure.PrimitivesRetained
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.SharedStages
import Quantum.TraceInequality.JensenOperatorInequalityIImpIVRetained
import Quantum.TraceInequality.Loewner.SharedDownstreamCompat.ConditionICompatCore

/-!
# Loewner theorem applications aggregate

This module imports the theorem-facing Hiai--Petz application surfaces built on
the Loewner core, together with the Cauer response-function applications.
`Quantum.lean` imports this aggregate.
-/
