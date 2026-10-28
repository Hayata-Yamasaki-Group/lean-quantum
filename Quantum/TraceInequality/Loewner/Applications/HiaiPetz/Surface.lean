/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.Basic
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.ConditionICompat
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.QuasiEntropyDPIAlignment
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.QuasiEntropyBlockSum
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.JointConcavityToMonotone
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.StrictOutputDPIViaLoewner
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.OutputSupportDPI
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.PaperSupport
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.SharedStages
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle

/-!
# Hiai--Petz theorem statement interface

This module is the public entry point for the minimal Hiai--Petz statements used
by the Loewner-route proof.  The actual definitions live under
`Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface`.

This interface contains the strict-output direct/inverse inequalities and the
theorem-facing HP62 bridge surface used to compare the Loewner route with the
existing Hiai--Petz proof route.
-/
