/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import
Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.BoundarySupport.SupportInfrastructure
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.BoundarySupport.PaperSupportSpecialization
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.SharedStages
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.JointConcavityToMonotone

set_option linter.style.longLine false

/-!
# Carlen 2022 Theorem 1.46 boundary-support stages

This module re-exports the split boundary-support infrastructure and
paper-support specialization stages for Carlen 2022, Theorem 1.46.
-/
