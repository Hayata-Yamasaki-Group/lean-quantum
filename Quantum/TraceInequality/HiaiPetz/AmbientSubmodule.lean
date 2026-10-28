/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.Basic
import Quantum.TraceInequality.HansenPedersen.AmbientSubmodule.JOperator
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.JOperator
import Quantum.TraceInequality.HansenPedersen.AmbientSubmodule.JOperatorInequalities
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.JOperatorInequalities
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.BlockDiagonal
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.Projections
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.OrthogonalSubmodule
import Quantum.TraceInequality.CoreRetained
import Quantum.TraceInequality.HansenPedersen.HilbertSchmidt.Instances
import Quantum.TraceInequality.HiaiPetz.Core
import Quantum.TraceInequality.LownerHeinz.ReciprocalRetained
import Quantum.TraceInequality.LownerHeinzTheoremRetained

/-!
# Ambient submodule aggregate

This module preserves the original import surface after splitting
`AmbientSubmodule`.
-/
