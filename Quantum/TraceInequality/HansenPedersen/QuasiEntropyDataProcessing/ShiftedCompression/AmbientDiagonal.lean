/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.ShiftedCompression.AmbientDiagonalBasic
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.ShiftedCompression.AmbientDiagonalOperators
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.ShiftedCompression.AmbientDiagonalInequality
import Quantum.TraceInequality.HiaiPetz.Support.MatrixSupport
-- The imported module names above are indivisible tokens longer than the style limit.
set_option linter.style.longLine false

/-!
This module preserves the original import surface after splitting `AmbientDiagonal`.
-/
