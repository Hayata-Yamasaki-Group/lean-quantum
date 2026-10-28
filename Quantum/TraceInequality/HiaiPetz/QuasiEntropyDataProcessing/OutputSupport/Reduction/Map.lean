/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Model.MatrixCorner
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Reduction.Basic

/-!
# Output-support reduced map

This lightweight module owns only the reduced-map definition needed by the
provider-neutral output-support interface.  Readiness and proof payload remain
in `Reduction.ReducedMap`.
-/

namespace HiaiPetz

/-- The reduced Hilbert–Schmidt map on the output support: `Φ` with its codomain transported
through the fixed orthonormal matrix realization `outputSupportMatrixCornerModel Φ` of the
support corner. -/
noncomputable def outputSupportReducedMap {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) :
    HSMap n (outputSupportMatrixCornerModel Φ).dim :=
  (outputSupportMatrixCornerModel Φ).transportMap Φ (map_mem_outputCorner Φ hPos)

/-- Short API for the reduced Hilbert--Schmidt map on the chosen output-support realization. -/
noncomputable abbrev outputSupportReducedHSMap {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) :
    HSMap n (outputSupportMatrixCornerModel Φ).dim :=
  outputSupportReducedMap Φ hPos

end HiaiPetz
