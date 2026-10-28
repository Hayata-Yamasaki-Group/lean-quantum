/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Interface
import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.OutputSupport.BookSurface
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.DirectToConcavity
import Quantum.TraceInequality.HiaiPetzTheorem.QuasiEntropyDataProcessing.JointToMonotone

/-!
# Hansen--Pedersen provider for the neutral Hiai--Petz 6.2 interface
-/

namespace ProofNet

open HiaiPetz.QuasiEntropyDataProcessing

/-- The Hansen--Pedersen route (H1) supplies the common strict-output package. -/
theorem strictDPIEquivalences_via_hansenPedersen
    {f : ℝ → ℝ} : StrictDPIEquivalences f := by
  intro hf hpos
  rcases strictlyPositive_characterizations (f := f) hf hpos with
    ⟨hIiffII, hIIiffIII, hIIIiffIV, _hIVtoImat, hImatToI⟩
  refine {
    matrixMonotone_iff_strictInverseDPI := ?_
    strictInverseDPI_iff_strictDirectDPI := hIIiffIII
    strictDirectDPI_iff_jointConcavity :=
      ⟨jointConcavity_of_strictDirectDPI f hf, hIIIiffIV.mpr⟩
    matrixMonotone_of_jointConcavity :=
      HiaiPetz.QuasiEntropyDataProcessing.matrixMonotone_of_jointConcavity f hf hpos }
  constructor
  · intro hImat
    exact hIiffII.mp (hImatToI hImat)
  · intro hII
    exact HiaiPetz.QuasiEntropyDataProcessing.matrixMonotone_of_jointConcavity f hf hpos
      (jointConcavity_of_strictDirectDPI f hf (hIIiffIII.mp hII))

/-- The Hansen--Pedersen route (H1) supplies the common general-output package. -/
theorem outputSupportDPIEquivalences_via_hansenPedersen
    {f : ℝ → ℝ} : OutputSupportDPIEquivalences f := by
  intro hf hpos
  rcases outputSupport_characterizations (f := f) hf hpos with
    ⟨hItoIII, hIIiffIII, hIIItoIV, _hIVtoImat, hImatToI⟩
  exact {
    outputSupportDirectDPI_of_matrixMonotone := fun hImat ↦ hItoIII (hImatToI hImat)
    outputSupportInverseDPI_iff_outputSupportDirectDPI := hIIiffIII
    jointConcavity_of_outputSupportDirectDPI := hIIItoIV
    matrixMonotone_of_jointConcavity :=
      HiaiPetz.QuasiEntropyDataProcessing.matrixMonotone_of_jointConcavity f hf hpos }

/-- Both packages of the Hansen--Pedersen route (H1), bundled as an explicit provider value. -/
def hansenPedersenProvider : Provider where
  route := .hansenPedersen
  strictDPIEquivalences := strictDPIEquivalences_via_hansenPedersen
  outputSupportDPIEquivalences := outputSupportDPIEquivalences_via_hansenPedersen

end ProofNet
