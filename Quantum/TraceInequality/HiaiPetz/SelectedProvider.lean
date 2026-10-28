import Quantum.TraceInequality.HansenPedersen.HansenPedersenAdapter

namespace ProofNet

/-- The unique entry point that selects the Hiai--Petz 6.2 provider. It currently selects the
Hansen--Pedersen provider (`hansenPedersenProvider`). -/
def selectedProvider : Provider := hansenPedersenProvider

/-- Canonical strict-output Hiai--Petz 6.2 equivalences from the selected provider. -/
theorem strictDPIEquivalences {f : ℝ → ℝ} : StrictDPIEquivalences f :=
  selectedProvider.strictDPIEquivalences

/-- Canonical general-output Hiai--Petz 6.2 equivalences from the selected provider. -/
theorem outputSupportDPIEquivalences {f : ℝ → ℝ} : OutputSupportDPIEquivalences f :=
  selectedProvider.outputSupportDPIEquivalences

end ProofNet
