/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Petz.Provider
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.Provider
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificatesGeneralizedStein
import Quantum.QuantumEntropy.Common.TensorDensitySupport.GSLCoreGeneralizedStein
import Quantum.QuantumEntropy.Common.TraceReGeneralizedStein
import Quantum.QuantumEntropy.SandwichedRenyi.Internal.BridgeCertificates
import Quantum.QuantumEntropy.SandwichedRenyiRelativeEntropy
import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneCore
import Quantum.QuantumEntropy.UmegakiDPI.ViaSandwiched.AlphaOne
import Quantum.QuantumMechanics.Channel.ChoiKrausGeneralizedStein
import Quantum.QuantumMechanics.QuantumChannel
import Quantum.TraceInequality.GeneralizedPerspectiveFunctionRetained
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
import Quantum.TraceInequality.HiaiPetz.TraceMonotonicity.StrictlyPositiveRetained
import Quantum.TraceInequality.LiebTrace.MonotonicityRetained
import Quantum.TraceInequality.Loewner.RealComplexOrder
import Quantum.TraceInequality.LownerHeinz.ReciprocalRetained

/-! # Consumer façade for both independently selected Rényi sides

Umegaki adapters import the relevant side-specific `Provider` module.
This root only re-exports the sides; it defines no combined provider value.
-/
