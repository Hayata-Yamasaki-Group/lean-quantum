/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.Umegaki.GSLCoreUmegaki
import Quantum.QuantumEntropy.Common.Umegaki.GSLCore
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificatesGeneralizedStein
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificatesStrongSubadditivity
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.PositiveDefiniteCertificates
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.TensorCFC
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.YoungInequality
import Quantum.QuantumMechanics.Channel.BasicGeneralizedStein
import Quantum.QuantumMechanics.Channel.ChoiKrausGeneralizedStein
import Quantum.QuantumMechanics.QuantumChannel
import Quantum.TraceInequality.GeneralizedPerspectiveFunctionRetained
import Quantum.TraceInequality.HansenPedersen.LownerHeinzTheorem
import Quantum.TraceInequality.LiebAndo.AndoConvexity.LiebTrace.Bridge
import Quantum.TraceInequality.LiebAndo.LiebTrace.Bridge
import Quantum.TraceInequality.LownerHeinz.ReciprocalRetained

/-! Compatibility import for the route-neutral Umegaki definitions.
All declarations retain their original namespace and definitions. -/
