/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.GourQuantumThompsonDistance.GSLCore
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Quantum.QuantumMechanics.DensityOperator.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiRelativeEntropy.GSLCore
import Quantum.OperationalProbabilistic.Framework.OrderedConeMaxRelativeEntropy.GSLCore
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Data.Sum.Interval
import Quantum.OperationalProbabilistic.Framework.OrderedConeMaxRelativeEntropyDensity.GSLCore
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Bases
import Mathlib.Topology.Sequences
import Quantum.OperationalProbabilistic.Framework.QuantumRelativeEntropyLaws.GSLCoreRetained
import Quantum.OperationalProbabilistic.Framework.TestingRegion.GSLCore
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificatesGeneralizedStein
import Quantum.QuantumEntropy.SandwichedRenyi.Internal.BridgeCertificates
import Quantum.QuantumEntropy.SandwichedRenyiBase.MaxRelativeEntropy.Monotonicity
import Quantum.QuantumEntropy.SandwichedRenyiRelativeEntropy
import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneCore
import Quantum.QuantumEntropy.UmegakiDPI.ViaPetz.FromRenyi.GSLCore
import Quantum.QuantumMechanics.Channel.ChoiKrausGeneralizedStein
import Quantum.QuantumMechanics.QuantumChannel
import Quantum.TraceInequality.GeneralizedPerspectiveFunctionRetained
import Quantum.TraceInequality.HansenPedersen.LownerHeinzTheorem
import Quantum.TraceInequality.LiebTrace.MonotonicityRetained
import Quantum.TraceInequality.LownerHeinz.ReciprocalRetained

open Filter Set
open scoped ENNReal Topology ComplexOrder

/-!
# Semicontinuity for Gour's quantum relative entropy: generated equations

This module keeps only the generated equation lemmas of `suppLE` that the public development
uses; the semicontinuity statements of the original module are not included.
-/

namespace OPT

noncomputable section

universe u

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy

end

end OPT
