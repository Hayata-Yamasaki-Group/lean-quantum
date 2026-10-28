/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiOrder.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivConcrete.GSLCore
import Quantum.OperationalProbabilistic.Framework.OrderedConeMaxRelativeEntropy.GSLCore
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Quantum.OperationalProbabilistic.Framework.Core.GSLCore
import Quantum.OperationalProbabilistic.Framework.MeasurementStatistics.GSLCore

open CategoryTheory Set
open scoped MonoidalCategory ENNReal NNReal

/-!
# Binary calibration for relative-entropy laws

The type `ERealStateDivergence` of extended-real state divergences, the base-two negative
logarithm `binaryNegLog2` of binary exponent probabilities, and the uniqueness of monotone
additive functions on `ℝ≥0`, which identifies a binary calibration with `binaryNegLog2`
(`binaryCalibration_eq_negLog2`).  This is the analytic step of Lemma 1.1 in M. Tomamichel,
*Quantum Relative Entropy: An Axiomatic Approach*, QMath Masterclass notes, Copenhagen,
August 2022.
-/

namespace OPT

noncomputable section

universe u v w

section Operational

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]
  [Preadditive Sys] [CategoryTheory.Linear ℝ Sys]
  [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
  [CausalOperationalProbabilisticTheory Sys]

/-- A system-polymorphic extended-real divergence on normalized OPT states.

The codomain is the extended real line used in Tomamichel 2022, Eq. (1.7), so
support-mismatch cases can be represented by `top`. -/
abbrev ERealStateDivergence :=
  {A : Sys} →
    NormalizedState (Sys := Sys) A →
      NormalizedState (Sys := Sys) A → EReal

end Operational

end

end OPT
