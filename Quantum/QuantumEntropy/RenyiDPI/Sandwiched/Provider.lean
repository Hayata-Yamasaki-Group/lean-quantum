/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.SelectedProvider
import Quantum.QuantumEntropy.RenyiDPI.Interface
import Quantum.QuantumMechanics.QuantumState

/-! # Sandwiched Rényi data processing, tensor additivity and continuity

Each theorem projects only the corresponding field of the selected Sandwiched value.
-/

namespace RenyiDPI

universe u v

/-- Sandwiched data processing for nonnegative inputs. -/
theorem sandwichedMonotoneOnNonNeg : SandwichedMonotoneOnNonNeg.{u} :=
  selectedSandwichedProvider.{u, u}.monotoneOnNonNeg

/-- Tensor additivity for density pairs. -/
theorem sandwichedTensorAdditivity : SandwichedTensorAdditiveOnDensity.{u, v} :=
  selectedSandwichedProvider.{u, v}.tensorAdditivity

/-- Right continuity of the real sandwiched divergence at order one. -/
theorem sandwichedLimitAtOne : SandwichedLimitAtOneOnPosDef.{u} :=
  selectedSandwichedProvider.{u, u}.limitAtOne

end RenyiDPI
