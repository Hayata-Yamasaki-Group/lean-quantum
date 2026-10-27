/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Algebra.Module.LinearMap

/-!
# Operator notation

This file provides the abbreviations `QuantumState.L ℋ` for complex-linear endomorphisms
`ℋ →ₗ[ℂ] ℋ` and `QuantumState.B ℋ` for continuous complex-linear endomorphisms
`ℋ →L[ℂ] ℋ`.

It deliberately imports only what is needed to state these two abbreviations, so that files
can use the notation without importing the C*-algebra and completely positive map
infrastructure pulled in by `Quantum.QuantumMechanics.QuantumState`.
-/

namespace QuantumState

universe u

abbrev L (ℋ : Type u) [AddCommGroup ℋ] [Module ℂ ℋ] : Type u :=
  ℋ →ₗ[ℂ] ℋ

abbrev B (ℋ : Type u) [AddCommGroup ℋ] [Module ℂ ℋ] [TopologicalSpace ℋ] : Type u :=
  ℋ →L[ℂ] ℋ

end QuantumState
