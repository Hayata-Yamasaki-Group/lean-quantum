/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.Channel.Representations
import Mathlib.Analysis.InnerProductSpace.Trace
import Quantum.QuantumMechanics.Channel.ChoiKraus

/-!
Choi expansion, injectivity, Kraus recovery, and the right partial trace as a Kraus map.
-/

namespace QuantumChannel

open QuantumState
open TensorProduct

universe u v w

section RepresentationsOfChannels

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

lemma tensorRightSlice_tmul
    {κ : Type*} [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (i : κ) (x : E) (y : F) :
    tensorRightSlice (E := E) (F := F) b i (x ⊗ₜ[ℂ] y) =
      b.toBasis.coord i y • x := by
  simp [tensorRightSlice]

end RepresentationsOfChannels

end QuantumChannel
