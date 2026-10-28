/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCoreGeneralizedStein
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCore
import Quantum.QuantumMechanics.BridgeCertificates
import Quantum.QuantumEntropy.HaarUnitaryLM.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiUmegakiKWExtra.GSLCore
import Quantum.QuantumEntropy.VonNeumann.Basic
import Quantum.QuantumEntropy.VonNeumann.PartialTraceCPTP
import Quantum.QuantumEntropy.VonNeumann.PartialTraceThirdCPTP

/-! `trace_conjugateEnd`: conjugation by a linear equivalence preserves the trace. -/

namespace QuantumChannel

open QuantumState TensorProduct

universe u

section TraceConj

variable {E : Type*} {F : Type*} [Qudit E] [Qudit F]

/-- Conjugation of an endomorphism by a linear equivalence preserves the
trace. -/
lemma trace_conjugateEnd (e : E ≃ₗ[ℂ] F) (X : L E) :
    Tr (conjugateEnd e X) = Tr X := by
  change Tr ((e : E →ₗ[ℂ] F) ∘ₗ (X ∘ₗ (e.symm : F →ₗ[ℂ] E))) = Tr X
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  have hid : ((e.symm : F →ₗ[ℂ] E) ∘ₗ (e : E →ₗ[ℂ] F)) = LinearMap.id := by
    ext x; simp
  rw [hid, LinearMap.comp_id]

end TraceConj

variable {ℋ₁ ℋ₂ ℋ₃ : Type u} [Qudit ℋ₁] [Qudit ℋ₂] [Qudit ℋ₃]

end QuantumChannel
