/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.VonNeumann.PartialTraceCPTP

/-!
# The partial trace over the third factor as a CPTP channel

`traceOutThird : T (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃)) (ℋ₁ ⊗[ℂ] ℋ₂)` traces out the
third tensor factor of a three-body system, and is bundled as a `CPTP`
channel.

* Definition: conjugation by the (inverse) tensor associator
  `(TensorProduct.assoc ℂ ℋ₁ ℋ₂ ℋ₃).symm` — a unitary, hence a
  single-Kraus-operator channel via `TensorProduct.assocIsometry` —
  followed by `traceOutRight` on `(ℋ₁ ⊗[ℂ] ℋ₂) ⊗[ℂ] ℋ₃`.
* Complete positivity: `isCompletelyPositive_comp` of the associator
  Kraus channel with `cp_traceOutRight`.
* Trace preservation: conjugation by a linear equivalence preserves the
  trace (`trace_conjugateEnd`), and `traceOutRight` preserves the trace
  (`trace_traceOutRight`, reduced to `trace_traceOutLeft`).

This is the associator analogue of the swap-conjugation pattern used for
`CPTP.traceOutLeft` in `PartialTraceCPTP`.
-/

namespace QuantumChannel

open QuantumState TensorProduct

universe u

section TraceConj

variable {E : Type*} {F : Type*} [Qudit E] [Qudit F]

/-- Conjugation of an endomorphism by a linear equivalence preserves the
trace. -/
private lemma trace_conjugateEnd (e : E ≃ₗ[ℂ] F) (X : L E) :
    Tr (conjugateEnd e X) = Tr X := by
  change Tr ((e : E →ₗ[ℂ] F) ∘ₗ (X ∘ₗ (e.symm : F →ₗ[ℂ] E))) = Tr X
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  have hid : ((e.symm : F →ₗ[ℂ] E) ∘ₗ (e : E →ₗ[ℂ] F)) = LinearMap.id := by
    ext x; simp
  rw [hid, LinearMap.comp_id]

end TraceConj

section TraceOutRightTP

variable {ℋ₁ : Type*} {ℋ₂ : Type*} [Qudit ℋ₁] [Qudit ℋ₂]

/-- **Trace preservation of the right partial trace**:
`Tr (traceOutRight Z) = Tr Z`. -/
lemma trace_traceOutRight (Z : L (ℋ₁ ⊗[ℂ] ℋ₂)) :
    Tr (traceOutRight (ℋ₂ := ℋ₁) (ℋ₃ := ℋ₂) Z) = Tr Z := by
  unfold traceOutRight
  rw [LinearMap.comp_apply, trace_traceOutLeft, trace_conjugateEnd]

end TraceOutRightTP

variable {ℋ₁ ℋ₂ ℋ₃ : Type u} [Qudit ℋ₁] [Qudit ℋ₂] [Qudit ℋ₃]

/-- The adjoint of the (inverse) tensor associator is the associator (the
associator is unitary, via `TensorProduct.assocIsometry`). -/
private lemma adjoint_assoc_symm_toLinearMap :
    LinearMap.adjoint
        (((TensorProduct.assoc ℂ ℋ₁ ℋ₂ ℋ₃).symm :
          (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃)) ≃ₗ[ℂ] ((ℋ₁ ⊗[ℂ] ℋ₂) ⊗[ℂ] ℋ₃)) :
          (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃)) →ₗ[ℂ] ((ℋ₁ ⊗[ℂ] ℋ₂) ⊗[ℂ] ℋ₃)) =
      ((TensorProduct.assoc ℂ ℋ₁ ℋ₂ ℋ₃ :
          ((ℋ₁ ⊗[ℂ] ℋ₂) ⊗[ℂ] ℋ₃) ≃ₗ[ℂ] (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃))) :
          ((ℋ₁ ⊗[ℂ] ℋ₂) ⊗[ℂ] ℋ₃) →ₗ[ℂ] (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃))) := by
  simpa using
    LinearIsometryEquiv.adjoint_toLinearMap_eq_symm
      (TensorProduct.assocIsometry ℂ ℋ₁ ℋ₂ ℋ₃).symm

/-- Conjugation by the (inverse) tensor associator is a single-operator Kraus
channel. -/
private theorem krausRep_conjugateEnd_assoc_symm :
    KrausRep (ℋ₁ := ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃)) (ℋ₂ := (ℋ₁ ⊗[ℂ] ℋ₂) ⊗[ℂ] ℋ₃)
      (conjugateEnd (TensorProduct.assoc ℂ ℋ₁ ℋ₂ ℋ₃).symm) (Fin 1) := by
  refine ⟨fun _ =>
    (((TensorProduct.assoc ℂ ℋ₁ ℋ₂ ℋ₃).symm :
      (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃)) ≃ₗ[ℂ] ((ℋ₁ ⊗[ℂ] ℋ₂) ⊗[ℂ] ℋ₃)) :
      (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃)) →ₗ[ℂ] ((ℋ₁ ⊗[ℂ] ℋ₂) ⊗[ℂ] ℋ₃)), fun X => ?_⟩
  rw [Fin.sum_univ_one, adjoint_assoc_symm_toLinearMap]
  rfl

/-- **The partial trace over the third factor** (linear-map carrier):
regroup `ℋ₁ ⊗ (ℋ₂ ⊗ ℋ₃)` to `(ℋ₁ ⊗ ℋ₂) ⊗ ℋ₃` by the associator, then trace
out the right factor. -/
noncomputable def traceOutThird : T (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃)) (ℋ₁ ⊗[ℂ] ℋ₂) :=
  (traceOutRight (ℋ₂ := ℋ₁ ⊗[ℂ] ℋ₂) (ℋ₃ := ℋ₃)) ∘ₗ
    conjugateEnd (TensorProduct.assoc ℂ ℋ₁ ℋ₂ ℋ₃).symm

/-- **Trace preservation of the third-factor partial trace**:
`Tr (traceOutThird X) = Tr X`. -/
lemma trace_traceOutThird (X : L (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃))) :
    Tr (traceOutThird X) = Tr X := by
  unfold traceOutThird
  rw [LinearMap.comp_apply, trace_traceOutRight, trace_conjugateEnd]

/-- **Complete positivity of the third-factor partial trace**. -/
private theorem cp_traceOutThird :
    IsCompletelyPositive
      (traceOutThird : T (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃)) (ℋ₁ ⊗[ℂ] ℋ₂)) := by
  exact isCompletelyPositive_comp
    (conjugateEnd (TensorProduct.assoc ℂ ℋ₁ ℋ₂ ℋ₃).symm)
    (traceOutRight (ℋ₂ := ℋ₁ ⊗[ℂ] ℋ₂) (ℋ₃ := ℋ₃))
    (cp_of_krausRep _ krausRep_conjugateEnd_assoc_symm)
    (cp_traceOutRight (stdOrthonormalBasis ℂ ℋ₃))

/-- **The third-factor partial trace as a CPTP channel**
`CPTP (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃)) (ℋ₁ ⊗[ℂ] ℋ₂)`. -/
noncomputable def CPTP.traceOutThird (ℋ₁ ℋ₂ ℋ₃ : Type u)
    [Qudit ℋ₁] [Qudit ℋ₂] [Qudit ℋ₃] :
    CPTP (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃)) (ℋ₁ ⊗[ℂ] ℋ₂) := by
  let Ψ : CompletelyPositiveMap
      (L (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃))) (L (ℋ₁ ⊗[ℂ] ℋ₂)) :=
    { (QuantumChannel.traceOutThird :
        T (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃)) (ℋ₁ ⊗[ℂ] ℋ₂)) with
      map_cstarMatrix_nonneg' := by
        intro k M hM
        exact (isCompletelyPositive_iff_cstarMatrix_nonneg
          (QuantumChannel.traceOutThird :
            T (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃)) (ℋ₁ ⊗[ℂ] ℋ₂))).mp
          (cp_traceOutThird (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) (ℋ₃ := ℋ₃)) k M hM }
  exact
    { Ψ with
      trace_map := by
        intro ρ
        exact (trace_traceOutThird ρ).symm }

/-- Action of the CPTP-bundled third-factor partial trace. -/
@[simp] lemma CPTP.traceOutThird_toFun
    (ρ : L (ℋ₁ ⊗[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃))) :
    (CPTP.traceOutThird ℋ₁ ℋ₂ ℋ₃).toFun ρ =
      QuantumChannel.traceOutThird ρ :=
  rfl

end QuantumChannel
