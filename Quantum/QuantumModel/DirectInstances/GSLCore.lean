/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.OperationalInstances.GSLCore
import Quantum.QuantumModel.SupportCompression.GSLCore
import Quantum.OperationalProbabilistic.Framework.LosslessConditioning.GSLCore
import Quantum.OperationalProbabilistic.Framework.ExactCompression.GSLCore
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Direct finite-dimensional quantum-model interfaces

A transformation whose composition with the trace effect is an event is a channel
(`isChannel_of_isEvent_comp_traceEffect`), and the quantum model has rescaled preparations
(`instRescaledPreparationTheory`).
-/

noncomputable section

namespace QuantumModel

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TensorProduct
open scoped ComplexOrder

variable {A B C D : Sys}

/-- A CP map that preserves the trace effect is CPTP. -/
theorem isChannel_of_isEvent_comp_traceEffect
    {f : A ⟶ B} (hf : IsEvent f)
    (hpres : f ≫ traceEffect B = traceEffect A) :
    IsChannel f := by
  obtain ⟨K, hKmap⟩ := exists_krausFamily_of_isEvent hf
  refine ⟨hf, K, hKmap, ?_⟩
  apply operator_eq_of_trace_comp_eq
  intro X
  rw [← trace_krausFamily_map K, hKmap]
  have hpresX := congrArg
    (fun h : A ⟶ tensorUnitSystem ↦ HPHom.toRawSuperoperator h X) hpres
  change HPHom.toRawSuperoperator (traceEffect B)
      (HPHom.toRawSuperoperator f X) =
    HPHom.toRawSuperoperator (traceEffect A) X at hpresX
  rw [traceEffect_apply, traceEffect_apply] at hpresX
  exact operatorUnitEquiv.injective hpresX

/-- A positive-trace subnormalized density operator rescales by its trace to a
trace-one density operator, and the original state is its positive scalar multiple. -/
instance instRescaledPreparationTheory :
    OPT.RescaledPreparationTheory Sys where
  rescaled_deterministic_preparation := by
    intro A ρ hρ hprob
    change IsTransformation ρ at hρ
    let p : ℝ := OPT.prob (Sys := Sys) (OPT.detEffect (Sys := Sys) A) ρ
    change 0 < p at hprob
    obtain ⟨K, hKmap, _hKle⟩ := hρ.2
    letI := K.fintypeIndex
    letI := K.decidableEqIndex
    have hKnonneg : 0 ≤ K.normalization :=
      krausFamily_normalization_nonneg K
    have htrace_nonneg : (0 : ℂ) ≤ QuantumState.Tr K.normalization :=
      ((LinearMap.nonneg_iff_isPositive _).mp hKnonneg).trace_nonneg
    have htrace_im : (QuantumState.Tr K.normalization).im = 0 :=
      (Complex.nonneg_iff.mp htrace_nonneg).2.symm
    have hp_re : p = (QuantumState.Tr K.normalization).re := by
      change
        (QuantumState.Tr
          (HPHom.toRawSuperoperator (traceEffect A)
            (HPHom.toRawSuperoperator ρ
              (LinearMap.id : Operator tensorUnitSystem)))).re = _
      rw [traceEffect_apply, trace_operatorUnitEquiv]
      rw [← hKmap, trace_krausFamily_map]
      simp
    have hp_trace : (p : ℂ) = QuantumState.Tr K.normalization := by
      apply Complex.ext
      · exact hp_re
      · simpa using htrace_im.symm
    have hKnorm :
        K.normalization = (p : ℂ) • (LinearMap.id : Operator tensorUnitSystem) := by
      calc
        K.normalization = operatorUnitEquiv (QuantumState.Tr K.normalization) :=
          (operatorUnitEquiv_trace K.normalization).symm
        _ = operatorUnitEquiv (p : ℂ) := by rw [← hp_trace]
        _ = (p : ℂ) • (LinearMap.id : Operator tensorUnitSystem) :=
          operatorUnitEquiv_eq_smul_id (p : ℂ)
    have hp_inv_nonneg : 0 ≤ p⁻¹ := inv_nonneg.mpr hprob.le
    let L : KrausFamily tensorUnitSystem A := K.scale p⁻¹
    have hLmap : L.map = p⁻¹ • ρ := by
      dsimp [L]
      rw [KrausFamily.scale_map K hp_inv_nonneg, hKmap]
    have hLnorm : L.normalization = LinearMap.id := by
      dsimp [L]
      rw [KrausFamily.scale_normalization K hp_inv_nonneg, hKnorm]
      simp [smul_smul, hprob.ne']
    refine ⟨p⁻¹ • ρ, ?_, ?_⟩
    · change IsChannel (p⁻¹ • ρ)
      exact ⟨isEvent_nonneg_smul hp_inv_nonneg hρ.1, L, hLmap, hLnorm⟩
    · change ρ = p • (p⁻¹ • ρ)
      rw [smul_smul]
      simp [hprob.ne']

end QuantumModel
