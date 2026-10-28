/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.OperatorCFC
import Quantum.QuantumEntropy.Common.TraceRe
import Quantum.QuantumEntropy.RenyiDPI.Petz.HiaiPetz.ChannelAdapter
import Quantum.TraceInequality.TraceFunctionMonotonicity.TraceMonotonicity.StrictlyPositive
import Quantum.TraceInequality.HiaiPetz.ConditionICompatCore
import Quantum.TraceInequality.TraceFunctionMonotonicity.Petz.CarlenKernel.AdjointHelpers
import Quantum.TraceInequality.TraceFunctionMonotonicity.PowerTrace

open scoped Quantum.TraceInequality.Loewner

/-!
# Operator transfer for Hiai--Petz trace powers

This module transports the matrix trace-power data-processing inequality to
the operator model used by Umegaki relative entropy.
-/

namespace UmegakiDPI

open QuantumState QuantumChannel QuantumEntropy
open SandwichedRenyiRelativeEntropy
open scoped QuantumEntropy
open scoped ComplexOrder MatrixOrder

noncomputable section

universe u

variable {ℋ : Type u} [Qudit ℋ]

/-- Align the matrix star-ring projection selected by `CFC.rpow` with the
canonical matrix instance. -/
private noncomputable local instance matrixStarRingOfRing
    {n : Type*} [Fintype n] [DecidableEq n] :
    @StarRing (Matrix n n ℂ)
      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring _
        (@NonAssocRing.toNonUnitalNonAssocRing _
          (@Ring.toNonAssocRing _ Matrix.instRing))) :=
  Matrix.instStarRing

/-- Align the matrix nonnegative-spectrum projection selected by `CFC.rpow`. -/
private local instance matrixNonnegSpectrumClassOfRing
    {n : Type*} [Fintype n] [DecidableEq n] :
    @NonnegSpectrumClass ℝ (Matrix n n ℂ) Real.instCommSemiring Real.partialOrder
      (@Ring.toNonUnitalRing _ Matrix.instRing)
      inferInstance
      (@Algebra.toModule ℝ _ Real.instCommSemiring (@Ring.toSemiring _ Matrix.instRing)
        inferInstance) :=
  Matrix.instNonnegSpectrumClass

/-- Matrix powers in the Hiai--Petz model agree with operator `CFC.rpow`. -/
theorem matrixPower_eq_toMatrixOrthonormal_cfc_rpow
    {X : L ℋ} (hX : X ∈ pdSetLM (ℋ := ℋ)) (p : ℝ) :
    HiaiPetz.matrixPower p
        (LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ ℋ) X) =
      LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ ℋ)
        (((CFC.rpow X.toContinuousLinearMap p : B ℋ) : L ℋ)) := by
  let b := stdOrthonormalBasis ℂ ℋ
  let A := LinearMap.toMatrixOrthonormal b X
  have hA : Matrix.PosDef A := by
    exact (pdSetLM_iff_toMatrixOrthonormal_posDef X).1 hX
  have hA_selfAdjoint : IsSelfAdjoint A :=
    Matrix.isHermitian_iff_isSelfAdjoint.mp hA.isHermitian
  have hX_strict : IsStrictlyPositive X.toContinuousLinearMap := by
    apply (GeneralizedPerspectiveFunction.pdSet_membership_certificate _).1
    exact hX
  have hX_positive : X.toContinuousLinearMap.IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).1 hX_strict.nonneg
  calc
    HiaiPetz.matrixPower p A =
        HansenPedersen.matrixCfcR (HiaiPetz.powerFn p) A := rfl
    _ = cfc (HiaiPetz.powerFn p) A :=
      Quantum.TraceInequality.Loewner.HiaiPetz.conditionICompat_matrixCfcR_eq_cfc
        A hA_selfAdjoint
    _ = CFC.rpow A p := by
      rw [CFC.rpow_eq_pow,
        CFC.rpow_eq_cfc_real (a := A) (y := p) (ha := hA.posSemidef.nonneg)]
      rfl
    _ = LinearMap.toMatrixOrthonormal b
        (((CFC.rpow X.toContinuousLinearMap p : B ℋ) : L ℋ)) := by
      simpa [A, b] using
        (toMatrixOrthonormal_rpow_pd b X.toContinuousLinearMap
          hX_positive hX_strict.isUnit p).symm

/-- Strict trace-power data processing for a CPTP channel. -/
theorem tracePower_le_of_cptp
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦] (E : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ))
    (hσ : σ ∈ pdSetLM (ℋ := ℋ))
    (hEρ : E.toFun ρ ∈ pdSetLM (ℋ := 𝒦))
    (hEσ : E.toFun σ ∈ pdSetLM (ℋ := 𝒦))
    {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    realTrace
        (CFC.rpow ρ.toContinuousLinearMap p *
          CFC.rpow σ.toContinuousLinearMap (1 - p)) ≤
      realTrace
        (CFC.rpow (E.toFun ρ).toContinuousLinearMap p *
          CFC.rpow (E.toFun σ).toContinuousLinearMap (1 - p)) := by
  let bℋ := stdOrthonormalBasis ℂ ℋ
  let b𝒦 := stdOrthonormalBasis ℂ 𝒦
  let Φ := hsMapOfCPTP E
  let A := LinearMap.toMatrixOrthonormal bℋ ρ
  let Bmat := LinearMap.toMatrixOrthonormal bℋ σ
  have hA : Matrix.PosDef A := by
    exact (pdSetLM_iff_toMatrixOrthonormal_posDef ρ).1 hρ
  have hB : Matrix.PosDef Bmat := by
    exact (pdSetLM_iff_toMatrixOrthonormal_posDef σ).1 hσ
  have hΦA : Matrix.PosDef (Φ A) := by
    have hEρmat := (pdSetLM_iff_toMatrixOrthonormal_posDef (E.toFun ρ)).1 hEρ
    simpa [Φ, A, bℋ, b𝒦] using hEρmat
  have hΦ1 : Matrix.PosDef
      (Φ (1 : HiaiPetz.Mₙ (Module.finrank ℂ ℋ))) :=
    posMap_one_posDef_of_posDef_image Φ
      (hsMapOfCPTP_isPositiveMap E) hA hΦA
  have hpIcc : p ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_of_lt hp.1, le_of_lt hp.2⟩
  have hdirect :=
    HiaiPetz.TraceMonotonicity.directTracePowerStrictlyPositive
      Φ (p := p) (A := A) (B := Bmat)
        (X := (1 : HiaiPetz.Mₙ (Module.finrank ℂ 𝒦)))
      hpIcc (hsMapOfCPTP_isPositiveMap E)
      (hsMapOfCPTP_tracePreserving E)
      (hsMapOfCPTP_hsAdjointSchwarz E) hA hB hΦ1
  have hadjOne :
      HiaiPetz.hsAdjoint Φ (1 : HiaiPetz.Mₙ (Module.finrank ℂ 𝒦)) =
        (1 : HiaiPetz.Mₙ (Module.finrank ℂ ℋ)) :=
    Quantum.TraceInequality.Loewner.HiaiPetz.isUnitalMap_hsAdjoint_of_tracePreserving
      (hsMapOfCPTP_tracePreserving E)
  have hmatrix :
      (Matrix.trace
          (HiaiPetz.matrixPower p A *
            HiaiPetz.matrixPower (1 - p) Bmat)).re ≤
        (Matrix.trace
          (HiaiPetz.matrixPower p (Φ A) *
            HiaiPetz.matrixPower (1 - p) (Φ Bmat))).re := by
    simpa [HiaiPetz.liebTracePower, HiaiPetz.powerTrace, hadjOne] using hdirect
  have hsource :
      realTrace
          (CFC.rpow ρ.toContinuousLinearMap p *
            CFC.rpow σ.toContinuousLinearMap (1 - p)) =
        (Matrix.trace
          (HiaiPetz.matrixPower p A *
            HiaiPetz.matrixPower (1 - p) Bmat)).re := by
    rw [realTrace, tr_eq_matrix_trace_orthonormal bℋ]
    change
      (Matrix.trace
        (LinearMap.toMatrixOrthonormal bℋ
          (((CFC.rpow ρ.toContinuousLinearMap p : B ℋ) : L ℋ) *
            ((CFC.rpow σ.toContinuousLinearMap (1 - p) : B ℋ) : L ℋ)))).re = _
    rw [map_mul,
      ← matrixPower_eq_toMatrixOrthonormal_cfc_rpow hρ p,
      ← matrixPower_eq_toMatrixOrthonormal_cfc_rpow hσ (1 - p)]
  have htarget :
      realTrace
          (CFC.rpow (E.toFun ρ).toContinuousLinearMap p *
            CFC.rpow (E.toFun σ).toContinuousLinearMap (1 - p)) =
        (Matrix.trace
          (HiaiPetz.matrixPower p (Φ A) *
            HiaiPetz.matrixPower (1 - p) (Φ Bmat))).re := by
    rw [realTrace, tr_eq_matrix_trace_orthonormal b𝒦]
    change
      (Matrix.trace
        (LinearMap.toMatrixOrthonormal b𝒦
          (((CFC.rpow (E.toFun ρ).toContinuousLinearMap p : B 𝒦) : L 𝒦) *
            ((CFC.rpow (E.toFun σ).toContinuousLinearMap (1 - p) : B 𝒦) : L 𝒦)))).re = _
    rw [map_mul,
      ← matrixPower_eq_toMatrixOrthonormal_cfc_rpow hEρ p,
      ← matrixPower_eq_toMatrixOrthonormal_cfc_rpow hEσ (1 - p),
      hsMapOfCPTP_toMatrixOrthonormal,
      hsMapOfCPTP_toMatrixOrthonormal]
  calc
    realTrace
        (CFC.rpow ρ.toContinuousLinearMap p *
          CFC.rpow σ.toContinuousLinearMap (1 - p)) =
      (Matrix.trace
        (HiaiPetz.matrixPower p A *
          HiaiPetz.matrixPower (1 - p) Bmat)).re := hsource
    _ ≤ (Matrix.trace
        (HiaiPetz.matrixPower p (Φ A) *
          HiaiPetz.matrixPower (1 - p) (Φ Bmat))).re := hmatrix
    _ = realTrace
        (CFC.rpow (E.toFun ρ).toContinuousLinearMap p *
          CFC.rpow (E.toFun σ).toContinuousLinearMap (1 - p)) := htarget.symm

end

end UmegakiDPI
