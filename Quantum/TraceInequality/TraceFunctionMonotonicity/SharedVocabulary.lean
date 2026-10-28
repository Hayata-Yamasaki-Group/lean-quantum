/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.HilbertSchmidt.QuadraticForm
import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

namespace ProofNet

open HiaiPetz Matrix Unitary
open scoped CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section

@[reducible, local instance]
private noncomputable def instSharedCStarAlgebraEuclideanCLM {n : ℕ} :
    CStarAlgebra (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  inferInstance

@[reducible, local instance]
private noncomputable def instSharedCFCRealEuclideanCLM {n : ℕ} :
    ContinuousFunctionalCalculus ℝ
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) IsSelfAdjoint :=
  inferInstance

@[reducible, local instance]
private noncomputable def instSharedAlgebraRealEuclideanCLM {n : ℕ} :
    Algebra ℝ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  inferInstance

@[reducible, local instance]
private noncomputable def instSharedAddRightMonoEuclideanCLM {n : ℕ} :
    AddRightMono (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  inferInstance

@[reducible, local instance]
private noncomputable def instSharedAlgebraRealMatrix {n : ℕ} : Algebra ℝ (Mₙ n) :=
  inferInstance

@[reducible, local instance]
private noncomputable def instSharedAddRightMonoMatrix {n : ℕ} : AddRightMono (Mₙ n) :=
  inferInstance

/-- `Matrix.toEuclideanCLM` preserves self-adjointness. -/
private lemma isSelfAdjoint_toEuclideanCLM {n : ℕ} {A : Mₙ n} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A) := by
  have h1 : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (star A) =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A :=
    congrArg _ hA
  simpa [map_star] using h1

/-- `Matrix.toEuclideanCLM` preserves the real spectrum. -/
private lemma spectrum_toEuclideanCLM {n : ℕ} (A : Mₙ n) :
    spectrum ℝ (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A) = spectrum ℝ A := by
  simpa using
    AlgEquiv.spectrum_eq ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).restrictScalars ℝ) A

/-- `Matrix.toEuclideanCLM` is monotone for the Loewner orders. -/
private lemma toEuclideanCLM_mono {n : ℕ} {A B : Mₙ n} (hAB : A ≤ B) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A ≤
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B := by
  have hBA_psd : (B - A).PosSemidef := by
    exact (Matrix.nonneg_iff_posSemidef).mp (sub_nonneg.mpr hAB)
  have hφBA_pos :
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (B - A) :
          EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).IsPositive := by
    simpa [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
      ((Matrix.isPositive_toEuclideanLin_iff (A := B - A)).2 hBA_psd)
  have hφBA_nonneg : 0 ≤ Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (B - A) := by
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).2 hφBA_pos
  exact sub_nonneg.mp (by simpa [map_sub] using hφBA_nonneg)

/-- The Loewner order on matrices is reflected by `Matrix.toEuclideanCLM`. -/
private lemma le_of_toEuclideanCLM_le {n : ℕ} {X Y : Mₙ n}
    (h : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X ≤
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) Y) :
    X ≤ Y := by
  have hpos :
      ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) (Y - X) :
          EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).IsPositive := by
    rw [map_sub]
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).1 (sub_nonneg.mpr h)
  have hTpos : (Matrix.toEuclideanLin (Y - X)).IsPositive := by
    refine (LinearMap.isPositive_toContinuousLinearMap_iff _).1 ?_
    change ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) (Y - X) :
        EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).IsPositive
    exact hpos
  exact sub_nonneg.mp ((Matrix.nonneg_iff_posSemidef).2
    ((Matrix.isPositive_toEuclideanLin_iff (A := Y - X)).1 hTpos))

/-- `Matrix.toEuclideanCLM` intertwines the matrix real CFC with the operator real CFC. -/
private lemma toEuclideanCLM_matrixCfcR {n : ℕ} (f : ℝ → ℝ) (A : Mₙ n) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (HansenPedersen.matrixCfcR f A) =
      HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A) := by
  change
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm
          (HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f
            (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A))) =
      HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A)
  simp

/-- Restrict all-Hilbert-space operator monotonicity to the finite matrix model.

This is representation transport, not a Hiai--Petz 6.2 implication. -/
theorem matrixMonotoneCondition_of_allHOperatorMonotoneOnIoi
    {f : ℝ → ℝ}
    (hmono : QuasiEntropyDataProcessing.AllHOperatorMonotoneOnIoi f) :
    QuasiEntropyDataProcessing.MatrixMonotoneCondition f := by
  intro n A B hA hB hσA hσB hAB
  cases n with
  | zero =>
      exact le_of_eq (Subsingleton.elim _ _)
  | succ k =>
      have hpush :
          HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin (k + 1))) f
              (Matrix.toEuclideanCLM (n := Fin (k + 1)) (𝕜 := ℂ) A) ≤
            HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin (k + 1))) f
              (Matrix.toEuclideanCLM (n := Fin (k + 1)) (𝕜 := ℂ) B) :=
        hmono (EuclideanSpace ℂ (Fin (k + 1)))
          (isSelfAdjoint_toEuclideanCLM hA) (isSelfAdjoint_toEuclideanCLM hB)
          (by rw [spectrum_toEuclideanCLM]; exact hσA)
          (by rw [spectrum_toEuclideanCLM]; exact hσB)
          (toEuclideanCLM_mono hAB)
      apply le_of_toEuclideanCLM_le
      rw [toEuclideanCLM_matrixCfcR, toEuclideanCLM_matrixCfcR]
      exact hpush

end

end ProofNet
