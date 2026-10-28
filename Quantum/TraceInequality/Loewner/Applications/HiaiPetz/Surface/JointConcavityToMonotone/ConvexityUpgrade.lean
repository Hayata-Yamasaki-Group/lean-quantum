/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.JointConcavityToMonotone.MidpointTransport
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.JointConcavityToMonotone.ConcavityToMonotonicity
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.SharedStageCompatibility
import Quantum.QuantumEntropy.Common.RealComplexOrder

set_option linter.style.longLine false -- unbreakable long import lines

/-!
# HP62 Condition IV to I: convexity upgrade

This module contains the scalar midpoint-convexity gap, the upgrade to
all-H operator concavity, and the final wrappers for the Hiai--Petz 6.2
condition IV to condition I stage.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder FinMatrixCStar

noncomputable section

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

/--
Hansen--Pedersen [hiaiyanagi2021]: continuous all-H midpoint convexity on `(0,∞)`
upgrades to all-H operator convexity.
-/
theorem allHOperatorMidpointConvex_to_allHOperatorConvex_Ioi
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    HansenPedersen.AllHOperatorMidpointConvexOnInterval.{0} (Set.Ioi (0 : ℝ)) f →
      HansenPedersen.AllHOperatorConvexOnInterval.{0} (Set.Ioi (0 : ℝ)) f := by
  exact _root_.HiaiPetz.QuasiEntropyDataProcessing.allHOperatorConvex_of_midpointConvex f hf

/-- Operator convexity of `-f` on `(0,∞)` gives operator concavity of `f`. -/
theorem allHOperatorConvex_neg_to_allHOperatorConcave_Ioi (f : ℝ → ℝ) :
    HansenPedersen.AllHOperatorConvexOnInterval.{0}
        (Set.Ioi (0 : ℝ)) (fun x : ℝ => -f x) →
      HansenPedersen.AllHOperatorConcaveOnInterval.{0} (Set.Ioi (0 : ℝ)) f := by
  intro hconv K _ _ _ _ _ A B t hA hB hσA hσB ht0 ht1
  have h := hconv K (A := A) (B := B) (t := t) hA hB hσA hσB ht0 ht1
  simpa [HansenPedersen.cfcR, cfc_neg, smul_neg, neg_add, add_comm] using neg_le_neg h

/-! ### All-H Monotonicity Back to Matrix Condition I -/
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

private theorem conditionI_matrix_of_allHOperatorMonotone_Ioi
    (f : ℝ → ℝ)
    (hmono :
      HansenPedersen.AllHOperatorMonotoneOnInterval.{0} (Set.Ioi (0 : ℝ)) f) :
    QuasiEntropyDPI.matrixMonotoneConditionMatrix f := by
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
          ((spectrum_toEuclideanCLM A).subset.trans hσA)
          ((spectrum_toEuclideanCLM B).subset.trans hσB)
          (toEuclideanCLM_mono hAB)
      apply le_of_toEuclideanCLM_le
      rw [toEuclideanCLM_matrixCfcR, toEuclideanCLM_matrixCfcR]
      exact hpush

/-! ### HP62 Condition IV to Condition I Wrappers -/
-- Preserve the theorem-facing compatibility signature.
/--
Third legacy substep: positive all-H operator concavity on `(0,∞)` implies the
matrix form of Hiai--Petz condition (i).
-/
theorem allHOperatorConcave_to_conditionI_matrix
    (f : ℝ → ℝ) (_hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    HansenPedersen.AllHOperatorConcaveOnInterval.{0} (Set.Ioi (0 : ℝ)) f →
      QuasiEntropyDPI.matrixMonotoneConditionMatrix f := by
  intro hconc
  exact conditionI_matrix_of_allHOperatorMonotone_Ioi f
    (allHOperatorMonotone_of_concave_pos_Ioi f hpos hconc)

/--
The theorem-facing version of the legacy implication
`ConditionIV -> ConditionI_matrix`.
-/
theorem quasiEntropy_conditionIV_to_conditionI_matrix
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    QuasiEntropyDPI.quasiEntropyJointConcavityCondition f →
      QuasiEntropyDPI.matrixMonotoneConditionMatrix f := by
  exact matrixMonotone_of_jointConcavity f hf hpos

end

end Quantum.TraceInequality.Loewner.HiaiPetz
