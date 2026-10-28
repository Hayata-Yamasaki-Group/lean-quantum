/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.QuasiEntropyBlockSum
import Quantum.TraceInequality.HansenPedersen.Basic
import Quantum.TraceInequality.HiaiPetzTheorem.Basic
import Quantum.TraceInequality.HiaiPetz.Basic
import Quantum.TraceInequality.HiaiPetz.HilbertSchmidt.QuadraticForm
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.LinearAlgebra.Lagrange
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.JointConcavityToMonotone.MidpointTransport
-- The imported module names above are indivisible tokens longer than the style limit.
set_option linter.style.longLine false

/-!
# HP62 Condition IV to I: midpoint transport

This module contains the midpoint/unit-J setup, matrix CFC transport,
trace midpoint inequality, and positive-spectrum transport for the
Hiai--Petz 6.2 condition IV to condition I stage.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder FinMatrixCStar

attribute [local instance]
  _root_.HiaiPetz.instMatrixNormedAddCommGroup
  _root_.HiaiPetz.instMatrixNormedSpace
  _root_.HiaiPetz.instMatrixInnerProductSpace
  _root_.HiaiPetz.instMatrixCompleteSpace

noncomputable section

/-! ### HP62 Midpoint and Unit J Setup -/
attribute [local instance] quasiEntropyDpiConditionIVToIHSOpCStarAlgebra

attribute [local instance] quasiEntropyDpiConditionIVToIHSOpComplexCFC

attribute [local instance] quasiEntropyDpiConditionIVToIHSOpRealCFC

attribute [local instance] quasiEntropyDpiConditionIVToIEuclideanOpCStarAlgebra

attribute [local instance] quasiEntropyDpiConditionIVToIEuclideanOpComplexCFC

attribute [local instance] quasiEntropyDpiConditionIVToIEuclideanOpRealCFC

/--
First legacy substep in `quasiEntropy_conditionIV_to_conditionI_matrix`: joint concavity of the
`J_f` quasi-entropy implies matrix midpoint concavity of `A ↦ f(A)` on
`(0,∞)`.
-/
theorem quasiEntropy_conditionIV_to_matrixMidpointConcave_Ioi
    (f : ℝ → ℝ) :
    QuasiEntropyDPI.quasiEntropyJointConcavityCondition f →
      HansenPedersen.MatrixOperatorMidpointConcaveOnInterval (Set.Ioi (0 : ℝ)) f := by
  intro hIV n A B hA hB hσA hσB
  have hA_pd : MatrixPosDef A := matrixPosDef_of_isSelfAdjoint_of_spectrum_subset_Ioi hA hσA
  have hB_pd : MatrixPosDef B := matrixPosDef_of_isSelfAdjoint_of_spectrum_subset_Ioi hB hσB
  let M :=
    HansenPedersen.matrixCfcR f ((1 / 2 : ℝ) • (A + B)) -
      (1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f A + HansenPedersen.matrixCfcR f B)
  have hmid_sa : IsSelfAdjoint ((1 / 2 : ℝ) • (A + B)) := by
    have hsa :
        IsSelfAdjoint ((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B) :=
      ((IsSelfAdjoint.all (1 / 2 : ℝ)).smul hA).add
        ((IsSelfAdjoint.all (1 / 2 : ℝ)).smul hB)
    have hsum :
        (1 / 2 : ℝ) • (A + B) = (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B := by
      ext i j
      exact smul_add (1 / 2 : ℝ) (A i j) (B i j)
    rw [hsum]
    exact hsa
  have hM_sa : IsSelfAdjoint M := by
    refine (matrixCfcR_isSelfAdjoint f hmid_sa).sub ?_
    refine ((IsSelfAdjoint.all (1 / 2 : ℝ)).smul ?_)
    exact (matrixCfcR_isSelfAdjoint f hA).add (matrixCfcR_isSelfAdjoint f hB)
  have hM_psd : M.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · simpa [Matrix.IsHermitian, IsSelfAdjoint] using hM_sa
    · intro x
      have hquad :=
        conditionIV_midpoint_unit_dotProduct f hIV (A₁ := A) (A₂ := B) (x := x)
          hA_pd hB_pd
      have hmid_eq :
          ((1 / 2 : ℝ) • A + (1 - (1 / 2 : ℝ)) • B) =
            ((1 / 2 : ℝ) • (A + B)) := by
        have hhalf : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by norm_num
        have hsmul :
            (1 / 2 : ℝ) • (A + B) = (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B := by
          ext i j
          exact smul_add (1 / 2 : ℝ) (A i j) (B i j)
        calc
          ((1 / 2 : ℝ) • A + (1 - (1 / 2 : ℝ)) • B)
              = (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B := by rw [hhalf]
          _ = (1 / 2 : ℝ) • (A + B) := hsmul.symm
      have hhalf : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by norm_num
      let a : ℝ :=
        Complex.re (dotProduct (star x) ((HansenPedersen.matrixCfcR f A).mulVec x))
      let b : ℝ :=
        Complex.re (dotProduct (star x) ((HansenPedersen.matrixCfcR f B).mulVec x))
      let c : ℝ :=
        Complex.re
          (dotProduct (star x)
            ((HansenPedersen.matrixCfcR f ((1 / 2 : ℝ) • (A + B))).mulVec x))
      have hquad' : (1 / 2 : ℝ) * a + (1 - (1 / 2 : ℝ)) * b ≤ c := by
        have hquad0 := hquad
        rw [hmid_eq] at hquad0
        simpa [a, b, c] using hquad0
      let u : ℂ :=
        dotProduct (star x) ((HansenPedersen.matrixCfcR f ((1 / 2 : ℝ) • (A + B))).mulVec x)
      let v : ℂ :=
        dotProduct (star x) ((HansenPedersen.matrixCfcR f A).mulVec x)
      let w : ℂ :=
        dotProduct (star x) ((HansenPedersen.matrixCfcR f B).mulVec x)
      have hlinVec :
          M.mulVec x =
            (HansenPedersen.matrixCfcR f ((1 / 2 : ℝ) • (A + B))).mulVec x -
              ((1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f A).mulVec x +
                (1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f B).mulVec x) := by
        have hsumVec :
            (((1 / 2 : ℝ) •
                (HansenPedersen.matrixCfcR f A + HansenPedersen.matrixCfcR f B)).mulVec x) =
              (1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f A).mulVec x +
                (1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f B).mulVec x := by
          calc
            (((1 / 2 : ℝ) •
                (HansenPedersen.matrixCfcR f A + HansenPedersen.matrixCfcR f B)).mulVec x)
                = (1 / 2 : ℝ) •
                    ((HansenPedersen.matrixCfcR f A + HansenPedersen.matrixCfcR f B).mulVec x) := by
                  exact Matrix.smul_mulVec (1 / 2 : ℝ)
                    (HansenPedersen.matrixCfcR f A + HansenPedersen.matrixCfcR f B) x
            _ = (1 / 2 : ℝ) •
                    ((HansenPedersen.matrixCfcR f A).mulVec x +
                      (HansenPedersen.matrixCfcR f B).mulVec x) := by
                  rw [Matrix.add_mulVec]
            _ = (1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f A).mulVec x +
                  (1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f B).mulVec x := by
                  exact smul_add (1 / 2 : ℝ)
                    ((HansenPedersen.matrixCfcR f A).mulVec x)
                    ((HansenPedersen.matrixCfcR f B).mulVec x)
        dsimp [M]
        rw [Matrix.sub_mulVec, hsumVec]
      have hlin :
          dotProduct (star x) (M.mulVec x) =
            u - ((1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w) := by
        have hdotA :
            dotProduct (star x) ((1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f A).mulVec x) =
              (1 / 2 : ℝ) • v := by
          exact dotProduct_smul (1 / 2 : ℝ) (star x)
            ((HansenPedersen.matrixCfcR f A).mulVec x)
        have hdotB :
            dotProduct (star x) ((1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f B).mulVec x) =
              (1 / 2 : ℝ) • w := by
          exact dotProduct_smul (1 / 2 : ℝ) (star x)
            ((HansenPedersen.matrixCfcR f B).mulVec x)
        calc
          dotProduct (star x) (M.mulVec x)
              = dotProduct (star x)
                  ((HansenPedersen.matrixCfcR f ((1 / 2 : ℝ) • (A + B))).mulVec x -
                    ((1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f A).mulVec x +
                      (1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f B).mulVec x)) := by
                rw [hlinVec]
          _ = u -
                (dotProduct (star x)
                    ((1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f A).mulVec x) +
                  dotProduct (star x)
                    ((1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f B).mulVec x)) := by
                simp [u, dotProduct_sub, dotProduct_add]
          _ = u - ((1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w) := by
                rw [hdotA, hdotB]
      have hcalc :
          Complex.re (dotProduct (star x) (M.mulVec x)) =
            c - ((1 / 2 : ℝ) * a + (1 - (1 / 2 : ℝ)) * b) := by
        have hreal := congrArg Complex.re hlin
        dsimp [u, v, w, a, b, c] at hreal ⊢
        rw [hhalf]
        simpa using hreal
      have hre : 0 ≤ Complex.re (dotProduct (star x) (M.mulVec x)) := by
        rw [hcalc]
        exact sub_nonneg.mpr hquad'
      have him : Complex.im (dotProduct (star x) (M.mulVec x)) = 0 := by
        have hHerm : M.IsHermitian := by
          simpa [Matrix.IsHermitian, IsSelfAdjoint] using hM_sa
        exact Matrix.IsHermitian.im_star_dotProduct_mulVec_self (A := M) hHerm x
      rw [Complex.le_def]
      exact ⟨hre, by simpa using him.symm⟩
  refine sub_nonneg.mp ?_
  simpa [M, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (hM_psd.nonneg : (0 : Mₙ n) ≤ M)

end

end Quantum.TraceInequality.Loewner.HiaiPetz
