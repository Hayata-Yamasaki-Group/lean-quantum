/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.BlockSumBase
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagOrthogonalTransport
import Quantum.TraceInequality.HiaiPetz.JArgAction
import Quantum.TraceInequality.HansenPedersen.MatrixFunctionalCalculus
import Quantum.TraceInequality.HiaiPetzTheorem.MatrixFunctionalCalculus
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus
import Quantum.TraceInequality.HansenPedersen.OffDiagonalCore
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.Conditions
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.StandardRectangle.Main
import
Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.StandardRectangle.DirectToInverse
import Quantum.TraceInequality.HansenPedersen.LaterConsequences
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Quantum.TraceInequality.HansenPedersen.MatrixPosDef
import Quantum.TraceInequality.HiaiPetz.MatrixPosDef
import Quantum.TraceInequality.HansenPedersen.Core.Basic
import Quantum.TraceInequality.HiaiPetz.Core.Basic
import Quantum.TraceInequality.HansenPedersen.Core.JOperatorPositivity

/-!
# Standard compression basics

Zero-dimensional boundary cases, standard `J`-form quadratic forms, and their
first reduction to compression quadratic forms.
-/

namespace HiaiPetz

open Matrix Unitary
open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- For a Hilbert–Schmidt map `Φ : HSMap 0 (m+1)`, the image `Φ 1` of the identity
is not positive definite, since it equals the zero matrix on a positive dimension. -/
theorem not_matrixPosDef_image_one_zeroDomain_succ {m : ℕ} (Φ : HSMap 0 (Nat.succ m)) :
    ¬ Matrix.PosDef (Φ (1 : Mₙ 0)) := by
  intro hΦ1
  exact HiaiPetz.MatrixPosDef.not_matrixPosDef_zero_succ m
    (by simpa [HiaiPetz.Core.image_one_zeroDomain_eq_zero Φ] using hΦ1)

/-- With zero-dimensional codomain, the inverse `J`-operator inequality for `Φ`
holds: the compressed left-hand operator vanishes and the right-hand
`jOperatorInv f A B` is nonnegative for positive definite `A`, `B`. -/
theorem StrictlyPositive.inverse_zeroCodomain (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    {n : ℕ} (Φ : HSMap n 0) {A B : Mₙ n}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    (show HSOp n from
      (hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ)) ≤
      (jOperatorInv f A B) := by
  have hΦzero : Φ = 0 := HiaiPetz.Core.hsMap_eq_zero_of_zeroCodomain Φ
  have hAdjZero : hsAdjoint (0 : HSMap n 0) = 0 := by
    exact Subsingleton.elim _ _
  have hleft :
      ((hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ)) = 0 := by
    subst hΦzero
    rw [hAdjZero]
    simp
  have hleft' :
      (show HSOp n from
        (hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ)) = 0 :=
    congrArg (fun T : HSOp n => T) hleft
  rw [hleft']
  exact jOperatorInv_nonneg (f := f) (A := A) (B := B) hf hpos hA hB

/-- Standard quadratic form for the strict-output inverse condition, using the
reciprocal `x ↦ (f x)⁻¹`: the `A`-side real trace on `rightMul (B⁻¹) X`
minus the compressed `Φ`-side trace weighted by `((Φ B)⁻¹)`. -/
noncomputable def StrictlyPositive.inverseStandardQForm (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (X : Mₙ (Nat.succ k)) : ℝ :=
  Complex.re
      (Matrix.trace
        (Matrix.conjTranspose (rightMul (B⁻¹) X) *
          hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) X)) -
    Complex.re
      (Matrix.trace
        ((Matrix.conjTranspose (Φ X) *
            hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg (Φ A) (Φ B)) (Φ X)) *
          ((Φ B)⁻¹)))

/-- Standard quadratic form for the strict-output direct condition: the `Φ`-side
real trace of `⟨X, hsCfcR f (jArg (Φ A) (Φ B)) X⟩` weighted by `Φ B`, minus the
compressed `A`-side trace evaluated on `hsAdjoint Φ X`. -/
noncomputable def StrictlyPositive.directStandardQForm (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (X : Mₙ (Nat.succ l)) : ℝ :=
  Complex.re
      (Matrix.trace
        ((Matrix.conjTranspose X * hsCfcR f (jArg (Φ A) (Φ B)) X) *
          (Φ B))) -
    Complex.re
      (Matrix.trace
        (Matrix.conjTranspose (rightMul B ((hsAdjoint Φ) X)) *
          hsCfcR f (jArg A B) ((hsAdjoint Φ) X)))

namespace StrictlyPositive

/-- Strict-output inverse standard condition: `inverseStandardQForm f Φ A B` is
nonnegative on every test matrix `X : Mₙ (k+1)`. -/
def InverseStandard (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k)) : Prop :=
  ∀ X : Mₙ (Nat.succ k), 0 ≤ StrictlyPositive.inverseStandardQForm f Φ A B X

/-- Strict-output direct standard condition: `directStandardQForm f Φ A B` is
nonnegative on every test matrix `X : Mₙ (l+1)`. -/
def DirectStandard (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k)) : Prop :=
  ∀ X : Mₙ (Nat.succ l), 0 ≤ StrictlyPositive.directStandardQForm f Φ A B X

end StrictlyPositive

/-- The CFC `J`-argument operator `hsCfcR f (jArg A B)` commutes with right
multiplication by the positive square root `matrixSqrtPos B`. -/
theorem commute_cfc_jArg_rightMul_sqrt
    (f : ℝ → ℝ)
    {n : ℕ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    Commute
      (hsCfcR f (jArg A B))
      (rightMul (matrixSqrtPos B)) := by
  have hcommSqrtB : Commute (matrixSqrtPos B) B := by
    change matrixSqrtPos B * B = B * matrixSqrtPos B
    calc
      matrixSqrtPos B * B = matrixSqrtPos B * (matrixSqrtPos B * matrixSqrtPos B) := by
        rw [HiaiPetz.OffDiagonalCore.matrixSqrtPos_mul_self hB]
      _ = (matrixSqrtPos B * matrixSqrtPos B) * matrixSqrtPos B := by
        simp [Matrix.mul_assoc]
      _ = B * matrixSqrtPos B := by
        rw [HiaiPetz.OffDiagonalCore.matrixSqrtPos_mul_self hB]
  have hcommSqrtInv : Commute (matrixSqrtPos B) (B⁻¹) := by
    rcases hB.isUnit with ⟨u, hu⟩
    have hcommUnit : Commute (matrixSqrtPos B) (u : Mₙ n) := by
      simpa [hu] using hcommSqrtB
    simpa [hu] using (Commute.units_inv_right hcommUnit)
  have hcommSqrtInv_eq : matrixSqrtPos B * B⁻¹ = B⁻¹ * matrixSqrtPos B := by
    simpa using hcommSqrtInv.eq
  have hcomm0 : Commute (jArg A B) (rightMul (matrixSqrtPos B)) := by
    ext X i j
    simp only [ContinuousLinearMap.coe_mul', Function.comp_apply, rightMul_apply, jArg_apply]
    have hmatrix :
        A * (X * matrixSqrtPos B) * B⁻¹ = A * X * B⁻¹ * matrixSqrtPos B := by
      calc
        A * (X * matrixSqrtPos B) * B⁻¹
            = A * X * (matrixSqrtPos B * B⁻¹) := by
              simp [Matrix.mul_assoc]
        _ = A * X * (B⁻¹ * matrixSqrtPos B) := by
              rw [hcommSqrtInv_eq]
        _ = A * X * B⁻¹ * matrixSqrtPos B := by
              simp [Matrix.mul_assoc]
    exact congrArg (fun M => M i j) hmatrix
  simpa using hcomm0.cfc_real f

/-- The CFC `J`-argument operator `hsCfcR f (jArg A B)` commutes with right
multiplication by the inverse square root `matrixInvSqrtPos B`. -/
theorem commute_cfc_jArg_rightMul_invSqrt
    (f : ℝ → ℝ)
    {n : ℕ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) :
    Commute
      (hsCfcR f (jArg A B))
      (rightMul (matrixInvSqrtPos B)) := by
  have hcommInvSqrtInv :
      matrixInvSqrtPos B * B⁻¹ = B⁻¹ * matrixInvSqrtPos B := by
    calc
      matrixInvSqrtPos B * B⁻¹
          = matrixInvSqrtPos B * (matrixInvSqrtPos B * matrixInvSqrtPos B) := by
              rw [matrixInvSqrtPos_mul_self hB]
      _ = (matrixInvSqrtPos B * matrixInvSqrtPos B) * matrixInvSqrtPos B := by
            simp [Matrix.mul_assoc]
      _ = B⁻¹ * matrixInvSqrtPos B := by
            rw [matrixInvSqrtPos_mul_self hB]
  have hcomm0 : Commute (jArg A B) (rightMul (matrixInvSqrtPos B)) := by
    ext X i j
    simp only [ContinuousLinearMap.coe_mul', Function.comp_apply, rightMul_apply, jArg_apply]
    have hmatrix :
        A * (X * matrixInvSqrtPos B) * B⁻¹ = A * X * B⁻¹ * matrixInvSqrtPos B := by
      calc
        A * (X * matrixInvSqrtPos B) * B⁻¹
            = A * X * (matrixInvSqrtPos B * B⁻¹) := by
              simp [Matrix.mul_assoc]
        _ = A * X * (B⁻¹ * matrixInvSqrtPos B) := by
              rw [hcommInvSqrtInv]
        _ = A * X * B⁻¹ * matrixInvSqrtPos B := by
              simp [Matrix.mul_assoc]
    exact congrArg (fun M => M i j) hmatrix
  simpa using hcomm0.cfc_real f

/-- Unfolds the action of the compression `StrictlyPositive.contraction Φ` on a
test matrix `X`: it maps `X` to `hsAdjoint Φ (X * matrixInvSqrtPos (Φ B)) *
matrixSqrtPos B`. -/
@[simp] theorem StrictlyPositive.contraction_apply
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ) (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ l)) :
    StrictlyPositive.contraction Φ hPos hB hΦ1 X =
      ((hsAdjoint Φ) (X * matrixInvSqrtPos (Φ B))) * matrixSqrtPos B := by
  rfl

/-- The adjoint of the compression `StrictlyPositive.contraction Φ`, applied to
`rightMul (matrixInvSqrtPos B) X`, equals `rightMul (matrixInvSqrtPos (Φ B)) (Φ X)`. -/
theorem hsAdjoint_contraction_apply_invSqrtShift
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ) (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ k)) :
    hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)
        (rightMul (matrixInvSqrtPos B) X) =
      rightMul (matrixInvSqrtPos (Φ B)) (Φ X) := by
  letI : NormedAddCommGroup (Mₙ (Nat.succ k)) := instMatrixNormedAddCommGroup (n := Nat.succ k)
  letI : NormedSpace ℂ (Mₙ (Nat.succ k)) := instMatrixNormedSpace (n := Nat.succ k)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ k)) := instMatrixInnerProductSpace (n := Nat.succ k)
  letI : CompleteSpace (Mₙ (Nat.succ k)) := instMatrixCompleteSpace (n := Nat.succ k)
  letI : NormedAddCommGroup (Mₙ (Nat.succ l)) := instMatrixNormedAddCommGroup (n := Nat.succ l)
  letI : NormedSpace ℂ (Mₙ (Nat.succ l)) := instMatrixNormedSpace (n := Nat.succ l)
  letI : InnerProductSpace ℂ (Mₙ (Nat.succ l)) := instMatrixInnerProductSpace (n := Nat.succ l)
  letI : CompleteSpace (Mₙ (Nat.succ l)) := instMatrixCompleteSpace (n := Nat.succ l)
  /- Step 1: Record self-adjointness of the square-root factors and of Φ's double adjoint. -/
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  have hsqrtB_sa : IsSelfAdjoint (matrixSqrtPos B) :=
    (HiaiPetz.OffDiagonalCore.matrixPosDef_sqrt hB).1
  have hInvΦB_sa : IsSelfAdjoint (matrixInvSqrtPos (Φ B)) := (matrixInvSqrtPos_posDef hΦB).1
  have hadjInv :
      hsAdjoint (rightMul (matrixInvSqrtPos (Φ B))) =
        rightMul (matrixInvSqrtPos (Φ B)) := by
    exact rightMul_isSelfAdjoint hInvΦB_sa
  have hadjSqrt :
      hsAdjoint (rightMul (matrixSqrtPos B)) =
        rightMul (matrixSqrtPos B) := by
    exact rightMul_isSelfAdjoint hsqrtB_sa
  have hΦAdjAdj : hsAdjoint (hsAdjoint Φ) = Φ := by
    simp [hsAdjoint]
  /- Step 2: Establish the square-root cancellation identity for B. -/
  have hcancel :
      rightMul (matrixSqrtPos B) (rightMul (matrixInvSqrtPos B) X) = X := by
    ext i j
    simp [rightMul_apply, Matrix.mul_assoc, matrixInvSqrtPos_mul_matrixSqrtPos hB]
  have hcancel' :
      X * matrixInvSqrtPos B * matrixSqrtPos B = X := by
    simpa [rightMul_apply, Matrix.mul_assoc] using hcancel
  /- Step 3: Expand the adjoint of the contraction into composed right-multiplications and Φ. -/
  have hAdj :
      hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1) =
        ((hsAdjoint (rightMul (matrixInvSqrtPos (Φ B)))).comp Φ).comp
          (hsAdjoint (rightMul (matrixSqrtPos B))) := by
    calc
      hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)
          = (hsAdjoint ((hsAdjoint Φ).comp (rightMul (matrixInvSqrtPos (Φ B))))).comp
              (hsAdjoint (rightMul (matrixSqrtPos B))) := by
                dsimp [StrictlyPositive.contraction, hsAdjoint]
                exact
                  (@ContinuousLinearMap.adjoint_comp ℂ (Mₙ (Nat.succ l)) (Mₙ (Nat.succ k))
                    (Mₙ (Nat.succ k))
                    (inferInstance : RCLike ℂ)
                    (instMatrixNormedAddCommGroup (n := Nat.succ l))
                    (instMatrixNormedAddCommGroup (n := Nat.succ k))
                    (instMatrixNormedAddCommGroup (n := Nat.succ k))
                    (instMatrixInnerProductSpace (n := Nat.succ l))
                    (instMatrixInnerProductSpace (n := Nat.succ k))
                    (instMatrixInnerProductSpace (n := Nat.succ k))
                    (instMatrixCompleteSpace (n := Nat.succ l))
                    (instMatrixCompleteSpace (n := Nat.succ k))
                    (instMatrixCompleteSpace (n := Nat.succ k))
                    (rightMul (matrixSqrtPos B))
                    ((hsAdjoint Φ).comp (rightMul (matrixInvSqrtPos (Φ B)))))
      _ = (((hsAdjoint (rightMul (matrixInvSqrtPos (Φ B)))).comp
              (hsAdjoint (hsAdjoint Φ)))).comp
            (hsAdjoint (rightMul (matrixSqrtPos B))) := by
              rw [show hsAdjoint ((hsAdjoint Φ).comp (rightMul (matrixInvSqrtPos (Φ B)))) =
                  (hsAdjoint (rightMul (matrixInvSqrtPos (Φ B)))).comp
                    (hsAdjoint (hsAdjoint Φ)) by
                dsimp [hsAdjoint]
                exact
                  (@ContinuousLinearMap.adjoint_comp ℂ (Mₙ (Nat.succ l)) (Mₙ (Nat.succ l))
                    (Mₙ (Nat.succ k))
                    (inferInstance : RCLike ℂ)
                    (instMatrixNormedAddCommGroup (n := Nat.succ l))
                    (instMatrixNormedAddCommGroup (n := Nat.succ l))
                    (instMatrixNormedAddCommGroup (n := Nat.succ k))
                    (instMatrixInnerProductSpace (n := Nat.succ l))
                    (instMatrixInnerProductSpace (n := Nat.succ l))
                    (instMatrixInnerProductSpace (n := Nat.succ k))
                    (instMatrixCompleteSpace (n := Nat.succ l))
                    (instMatrixCompleteSpace (n := Nat.succ k))
                    (instMatrixCompleteSpace (n := Nat.succ l))
                    (hsAdjoint Φ)
                    (rightMul (matrixInvSqrtPos (Φ B))))]
      _ = ((hsAdjoint (rightMul (matrixInvSqrtPos (Φ B)))).comp Φ).comp
            (hsAdjoint (rightMul (matrixSqrtPos B))) := by
              apply ContinuousLinearMap.ext
              intro Z
              simp [ContinuousLinearMap.comp_apply, hΦAdjAdj]
  /- Step 4: Apply the expanded adjoint to the shifted input. -/
  have hAdjApply :
      hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1) (rightMul (matrixInvSqrtPos B) X) =
        rightMul (matrixInvSqrtPos (Φ B))
          (Φ (rightMul (matrixSqrtPos B) (rightMul (matrixInvSqrtPos B) X))) := by
    simpa [ContinuousLinearMap.comp_apply, hadjInv, hadjSqrt] using
      congrArg (fun T : HSMap (Nat.succ k) (Nat.succ l) =>
        T (rightMul (matrixInvSqrtPos B) X)) hAdj
  /- Step 5: Use the cancellation to reach the target form and conclude. -/
  have hfinal :
      rightMul (matrixInvSqrtPos (Φ B))
          (Φ (rightMul (matrixSqrtPos B) (rightMul (matrixInvSqrtPos B) X))) =
        rightMul (matrixInvSqrtPos (Φ B)) (Φ X) := by
    exact congrArg (fun Z : Mₙ (Nat.succ k) =>
      rightMul (matrixInvSqrtPos (Φ B)) (Φ Z)) hcancel
  exact hAdjApply.trans hfinal

/-- First reduction of the direct `Φ`-side form: on `Y = rightMul (matrixSqrtPos
(Φ B)) X`, the `J`-form trace `⟨Y, TΦ Y⟩` equals the `Φ B`-weighted trace
`⟨X, TΦ X⟩ · Φ B`, using that `TΦ` commutes with `rightMul (matrixSqrtPos (Φ B))`. -/
theorem StrictlyPositive.direct_contraction_first
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ l)) :
    let TΦ : HSOp (Nat.succ l) :=
      hsCfcR f (jArg (Φ A) (Φ B))
    let Y : Mₙ (Nat.succ l) := rightMul (matrixSqrtPos (Φ B)) X
    Complex.re (Matrix.trace (Matrix.conjTranspose Y * (TΦ Y))) =
      Complex.re (Matrix.trace ((Matrix.conjTranspose X * (TΦ X)) * (Φ B))) := by
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  let TΦ : HSOp (Nat.succ l) := hsCfcR f (jArg (Φ A) (Φ B))
  let Y : Mₙ (Nat.succ l) := rightMul (matrixSqrtPos (Φ B)) X
  have hsqrtΦ_sa : IsSelfAdjoint (matrixSqrtPos (Φ B)) :=
    (HiaiPetz.OffDiagonalCore.matrixPosDef_sqrt hΦB).1
  have hcommΦ :
      Commute TΦ (rightMul (matrixSqrtPos (Φ B))) :=
    commute_cfc_jArg_rightMul_sqrt (f := f) (A := Φ A) hΦB
  have hTY : TΦ Y = rightMul (matrixSqrtPos (Φ B)) (TΦ X) := by
    dsimp [Y, TΦ]
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun S : HSOp (Nat.succ l) => S X) hcommΦ.eq
  have hYY : rightMul (matrixSqrtPos (Φ B)) Y = rightMul (Φ B) X := by
    ext i j
    simp [Y, rightMul_apply, Matrix.mul_assoc, HiaiPetz.OffDiagonalCore.matrixSqrtPos_mul_self hΦB]
  calc
    Complex.re (Matrix.trace (Matrix.conjTranspose Y * (TΦ Y)))
        = Complex.re
            (Matrix.trace
              (Matrix.conjTranspose Y *
                (rightMul (matrixSqrtPos (Φ B)) (TΦ X)))) := by
                  rw [hTY]
    _ = Complex.re
          (Matrix.trace
            ((Matrix.conjTranspose Y * TΦ X) * matrixSqrtPos (Φ B))) := by
              simp [rightMul_apply, Matrix.mul_assoc]
    _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (rightMul (matrixSqrtPos (Φ B)) Y) * TΦ X)) := by
              symm
              exact
                (hsQForm_shift_rightMul_testMatrix
                  (B := matrixSqrtPos (Φ B)) (X := Y) (Y := TΦ X) hsqrtΦ_sa).symm
    _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (rightMul (Φ B) X) * TΦ X)) := by
              rw [hYY]
    _ = Complex.re
          (Matrix.trace
            ((Matrix.conjTranspose X * (TΦ X)) * (Φ B))) := by
              exact
                (hsQForm_shift_rightMul_testMatrix
                  (B := Φ B) (X := X) (Y := TΦ X) hΦB.1).symm

/-- Second reduction of the direct condition: on `Y = rightMul (matrixSqrtPos
(Φ B)) X`, the compressed form `⟨Y, (hsAdjoint V ∘ TA ∘ V) Y⟩` equals the `A`-side
trace `⟨rightMul B (hsAdjoint Φ X), TA (hsAdjoint Φ X)⟩`. -/
theorem StrictlyPositive.direct_contraction_second
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ l)) :
    let TA : HSOp (Nat.succ k) :=
      hsCfcR f (jArg A B)
    let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
    let Y : Mₙ (Nat.succ l) := rightMul (matrixSqrtPos (Φ B)) X
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose Y *
            (((hsAdjoint V).comp (TA.comp V)) Y))) =
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose (rightMul B ((hsAdjoint Φ) X)) *
            (TA ((hsAdjoint Φ) X)))) := by
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  let TA : HSOp (Nat.succ k) := hsCfcR f (jArg A B)
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  let Y : Mₙ (Nat.succ l) := rightMul (matrixSqrtPos (Φ B)) X
  have hsqrtB_sa : IsSelfAdjoint (matrixSqrtPos B) :=
    (HiaiPetz.OffDiagonalCore.matrixPosDef_sqrt hB).1
  have hcommA :
      Commute TA (rightMul (matrixSqrtPos B)) :=
    commute_cfc_jArg_rightMul_sqrt (f := f) (A := A) hB
  have hVY : V Y = rightMul (matrixSqrtPos B) ((hsAdjoint Φ) X) := by
    simpa [Y, rightMul_apply] using
      StrictlyPositive.contraction_apply_sqrtShift Φ hPos hB hΦ1 X
  have hTAV : TA (V Y) = rightMul (matrixSqrtPos B) (TA ((hsAdjoint Φ) X)) := by
    rw [hVY]
    dsimp [TA]
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun S : HSOp (Nat.succ k) => S ((hsAdjoint Φ) X)) hcommA.eq
  have hTAV' :
      TA (rightMul (matrixSqrtPos B) ((hsAdjoint Φ) X)) =
        rightMul (matrixSqrtPos B) (TA ((hsAdjoint Φ) X)) := by
    simpa [hVY] using hTAV
  calc
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose Y *
            (((hsAdjoint V).comp (TA.comp V)) Y)))
      = Complex.re
          (Matrix.trace (Matrix.conjTranspose (V Y) * (TA (V Y)))) := by
            simpa [V, TA, Y] using hsQForm_hsAdjoint_comp V TA Y
    _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (rightMul (matrixSqrtPos B) ((hsAdjoint Φ) X)) *
              (rightMul (matrixSqrtPos B) (TA ((hsAdjoint Φ) X))))) := by
                rw [hVY, hTAV']
    _ = Complex.re
          (Matrix.trace
            ((Matrix.conjTranspose (rightMul (matrixSqrtPos B) ((hsAdjoint Φ) X)) *
                TA ((hsAdjoint Φ) X)) * matrixSqrtPos B)) := by
                  simp [rightMul_apply, Matrix.mul_assoc]
    _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (rightMul B ((hsAdjoint Φ) X)) *
              TA ((hsAdjoint Φ) X))) := by
                rw [hsQForm_shift_rightMul_testMatrix hsqrtB_sa]
                congr 1
                simp [rightMul_apply, Matrix.mul_assoc,
                  HiaiPetz.OffDiagonalCore.matrixSqrtPos_mul_self hB]

/-- Direct compression quadratic form: the real trace `⟨Y, C Y⟩` of the core
operator `C = TΦ - (hsAdjoint V ∘ TA ∘ V)` on `Y = rightMul (matrixSqrtPos (Φ B))
X`, where `V` is the compression `StrictlyPositive.contraction Φ`. -/
noncomputable def StrictlyPositive.directCompressionQForm (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ l)) : ℝ :=
  let TΦ : HSOp (Nat.succ l) :=
    hsCfcR f (jArg (Φ A) (Φ B))
  let TA : HSOp (Nat.succ k) :=
    hsCfcR f (jArg A B)
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  let TV : HSOp (Nat.succ l) := (hsAdjoint V).comp (TA.comp V)
  let C : HSOp (Nat.succ l) := TΦ - TV
  let Y : Mₙ (Nat.succ l) := rightMul (matrixSqrtPos (Φ B)) X
  Complex.re
    (Matrix.trace
      (Matrix.conjTranspose Y * (C Y)))

/-- The direct standard quadratic form equals the direct compression quadratic
form, obtained by reducing its two trace terms via `direct_contraction_first` and
`direct_contraction_second`. -/
theorem StrictlyPositive.directStandardQForm_eq_contraction_qform
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ l)) :
    StrictlyPositive.directStandardQForm f Φ A B X =
      StrictlyPositive.directCompressionQForm f Φ A B hPos hB hΦ1 X := by
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  let TΦ : HSOp (Nat.succ l) := hsCfcR f (jArg (Φ A) (Φ B))
  let TA : HSOp (Nat.succ k) := hsCfcR f (jArg A B)
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  let TV : HSOp (Nat.succ l) := (hsAdjoint V).comp (TA.comp V)
  let C : HSOp (Nat.succ l) := TΦ - TV
  let Y : Mₙ (Nat.succ l) := rightMul (matrixSqrtPos (Φ B)) X
  have hfirst :
      Complex.re (Matrix.trace (Matrix.conjTranspose Y * (TΦ Y))) =
        Complex.re
          (Matrix.trace
            ((Matrix.conjTranspose X * (TΦ X)) * (Φ B))) := by
    simpa [TΦ, Y] using
      StrictlyPositive.direct_contraction_first
        (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X
  have hsecond :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose Y *
              (((hsAdjoint V).comp (TA.comp V)) Y))) =
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (rightMul B ((hsAdjoint Φ) X)) *
              (TA ((hsAdjoint Φ) X)))) := by
    simpa [TA, V, Y] using
      StrictlyPositive.direct_contraction_second
        (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X
  calc
    StrictlyPositive.directStandardQForm f Φ A B X
        = Complex.re
            (Matrix.trace
              ((Matrix.conjTranspose X * (TΦ X)) * (Φ B))) -
          Complex.re
            (Matrix.trace
              (Matrix.conjTranspose (rightMul B ((hsAdjoint Φ) X)) *
                (TA ((hsAdjoint Φ) X)))) := by
                  simp [StrictlyPositive.directStandardQForm, TΦ, TA]
    _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose Y * (TΦ Y))) -
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose Y *
              (((hsAdjoint V).comp (TA.comp V)) Y))) := by
                rw [hfirst, hsecond]
    _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose Y * (C Y))) := by
                simpa [C, TV] using (hsQForm_sub (S := TΦ) (T := TV) (X := Y)).symm
    _ = StrictlyPositive.directCompressionQForm f Φ A B hPos hB hΦ1 X := by
          simp [StrictlyPositive.directCompressionQForm, TΦ, TA, V, TV, C, Y]

/-- Restatement of `directStandardQForm_eq_contraction_qform`: the direct standard
quadratic form equals the direct compression quadratic form. -/
theorem StrictlyPositive.directStandardQForm_eq_directCompressionQForm
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ l)) :
    StrictlyPositive.directStandardQForm f Φ A B X =
      StrictlyPositive.directCompressionQForm f Φ A B hPos hB hΦ1 X := by
  simpa using
    StrictlyPositive.directStandardQForm_eq_contraction_qform
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X

/-- Inverse compression quadratic form: the real trace `⟨Y, C Y⟩` of the core
operator `C = TA - (hsAdjoint W ∘ TΦ ∘ W)` on `Y = rightMul (matrixInvSqrtPos B)
X`, where `W = hsAdjoint (StrictlyPositive.contraction Φ)` and the CFC uses
`x ↦ (f x)⁻¹`. -/
noncomputable def StrictlyPositive.inverseCompressionQForm (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ k)) : ℝ :=
  let TA : HSOp (Nat.succ k) :=
    hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B)
  let TΦ : HSOp (Nat.succ l) :=
    hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg (Φ A) (Φ B))
  let W : HSMap (Nat.succ k) (Nat.succ l) := hsAdjoint (StrictlyPositive.contraction Φ hPos hB
    hΦ1)
  let TW : HSOp (Nat.succ k) := (hsAdjoint W).comp (TΦ.comp W)
  let C : HSOp (Nat.succ k) := TA - TW
  let Y : Mₙ (Nat.succ k) := rightMul (matrixInvSqrtPos B) X
  Complex.re
    (Matrix.trace
      (Matrix.conjTranspose Y * (C Y)))

/-- The inverse standard quadratic form equals the inverse compression quadratic
form, reducing each of its two trace terms through the compression `W` and the
commutation of the reciprocal `J`-argument operator with the inverse square roots. -/
theorem StrictlyPositive.inverseStandardQForm_eq_inverseCompressionQForm
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ k)) :
    StrictlyPositive.inverseStandardQForm f Φ A B X =
      StrictlyPositive.inverseCompressionQForm f Φ A B hPos hB hΦ1 X := by
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  /- Step 1: Name the CFC operators, the contraction adjoint W, and the shifted test vector Y. -/
  let TA : HSOp (Nat.succ k) := hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B)
  let TΦ : HSOp (Nat.succ l) := hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg (Φ A) (Φ B))
  let W : HSMap (Nat.succ k) (Nat.succ l) := hsAdjoint (StrictlyPositive.contraction Φ hPos hB
    hΦ1)
  let TW : HSOp (Nat.succ k) := (hsAdjoint W).comp (TΦ.comp W)
  let C : HSOp (Nat.succ k) := TA - TW
  let Y : Mₙ (Nat.succ k) := rightMul (matrixInvSqrtPos B) X
  /- Step 2: Record CFC commutation with the inverse-square-root factor and evaluate on Y. -/
  have hcommA :
      Commute TA (rightMul (matrixInvSqrtPos B)) :=
    commute_cfc_jArg_rightMul_invSqrt (f := fun x : ℝ ↦ (f x)⁻¹) (A := A) hB
  have hcommΦ :
      Commute TΦ (rightMul (matrixInvSqrtPos (Φ B))) :=
    commute_cfc_jArg_rightMul_invSqrt (f := fun x : ℝ ↦ (f x)⁻¹) (A := Φ A) hΦB
  have hTAY : TA Y = rightMul (matrixInvSqrtPos B) (TA X) := by
    dsimp [TA, Y]
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun S : HSOp (Nat.succ k) => S X) hcommA.eq
  have hWY : W Y = rightMul (matrixInvSqrtPos (Φ B)) (Φ X) := by
    simpa [W, Y] using
      hsAdjoint_contraction_apply_invSqrtShift Φ hPos hB hΦ1 X
  have hTWY :
      TΦ (W Y) = rightMul (matrixInvSqrtPos (Φ B)) (TΦ (Φ X)) := by
    rw [hWY]
    dsimp [TΦ]
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun S : HSOp (Nat.succ l) => S (Φ X)) hcommΦ.eq
  /- Step 3: Reduce the first (codomain-argument) trace term to the standard B⁻¹ form. -/
  have hfirst :
      Complex.re (Matrix.trace (Matrix.conjTranspose Y * (TA Y))) =
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (rightMul (B⁻¹) X) * (TA X))) := by
    have hYY : rightMul (matrixInvSqrtPos B) Y = rightMul (B⁻¹) X := by
      ext i j
      simp [Y, rightMul_apply, Matrix.mul_assoc, matrixInvSqrtPos_mul_self hB]
    calc
      Complex.re (Matrix.trace (Matrix.conjTranspose Y * (TA Y)))
          = Complex.re
              (Matrix.trace
                (Matrix.conjTranspose Y * (rightMul (matrixInvSqrtPos B) (TA X)))) := by
                  rw [hTAY]
      _ = Complex.re
            (Matrix.trace
              ((Matrix.conjTranspose Y * TA X) * matrixInvSqrtPos B)) := by
                simp [rightMul_apply, Matrix.mul_assoc]
      _ = Complex.re
            (Matrix.trace
              (Matrix.conjTranspose (rightMul (matrixInvSqrtPos B) Y) * TA X)) := by
                exact
                  (hsQForm_shift_rightMul_testMatrix
                    (B := matrixInvSqrtPos B) (X := Y) (Y := TA X)
                    (matrixInvSqrtPos_posDef hB).1)
      _ = Complex.re
            (Matrix.trace
              (Matrix.conjTranspose (rightMul (B⁻¹) X) * TA X)) := by
                rw [hYY]
  /- Step 4: Reduce the second (compressed) trace term to the ((Φ B)⁻¹) form. -/
  have hsecond :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose Y *
              (((hsAdjoint W).comp (TΦ.comp W)) Y))) =
        Complex.re
          (Matrix.trace
            ((Matrix.conjTranspose (Φ X) * (TΦ (Φ X))) * ((Φ B)⁻¹))) := by
    have hWWY :
        rightMul (matrixInvSqrtPos (Φ B)) (W Y) = rightMul (((Φ B)⁻¹)) (Φ X) := by
      rw [hWY]
      ext i j
      simp [rightMul_apply, Matrix.mul_assoc, matrixInvSqrtPos_mul_self hΦB]
    have hWWY' :
        rightMul (matrixInvSqrtPos (Φ B))
            (rightMul (matrixInvSqrtPos (Φ B)) (Φ X)) =
          rightMul (((Φ B)⁻¹)) (Φ X) := by
      ext i j
      simp [rightMul_apply, Matrix.mul_assoc, matrixInvSqrtPos_mul_self hΦB]
    calc
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose Y *
              (((hsAdjoint W).comp (TΦ.comp W)) Y)))
        = Complex.re (Matrix.trace (Matrix.conjTranspose (W Y) * (TΦ (W Y)))) := by
            simpa [W, TΦ, Y] using hsQForm_hsAdjoint_comp W TΦ Y
      _ = Complex.re
            (Matrix.trace
              (Matrix.conjTranspose (rightMul (matrixInvSqrtPos (Φ B)) (Φ X)) *
                (rightMul (matrixInvSqrtPos (Φ B)) (TΦ (Φ X))))) := by
                  rw [hTWY, hWY]
      _ = Complex.re
            (Matrix.trace
              ((Matrix.conjTranspose (rightMul (matrixInvSqrtPos (Φ B)) (Φ X)) * TΦ (Φ X)) *
                matrixInvSqrtPos (Φ B))) := by
                  simp [rightMul_apply, Matrix.mul_assoc]
      _ = Complex.re
            (Matrix.trace
              (Matrix.conjTranspose (rightMul (((Φ B)⁻¹)) (Φ X)) * TΦ (Φ X))) := by
                rw [hsQForm_shift_rightMul_testMatrix
                  (B := matrixInvSqrtPos (Φ B))
                  (X := rightMul (matrixInvSqrtPos (Φ B)) (Φ X))
                  (Y := TΦ (Φ X))
                  (matrixInvSqrtPos_posDef hΦB).1]
                rw [hWWY']
      _ = Complex.re
            (Matrix.trace
              ((Matrix.conjTranspose (Φ X) * TΦ (Φ X)) * ((Φ B)⁻¹))) := by
                exact
                  (hsQForm_shift_rightMul_posInv_testMatrix
                    (B := Φ B) (X := Φ X) (Y := TΦ (Φ X)) hΦB).symm
  /- Step 5: Assemble both reductions into the equality of the two quadratic forms. -/
  calc
    StrictlyPositive.inverseStandardQForm f Φ A B X
        = Complex.re
            (Matrix.trace
              (Matrix.conjTranspose (rightMul (B⁻¹) X) * (TA X))) -
          Complex.re
            (Matrix.trace
              ((Matrix.conjTranspose (Φ X) * (TΦ (Φ X))) * ((Φ B)⁻¹))) := by
                simp [StrictlyPositive.inverseStandardQForm, TA, TΦ]
    _ = Complex.re
          (Matrix.trace (Matrix.conjTranspose Y * (TA Y))) -
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose Y *
              (((hsAdjoint W).comp (TΦ.comp W)) Y))) := by
                rw [hfirst, hsecond]
    _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose Y * (C Y))) := by
                simpa [C, TW] using (hsQForm_sub (S := TA) (T := TW) (X := Y)).symm
    _ = StrictlyPositive.inverseCompressionQForm f Φ A B hPos hB hΦ1 X := by
          simp [StrictlyPositive.inverseCompressionQForm, TA, TΦ, W, TW, C, Y]


end MatrixScopedInstances

end HiaiPetz
