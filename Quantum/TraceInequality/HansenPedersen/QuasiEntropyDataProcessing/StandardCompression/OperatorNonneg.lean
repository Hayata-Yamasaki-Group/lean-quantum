/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import
  Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.StandardCompression.Operators
import Quantum.TraceInequality.HansenPedersen.AmbientSubmodule.JOperatorInequalities

/-!
# Standard compression nonnegativity equivalences

Final equivalences between standard strict-output assertions and the concrete
operator-nonnegativity formulations.
-/

namespace HiaiPetz

open Matrix Unitary
open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances
/-- Nonnegativity of the direct compression operator is equivalent to nonnegativity of the
direct core operator, via the invertible shift `X ↦ rightMul (matrixSqrtPos (Φ B)) X`. -/
theorem StrictlyPositive.directCompressionOperatorNonneg_iff_coreOperatorNonneg
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.DirectCompressionOperatorNonneg f Φ A B hPos hB hΦ1 ↔
      StrictlyPositive.DirectCoreOperatorNonneg f Φ A B hPos hB hΦ1 := by
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  constructor
  · intro hcomp Y
    let X : Mₙ (Nat.succ l) := rightMul (matrixInvSqrtPos (Φ B)) Y
    have hX :
        rightMul (matrixSqrtPos (Φ B)) X = Y := by
      simp [X, rightMul_apply, Matrix.mul_assoc, matrixInvSqrtPos_mul_matrixSqrtPos hΦB]
    specialize hcomp X
    have hq :=
      StrictlyPositive.directCompressionOperator_qform_eq_coreOperatorQForm
        (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X
    simpa [StrictlyPositive.DirectCoreOperatorNonneg, X, rightMul_apply, Matrix.mul_assoc,
      Matrix.conjTranspose_mul, (HiaiPetz.OffDiagonalCore.matrixPosDef_sqrt hΦB).isHermitian,
      (matrixInvSqrtPos_posDef hΦB).isHermitian, matrixInvSqrtPos_mul_matrixSqrtPos hΦB] using
      (show 0 ≤
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (rightMul (matrixSqrtPos (Φ B)) X) *
              ((StrictlyPositive.directCoreOperator f Φ A B hPos hB hΦ1)
                (rightMul (matrixSqrtPos (Φ B)) X)))) from
        by simpa [hq] using hcomp)
  · intro hcore X
    have hq :=
      StrictlyPositive.directCompressionOperator_qform_eq_coreOperatorQForm
        (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X
    simpa [StrictlyPositive.DirectCoreOperatorNonneg] using
      (show 0 ≤
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.directCompressionOperator f Φ A B hPos hB hΦ1) X))) from
        by simpa [hq] using hcore (rightMul (matrixSqrtPos (Φ B)) X))

/-- Nonnegativity of the inverse compression operator is equivalent to nonnegativity of the
inverse core operator, via the invertible shift `X ↦ rightMul (matrixInvSqrtPos B) X`. -/
theorem StrictlyPositive.inverseCompressionOperatorNonneg_iff_coreOperatorNonneg
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.InverseCompressionOperatorNonneg f Φ A B hPos hB hΦ1 ↔
      StrictlyPositive.InverseCoreOperatorNonneg f Φ A B hPos hB hΦ1 := by
  constructor
  · intro hcomp Y
    let X : Mₙ (Nat.succ k) := rightMul (matrixSqrtPos B) Y
    have hX :
        rightMul (matrixInvSqrtPos B) X = Y := by
      simp [X, rightMul_apply, Matrix.mul_assoc, matrixSqrtPos_mul_matrixInvSqrtPos hB]
    specialize hcomp X
    have hq :=
      StrictlyPositive.inverseCompressionOperator_qform_eq_coreOperatorQForm
        (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X
    simpa [StrictlyPositive.InverseCoreOperatorNonneg, X, rightMul_apply, Matrix.mul_assoc,
      Matrix.conjTranspose_mul, (HiaiPetz.OffDiagonalCore.matrixPosDef_sqrt hB).isHermitian,
      (matrixInvSqrtPos_posDef hB).isHermitian, matrixSqrtPos_mul_matrixInvSqrtPos hB] using
      (show 0 ≤
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (rightMul (matrixInvSqrtPos B) X) *
              ((StrictlyPositive.inverseCoreOperator f Φ A B hPos hB hΦ1)
                (rightMul (matrixInvSqrtPos B) X)))) from
        by simpa [hq] using hcomp)
  · intro hcore X
    have hq :=
      StrictlyPositive.inverseCompressionOperator_qform_eq_coreOperatorQForm
        (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X
    simpa [StrictlyPositive.InverseCoreOperatorNonneg] using
      (show 0 ≤
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.inverseCompressionOperator f Φ A B hPos hB hΦ1) X))) from
        by simpa [hq] using hcore (rightMul (matrixInvSqrtPos B) X))

/-- For `f` continuous and strictly positive on `(0, ∞)`, nonnegativity of the inverse core
operator is equivalent to that of the inverse ring-core operator, since the two operators
agree (`inverseCoreOperator_eq_inverseRingCoreOperator`). -/
theorem StrictlyPositive.inverseCoreOperatorNonneg_iff_ringCoreOperatorNonneg
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.InverseCoreOperatorNonneg f Φ A B hPos hB hΦ1 ↔
      StrictlyPositive.InverseRingCoreOperatorNonneg f Φ A B hPos hB hΦ1 := by
  rw [StrictlyPositive.InverseCoreOperatorNonneg, StrictlyPositive.InverseRingCoreOperatorNonneg,
    StrictlyPositive.inverseCoreOperator_eq_inverseRingCoreOperator
      (f := f) (Φ := Φ) (A := A) (B := B) hf hpos hPos hA hB hΦ1]

/-- Nonnegativity of the direct core operator is equivalent to the concrete Loewner-order
condition `DirectCompressedLE f Φ A B hPos hB hΦ1`. -/
theorem StrictlyPositive.directCoreOperatorNonneg_iff_le_concrete
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ) (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.DirectCoreOperatorNonneg f Φ A B hPos hB hΦ1 ↔
      StrictlyPositive.DirectCompressedLE f Φ A B hPos hB hΦ1 := by
  let C : HSOp (Nat.succ l) :=
    StrictlyPositive.directCoreOperator f Φ A B hPos hB hΦ1
  have hCself : IsSelfAdjoint C := by
    let TΦ : HSOp (Nat.succ l) := hsCfcR f (jArg (Φ A) (Φ B))
    let TA : HSOp (Nat.succ k) := hsCfcR f (jArg A B)
    let V : HSMap (Nat.succ l) (Nat.succ k) :=
      StrictlyPositive.contraction Φ hPos hB hΦ1
    have hTΦself : IsSelfAdjoint TΦ := by
      simp [TΦ]
    have hTAself : IsSelfAdjoint TA := by
      simp [TA]
    have hcompressedSelf : IsSelfAdjoint (directRectOp V TA) := by
      simpa [hsAdjoint] using hsAdjoint_directRectOp (V := V) (TA := TA) hTAself
    simpa [C, StrictlyPositive.directCoreOperator, directRectOp, TΦ, TA, V] using
      hTΦself.sub hcompressedSelf
  constructor
  · intro hquad
    have hCnonneg : (0 : HSOp (Nat.succ l)) ≤ C := by
      refine le_of_quadratic_form_nonneg ?_ ?_
      · simpa using hCself
      · intro X
        simpa [C, hsQForm_real_eq_inner_real] using hquad X
    apply sub_nonneg.mp
    simpa [C, StrictlyPositive.DirectCompressedLE,
      StrictlyPositive.sourceJOp, StrictlyPositive.imageJOp,
      StrictlyPositive.contraction, StrictlyPositive.directCoreOperator] using hCnonneg
  · intro hle X
    have hCnonneg : (0 : HSOp (Nat.succ l)) ≤ C := by
      have := sub_nonneg.mpr hle
      simpa [C, StrictlyPositive.DirectCompressedLE,
        StrictlyPositive.sourceJOp, StrictlyPositive.imageJOp,
        StrictlyPositive.contraction, StrictlyPositive.directCoreOperator] using this
    have hq := hsQForm_le_of_le hCnonneg X
    simpa [C] using hq

/-- Nonnegativity of the inverse ring-core operator is equivalent to the concrete Loewner-order
condition `InverseCompressedLE f Φ A B hPos hB hΦ1`. -/
theorem StrictlyPositive.inverseRingCoreOperatorNonneg_iff_le_concrete
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ) (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.InverseRingCoreOperatorNonneg f Φ A B hPos hB hΦ1 ↔
      StrictlyPositive.InverseCompressedLE f Φ A B hPos hB hΦ1 := by
  let C : HSOp (Nat.succ k) :=
    StrictlyPositive.inverseRingCoreOperator f Φ A B hPos hB hΦ1
  have hCself : IsSelfAdjoint C := by
    let TA : HSOp (Nat.succ k) := hsCfcR f (jArg A B)
    let TΦ : HSOp (Nat.succ l) := hsCfcR f (jArg (Φ A) (Φ B))
    let V : HSMap (Nat.succ l) (Nat.succ k) :=
      StrictlyPositive.contraction Φ hPos hB hΦ1
    have hTAself : IsSelfAdjoint TA := by
      simp [TA]
    have hTΦself : IsSelfAdjoint TΦ := by
      simp [TΦ]
    have hTAinvSelf : IsSelfAdjoint (Ring.inverse TA) := by
      calc
        star (Ring.inverse TA) = Ring.inverse (star TA) := (Ring.inverse_star TA).symm
        _ = Ring.inverse TA := congrArg Ring.inverse hTAself.star_eq
    have hTΦinvSelf : IsSelfAdjoint (Ring.inverse TΦ) := by
      calc
        star (Ring.inverse TΦ) = Ring.inverse (star TΦ) := (Ring.inverse_star TΦ).symm
        _ = Ring.inverse TΦ := congrArg Ring.inverse hTΦself.star_eq
    have hcompressedSelf : IsSelfAdjoint (inverseRectOp V TΦ) := by
      simpa [hsAdjoint] using hsAdjoint_inverseRectOp (V := V) (TΦ := TΦ) hTΦinvSelf
    simpa [C, StrictlyPositive.inverseRingCoreOperator, inverseRectOp, TA, TΦ, V,
      hsAdjoint] using hTAinvSelf.sub hcompressedSelf
  constructor
  · intro hquad
    have hCnonneg : (0 : HSOp (Nat.succ k)) ≤ C := by
      refine le_of_quadratic_form_nonneg ?_ ?_
      · simpa using hCself
      · intro X
        simpa [C, hsQForm_real_eq_inner_real] using hquad X
    apply sub_nonneg.mp
    simpa [C, StrictlyPositive.InverseCompressedLE,
      StrictlyPositive.sourceJOp, StrictlyPositive.imageJOp,
      StrictlyPositive.contraction, StrictlyPositive.inverseRingCoreOperator,
      hsAdjoint] using hCnonneg
  · intro hle X
    have hCnonneg : (0 : HSOp (Nat.succ k)) ≤ C := by
      have := sub_nonneg.mpr hle
      simpa [C, StrictlyPositive.InverseCompressedLE,
        StrictlyPositive.sourceJOp, StrictlyPositive.imageJOp,
        StrictlyPositive.contraction, StrictlyPositive.inverseRingCoreOperator,
        hsAdjoint] using this
    have hq := hsQForm_le_of_le hCnonneg X
    simpa [C] using hq

/-- The ring inverse `Ring.inverse (hsCfcR f (jArg A B))` is self-adjoint for the Hilbert–Schmidt
adjoint, for `f` continuous and strictly positive on `(0, ∞)`. -/
theorem ringInverse_cfcR_jArg_isSelfAdjoint
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    {n : ℕ} {A B : Mₙ n}
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B) :
    hsAdjoint (Ring.inverse (hsCfcR f (jArg A B))) =
      Ring.inverse (hsCfcR f (jArg A B)) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  have hInvEq : Ring.inverse (hsCfcR f (jArg A B)) =
      hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) := by
    simpa using (HiaiPetz.AmbientSubmodule.cfcR_inv_eq_ringInverse_of_jArg_posDef
      (f := f) hf hpos hA hB).symm
  have hAdjInvEq :
      hsAdjoint (Ring.inverse (hsCfcR f (jArg A B))) =
        hsAdjoint (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B)) := by
    simpa using congrArg hsAdjoint hInvEq
  have hsaInv :
      hsAdjoint (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B)) =
        hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) := by
    exact HiaiPetz.AmbientSubmodule.cfcR_jArg_isSelfAdjoint (f := fun x : ℝ ↦ (f x)⁻¹) hA hB
  calc
    hsAdjoint (Ring.inverse (hsCfcR f (jArg A B)))
        = hsAdjoint (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B)) := hAdjInvEq
    _ = hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) := hsaInv
    _ = Ring.inverse (hsCfcR f (jArg A B)) := by
          simpa using hInvEq.symm

/-- For `f` continuous and strictly positive on `(0, ∞)`, the ring inverse
`Ring.inverse (hsCfcR f (jArg A B))` is nonnegative. -/
theorem ringInverse_cfcR_jArg_nonneg
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    {n : ℕ} {A B : Mₙ n}
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B) :
    0 ≤ Ring.inverse (hsCfcR f (jArg A B)) := by
  rw [show Ring.inverse (hsCfcR f (jArg A B)) =
    hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) by
      simpa using (HiaiPetz.AmbientSubmodule.cfcR_inv_eq_ringInverse_of_jArg_posDef
        (f := f) hf hpos hA hB).symm]
  exact HiaiPetz.AmbientSubmodule.cfcR_jArg_nonneg
    (f := fun x : ℝ ↦ (f x)⁻¹)
    (hpos := by
      intro x hx
      exact inv_pos.mpr (hpos x hx))
    hA hB

/-- For `f` continuous and strictly positive on `(0, ∞)`, the J-operator `hsCfcR f (jArg A B)`
is a unit, with `Ring.inverse` as its two-sided inverse. -/
theorem cfcR_jArg_isUnit
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    {n : ℕ} {A B : Mₙ n}
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B) :
    IsUnit (hsCfcR f (jArg A B)) := by
  let T : HSOp n := hsCfcR f (jArg A B)
  change IsUnit T
  refine ⟨⟨T, Ring.inverse T, ?_, ?_⟩, rfl⟩
  · exact cfcR_mul_ringInverse_cfcR_eq_one_of_jArg_posDef
      (f := f) hf hpos hA hB
  · exact ringInverse_cfcR_mul_cfcR_eq_one_of_jArg_posDef
      (f := f) hf hpos hA hB

/-- Image-side counterpart: for a positive map `Φ`, the J-operator `hsCfcR f (jArg (Φ A) (Φ B))`
is a unit, with `Ring.inverse` as its two-sided inverse. -/
theorem cfcR_image_jArg_isUnit
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    IsUnit (hsCfcR f (jArg (Φ A) (Φ B))) := by
  let T : HSOp (Nat.succ l) := hsCfcR f (jArg (Φ A) (Φ B))
  change IsUnit T
  refine ⟨⟨T, Ring.inverse T, ?_, ?_⟩, rfl⟩
  · exact cfcR_mul_ringInverse_cfcR_eq_one_of_image_jArg_posDef
      (f := f) (Φ := Φ) hf hpos hPos hA hB hΦ1
  · exact ringInverse_cfcR_mul_cfcR_eq_one_of_image_jArg_posDef
      (f := f) (Φ := Φ) hf hpos hPos hA hB hΦ1

/-- The direct compressed operator on `Mₙ (l+1)`, namely `V* ∘ (hsCfcR f (jArg A B)) ∘
  V`, where
`V = contraction Φ hPos hB hΦ1` is the contraction map. -/
noncomputable def StrictlyPositive.directCompressedOperator
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) : HSOp (Nat.succ l) :=
  (hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)).comp
    ((hsCfcR f (jArg A B)).comp
      (StrictlyPositive.contraction Φ hPos hB hΦ1))

/-- The inverse ring-compressed operator on `Mₙ (k+1)`, namely
`V ∘ Ring.inverse (hsCfcR f (jArg (Φ A) (Φ B))) ∘ V*`, where `V = contraction Φ hPos hB
  hΦ1`. -/
noncomputable def StrictlyPositive.inverseRingCompressedOperator
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) : HSOp (Nat.succ k) :=
  (StrictlyPositive.contraction Φ hPos hB hΦ1).comp
    ((Ring.inverse (hsCfcR f (jArg (Φ A) (Φ B)))).comp
      (hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)))

/-- The direct compressed operator is self-adjoint for the Hilbert–Schmidt adjoint:
`hsAdjoint (directCompressedOperator ...) = directCompressedOperator ...`. -/
theorem StrictlyPositive.directCompressedOperator_isSelfAdjoint
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (_hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    hsAdjoint (StrictlyPositive.directCompressedOperator f Φ A B hPos hB hΦ1) =
      StrictlyPositive.directCompressedOperator f Φ A B hPos hB hΦ1 := by
  let TA : HSOp (Nat.succ k) :=
    hsCfcR f (jArg A B)
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  have hTA_sa : IsSelfAdjoint TA := by
    simp [TA]
  simpa [StrictlyPositive.directCompressedOperator, directRectOp, TA, V] using
    hsAdjoint_directRectOp (V := V) (TA := TA) hTA_sa

/-- The inverse ring-compressed operator is self-adjoint for the Hilbert–Schmidt adjoint,
for `f` continuous and strictly positive on `(0, ∞)`. -/
theorem StrictlyPositive.inverseRingCompressedOperator_isSelfAdjoint
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    hsAdjoint (StrictlyPositive.inverseRingCompressedOperator f Φ A B hPos hB hΦ1) =
      StrictlyPositive.inverseRingCompressedOperator f Φ A B hPos hB hΦ1 := by
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  let TΦ : HSOp (Nat.succ l) :=
    hsCfcR f (jArg (Φ A) (Φ B))
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  have hTΦinv_sa : IsSelfAdjoint (Ring.inverse TΦ) := by
    simpa [hsAdjoint, TΦ] using
      ringInverse_cfcR_jArg_isSelfAdjoint (f := f) hf hpos hΦA hΦB
  simpa [StrictlyPositive.inverseRingCompressedOperator, inverseRectOp, TΦ, V] using
    hsAdjoint_inverseRectOp (V := V) (TΦ := TΦ) hTΦinv_sa

/-- The strict-output direct standard condition `DirectStandard f Φ A B` is equivalent to the
operator-nonnegativity form `DirectCompressionOperatorNonneg f Φ A B hPos hB hΦ1`. -/
theorem StrictlyPositive.directStandard_iff_operatorNonneg
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.DirectStandard f Φ A B ↔
      StrictlyPositive.DirectCompressionOperatorNonneg f Φ A B hPos hB hΦ1 := by
  constructor
  · intro hDir
    exact ((StrictlyPositive.directCompression_iff_operatorNonneg
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).symm).mpr <|
      (StrictlyPositive.directStandard_iff_compression
        (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).mp hDir
  · intro hDir
    exact (StrictlyPositive.directStandard_iff_compression
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).mpr <|
      ((StrictlyPositive.directCompression_iff_operatorNonneg
        (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).symm).mp hDir

/-- The strict-output inverse standard condition `InverseStandard f Φ A B` is equivalent to the
operator-nonnegativity form `InverseCompressionOperatorNonneg f Φ A B hPos hB hΦ1`. -/
theorem StrictlyPositive.inverseStandard_iff_operatorNonneg
    (f : ℝ → ℝ)
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.InverseStandard f Φ A B ↔
      StrictlyPositive.InverseCompressionOperatorNonneg f Φ A B hPos hB hΦ1 := by
  constructor
  · intro hInv
    exact ((StrictlyPositive.inverseCompression_iff_operatorNonneg
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).symm).mpr <|
      (StrictlyPositive.inverseStandard_iff_compression
        (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).mp hInv
  · intro hInv
    exact (StrictlyPositive.inverseStandard_iff_compression
      (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).mpr <|
      ((StrictlyPositive.inverseCompression_iff_operatorNonneg
        (f := f) (Φ := Φ) (A := A) (B := B) hPos hB hΦ1).symm).mp hInv



end MatrixScopedInstances

end HiaiPetz
