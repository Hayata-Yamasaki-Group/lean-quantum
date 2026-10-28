/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.ShiftedCompression.AmbientDiagonalBasic
import Quantum.TraceInequality.HansenPedersen.Internal.ShiftedCompressionInstances
import Quantum.TraceInequality.HiaiPetz.MatrixPosDef
-- The imported module names above are indivisible tokens longer than the style limit.
set_option linter.style.longLine false

/-!
# Ambient diagonal compression operators

Compressions of the block-diagonal ambient operator to its codomain and domain factors:
`ambientFirstOperator` and `ambientSecondOperator`, together with their self-adjointness,
quadratic-form positivity, and identities relating them to the underlying `jArg` operators.
-/

namespace HiaiPetz
open Matrix Unitary
open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances
open scoped HiaiPetz.RectangularOperatorInstances
open ProofNetInternal.ShiftedCompressionInstances
noncomputable section MatrixScopedInstances

private noncomputable abbrev ambientJArgABINormedAddCommGroup {k l : ℕ} :
    NormedAddCommGroup (WithLp 2 (Mₙ l × Mₙ k)) :=
  WithLp.instProdNormedAddCommGroup (p := 2) (α := Mₙ l) (β := Mₙ k)

private noncomputable abbrev ambientJArgABIInnerProductSpace {k l : ℕ} :
    InnerProductSpace ℂ (WithLp 2 (Mₙ l × Mₙ k)) :=
  @WithLp.instProdInnerProductSpace ℂ (Mₙ l) (Mₙ k)
    inferInstance
    (instMatrixNormedAddCommGroup (n := l))
    (instMatrixInnerProductSpace (n := l))
    (instMatrixNormedAddCommGroup (n := k))
    (instMatrixInnerProductSpace (n := k))

/-- The ambient `jArg` operator on the `L²` pair space: the block-diagonal ambient operator
`ambientDiagOperator Φ A B` conjugated by the codomain-first off-diagonal contraction. -/
noncomputable def StrictlyPositive.ambientJArgOperator
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ) (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ 1)) :
    @HansenPedersen.L (WithLp 2 (Mₙ (Nat.succ l) × Mₙ (Nat.succ k)))
      (ambientJArgABINormedAddCommGroup (k := Nat.succ k) (l := Nat.succ l))
      (ambientJArgABIInnerProductSpace (k := Nat.succ k) (l := Nat.succ l)) :=
  star (StrictlyPositive.offDiagContractionCodomainFirstPair Φ hPos hB hΦ1) *
    StrictlyPositive.ambientDiagOperator Φ A B *
    StrictlyPositive.offDiagContractionCodomainFirstPair Φ hPos hB hΦ1

/-- Compression of the domain block `jArg A B` by the strict-output contraction `V`, i.e. the
codomain operator `V⋆ (jArg A B) V` on `HSOp (l+1)`. -/
noncomputable def StrictlyPositive.ambientFirstOperator
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ) (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ 1)) :
    HSOp (Nat.succ l) :=
  (hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)).comp
    ((jArg A B).comp (StrictlyPositive.contraction Φ hPos hB hΦ1))

/-- Compression of the codomain block `jArg (Φ A) (Φ B)` by the adjoint contraction `V⋆`,
  i.e. the
domain operator `V (jArg (Φ A) (Φ B)) V⋆` on `HSOp (k+1)`. -/
noncomputable def StrictlyPositive.ambientSecondOperator
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) (A B : Mₙ (Nat.succ k))
    (hPos : IsPositiveMap Φ) (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ 1)) :
    HSOp (Nat.succ k) :=
  (StrictlyPositive.contraction Φ hPos hB hΦ1).comp
    ((jArg (Φ A) (Φ B)).comp (hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)))

/-- The ambient `jArg` operator is block-diagonal: it equals `diagMapCLMRectHs` of the codomain
compression `ambientFirstOperator` and the domain compression `ambientSecondOperator`. -/
theorem StrictlyPositive.ambientJArgOperator_eq_diagMapCLM
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    StrictlyPositive.ambientJArgOperator Φ A B hPos hB hΦ1 =
      diagMapCLMRectHs (k := l) (l := k)
        (StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1)
        (StrictlyPositive.ambientSecondOperator Φ A B hPos hB hΦ1) := by
  simpa [StrictlyPositive.ambientJArgOperator, StrictlyPositive.ambientDiagOperator,
    StrictlyPositive.ambientFirstOperator, StrictlyPositive.ambientSecondOperator] using
    StrictlyPositive.offDiagContractionCodomainFirst_star_mul_jArg_diagMapCLM
      (Φ := Φ) (A := A) (B := B) hPos hA hB hΦ1

/-- The codomain compression `ambientFirstOperator` is self-adjoint. -/
theorem StrictlyPositive.ambientFirstOperator_isSelfAdjoint
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    hsAdjoint (StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1) =
      StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1 := by
  let J : HSOp (Nat.succ k) := jArg A B
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  have hJ : hsAdjoint J = J := by
    simpa [J, hsAdjoint] using jArg_isSelfAdjoint (A := A) (B := B) hA.1 hB
  have hV : hsAdjoint (hsAdjoint V) = V := by
    simp [hsAdjoint]
  calc
    hsAdjoint (StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1)
        = (hsAdjoint (J.comp V)).comp (hsAdjoint (hsAdjoint V)) := by
          dsimp [StrictlyPositive.ambientFirstOperator, J, V, hsAdjoint]
          exact
            (@ContinuousLinearMap.adjoint_comp ℂ (Mₙ (Nat.succ l)) (Mₙ (Nat.succ k))
              (Mₙ (Nat.succ l))
              (inferInstance : RCLike ℂ)
              (instMatrixNormedAddCommGroup (n := Nat.succ l))
              (instMatrixNormedAddCommGroup (n := Nat.succ k))
              (instMatrixNormedAddCommGroup (n := Nat.succ l))
              (instMatrixInnerProductSpace (n := Nat.succ l))
              (instMatrixInnerProductSpace (n := Nat.succ k))
              (instMatrixInnerProductSpace (n := Nat.succ l))
              (instMatrixCompleteSpace (n := Nat.succ l))
              (instMatrixCompleteSpace (n := Nat.succ l))
              (instMatrixCompleteSpace (n := Nat.succ k))
              (hsAdjoint V) (J.comp V))
    _ = ((hsAdjoint V).comp (hsAdjoint J)).comp (hsAdjoint (hsAdjoint V)) := by
          rw [show hsAdjoint (J.comp V) = (hsAdjoint V).comp (hsAdjoint J) by
            dsimp [hsAdjoint]
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
                J V)]
    _ = StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1 := by
          rw [hV, hJ, ContinuousLinearMap.comp_assoc]
          rfl

/-- The domain compression `ambientSecondOperator` is self-adjoint. -/
theorem StrictlyPositive.ambientSecondOperator_isSelfAdjoint
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) :
    hsAdjoint (StrictlyPositive.ambientSecondOperator Φ A B hPos hB hΦ1) =
      StrictlyPositive.ambientSecondOperator Φ A B hPos hB hΦ1 := by
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  let J : HSOp (Nat.succ l) := jArg (Φ A) (Φ B)
  let V : HSMap (Nat.succ l) (Nat.succ k) := StrictlyPositive.contraction Φ hPos hB hΦ1
  have hJ : hsAdjoint J = J := by
    simpa [J, hsAdjoint] using jArg_isSelfAdjoint (A := Φ A) (B := Φ B) hΦA.1 hΦB
  have hV : hsAdjoint (hsAdjoint V) = V := by
    simp [hsAdjoint]
  calc
    hsAdjoint (StrictlyPositive.ambientSecondOperator Φ A B hPos hB hΦ1)
        = (hsAdjoint (J.comp (hsAdjoint V))).comp (hsAdjoint V) := by
          dsimp [StrictlyPositive.ambientSecondOperator, J, V, hsAdjoint]
          exact
            (@ContinuousLinearMap.adjoint_comp ℂ (Mₙ (Nat.succ k)) (Mₙ (Nat.succ l))
              (Mₙ (Nat.succ k))
              (inferInstance : RCLike ℂ)
              (instMatrixNormedAddCommGroup (n := Nat.succ k))
              (instMatrixNormedAddCommGroup (n := Nat.succ l))
              (instMatrixNormedAddCommGroup (n := Nat.succ k))
              (instMatrixInnerProductSpace (n := Nat.succ k))
              (instMatrixInnerProductSpace (n := Nat.succ l))
              (instMatrixInnerProductSpace (n := Nat.succ k))
              (instMatrixCompleteSpace (n := Nat.succ k))
              (instMatrixCompleteSpace (n := Nat.succ k))
              (instMatrixCompleteSpace (n := Nat.succ l))
              V (J.comp (hsAdjoint V)))
    _ = ((hsAdjoint (hsAdjoint V)).comp (hsAdjoint J)).comp (hsAdjoint V) := by
          rw [show hsAdjoint (J.comp (hsAdjoint V)) =
              (hsAdjoint (hsAdjoint V)).comp (hsAdjoint J) by
            dsimp [hsAdjoint]
            exact
              (@ContinuousLinearMap.adjoint_comp ℂ (Mₙ (Nat.succ k)) (Mₙ (Nat.succ l))
                (Mₙ (Nat.succ l))
                (inferInstance : RCLike ℂ)
                (instMatrixNormedAddCommGroup (n := Nat.succ k))
                (instMatrixNormedAddCommGroup (n := Nat.succ l))
                (instMatrixNormedAddCommGroup (n := Nat.succ l))
                (instMatrixInnerProductSpace (n := Nat.succ k))
                (instMatrixInnerProductSpace (n := Nat.succ l))
                (instMatrixInnerProductSpace (n := Nat.succ l))
                (instMatrixCompleteSpace (n := Nat.succ k))
                (instMatrixCompleteSpace (n := Nat.succ l))
                (instMatrixCompleteSpace (n := Nat.succ l))
                J (hsAdjoint V))]
    _ = StrictlyPositive.ambientSecondOperator Φ A B hPos hB hΦ1 := by
          rw [hV, hJ, ContinuousLinearMap.comp_assoc]
          rfl

/-- Nonnegativity of the `ambientFirstOperator` quadratic form:
`0 ≤ Re (tr (X⋆ · ambientFirstOperator X))` for every `X`. -/
theorem StrictlyPositive.ambientFirstOperator_trace_nonneg
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) (X : Mₙ (Nat.succ l)) :
    0 ≤
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1) X))) := by
  have hcomp :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1) X))) =
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
              ((jArg A B) (StrictlyPositive.contraction Φ hPos hB hΦ1 X)))) := by
    simpa [StrictlyPositive.ambientFirstOperator] using
      hsQForm_hsAdjoint_comp
        (StrictlyPositive.contraction Φ hPos hB hΦ1)
        (jArg A B)
        X
  rw [hcomp]
  simpa using hsQForm_le_of_le
    (jArg_nonneg (A := A) (B := B) (Matrix.PosDef.nonneg hA) hB)
    (StrictlyPositive.contraction Φ hPos hB hΦ1 X)

/-- Nonnegativity of the `ambientSecondOperator` quadratic form:
`0 ≤ Re (tr (X⋆ · ambientSecondOperator X))` for every `X`. -/
theorem StrictlyPositive.ambientSecondOperator_trace_nonneg
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1)) (X : Mₙ (Nat.succ k)) :
    0 ≤
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.ambientSecondOperator Φ A B hPos hB hΦ1) X))) := by
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hΦB : Matrix.PosDef (Φ B) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hB hΦ1
  have hcomp :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((StrictlyPositive.ambientSecondOperator Φ A B hPos hB hΦ1) X))) =
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose
                (hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1) X) *
              ((jArg (Φ A) (Φ B)) (hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1) X))))
                := by
    simpa [StrictlyPositive.ambientSecondOperator] using
      hsQForm_comp_hsAdjoint
        (StrictlyPositive.contraction Φ hPos hB hΦ1)
        (jArg (Φ A) (Φ B))
        X
  rw [hcomp]
  simpa using hsQForm_le_of_le
    (jArg_nonneg (A := Φ A) (B := Φ B) (Matrix.PosDef.nonneg hΦA) hΦB)
    (hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1) X)

/-- The `ambientFirstOperator` quadratic form at `X` equals the `jArg A B` quadratic form at the
contracted vector `contraction Φ … X`. -/
theorem StrictlyPositive.ambientFirstOperator_qform_eq_jArg_qform
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ l)) :
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1) X))) =
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose (StrictlyPositive.contraction Φ hPos hB hΦ1 X) *
            ((jArg A B) (StrictlyPositive.contraction Φ hPos hB hΦ1 X)))) := by
  simpa [StrictlyPositive.ambientFirstOperator] using
    hsQForm_hsAdjoint_comp (StrictlyPositive.contraction Φ hPos hB hΦ1) (jArg A B) X

/-- The `ambientFirstOperator` quadratic form at `X` rewritten through the adjoint map: it equals
`Re (tr (Z⋆ · (A Z)))` with `Z = Φ⋆ (X · matrixInvSqrtPos (Φ B))`. -/
theorem StrictlyPositive.ambientFirstOperator_qform_eq_hsAdjointImage_qform
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ l)) :
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1) X))) =
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose ((hsAdjoint Φ) (X * matrixInvSqrtPos (Φ B))) *
            (A * ((hsAdjoint Φ) (X * matrixInvSqrtPos (Φ B)))))) := by
  let Z : Mₙ (Nat.succ k) := (hsAdjoint Φ) (X * matrixInvSqrtPos (Φ B))
  have hq :=
    StrictlyPositive.ambientFirstOperator_qform_eq_jArg_qform
      (Φ := Φ) (A := A) (B := B) hPos hB hΦ1 X
  rw [StrictlyPositive.contraction_apply] at hq
  have hsqrt_star : Matrix.conjTranspose (matrixSqrtPos B) = matrixSqrtPos B := by
    exact (HiaiPetz.OffDiagonalCore.matrixPosDef_sqrt hB).isHermitian
  have hinv_eq :
      B⁻¹ = matrixInvSqrtPos B * matrixInvSqrtPos B := by
    simpa using (matrixInvSqrtPos_mul_self hB).symm
  have hsqrt_inv :
      matrixSqrtPos B * B⁻¹ = matrixInvSqrtPos B := by
    calc
      matrixSqrtPos B * B⁻¹
          = matrixSqrtPos B * (matrixInvSqrtPos B * matrixInvSqrtPos B) := by
              rw [hinv_eq]
      _ = (matrixSqrtPos B * matrixInvSqrtPos B) * matrixInvSqrtPos B := by
            simp [Matrix.mul_assoc]
      _ = matrixInvSqrtPos B := by
            simp [matrixSqrtPos_mul_matrixInvSqrtPos hB]
  calc
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.ambientFirstOperator Φ A B hPos hB hΦ1) X)))
      = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose (Z * matrixSqrtPos B) *
              (A * (Z * matrixSqrtPos B) * B⁻¹))) := by
              simpa [Z, jArg_apply] using hq
    _ = Complex.re
          (Matrix.trace
            (((matrixSqrtPos B * Matrix.conjTranspose Z) * A * Z) * matrixInvSqrtPos B)) := by
              simp [Matrix.mul_assoc, hsqrt_star, hsqrt_inv]
    _ = Complex.re
          (Matrix.trace
            (matrixInvSqrtPos B * ((matrixSqrtPos B * Matrix.conjTranspose Z) * A * Z))) := by
              rw [Matrix.trace_mul_comm]
    _ = Complex.re
          (Matrix.trace
            ((((matrixInvSqrtPos B * matrixSqrtPos B) * Matrix.conjTranspose Z) * A) * Z)) := by
              simp [Matrix.mul_assoc]
    _ = Complex.re
          (Matrix.trace (Matrix.conjTranspose Z * (A * Z))) := by
              simp [Matrix.mul_assoc, matrixInvSqrtPos_mul_matrixSqrtPos hB]
    _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose ((hsAdjoint Φ) (X * matrixInvSqrtPos (Φ B))) *
              (A * ((hsAdjoint Φ) (X * matrixInvSqrtPos (Φ B)))))) := by
              simp [Z]

/-- The `ambientSecondOperator` quadratic form at `X` equals the `jArg (Φ A) (Φ B)` quadratic form
at the adjoint-contracted vector `(contraction Φ …)⋆ X`. -/
theorem StrictlyPositive.ambientSecondOperator_qform_eq_jArg_qform
    {k l : ℕ} (Φ : HSMap (Nat.succ k) (Nat.succ l)) {A B : Mₙ (Nat.succ k)}
    (hPos : IsPositiveMap Φ)
    (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ 1))
    (X : Mₙ (Nat.succ k)) :
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            ((StrictlyPositive.ambientSecondOperator Φ A B hPos hB hΦ1) X))) =
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose
              ((hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)) X) *
            ((jArg (Φ A) (Φ B)) ((hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1)) X))))
              := by
  simpa [StrictlyPositive.ambientSecondOperator] using
    hsQForm_comp_hsAdjoint (StrictlyPositive.contraction Φ hPos hB hΦ1) (jArg (Φ A) (Φ B)) X

end MatrixScopedInstances

end HiaiPetz
