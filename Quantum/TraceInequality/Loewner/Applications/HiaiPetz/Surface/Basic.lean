/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Topology.Algebra.Module.LinearMap
import Quantum.TraceInequality.HiaiPetz.MatrixHilbert

/-!
# Hiai--Petz strict-output statement interface for the Loewner route

This file contains only theorem-facing definitions needed to state the
strict-output Hiai--Petz data-processing inequalities.  It deliberately avoids
importing the existing Hiai--Petz proof route.  The Hiai--Petz condition (i)
compatibility name is kept in `Surface.ConditionICompat`, so this core file
does not depend on matrix-CFC monotonicity plumbing.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

universe u

open Matrix
open scoped MatrixOrder CStarAlgebra Matrix.Norms.Frobenius ComplexOrder

noncomputable section

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

/-- Hilbert--Schmidt operators on `Mₙ n`. -/
noncomputable abbrev HSOp (n : ℕ) : Type :=
  _root_.HiaiPetz.HSOp n


/-- The Hilbert--Schmidt operator algebra `HSOp n` is a C⋆-algebra. -/
noncomputable local instance instHSOpCStarAlgebra {n : ℕ} : CStarAlgebra (HSOp n) :=
  @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace (Mₙ n)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (instMatrixCompleteSpace (n := n))

/-- `HSOp n` has a complex continuous functional calculus for star-normal elements. -/
noncomputable local instance instHSOpComplexCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℂ (HSOp n) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

/-- `HSOp n` has a real continuous functional calculus for self-adjoint elements. -/
local instance instHSOpRealCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℝ (HSOp n) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- Real continuous functional calculus on Hilbert--Schmidt operators. -/
noncomputable abbrev hsCfcR {n : ℕ} (f : ℝ → ℝ) (T : HSOp n) : HSOp n :=
  _root_.HiaiPetz.hsCfcR f T

/-- Positive-definite matrices used in the strict-output statements. -/
def MatrixPosDef {n : ℕ} (A : Mₙ n) : Prop :=
  IsSelfAdjoint A ∧
    ∀ x : Fin n → ℂ, x ≠ 0 → 0 < Complex.re (dotProduct (star x) (A.mulVec x))

/-- The theorem-facing positive-definite predicate implies Mathlib's matrix predicate. -/
theorem matrixPosDef_posDef {n : ℕ} {A : Mₙ n} (hA : MatrixPosDef A) :
    A.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hA.1.isHermitian ?_
  intro x hx
  have hre := hA.2 x hx
  have him := Matrix.IsHermitian.im_star_dotProduct_mulVec_self hA.1.isHermitian x
  rw [RCLike.pos_iff]
  exact ⟨hre, him⟩

/-- The theorem-facing positive-definite predicate agrees with Mathlib's matrix predicate. -/
theorem matrixPosDef_iff_posDef {n : ℕ} {A : Mₙ n} :
    MatrixPosDef A ↔ A.PosDef := by
  constructor
  · exact matrixPosDef_posDef
  · intro hA
    refine ⟨hA.isHermitian.isSelfAdjoint, fun x hx => ?_⟩
    exact (RCLike.pos_iff.mp (hA.dotProduct_mulVec_pos hx)).1

/-- The theorem-facing positive-definite predicate gives invertibility. -/
theorem matrixPosDef_isUnit {n : ℕ} {A : Mₙ n} (hA : MatrixPosDef A) :
    IsUnit A :=
  (matrixPosDef_posDef hA).isUnit

/-- Positivity on the Hilbert--Schmidt matrix space, encoded by quadratic forms. -/
def HSNonneg {n : ℕ} (T : HSOp n) : Prop :=
  ∀ X : Mₙ n, 0 ≤ Complex.re (Matrix.trace (Matrix.conjTranspose X * T X))

/-- Hilbert--Schmidt quadratic form associated to an operator. -/
noncomputable def hsQF {n : ℕ} (T : HSOp n) (Z : Mₙ n) : ℝ :=
  Complex.re (Matrix.trace (Matrix.conjTranspose Z * T Z))

/-- Conjugating a Hilbert--Schmidt operator by matrix conjugate transpose. -/
noncomputable def conjTransposeConjHSOp {n : ℕ} (T : HSOp n) : HSOp n :=
  ({ toFun := fun Z ↦ Matrix.conjTranspose (T (Matrix.conjTranspose Z))
     map_add' := by
       intro X Y
       simp
     map_smul' := by
       intro z X
       simp } : Mₙ n →ₗ[ℂ] Mₙ n).toContinuousLinearMap

/-- The conjugate-transpose conjugation operator acts by conjugating input and output. -/
@[simp]
theorem conjTransposeConjHSOp_apply {n : ℕ} (T : HSOp n) (Z : Mₙ n) :
    conjTransposeConjHSOp T Z = Matrix.conjTranspose (T (Matrix.conjTranspose Z)) :=
  rfl

/-- Order on Hilbert--Schmidt operators, encoded through positivity of the difference. -/
def HSLE {n : ℕ} (S T : HSOp n) : Prop :=
  HSNonneg (T - S)


/-- Left multiplication on the Hilbert--Schmidt matrix space. -/
noncomputable abbrev leftMul {n : ℕ} (A : Mₙ n) : HSOp n :=
  _root_.HiaiPetz.leftMul A

/-- Right multiplication on the Hilbert--Schmidt matrix space. -/
noncomputable abbrev rightMul {n : ℕ} (B : Mₙ n) : HSOp n :=
  _root_.HiaiPetz.rightMul B

/-- The matrix inverse used in the strict positive-definite regime. -/
noncomputable def posInv {n : ℕ} (B : Mₙ n) : Mₙ n :=
  B⁻¹

/-- The inverse of a theorem-facing positive-definite matrix is positive-definite. -/
theorem matrixPosDef_posInv_posDef {n : ℕ} {B : Mₙ n} (hB : MatrixPosDef B) :
    (posInv B).PosDef := by
  classical
  simpa [posInv] using (matrixPosDef_posDef hB).inv

/-- The positive argument `L_A R_{B^{-1}}` of `J_f(A,B)`. -/
noncomputable abbrev jArg {n : ℕ} (A B : Mₙ n) : HSOp n :=
  _root_.HiaiPetz.jArg A B

/-- Hiai--Petz perspective operator `J_f(A,B) = f(L_A R_{B^{-1}}) R_B`. -/
noncomputable abbrev jOperator {n : ℕ} (f : ℝ → ℝ) (A B : Mₙ n) : HSOp n :=
  _root_.HiaiPetz.jOperator f A B

/-- Inverse perspective operator used in the strict inverse inequality. -/
noncomputable abbrev jOperatorInv {n : ℕ} (f : ℝ → ℝ) (A B : Mₙ n) : HSOp n :=
  _root_.HiaiPetz.jOperatorInv f A B

/-- Carlen's positive argument `R_X L_{Y^{-1}}` of `G_f(X,Y)`. -/
noncomputable def gArg {n : ℕ} (X Y : Mₙ n) : HSOp n :=
  (rightMul X).comp (leftMul (posInv Y))

/-- Carlen perspective operator `G_f(X,Y) = f(R_X L_{Y^{-1}}) L_Y`. -/
noncomputable def gOperator {n : ℕ} (f : ℝ → ℝ) (X Y : Mₙ n) : HSOp n :=
  hsCfcR f (gArg X Y) * leftMul Y

/-- The theorem-facing inverse of Carlen's perspective operator. -/
noncomputable def gOperatorInv {n : ℕ} (f : ℝ → ℝ) (X Y : Mₙ n) : HSOp n :=
  hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (gArg X Y) * leftMul (posInv Y)

/-- Quadratic form associated to the theorem-facing inverse of `G_f`. -/
noncomputable def gInvQF {n : ℕ} (f : ℝ → ℝ) (X Y Z : Mₙ n) : ℝ :=
  hsQF (gOperatorInv f X Y) Z

/--
If two Hilbert--Schmidt operators are intertwined by matrix conjugate
transpose, their quadratic forms agree after conjugate-transposing the vector.
-/
theorem hsQF_eq_hsQF_conjTranspose_of_conjTranspose_apply {n : ℕ}
    {TG TJ : HSOp n}
    (h : ∀ Z : Mₙ n,
      Matrix.conjTranspose (TG Z) = TJ (Matrix.conjTranspose Z))
    (Z : Mₙ n) :
    hsQF TG Z = hsQF TJ (Matrix.conjTranspose Z) := by
  let W : Mₙ n := TJ (Matrix.conjTranspose Z)
  have hTG : TG Z = Matrix.conjTranspose W := by
    have hstar := congrArg Matrix.conjTranspose (h Z)
    simpa [W] using hstar
  have htrace :
      Matrix.trace (Matrix.conjTranspose Z * Matrix.conjTranspose W) =
        star (Matrix.trace (W * Z)) := by
    simpa [Matrix.conjTranspose_mul] using Matrix.trace_conjTranspose (W * Z)
  calc
    hsQF TG Z
        = Complex.re (Matrix.trace (Matrix.conjTranspose Z * Matrix.conjTranspose W)) := by
            simp [hsQF, hTG, W]
    _ = Complex.re (star (Matrix.trace (W * Z))) := by rw [htrace]
    _ = Complex.re (Matrix.trace (W * Z)) := by simp
    _ = Complex.re (Matrix.trace (Z * W)) := by rw [Matrix.trace_mul_comm]
    _ = hsQF TJ (Matrix.conjTranspose Z) := by
          simp [hsQF, W]

/-- Conjugate transpose turns Carlen's `gArg` convention into the `jArg` convention. -/
theorem gArg_conjTranspose_eq_jArg_conjTranspose {n : ℕ}
    {A B Z : Mₙ n} (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    Matrix.conjTranspose ((gArg A B) Z) =
      (jArg A B) (Matrix.conjTranspose Z) := by
  have hBInv_sa : IsSelfAdjoint (posInv B) :=
    (matrixPosDef_posInv_posDef hB).1
  have hA_ct : Matrix.conjTranspose A = A := by
    simpa [Matrix.star_eq_conjTranspose] using hA.1.star_eq
  have hBInv_ct : Matrix.conjTranspose (posInv B) = posInv B := by
    simpa [Matrix.star_eq_conjTranspose] using hBInv_sa.star_eq
  change Matrix.conjTranspose (((posInv B) * Z) * A) =
    (A * Matrix.conjTranspose Z) * posInv B
  calc
    Matrix.conjTranspose (((posInv B) * Z) * A)
        = Matrix.conjTranspose A * Matrix.conjTranspose ((posInv B) * Z) := by
            rw [Matrix.conjTranspose_mul]
    _ = A * (Matrix.conjTranspose Z * Matrix.conjTranspose (posInv B)) := by
          rw [Matrix.conjTranspose_mul, hA_ct]
    _ = A * (Matrix.conjTranspose Z * posInv B) := by
          rw [hBInv_ct]
    _ = (A * Matrix.conjTranspose Z) * posInv B := by
          rw [Matrix.mul_assoc]

/--
The positive arguments of the `G_f` and `J_f` conventions have the same
Hilbert--Schmidt quadratic form after conjugate-transposing the test matrix.
-/
theorem gArg_qform_eq_jArg_qform_star {n : ℕ}
    {A B Z : Mₙ n} (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    hsQF (gArg A B) Z = hsQF (jArg A B) (Matrix.conjTranspose Z) :=
  hsQF_eq_hsQF_conjTranspose_of_conjTranspose_apply
    (fun W => gArg_conjTranspose_eq_jArg_conjTranspose (A := A) (B := B) (Z := W) hA hB)
    Z

/-- Operator-level form of the `gArg`/`jArg` star convention bridge. -/
theorem conjTransposeConjHSOp_gArg_eq_jArg {n : ℕ}
    {A B : Mₙ n} (hA : MatrixPosDef A) (hB : MatrixPosDef B) :
    conjTransposeConjHSOp (gArg A B) = jArg A B := by
  apply ContinuousLinearMap.ext
  intro Z
  simpa using
    (gArg_conjTranspose_eq_jArg_conjTranspose
      (A := A) (B := B) (Z := Matrix.conjTranspose Z) hA hB)

/--
If the real functional calculi of `gArg A B` and `jArg A B` are intertwined by
conjugate transpose, then the same intertwining holds for the full direct
perspective operators.
-/
theorem gOperator_conjTranspose_eq_jOperator_conjTranspose_of_hsCfcR_intertwines {n : ℕ}
    {f : ℝ → ℝ} {A B Z : Mₙ n} (hB : MatrixPosDef B)
    (hCfc : ∀ W : Mₙ n,
      Matrix.conjTranspose ((hsCfcR f (gArg A B)) W) =
        (hsCfcR f (jArg A B)) (Matrix.conjTranspose W)) :
    Matrix.conjTranspose ((gOperator f A B) Z) =
      (jOperator f A B) (Matrix.conjTranspose Z) := by
  have hB_ct : Matrix.conjTranspose B = B := by
    simpa [Matrix.star_eq_conjTranspose] using hB.1.star_eq
  change Matrix.conjTranspose ((hsCfcR f (gArg A B)) (B * Z)) =
    (hsCfcR f (jArg A B)) (Matrix.conjTranspose Z * B)
  rw [hCfc]
  congr 1
  rw [Matrix.conjTranspose_mul, hB_ct]

/--
If the real functional calculi of `gArg A B` and `jArg A B` are intertwined by
conjugate transpose, then the same intertwining holds for the theorem-facing
inverse perspective operators.
-/
theorem gOperatorInv_conjTranspose_eq_jOperatorInv_conjTranspose_of_hsCfcR_intertwines {n : ℕ}
    {f : ℝ → ℝ} {A B Z : Mₙ n} (hB : MatrixPosDef B)
    (hCfc : ∀ W : Mₙ n,
      Matrix.conjTranspose ((hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (gArg A B)) W) =
        (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B)) (Matrix.conjTranspose W)) :
    Matrix.conjTranspose ((gOperatorInv f A B) Z) =
      (jOperatorInv f A B) (Matrix.conjTranspose Z) := by
  have hBInv_ct : Matrix.conjTranspose (posInv B) = posInv B := by
    simpa using (matrixPosDef_posInv_posDef hB).1
  change Matrix.conjTranspose
      ((hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (gArg A B)) (posInv B * Z)) =
    (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B)) (Matrix.conjTranspose Z * posInv B)
  rw [hCfc]
  congr 1
  rw [Matrix.conjTranspose_mul, hBInv_ct]

/--
The direct `G_f` and `J_f` quadratic forms agree under star once the
corresponding CFC arguments are known to be star-intertwined.
-/
theorem gOperator_qform_eq_jOperator_qform_star_of_hsCfcR_intertwines {n : ℕ}
    {f : ℝ → ℝ} {A B Z : Mₙ n} (hB : MatrixPosDef B)
    (hCfc : ∀ W : Mₙ n,
      Matrix.conjTranspose ((hsCfcR f (gArg A B)) W) =
        (hsCfcR f (jArg A B)) (Matrix.conjTranspose W)) :
    hsQF (gOperator f A B) Z = hsQF (jOperator f A B) (Matrix.conjTranspose Z) :=
  hsQF_eq_hsQF_conjTranspose_of_conjTranspose_apply
    (fun W => gOperator_conjTranspose_eq_jOperator_conjTranspose_of_hsCfcR_intertwines
      (f := f) (A := A) (B := B) (Z := W) hB hCfc)
    Z

/--
The inverse `G_f` and `J_f` quadratic forms agree under star once the
corresponding inverse-CFC arguments are known to be star-intertwined.
-/
theorem gOperatorInv_qform_eq_jOperatorInv_qform_star_of_hsCfcR_intertwines {n : ℕ}
    {f : ℝ → ℝ} {A B Z : Mₙ n} (hB : MatrixPosDef B)
    (hCfc : ∀ W : Mₙ n,
      Matrix.conjTranspose ((hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (gArg A B)) W) =
        (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B)) (Matrix.conjTranspose W)) :
    hsQF (gOperatorInv f A B) Z =
      hsQF (jOperatorInv f A B) (Matrix.conjTranspose Z) :=
  hsQF_eq_hsQF_conjTranspose_of_conjTranspose_apply
    (fun W => gOperatorInv_conjTranspose_eq_jOperatorInv_conjTranspose_of_hsCfcR_intertwines
      (f := f) (A := A) (B := B) (Z := W) hB hCfc)
    Z

/-- Positivity of a Hilbert--Schmidt linear map on matrix positive semidefinite
elements. -/
abbrev IsPositiveMap {n m : ℕ} (Φ : HSMap n m) : Prop :=
  _root_.HiaiPetz.IsPositiveMap Φ

/-- Schwarz inequality for the Hilbert--Schmidt adjoint. -/
abbrev HSAdjointSchwarz {n m : ℕ} (Φ : HSMap n m) : Prop :=
  _root_.HiaiPetz.HSAdjointSchwarz Φ

/-- Strict-output inverse inequality: Hiai, Theorem 6.2, condition (ii), for positive
trace-preserving maps whose Hilbert--Schmidt adjoint satisfies the Schwarz inequality, with the
additional assumption `Φ(1) > 0`. -/
def ConditionII_strict (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {A B : Mₙ n},
    _root_.HiaiPetz.IsPositiveMap Φ →
    _root_.HiaiPetz.TracePreserving Φ →
    _root_.HiaiPetz.HSAdjointSchwarz Φ →
    MatrixPosDef A →
    MatrixPosDef B →
    MatrixPosDef (Φ (1 : Mₙ n)) →
    HSLE
      ((hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ))
      (jOperatorInv f A B)

/-- Strict-output direct inequality: Hiai, Theorem 6.2, condition (iii), for positive
trace-preserving maps whose Hilbert--Schmidt adjoint satisfies the Schwarz inequality, with the
additional assumption `Φ(1) > 0`. -/
def ConditionIII_strict (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {A B : Mₙ n},
    _root_.HiaiPetz.IsPositiveMap Φ →
    _root_.HiaiPetz.TracePreserving Φ →
    _root_.HiaiPetz.HSAdjointSchwarz Φ →
    MatrixPosDef A →
    MatrixPosDef B →
    MatrixPosDef (Φ (1 : Mₙ n)) →
    HSLE
      (Φ.comp ((jOperator f A B).comp (hsAdjoint Φ)))
      (jOperator f (Φ A) (Φ B))

end

end Quantum.TraceInequality.Loewner.HiaiPetz
