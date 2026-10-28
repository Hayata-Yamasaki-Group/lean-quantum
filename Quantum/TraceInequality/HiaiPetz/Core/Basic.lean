/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.OperatorCore
import Quantum.TraceInequality.HiaiPetz.Core.MatrixType
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Topology.Algebra.Module.LinearMap

/-!
# Core matrix and Hilbert-Schmidt structures for Hiai-Petz

This file fixes the matrix type, Frobenius Hilbert-space structure, and basic
Hilbert-Schmidt operator algebra used in the Chapter 6.1 quasi-entropy
development. It also defines left and right multiplication, the strict-regime
inverse, the operator `J_f(A,B)`, and the associated quasi-entropy quadratic
form.

## Main results

* `Matrix.PosDef`: Mathlib's positive-definite matrix predicate, used directly
  for Hiai-Petz inputs.
* `ContinuousLinearMap.IsPositive`, the Loewner order on continuous linear
  maps, and `IsStrictlyPositive`: the standard positivity APIs used for
  operators on the Hilbert-Schmidt matrix space.
* `leftMul`, `rightMul`, `jArg`, `jOperator`, and `quasiEntropy`: the basic
  algebraic objects of Definition 6.1.
* `hsAdjoint_leftMul`, `hsAdjoint_rightMul`, `leftMul_nonneg`, and
  `rightMul_nonneg`: adjoint and positivity facts used by later `J_f` proofs.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Chapter 6, Definition 6.1.
-/

namespace HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder

/-
The four matrix instances below are the single source of truth for the
Hilbert-Schmidt (Frobenius) analytic structure on `Mₙ n` used throughout the
HiaiPetz development.  They are `scoped` (following the Mathlib convention that
matrix norms are opt-in) and are automatically active inside `namespace
HiaiPetz`.  Crucially, `Matrix.Norms.Frobenius` is *not* opened here, so the
`SeminormedAddCommGroup` index of `instMatrixNormedSpace` and
`instMatrixInnerProductSpace` resolves through
`instMatrixNormedAddCommGroup.toSeminormedAddCommGroup`, matching the index
that downstream goals carry.
-/

/-- Scoped Frobenius normed additive-group structure on complex matrices. This
keeps the Hilbert-Schmidt norm opt-in while making it available inside the
Hiai-Petz namespace. -/
noncomputable scoped instance instMatrixNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup (Mₙ n) :=
  Matrix.frobeniusNormedAddCommGroup

/-- Scoped complex normed-space structure for matrices with the Frobenius norm. -/
noncomputable scoped instance instMatrixNormedSpace {n : ℕ} : NormedSpace ℂ (Mₙ n) :=
  Matrix.frobeniusNormedSpace

private lemma hs_trace_eq_sum_normSq {n : ℕ} (A : Mₙ n) :
    Matrix.trace (A * Matrix.conjTranspose A) = ∑ i, ∑ j, Complex.ofReal (‖A i j‖ ^ 2) := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, RCLike.mul_conj]

private lemma hs_re_trace_eq_sum_normSq {n : ℕ} (A : Mₙ n) :
    Complex.re (Matrix.trace (A * Matrix.conjTranspose A)) = Complex.re
      (∑ i, ∑ j, Complex.ofReal (‖A i j‖ ^ 2)) := by
  exact congrArg Complex.re (hs_trace_eq_sum_normSq A)

/-- Scoped Frobenius inner-product structure on matrices, with inner product
`trace (Y * Xᴴ)`. This is the Hilbert-Schmidt structure used for adjoints and
quadratic forms. -/
noncomputable scoped instance instMatrixInnerProductSpace {n : ℕ} :
    InnerProductSpace ℂ (Mₙ n) where
  inner x y := Matrix.trace (y * Matrix.conjTranspose x)
  norm_sq_eq_re_inner x := by
    let s : ℝ := ∑ i, ∑ j, ‖x i j‖ ^ (2 : ℝ)
    have hnonneg : 0 ≤ s := by
      dsimp [s]
      positivity
    have hsReal' :
        Complex.re (∑ i, ∑ j, Complex.ofReal (‖x i j‖ ^ 2)) =
          ∑ i, ∑ j, ‖x i j‖ ^ (2 : ℝ) := by
      change Complex.reAddGroupHom (∑ i, ∑ j, Complex.ofReal (‖x i j‖ ^ 2)) = _
      rw [map_sum]
      congr
      ext i
      change Complex.reAddGroupHom (∑ j, Complex.ofReal (‖x i j‖ ^ 2)) = _
      rw [map_sum]
      congr
      ext j
      simpa using (Complex.ofReal_re (‖x i j‖ ^ (2 : ℝ)))
    have hsReal :
        Complex.re (∑ i, ∑ j, Complex.ofReal (‖x i j‖ ^ 2)) = s := by
      simpa [s] using hsReal'
    have hs : Complex.re (Matrix.trace (x * Matrix.conjTranspose x)) = s := by
      rw [hs_re_trace_eq_sum_normSq]
      exact hsReal
    calc
      ‖x‖ ^ 2 = (Real.sqrt s) ^ 2 := by
        simp [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow, s]
      _ = s := Real.sq_sqrt hnonneg
      _ = Complex.re (Matrix.trace (x * Matrix.conjTranspose x)) := by
        simpa using hs.symm
  conj_inner_symm x y := by
    simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
      (Matrix.trace_conjTranspose (A := x * Matrix.conjTranspose y)).symm
  add_left x y z := by
    simp [Matrix.mul_add]
  smul_left x y r := by
    simp

/-- Completeness of the finite-dimensional Hilbert-Schmidt matrix space. -/
noncomputable scoped instance instMatrixCompleteSpace {n : ℕ} : CompleteSpace (Mₙ n) :=
  FiniteDimensional.complete ℂ (Mₙ n)

/-- Continuous linear maps between Hilbert spaces with fixed choices of the
normed-additive and inner-product instances. -/
private abbrev HilbertSpaceMap (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] : Type _ :=
  E →L[ℂ] F

/-- Continuous linear maps between two canonical Frobenius matrix spaces. -/
abbrev HSMap (n m : ℕ) :=
  @HilbertSpaceMap (Mₙ n) (Mₙ m)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (instMatrixNormedAddCommGroup (n := m))
    (instMatrixInnerProductSpace (n := m))

/-- Hilbert-Schmidt operators on `Mₙ n`, represented as continuous linear
endomorphisms of the canonical Frobenius Hilbert space. -/
noncomputable abbrev HSOp (n : ℕ) : Type := HSMap n n

/-- Real continuous functional calculus on Hilbert-Schmidt operators, using the
explicit Frobenius instances fixed in this namespace. -/
noncomputable abbrev hsCfcR {n : ℕ} (f : ℝ → ℝ) (T : HSOp n) : HSOp n :=
  cfc (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint) f T

end HiaiPetz

namespace Matrix.PosDef

open scoped MatrixOrder ComplexOrder

/-- Positive-definite matrices are nonnegative in the matrix order.
This is the order-facing convenience lemma used by the Hiai–Petz inequalities. -/
theorem nonneg {n : ℕ} {A : HiaiPetz.Mₙ n} (hA : Matrix.PosDef A) :
    0 ≤ A :=
  hA.posSemidef.nonneg

/-- A positive-definite matrix is self-adjoint in the ambient star algebra. -/
theorem isSelfAdjoint {n : ℕ} {A : HiaiPetz.Mₙ n} (hA : Matrix.PosDef A) :
    IsSelfAdjoint A := by
  simpa [Matrix.IsHermitian, IsSelfAdjoint] using hA.isHermitian

end Matrix.PosDef

namespace HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder

noncomputable section MatrixScopedInstances

variable {n m : ℕ}

/-- File-local weak quadratic-form nonnegativity. It deliberately carries no
self-adjointness and is not part of the public operator-order API. -/
private def HSQuadraticNonneg (T : HSOp n) : Prop :=
  ∀ X : Mₙ n, 0 ≤ Complex.re (Matrix.trace (Matrix.conjTranspose X * T X))

/-- The Hilbert-Schmidt adjoint induced by the Frobenius inner product. -/
noncomputable def hsAdjoint (Φ : HSMap n m) : HSMap m n :=
  (@ContinuousLinearMap.adjoint ℂ (Mₙ n) (Mₙ m)
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := n))
      (instMatrixNormedAddCommGroup (n := m))
      (instMatrixInnerProductSpace (n := n))
      (instMatrixInnerProductSpace (n := m))
      (instMatrixCompleteSpace (n := n))
      (instMatrixCompleteSpace (n := m))) Φ

/-- File-local bridge from weak quadratic-form nonnegativity to Mathlib
positivity once self-adjointness is fixed. -/
private theorem hsQuadraticNonneg_iff_isPositive {T : HSOp n}
    (hsa : hsAdjoint T = T) :
    HSQuadraticNonneg T ↔
      @ContinuousLinearMap.IsPositive ℂ (Mₙ n)
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixInnerProductSpace (n := n)) T := by
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  constructor
  · intro hT
    have hadj : hsAdjoint T = T := hsa
    dsimp [hsAdjoint] at hadj
    refine ⟨?_, ?_⟩
    · intro X Y
      simpa [hadj] using
        @ContinuousLinearMap.adjoint_inner_left ℂ (Mₙ n) (Mₙ n)
          (inferInstance : RCLike ℂ)
          (instMatrixNormedAddCommGroup (n := n))
          (instMatrixNormedAddCommGroup (n := n))
          (instMatrixInnerProductSpace (n := n))
          (instMatrixInnerProductSpace (n := n))
          (instMatrixCompleteSpace (n := n))
          (instMatrixCompleteSpace (n := n))
          T Y X
    · intro X
      have hsymm : T.IsSymmetric := by
        intro Y Z
        simpa [hadj] using
          @ContinuousLinearMap.adjoint_inner_left ℂ (Mₙ n) (Mₙ n)
            (inferInstance : RCLike ℂ)
            (instMatrixNormedAddCommGroup (n := n))
            (instMatrixNormedAddCommGroup (n := n))
            (instMatrixInnerProductSpace (n := n))
            (instMatrixInnerProductSpace (n := n))
            (instMatrixCompleteSpace (n := n))
            (instMatrixCompleteSpace (n := n))
            T Z Y
      have hinner : 0 ≤ Complex.re (Matrix.trace (T X * Matrix.conjTranspose X)) := by
        rw [Matrix.trace_mul_comm]
        exact hT X
      have hswap : inner ℂ (T X) X = inner ℂ X (T X) := by
        exact hsymm X X
      simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hswap ▸ hinner
  · intro hT X
    have hinner : 0 ≤ Complex.re (inner ℂ (T X) X) := by
      simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hT.2 X
    have hswap : inner ℂ (T X) X = inner ℂ X (T X) := by
      exact hT.1 X X
    have hinner' : 0 ≤ Complex.re (inner ℂ X (T X)) := by
      rwa [hswap] at hinner
    have htrace : 0 ≤ Complex.re (Matrix.trace (T X * Matrix.conjTranspose X)) := by
      simpa using hinner'
    rwa [Matrix.trace_mul_comm] at htrace

/-- Left multiplication on the Hilbert-Schmidt matrix space.
Source: Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Definition 6.1. -/
noncomputable def leftMul (A : Mₙ n) : HSOp n :=
  ({ toFun := fun X ↦ A * X
     map_add' := by
       intro X Y
       simp [Matrix.mul_add]
     map_smul' := by
       intro z X
       simp } : Mₙ n →ₗ[ℂ] Mₙ n).toContinuousLinearMap

/-- Right multiplication on the Hilbert-Schmidt matrix space.
Source: Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Definition 6.1. -/
noncomputable def rightMul (B : Mₙ n) : HSOp n :=
  ({ toFun := fun X ↦ X * B
     map_add' := by
       intro X Y
       simp [Matrix.add_mul]
     map_smul' := by
       intro z X
       simp } : Mₙ n →ₗ[ℂ] Mₙ n).toContinuousLinearMap

/-- The positive argument `L_A R_{B^{-1}}` of `J_f(A,B)`. -/
noncomputable def jArg (A B : Mₙ n) : HSOp n :=
  (rightMul B⁻¹).comp (leftMul A)

/-- Definition 6.1(2): `J_f(A,B) = f(L_A R_{B^{-1}}) R_B`.
Source: Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Definition 6.1. -/
noncomputable def jOperator (f : ℝ → ℝ) (A B : Mₙ n) : HSOp n :=
  hsCfcR f (jArg A B) * rightMul B

/-- Helper inverse formula used in the strict-output form of Theorem 6.2. -/
noncomputable def jOperatorInv (f : ℝ → ℝ) (A B : Mₙ n) : HSOp n :=
  hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) * rightMul B⁻¹

/-- Hiai-Petz quasi-entropy.
Source: Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Definition 6.1. -/
noncomputable def quasiEntropy (f : ℝ → ℝ) (A B X : Mₙ n) : ℝ :=
  Complex.re (Matrix.trace (Matrix.conjTranspose X * jOperator f A B X))

/-- Left multiplication acts on a matrix by ordinary multiplication on the left. -/
@[simp] lemma leftMul_apply (A X : Mₙ n) :
    leftMul A X = A * X := rfl

/-- Right multiplication acts on a matrix by ordinary multiplication on the right. -/
@[simp] lemma rightMul_apply (B X : Mₙ n) :
    rightMul B X = X * B := rfl

/-- A unit matrix gives a unit left-multiplication operator.
Source: Hiai, Definition 6.1 left multiplication. -/
theorem leftMul_isUnit_of_isUnit {A : Mₙ n} (hA : IsUnit A) :
    IsUnit (leftMul A) := by
  rcases hA with ⟨u, rfl⟩
  refine ⟨⟨leftMul (↑u : Mₙ n), leftMul (↑(u⁻¹) : Mₙ n), ?_, ?_⟩, rfl⟩
  · ext X
    simp [leftMul_apply]
  · ext X
    simp [leftMul_apply]

/-- A unit matrix gives a unit right-multiplication operator.
Source: Hiai, Definition 6.1 right multiplication. -/
theorem rightMul_isUnit_of_isUnit {A : Mₙ n} (hA : IsUnit A) :
    IsUnit (rightMul A) := by
  rcases hA with ⟨u, rfl⟩
  refine ⟨⟨rightMul (↑u : Mₙ n), rightMul (↑(u⁻¹) : Mₙ n), ?_, ?_⟩, rfl⟩
  · ext X
    simp [rightMul_apply, Matrix.mul_assoc]
  · ext X
    simp [rightMul_apply, Matrix.mul_assoc]

/-- The argument of `J_f(A,B)` applies to `X` as `A * X * B⁻¹`. -/
@[simp] lemma jArg_apply (A B X : Mₙ n) :
    jArg A B X = A * X * B⁻¹ := by
  simp [jArg, mul_assoc]

/-- Left and right multiplication commute as Hilbert-Schmidt operators because
matrix multiplication is associative. -/
lemma leftMul_comm_rightMul (A B : Mₙ n) :
    (rightMul B).comp (leftMul A) = (leftMul A).comp (rightMul B) := by
  apply ContinuousLinearMap.ext
  intro X
  change (A * X) * B = A * (X * B)
  rw [Matrix.mul_assoc]

private lemma inner_leftMul_apply (A X Y : Mₙ n) :
    inner ℂ X (A * Y) = inner ℂ (Matrix.conjTranspose A * X) Y := by
  change Matrix.trace ((A * Y) * Matrix.conjTranspose X) =
    Matrix.trace (Y * Matrix.conjTranspose (Matrix.conjTranspose A * X))
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simpa [Matrix.mul_assoc] using Matrix.trace_mul_comm A (Y * Matrix.conjTranspose X)

private lemma inner_rightMul_apply (B X Y : Mₙ n) :
    inner ℂ X (Y * B) = inner ℂ (X * Matrix.conjTranspose B) Y := by
  change Matrix.trace ((Y * B) * Matrix.conjTranspose X) =
    Matrix.trace (Y * Matrix.conjTranspose (X * Matrix.conjTranspose B))
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp [Matrix.mul_assoc]

/-- The Hilbert-Schmidt adjoint of left multiplication is left multiplication by
the conjugate transpose. -/
theorem hsAdjoint_leftMul (A : Mₙ n) :
    hsAdjoint (leftMul A) = leftMul (Matrix.conjTranspose A) := by
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  apply ContinuousLinearMap.ext
  intro X
  apply (@ext_inner_right ℂ (Mₙ n) (inferInstance : RCLike ℂ)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n)))
  intro Y
  have hAdj :
      inner ℂ ((hsAdjoint (leftMul A)) X) Y = inner ℂ X ((leftMul A) Y) := by
    simpa [hsAdjoint] using
      (@ContinuousLinearMap.adjoint_inner_left ℂ (Mₙ n) (Mₙ n)
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixInnerProductSpace (n := n))
        (instMatrixInnerProductSpace (n := n))
        (instMatrixCompleteSpace (n := n))
        (instMatrixCompleteSpace (n := n))
        (leftMul A) Y X)
  exact hAdj.trans <| by simpa using inner_leftMul_apply A X Y

/-- The Hilbert-Schmidt adjoint of right multiplication is right multiplication by
the conjugate transpose. -/
theorem hsAdjoint_rightMul (B : Mₙ n) :
    hsAdjoint (rightMul B) = rightMul (Matrix.conjTranspose B) := by
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  apply ContinuousLinearMap.ext
  intro X
  apply (@ext_inner_right ℂ (Mₙ n) (inferInstance : RCLike ℂ)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n)))
  intro Y
  have hAdj :
      inner ℂ ((hsAdjoint (rightMul B)) X) Y = inner ℂ X ((rightMul B) Y) := by
    simpa [hsAdjoint] using
      (@ContinuousLinearMap.adjoint_inner_left ℂ (Mₙ n) (Mₙ n)
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixInnerProductSpace (n := n))
        (instMatrixInnerProductSpace (n := n))
        (instMatrixCompleteSpace (n := n))
        (instMatrixCompleteSpace (n := n))
        (rightMul B) Y X)
  exact hAdj.trans <| by simpa using inner_rightMul_apply B X Y

/-- A self-adjoint matrix induces a self-adjoint left multiplication operator
for the Hilbert-Schmidt adjoint. -/
theorem leftMul_isSelfAdjoint {A : Mₙ n} :
    IsSelfAdjoint A → hsAdjoint (leftMul A) = leftMul A := by
  intro hA
  simpa [hsAdjoint_leftMul A] using congrArg leftMul hA.star_eq

/-- A self-adjoint matrix induces a self-adjoint right multiplication operator
for the Hilbert-Schmidt adjoint. -/
theorem rightMul_isSelfAdjoint {B : Mₙ n} :
    IsSelfAdjoint B → hsAdjoint (rightMul B) = rightMul B := by
  intro hB
  simpa [hsAdjoint_rightMul B] using congrArg rightMul hB.star_eq

/-- Weak quadratic-form nonnegativity for left multiplication. This helper is
kept private; the public theorem below uses Mathlib's operator order. -/
private theorem leftMul_quadratic_nonneg {A : Mₙ n} :
    0 ≤ A → HSQuadraticNonneg (leftMul A) := by
  intro hA X
  have hA_psd : A.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hA
  have hpsd : (Matrix.conjTranspose X * A * X).PosSemidef :=
    Matrix.PosSemidef.conjTranspose_mul_mul_same hA_psd X
  have htrace : 0 ≤ Matrix.trace (Matrix.conjTranspose X * A * X) :=
    Matrix.PosSemidef.trace_nonneg hpsd
  exact (Complex.le_def.mp <| by simpa [leftMul_apply, Matrix.mul_assoc] using htrace).1

/-- Weak quadratic-form nonnegativity for right multiplication. This helper is
kept private; the public theorem below uses Mathlib's operator order. -/
private theorem rightMul_quadratic_nonneg {B : Mₙ n} :
    0 ≤ B → HSQuadraticNonneg (rightMul B) := by
  intro hB X
  have hB_psd : B.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hB
  have hpsd : (X * B * Matrix.conjTranspose X).PosSemidef :=
    Matrix.PosSemidef.mul_mul_conjTranspose_same hB_psd X
  have htrace : 0 ≤ Matrix.trace (X * B * Matrix.conjTranspose X) :=
    Matrix.PosSemidef.trace_nonneg hpsd
  have hre : 0 ≤ Complex.re (Matrix.trace (X * B * Matrix.conjTranspose X)) :=
    (Complex.le_def.mp htrace).1
  calc
    0 ≤ Complex.re (Matrix.trace (X * B * Matrix.conjTranspose X)) := hre
    _ = Complex.re (Matrix.trace (Matrix.conjTranspose X * (X * B))) := by
          rw [show Matrix.trace (X * B * Matrix.conjTranspose X) =
              Matrix.trace ((X * B) * Matrix.conjTranspose X) by simp [Matrix.mul_assoc]]
          rw [Matrix.trace_mul_comm]
    _ = Complex.re (Matrix.trace (Matrix.conjTranspose X * (rightMul B X))) := by
          simp [rightMul_apply]

/-- A nonnegative matrix gives a nonnegative left-multiplication operator in
Mathlib's Loewner order on continuous linear maps. -/
theorem leftMul_nonneg {A : Mₙ n} (hA : 0 ≤ A) :
    0 ≤ leftMul A := by
  apply (@ContinuousLinearMap.nonneg_iff_isPositive ℂ (Mₙ n)
    (inferInstance : RCLike ℂ)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (leftMul A)).2
  exact (hsQuadraticNonneg_iff_isPositive
    (leftMul_isSelfAdjoint (IsSelfAdjoint.of_nonneg hA))).mp
    (leftMul_quadratic_nonneg hA)

/-- A nonnegative matrix gives a nonnegative right-multiplication operator in
Mathlib's Loewner order on continuous linear maps. -/
theorem rightMul_nonneg {B : Mₙ n} (hB : 0 ≤ B) :
    0 ≤ rightMul B := by
  apply (@ContinuousLinearMap.nonneg_iff_isPositive ℂ (Mₙ n)
    (inferInstance : RCLike ℂ)
    (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n))
    (rightMul B)).2
  exact (hsQuadraticNonneg_iff_isPositive
    (rightMul_isSelfAdjoint (IsSelfAdjoint.of_nonneg hB))).mp
    (rightMul_quadratic_nonneg hB)

end MatrixScopedInstances

end HiaiPetz
