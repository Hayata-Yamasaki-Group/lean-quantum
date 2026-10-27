/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.GeneralizedPerspectiveFunction

import Mathlib.Analysis.InnerProductSpace.Trace
import Quantum.QuantumMechanics.OperatorNotation

/-!
# Hilbert-Schmidt operator spaces

This module equips operators on a finite-dimensional complex Hilbert space with the
Hilbert-Schmidt inner product. It develops adjoints, positivity and left and right
multiplication on this operator space for the proofs of the Lieb-Ando inequalities.
-/

namespace HilbertSchmidtOperatorSpace

open LownerHeinzTheorem

universe u

noncomputable section

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [FiniteDimensional ℂ ℋ]

/-- The canonical finite index used for Hilbert-Schmidt coordinates. -/
abbrev HSIndex (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [FiniteDimensional ℂ ℋ] :=
  Fin (Module.finrank ℂ ℋ)

/-- The standard orthonormal basis on a finite-dimensional Hilbert space. -/
noncomputable abbrev hsOrthonormalBasis :
    OrthonormalBasis (HSIndex ℋ) ℂ ℋ :=
  stdOrthonormalBasis ℂ ℋ

/-- Coordinate space for Hilbert-Schmidt operators. -/
abbrev HSCoords (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [FiniteDimensional ℂ ℋ] :=
  EuclideanSpace ℂ (HSIndex ℋ × HSIndex ℋ)

/-- The underlying coordinate function space for Hilbert-Schmidt operators. -/
abbrev HSCoordFun (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [FiniteDimensional ℂ ℋ] :=
  HSIndex ℋ × HSIndex ℋ → ℂ

/-- The operator space `B ℋ`, viewed later with the Hilbert-Schmidt structure. -/
def HSOp (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] : Type u :=
  QuantumState.B ℋ

instance : AddCommGroup (HSOp ℋ) := by
  delta HSOp
  infer_instance

instance : Module ℂ (HSOp ℋ) := by
  change Module ℂ (ℋ →L[ℂ] ℋ)
  infer_instance

instance : FiniteDimensional ℂ (HSOp ℋ) := by
  change FiniteDimensional ℂ (ℋ →L[ℂ] ℋ)
  infer_instance

private noncomputable def hsCoordsLinearEquiv :
    HSCoords ℋ ≃ₗ[ℂ] (HSCoordFun ℋ) := by
  simpa [HSCoords, HSCoordFun] using
    (WithLp.linearEquiv (2 : ENNReal) ℂ (HSCoordFun ℋ))

private def matrixToFun :
    Matrix (HSIndex ℋ) (HSIndex ℋ) ℂ ≃ₗ[ℂ] HSCoordFun ℋ where
  toFun M p := M p.1 p.2
  invFun f i j := f (i, j)
  map_add' M N := by
    ext ⟨i, j⟩
    rfl
  map_smul' c M := by
    ext ⟨i, j⟩
    rfl
  left_inv M := by
    ext i j
    rfl
  right_inv f := by
    ext ⟨i, j⟩
    rfl

private noncomputable def matrixToCoords :
    Matrix (HSIndex ℋ) (HSIndex ℋ) ℂ ≃ₗ[ℂ] HSCoords ℋ :=
  (matrixToFun (ℋ := ℋ)).trans hsCoordsLinearEquiv.symm

/-- Forget continuity and identify continuous linear operators with linear endomorphisms. -/
private noncomputable def hsLinearMapEquiv :
    HSOp ℋ ≃ₗ[ℂ] (ℋ →ₗ[ℂ] ℋ) :=
  LinearMap.toContinuousLinearMap.symm

/-- Hilbert-Schmidt coordinates on `B ℋ`. -/
noncomputable def toHSCoordsLinearEquiv :
    HSOp ℋ ≃ₗ[ℂ] HSCoords ℋ :=
  (hsLinearMapEquiv (ℋ := ℋ)).trans <|
    (LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
      (hsOrthonormalBasis (ℋ := ℋ)).toBasis).trans <|
      matrixToCoords (ℋ := ℋ)

omit [CompleteSpace ℋ] in
@[simp] lemma toHSCoordsLinearEquiv_apply_apply
    (T : HSOp ℋ) (i j : HSIndex ℋ) :
    toHSCoordsLinearEquiv (ℋ := ℋ) T (i, j) =
      LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
        (hsOrthonormalBasis (ℋ := ℋ)).toBasis
        ((hsLinearMapEquiv (ℋ := ℋ)) T) i j := by
  change hsCoordsLinearEquiv (toHSCoordsLinearEquiv (ℋ := ℋ) T) (i, j) =
    LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
      (hsOrthonormalBasis (ℋ := ℋ)).toBasis
      ((hsLinearMapEquiv (ℋ := ℋ)) T) i j
  let f : HSCoordFun ℋ := fun p =>
    LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
      (hsOrthonormalBasis (ℋ := ℋ)).toBasis
      ((hsLinearMapEquiv (ℋ := ℋ)) T) p.1 p.2
  have h : hsCoordsLinearEquiv (toHSCoordsLinearEquiv (ℋ := ℋ) T) = f := by
    dsimp only [toHSCoordsLinearEquiv]
    simp [matrixToCoords, matrixToFun, f]
  have hEval := congrArg (fun g : HSCoordFun ℋ => g (i, j)) h
  simpa [f] using hEval

instance : NormedAddCommGroup (HSOp ℋ) :=
  NormedAddCommGroup.induced (HSOp ℋ) (HSCoords ℋ)
    (toHSCoordsLinearEquiv (ℋ := ℋ)) (toHSCoordsLinearEquiv (ℋ := ℋ)).injective

instance : NormedSpace ℂ (HSOp ℋ) :=
  NormedSpace.induced ℂ (HSOp ℋ) (HSCoords ℋ) (toHSCoordsLinearEquiv (ℋ := ℋ))

instance : Inner ℂ (HSOp ℋ) where
  inner T S := inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) T) (toHSCoordsLinearEquiv (ℋ := ℋ) S)

instance : InnerProductSpace ℂ (HSOp ℋ) where
  norm_sq_eq_re_inner T := by
    change ‖toHSCoordsLinearEquiv (ℋ := ℋ) T‖ ^ 2 =
      Complex.re (inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) T)
        (toHSCoordsLinearEquiv (ℋ := ℋ) T))
    simpa using
      (inner_self_eq_norm_sq (𝕜 := ℂ) (toHSCoordsLinearEquiv (ℋ := ℋ) T)).symm
  conj_inner_symm T S := by
    change star (inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) S)
      (toHSCoordsLinearEquiv (ℋ := ℋ) T)) =
      inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) T) (toHSCoordsLinearEquiv (ℋ := ℋ) S)
    simp [inner_conj_symm (toHSCoordsLinearEquiv (ℋ := ℋ) T)
      (toHSCoordsLinearEquiv (ℋ := ℋ) S)]
  add_left T S R := by
    change inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) (T + S))
      (toHSCoordsLinearEquiv (ℋ := ℋ) R) =
      inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) T)
        (toHSCoordsLinearEquiv (ℋ := ℋ) R) +
      inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) S)
        (toHSCoordsLinearEquiv (ℋ := ℋ) R)
    simp [inner_add_left, map_add]
  smul_left T S z := by
    change inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) (z • T))
      (toHSCoordsLinearEquiv (ℋ := ℋ) S) =
      star z * inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) T)
        (toHSCoordsLinearEquiv (ℋ := ℋ) S)
    simp [inner_smul_left, map_smul]

/-- Hilbert-Schmidt coordinates as a linear isometry. -/
noncomputable def toHSCoordsLinearIsometryEquiv :
    HSOp ℋ ≃ₗᵢ[ℂ] HSCoords ℋ :=
  LinearEquiv.isometryOfInner (toHSCoordsLinearEquiv (ℋ := ℋ)) <| by
    intro T S
    change inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) T)
      (toHSCoordsLinearEquiv (ℋ := ℋ) S) =
      inner ℂ T S
    rfl

instance : CompleteSpace (HSOp ℋ) :=
  let e : HSOp ℋ ≃ HSCoords ℋ :=
    (toHSCoordsLinearIsometryEquiv.toContinuousLinearEquiv.toLinearEquiv.toEquiv)
  (completeSpace_congr (e := e) <| by
    simpa using
      (toHSCoordsLinearIsometryEquiv.toContinuousLinearEquiv.isUniformEmbedding)).2
    inferInstance

instance : ContinuousSMul ℂ (HSOp ℋ) :=
  (toHSCoordsLinearIsometryEquiv (ℋ := ℋ)).isometry.isUniformInducing.isInducing.continuousSMul
    continuous_id fun {c x} => map_smul (toHSCoordsLinearEquiv (ℋ := ℋ)) c x

/-- Reinterpret an operator as an element of the Hilbert-Schmidt operator space. -/
abbrev ofOp (T : QuantumState.B ℋ) : HSOp ℋ := T

/-- Forget the Hilbert-Schmidt structure and recover the underlying operator. -/
abbrev toOp (T : HSOp ℋ) : QuantumState.B ℋ := T

/-- Left multiplication on the Hilbert-Schmidt operator space. -/
noncomputable def leftMulHS (A : QuantumState.B ℋ) : QuantumState.B (HSOp ℋ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => ofOp (A * toOp T)
      map_add' := fun T S => mul_add A (toOp T) (toOp S)
      map_smul' := fun z T => mul_smul_comm z A (toOp T) }

/-- Right multiplication on the Hilbert-Schmidt operator space. -/
noncomputable def rightMulHS (B : QuantumState.B ℋ) : QuantumState.B (HSOp ℋ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => ofOp (toOp T * B)
      map_add' := fun T S => add_mul (toOp T) (toOp S) B
      map_smul' := fun z T => smul_mul_assoc z (toOp T) B }

omit [CompleteSpace ℋ] in
@[simp] lemma leftMulHS_mul (A B : QuantumState.B ℋ) :
    leftMulHS (ℋ := ℋ) (A * B) = leftMulHS (ℋ := ℋ) A * leftMulHS (ℋ := ℋ) B := by
  ext T
  change ofOp ((A * B) * toOp T) = ofOp (A * (B * toOp T))
  rw [mul_assoc]

omit [CompleteSpace ℋ] in
@[simp] lemma rightMulHS_mul (A B : QuantumState.B ℋ) :
    rightMulHS (ℋ := ℋ) (A * B) = rightMulHS (ℋ := ℋ) B * rightMulHS (ℋ := ℋ) A := by
  ext T
  change ofOp (toOp T * (A * B)) = ofOp ((toOp T * A) * B)
  rw [mul_assoc]

omit [CompleteSpace ℋ] in
@[simp] lemma leftMulHS_one :
    leftMulHS (ℋ := ℋ) (1 : QuantumState.B ℋ) = (1 : QuantumState.B (HSOp ℋ)) := by
  ext T
  change 1 * toOp T = toOp T
  exact one_mul _

omit [CompleteSpace ℋ] in
@[simp] lemma rightMulHS_one :
    rightMulHS (ℋ := ℋ) (1 : QuantumState.B ℋ) = (1 : QuantumState.B (HSOp ℋ)) := by
  ext T
  change toOp T * 1 = toOp T
  exact mul_one _

omit [CompleteSpace ℋ] in
lemma leftMulHS_rightMulHS_commute (A B : QuantumState.B ℋ) :
    Commute (leftMulHS A) (rightMulHS B) := by
  ext T
  change ofOp (A * (toOp T * B)) = ofOp ((A * toOp T) * B)
  rw [mul_assoc]

omit [CompleteSpace ℋ] in
private lemma hsInner_eq_pairSum (X Y : (ℋ →L[ℂ] ℋ)) :
    inner ℂ (ofOp X) (ofOp Y) =
      ∑ p : HSIndex ℋ × HSIndex ℋ,
        LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
          (hsOrthonormalBasis (ℋ := ℋ)).toBasis (Y : ℋ →ₗ[ℂ] ℋ) p.1 p.2 *
        star
          (LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
            (hsOrthonormalBasis (ℋ := ℋ)).toBasis (X : ℋ →ₗ[ℂ] ℋ) p.1 p.2) := by
  have hXfun :
      ((toHSCoordsLinearEquiv (ℋ := ℋ) (ofOp X) : HSCoords ℋ).ofLp : HSCoordFun ℋ) =
        fun p =>
          LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
            (hsOrthonormalBasis (ℋ := ℋ)).toBasis (X : ℋ →ₗ[ℂ] ℋ) p.1 p.2 := by
    funext p
    change (toHSCoordsLinearEquiv (ℋ := ℋ) (ofOp X) :
      EuclideanSpace ℂ (HSIndex ℋ × HSIndex ℋ)) p = _
    exact toHSCoordsLinearEquiv_apply_apply (ℋ := ℋ) (T := ofOp X) p.1 p.2
  have hYfun :
      ((toHSCoordsLinearEquiv (ℋ := ℋ) (ofOp Y) : HSCoords ℋ).ofLp : HSCoordFun ℋ) =
        fun p =>
          LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
            (hsOrthonormalBasis (ℋ := ℋ)).toBasis (Y : ℋ →ₗ[ℂ] ℋ) p.1 p.2 := by
    funext p
    change (toHSCoordsLinearEquiv (ℋ := ℋ) (ofOp Y) :
      EuclideanSpace ℂ (HSIndex ℋ × HSIndex ℋ)) p = _
    exact toHSCoordsLinearEquiv_apply_apply (ℋ := ℋ) (T := ofOp Y) p.1 p.2
  change inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) (ofOp X))
      (toHSCoordsLinearEquiv (ℋ := ℋ) (ofOp Y)) = _
  rw [EuclideanSpace.inner_eq_star_dotProduct, hXfun, hYfun]
  simp [dotProduct]

private lemma trace_star_mul_eq_pairSum (X Y : (ℋ →L[ℂ] ℋ)) :
    LinearMap.trace ℂ ℋ ((star X * Y : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ) =
      ∑ p : HSIndex ℋ × HSIndex ℋ,
        LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
          (hsOrthonormalBasis (ℋ := ℋ)).toBasis (Y : ℋ →ₗ[ℂ] ℋ) p.1 p.2 *
        star
          (LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
            (hsOrthonormalBasis (ℋ := ℋ)).toBasis (X : ℋ →ₗ[ℂ] ℋ) p.1 p.2) := by
  let b := hsOrthonormalBasis (ℋ := ℋ)
  calc
    LinearMap.trace ℂ ℋ ((star X * Y : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ)
        = ∑ i : HSIndex ℋ, ∑ j : HSIndex ℋ,
            LinearMap.toMatrix b.toBasis b.toBasis (Y : ℋ →ₗ[ℂ] ℋ) j i *
              star (LinearMap.toMatrix b.toBasis b.toBasis (X : ℋ →ₗ[ℂ] ℋ) j i) := by
            rw [LinearMap.trace_eq_sum_inner
              ((star X * Y : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ) b]
            apply Finset.sum_congr rfl
            intro i hi
            calc
              inner ℂ (b i) (((star X * Y : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ) (b i)) =
                  inner ℂ (X (b i)) (Y (b i)) := by
                simpa [ContinuousLinearMap.star_eq_adjoint] using
                  (ContinuousLinearMap.adjoint_inner_right (A := X) (x := b i) (y := Y (b i)))
              _ = ∑ j : HSIndex ℋ, inner ℂ (X (b i)) (b j) * inner ℂ (b j) (Y (b i)) := by
                symm
                exact OrthonormalBasis.sum_inner_mul_inner b (X (b i)) (Y (b i))
              _ = ∑ j : HSIndex ℋ,
                    LinearMap.toMatrix b.toBasis b.toBasis (Y : ℋ →ₗ[ℂ] ℋ) j i *
                      star (LinearMap.toMatrix b.toBasis b.toBasis (X : ℋ →ₗ[ℂ] ℋ) j i) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  simp [LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply, mul_comm]
    _ = ∑ p : HSIndex ℋ × HSIndex ℋ,
          LinearMap.toMatrix b.toBasis b.toBasis (Y : ℋ →ₗ[ℂ] ℋ) p.1 p.2 *
            star (LinearMap.toMatrix b.toBasis b.toBasis (X : ℋ →ₗ[ℂ] ℋ) p.1 p.2) := by
          rw [Finset.sum_comm]
          symm
          simpa [Finset.univ_product_univ] using
            (Finset.sum_product' (s := (Finset.univ : Finset (HSIndex ℋ)))
              (t := (Finset.univ : Finset (HSIndex ℋ)))
              (f := fun j i =>
                LinearMap.toMatrix b.toBasis b.toBasis (Y : ℋ →ₗ[ℂ] ℋ) j i *
                  star (LinearMap.toMatrix b.toBasis b.toBasis (X : ℋ →ₗ[ℂ] ℋ) j i)))

lemma hsInner_eq_trace (X Y : QuantumState.B ℋ) :
    inner ℂ (ofOp X) (ofOp Y) =
      LinearMap.trace ℂ ℋ ((star X * Y : QuantumState.B ℋ) : QuantumState.L ℋ) := by
  calc
    inner ℂ (ofOp X) (ofOp Y)
        = ∑ p : HSIndex ℋ × HSIndex ℋ,
            LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
              (hsOrthonormalBasis (ℋ := ℋ)).toBasis (Y : ℋ →ₗ[ℂ] ℋ) p.1 p.2 *
            star
              (LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
                (hsOrthonormalBasis (ℋ := ℋ)).toBasis (X : ℋ →ₗ[ℂ] ℋ) p.1 p.2) :=
          hsInner_eq_pairSum (X := X) (Y := Y)
    _ = LinearMap.trace ℂ ℋ ((star X * Y : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ) := by
          symm
          exact trace_star_mul_eq_pairSum (X := X) (Y := Y)

lemma re_hsInner_eq_traceRe (X Y : QuantumState.B ℋ) :
    Complex.re (inner ℂ (ofOp X) (ofOp Y)) =
      Complex.re
        (LinearMap.trace ℂ ℋ ((star X * Y : QuantumState.B ℋ) : ℋ →ₗ[ℂ] ℋ)) := by
  simpa using congrArg Complex.re (hsInner_eq_trace (X := X) (Y := Y))

@[simp] lemma leftMulHS_star (A : QuantumState.B ℋ) :
    star (leftMulHS (ℋ := ℋ) A) = leftMulHS (ℋ := ℋ) (star A) := by
  rw [eq_comm, ContinuousLinearMap.star_eq_adjoint]
  refine (ContinuousLinearMap.eq_adjoint_iff
    (A := leftMulHS (ℋ := ℋ) (star A)) (B := leftMulHS (ℋ := ℋ) A)).2 ?_
  intro X Y
  change inner ℂ (ofOp ((star A) * toOp X)) (ofOp (toOp Y)) =
    inner ℂ (ofOp (toOp X)) (ofOp (A * toOp Y))
  rw [hsInner_eq_trace]
  rw [hsInner_eq_trace]
  simp [mul_assoc]

@[simp] lemma leftMulHS_real_smul_one (r : ℝ) :
    leftMulHS (ℋ := ℋ) (r • (1 : QuantumState.B ℋ)) = r • (1 : QuantumState.B (HSOp ℋ)) := by
  ext T
  change ofOp ((r • (1 : (ℋ →L[ℂ] ℋ))) * toOp T) = ofOp (r • toOp T)
  simp [Algebra.smul_def]

@[simp] lemma rightMulHS_real_smul_one (r : ℝ) :
    rightMulHS (ℋ := ℋ) (r • (1 : QuantumState.B ℋ)) = r • (1 : QuantumState.B (HSOp ℋ)) := by
  ext T
  change ofOp (toOp T * (r • (1 : (ℋ →L[ℂ] ℋ)))) = ofOp (r • toOp T)
  simp [Algebra.smul_def, Algebra.commutes (R := ℝ) (A := (ℋ →L[ℂ] ℋ)) r (toOp T)]

lemma leftMulHS_nonneg {A : QuantumState.B ℋ} (hA0 : 0 ≤ A) :
    0 ≤ leftMulHS A := by
  rw [← CFC.sqrt_mul_sqrt_self A hA0, leftMulHS_mul]
  simpa [leftMulHS_star, (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq] using
    star_mul_self_nonneg (leftMulHS (ℋ := ℋ) (CFC.sqrt A))

@[gcongr]
lemma leftMulHS_le_leftMulHS {A B : QuantumState.B ℋ} (hAB : A ≤ B) :
    leftMulHS A ≤ leftMulHS B := by
  have hnonneg : 0 ≤ leftMulHS (ℋ := ℋ) (B - A) :=
    leftMulHS_nonneg (ℋ := ℋ) (sub_nonneg.mpr hAB)
  have hsub :
      leftMulHS (ℋ := ℋ) B - leftMulHS (ℋ := ℋ) A =
        leftMulHS (ℋ := ℋ) (B - A) := by
    ext T; exact congrArg ofOp (sub_mul B A (toOp T)).symm
  exact sub_nonneg.mp (by simpa [hsub] using hnonneg)

lemma leftMulHS_pdSet [ContinuousFunctionalCalculus ℝ (QuantumState.B ℋ) IsSelfAdjoint]
    [Nontrivial (QuantumState.B ℋ)]
    {A : QuantumState.B ℋ} (hA : A ∈ GeneralizedPerspectiveFunction.pdSet (ℋ := ℋ)) :
    leftMulHS (ℋ := ℋ) A ∈ GeneralizedPerspectiveFunction.pdSet (ℋ := HSOp ℋ) := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  have hleft_sa : IsSelfAdjoint (leftMulHS (ℋ := ℋ) A) := by
    change star (leftMulHS (ℋ := ℋ) A) = leftMulHS (ℋ := ℋ) A
    simp [hA_sa.star_eq, leftMulHS_star (ℋ := ℋ) A]
  letI : Nontrivial (HSOp ℋ) := by
    delta HSOp
    infer_instance
  letI : Nontrivial (HSOp ℋ →L[ℂ] HSOp ℋ) := inferInstance
  refine ⟨?_, ?_⟩
  · exact hleft_sa
  · rcases (CFC.exists_pos_algebraMap_le_iff (A := (ℋ →L[ℂ] ℋ)) (a := A) (ha :=
      hA_sa)).2 hA_spec
      with ⟨r, hr, hrA⟩
    refine (CFC.exists_pos_algebraMap_le_iff
      (A := (HSOp ℋ →L[ℂ] HSOp ℋ)) (a := leftMulHS (ℋ := ℋ) A) (ha := hleft_sa)).1 ?_
    refine ⟨r, hr, ?_⟩
    simpa [Algebra.algebraMap_eq_smul_one, leftMulHS_real_smul_one (r := r)] using
      leftMulHS_le_leftMulHS (ℋ := ℋ) hrA

@[simp] lemma rightMulHS_star (A : QuantumState.B ℋ) :
    star (rightMulHS (ℋ := ℋ) A) = rightMulHS (ℋ := ℋ) (star A) := by
  rw [eq_comm, ContinuousLinearMap.star_eq_adjoint]
  refine (ContinuousLinearMap.eq_adjoint_iff
    (A := rightMulHS (ℋ := ℋ) (star A)) (B := rightMulHS (ℋ := ℋ) A)).2 ?_
  intro X Y
  change inner ℂ (ofOp (toOp X * star A)) (ofOp (toOp Y)) =
    inner ℂ (ofOp (toOp X)) (ofOp (toOp Y * A))
  rw [hsInner_eq_trace]
  rw [hsInner_eq_trace]
  rw [star_mul, star_star, mul_assoc]
  symm
  simpa [mul_assoc] using
    (LinearMap.trace_mul_cycle (R := ℂ) (M := ℋ)
      (f := ((star (toOp X) : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ))
      (g := ((toOp Y : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ)) (h := (A : ℋ →ₗ[ℂ] ℋ)))

/-- Left multiplication as a real `⋆`-algebra homomorphism on the Hilbert-Schmidt operator space. -/
noncomputable def leftMulHSStarAlgHom : QuantumState.B ℋ →⋆ₐ[ℝ] QuantumState.B (HSOp ℋ) where
  toFun := leftMulHS (ℋ := ℋ)
  map_one' := leftMulHS_one (ℋ := ℋ)
  map_mul' := leftMulHS_mul (ℋ := ℋ)
  map_zero' := by ext T; exact congrArg ofOp (zero_mul (toOp T))
  map_add' := fun A B => by ext T; exact congrArg ofOp (add_mul A B (toOp T))
  commutes' := by
    intro r
    simp only [Algebra.algebraMap_eq_smul_one]
    exact leftMulHS_real_smul_one (ℋ := ℋ) r
  map_star' := by
    intro A
    simp [leftMulHS_star (ℋ := ℋ) A]

/-- Right multiplication as a real `⋆`-algebra homomorphism out of the opposite algebra. -/
noncomputable def rightMulHSStarAlgHom : (QuantumState.B ℋ)ᵐᵒᵖ →⋆ₐ[ℝ] QuantumState.B (HSOp ℋ) where
  toFun := fun A => rightMulHS (ℋ := ℋ) (MulOpposite.unop A)
  map_one' := by simp [rightMulHS_one (ℋ := ℋ)]
  map_mul' := by
    intro A B
    ext T
    change ofOp (toOp T * MulOpposite.unop (A * B)) =
      ofOp ((toOp T * MulOpposite.unop B) * MulOpposite.unop A)
    simp [mul_assoc]
  map_zero' := by
    ext T
    change ofOp (toOp T * MulOpposite.unop (0 : (ℋ →L[ℂ] ℋ)ᵐᵒᵖ)) = ofOp (0
        : (ℋ →L[ℂ] ℋ))
    congr 1; simp
  map_add' := fun A B => by
    ext T
    change ofOp (toOp T * MulOpposite.unop (A + B)) =
      ofOp (toOp T * MulOpposite.unop A + toOp T * MulOpposite.unop B)
    congr 1; simp [MulOpposite.unop_add, mul_add]
  commutes' := by
    intro r
    change rightMulHS (ℋ := ℋ) (MulOpposite.unop (MulOpposite.op (r • (1 : (ℋ →L[ℂ] ℋ))))) =
      r • (1 : (HSOp ℋ →L[ℂ] HSOp ℋ))
    simp [rightMulHS_real_smul_one (ℋ := ℋ) r]
  map_star' := by
    intro A
    simp [rightMulHS_star (ℋ := ℋ) (MulOpposite.unop A)]

/-- The `⋆`-algebra hom sending `A` to `op (star A)`. On selfadjoint operators this is just `op`. -/
noncomputable def opStarHSStarAlgHom : QuantumState.B ℋ →⋆ₐ[ℝ] (QuantumState.B ℋ)ᵐᵒᵖ where
  toFun := fun A => MulOpposite.op (star A)
  map_one' := by simp
  map_mul' := by
    intro A B
    simp [star_mul]
  map_zero' := by simp
  map_add' := by
    intro A B
    simp
  commutes' := by
    intro r
    apply congrArg MulOpposite.op
    simp [Algebra.algebraMap_eq_smul_one]
  map_star' := by
    intro A
    simp

private noncomputable def opStarHSAlgEquiv : (ℋ →L[ℂ] ℋ) ≃ₐ[ℝ] (ℋ →L[ℂ] ℋ)ᵐᵒᵖ where
  toFun A := MulOpposite.op (star A)
  invFun A := star (MulOpposite.unop A)
  left_inv A := by simp
  right_inv A := by simp
  map_mul' A B := by simp [star_mul]
  map_add' A B := by simp
  commutes' r := by
    apply congrArg MulOpposite.op
    simp [Algebra.algebraMap_eq_smul_one]

omit [FiniteDimensional ℂ ℋ] in
lemma isSelfAdjoint_op (A : QuantumState.B ℋ) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (MulOpposite.op A : (QuantumState.B ℋ)ᵐᵒᵖ) := by
  exact congrArg MulOpposite.op hA.star_eq

private noncomputable def opStarHSLinearMap : (ℋ →L[ℂ] ℋ) →ₗ[ℝ] (ℋ →L[ℂ] ℋ)ᵐᵒᵖ where
  toFun := fun A => MulOpposite.op (star A)
  map_add' A B := by simp
  map_smul' r A := by
    apply MulOpposite.unop_injective
    rw [MulOpposite.unop_op, MulOpposite.unop_smul, MulOpposite.unop_op]
    rw [Algebra.smul_def, star_mul]
    change star A * star ((algebraMap ℝ (ℋ →L[ℂ] ℋ)) r) = (algebraMap ℝ
        (ℋ →L[ℂ] ℋ)) r * star A
    have hstar : star ((algebraMap ℝ (ℋ →L[ℂ] ℋ)) r) = (algebraMap ℝ ((ℋ →L[ℂ] ℋ))) r := by
      rw [Algebra.algebraMap_eq_smul_one, star_smul, star_one]
      simp
    rw [hstar]
    simpa using (Algebra.commutes (R := ℝ) (A := (ℋ →L[ℂ] ℋ)) r (star A)).symm

private noncomputable def leftMulHSLinearMap : (ℋ →L[ℂ] ℋ) →ₗ[ℝ] (HSOp ℋ →L[ℂ] HSOp ℋ) where
  toFun := leftMulHS (ℋ := ℋ)
  map_add' A B := by ext T; exact congrArg ofOp (add_mul A B (toOp T))
  map_smul' r A := by
    ext T
    change ((r • A) * toOp T : (ℋ →L[ℂ] ℋ)) = r • (A * toOp T)
    rw [smul_mul_assoc]

private noncomputable def rightMulHSLinearMap : (ℋ →L[ℂ] ℋ)ᵐᵒᵖ →ₗ[ℝ] (HSOp ℋ →L[ℂ] HSOp ℋ) where
  toFun := fun A => rightMulHS (ℋ := ℋ) (MulOpposite.unop A)
  map_add' A B := by
    ext T
    change ofOp (toOp T * MulOpposite.unop (A + B)) =
      ofOp (toOp T * MulOpposite.unop A + toOp T * MulOpposite.unop B)
    congr 1; simp [MulOpposite.unop_add, mul_add]
  map_smul' r A := by
    ext T
    change ofOp (toOp T * MulOpposite.unop (r • A)) =
      ofOp (r • (toOp T * MulOpposite.unop A))
    congr 1
    rw [MulOpposite.unop_smul, mul_smul_comm]

omit [FiniteDimensional ℂ ℋ] in
lemma spectrum_op_eq [ContinuousFunctionalCalculus ℝ (QuantumState.B ℋ) IsSelfAdjoint]
    [Nontrivial (QuantumState.B ℋ)]
    (A : QuantumState.B ℋ) (hA : IsSelfAdjoint A) :
    spectrum ℝ (MulOpposite.op A : (QuantumState.B ℋ)ᵐᵒᵖ) = spectrum ℝ A := by
  have hopA : IsSelfAdjoint (MulOpposite.op A : (ℋ →L[ℂ] ℋ)ᵐᵒᵖ) := isSelfAdjoint_op
      (A := A) hA
  simpa [opStarHSAlgEquiv, hA.star_eq, hopA.star_eq] using
    (AlgEquiv.spectrum_eq (opStarHSAlgEquiv (ℋ := ℋ)) A)

lemma cfc_op_eq_op_cfc [ContinuousFunctionalCalculus ℝ (QuantumState.B ℋ) IsSelfAdjoint]
    [ContinuousFunctionalCalculus ℝ ((QuantumState.B ℋ)ᵐᵒᵖ) IsSelfAdjoint] [Nontrivial
        (QuantumState.B ℋ)]
    (f : ℝ → ℝ) (A : QuantumState.B ℋ) (hA : IsSelfAdjoint A)
    (hf : ContinuousOn f (spectrum ℝ A)) :
    cfc (R := ℝ) (A := (QuantumState.B ℋ)ᵐᵒᵖ) (p := IsSelfAdjoint) f (MulOpposite.op A) =
      MulOpposite.op (cfcR f A) := by
  let φ : (ℋ →L[ℂ] ℋ) →⋆ₐ[ℝ] (ℋ →L[ℂ] ℋ)ᵐᵒᵖ := opStarHSStarAlgHom (ℋ := ℋ)
  have hφ : Continuous φ := by
    simpa [opStarHSLinearMap] using
      (LinearMap.continuous_of_finiteDimensional (opStarHSLinearMap (ℋ := ℋ)))
  have hopA : IsSelfAdjoint (MulOpposite.op A : (ℋ →L[ℂ] ℋ)ᵐᵒᵖ) := isSelfAdjoint_op
      (A := A) hA
  have hφA : IsSelfAdjoint (φ A) := hA.map φ
  have hcfcA :
      IsSelfAdjoint (cfc (R := ℝ) (A := (ℋ →L[ℂ] ℋ)) (p := IsSelfAdjoint) f A) := by
    simp [IsSelfAdjoint.cfc (f := f) (a := A)]
  have hopcfcA :
      IsSelfAdjoint
        (MulOpposite.op (cfc (R := ℝ) (A := (ℋ →L[ℂ] ℋ)) (p := IsSelfAdjoint) f A)
            : (ℋ →L[ℂ] ℋ)ᵐᵒᵖ) :=
    isSelfAdjoint_op (A := cfc (R := ℝ) (A := (ℋ →L[ℂ] ℋ)) (p := IsSelfAdjoint) f A) hcfcA
  have hmap := StarAlgHom.map_cfc (φ := φ) (f := f) (a := A)
    (hf := hf) (hφ := hφ) (ha := hA) (hφa := hφA)
  simpa [φ, opStarHSStarAlgHom, cfcR, hA.star_eq, hopA.star_eq, hcfcA.star_eq,
    hopcfcA.star_eq] using hmap.symm

lemma leftMulHS_cfcR
    (f : ℝ → ℝ) (A : QuantumState.B ℋ) (hA : IsSelfAdjoint A)
    (hf : ContinuousOn f (spectrum ℝ A)) :
    leftMulHS (cfcR f A) =
      cfcR f (leftMulHS A) := by
  rcases subsingleton_or_nontrivial (QuantumState.B ℋ) with h | h
  · haveI : Subsingleton (HSOp ℋ) := h
    ext x
    exact Subsingleton.elim _ _
  · let φ : (ℋ →L[ℂ] ℋ) →⋆ₐ[ℝ] (HSOp ℋ →L[ℂ] HSOp ℋ) := leftMulHSStarAlgHom (ℋ := ℋ)
    have hφ : Continuous φ := by
      simpa [leftMulHSLinearMap] using
        (LinearMap.continuous_of_finiteDimensional (leftMulHSLinearMap (ℋ := ℋ)))
    have hφA : IsSelfAdjoint (φ A) := hA.map φ
    have hmap := StarAlgHom.map_cfc (φ := φ) (f := f) (a := A)
      (hf := hf) (hφ := hφ) (ha := hA) (hφa := hφA)
    simpa [φ, cfcR] using hmap

lemma rightMulHS_cfcR
    (f : ℝ → ℝ) (A : QuantumState.B ℋ) (hA : IsSelfAdjoint A)
    (hf : ContinuousOn f (spectrum ℝ A)) :
    rightMulHS (cfcR f A) =
      cfcR f (rightMulHS A) := by
  rcases subsingleton_or_nontrivial (QuantumState.B ℋ) with h | h
  · haveI : Subsingleton (HSOp ℋ) := h
    ext x
    exact Subsingleton.elim _ _
  · letI : ContinuousFunctionalCalculus ℝ ((QuantumState.B ℋ)ᵐᵒᵖ) IsSelfAdjoint :=
      (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
        (A := (QuantumState.B ℋ)ᵐᵒᵖ)).toContinuousFunctionalCalculus
    let φ : (ℋ →L[ℂ] ℋ)ᵐᵒᵖ →⋆ₐ[ℝ] (HSOp ℋ →L[ℂ] HSOp ℋ) := rightMulHSStarAlgHom (ℋ := ℋ)
    have hφ : Continuous φ := by
      simpa [rightMulHSLinearMap] using
        (LinearMap.continuous_of_finiteDimensional (rightMulHSLinearMap (ℋ := ℋ)))
    have hopA : IsSelfAdjoint (MulOpposite.op A : (ℋ →L[ℂ] ℋ)ᵐᵒᵖ) := isSelfAdjoint_op
        (A := A) hA
    have hφA : IsSelfAdjoint (φ (MulOpposite.op A)) := hopA.map φ
    have hmap := StarAlgHom.map_cfc (φ := φ) (f := f) (a := MulOpposite.op A)
      (hf := by simpa [spectrum_op_eq (A := A) hA] using hf)
      (hφ := hφ) (ha := hopA) (hφa := hφA)
    have hopcfc :
        cfc (R := ℝ) (A := (ℋ →L[ℂ] ℋ)ᵐᵒᵖ) (p := IsSelfAdjoint) f (MulOpposite.op A) =
          MulOpposite.op (cfcR f A) :=
      cfc_op_eq_op_cfc (ℋ := ℋ) f A hA hf
    dsimp only [φ, rightMulHSStarAlgHom] at hmap
    simpa [cfcR, hopcfc] using hmap

end

end HilbertSchmidtOperatorSpace
