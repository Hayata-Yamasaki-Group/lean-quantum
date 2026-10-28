/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.OperatorInstances
import Mathlib.Analysis.CStarAlgebra.Matrix
import Quantum.QuantumMechanics.OperatorBridge

open QuantumState
open scoped ComplexOrder
open scoped MatrixOrder
open scoped Matrix.Norms.L2Operator

universe u

/-- `CStarAlgebra` structure on the square complex matrices of size `Module.finrank ℂ ℋ`,
with the L2 operator norm opened above (Mathlib keeps matrix norms scoped). The fields are
filled from existing instances. This is a global instance, visible in every module that
imports this file; it is used where operators on `ℋ` are compared with matrices, for example
in the Umegaki data-processing proofs. -/
noncomputable instance matrixCStarAlgebra {ℋ : Type u} [Qudit ℋ] :
    CStarAlgebra (Matrix (Fin (Module.finrank ℂ ℋ)) (Fin (Module.finrank ℂ ℋ)) ℂ) where

/-- The signature of `CFC.rpow` fixes the semiring argument of `StarRing` from `[Ring A]`
through the projection chain `Ring.toNonAssocRing → NonAssocRing.toNonUnitalNonAssocRing →
NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring`. Goals with this chain at matrix types
cannot be unified at instance transparency with the argument coming from
`Matrix.nonUnitalNonAssocSemiring` on the `Matrix.instStarRing` side (they are defeq at
default transparency). The product and order structures on the corresponding linear maps are
used. -/
private noncomputable local instance matrixStarRingOfRing
    {n : Type*} [Fintype n] [DecidableEq n] :
    @StarRing (Matrix n n ℂ)
      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring _
        (@NonAssocRing.toNonUnitalNonAssocRing _
          (@Ring.toNonAssocRing _ Matrix.instRing))) :=
  Matrix.instStarRing

/-- For `NonnegSpectrumClass` goals with the `NonUnitalRing`/`Module` arguments fixed by the
signature of `CFC.rpow` from `[Ring A]` and `[Algebra ℝ A]`. Instead of the argument chain of
`Matrix.instNonnegSpectrumClass` (scoped `MatrixOrder`), the structure corresponding to the
linear-map representation is used. -/
private local instance matrixNonnegSpectrumClassOfRing
    {n : Type*} [Fintype n] [DecidableEq n] :
    @NonnegSpectrumClass ℝ (Matrix n n ℂ) Real.instCommSemiring Real.partialOrder
      (@Ring.toNonUnitalRing _ Matrix.instRing)
      inferInstance
      (@Algebra.toModule ℝ _ Real.instCommSemiring (@Ring.toSemiring _ Matrix.instRing)
        inferInstance) :=
  Matrix.instNonnegSpectrumClass

lemma weighted_young_finset {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p q : ℝ) (hpq : p.HolderConjugate q)
    (x : ι → ℝ) (y : κ → ℝ) (c : ι → κ → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j) (hc : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, (∑ j, c i j) = 1) (hcol : ∀ j, (∑ i, c i j) = 1) :
    (∑ i, ∑ j, x i * y j * c i j)
      ≤ (∑ i, x i ^ p) / p + (∑ j, y j ^ q) / q := by
  calc
    (∑ i, ∑ j, x i * y j * c i j)
        ≤ ∑ i, ∑ j, ((x i ^ p) / p + (y j ^ q) / q) * c i j := by
      refine Finset.sum_le_sum ?_
      intro i hi
      refine Finset.sum_le_sum ?_
      intro j hj
      have hyoung : x i * y j ≤ x i ^ p / p + y j ^ q / q :=
        Real.young_inequality_of_nonneg (hx i) (hy j) hpq
      exact mul_le_mul_of_nonneg_right hyoung (hc i j)
    _ = (∑ i, ∑ j, (x i ^ p / p) * c i j) + (∑ i, ∑ j, (y j ^ q / q) * c i j) := by
      simp [add_mul, Finset.sum_add_distrib]
    _ = (∑ i, (x i ^ p / p) * (∑ j, c i j)) + (∑ j, (y j ^ q / q) * (∑ i, c i j)) := by
      have hxpart : (∑ i, ∑ j, (x i ^ p / p) * c i j) = ∑ i, (x i ^ p / p) * (∑ j, c i j) := by
        simp [Finset.mul_sum]
      have hypart : (∑ i, ∑ j, (y j ^ q / q) * c i j) = ∑ j, (y j ^ q / q) * (∑ i, c i j) := by
        calc
          (∑ i, ∑ j, (y j ^ q / q) * c i j) = ∑ j, ∑ i, (y j ^ q / q) * c i j := by
            rw [Finset.sum_comm]
          _ = ∑ j, (y j ^ q / q) * (∑ i, c i j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [Finset.mul_sum]
      simp [hxpart, hypart]
    _ = (∑ i, x i ^ p / p) + (∑ j, y j ^ q / q) := by
      simp [hrow, hcol]
    _ = (∑ i, x i ^ p) / p + (∑ j, y j ^ q) / q := by
      simp [div_eq_mul_inv, Finset.sum_mul]

lemma trace_comp_eq_sum_eigen_right {ℋ : Type u} [Qudit ℋ] (X Y : L ℋ) (hY : Y.IsPositive) :
    Tr (X ∘ₗ Y)
      = ∑ i : Fin (Module.finrank ℂ ℋ),
          ((hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i : ℝ) : ℂ)
            * inner ℂ
                (hY.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl i)
                (X (hY.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl i)) := by
  let b := hY.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
  calc
    Tr (X ∘ₗ Y) = ∑ i : Fin (Module.finrank ℂ ℋ), inner ℂ (b i) ((X ∘ₗ Y) (b i)) := by
      simpa [QuantumState.Tr] using LinearMap.trace_eq_sum_inner (T := X ∘ₗ Y) b
    _ = ∑ i : Fin (Module.finrank ℂ ℋ), inner ℂ (b i) (X (Y (b i))) := by
      simp
    _ = ∑ i : Fin (Module.finrank ℂ ℋ),
          inner ℂ (b i)
            (X (((hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i : ℝ) : ℂ) • b i)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [b] at *
    _ = ∑ i : Fin (Module.finrank ℂ ℋ),
          ((hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i : ℝ) : ℂ)
            * inner ℂ (b i) (X (b i)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, inner_smul_right]

lemma tr_eq_matrix_trace_orthonormal {ℋ : Type u} [Qudit ℋ]
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ) (T : L ℋ) :
    Tr T = Matrix.trace (LinearMap.toMatrixOrthonormal b T) := by
  simpa [QuantumState.Tr, LinearMap.toMatrixOrthonormal] using
    (LinearMap.trace_eq_matrix_trace (R := ℂ) (b := b.toBasis) (f := T))

lemma toMatrixOrthonormal_rpow {ℋ : Type u} [Qudit ℋ]
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ) (X : B ℋ)
    (hX : X.IsPositive) (p : ℝ) (hp : 0 ≤ p) :
    LinearMap.toMatrixOrthonormal b
      ((CFC.rpow X p : B ℋ) : L ℋ)
      = CFC.rpow (LinearMap.toMatrixOrthonormal b (X : L ℋ)) p := by
  haveI : IsScalarTower ℝ ℂ (B ℋ) :=
    RestrictScalars.isScalarTower ℝ ℂ (B ℋ)
  have hXnonneg : 0 ≤ X := (ContinuousLinearMap.nonneg_iff_isPositive X).2 hX
  let φ : B ℋ ≃⋆ₐ[ℂ]
      Matrix (Fin (Module.finrank ℂ ℋ)) (Fin (Module.finrank ℂ ℋ)) ℂ :=
    (QuantumChannel.linearToContinuousEndStarAlgEquiv ℋ).symm.trans
      (LinearMap.toMatrixOrthonormal b)
  have hφ : Continuous φ := (StarAlgEquiv.isometry φ).continuous
  have hφnonneg : 0 ≤ φ X := map_nonneg φ hXnonneg
  have hφselfAdjoint : IsSelfAdjoint (φ X) :=
    IsSelfAdjoint.map hX.isSelfAdjoint φ
  have hf : ContinuousOn (fun x : ℝ => x ^ p) (spectrum ℝ X) :=
    (Real.continuous_rpow_const hp).continuousOn
  change φ (CFC.rpow X p) = CFC.rpow (φ X) p
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_pow]
  rw [CFC.rpow_eq_cfc_real (a := X) (y := p) (ha := hXnonneg)]
  rw [CFC.rpow_eq_cfc_real (a := φ X) (y := p) (ha := hφnonneg)]
  simpa using
    (StarAlgHomClass.map_cfc
      (R := ℝ)
      (φ := φ)
      (f := fun x : ℝ => x ^ p)
      (a := X)
      (hf := hf)
      (hφ := hφ)
      (ha := hX.isSelfAdjoint)
      (hφa := hφselfAdjoint))

lemma matrix_trace_rpow_eq_sum_eigenvalues {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (hA0 : 0 ≤ A) (p : ℝ) :
    Matrix.trace (CFC.rpow A p)
      = ∑ i, (((hA.eigenvalues i) ^ p : ℝ) : ℂ) := by
  rw [CFC.rpow_eq_pow]
  rw [CFC.rpow_eq_cfc_real (a := A) (y := p) (ha := hA0)]
  have htrace :
      Matrix.trace (cfc (fun x : ℝ => x ^ p) A)
        = ((Matrix.charpoly (cfc (fun x : ℝ => x ^ p) A)).roots.sum) := by
    simpa using (Matrix.trace_eq_sum_roots_charpoly (A := cfc (fun x : ℝ => x ^ p) A))
  rw [htrace]
  rw [hA.charpoly_cfc_eq (f := fun x : ℝ => x ^ p)]
  have hroots :
      (Polynomial.roots
        (∏ i, (Polynomial.X - Polynomial.C ((((hA.eigenvalues i) ^ p : ℝ)) : ℂ))))
        = (Finset.univ.val.bind fun i =>
            Polynomial.roots
              (Polynomial.X - Polynomial.C ((((hA.eigenvalues i) ^ p : ℝ)) : ℂ))) := by
    exact Polynomial.roots_prod
      (f := fun i => (Polynomial.X - Polynomial.C ((((hA.eigenvalues i) ^ p : ℝ)) : ℂ)))
      (s := Finset.univ)
      (Finset.prod_ne_zero_iff.mpr (by
        intro i hi
        exact Polynomial.X_sub_C_ne_zero _))
  have hsum := congrArg Multiset.sum hroots
  simpa using hsum

lemma toMatrixOrthonormal_eq_diagonal_eigenvalues {ℋ : Type u} [Qudit ℋ]
    (X : L ℋ) (hX : X.IsPositive) :
    LinearMap.toMatrixOrthonormal (hX.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl) X
      = Matrix.diagonal (fun i =>
          (((hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) : ℝ) : ℂ)) := by
  let bx := hX.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [LinearMap.toMatrixOrthonormal_apply_apply,
      hX.isSymmetric.apply_eigenvectorBasis, Matrix.diagonal_apply_eq]
    haveI : IsScalarTower ℝ ℂ ℋ := RestrictScalars.isScalarTower ℝ ℂ ℋ
    rw [inner_smul_right_eq_smul, inner_self_eq_one_of_norm_eq_one (bx.norm_eq_one i),
      Algebra.smul_def, mul_one]
    exact Algebra.algebraMap_self_apply _
  · simp [LinearMap.toMatrixOrthonormal_apply_apply, hij,
      hX.isSymmetric.apply_eigenvectorBasis]

lemma sum_rpow_eq_of_multiset_map_eq {ι : Type*} [Fintype ι]
    (f g : ι → ℝ) (p : ℝ)
    (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    (∑ i, (f i) ^ p) = ∑ i, (g i) ^ p := by
  have hpow := congrArg (Multiset.map (fun x : ℝ => x ^ p)) h
  have hsum := congrArg Multiset.sum hpow
  simpa using hsum

lemma trace_rpow_eq_sum_eigenvalues {ℋ : Type u} [Qudit ℋ]
    (X : B ℋ) (hX : X.IsPositive) (p : ℝ) (hp : 0 ≤ p) :
    Tr ((CFC.rpow X p : B ℋ) : L ℋ)
      = ((((∑ i : Fin (Module.finrank ℂ ℋ),
              (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ p) : ℝ)) : ℂ) := by
  let bx := hX.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
  let eVals : Fin (Module.finrank ℂ ℋ) → ℝ :=
    fun i => hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i
  let M : Matrix (Fin (Module.finrank ℂ ℋ)) (Fin (Module.finrank ℂ ℋ)) ℂ :=
    LinearMap.toMatrixOrthonormal bx (X : L ℋ)
  have hMnonneg : 0 ≤ M := by
    simpa [M] using map_nonneg (LinearMap.toMatrixOrthonormal bx)
      ((LinearMap.nonneg_iff_isPositive (X : L ℋ)).2 hX.toLinearMap)
  have hMherm : M.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hMnonneg).1
  have hrootsDiag :
      M.charpoly.roots = Multiset.map (RCLike.ofReal ∘ eVals) Finset.univ.val := by
    rw [show M = Matrix.diagonal (fun i => ((eVals i : ℝ) : ℂ)) by
      simpa [M, eVals] using
        toMatrixOrthonormal_eq_diagonal_eigenvalues (X : L ℋ) hX.toLinearMap,
      Matrix.charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hrealMulti :
      Multiset.map hMherm.eigenvalues Finset.univ.val = Multiset.map eVals Finset.univ.val := by
    simpa [Function.comp, eVals] using congrArg (Multiset.map Complex.re)
      (hMherm.roots_charpoly_eq_eigenvalues.symm.trans hrootsDiag)
  have hsumPow :
      (∑ i : Fin (Module.finrank ℂ ℋ), (hMherm.eigenvalues i) ^ p)
        = ∑ i : Fin (Module.finrank ℂ ℋ), (eVals i) ^ p :=
    sum_rpow_eq_of_multiset_map_eq (hMherm.eigenvalues) eVals p hrealMulti
  calc
    Tr ((CFC.rpow X p : B ℋ) : L ℋ) =
        Matrix.trace
          (LinearMap.toMatrixOrthonormal bx ((CFC.rpow X p : B ℋ) : L ℋ)) :=
      tr_eq_matrix_trace_orthonormal bx ((CFC.rpow X p : B ℋ) : L ℋ)
    _ = ∑ i : Fin (Module.finrank ℂ ℋ), (((hMherm.eigenvalues i) ^ p : ℝ) : ℂ) := by
      have hmap := congrArg Matrix.trace (toMatrixOrthonormal_rpow bx X hX p hp)
      have htrace := matrix_trace_rpow_eq_sum_eigenvalues M hMherm hMnonneg p
      exact hmap.trans (by simpa [M] using htrace)
    _ = (((∑ i : Fin (Module.finrank ℂ ℋ), (hMherm.eigenvalues i) ^ p) : ℝ) : ℂ) := by
      simp
    _ = (((∑ i : Fin (Module.finrank ℂ ℋ), (eVals i) ^ p) : ℝ) : ℂ) :=
      congrArg (fun r : ℝ => (r : ℂ)) hsumPow
    _ = ((((∑ i : Fin (Module.finrank ℂ ℋ),
              (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ p) : ℝ)) : ℂ) := by
      simp [eVals]

lemma overlap_coeff_nonneg {ℋ : Type u} [Qudit ℋ]
    (bx bY : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ) :
    ∀ i j, 0 ≤ ‖inner ℂ (bx i) (bY j)‖ ^ 2 := by
  intro i j
  positivity

lemma overlap_coeff_row_sum {ℋ : Type u} [Qudit ℋ]
    (bx bY : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ) :
    ∀ i, (∑ j, ‖inner ℂ (bx i) (bY j)‖ ^ 2) = 1 := by
  intro i
  simpa [bx.norm_eq_one i] using bY.sum_sq_norm_inner_left (x := bx i)

lemma overlap_coeff_col_sum {ℋ : Type u} [Qudit ℋ]
    (bx bY : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ) :
    ∀ j, (∑ i, ‖inner ℂ (bx i) (bY j)‖ ^ 2) = 1 := by
  intro j
  simpa [bY.norm_eq_one j] using bx.sum_sq_norm_inner_right (x := bY j)

lemma weighted_young_overlap {ℋ : Type u} [Qudit ℋ] {p q : ℝ} (hpq : p.HolderConjugate q)
    (bx bY : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ)
    (x y : Fin (Module.finrank ℂ ℋ) → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ j, 0 ≤ y j) :
    (∑ i, ∑ j, x i * y j * ‖inner ℂ (bx i) (bY j)‖ ^ 2)
      ≤ (∑ i, x i ^ p) / p + (∑ j, y j ^ q) / q := by
  simpa using
    weighted_young_finset p q hpq x y
      (fun i j => ‖inner ℂ (bx i) (bY j)‖ ^ 2)
      hx hy (overlap_coeff_nonneg bx bY)
      (overlap_coeff_row_sum bx bY) (overlap_coeff_col_sum bx bY)

lemma inner_apply_eq_sum_eigen_overlap {ℋ : Type u} [Qudit ℋ]
    (X : L ℋ) (hX : X.IsPositive)
    (bY : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ)
    (j : Fin (Module.finrank ℂ ℋ)) :
    inner ℂ (bY j) (X (bY j))
      = ∑ i : Fin (Module.finrank ℂ ℋ),
          ((hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i : ℝ) : ℂ)
            * Complex.normSq (inner ℂ
                (hX.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl i) (bY j)) := by
  let bx := hX.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
  calc
    inner ℂ (bY j) (X (bY j))
        = inner ℂ (bY j) (X (∑ i : Fin (Module.finrank ℂ ℋ), inner ℂ (bx i) (bY j) • bx i)) := by
      simp [bx.sum_repr']
    _ = inner ℂ (bY j) (∑ i : Fin (Module.finrank ℂ ℋ), inner ℂ (bx i) (bY j) • X (bx i)) := by
      simp [map_sum, map_smul]
    _ = ∑ i : Fin (Module.finrank ℂ ℋ), inner ℂ (bY j) (inner ℂ (bx i) (bY j) • X (bx i)) := by
      simp
    _ = ∑ i : Fin (Module.finrank ℂ ℋ),
          inner ℂ (bx i) (bY j)
            * (((hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i : ℝ) : ℂ)
              * inner ℂ (bY j) (bx i)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [hX.isSymmetric.apply_eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl i]
      haveI : IsScalarTower ℝ ℂ ℋ := RestrictScalars.isScalarTower ℝ ℂ ℋ
      rw [inner_smul_right, inner_smul_right_eq_smul]
      congr 1
    _ = ∑ i : Fin (Module.finrank ℂ ℋ),
          ((hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i : ℝ) : ℂ)
            * Complex.normSq (inner ℂ (bx i) (bY j)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hconj : inner ℂ (bY j) (bx i) = (starRingEnd ℂ) (inner ℂ (bx i) (bY j)) := by
        simp
      rw [hconj, Complex.normSq_eq_conj_mul_self]
      ring

lemma trace_comp_eq_double_sum_eigen_overlap {ℋ : Type u} [Qudit ℋ]
    (X Y : L ℋ) (hX : X.IsPositive) (hY : Y.IsPositive) :
    Tr (X ∘ₗ Y)
      = ∑ j : Fin (Module.finrank ℂ ℋ),
          ((hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j : ℝ) : ℂ)
            * (∑ i : Fin (Module.finrank ℂ ℋ),
                ((hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i : ℝ) : ℂ)
                  * Complex.normSq (inner ℂ
                      (hX.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl i)
                      (hY.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl j))) := by
  calc
    Tr (X ∘ₗ Y)
        = ∑ j : Fin (Module.finrank ℂ ℋ),
            ((hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j : ℝ) : ℂ)
              * inner ℂ
                  (hY.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl j)
                  (X (hY.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl j)) := by
      simpa [Finset.sum_mul] using trace_comp_eq_sum_eigen_right X Y hY
    _ = ∑ j : Fin (Module.finrank ℂ ℋ),
          ((hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j : ℝ) : ℂ)
            * (∑ i : Fin (Module.finrank ℂ ℋ),
                ((hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i : ℝ) : ℂ)
                  * Complex.normSq (inner ℂ
                      (hX.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl i)
                      (hY.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl j))) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [inner_apply_eq_sum_eigen_overlap X hX
        (hY.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl) j]

-- The simplification is followed by a rewrite of the inner-product identity.
/--
Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence).
-/
theorem trace_young_inequality {ℋ : Type u} [Qudit ℋ] {p q : ℝ} (hpq : p.HolderConjugate q)
  (X Y : B ℋ) (hX : X.IsPositive) (hY : Y.IsPositive) :
  Tr ((X : L ℋ) ∘ₗ (Y : L ℋ)) ≤
    Tr ((CFC.rpow X p : B ℋ) : L ℋ) / p +
      Tr ((CFC.rpow Y q : B ℋ) : L ℋ) / q := by
  let bx := hX.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
  let bY := hY.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
  have hdouble := trace_comp_eq_double_sum_eigen_overlap
    (X : L ℋ) (Y : L ℋ) hX.toLinearMap hY.toLinearMap
  have hYoung :=
    weighted_young_overlap hpq bx bY
      (fun i => hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
      (fun j => hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
      (fun i => hX.toLinearMap.nonneg_eigenvalues
        (hn := (rfl : Module.finrank ℂ ℋ = Module.finrank ℂ ℋ)) i)
      (fun j => hY.toLinearMap.nonneg_eigenvalues
        (hn := (rfl : Module.finrank ℂ ℋ = Module.finrank ℂ ℋ)) j)
  have hbound_double_real :
      (∑ j : Fin (Module.finrank ℂ ℋ),
          (hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
            * (∑ i : Fin (Module.finrank ℂ ℋ),
                (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
                  * Complex.normSq (inner ℂ (bx i) (bY j))))
        ≤ ((∑ i : Fin (Module.finrank ℂ ℋ),
              (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ p) / p : ℝ)
            + ((∑ j : Fin (Module.finrank ℂ ℋ),
              (hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j) ^ q) / q : ℝ) := by
    calc
      (∑ j : Fin (Module.finrank ℂ ℋ),
          (hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
            * (∑ i : Fin (Module.finrank ℂ ℋ),
                (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
                  * Complex.normSq (inner ℂ (bx i) (bY j))))
          = ∑ i : Fin (Module.finrank ℂ ℋ), ∑ j : Fin (Module.finrank ℂ ℋ),
              (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
                * (hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
                * ‖inner ℂ (bx i) (bY j)‖ ^ 2 := by
            rw [Finset.sum_comm]
            simp [Finset.mul_sum, Complex.normSq_eq_norm_sq, mul_assoc, mul_left_comm]
      _ ≤ ((∑ i : Fin (Module.finrank ℂ ℋ),
              (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ p) / p : ℝ)
            + ((∑ j : Fin (Module.finrank ℂ ℋ),
              (hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j) ^ q) / q : ℝ) := hYoung
  have htraceX := trace_rpow_eq_sum_eigenvalues X hX p hpq.nonneg
  have htraceY := trace_rpow_eq_sum_eigenvalues Y hY q hpq.symm.nonneg
  calc
    Tr ((X : L ℋ) ∘ₗ (Y : L ℋ))
      ≤ ((((∑ i : Fin (Module.finrank ℂ ℋ),
              (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ p) / p : ℝ)
            + ((∑ j : Fin (Module.finrank ℂ ℋ),
              (hY.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j) ^ q) / q : ℝ)) : ℂ) :=
      by rw [hdouble]; exact_mod_cast hbound_double_real
    _ = Tr ((CFC.rpow X p : B ℋ) : L ℋ) / p +
        Tr ((CFC.rpow Y q : B ℋ) : L ℋ) / q := by
      rw [htraceX, htraceY]
      push_cast
      rfl

section ReverseYoung

/-- Matrix representation of rpow for positive definite operators (any exponent). -/
lemma toMatrixOrthonormal_rpow_pd {ℋ : Type u} [Qudit ℋ]
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ) (X : B ℋ)
    (hX : X.IsPositive) (hX_unit : IsUnit X) (p : ℝ) :
    LinearMap.toMatrixOrthonormal b
      ((CFC.rpow X p : B ℋ) : L ℋ)
      = CFC.rpow (LinearMap.toMatrixOrthonormal b (X : L ℋ)) p := by
  haveI : IsScalarTower ℝ ℂ (B ℋ) :=
    RestrictScalars.isScalarTower ℝ ℂ (B ℋ)
  by_cases hp : 0 ≤ p
  · exact toMatrixOrthonormal_rpow b X hX p hp
  · push_neg at hp
    have hXnonneg : 0 ≤ X := (ContinuousLinearMap.nonneg_iff_isPositive X).2 hX
    let φ : B ℋ ≃⋆ₐ[ℂ]
        Matrix (Fin (Module.finrank ℂ ℋ)) (Fin (Module.finrank ℂ ℋ)) ℂ :=
      (QuantumChannel.linearToContinuousEndStarAlgEquiv ℋ).symm.trans
        (LinearMap.toMatrixOrthonormal b)
    have hφ : Continuous φ := (StarAlgEquiv.isometry φ).continuous
    have hφnonneg : 0 ≤ φ X := map_nonneg φ hXnonneg
    have hφselfAdjoint : IsSelfAdjoint (φ X) :=
      IsSelfAdjoint.map hX.isSelfAdjoint φ
    have h_spec_nn : spectrum ℝ X ⊆ Set.Ici 0 :=
      (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _
        (ha := hX.isSelfAdjoint)).1 hXnonneg
    have h0_not_mem : (0 : ℝ) ∉ spectrum ℝ X :=
      (spectrum.zero_notMem_iff (R := ℝ) (A := B ℋ)).mpr hX_unit
    have hf : ContinuousOn (fun x : ℝ => x ^ p)
        (spectrum ℝ X) :=
      ContinuousOn.rpow_const continuousOn_id fun x hx =>
        Or.inl (ne_of_gt (lt_of_le_of_ne
          (by simpa [Set.Ici] using h_spec_nn hx)
          (fun h => h0_not_mem (h ▸ hx))))
    change φ (CFC.rpow X p) = CFC.rpow (φ X) p
    rw [CFC.rpow_eq_pow, CFC.rpow_eq_pow]
    rw [CFC.rpow_eq_cfc_real (a := X) (y := p) (ha := hXnonneg)]
    rw [CFC.rpow_eq_cfc_real (a := φ X)
        (y := p) (ha := hφnonneg)]
    simpa using
      (StarAlgHomClass.map_cfc (R := ℝ)
        (φ := φ)
        (f := fun x : ℝ => x ^ p)
        (a := X) (hf := hf) (hφ := hφ)
        (ha := hX.isSelfAdjoint) (hφa := hφselfAdjoint))

end ReverseYoung
