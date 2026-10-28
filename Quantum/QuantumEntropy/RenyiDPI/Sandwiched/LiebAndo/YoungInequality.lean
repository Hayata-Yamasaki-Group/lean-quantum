/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.OperatorInstances
import Mathlib.Analysis.CStarAlgebra.Matrix
import Quantum.QuantumEntropy.YoungInequality

open QuantumState
open scoped ComplexOrder
open scoped MatrixOrder
open scoped Matrix.Norms.L2Operator

universe u

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

section ReverseYoung

/-- Bernoulli inequality for non-positive exponents: t^r ≥ 1 + r*(t - 1) for t > 0, r ≤ 0.
    Proved via exp convexity (1+x ≤ exp x) and log ≤ id-1. -/
private lemma rpow_ge_one_add_mul {t : ℝ} (ht : 0 < t) {r : ℝ} (hr : r ≤ 0) :
    1 + r * (t - 1) ≤ t ^ r := by
  have h_log_le : Real.log t ≤ t - 1 := by
    have h := Real.add_one_le_exp (Real.log t)
    rw [Real.exp_log ht] at h; linarith
  have h_rpow : r * Real.log t + 1 ≤ t ^ r := by
    have h := Real.add_one_le_exp (r * Real.log t)
    have : Real.exp (r * Real.log t) = t ^ r := by
      rw [show r * Real.log t = Real.log t * r from mul_comm _ _]
      exact (Real.rpow_def_of_pos ht r).symm
    linarith
  linarith [mul_le_mul_of_nonpos_left h_log_le hr]

/-- Scalar reverse Young inequality for strictly positive reals:
    a^r/r + b^s/s ≤ a*b when r < 0, 0 < s < 1, 1/r + 1/s = 1. -/
lemma reverse_young_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {r s : ℝ} (hr : r < 0) (hs0 : 0 < s) (hs1 : s < 1)
    (hrs : 1 / r + 1 / s = 1) :
    a ^ r / r + b ^ s / s ≤ a * b := by
  have hbs_pos : 0 < b ^ (1 - s) := Real.rpow_pos_of_pos hb _
  have ht_pos : 0 < a * b ^ (1 - s) := mul_pos ha hbs_pos
  have hBern := rpow_ge_one_add_mul ht_pos hr.le
  have hexp : (1 - s) * r = -s := by
    have h1r : 1 / r = 1 - 1 / s := by linarith
    have hr0 : r ≠ 0 := ne_of_lt hr
    have hs0' : s ≠ 0 := ne_of_gt hs0
    field_simp at h1r; nlinarith
  have h_tr : (a * b ^ (1 - s)) ^ r = a ^ r * (b ^ s)⁻¹ := by
    calc (a * b ^ (1 - s)) ^ r
        = a ^ r * (b ^ (1 - s)) ^ r := Real.mul_rpow ha.le hbs_pos.le
      _ = a ^ r * b ^ ((1 - s) * r) := by rw [← Real.rpow_mul hb.le]
      _ = a ^ r * b ^ (-s) := by rw [hexp]
      _ = a ^ r * (b ^ s)⁻¹ := by rw [Real.rpow_neg hb.le]
  have hbs_val : 0 < b ^ s := Real.rpow_pos_of_pos hb _
  rw [h_tr] at hBern
  have hBern_mul : (1 + r * (a * b ^ (1 - s) - 1)) * b ^ s ≤ a ^ r := by
    rw [← div_eq_mul_inv] at hBern
    exact (le_div_iff₀ hbs_val).mp hBern
  have hbb : b ^ (1 - s) * b ^ s = b := by
    rw [← Real.rpow_add hb]; ring_nf; exact Real.rpow_one b
  have h_expanded : (1 - r) * b ^ s + r * (a * b) ≤ a ^ r := by
    have : a * b ^ (1 - s) * b ^ s = a * b := by rw [mul_assoc, hbb]
    nlinarith
  have h_1mr_s : (1 - r) * s = -r := by
    have h1r : 1 / r = 1 - 1 / s := by linarith
    have hr0 : r ≠ 0 := ne_of_lt hr
    have hs0' : s ≠ 0 := ne_of_gt hs0
    field_simp at h1r; nlinarith
  have hrs_neg : r * s < 0 := mul_neg_of_neg_of_pos hr hs0
  rw [div_add_div _ _ (ne_of_lt hr) (ne_of_gt hs0), div_le_iff_of_neg hrs_neg]
  nlinarith [h_1mr_s, h_expanded]

/-- Scalar reverse Young inequality for a > 0, b ≥ 0. -/
lemma reverse_young_of_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    {r s : ℝ} (hr : r < 0) (hs0 : 0 < s) (hs1 : s < 1)
    (hrs : 1 / r + 1 / s = 1) :
    a ^ r / r + b ^ s / s ≤ a * b := by
  rcases eq_or_lt_of_le hb with rfl | hb_pos
  · simp only [Real.zero_rpow (ne_of_gt hs0), zero_div, add_zero, mul_zero]
    exact div_nonpos_of_nonneg_of_nonpos (Real.rpow_pos_of_pos ha _).le hr.le
  · exact reverse_young_of_pos ha hb_pos hr hs0 hs1 hrs

/-- Weighted reverse Young inequality with doubly stochastic coefficients. -/
lemma weighted_reverse_young_finset {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r s : ℝ) (hr : r < 0) (hs0 : 0 < s) (hs1 : s < 1) (hrs : 1 / r + 1 / s = 1)
    (x : ι → ℝ) (y : κ → ℝ) (c : ι → κ → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 ≤ y j) (hc : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, (∑ j, c i j) = 1) (hcol : ∀ j, (∑ i, c i j) = 1) :
    (∑ i, x i ^ r) / r + (∑ j, y j ^ s) / s
      ≤ ∑ i, ∑ j, x i * y j * c i j := by
  calc
    (∑ i, x i ^ r) / r + (∑ j, y j ^ s) / s
        = (∑ i, x i ^ r / r) + (∑ j, y j ^ s / s) := by
      simp [Finset.sum_div]
    _ = (∑ i, x i ^ r / r * (∑ j, c i j)) +
        (∑ j, y j ^ s / s * (∑ i, c i j)) := by
      simp [hrow, hcol]
    _ = (∑ i, ∑ j, x i ^ r / r * c i j) +
        (∑ i, ∑ j, y j ^ s / s * c i j) := by
      congr 1
      · simp_rw [Finset.mul_sum]
      · simp_rw [Finset.mul_sum, Finset.sum_comm (f := fun j i => y j ^ s / s * c i j)]
    _ = ∑ i, ∑ j, (x i ^ r / r + y j ^ s / s) * c i j := by
      simp_rw [← Finset.sum_add_distrib, ← add_mul]
    _ ≤ ∑ i, ∑ j, x i * y j * c i j := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      exact mul_le_mul_of_nonneg_right
        (reverse_young_of_nonneg (hx i) (hy j) hr hs0 hs1 hrs) (hc i j)

lemma weighted_reverse_young_overlap {ℋ : Type u} [Qudit ℋ] {r s : ℝ}
    (hr : r < 0) (hs0 : 0 < s) (hs1 : s < 1) (hrs : 1 / r + 1 / s = 1)
    (bx bY : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ)
    (x y : Fin (Module.finrank ℂ ℋ) → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 ≤ y j) :
    (∑ i, x i ^ r) / r + (∑ j, y j ^ s) / s
      ≤ ∑ i, ∑ j, x i * y j * ‖inner ℂ (bx i) (bY j)‖ ^ 2 := by
  simpa using
    weighted_reverse_young_finset r s hr hs0 hs1 hrs x y
      (fun i j => ‖inner ℂ (bx i) (bY j)‖ ^ 2)
      hx hy (overlap_coeff_nonneg bx bY)
      (overlap_coeff_row_sum bx bY) (overlap_coeff_col_sum bx bY)

/-- Strictly positive eigenvalues for positive definite operators. -/
lemma pos_eigenvalues_of_isPositive_of_isUnit {ℋ : Type u} [Qudit ℋ]
    (X : L ℋ) (hX : X.IsPositive) (hX_unit : IsUnit X) :
    ∀ i, 0 < hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i := by
  intro i
  have h_nn := hX.nonneg_eigenvalues (hn := rfl) i
  refine lt_of_le_of_ne h_nn (fun h => ?_)
  have h_eigvec := hX.isSymmetric.apply_eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl i
  have h_ker : X (hX.isSymmetric.eigenvectorBasis rfl i) = 0 := by
    rw [h_eigvec]
    haveI : IsScalarTower ℝ ℂ ℋ := RestrictScalars.isScalarTower ℝ ℂ ℋ
    simp [← h, Algebra.algebraMap_eq_smul_one]
  have h_ne : hX.isSymmetric.eigenvectorBasis rfl i ≠ 0 :=
    (hX.isSymmetric.eigenvectorBasis rfl).toBasis.ne_zero i
  obtain ⟨u, hu⟩ := hX_unit
  have h_inj : Function.Injective X := by
    have : Function.LeftInverse (↑u⁻¹ : L ℋ) X := by
      intro x
      change (↑u⁻¹ * X) x = x
      rw [← hu, Units.inv_mul]
      rfl
    exact this.injective
  have h_ker' : X (hX.isSymmetric.eigenvectorBasis rfl i) = X 0 := by
    rw [h_ker, map_zero]
  exact absurd (h_inj h_ker') h_ne

/-- Trace of rpow for pd operators as sum of eigenvalue powers (all exponents). -/
lemma trace_rpow_eq_sum_eigenvalues_pd {ℋ : Type u} [Qudit ℋ]
    (X : B ℋ) (hX : X.IsPositive) (hX_unit : IsUnit X) (p : ℝ) :
    Tr ((CFC.rpow X p : B ℋ) : L ℋ)
      = ((((∑ i : Fin (Module.finrank ℂ ℋ),
              (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ p) : ℝ)) : ℂ) := by
  by_cases hp : 0 ≤ p
  · exact trace_rpow_eq_sum_eigenvalues X hX p hp
  · let bx := hX.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
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
        have hmap := congrArg Matrix.trace (toMatrixOrthonormal_rpow_pd bx X hX hX_unit p)
        have htrace := matrix_trace_rpow_eq_sum_eigenvalues M hMherm hMnonneg p
        exact hmap.trans (by simpa [M] using htrace)
      _ = (((∑ i : Fin (Module.finrank ℂ ℋ), (hMherm.eigenvalues i) ^ p) : ℝ) : ℂ) := by
        simp
      _ = (((∑ i : Fin (Module.finrank ℂ ℋ), (eVals i) ^ p) : ℝ) : ℂ) :=
        congrArg (fun r : ℝ => (r : ℂ)) hsumPow
      _ = ((((∑ i : Fin (Module.finrank ℂ ℋ),
                (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ p) : ℝ)) : ℂ) := by
        simp [eVals]

/-- Reverse trace Young inequality: for r < 0, s ∈ (0, 1), 1/r + 1/s = 1,
    M positive definite, N positive semidefinite:
    Tr(M^r)/r + Tr(N^s)/s ≤ Tr(M ∘ₗ N).

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
theorem trace_reverse_young_inequality {ℋ : Type u} [Qudit ℋ] {r s : ℝ}
    (hr : r < 0) (hs0 : 0 < s) (hs1 : s < 1) (hrs : 1 / r + 1 / s = 1)
    (M N : B ℋ) (hM : M.IsPositive) (hM_unit : IsUnit M) (hN : N.IsPositive) :
    Tr ((CFC.rpow M r : B ℋ) : L ℋ) / r +
      Tr ((CFC.rpow N s : B ℋ) : L ℋ) / s ≤
      Tr ((M : L ℋ) ∘ₗ (N : L ℋ)) := by
  let bM := hM.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
  let bN := hN.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
  have hdouble := trace_comp_eq_double_sum_eigen_overlap
    (M : L ℋ) (N : L ℋ) hM.toLinearMap hN.toLinearMap
  have hM_unit_lm : IsUnit (M : L ℋ) :=
    (ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap (f := M)).mp hM_unit
  have hMpos :
      ∀ i : Fin (Module.finrank ℂ ℋ),
        0 < hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i :=
    pos_eigenvalues_of_isPositive_of_isUnit (M : L ℋ) hM.toLinearMap hM_unit_lm
  have hNnonneg :
      ∀ j : Fin (Module.finrank ℂ ℋ),
        0 ≤ hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j := by
    intro j
    exact hN.toLinearMap.nonneg_eigenvalues (hn := rfl) j
  have hRevYoung :=
    weighted_reverse_young_overlap hr hs0 hs1 hrs bM bN
      (fun i => hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
      (fun j => hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
      hMpos hNnonneg
  have hbound_double_real :
      ((∑ i : Fin (Module.finrank ℂ ℋ),
            (hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ r) / r : ℝ)
          + ((∑ j : Fin (Module.finrank ℂ ℋ),
            (hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j) ^ s) / s : ℝ)
        ≤ (∑ j : Fin (Module.finrank ℂ ℋ),
          (hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
            * (∑ i : Fin (Module.finrank ℂ ℋ),
                (hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
                  * Complex.normSq (inner ℂ (bM i) (bN j)))) := by
    calc
      ((∑ i : Fin (Module.finrank ℂ ℋ),
            (hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ r) / r : ℝ)
          + ((∑ j : Fin (Module.finrank ℂ ℋ),
            (hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j) ^ s) / s : ℝ)
        ≤ ∑ i : Fin (Module.finrank ℂ ℋ), ∑ j : Fin (Module.finrank ℂ ℋ),
            (hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
              * (hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
              * ‖inner ℂ (bM i) (bN j)‖ ^ 2 := hRevYoung
      _ = ∑ j : Fin (Module.finrank ℂ ℋ), ∑ i : Fin (Module.finrank ℂ ℋ),
            (hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
              * (hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
              * ‖inner ℂ (bM i) (bN j)‖ ^ 2 := Finset.sum_comm
      _ = ∑ j : Fin (Module.finrank ℂ ℋ),
          (hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
            * (∑ i : Fin (Module.finrank ℂ ℋ),
                (hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
                  * Complex.normSq (inner ℂ (bM i) (bN j))) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        simp [Complex.normSq_eq_norm_sq, mul_assoc, mul_left_comm]
  have hbound_double_complex :
      Tr ((CFC.rpow M r : B ℋ) : L ℋ) / r +
          Tr ((CFC.rpow N s : B ℋ) : L ℋ) / s
        ≤ Tr ((M : L ℋ) ∘ₗ (N : L ℋ)) := by
    rw [hdouble]
    have htraceM := trace_rpow_eq_sum_eigenvalues_pd M hM hM_unit r
    have hs_nonneg : 0 ≤ s := hs0.le
    have htraceN := trace_rpow_eq_sum_eigenvalues N hN s hs_nonneg
    have htraceM' :
        Tr ((CFC.rpow M r : B ℋ) : L ℋ) =
          ∑ i : Fin (Module.finrank ℂ ℋ),
            (((hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ r : ℝ) : ℂ) := by
      simpa using htraceM
    have htraceN' :
        Tr ((CFC.rpow N s : B ℋ) : L ℋ) =
          ∑ j : Fin (Module.finrank ℂ ℋ),
            (((hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j) ^ s : ℝ) : ℂ) := by
      simpa using htraceN
    rw [htraceM', htraceN']
    exact_mod_cast hbound_double_real
  exact hbound_double_complex

end ReverseYoung
