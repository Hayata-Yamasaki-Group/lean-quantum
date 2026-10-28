/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

-- This file is long but is not split: its private declarations are specific to the proof
-- route of the midpoint kernel of Theorem 6.4, and splitting the file or making them public
-- would add API without benefit. The lemmas shared with `MatrixFunctionalCalculus` are used in
-- their public versions there.

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.TraceConvexity.ThreeVariableConvexity

/-!
# Midpoint convexity kernel for the negative rectangle

Kernel lemmas establishing the midpoint convexity of the power trace on the negative-exponent
rectangle, culminating in `powerTrace_midpointConvex_negRectangle` (Hiai–Petz Theorem 6.4).

## Main results

* `leftRightMul_matrixPower_product_isUnit` /
  `leftRightMul_matrixPower_product_qform_eq_powerTrace`: invertibility of the left/right
  multiplication operator built from matrix powers and its quadratic-form identification with
  the power trace.
* `ringInverse_leftRightMul_matrixPower_product`: the ring inverse of that operator.
* `powerTrace_midpointConvex_negRectangle`: midpoint convexity of the power trace on the
  negative rectangle.

## Implementation notes

The private-lemma dependency graph forms a single indivisible cluster, so this file is kept
undivided (see the note above the imports).

## References

* Hiai, Theorem 6.4.
-/

namespace HiaiPetz

namespace TraceConvexity

open Matrix
open scoped ComplexOrder MatrixOrder Topology
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/- Instance caches: CFC real powers on `Matrix.toEuclideanCLM` trigger deep
`synthInstance` searches (`HPow _ ℝ _` via the C⋆-algebra `Rpow` route, and the
`Algebra ℝ _` structure feeding `cfc`), each exceeding the default heartbeat
budget on its own and re-run at every use site. Caching them as section-level
reducible instances makes each search a head-match (same pattern as
`MatrixFunctionalCalculus/MatrixPower/Composition.lean`; the caches there are
`local` and do not export). -/

/-- Cached `Algebra ℝ` structure on `EuclideanSpace ℂ (Fin n) →L[ℂ] …`, feeding
the CFC route; caching it as a section-level reducible instance turns the
otherwise costly `synthInstance` search into a head-match. -/
@[reducible, local instance]
private noncomputable def instAlgebraRealEuclideanCLMScopedHp64 {n : ℕ} :
    Algebra ℝ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  inferInstance

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem leftMul_operator_nonneg {n : ℕ} {A : Mₙ n} (hA : 0 ≤ A) :
    0 ≤ leftMul A := by
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  exact leftMul_nonneg (n := n) hA

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem rightMul_operator_nonneg {n : ℕ} {B : Mₙ n} (hB : 0 ≤ B) :
    0 ≤ rightMul B := by
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  exact rightMul_nonneg (n := n) hB

/-- Local API: auxiliary algebraic fact; used in Hiai, proof of Theorem 6.4. -/
private theorem leftMul_isUnit_of_posDef {n : ℕ} {A : Mₙ n}
    (hA : Matrix.PosDef A) :
    IsUnit (leftMul A) :=
  leftMul_isUnit_of_isUnit hA.isUnit

/-- Local API: auxiliary algebraic fact; used in Hiai, proof of Theorem 6.4. -/
private theorem rightMul_isUnit_of_posDef {n : ℕ} {B : Mₙ n}
    (hB : Matrix.PosDef B) :
    IsUnit (rightMul B) :=
  rightMul_isUnit_of_isUnit hB.isUnit

/-- Local API: auxiliary algebraic fact; used in Hiai, proof of Theorem 6.4. -/
private theorem leftMul_commute_rightMul {n : ℕ} (A B : Mₙ n) :
    Commute (leftMul A) (rightMul B) := by
  change leftMul A * rightMul B = rightMul B * leftMul A
  simpa using (leftMul_comm_rightMul A B).symm

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem leftRightMul_product_nonneg {n : ℕ} {A B : Mₙ n}
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ leftMul A * rightMul B := by
  have hL : 0 ≤ leftMul A := leftMul_operator_nonneg hA
  have hR : 0 ≤ rightMul B := rightMul_operator_nonneg hB
  exact (commute_iff_mul_nonneg hL hR).mp (leftMul_commute_rightMul A B)

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem leftMul_mono {n : ℕ} {A B : Mₙ n} (hle : A ≤ B) :
    leftMul A ≤ leftMul B := by
  rw [← sub_nonneg]
  have hdiff : leftMul B - leftMul A = leftMul (B - A) := by
    ext X i j
    simp [leftMul_apply, Matrix.sub_mul]
  rw [hdiff]
  exact leftMul_operator_nonneg (sub_nonneg.mpr hle)

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem rightMul_mono {n : ℕ} {A B : Mₙ n} (hle : A ≤ B) :
    rightMul A ≤ rightMul B := by
  rw [← sub_nonneg]
  have hdiff : rightMul B - rightMul A = rightMul (B - A) := by
    ext X i j
    simp [rightMul_apply, Matrix.mul_sub]
  rw [hdiff]
  exact rightMul_operator_nonneg (sub_nonneg.mpr hle)

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem leftRightMul_product_mono {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hA₂ : 0 ≤ A₂) (hB₁ : 0 ≤ B₁)
    (hA : A₁ ≤ A₂) (hB : B₁ ≤ B₂) :
    leftMul A₁ * rightMul B₁ ≤ leftMul A₂ * rightMul B₂ := by
  rw [← sub_nonneg]
  have hA_diff : 0 ≤ A₂ - A₁ := sub_nonneg.mpr hA
  have hB_diff : 0 ≤ B₂ - B₁ := sub_nonneg.mpr hB
  have hdecomp :
      leftMul A₂ * rightMul B₂ - leftMul A₁ * rightMul B₁ =
        leftMul (A₂ - A₁) * rightMul B₁ + leftMul A₂ * rightMul (B₂ - B₁) := by
    ext X i j
    simp [leftMul_apply, rightMul_apply, Matrix.mul_add, sub_eq_add_neg]
    abel_nf
  rw [hdecomp]
  exact add_nonneg
    (leftRightMul_product_nonneg hA_diff hB₁)
    (leftRightMul_product_nonneg hA₂ hB_diff)

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem leftRightMul_matrixPower_product_nonneg {n : ℕ} {p q : ℝ}
    {A B : Mₙ n} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    0 ≤ leftMul (matrixPower p A) * rightMul (matrixPower q B) :=
  leftRightMul_product_nonneg
    (Matrix.PosDef.nonneg (matrixPower_posDef_of_posDef (r := p) hA))
    (Matrix.PosDef.nonneg (matrixPower_posDef_of_posDef (r := q) hB))

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem leftRightMul_product_isUnit {n : ℕ} {A B : Mₙ n}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    IsUnit (leftMul A * rightMul B) :=
  (leftMul_isUnit_of_posDef hA).mul (rightMul_isUnit_of_posDef hB)

/-- Source: Hiai, proof of Theorem 6.4. -/
theorem leftRightMul_matrixPower_product_isUnit {n : ℕ} {p q : ℝ}
    {A B : Mₙ n} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    IsUnit (leftMul (matrixPower p A) * rightMul (matrixPower q B)) :=
  leftRightMul_product_isUnit
    (matrixPower_posDef_of_posDef (r := p) hA)
    (matrixPower_posDef_of_posDef (r := q) hB)

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem leftRightMul_matrixPower_product_isStrictlyPositive {n : ℕ} {p q : ℝ}
    {A B : Mₙ n} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    IsStrictlyPositive (leftMul (matrixPower p A) * rightMul (matrixPower q B)) :=
  (leftRightMul_matrixPower_product_isUnit (p := p) (q := q) hA hB).isStrictlyPositive
    (leftRightMul_matrixPower_product_nonneg (p := p) (q := q) hA hB)

/-- Source: Hiai, proof of Theorem 6.4. -/
theorem leftRightMul_matrixPower_product_qform_eq_powerTrace {n : ℕ}
    {p q : ℝ} {A B X : Mₙ n} :
    Complex.re
        (Matrix.trace (Matrix.conjTranspose X *
          ((leftMul (matrixPower p A) * rightMul (matrixPower q B)) X))) =
      powerTrace p q A B X := by
  simp [powerTrace, leftMul_apply, rightMul_apply, Matrix.mul_assoc]

/-- Source: Hiai, proof of Theorem 6.4. -/
private lemma matrix_eq_sum_eigenmatrix_right_posDef
    {n : ℕ} {B : Mₙ n} (hB : Matrix.PosDef B) (X : Mₙ n) :
    X =
      ∑ j : Fin n,
        Matrix.vecMulVec
          (Matrix.mulVec X
            (hB.isSelfAdjoint.isHermitian.eigenvectorBasis j : Fin n → ℂ))
          (star (hB.isSelfAdjoint.isHermitian.eigenvectorBasis j : Fin n → ℂ)) := by
  let U : Mₙ n := hB.isSelfAdjoint.isHermitian.eigenvectorUnitary
  have hU : U * star U = (1 : Mₙ n) := by
    simp [U]
  calc
    X = X * (1 : Mₙ n) := by rw [Matrix.mul_one]
    _ = X * (U * star U) := by rw [hU]
    _ = (X * U) * star U := by rw [Matrix.mul_assoc]
    _ =
      ∑ j : Fin n,
        Matrix.vecMulVec
          (Matrix.mulVec X
            (hB.isSelfAdjoint.isHermitian.eigenvectorBasis j : Fin n → ℂ))
          (star (hB.isSelfAdjoint.isHermitian.eigenvectorBasis j : Fin n → ℂ)) := by
        ext a b
        rw [Matrix.sum_apply]
        simp [U, Matrix.mul_apply, Matrix.vecMulVec, Matrix.mulVec, dotProduct,
          Matrix.IsHermitian.eigenvectorUnitary_apply]

/-- Source: Hiai, proof of Theorem 6.4. -/
private noncomputable def powerTraceEigenCoeff
    {n : ℕ} {C D : Mₙ n} (hC : Matrix.PosDef C) (hD : Matrix.PosDef D)
    (X : Mₙ n) (j i : Fin n) : ℂ :=
  ((hC.isSelfAdjoint.isHermitian.eigenvectorBasis.toBasis).repr
    (WithLp.toLp 2
      (Matrix.mulVec X
        (hD.isSelfAdjoint.isHermitian.eigenvectorBasis j : Fin n → ℂ))) i : ℂ)

/-- Source: Hiai, proof of Theorem 6.4. -/
private noncomputable def powerTraceEigenmatrix
    {n : ℕ} {C D : Mₙ n} (hC : Matrix.PosDef C) (hD : Matrix.PosDef D)
    (j i : Fin n) : Mₙ n :=
  Matrix.vecMulVec
    ((hC.isSelfAdjoint.isHermitian.eigenvectorBasis i : Fin n → ℂ))
    (star ((hD.isSelfAdjoint.isHermitian.eigenvectorBasis j : Fin n → ℂ)))

/-- Source: Hiai, proof of Theorem 6.4. -/
private lemma matrix_eq_sum_eigenmatrix_posDef
    {n : ℕ} {A B : Mₙ n} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) (X : Mₙ n) :
    let c : Fin n → Fin n → ℂ := fun j i =>
      ((hA.isSelfAdjoint.isHermitian.eigenvectorBasis.toBasis).repr
        (WithLp.toLp 2
          (Matrix.mulVec X
            (hB.isSelfAdjoint.isHermitian.eigenvectorBasis j : Fin n → ℂ))) i : ℂ)
    let E : Fin n → Fin n → Mₙ n := fun j i =>
      Matrix.vecMulVec
        ((hA.isSelfAdjoint.isHermitian.eigenvectorBasis i : Fin n → ℂ))
        (star ((hB.isSelfAdjoint.isHermitian.eigenvectorBasis j : Fin n → ℂ)))
    X = ∑ j : Fin n, ∑ i : Fin n, c j i • E j i := by
  dsimp only
  let c : Fin n → Fin n → ℂ := fun j i =>
    ((hA.isSelfAdjoint.isHermitian.eigenvectorBasis.toBasis).repr
      (WithLp.toLp 2
        (Matrix.mulVec X
          (hB.isSelfAdjoint.isHermitian.eigenvectorBasis j : Fin n → ℂ))) i : ℂ)
  let E : Fin n → Fin n → Mₙ n := fun j i =>
    Matrix.vecMulVec
      ((hA.isSelfAdjoint.isHermitian.eigenvectorBasis i : Fin n → ℂ))
      (star ((hB.isSelfAdjoint.isHermitian.eigenvectorBasis j : Fin n → ℂ)))
  have hXj : ∀ j : Fin n,
      Matrix.vecMulVec
          (Matrix.mulVec X
            (hB.isSelfAdjoint.isHermitian.eigenvectorBasis j : Fin n → ℂ))
          (star (hB.isSelfAdjoint.isHermitian.eigenvectorBasis j : Fin n → ℂ)) =
        ∑ i : Fin n, c j i • E j i := by
    intro j
    simpa [c, E] using
      vecMulVec_left_eq_sum_eigenbasis (hA := hA.1)
        (Matrix.mulVec X (hB.isSelfAdjoint.isHermitian.eigenvectorBasis j : Fin n → ℂ))
        (star (hB.isSelfAdjoint.isHermitian.eigenvectorBasis j : Fin n → ℂ))
  calc
    X =
        ∑ j : Fin n,
          Matrix.vecMulVec
            (Matrix.mulVec X
              (hB.isSelfAdjoint.isHermitian.eigenvectorBasis j : Fin n → ℂ))
            (star (hB.isSelfAdjoint.isHermitian.eigenvectorBasis j : Fin n → ℂ)) :=
      matrix_eq_sum_eigenmatrix_right_posDef (B := B) hB X
    _ = ∑ j : Fin n, ∑ i : Fin n, c j i • E j i :=
      Finset.sum_congr rfl (fun j _ => hXj j)

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem eigenmatrix_trace_orthogonal
    {n : ℕ} {A B : Mₙ n} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    (i k j l : Fin n) :
    Matrix.trace
        (Matrix.conjTranspose
          (Matrix.vecMulVec
            ((hA.isSelfAdjoint.isHermitian.eigenvectorBasis i : Fin n → ℂ))
            (star ((hB.isSelfAdjoint.isHermitian.eigenvectorBasis j : Fin n → ℂ)))) *
          Matrix.vecMulVec
            ((hA.isSelfAdjoint.isHermitian.eigenvectorBasis k : Fin n → ℂ))
            (star ((hB.isSelfAdjoint.isHermitian.eigenvectorBasis l : Fin n → ℂ)))) =
      if i = k then if j = l then 1 else 0 else 0 := by
  rw [Matrix.conjTranspose_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.trace_vecMulVec]
  have hAorth :=
    orthonormal_iff_ite.mp hA.isSelfAdjoint.isHermitian.eigenvectorBasis.orthonormal i k
  have hBorth :=
    orthonormal_iff_ite.mp hB.isSelfAdjoint.isHermitian.eigenvectorBasis.orthonormal l j
  have hAorthDot :
      (star ((hA.isSelfAdjoint.isHermitian.eigenvectorBasis i : Fin n → ℂ)) ⬝ᵥ
        (hA.isSelfAdjoint.isHermitian.eigenvectorBasis k : Fin n → ℂ)) =
        if i = k then 1 else 0 := by
    simpa [inner, dotProduct, mul_comm] using hAorth
  have hBorthDot :
      ((hB.isSelfAdjoint.isHermitian.eigenvectorBasis j : Fin n → ℂ) ⬝ᵥ
        star ((hB.isSelfAdjoint.isHermitian.eigenvectorBasis l : Fin n → ℂ))) =
        if j = l then 1 else 0 := by
    simpa [inner, dotProduct, eq_comm] using hBorth
  rw [hAorthDot]
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l
    · subst l
      simpa using hBorthDot
    · simpa [hjl] using hBorthDot
  · simp [hik]

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem eigenmatrix_weighted_trace_orthogonal
    {n : ℕ} {r s : ℝ} {C D : Mₙ n} (hC : Matrix.PosDef C) (hD : Matrix.PosDef D)
    (i k j l : Fin n) :
    Matrix.trace
        (Matrix.conjTranspose (powerTraceEigenmatrix hC hD j i) *
          (matrixPower r C * powerTraceEigenmatrix hC hD l k * matrixPower s D)) =
      if i = k then
        if j = l then
          (powerFn r (hC.isSelfAdjoint.isHermitian.eigenvalues i) *
            powerFn s (hD.isSelfAdjoint.isHermitian.eigenvalues j) : ℂ)
        else 0
      else 0 := by
  let lam : ℂ := powerFn r (hC.isSelfAdjoint.isHermitian.eigenvalues k)
  let mu : ℂ := powerFn s (hD.isSelfAdjoint.isHermitian.eigenvalues l)
  have hact :
      matrixPower r C * powerTraceEigenmatrix hC hD l k * matrixPower s D =
        lam • (mu • powerTraceEigenmatrix hC hD l k) := by
    simpa [powerTraceEigenmatrix] using
      matrixPower_apply_eigenmatrix (r := r) (s := s) hC hD k l
  rw [hact]
  have hsmul :
      Matrix.trace
          (Matrix.conjTranspose (powerTraceEigenmatrix hC hD j i) *
            (lam • (mu • powerTraceEigenmatrix hC hD l k))) =
        lam * mu *
          Matrix.trace
            (Matrix.conjTranspose (powerTraceEigenmatrix hC hD j i) *
              powerTraceEigenmatrix hC hD l k) := by
    rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul]
    simp [smul_eq_mul, mul_assoc]
  rw [hsmul]
  have horth :
      Matrix.trace
          (Matrix.conjTranspose (powerTraceEigenmatrix hC hD j i) *
            powerTraceEigenmatrix hC hD l k) =
        if i = k then if j = l then 1 else 0 else 0 := by
    simpa [powerTraceEigenmatrix] using
      eigenmatrix_trace_orthogonal hC hD i k j l
  rw [horth]
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l
    · subst l
      simp [lam, mu]
    · simp [hjl]
  · simp [hik]

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem eigenmatrix_weighted_trace_orthogonal_assoc
    {n : ℕ} {r s : ℝ} {C D : Mₙ n} (hC : Matrix.PosDef C) (hD : Matrix.PosDef D)
    (i k j l : Fin n) :
    Matrix.trace
        (Matrix.conjTranspose (powerTraceEigenmatrix hC hD j i) *
          matrixPower r C * powerTraceEigenmatrix hC hD l k * matrixPower s D) =
      if i = k then
        if j = l then
          (powerFn r (hC.isSelfAdjoint.isHermitian.eigenvalues i) *
            powerFn s (hD.isSelfAdjoint.isHermitian.eigenvalues j) : ℂ)
        else 0
      else 0 := by
  simpa [Matrix.mul_assoc] using
    eigenmatrix_weighted_trace_orthogonal (r := r) (s := s) hC hD i k j l

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem eigenmatrix_weighted_trace_orthogonal_nested
    {n : ℕ} {r s : ℝ} {C D : Mₙ n} (hC : Matrix.PosDef C) (hD : Matrix.PosDef D)
    (i k j l : Fin n) :
    Matrix.trace
        (Matrix.conjTranspose (powerTraceEigenmatrix hC hD j i) *
          (matrixPower r C * (powerTraceEigenmatrix hC hD l k * matrixPower s D))) =
      if i = k then
        if j = l then
          (powerFn r (hC.isSelfAdjoint.isHermitian.eigenvalues i) *
            powerFn s (hD.isSelfAdjoint.isHermitian.eigenvalues j) : ℂ)
        else 0
      else 0 := by
  simpa [Matrix.mul_assoc] using
    eigenmatrix_weighted_trace_orthogonal (r := r) (s := s) hC hD i k j l

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem powerTrace_complex_eigenbasis_sum_posDef
    {n : ℕ} {r s : ℝ} {C D X : Mₙ n}
    (hC : Matrix.PosDef C) (hD : Matrix.PosDef D) :
    Matrix.trace (Matrix.conjTranspose X * matrixPower r C * X * matrixPower s D) =
      ∑ j : Fin n, ∑ i : Fin n,
        star (powerTraceEigenCoeff hC hD X j i) *
          powerTraceEigenCoeff hC hD X j i *
          (powerFn r (hC.isSelfAdjoint.isHermitian.eigenvalues i) *
            powerFn s (hD.isSelfAdjoint.isHermitian.eigenvalues j) : ℂ) := by
  classical
  have hX :
      X =
        ∑ j : Fin n, ∑ i : Fin n,
          powerTraceEigenCoeff hC hD X j i •
            powerTraceEigenmatrix hC hD j i := by
    simpa [powerTraceEigenCoeff, powerTraceEigenmatrix] using
      matrix_eq_sum_eigenmatrix_posDef hC hD X
  conv_lhs =>
    rw [hX]
  simp only [conjTranspose_sum, conjTranspose_smul, RCLike.star_def, Finset.sum_mul,
    Algebra.smul_mul_assoc, Finset.mul_sum, Algebra.mul_smul_comm, mul_assoc, trace_sum,
    trace_smul, eigenmatrix_weighted_trace_orthogonal_nested, smul_eq_mul, mul_comm,
    ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Local API: auxiliary algebraic fact; used in Hiai, proof of Theorem 6.4. -/
private lemma re_star_mul_self_mul_real (z : ℂ) (a : ℝ) :
    Complex.re (star z * z * (a : ℂ)) = Complex.normSq z * a := by
  rw [Complex.star_def]
  rw [← Complex.normSq_eq_conj_mul_self]
  simp

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem powerTrace_eigenbasis_sum_posDef
    {n : ℕ} {r s : ℝ} {C D X : Mₙ n}
    (hC : Matrix.PosDef C) (hD : Matrix.PosDef D) :
    powerTrace r s C D X =
      ∑ j : Fin n, ∑ i : Fin n,
        Complex.normSq (powerTraceEigenCoeff hC hD X j i) *
          powerFn r (hC.isSelfAdjoint.isHermitian.eigenvalues i) *
          powerFn s (hD.isSelfAdjoint.isHermitian.eigenvalues j) := by
  rw [powerTrace, powerTrace_complex_eigenbasis_sum_posDef hC hD]
  simp_rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simpa [Complex.ofReal_mul, mul_assoc] using
    re_star_mul_self_mul_real
      (powerTraceEigenCoeff hC hD X j i)
      (powerFn r (hC.isSelfAdjoint.isHermitian.eigenvalues i) *
        powerFn s (hD.isSelfAdjoint.isHermitian.eigenvalues j))

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem scalar_kernel_pos {x y u v : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hu : 0 < u) (hv : 0 < v) :
    (((x + y) / 2) * ((u + v) / 2))⁻¹ ≤
      (x⁻¹ * u⁻¹ + y⁻¹ * v⁻¹) / 2 := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hv0 : v ≠ 0 := ne_of_gt hv
  have hxy : x + y ≠ 0 := by positivity
  have huv : u + v ≠ 0 := by positivity
  have hpoly :
      x * y * 2 ^ 3 * u * v ≤ (x + y) * (u + v) * (y * v + x * u) := by
    have h1 : 0 ≤ (x * u - y * v) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ u * v * (x - y) ^ 2 :=
      mul_nonneg (le_of_lt (mul_pos hu hv)) (sq_nonneg _)
    have h3 : 0 ≤ x * y * (u - v) ^ 2 :=
      mul_nonneg (le_of_lt (mul_pos hx hy)) (sq_nonneg _)
    nlinarith
  field_simp [hx0, hy0, hu0, hv0, hxy, huv]
  nlinarith [hpoly]

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem scalar_kernel_rpow {a b α₁ α₂ β₁ β₂ : ℝ}
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) :
    (((α₁ ^ a + α₂ ^ a) / 2) * ((β₁ ^ b + β₂ ^ b) / 2))⁻¹ ≤
      (α₁ ^ (-a) * β₁ ^ (-b) + α₂ ^ (-a) * β₂ ^ (-b)) / 2 := by
  have h :=
    scalar_kernel_pos
      (Real.rpow_pos_of_pos hα₁ a) (Real.rpow_pos_of_pos hα₂ a)
      (Real.rpow_pos_of_pos hβ₁ b) (Real.rpow_pos_of_pos hβ₂ b)
  simpa [Real.rpow_neg hα₁.le a, Real.rpow_neg hα₂.le a,
    Real.rpow_neg hβ₁.le b, Real.rpow_neg hβ₂.le b] using h

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem scalar_kernel_normalized {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) :
    (((c + 1) / 2) * ((1 + d) / 2))⁻¹ ≤ (c⁻¹ + d⁻¹) / 2 := by
  have h :=
    scalar_kernel_rpow
      (a := (1 : ℝ)) (b := (1 : ℝ))
      (α₁ := c) (α₂ := 1) (β₁ := 1) (β₂ := d)
      hc (by norm_num) (by norm_num) hd
  simpa [Real.rpow_neg hc.le 1, Real.rpow_neg hd.le 1, Real.rpow_one] using h

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem normalized_matrixPower_posDef {n : ℕ} {a : ℝ}
    {A₁ A₂ : Mₙ n} (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂) :
    Matrix.PosDef
      (matrixPower (-(a / 2)) A₂ * matrixPower a A₁ * matrixPower (-(a / 2)) A₂) := by
  have hmid : (matrixPower a A₁).PosDef :=
    matrixPower_posDef_of_posDef (r := a) hA₁
  have hU_pd : Matrix.PosDef (matrixPower (-(a / 2)) A₂) :=
    matrixPower_posDef_of_posDef (r := -(a / 2)) hA₂
  have hU_unit : IsUnit (matrixPower (-(a / 2)) A₂) :=
    hU_pd.isUnit
  have hU_star :
      star (matrixPower (-(a / 2)) A₂) = matrixPower (-(a / 2)) A₂ :=
    by simpa using hU_pd.isHermitian
  have hpos :
      (star (matrixPower (-(a / 2)) A₂) * matrixPower a A₁ *
          matrixPower (-(a / 2)) A₂).PosDef :=
    (Matrix.IsUnit.posDef_star_left_conjugate_iff hU_unit).2 hmid
  exact (by simpa [hU_star, Matrix.mul_assoc] using hpos)

/-- Local API: auxiliary algebraic fact; used in Hiai, proof of Theorem 6.4. -/
private theorem leftMul_half_add_one_eq {n : ℕ} (C : Mₙ n) :
    ((2 : ℂ)⁻¹) • (leftMul C + 1) =
      leftMul (((2 : ℂ)⁻¹) • (C + 1)) := by
  ext X i j
  simp [leftMul_apply, add_mul]
  ring

/-- Local API: auxiliary algebraic fact; used in Hiai, proof of Theorem 6.4. -/
private theorem rightMul_half_add_one_eq {n : ℕ} (D : Mₙ n) :
    ((2 : ℂ)⁻¹) • (1 + rightMul D) =
      rightMul (((2 : ℂ)⁻¹) • (1 + D)) := by
  ext X i j
  simp [rightMul_apply, Matrix.mul_add]
  ring

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem matrixPosDef_half_add_one {n : ℕ} {C : Mₙ n}
    (hC : Matrix.PosDef C) :
    Matrix.PosDef (((2 : ℂ)⁻¹) • (C + 1)) := by
  have hone : Matrix.PosDef (1 : Mₙ n) :=
    Matrix.PosDef.one (R := ℂ) (n := Fin n)
  have hconv :=
    matrixPosDef_convex_combo (A1 := C) (A2 := (1 : Mₙ n)) (t := (1 / 2 : ℝ))
      (by norm_num) hC hone
  convert hconv using 1
  ext i j
  simp
  ring

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem matrixCfcR_mulVec_of_mulVec_eq
    {n : ℕ} (f : ℝ → ℝ) {A : Mₙ n} (hA : IsSelfAdjoint A)
    {lam : ℝ} {x : Fin n → ℂ} (hx : A.mulVec x = (lam : ℂ) • x) :
    (HansenPedersen.matrixCfcR f A).mulVec x = (f lam : ℂ) • x := by
  have hxEig :
      (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n)) ∈
        Module.End.eigenspace
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A).toLinearMap (lam : ℂ) := by
    rw [Module.End.mem_eigenspace_iff]
    ext k
    simpa using congrArg (fun v : Fin n → ℂ => v k) hx
  have hcalc :=
    @HiaiPetz.cfcR_apply_of_mem_eigenspace_real_transport (EuclideanSpace ℂ (Fin n))
      inferInstance inferInstance inferInstance inferInstance inferInstance
      f ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A)
      (hA.map (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))) lam (WithLp.toLp 2 x) hxEig
  ext k
  calc
    ((HansenPedersen.matrixCfcR f A).mulVec x) k =
        (HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A) (WithLp.toLp 2 x)) k := by
          simpa using congrArg (fun v : EuclideanSpace ℂ (Fin n) => v k)
            (HiaiPetz.matrixCfcR_mulVec_toLp_eq_euclidCfc_apply_transport (f := f) A x)
    _ = ((f lam : ℂ) • x) k := by
          simpa using congrArg (fun v : EuclideanSpace ℂ (Fin n) => v k) hcalc

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem matrixPower_halfAddOne_mulVec_eigenvectorBasis
    {n : ℕ} (r : ℝ) {C : Mₙ n} (hC : Matrix.PosDef C) (i : Fin n) :
    (matrixPower r (((2 : ℂ)⁻¹) • (C + 1))).mulVec
        (hC.isSelfAdjoint.isHermitian.eigenvectorBasis i : Fin n → ℂ) =
      (powerFn r ((hC.isSelfAdjoint.isHermitian.eigenvalues i + 1) / 2) : ℂ) •
        (hC.isSelfAdjoint.isHermitian.eigenvectorBasis i : Fin n → ℂ) := by
  let u : Fin n → ℂ := hC.isSelfAdjoint.isHermitian.eigenvectorBasis i
  let μ : ℝ := (hC.isSelfAdjoint.isHermitian.eigenvalues i + 1) / 2
  have hCavg : Matrix.PosDef (((2 : ℂ)⁻¹) • (C + 1)) :=
    matrixPosDef_half_add_one hC
  have heig : ((((2 : ℂ)⁻¹) • (C + 1)).mulVec u) = (μ : ℂ) • u := by
    ext k
    have hCu :=
      congrArg (fun v : Fin n → ℂ => v k) (hC.isSelfAdjoint.isHermitian.mulVec_eigenvectorBasis i)
    simp [u, μ, Matrix.add_mulVec, Matrix.smul_mulVec, hCu]
    ring
  simpa [matrixPower, u, μ] using
    matrixCfcR_mulVec_of_mulVec_eq (f := powerFn r) hCavg.1 heig

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem eigenrow_matrixPower_halfAddOne
    {n : ℕ} (r : ℝ) {D : Mₙ n} (hD : Matrix.PosDef D) (j : Fin n) :
    star ((hD.isSelfAdjoint.isHermitian.eigenvectorBasis j : Fin n → ℂ)) ᵥ*
        matrixPower r (((2 : ℂ)⁻¹) • (1 + D)) =
      (powerFn r ((1 + hD.isSelfAdjoint.isHermitian.eigenvalues j) / 2) : ℂ) •
        star ((hD.isSelfAdjoint.isHermitian.eigenvectorBasis j : Fin n → ℂ)) := by
  have havg :
      (((2 : ℂ)⁻¹) • (1 + D)) = (((2 : ℂ)⁻¹) • (D + 1)) := by
    rw [add_comm]
  rw [havg]
  have hmul := matrixPower_halfAddOne_mulVec_eigenvectorBasis (r := r) hD j
  have hstar := congrArg star hmul
  rw [Matrix.star_mulVec] at hstar
  have hself :
      Matrix.conjTranspose (matrixPower r (((2 : ℂ)⁻¹) • (D + 1))) =
        matrixPower r (((2 : ℂ)⁻¹) • (D + 1)) := by
    simpa [matrixPower, Matrix.IsHermitian, IsSelfAdjoint] using
      matrixCfcR_isSelfAdjoint (f := powerFn r) (matrixPosDef_half_add_one hD).1
  rw [hself] at hstar
  simpa [add_comm] using hstar

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem matrixPower_halfAddOne_apply_eigenmatrix
    {n : ℕ} (r s : ℝ) {C D : Mₙ n} (hC : Matrix.PosDef C) (hD : Matrix.PosDef D)
    (i j : Fin n) :
    matrixPower r (((2 : ℂ)⁻¹) • (C + 1)) *
        powerTraceEigenmatrix hC hD j i *
        matrixPower s (((2 : ℂ)⁻¹) • (1 + D)) =
      (powerFn r ((hC.isSelfAdjoint.isHermitian.eigenvalues i + 1) / 2) : ℂ) •
        ((powerFn s ((1 + hD.isSelfAdjoint.isHermitian.eigenvalues j) / 2) : ℂ) •
          powerTraceEigenmatrix hC hD j i) := by
  calc
    matrixPower r (((2 : ℂ)⁻¹) • (C + 1)) *
          powerTraceEigenmatrix hC hD j i *
          matrixPower s (((2 : ℂ)⁻¹) • (1 + D)) =
        ((powerFn r ((hC.isSelfAdjoint.isHermitian.eigenvalues i + 1) / 2) : ℂ) •
          powerTraceEigenmatrix hC hD j i) *
          matrixPower s (((2 : ℂ)⁻¹) • (1 + D)) := by
            rw [powerTraceEigenmatrix, Matrix.mul_vecMulVec,
              matrixPower_halfAddOne_mulVec_eigenvectorBasis (r := r) hC i,
              Matrix.smul_vecMulVec]
    _ =
        (powerFn r ((hC.isSelfAdjoint.isHermitian.eigenvalues i + 1) / 2) : ℂ) •
          (powerTraceEigenmatrix hC hD j i *
            matrixPower s (((2 : ℂ)⁻¹) • (1 + D))) := by
            rw [smul_mul_assoc]
    _ =
        (powerFn r ((hC.isSelfAdjoint.isHermitian.eigenvalues i + 1) / 2) : ℂ) •
          ((powerFn s ((1 + hD.isSelfAdjoint.isHermitian.eigenvalues j) / 2) : ℂ) •
            powerTraceEigenmatrix hC hD j i) := by
            rw [powerTraceEigenmatrix, Matrix.vecMulVec_mul,
              eigenrow_matrixPower_halfAddOne (r := s) hD j]
            rw [Matrix.vecMulVec_smul]

/-- Local API: auxiliary algebraic fact; used in Hiai, proof of Theorem 6.4. -/
private theorem trace_mul_two_smul {n : ℕ} (A B : Mₙ n) (a b : ℂ) :
    Matrix.trace (A * (a • (b • B))) = a * b * Matrix.trace (A * B) := by
  simp [mul_assoc]

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem eigenmatrix_halfAddOne_weighted_trace_orthogonal_nested
    {n : ℕ} {r s : ℝ} {C D : Mₙ n} (hC : Matrix.PosDef C) (hD : Matrix.PosDef D)
    (i k j l : Fin n) :
    Matrix.trace
        (Matrix.conjTranspose (powerTraceEigenmatrix hC hD j i) *
          (matrixPower r (((2 : ℂ)⁻¹) • (C + 1)) *
            (powerTraceEigenmatrix hC hD l k *
              matrixPower s (((2 : ℂ)⁻¹) • (1 + D))))) =
      if i = k then
        if j = l then
          (powerFn r ((hC.isSelfAdjoint.isHermitian.eigenvalues i + 1) / 2) *
            powerFn s ((1 + hD.isSelfAdjoint.isHermitian.eigenvalues j) / 2) : ℂ)
        else 0
      else 0 := by
  let Eji := powerTraceEigenmatrix hC hD j i
  let Elk := powerTraceEigenmatrix hC hD l k
  let ar : ℂ := powerFn r ((hC.isSelfAdjoint.isHermitian.eigenvalues k + 1) / 2)
  let bs : ℂ := powerFn s ((1 + hD.isSelfAdjoint.isHermitian.eigenvalues l) / 2)
  rw [← Matrix.mul_assoc (matrixPower r (((2 : ℂ)⁻¹) • (C + 1)))]
  rw [matrixPower_halfAddOne_apply_eigenmatrix (r := r) (s := s) hC hD k l]
  change Matrix.trace (Matrix.conjTranspose Eji * (ar • (bs • Elk))) =
    if i = k then
      if j = l then
        (powerFn r ((hC.isSelfAdjoint.isHermitian.eigenvalues i + 1) / 2) *
          powerFn s ((1 + hD.isSelfAdjoint.isHermitian.eigenvalues j) / 2) : ℂ)
      else 0
    else 0
  rw [trace_mul_two_smul]
  have horth :
      Matrix.trace (Matrix.conjTranspose Eji * Elk) =
        if i = k then if j = l then (1 : ℂ) else 0 else 0 := by
    simpa [Eji, Elk, powerTraceEigenmatrix] using
      eigenmatrix_trace_orthogonal hC hD i k j l
  rw [horth]
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l
    · subst l
      simp [ar, bs, mul_comm]
    · simp [ar, bs, hjl]
  · simp [ar, bs, hik]

/-- Bilinear expansion of the weighted trace form on **atom** variables: the
fourfold finite-sum expansion (conjugate-transpose push-through, distribution
of the two sums, trace linearity, scalar extraction) runs here once, on opaque
atoms `c`, `E`, `P`, `Q`.  Keeping `matrixPower`/eigenvector terms out of the
expansion prevents `simp` from re-unfolding them at every congruence pass.

Source: Hiai, proof of Theorem 6.4. -/
private theorem trace_conjTranspose_sum_mul_mul_sum_mul
    {n : ℕ} (c : Fin n → Fin n → ℂ) (E : Fin n → Fin n → Mₙ n) (P Q : Mₙ n) :
    Matrix.trace
        (Matrix.conjTranspose (∑ j : Fin n, ∑ i : Fin n, c j i • E j i) * P *
          (∑ j : Fin n, ∑ i : Fin n, c j i • E j i) * Q) =
      ∑ l : Fin n, ∑ k : Fin n, ∑ j : Fin n, ∑ i : Fin n,
        c l k * (star (c j i) *
          Matrix.trace (Matrix.conjTranspose (E j i) * (P * (E l k * Q)))) := by
  classical
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Finset.sum_mul,
    Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, Matrix.mul_assoc]

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem powerTrace_halfAddOne_complex_eigenbasis_sum_posDef
    {n : ℕ} {r s : ℝ} {C D X : Mₙ n}
    (hC : Matrix.PosDef C) (hD : Matrix.PosDef D) :
    Matrix.trace
        (Matrix.conjTranspose X * matrixPower r (((2 : ℂ)⁻¹) • (C + 1)) * X *
          matrixPower s (((2 : ℂ)⁻¹) • (1 + D))) =
      ∑ j : Fin n, ∑ i : Fin n,
        star (powerTraceEigenCoeff hC hD X j i) *
          powerTraceEigenCoeff hC hD X j i *
          (powerFn r ((hC.isSelfAdjoint.isHermitian.eigenvalues i + 1) / 2) *
            powerFn s ((1 + hD.isSelfAdjoint.isHermitian.eigenvalues j) / 2) : ℂ) := by
  classical
  have hX :
      X =
        ∑ j : Fin n, ∑ i : Fin n,
          powerTraceEigenCoeff hC hD X j i •
            powerTraceEigenmatrix hC hD j i := by
    simpa [powerTraceEigenCoeff, powerTraceEigenmatrix] using
      matrix_eq_sum_eigenmatrix_posDef hC hD X
  conv_lhs =>
    rw [hX]
  rw [trace_conjTranspose_sum_mul_mul_sum_mul]
  simp only [eigenmatrix_halfAddOne_weighted_trace_orthogonal_nested hC hD,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem powerTrace_halfAddOne_eigenbasis_sum_posDef
    {n : ℕ} {r s : ℝ} {C D X : Mₙ n}
    (hC : Matrix.PosDef C) (hD : Matrix.PosDef D) :
    powerTrace r s (((2 : ℂ)⁻¹) • (C + 1)) (((2 : ℂ)⁻¹) • (1 + D)) X =
      ∑ j : Fin n, ∑ i : Fin n,
        Complex.normSq (powerTraceEigenCoeff hC hD X j i) *
          powerFn r ((hC.isSelfAdjoint.isHermitian.eigenvalues i + 1) / 2) *
          powerFn s ((1 + hD.isSelfAdjoint.isHermitian.eigenvalues j) / 2) := by
  rw [powerTrace, powerTrace_halfAddOne_complex_eigenbasis_sum_posDef hC hD]
  simp_rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simpa [Complex.ofReal_mul, mul_assoc] using
    re_star_mul_self_mul_real
      (powerTraceEigenCoeff hC hD X j i)
      (powerFn r ((hC.isSelfAdjoint.isHermitian.eigenvalues i + 1) / 2) *
        powerFn s ((1 + hD.isSelfAdjoint.isHermitian.eigenvalues j) / 2))

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem scalar_kernel_normalized_powerFn {c d : ℝ}
    (hc : 0 < c) (hd : 0 < d) :
    powerFn (-1) ((c + 1) / 2) * powerFn (-1) ((1 + d) / 2) ≤
      (powerFn (-1) c * powerFn 0 d + powerFn 0 c * powerFn (-1) d) / 2 := by
  have h := scalar_kernel_normalized hc hd
  have hcavg : 0 ≤ (c + 1) / 2 := by positivity
  have hdavg : 0 ≤ (1 + d) / 2 := by positivity
  simpa [powerFn, Real.rpow_neg hcavg 1, Real.rpow_neg hdavg 1,
    Real.rpow_neg hc.le 1, Real.rpow_neg hd.le 1, Real.rpow_one, Real.rpow_zero,
    mul_comm]
    using h

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem double_sum_mul_add_div_two {n : ℕ}
    (w a b : Fin n → Fin n → ℝ) :
    (∑ j : Fin n, ∑ i : Fin n, w j i * ((a j i + b j i) / 2)) =
      ((∑ j : Fin n, ∑ i : Fin n, w j i * a j i) +
        ∑ j : Fin n, ∑ i : Fin n, w j i * b j i) / 2 := by
  calc
    (∑ j : Fin n, ∑ i : Fin n, w j i * ((a j i + b j i) / 2)) =
        ∑ j : Fin n, ∑ i : Fin n, ((w j i * a j i) / 2 + (w j i * b j i) / 2) := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = (∑ j : Fin n, ∑ i : Fin n, (w j i * a j i) / 2) +
        ∑ j : Fin n, ∑ i : Fin n, (w j i * b j i) / 2 := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          rw [← Finset.sum_add_distrib]
    _ = (∑ j : Fin n, ∑ i : Fin n, w j i * a j i) / 2 +
        (∑ j : Fin n, ∑ i : Fin n, w j i * b j i) / 2 := by
          simp [Finset.sum_div]
    _ = ((∑ j : Fin n, ∑ i : Fin n, w j i * a j i) +
        ∑ j : Fin n, ∑ i : Fin n, w j i * b j i) / 2 := by
          ring

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem normalized_endpoint_average_qform {n : ℕ}
    {C D X : Mₙ n} (hC : Matrix.PosDef C) (hD : Matrix.PosDef D) :
    powerTrace (-1) (-1) (((2 : ℂ)⁻¹) • (C + 1)) (((2 : ℂ)⁻¹) • (1 + D)) X ≤
      (powerTrace (-1) 0 C D X + powerTrace 0 (-1) C D X) / 2 := by
  classical
  have hCpos : C.PosDef := hC
  have hDpos : D.PosDef := hD
  rw [powerTrace_halfAddOne_eigenbasis_sum_posDef hC hD]
  rw [powerTrace_eigenbasis_sum_posDef (r := -1) (s := 0) hC hD]
  rw [powerTrace_eigenbasis_sum_posDef (r := 0) (s := -1) hC hD]
  calc
    (∑ j : Fin n, ∑ i : Fin n,
        Complex.normSq (powerTraceEigenCoeff hC hD X j i) *
          powerFn (-1) ((hC.isSelfAdjoint.isHermitian.eigenvalues i + 1) / 2) *
          powerFn (-1) ((1 + hD.isSelfAdjoint.isHermitian.eigenvalues j) / 2)) ≤
      ∑ j : Fin n, ∑ i : Fin n,
        Complex.normSq (powerTraceEigenCoeff hC hD X j i) *
          ((powerFn (-1) (hC.isSelfAdjoint.isHermitian.eigenvalues i) *
              powerFn 0 (hD.isSelfAdjoint.isHermitian.eigenvalues j) +
            powerFn 0 (hC.isSelfAdjoint.isHermitian.eigenvalues i) *
              powerFn (-1) (hD.isSelfAdjoint.isHermitian.eigenvalues j)) / 2) := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro i _
        have hγ : 0 < hC.isSelfAdjoint.isHermitian.eigenvalues i :=
          hC.isSelfAdjoint.isHermitian.posDef_iff_eigenvalues_pos.mp hCpos i
        have hδ : 0 < hD.isSelfAdjoint.isHermitian.eigenvalues j :=
          hD.isSelfAdjoint.isHermitian.posDef_iff_eigenvalues_pos.mp hDpos j
        have hscalar :=
          scalar_kernel_normalized_powerFn hγ hδ
        have hw :
            0 ≤ Complex.normSq (powerTraceEigenCoeff hC hD X j i) :=
          Complex.normSq_nonneg _
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hscalar hw
    _ =
      ((∑ j : Fin n, ∑ i : Fin n,
          Complex.normSq (powerTraceEigenCoeff hC hD X j i) *
            powerFn (-1) (hC.isSelfAdjoint.isHermitian.eigenvalues i) *
            powerFn 0 (hD.isSelfAdjoint.isHermitian.eigenvalues j)) +
        ∑ j : Fin n, ∑ i : Fin n,
          Complex.normSq (powerTraceEigenCoeff hC hD X j i) *
            powerFn 0 (hC.isSelfAdjoint.isHermitian.eigenvalues i) *
            powerFn (-1) (hD.isSelfAdjoint.isHermitian.eigenvalues j)) / 2 := by
        simpa [mul_assoc] using
          double_sum_mul_add_div_two
            (fun j i => Complex.normSq (powerTraceEigenCoeff hC hD X j i))
            (fun j i =>
              powerFn (-1) (hC.isSelfAdjoint.isHermitian.eigenvalues i) *
                powerFn 0 (hD.isSelfAdjoint.isHermitian.eigenvalues j))
            (fun j i =>
              powerFn 0 (hC.isSelfAdjoint.isHermitian.eigenvalues i) *
                powerFn (-1) (hD.isSelfAdjoint.isHermitian.eigenvalues j))

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem matrixPower_mul_neg_eq_one_posDef {n : ℕ} {r : ℝ} {A : Mₙ n}
    (hA : Matrix.PosDef A) :
    matrixPower r A * matrixPower (-r) A = 1 := by
  rw [matrixPower_mul_matrixPower_posDef hA]
  have hr : r + -r = 0 := by ring
  rw [hr, matrixPower_zero_posDef hA]

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem matrixPower_neg_mul_eq_one_posDef {n : ℕ} {r : ℝ} {A : Mₙ n}
    (hA : Matrix.PosDef A) :
    matrixPower (-r) A * matrixPower r A = 1 := by
  rw [matrixPower_mul_matrixPower_posDef hA]
  have hr : -r + r = 0 := by ring
  rw [hr, matrixPower_zero_posDef hA]

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem matrixPower_neg_one_normalized_matrixPower {n : ℕ} {a : ℝ}
    {A₁ A₂ : Mₙ n} (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂) :
    matrixPower (-1)
        (matrixPower (-(a / 2)) A₂ * matrixPower a A₁ *
          matrixPower (-(a / 2)) A₂) =
      matrixPower (a / 2) A₂ * matrixPower (-a) A₁ * matrixPower (a / 2) A₂ := by
  let U : Mₙ n := matrixPower (-(a / 2)) A₂
  let Uinv : Mₙ n := matrixPower (a / 2) A₂
  let H : Mₙ n := matrixPower a A₁
  let Hinv : Mₙ n := matrixPower (-a) A₁
  let C : Mₙ n := U * H * U
  let R : Mₙ n := Uinv * Hinv * Uinv
  have hCpos : Matrix.PosDef C := by
    simpa [C, U, H] using normalized_matrixPower_posDef (a := a) hA₁ hA₂
  have hUUinv : U * Uinv = 1 := by
    simpa [U, Uinv, neg_neg] using
      matrixPower_mul_neg_eq_one_posDef (r := -(a / 2)) hA₂
  have hHinv : H * Hinv = 1 := by
    simpa [H, Hinv] using matrixPower_mul_neg_eq_one_posDef (r := a) hA₁
  have hCR : C * R = 1 := by
    dsimp [C, R]
    simp only [Matrix.mul_assoc]
    change U * (H * (U * (Uinv * (Hinv * Uinv)))) = 1
    calc
      U * (H * (U * (Uinv * (Hinv * Uinv)))) =
          U * (H * ((U * Uinv) * (Hinv * Uinv))) := by
            rw [← Matrix.mul_assoc U Uinv (Hinv * Uinv)]
      _ = U * (H * (1 * (Hinv * Uinv))) := by rw [hUUinv]
      _ = U * (H * (Hinv * Uinv)) := by rw [Matrix.one_mul]
      _ = U * ((H * Hinv) * Uinv) := by rw [← Matrix.mul_assoc H Hinv Uinv]
      _ = U * (1 * Uinv) := by rw [hHinv]
      _ = U * Uinv := by rw [Matrix.one_mul]
      _ = 1 := hUUinv
  have hPowC : matrixPower (-1) C * C = 1 := by
    nth_rw 2 [← matrixPower_one_posDef hCpos]
    exact matrixPower_neg_mul_eq_one_posDef (r := 1) hCpos
  calc
    matrixPower (-1) C = matrixPower (-1) C * 1 := by rw [Matrix.mul_one]
    _ = matrixPower (-1) C * (C * R) := by rw [hCR]
    _ = (matrixPower (-1) C * C) * R := by
      dsimp [C, R]
      simp only [Matrix.mul_assoc]
    _ = 1 * R := by rw [hPowC]
    _ = R := by rw [Matrix.one_mul]

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem matrixPower_neg_one_conj_posDef {n : ℕ} {r : ℝ}
    {A H : Mₙ n} (hA : Matrix.PosDef A) (hH : Matrix.PosDef H) :
    matrixPower (-1) (matrixPower (-r) A * H * matrixPower (-r) A) =
      matrixPower r A * matrixPower (-1) H * matrixPower r A := by
  let U : Mₙ n := matrixPower (-r) A
  let Uinv : Mₙ n := matrixPower r A
  let Hinv : Mₙ n := matrixPower (-1) H
  let C : Mₙ n := U * H * U
  let R : Mₙ n := Uinv * Hinv * Uinv
  have hCpos : Matrix.PosDef C := by
    have hmid : H.PosDef := hH
    have hU_pd : Matrix.PosDef U := by
      simpa [U] using matrixPower_posDef_of_posDef (r := -r) hA
    have hU_unit : IsUnit U := hU_pd.isUnit
    have hU_star : star U = U := by simpa using hU_pd.isHermitian
    have hpos : (star U * H * U).PosDef :=
      (Matrix.IsUnit.posDef_star_left_conjugate_iff hU_unit).2 hmid
    exact (by simpa [C, hU_star, Matrix.mul_assoc] using hpos)
  have hUUinv : U * Uinv = 1 := by
    simpa [U, Uinv] using matrixPower_mul_neg_eq_one_posDef (r := -r) hA
  have hUinvU : Uinv * U = 1 := by
    simpa [U, Uinv] using matrixPower_neg_mul_eq_one_posDef (r := -r) hA
  have hHinv : H * Hinv = 1 := by
    calc
      H * Hinv = matrixPower 1 H * matrixPower (-1) H := by
        rw [matrixPower_one_posDef hH]
      _ = 1 := matrixPower_mul_neg_eq_one_posDef (r := 1) hH
  have hCR : C * R = 1 := by
    dsimp [C, R]
    simp only [Matrix.mul_assoc]
    change U * (H * (U * (Uinv * (Hinv * Uinv)))) = 1
    calc
      U * (H * (U * (Uinv * (Hinv * Uinv)))) =
          U * (H * ((U * Uinv) * (Hinv * Uinv))) := by
            rw [← Matrix.mul_assoc U Uinv (Hinv * Uinv)]
      _ = U * (H * (1 * (Hinv * Uinv))) := by rw [hUUinv]
      _ = U * (H * (Hinv * Uinv)) := by rw [Matrix.one_mul]
      _ = U * ((H * Hinv) * Uinv) := by rw [← Matrix.mul_assoc H Hinv Uinv]
      _ = U * (1 * Uinv) := by rw [hHinv]
      _ = U * Uinv := by rw [Matrix.one_mul]
      _ = 1 := hUUinv
  have hPowC : matrixPower (-1) C * C = 1 := by
    nth_rw 2 [← matrixPower_one_posDef hCpos]
    exact matrixPower_neg_mul_eq_one_posDef (r := 1) hCpos
  calc
    matrixPower (-1) C = matrixPower (-1) C * 1 := by rw [Matrix.mul_one]
    _ = matrixPower (-1) C * (C * R) := by rw [hCR]
    _ = (matrixPower (-1) C * C) * R := by
      dsimp [C, R]
      simp only [Matrix.mul_assoc]
    _ = 1 * R := by rw [hPowC]
    _ = R := by rw [Matrix.one_mul]

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem powerTrace_neg_one_conj_posDef {n : ℕ} {r s : ℝ}
    {A B H K X : Mₙ n} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    (hH : Matrix.PosDef H) (hK : Matrix.PosDef K) :
    let U : Mₙ n := matrixPower (-r) A
    let V : Mₙ n := matrixPower (-s) B
    powerTrace (-1) (-1) (U * H * U) (V * K * V) (U * X * V) =
      powerTrace (-1) (-1) H K X := by
  dsimp only
  let U : Mₙ n := matrixPower (-r) A
  let Uinv : Mₙ n := matrixPower r A
  let V : Mₙ n := matrixPower (-s) B
  let Vinv : Mₙ n := matrixPower s B
  let Hinv : Mₙ n := matrixPower (-1) H
  let Kinv : Mₙ n := matrixPower (-1) K
  have hCinv :
      matrixPower (-1) (U * H * U) = Uinv * Hinv * Uinv := by
    simpa [U, Uinv, Hinv] using
      matrixPower_neg_one_conj_posDef (r := r) hA hH
  have hDinv :
      matrixPower (-1) (V * K * V) = Vinv * Kinv * Vinv := by
    simpa [V, Vinv, Kinv] using
      matrixPower_neg_one_conj_posDef (r := s) hB hK
  have hCinv_assoc :
      matrixPower (-1) (U * (H * U)) = Uinv * Hinv * Uinv := by
    simpa [Matrix.mul_assoc] using hCinv
  have hDinv_assoc :
      matrixPower (-1) (V * (K * V)) = Vinv * Kinv * Vinv := by
    simpa [Matrix.mul_assoc] using hDinv
  have hUstar : Matrix.conjTranspose U = U := by
    simpa [U] using (matrixPower_posDef_of_posDef (r := -r) hA).1
  have hVstar : Matrix.conjTranspose V = V := by
    simpa [V] using (matrixPower_posDef_of_posDef (r := -s) hB).1
  have hUUinv : U * Uinv = 1 := by
    simpa [U, Uinv] using matrixPower_mul_neg_eq_one_posDef (r := -r) hA
  have hUinvU : Uinv * U = 1 := by
    simpa [U, Uinv] using matrixPower_neg_mul_eq_one_posDef (r := -r) hA
  have hVVinv : V * Vinv = 1 := by
    simpa [V, Vinv] using matrixPower_mul_neg_eq_one_posDef (r := -s) hB
  have hVinvV : Vinv * V = 1 := by
    simpa [V, Vinv] using matrixPower_neg_mul_eq_one_posDef (r := -s) hB
  have hinner :
      U * (Uinv * (Hinv * (Uinv * (U * (X * V))))) = Hinv * (X * V) := by
    calc
      U * (Uinv * (Hinv * (Uinv * (U * (X * V))))) =
          (U * Uinv) * (Hinv * (Uinv * (U * (X * V)))) := by
            rw [Matrix.mul_assoc]
      _ = 1 * (Hinv * (Uinv * (U * (X * V)))) := by rw [hUUinv]
      _ = Hinv * (Uinv * (U * (X * V))) := by rw [Matrix.one_mul]
      _ = Hinv * ((Uinv * U) * (X * V)) := by
            rw [← Matrix.mul_assoc Uinv U (X * V)]
      _ = Hinv * (1 * (X * V)) := by rw [hUinvU]
      _ = Hinv * (X * V) := by rw [Matrix.one_mul]
  have htrace :
      Matrix.trace
          (Matrix.conjTranspose (U * X * V) * matrixPower (-1) (U * H * U) *
            (U * X * V) * matrixPower (-1) (V * K * V)) =
        Matrix.trace (Matrix.conjTranspose X * Hinv * X * Kinv) := by
    calc
      Matrix.trace
          (Matrix.conjTranspose (U * X * V) * matrixPower (-1) (U * H * U) *
            (U * X * V) * matrixPower (-1) (V * K * V)) =
          Matrix.trace
            (V * (Matrix.conjTranspose X *
              (U * (Uinv * (Hinv * (Uinv * (U * (X * V)))))) *
                (Vinv * (Kinv * Vinv)))) := by
            simp [hCinv_assoc, hDinv_assoc, hUstar, hVstar, Matrix.conjTranspose_mul,
              Matrix.mul_assoc]
      _ = Matrix.trace
            (V * (Matrix.conjTranspose X * (Hinv * (X * V)) *
                (Vinv * (Kinv * Vinv)))) := by
            rw [hinner]
      _ = Matrix.trace
            (V * ((Matrix.conjTranspose X * Hinv * X) *
                (V * (Vinv * (Kinv * Vinv))))) := by
            simp [Matrix.mul_assoc]
      _ = Matrix.trace
            (V * ((Matrix.conjTranspose X * Hinv * X) *
                ((V * Vinv) * (Kinv * Vinv)))) := by
            rw [← Matrix.mul_assoc V Vinv (Kinv * Vinv)]
      _ = Matrix.trace
            (V * ((Matrix.conjTranspose X * Hinv * X) *
                (1 * (Kinv * Vinv)))) := by rw [hVVinv]
      _ = Matrix.trace
            (V * ((Matrix.conjTranspose X * Hinv * X) * (Kinv * Vinv))) := by
            rw [Matrix.one_mul]
      _ = Matrix.trace
            (((Matrix.conjTranspose X * Hinv * X) * Kinv * Vinv) * V) := by
            rw [Matrix.trace_mul_comm]
            simp [Matrix.mul_assoc]
      _ = Matrix.trace
            ((Matrix.conjTranspose X * Hinv * X) * Kinv * (Vinv * V)) := by
            simp [Matrix.mul_assoc]
      _ = Matrix.trace
            ((Matrix.conjTranspose X * Hinv * X) * Kinv * 1) := by rw [hVinvV]
      _ = Matrix.trace (Matrix.conjTranspose X * Hinv * X * Kinv) := by
            rw [Matrix.mul_one]
  simpa [powerTrace, Hinv, Kinv] using congrArg Complex.re htrace

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem average_eq_normalized_qform {n : ℕ}
    {a b : ℝ} {A₁ A₂ B₁ B₂ X : Mₙ n}
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    let Aavg : Mₙ n := ((2 : ℂ)⁻¹) • (matrixPower a A₁ + matrixPower a A₂)
    let Bavg : Mₙ n := ((2 : ℂ)⁻¹) • (matrixPower b B₁ + matrixPower b B₂)
    let C : Mₙ n := matrixPower (-(a / 2)) A₂ * matrixPower a A₁ *
      matrixPower (-(a / 2)) A₂
    let D : Mₙ n := matrixPower (-(b / 2)) B₁ * matrixPower b B₂ *
      matrixPower (-(b / 2)) B₁
    let Y : Mₙ n := matrixPower (-(a / 2)) A₂ * X * matrixPower (-(b / 2)) B₁
    powerTrace (-1) (-1) Aavg Bavg X =
      powerTrace (-1) (-1) (((2 : ℂ)⁻¹) • (C + 1)) (((2 : ℂ)⁻¹) • (1 + D)) Y := by
  dsimp only
  let U : Mₙ n := matrixPower (-(a / 2)) A₂
  let V : Mₙ n := matrixPower (-(b / 2)) B₁
  let Aavg : Mₙ n := ((2 : ℂ)⁻¹) • (matrixPower a A₁ + matrixPower a A₂)
  let Bavg : Mₙ n := ((2 : ℂ)⁻¹) • (matrixPower b B₁ + matrixPower b B₂)
  let C : Mₙ n := U * matrixPower a A₁ * U
  let D : Mₙ n := V * matrixPower b B₂ * V
  have hAavg_pos : Matrix.PosDef Aavg := by
    have h :=
      matrixPosDef_convex_combo (t := (1 / 2 : ℝ))
        (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
        (matrixPower_posDef_of_posDef (r := a) hA₁)
        (matrixPower_posDef_of_posDef (r := a) hA₂)
    convert h using 1
    ext i j
    simp [Aavg, one_div]
    ring
  have hBavg_pos : Matrix.PosDef Bavg := by
    have h :=
      matrixPosDef_convex_combo (t := (1 / 2 : ℝ))
        (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
        (matrixPower_posDef_of_posDef (r := b) hB₁)
        (matrixPower_posDef_of_posDef (r := b) hB₂)
    convert h using 1
    ext i j
    simp [Bavg, one_div]
    ring
  have hU_A₂_U : U * matrixPower a A₂ * U = 1 := by
    have hmul₁ :=
      matrixPower_mul_matrixPower_posDef
        (r := -(a / 2)) (s := a) hA₂
    have hmul₂ :=
      matrixPower_mul_matrixPower_posDef
        (r := -(a / 2) + a) (s := -(a / 2)) hA₂
    calc
      U * matrixPower a A₂ * U =
          matrixPower (-(a / 2) + a) A₂ * U := by
            rw [show U * matrixPower a A₂ = matrixPower (-(a / 2) + a) A₂ by
              simpa [U] using hmul₁]
      _ = matrixPower (-(a / 2) + a + -(a / 2)) A₂ := by
            simpa [U] using hmul₂
      _ = 1 := by
            have hzero : -(a / 2) + a + -(a / 2) = 0 := by ring
            rw [hzero, matrixPower_zero_posDef hA₂]
  have hV_B₁_V : V * matrixPower b B₁ * V = 1 := by
    have hmul₁ :=
      matrixPower_mul_matrixPower_posDef
        (r := -(b / 2)) (s := b) hB₁
    have hmul₂ :=
      matrixPower_mul_matrixPower_posDef
        (r := -(b / 2) + b) (s := -(b / 2)) hB₁
    calc
      V * matrixPower b B₁ * V =
          matrixPower (-(b / 2) + b) B₁ * V := by
            rw [show V * matrixPower b B₁ = matrixPower (-(b / 2) + b) B₁ by
              simpa [V] using hmul₁]
      _ = matrixPower (-(b / 2) + b + -(b / 2)) B₁ := by
            simpa [V] using hmul₂
      _ = 1 := by
            have hzero : -(b / 2) + b + -(b / 2) = 0 := by ring
            rw [hzero, matrixPower_zero_posDef hB₁]
  have hCavg :
      ((2 : ℂ)⁻¹) • (C + 1) = U * Aavg * U := by
    rw [show (1 : Mₙ n) = U * matrixPower a A₂ * U from hU_A₂_U.symm]
    simp [Aavg, C, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have hDavg :
      ((2 : ℂ)⁻¹) • (1 + D) = V * Bavg * V := by
    rw [show (1 : Mₙ n) = V * matrixPower b B₁ * V from hV_B₁_V.symm]
    simp [Bavg, D, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have hconj :=
    powerTrace_neg_one_conj_posDef
      (r := a / 2) (s := b / 2) (A := A₂) (B := B₁)
      (H := Aavg) (K := Bavg) (X := X) hA₂ hB₁ hAavg_pos hBavg_pos
  simpa [U, V, Aavg, Bavg, C, D, hCavg, hDavg] using hconj.symm

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem concrete_normalized_endpoint_average_qform {n : ℕ}
    {a b : ℝ} {A₁ A₂ B₁ B₂ X : Mₙ n}
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    let C : Mₙ n := matrixPower (-(a / 2)) A₂ * matrixPower a A₁ *
      matrixPower (-(a / 2)) A₂
    let D : Mₙ n := matrixPower (-(b / 2)) B₁ * matrixPower b B₂ *
      matrixPower (-(b / 2)) B₁
    let Y : Mₙ n := matrixPower (-(a / 2)) A₂ * X * matrixPower (-(b / 2)) B₁
    powerTrace (-1) (-1) (((2 : ℂ)⁻¹) • (C + 1)) (((2 : ℂ)⁻¹) • (1 + D)) Y ≤
      (powerTrace (-a) (-b) A₁ B₁ X + powerTrace (-a) (-b) A₂ B₂ X) / 2 := by
  dsimp only
  /- Step 1: Form the normalized congruence transforms C, D and the transformed vector Y. -/
  let C : Mₙ n := matrixPower (-(a / 2)) A₂ * matrixPower a A₁ *
    matrixPower (-(a / 2)) A₂
  let D : Mₙ n := matrixPower (-(b / 2)) B₁ * matrixPower b B₂ *
    matrixPower (-(b / 2)) B₁
  let Y : Mₙ n := matrixPower (-(a / 2)) A₂ * X * matrixPower (-(b / 2)) B₁
  /- Step 2: Establish positive-definiteness of the normalized operators C and D. -/
  have hC : Matrix.PosDef C := by
    simpa [C] using normalized_matrixPower_posDef (a := a) hA₁ hA₂
  have hD : Matrix.PosDef D := by
    simpa [D] using normalized_matrixPower_posDef (a := b) hB₂ hB₁
  /- Step 3: Identify the left-endpoint powerTrace with the a-weighted form by congruence. -/
  have hleft :
      powerTrace (-1) 0 C D Y = powerTrace (-a) (-b) A₁ B₁ X := by
    let U : Mₙ n := matrixPower (-(a / 2)) A₂
    let Uinv : Mₙ n := matrixPower (a / 2) A₂
    let V : Mₙ n := matrixPower (-(b / 2)) B₁
    let Aneg : Mₙ n := matrixPower (-a) A₁
    let Bneg : Mₙ n := matrixPower (-b) B₁
    have hCinv :
        matrixPower (-1) C =
          Uinv * Aneg * Uinv := by
      simpa [C] using matrixPower_neg_one_normalized_matrixPower (a := a) hA₁ hA₂
    have hDzero : matrixPower 0 D = 1 := matrixPower_zero_posDef hD
    have hUstar : Matrix.conjTranspose U = U := by
      simpa [U] using
        (matrixPower_posDef_of_posDef (r := -(a / 2)) hA₂).1
    have hVstar : Matrix.conjTranspose V = V := by
      simpa [V] using
        (matrixPower_posDef_of_posDef (r := -(b / 2)) hB₁).1
    have hUUinv : U * Uinv = 1 := by
      simpa [U, Uinv, neg_neg] using
        matrixPower_mul_neg_eq_one_posDef (r := -(a / 2)) hA₂
    have hUinvU : Uinv * U = 1 := by
      simpa [U, Uinv, neg_neg] using
        matrixPower_neg_mul_eq_one_posDef (r := -(a / 2)) hA₂
    have hVV : V * V = Bneg := by
      calc
        V * V = matrixPower (-(b / 2) + -(b / 2)) B₁ := by
          simpa [V] using matrixPower_mul_matrixPower_posDef
            (r := -(b / 2)) (s := -(b / 2)) hB₁
        _ = Bneg := by
          congr 1
          ring
    have htrace :
        Matrix.trace (Matrix.conjTranspose Y * matrixPower (-1) C * Y * matrixPower 0 D) =
          Matrix.trace (Matrix.conjTranspose X * Aneg * X * Bneg) := by
      have hinner :
          U * (Uinv * (Aneg * (Uinv * (U * (X * V))))) = Aneg * (X * V) := by
        calc
          U * (Uinv * (Aneg * (Uinv * (U * (X * V))))) =
              (U * Uinv) * (Aneg * (Uinv * (U * (X * V)))) := by
                rw [Matrix.mul_assoc]
          _ = 1 * (Aneg * (Uinv * (U * (X * V)))) := by rw [hUUinv]
          _ = Aneg * (Uinv * (U * (X * V))) := by rw [Matrix.one_mul]
          _ = Aneg * ((Uinv * U) * (X * V)) := by
                rw [← Matrix.mul_assoc Uinv U (X * V)]
          _ = Aneg * (1 * (X * V)) := by rw [hUinvU]
          _ = Aneg * (X * V) := by rw [Matrix.one_mul]
      calc
        Matrix.trace (Matrix.conjTranspose Y * matrixPower (-1) C * Y * matrixPower 0 D) =
            Matrix.trace (V * (Matrix.conjTranspose X *
              (U * (Uinv * (Aneg * (Uinv * (U * (X * V)))))))) := by
              simp [Y, U, Uinv, V, Aneg, hCinv, hDzero, hUstar, hVstar,
                Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Matrix.trace (V * (Matrix.conjTranspose X * (Aneg * (X * V)))) := by
              rw [hinner]
        _ = Matrix.trace (V * ((Matrix.conjTranspose X * Aneg * X) * V)) := by
              simp [Matrix.mul_assoc]
        _ = Matrix.trace (((Matrix.conjTranspose X * Aneg * X) * V) * V) := by
              rw [Matrix.trace_mul_comm]
        _ = Matrix.trace ((Matrix.conjTranspose X * Aneg * X) * (V * V)) := by
              simp [Matrix.mul_assoc]
        _ = Matrix.trace ((Matrix.conjTranspose X * Aneg * X) * Bneg) := by
              rw [hVV]
        _ = Matrix.trace (Matrix.conjTranspose X * Aneg * X * Bneg) := by
              simp [Matrix.mul_assoc]
    simpa [powerTrace, Aneg, Bneg] using congrArg Complex.re htrace
  /- Step 4: Identify the right-endpoint powerTrace with the b-weighted form likewise. -/
  have hright :
      powerTrace 0 (-1) C D Y = powerTrace (-a) (-b) A₂ B₂ X := by
    let U : Mₙ n := matrixPower (-(a / 2)) A₂
    let V : Mₙ n := matrixPower (-(b / 2)) B₁
    let Vinv : Mₙ n := matrixPower (b / 2) B₁
    let Aneg : Mₙ n := matrixPower (-a) A₂
    let Bneg : Mₙ n := matrixPower (-b) B₂
    have hCzero : matrixPower 0 C = 1 := matrixPower_zero_posDef hC
    have hDinv :
        matrixPower (-1) D =
          Vinv * Bneg * Vinv := by
      simpa [D] using matrixPower_neg_one_normalized_matrixPower (a := b) hB₂ hB₁
    have hUstar : Matrix.conjTranspose U = U := by
      simpa [U] using
        (matrixPower_posDef_of_posDef (r := -(a / 2)) hA₂).1
    have hVstar : Matrix.conjTranspose V = V := by
      simpa [V] using
        (matrixPower_posDef_of_posDef (r := -(b / 2)) hB₁).1
    have hUU : U * U = Aneg := by
      calc
        U * U = matrixPower (-(a / 2) + -(a / 2)) A₂ := by
          simpa [U] using matrixPower_mul_matrixPower_posDef
            (r := -(a / 2)) (s := -(a / 2)) hA₂
        _ = Aneg := by
          congr 1
          ring
    have hVVinv : V * Vinv = 1 := by
      simpa [V, Vinv, neg_neg] using
        matrixPower_mul_neg_eq_one_posDef (r := -(b / 2)) hB₁
    have hVinvV : Vinv * V = 1 := by
      simpa [V, Vinv, neg_neg] using
        matrixPower_neg_mul_eq_one_posDef (r := -(b / 2)) hB₁
    have htrace :
        Matrix.trace (Matrix.conjTranspose Y * matrixPower 0 C * Y * matrixPower (-1) D) =
          Matrix.trace (Matrix.conjTranspose X * Aneg * X * Bneg) := by
      have hinner :
          U * (U * (X * (V * (Vinv * (Bneg * Vinv))))) =
            Aneg * (X * (Bneg * Vinv)) := by
        calc
          U * (U * (X * (V * (Vinv * (Bneg * Vinv))))) =
              (U * U) * (X * (V * (Vinv * (Bneg * Vinv)))) := by
                rw [Matrix.mul_assoc]
          _ = Aneg * (X * (V * (Vinv * (Bneg * Vinv)))) := by rw [hUU]
          _ = Aneg * (X * ((V * Vinv) * (Bneg * Vinv))) := by
                rw [← Matrix.mul_assoc V Vinv (Bneg * Vinv)]
          _ = Aneg * (X * (1 * (Bneg * Vinv))) := by rw [hVVinv]
          _ = Aneg * (X * (Bneg * Vinv)) := by rw [Matrix.one_mul]
      calc
        Matrix.trace (Matrix.conjTranspose Y * matrixPower 0 C * Y * matrixPower (-1) D) =
            Matrix.trace (V * (Matrix.conjTranspose X *
              (U * (U * (X * (V * (Vinv * (Bneg * Vinv)))))))) := by
              simp [Y, U, V, Vinv, Bneg, hCzero, hDinv, hUstar, hVstar,
                Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Matrix.trace (V * (Matrix.conjTranspose X * (Aneg * (X * (Bneg * Vinv))))) := by
              rw [hinner]
        _ = Matrix.trace (V * ((Matrix.conjTranspose X * Aneg * X * Bneg) * Vinv)) := by
              simp [Matrix.mul_assoc]
        _ = Matrix.trace (((Matrix.conjTranspose X * Aneg * X * Bneg) * Vinv) * V) := by
              rw [Matrix.trace_mul_comm]
        _ = Matrix.trace ((Matrix.conjTranspose X * Aneg * X * Bneg) * (Vinv * V)) := by
              simp [Matrix.mul_assoc]
        _ = Matrix.trace ((Matrix.conjTranspose X * Aneg * X * Bneg) * 1) := by
              rw [hVinvV]
        _ = Matrix.trace (Matrix.conjTranspose X * Aneg * X * Bneg) := by
              rw [Matrix.mul_one]
    simpa [powerTrace, Aneg, Bneg] using congrArg Complex.re htrace
  /- Step 5: Apply the abstract normalized-average inequality and rewrite both endpoints. -/
  have hnorm := normalized_endpoint_average_qform (C := C) (D := D) (X := Y) hC hD
  rwa [hleft, hright] at hnorm

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem ringInverse_leftMul_matrixPower {n : ℕ} {r : ℝ} {A : Mₙ n}
    (hA : Matrix.PosDef A) :
    Ring.inverse (leftMul (matrixPower r A)) = leftMul (matrixPower (-r) A) := by
  let u : (HSOp n)ˣ :=
    { val := leftMul (matrixPower r A)
      inv := leftMul (matrixPower (-r) A)
      val_inv := by
        ext X i j
        change (matrixPower r A * (matrixPower (-r) A * X)) i j = X i j
        rw [← Matrix.mul_assoc,
          matrixPower_mul_neg_eq_one_posDef (r := r) hA, Matrix.one_mul]
      inv_val := by
        ext X i j
        change (matrixPower (-r) A * (matrixPower r A * X)) i j = X i j
        rw [← Matrix.mul_assoc,
          matrixPower_neg_mul_eq_one_posDef (r := r) hA, Matrix.one_mul] }
  change Ring.inverse (leftMul (matrixPower r A)) = ↑u⁻¹
  simpa [u] using Ring.inverse_unit u

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem ringInverse_rightMul_matrixPower {n : ℕ} {r : ℝ} {B : Mₙ n}
    (hB : Matrix.PosDef B) :
    Ring.inverse (rightMul (matrixPower r B)) = rightMul (matrixPower (-r) B) := by
  let u : (HSOp n)ˣ :=
    { val := rightMul (matrixPower r B)
      inv := rightMul (matrixPower (-r) B)
      val_inv := by
        ext X i j
        change ((X * matrixPower (-r) B) * matrixPower r B) i j = X i j
        rw [Matrix.mul_assoc,
          matrixPower_neg_mul_eq_one_posDef (r := r) hB, Matrix.mul_one]
      inv_val := by
        ext X i j
        change ((X * matrixPower r B) * matrixPower (-r) B) i j = X i j
        rw [Matrix.mul_assoc,
          matrixPower_mul_neg_eq_one_posDef (r := r) hB, Matrix.mul_one] }
  change Ring.inverse (rightMul (matrixPower r B)) = ↑u⁻¹
  simpa [u] using Ring.inverse_unit u

/-- Source: Hiai, proof of Theorem 6.4. -/
theorem ringInverse_leftRightMul_matrixPower_product {n : ℕ}
    {r s : ℝ} {A B : Mₙ n} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    Ring.inverse (leftMul (matrixPower r A) * rightMul (matrixPower s B)) =
      leftMul (matrixPower (-r) A) * rightMul (matrixPower (-s) B) := by
  rw [Ring.mul_inverse_rev' (leftMul_commute_rightMul (matrixPower r A)
      (matrixPower s B))]
  rw [ringInverse_leftMul_matrixPower (r := r) hA,
    ringInverse_rightMul_matrixPower (r := s) hB]
  exact (leftMul_commute_rightMul (matrixPower (-r) A) (matrixPower (-s) B)).eq.symm

/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem normalized_inverse_product_qform_eq_powerTrace {n : ℕ}
    {C D X : Mₙ n} (hC : Matrix.PosDef C) (hD : Matrix.PosDef D) :
    (Matrix.conjTranspose X *
        (Ring.inverse
          ((((2 : ℂ)⁻¹) • (leftMul C + 1)) *
            (((2 : ℂ)⁻¹) • (1 + rightMul D))) X)).trace.re =
      powerTrace (-1) (-1)
        (((2 : ℂ)⁻¹) • (C + 1)) (((2 : ℂ)⁻¹) • (1 + D)) X := by
  let Cavg : Mₙ n := ((2 : ℂ)⁻¹) • (C + 1)
  let Davg : Mₙ n := ((2 : ℂ)⁻¹) • (1 + D)
  have hCavg : Matrix.PosDef Cavg := by
    simpa [Cavg] using matrixPosDef_half_add_one hC
  have hDavg : Matrix.PosDef Davg := by
    simpa [Davg, add_comm] using matrixPosDef_half_add_one hD
  have hT :
      (((2 : ℂ)⁻¹) • (leftMul C + 1)) * (((2 : ℂ)⁻¹) • (1 + rightMul D)) =
        leftMul Cavg * rightMul Davg := by
    rw [leftMul_half_add_one_eq C, rightMul_half_add_one_eq D]
  rw [hT]
  conv_lhs =>
    rw [← matrixPower_one_posDef hCavg, ← matrixPower_one_posDef hDavg]
  rw [ringInverse_leftRightMul_matrixPower_product
    (r := 1) (s := 1) hCavg hDavg]
  simpa [Cavg, Davg] using
    leftRightMul_matrixPower_product_qform_eq_powerTrace
      (p := -1) (q := -1) (A := Cavg) (B := Davg) (X := X)


/-- Ordered inverse kernel behind PDF (6.6), in the Hilbert--Schmidt operator
order and already returned to the fixed-vector quadratic form.

The pre-inversion order for the normalized left/right multiplication operators
is proved inside `powerTrace_midpointConvex_negRectangle_core` below; given that
order, this helper performs the antitone inverse step without importing Lieb--Ando.

Source: Hiai, proof of Theorem 6.4. -/
private theorem ordered_inverse_kernel_qform {n : ℕ} {S T : HSOp n}
    (hS : 0 ≤ S) (hST : S ≤ T) (hSunit : IsUnit S) (hTunit : IsUnit T)
    (X : Mₙ n) :
    (Matrix.conjTranspose X * (Ring.inverse T) X).trace.re ≤
      (Matrix.conjTranspose X * (Ring.inverse S) X).trace.re :=
  hsQForm_ringInverse_antitone_of_nonneg_isUnit hS hST hSunit hTunit X


/-- Source: Hiai, proof of Theorem 6.4. -/
private theorem concrete_average_inverse_kernel_qform_direct {n : ℕ}
    {a b : ℝ} {A₁ A₂ B₁ B₂ X : Mₙ n}
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    let T : HSOp n :=
      (((2 : ℂ)⁻¹) •
        (leftMul (matrixPower a A₁) + leftMul (matrixPower a A₂))) *
        (((2 : ℂ)⁻¹) •
          (rightMul (matrixPower b B₁) + rightMul (matrixPower b B₂)))
    (Matrix.conjTranspose X * (Ring.inverse T X)).trace.re ≤
      (powerTrace (-a) (-b) A₁ B₁ X + powerTrace (-a) (-b) A₂ B₂ X) / 2 := by
  dsimp only
  let Aavg : Mₙ n := ((2 : ℂ)⁻¹) • (matrixPower a A₁ + matrixPower a A₂)
  let Bavg : Mₙ n := ((2 : ℂ)⁻¹) • (matrixPower b B₁ + matrixPower b B₂)
  let T : HSOp n :=
    (((2 : ℂ)⁻¹) •
      (leftMul (matrixPower a A₁) + leftMul (matrixPower a A₂))) *
      (((2 : ℂ)⁻¹) •
        (rightMul (matrixPower b B₁) + rightMul (matrixPower b B₂)))
  have hAavg_pos : Matrix.PosDef Aavg := by
    have h :=
      matrixPosDef_convex_combo (t := (1 / 2 : ℝ))
        (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
        (matrixPower_posDef_of_posDef (r := a) hA₁)
        (matrixPower_posDef_of_posDef (r := a) hA₂)
    convert h using 1
    ext i j
    simp [Aavg, one_div]
    ring
  have hBavg_pos : Matrix.PosDef Bavg := by
    have h :=
      matrixPosDef_convex_combo (t := (1 / 2 : ℝ))
        (by norm_num : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
        (matrixPower_posDef_of_posDef (r := b) hB₁)
        (matrixPower_posDef_of_posDef (r := b) hB₂)
    convert h using 1
    ext i j
    simp [Bavg, one_div]
    ring
  have hL :
      ((2 : ℂ)⁻¹) •
          (leftMul (matrixPower a A₁) + leftMul (matrixPower a A₂)) =
        leftMul Aavg := by
    ext Y i j
    simp [Aavg, leftMul_apply, Matrix.add_mul]
    ring_nf
  have hR :
      ((2 : ℂ)⁻¹) •
          (rightMul (matrixPower b B₁) + rightMul (matrixPower b B₂)) =
        rightMul Bavg := by
    ext Y i j
    simp [Bavg, rightMul_apply, Matrix.mul_add]
    ring_nf
  have hT : T = leftMul Aavg * rightMul Bavg := by
    change
      (((2 : ℂ)⁻¹) •
        (leftMul (matrixPower a A₁) + leftMul (matrixPower a A₂))) *
        (((2 : ℂ)⁻¹) •
          (rightMul (matrixPower b B₁) + rightMul (matrixPower b B₂))) =
        leftMul Aavg * rightMul Bavg
    rw [hL, hR]
  have hqform :
      (Matrix.conjTranspose X * (Ring.inverse T X)).trace.re =
        powerTrace (-1) (-1) Aavg Bavg X := by
    rw [hT]
    conv_lhs =>
      rw [← matrixPower_one_posDef hAavg_pos, ← matrixPower_one_posDef hBavg_pos]
    rw [ringInverse_leftRightMul_matrixPower_product
      (r := 1) (s := 1) hAavg_pos hBavg_pos]
    have hAone : matrixPower 1 Aavg = Aavg := matrixPower_one_posDef hAavg_pos
    have hBone : matrixPower 1 Bavg = Bavg := matrixPower_one_posDef hBavg_pos
    simpa [hAone, hBone] using
      leftRightMul_matrixPower_product_qform_eq_powerTrace
        (p := -1) (q := -1) (A := Aavg) (B := Bavg) (X := X)
  have hnorm :=
    concrete_normalized_endpoint_average_qform
      (a := a) (b := b) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
      (X := X) hA₁ hA₂ hB₁ hB₂
  have heq :=
    average_eq_normalized_qform
      (a := a) (b := b) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
      (X := X) hA₁ hA₂ hB₁ hB₂
  dsimp only at hnorm heq
  rw [← heq] at hnorm
  exact hqform.trans_le hnorm


/-- Source: Hiai, Theorem 6.4. -/
private theorem powerTrace_midpointConvex_negRectangle_core {n : ℕ}
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    {A₁ A₂ B₁ B₂ X : Mₙ n}
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    powerTrace (-a) (-b) (((2 : ℂ)⁻¹) • (A₁ + A₂))
        (((2 : ℂ)⁻¹) • (B₁ + B₂)) X ≤
      (powerTrace (-a) (-b) A₁ B₁ X + powerTrace (-a) (-b) A₂ B₂ X) / 2 := by
  /- Step 1: Define the midpoint matrices, the power-averages, and the operators Tavg, Tmid. -/
  let Am : Mₙ n := ((2 : ℂ)⁻¹) • (A₁ + A₂)
  let Bm : Mₙ n := ((2 : ℂ)⁻¹) • (B₁ + B₂)
  let Aavg : Mₙ n := ((2 : ℂ)⁻¹) • (matrixPower a A₁ + matrixPower a A₂)
  let Bavg : Mₙ n := ((2 : ℂ)⁻¹) • (matrixPower b B₁ + matrixPower b B₂)
  let Tavg : HSOp n := leftMul Aavg * rightMul Bavg
  let Tmid : HSOp n := leftMul (matrixPower a Am) * rightMul (matrixPower b Bm)
  have hhalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  /- Step 2: Establish positive-definiteness of the midpoint and average matrices. -/
  have hAm_pos : Matrix.PosDef Am := by
    have h := matrixPosDef_convex_combo (t := (1 / 2 : ℝ)) hhalf hA₁ hA₂
    convert h using 1
    ext i j
    simp [Am, one_div]
    ring
  have hBm_pos : Matrix.PosDef Bm := by
    have h := matrixPosDef_convex_combo (t := (1 / 2 : ℝ)) hhalf hB₁ hB₂
    convert h using 1
    ext i j
    simp [Bm, one_div]
    ring
  have hAavg_pos : Matrix.PosDef Aavg := by
    have h :=
      matrixPosDef_convex_combo (t := (1 / 2 : ℝ)) hhalf
        (matrixPower_posDef_of_posDef (r := a) hA₁)
        (matrixPower_posDef_of_posDef (r := a) hA₂)
    convert h using 1
    ext i j
    simp [Aavg, one_div]
    ring
  have hBavg_pos : Matrix.PosDef Bavg := by
    have h :=
      matrixPosDef_convex_combo (t := (1 / 2 : ℝ)) hhalf
        (matrixPower_posDef_of_posDef (r := b) hB₁)
        (matrixPower_posDef_of_posDef (r := b) hB₂)
    convert h using 1
    ext i j
    simp [Bavg, one_div]
    ring
  /- Step 3: Bound each power-average below the power of the midpoint by matrix-power concavity. -/
  have hAavg_le : Aavg ≤ matrixPower a Am := by
    have hconc :=
      matrixPower_concave_nonneg ha hhalf
        (Matrix.PosDef.nonneg hA₁) (Matrix.PosDef.nonneg hA₂)
    have hAavg_eq :
        Aavg = (1 / 2 : ℝ) • matrixPower a A₁ + (1 - 1 / 2 : ℝ) • matrixPower a A₂ := by
      ext i j
      simp [Aavg, one_div]
      ring
    have hAm_eq :
        Am = (1 / 2 : ℝ) • A₁ + (1 - 1 / 2 : ℝ) • A₂ := by
      ext i j
      simp [Am, one_div]
      ring
    simpa [hAavg_eq, hAm_eq] using hconc
  have hBavg_le : Bavg ≤ matrixPower b Bm := by
    have hconc :=
      matrixPower_concave_nonneg hb hhalf
        (Matrix.PosDef.nonneg hB₁) (Matrix.PosDef.nonneg hB₂)
    have hBavg_eq :
        Bavg = (1 / 2 : ℝ) • matrixPower b B₁ + (1 - 1 / 2 : ℝ) • matrixPower b B₂ := by
      ext i j
      simp [Bavg, one_div]
      ring
    have hBm_eq :
        Bm = (1 / 2 : ℝ) • B₁ + (1 - 1 / 2 : ℝ) • B₂ := by
      ext i j
      simp [Bm, one_div]
      ring
    simpa [hBavg_eq, hBm_eq] using hconc
  /- Step 4: Lift the bounds to the operator order Tavg ≤ Tmid and record strict positivity. -/
  have hTle : Tavg ≤ Tmid := by
    dsimp [Tavg, Tmid]
    exact leftRightMul_product_mono
      (Matrix.PosDef.nonneg (matrixPower_posDef_of_posDef (r := a) hAm_pos))
      (Matrix.PosDef.nonneg hBavg_pos)
      hAavg_le hBavg_le
  have hTavg_pos : IsStrictlyPositive Tavg := by
    dsimp [Tavg]
    exact leftRightMul_product_isUnit hAavg_pos hBavg_pos |>.isStrictlyPositive
      (leftRightMul_product_nonneg
        (Matrix.PosDef.nonneg hAavg_pos) (Matrix.PosDef.nonneg hBavg_pos))
  have hTmid_pos : IsStrictlyPositive Tmid := by
    dsimp [Tmid]
    exact leftRightMul_matrixPower_product_isStrictlyPositive
      (p := a) (q := b) hAm_pos hBm_pos
  /- Step 5: Express the midpoint powerTrace via the inverse kernel and identify Tavg. -/
  have hmid_qform :
      powerTrace (-a) (-b) Am Bm X =
        (Matrix.conjTranspose X * (Ring.inverse Tmid X)).trace.re := by
    dsimp [Tmid]
    rw [ringInverse_leftRightMul_matrixPower_product (r := a) (s := b) hAm_pos hBm_pos]
    simpa using
      (leftRightMul_matrixPower_product_qform_eq_powerTrace
        (p := -a) (q := -b) (A := Am) (B := Bm) (X := X)).symm
  have hkernel :=
    concrete_average_inverse_kernel_qform_direct
      (a := a) (b := b) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
      (X := X) hA₁ hA₂ hB₁ hB₂
  have hTavg_eq :
      (((2 : ℂ)⁻¹) •
        (leftMul (matrixPower a A₁) + leftMul (matrixPower a A₂))) *
        (((2 : ℂ)⁻¹) •
          (rightMul (matrixPower b B₁) + rightMul (matrixPower b B₂))) = Tavg := by
    dsimp [Tavg, Aavg, Bavg]
    have hL :
        ((2 : ℂ)⁻¹) •
            (leftMul (matrixPower a A₁) + leftMul (matrixPower a A₂)) =
          leftMul (((2 : ℂ)⁻¹) • (matrixPower a A₁ + matrixPower a A₂)) := by
      ext Y i j
      simp [leftMul_apply, Matrix.add_mul]
      ring_nf
    have hR :
        ((2 : ℂ)⁻¹) •
            (rightMul (matrixPower b B₁) + rightMul (matrixPower b B₂)) =
          rightMul (((2 : ℂ)⁻¹) • (matrixPower b B₁ + matrixPower b B₂)) := by
      ext Y i j
      simp [rightMul_apply, Matrix.mul_add]
      ring_nf
    rw [hL, hR]
  dsimp only at hkernel
  rw [hTavg_eq] at hkernel
  /- Step 6: Use antitonicity of the inverse kernel and chain the bounds to conclude. -/
  have hanti :
      (Matrix.conjTranspose X * (Ring.inverse Tmid X)).trace.re ≤
        (Matrix.conjTranspose X * (Ring.inverse Tavg X)).trace.re :=
    ordered_inverse_kernel_qform
      hTavg_pos.nonneg hTle hTavg_pos.isUnit hTmid_pos.isUnit X
  calc
    powerTrace (-a) (-b) (((2 : ℂ)⁻¹) • (A₁ + A₂))
        (((2 : ℂ)⁻¹) • (B₁ + B₂)) X =
        powerTrace (-a) (-b) Am Bm X := by rfl
    _ = (Matrix.conjTranspose X * (Ring.inverse Tmid X)).trace.re := hmid_qform
    _ ≤ (Matrix.conjTranspose X * (Ring.inverse Tavg X)).trace.re := hanti
    _ ≤ (powerTrace (-a) (-b) A₁ B₁ X + powerTrace (-a) (-b) A₂ B₂ X) / 2 := hkernel

/-- Source: Hiai, Theorem 6.4. -/
theorem powerTrace_midpointConvex_negRectangle :
    ∀ {n : ℕ} {p q : ℝ} {X : Mₙ n},
      p ∈ Set.Icc (-1 : ℝ) 0 →
      q ∈ Set.Icc (-1 : ℝ) 0 →
      ∀ {A₁ A₂ B₁ B₂ : Mₙ n},
        Matrix.PosDef A₁ →
        Matrix.PosDef A₂ →
        Matrix.PosDef B₁ →
        Matrix.PosDef B₂ →
        powerTrace p q (((2 : ℂ)⁻¹) • (A₁ + A₂))
            (((2 : ℂ)⁻¹) • (B₁ + B₂)) X ≤
          (powerTrace p q A₁ B₁ X + powerTrace p q A₂ B₂ X) / 2 := by
  intro n p q X hp hq A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂
  let a : ℝ := -p
  let b : ℝ := -q
  have ha : a ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> dsimp [a] <;> linarith [hp.1, hp.2]
  have hb : b ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> dsimp [b] <;> linarith [hq.1, hq.2]
  have hcore :=
    powerTrace_midpointConvex_negRectangle_core
      (a := a) (b := b) ha hb (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
      (X := X) hA₁ hA₂ hB₁ hB₂
  simpa [a, b] using hcore


end MatrixScopedInstances

end TraceConvexity
end HiaiPetz
