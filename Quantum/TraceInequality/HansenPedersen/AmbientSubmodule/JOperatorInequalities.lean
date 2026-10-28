/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.AmbientSubmodule.JOperator
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.JOperator
import Quantum.TraceInequality.HiaiPetz.HilbertSchmidt.InnerProduct
import Quantum.TraceInequality.HansenPedersen.Core.Basic
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.JOperatorInequalities

/-!
# Quadratic-form consequences for ambient operators

Inequalities and quadratic-form transport lemmas following from the
positive-definite `J`-operator inverse identities.

## Main results

* `hsQForm_hsAdjoint_comp` and `hsQForm_comp_hsAdjoint`: quadratic-form
  identities for conjugating an operator by a Hilbert-Schmidt map and its
  adjoint.
* `ringInverse_antitone_of_nonneg_isUnit`: order reversal of the ring inverse
  for positive invertible operators.
* `hsle_jOperatorInv_of_hsle_jOperator_of_posDef` and
  `hsle_jOperator_of_hsle_jOperatorInv_of_posDef`: conversion between order
  inequalities for `jOperator` and `jOperatorInv`.

## References

* Internal finite-dimensional quadratic-form layer for the Hiai-Petz
  data-processing construction.
-/

namespace HiaiPetz

open scoped MatrixOrder

open scoped ComplexOrder

noncomputable section MatrixScopedInstances

attribute [local instance] instMatrixNormedAddCommGroupScoped
attribute [local instance] instMatrixNormedSpaceScoped
attribute [local instance] instMatrixInnerProductSpaceScoped
attribute [local instance] instMatrixCompleteSpaceScoped
attribute [local instance] instWithLpMatrixPairInnerProductSpace
attribute [local instance] instWithLpMatrixPairNormedSpace
attribute [local instance] instWithLpMatrixPairCompleteSpace

/-- Continuity on the positive half-line restricts to the union of spectra of
two positive-definite `jArg` operators. -/
@[fun_prop] theorem continuousOn_jArg_union {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    ContinuousOn f (spectrum ℝ (jArg A₁ B₁) ∪ spectrum ℝ (jArg A₂ B₂)) := by
  apply hf.mono
  intro x hx
  rcases hx with hx | hx
  · exact spectrum_jArg_subset_Ioi hA₁ hB₁ hx
  · exact spectrum_jArg_subset_Ioi hA₂ hB₂ hx

private theorem rightMul_mul_rightMul {n : ℕ} (B C : Mₙ n) :
    rightMul B * rightMul C = rightMul (C * B) := by
  ext X
  simp [rightMul_apply, mul_assoc]

private theorem hsTrace_leftMul_shift {n : ℕ} (A X Y : Mₙ n) :
    Matrix.trace (Matrix.conjTranspose X * (leftMul A Y)) =
      Matrix.trace ((Matrix.conjTranspose X * A) * Y) := by
  simp [leftMul_apply, Matrix.mul_assoc]

/-- Quadratic forms of `hsAdjoint Φ ∘ T ∘ Φ` are the quadratic forms of `T`
evaluated on the image `Φ X`. -/
theorem hsQForm_hsAdjoint_comp {n m : ℕ} (Φ : HSMap n m) (T : HSOp m) (X : Mₙ n) :
    Complex.re
      (Matrix.trace
        (Matrix.conjTranspose X * (((hsAdjoint Φ).comp (T.comp Φ)) X))) =
      Complex.re
        (Matrix.trace (Matrix.conjTranspose (Φ X) * (T (Φ X)))) := by
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  letI := instMatrixNormedAddCommGroup (n := m)
  letI := instMatrixNormedSpace (n := m)
  letI := instMatrixInnerProductSpace (n := m)
  letI := instMatrixCompleteSpace (n := m)
  have hinner :
      inner ℂ X (((hsAdjoint Φ).comp (T.comp Φ)) X) = inner ℂ (Φ X) (T (Φ X)) := by
    simpa [hsAdjoint, ContinuousLinearMap.comp_apply] using
      @ContinuousLinearMap.adjoint_inner_right ℂ (Mₙ n) (Mₙ m)
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixNormedAddCommGroup (n := m))
        (instMatrixInnerProductSpace (n := n))
        (instMatrixInnerProductSpace (n := m))
        (instMatrixCompleteSpace (n := n))
        (instMatrixCompleteSpace (n := m))
        Φ X (T (Φ X))
  calc
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X * (((hsAdjoint Φ).comp (T.comp Φ)) X)))
      = Complex.re
          (Matrix.trace ((((hsAdjoint Φ).comp (T.comp Φ)) X) * Matrix.conjTranspose X)) := by
            rw [Matrix.trace_mul_comm]
    _ = Complex.re (Matrix.trace (T (Φ X) * Matrix.conjTranspose (Φ X))) := by
          simpa [inner] using congrArg Complex.re hinner
    _ = Complex.re (Matrix.trace (Matrix.conjTranspose (Φ X) * T (Φ X))) := by
          rw [Matrix.trace_mul_comm]

/-- The Hilbert-Schmidt quadratic form of a difference is the difference of
the two quadratic forms. -/
theorem hsQForm_sub {n : ℕ} (S T : HSOp n) (X : Mₙ n) :
    Complex.re (Matrix.trace (Matrix.conjTranspose X * ((S - T) X))) =
      Complex.re (Matrix.trace (Matrix.conjTranspose X * (S X))) -
        Complex.re (Matrix.trace (Matrix.conjTranspose X * (T X))) := by
  change Complex.re (Matrix.trace (Matrix.conjTranspose X * (S X - T X))) = _
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

/-- For self-adjoint `B`, a right multiplication by `B` can be shifted from the
trace factor to the test matrix inside a real Hilbert-Schmidt quadratic form. -/
theorem hsQForm_shift_rightMul_testMatrix {n : ℕ} {B X Y : Mₙ n}
    (hB : IsSelfAdjoint B) :
    Complex.re (Matrix.trace ((Matrix.conjTranspose X * Y) * B)) =
      Complex.re (Matrix.trace (Matrix.conjTranspose (rightMul B X) * Y)) := by
  have htrace :
      Matrix.trace ((Matrix.conjTranspose X * Y) * B) =
        Matrix.trace (B * (Matrix.conjTranspose X * Y)) := by
    rw [Matrix.trace_mul_comm]
  have hrhs :
      Complex.re (Matrix.trace (Matrix.conjTranspose (rightMul B X) * Y)) =
        Complex.re (Matrix.trace (B * (Matrix.conjTranspose X * Y))) := by
    have hB' : Matrix.conjTranspose B = B := by
      simpa using hB.star_eq
    rw [rightMul_apply, Matrix.conjTranspose_mul, hB']
    simp [Matrix.mul_assoc]
  calc
    Complex.re (Matrix.trace ((Matrix.conjTranspose X * Y) * B))
      = Complex.re (Matrix.trace (B * (Matrix.conjTranspose X * Y))) := by
          exact congrArg Complex.re htrace
    _ = Complex.re (Matrix.trace (Matrix.conjTranspose (rightMul B X) * Y)) := hrhs.symm

/-- The right-multiplication shift specialized to the positive inverse of a
positive-definite matrix. -/
theorem hsQForm_shift_rightMul_posInv_testMatrix {n : ℕ} {B X Y : Mₙ n}
    (hB : Matrix.PosDef B) :
    Complex.re (Matrix.trace ((Matrix.conjTranspose X * Y) * B⁻¹)) =
      Complex.re (Matrix.trace (Matrix.conjTranspose (rightMul (B⁻¹) X) * Y)) := by
  have hInv : IsSelfAdjoint (B⁻¹) := (posInv_posDef hB).1
  simpa using hsQForm_shift_rightMul_testMatrix (B := B⁻¹) (X := X) (Y := Y) hInv

/-- Standard quadratic-form presentation of `jOperator f A B`, moving the
right-multiplication factor from the operator to the test matrix. -/
theorem hsQForm_standard_jOperator_of_posDef {n : ℕ} {f : ℝ → ℝ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) (X Y : Mₙ n) :
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose (rightMul B X) *
            (hsCfcR f (jArg A B) Y))) =
      Complex.re (Matrix.trace (Matrix.conjTranspose X * (jOperator f A B Y))) := by
  rw [← hsQForm_shift_rightMul_testMatrix hB.1, hsQForm_jOperator_of_posDef hB X Y]

/-- Standard quadratic-form presentation of `jOperatorInv f A B`, using the
positive inverse of `B` to shift the right-multiplication factor. -/
theorem hsQForm_standard_jOperatorInv_of_posDef {n : ℕ} {f : ℝ → ℝ} {A B : Mₙ n}
    (hB : Matrix.PosDef B) (X Y : Mₙ n) :
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose (rightMul (B⁻¹) X) *
            (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) Y))) =
      Complex.re (Matrix.trace (Matrix.conjTranspose X * (jOperatorInv f A B Y))) := by
  rw [← hsQForm_shift_rightMul_posInv_testMatrix hB, hsQForm_jOperatorInv_of_posDef hB X Y]

/-- Under positivity of `f` on the positive half-line and positive-definite
inputs, `jOperatorInv f A B` is a unit. -/
theorem jOperatorInv_isUnit_of_posDef {n : ℕ} {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    IsUnit (jOperatorInv f A B) := by
  rw [← ringInverse_jOperator_eq_jOperatorInv_of_posDef (f := f) (A := A) (B := B) hf hpos hA hB]
  exact (jOperator_isUnit_of_posDef hf hpos hA hB).ringInverse

/-- The ring inverse of `jOperatorInv f A B` recovers `jOperator f A B` for
positive-definite inputs and a positive continuous scalar function. -/
theorem ringInverse_jOperatorInv_eq_jOperator_of_posDef {n : ℕ} {f : ℝ → ℝ}
    {A B : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    Ring.inverse (jOperatorInv f A B) = jOperator f A B := by
  let u := (jOperator_isUnit_of_posDef hf hpos hA hB).unit
  rw [← ringInverse_jOperator_eq_jOperatorInv_of_posDef (f := f) (A := A) (B := B) hf hpos hA hB]
  have hInvU :
      Ring.inverse (jOperator f A B) = (((u : Units (HSOp n))⁻¹ : Units (HSOp n)) : HSOp n) := by
    change Ring.inverse (jOperator f A B) = (((u : Units (HSOp n))⁻¹ : Units (HSOp n)) : HSOp n)
    simpa [u] using Ring.inverse_unit u
  rw [hInvU]
  simp [u]

/-- In a C⋆-algebra of Hilbert-Schmidt operators, the ring inverse reverses
order on positive invertible elements. -/
theorem ringInverse_antitone_of_nonneg_isUnit {n : ℕ} {S T : HSOp n}
    (hS : 0 ≤ S) (hST : S ≤ T) (hSunit : IsUnit S) (hTunit : IsUnit T) :
    Ring.inverse T ≤ Ring.inverse S := by
  lift S to (HSOp n)ˣ using hSunit
  lift T to (HSOp n)ˣ using hTunit
  simpa using (CStarAlgebra.inv_le_inv (A := HSOp n) hS hST)

/-- Quadratic-form version of inverse antitonicity for positive invertible
Hilbert-Schmidt operators. -/
theorem hsQForm_ringInverse_antitone_of_nonneg_isUnit {n : ℕ} {S T : HSOp n}
    (hS : 0 ≤ S) (hST : S ≤ T) (hSunit : IsUnit S) (hTunit : IsUnit T)
    (X : Mₙ n) :
    Complex.re (Matrix.trace (Matrix.conjTranspose X * ((Ring.inverse T) X))) ≤
      Complex.re (Matrix.trace (Matrix.conjTranspose X * ((Ring.inverse S) X))) := by
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  have hInv : Ring.inverse T ≤ Ring.inverse S :=
    ringInverse_antitone_of_nonneg_isUnit hS hST hSunit hTunit
  have hPosInv :
      @ContinuousLinearMap.IsPositive ℂ (Mₙ n)
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixInnerProductSpace (n := n))
        ((Ring.inverse S) - (Ring.inverse T)) := by
    simpa [ContinuousLinearMap.le_def] using hInv
  have hq :=
    @ContinuousLinearMap.IsPositive.re_inner_nonneg_right ℂ (Mₙ n)
      (inferInstance : RCLike ℂ)
      (instMatrixNormedAddCommGroup (n := n))
      (instMatrixInnerProductSpace (n := n))
      ((Ring.inverse S) - (Ring.inverse T)) hPosInv X
  change 0 ≤
      Complex.re
        (Matrix.trace (((Ring.inverse S - Ring.inverse T) X) * Matrix.conjTranspose X)) at hq
  rw [Matrix.trace_mul_comm, hsQForm_sub] at hq
  linarith

/-- An order inequality for positive `jOperator` values reverses after passing
to the corresponding `jOperatorInv` values. -/
theorem hsle_jOperatorInv_of_hsle_jOperator_of_posDef {n : ℕ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    {A₁ B₁ A₂ B₂ : Mₙ n}
    (hA₁ : Matrix.PosDef A₁) (hB₁ : Matrix.PosDef B₁)
    (hA₂ : Matrix.PosDef A₂) (hB₂ : Matrix.PosDef B₂)
    (h0 : 0 ≤ jOperator f A₁ B₁)
    (hord : jOperator f A₁ B₁ ≤ jOperator f A₂ B₂) :
    jOperatorInv f A₂ B₂ ≤ jOperatorInv f A₁ B₁ := by
  have hInv :
      Ring.inverse (jOperator f A₂ B₂) ≤ Ring.inverse (jOperator f A₁ B₁) :=
    ringInverse_antitone_of_nonneg_isUnit h0 hord
      (jOperator_isUnit_of_posDef hf hpos hA₁ hB₁)
      (jOperator_isUnit_of_posDef hf hpos hA₂ hB₂)
  simpa [
    ringInverse_jOperator_eq_jOperatorInv_of_posDef
      (f := f) (A := A₂) (B := B₂) hf hpos hA₂ hB₂,
    ringInverse_jOperator_eq_jOperatorInv_of_posDef
      (f := f) (A := A₁) (B := B₁) hf hpos hA₁ hB₁] using
    hInv

/-- An order inequality for positive `jOperatorInv` values reverses back to an
order inequality for the corresponding `jOperator` values. -/
theorem hsle_jOperator_of_hsle_jOperatorInv_of_posDef {n : ℕ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    {A₁ B₁ A₂ B₂ : Mₙ n}
    (hA₁ : Matrix.PosDef A₁) (hB₁ : Matrix.PosDef B₁)
    (hA₂ : Matrix.PosDef A₂) (hB₂ : Matrix.PosDef B₂)
    (h0 : 0 ≤ jOperatorInv f A₂ B₂)
    (hord : jOperatorInv f A₂ B₂ ≤ jOperatorInv f A₁ B₁) :
    jOperator f A₁ B₁ ≤ jOperator f A₂ B₂ := by
  have hInv :
      Ring.inverse (jOperatorInv f A₁ B₁) ≤ Ring.inverse (jOperatorInv f A₂ B₂) :=
    ringInverse_antitone_of_nonneg_isUnit h0 hord
      (jOperatorInv_isUnit_of_posDef hf hpos hA₂ hB₂)
      (jOperatorInv_isUnit_of_posDef hf hpos hA₁ hB₁)
  simpa [
    ringInverse_jOperatorInv_eq_jOperator_of_posDef
      (f := f) (A := A₁) (B := B₁) hf hpos hA₁ hB₁,
    ringInverse_jOperatorInv_eq_jOperator_of_posDef
      (f := f) (A := A₂) (B := B₂) hf hpos hA₂ hB₂] using
    hInv

end MatrixScopedInstances

end HiaiPetz

namespace HiaiPetz.AmbientSubmodule

section

open HiaiPetz Matrix Unitary
open scoped MatrixOrder ComplexOrder CStarAlgebra

/-- The trace quadratic form of `hsAdjoint Φ ∘ Φ` at `x` is the squared
Frobenius norm of `Φ x`. -/
theorem hsQForm_hsAdjoint_comp_eq_norm_sq
    {n m : ℕ} (Φ : HSMap n m) (x : Mₙ n) :
    Complex.re (Matrix.trace (Matrix.conjTranspose x * (((hsAdjoint Φ).comp Φ) x))) =
      ‖Φ x‖ ^ 2 := by
  calc
    Complex.re (Matrix.trace (Matrix.conjTranspose x * (((hsAdjoint Φ).comp Φ) x))) =
        Complex.re
          (Matrix.trace (Matrix.conjTranspose (Φ x) * ((1 : HSOp m) (Φ x)))) := by
            simpa using hsQForm_hsAdjoint_comp Φ (1 : HSOp m) x
    _ = Complex.re (inner ℂ ((1 : HSOp m) (Φ x)) (Φ x)) := by
          rw [hsQForm_real_eq_inner_real]
    _ = (↑(‖Φ x‖ ^ 2) : ℂ).re := by
          -- `exact` bridges the (defeq) instance indices between the statement's
          -- norm and the unified `instMatrixInnerProductSpace` inner product.
          simp only [ContinuousLinearMap.one_apply, Complex.ofReal_pow]
          exact congrArg Complex.re
            (@inner_self_eq_norm_sq_to_K ℂ (Mₙ m) _
              (instMatrixNormedAddCommGroup (n := m)).toSeminormedAddCommGroup
              (instMatrixInnerProductSpace (n := m)) (Φ x))
    _ = ‖Φ x‖ ^ 2 := by
          rw [Complex.ofReal_re]

end

end HiaiPetz.AmbientSubmodule

namespace HiaiPetz.AmbientSubmodule

section

open HiaiPetz Matrix Unitary
open scoped MatrixOrder ComplexOrder CStarAlgebra

/-- The trace quadratic form of `Φ ∘ hsAdjoint Φ` at `y` is the squared
Frobenius norm of `hsAdjoint Φ y`. -/
theorem hsQForm_comp_hsAdjoint_eq_norm_sq
    {n m : ℕ} (Φ : HSMap n m) (y : Mₙ m) :
    Complex.re (Matrix.trace (Matrix.conjTranspose y * ((Φ.comp (hsAdjoint Φ)) y))) =
      ‖hsAdjoint Φ y‖ ^ 2 := by
  calc
    Complex.re (Matrix.trace (Matrix.conjTranspose y * ((Φ.comp (hsAdjoint Φ)) y))) =
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose ((hsAdjoint Φ) y) *
              ((1 : HSOp n) ((hsAdjoint Φ) y)))) := by
            simpa using hsQForm_comp_hsAdjoint Φ (1 : HSOp n) y
    _ = Complex.re (inner ℂ ((1 : HSOp n) ((hsAdjoint Φ) y)) ((hsAdjoint Φ) y)) := by
          rw [hsQForm_real_eq_inner_real]
    _ = (↑(‖hsAdjoint Φ y‖ ^ 2) : ℂ).re := by
          -- `exact` bridges the (defeq) instance indices between the statement's
          -- norm and the unified `instMatrixInnerProductSpace` inner product.
          simp only [ContinuousLinearMap.one_apply, Complex.ofReal_pow]
          exact congrArg Complex.re
            (@inner_self_eq_norm_sq_to_K ℂ (Mₙ n) _
              (instMatrixNormedAddCommGroup (n := n)).toSeminormedAddCommGroup
              (instMatrixInnerProductSpace (n := n)) (hsAdjoint Φ y))
    _ = ‖hsAdjoint Φ y‖ ^ 2 := by
          rw [Complex.ofReal_re]

end

end HiaiPetz.AmbientSubmodule

namespace HiaiPetz.AmbientSubmodule

section

open HiaiPetz Matrix Unitary
open scoped MatrixOrder ComplexOrder CStarAlgebra

/-- The J-operator `hsCfcR f (jArg A B)` is self-adjoint for the Hilbert–Schmidt adjoint:
`hsAdjoint (hsCfcR f (jArg A B)) = hsCfcR f (jArg A B)`. -/
theorem cfcR_jArg_isSelfAdjoint
    (f : ℝ → ℝ)
    {n : ℕ} {A B : Mₙ n}
    (_hA : Matrix.PosDef A)
    (_hB : Matrix.PosDef B) :
    hsAdjoint (hsCfcR f (jArg A B)) = hsCfcR f (jArg A B) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  have hsa :
      IsSelfAdjoint (hsCfcR f (jArg A B)) := by
    simp
  simpa [hsAdjoint] using hsa.star_eq

end

end HiaiPetz.AmbientSubmodule

namespace HiaiPetz.AmbientSubmodule

section

open HiaiPetz Matrix Unitary
open scoped MatrixOrder ComplexOrder CStarAlgebra

/-- For `f` strictly positive on `(0, ∞)` and `A`, `B` positive definite, the J-operator
`hsCfcR f (jArg A B)` is nonnegative: `0 ≤ hsCfcR f (jArg A B)`. -/
theorem cfcR_jArg_nonneg
    (f : ℝ → ℝ)
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    {n : ℕ} {A B : Mₙ n}
    (hA : Matrix.PosDef A)
    (hB : Matrix.PosDef B) :
    0 ≤ hsCfcR f (jArg A B) := by
  refine cfc_nonneg (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint) (a := jArg A B) ?_
  intro x hx
  exact le_of_lt (hpos x (spectrum_jArg_subset_Ioi_of_posDef hA hB hx))

end

end HiaiPetz.AmbientSubmodule

namespace HiaiPetz.AmbientSubmodule

section

open HiaiPetz Matrix Unitary
open scoped MatrixOrder ComplexOrder CStarAlgebra

/-- For positive-definite `A`, `B`, the J-argument map `jArg A B : X ↦ A · X · B⁻¹` is a
unit in the endomorphism ring of `Mₙ n`, with inverse `X ↦ A⁻¹ · X · B`. -/
theorem jArg_isUnit {n : ℕ} {A B : Mₙ n}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    IsUnit (jArg A B) := by
  rcases hA.isUnit with ⟨uA, rfl⟩
  rcases hB.isUnit with ⟨uB, rfl⟩
  refine ⟨⟨jArg (↑uA : Mₙ n) (↑uB : Mₙ n),
      (rightMul (↑uB : Mₙ n)).comp (leftMul (↑(uA⁻¹) : Mₙ n)), ?_, ?_⟩, rfl⟩
  · ext X
    simp [jArg, leftMul_apply, rightMul_apply, Matrix.mul_assoc]
  · ext X
    simp [jArg, leftMul_apply, rightMul_apply, Matrix.mul_assoc]

end

end HiaiPetz.AmbientSubmodule

namespace HiaiPetz.AmbientSubmodule

section

open HiaiPetz Matrix Unitary
open scoped MatrixOrder ComplexOrder CStarAlgebra

/-- For positive-definite `A`, `B` and `f` continuous and strictly positive on `(0, ∞)`,
the real CFC of the reciprocal `x ↦ (f x)⁻¹` at `jArg A B` equals the ring inverse of
`hsCfcR f (jArg A B)`. -/
theorem cfcR_inv_eq_ringInverse_of_jArg_posDef
    (f : ℝ → ℝ)
    {n : ℕ} {A B : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (jArg A B) =
      Ring.inverse (hsCfcR f (jArg A B)) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  have hjArg_sa : IsSelfAdjoint (jArg A B) := by
    simpa [hsAdjoint] using jArg_isSelfAdjoint (A := A) (B := B) hA.1 hB
  have hcont_f : ContinuousOn f (spectrum ℝ (jArg A B)) := by
    exact hf.mono (spectrum_jArg_subset_Ioi_of_posDef hA hB)
  simpa [cfc_id' (R := ℝ) (a := jArg A B) (ha := hjArg_sa)] using
    (cfc_inv (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
      (f := f) (a := jArg A B)
      (fun x hx ↦ (hpos x (spectrum_jArg_subset_Ioi_of_posDef hA hB hx)).ne')
      (hf := hcont_f) (ha := hjArg_sa))

end

end HiaiPetz.AmbientSubmodule
