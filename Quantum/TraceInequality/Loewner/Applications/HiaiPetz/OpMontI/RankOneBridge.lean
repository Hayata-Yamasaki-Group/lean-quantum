/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.KieferBound
import Quantum.TraceInequality.HiaiPetzTheorem.Core.Basic

/-!
# Carlen's `opmontI` conditions: right multiplication and rank-one bridge

This module contains the right-multiplication CFC transport, the rank-one trace
bridge from condition (4) to condition (1), and the weighted-block gate stage
for Carlen 2022 Theorem 1.46.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder FinMatrixCStar

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace
  instOpMontIBaseHSOpCStarAlgebra
  instOpMontIBaseHSOpComplexAlgebra
  instOpMontIBaseMatrixRealModule
  instOpMontIBaseMatrixRealScalarTower
  instOpMontIBaseMatrixRealNormedSpace
  instOpMontIBaseMatrixRealFiniteDimensional
  instOpMontIBaseHSOpRealAlgebra
  instOpMontIBaseHSOpStarRing
  instOpMontIBaseHSOpPartialOrder
  instOpMontIBaseHSOpStarOrderedRing
  instOpMontIBaseHSOpNonnegSpectrumClass
  instOpMontIBaseHSOpRealCFC
  instOpMontIBaseMatrixOppRealCFC
  instOpMontIBaseHSOpProdCStarAlgebra
  instOpMontIBaseHSOpProdRealCFC
  instOpMontIBaseHSOpProdProdCStarAlgebra
  instOpMontIBaseHSOpProdProdRealCFC

noncomputable section

/-! ### Right multiplication CFC transport -/
@[simp] theorem rightMul_star {n : ℕ} (B : Mₙ n) :
    star (rightMul B : HSOp n) = rightMul (star B) := by
  rw [eq_comm]
  change rightMul (star B) =
    @ContinuousLinearMap.adjoint ℂ (Mₙ n) (Mₙ n)
      _ (instMatrixNormedAddCommGroup (n := n)) (instMatrixNormedAddCommGroup (n := n))
      (instMatrixInnerProductSpace (n := n)) (instMatrixInnerProductSpace (n := n))
      (instMatrixCompleteSpace (n := n)) (instMatrixCompleteSpace (n := n))
      (show Mₙ n →L[ℂ] Mₙ n from rightMul B)
  refine (@ContinuousLinearMap.eq_adjoint_iff ℂ (Mₙ n) (Mₙ n)
    _ (instMatrixNormedAddCommGroup (n := n)) (instMatrixNormedAddCommGroup (n := n))
    (instMatrixInnerProductSpace (n := n)) (instMatrixInnerProductSpace (n := n))
    (instMatrixCompleteSpace (n := n)) (instMatrixCompleteSpace (n := n))
    (rightMul (star B)) (show Mₙ n →L[ℂ] Mₙ n from rightMul B)).2 ?_
  intro X Y
  calc
    @inner ℂ (Mₙ n) inferInstance ((rightMul (star B)) X) Y
        = Matrix.trace (Y * Matrix.conjTranspose (X * star B)) := rfl
    _ = Matrix.trace (Y * (B * Matrix.conjTranspose X)) := by
          have hstarB : Matrix.conjTranspose (star B) = B := by
            change Matrix.conjTranspose (Matrix.conjTranspose B) = B
            rw [Matrix.conjTranspose_conjTranspose]
          rw [Matrix.conjTranspose_mul]
          rw [hstarB]
    _ = Matrix.trace ((Y * B) * Matrix.conjTranspose X) := by
          rw [Matrix.mul_assoc]
    _ = @inner ℂ (Mₙ n) inferInstance X ((rightMul B) Y) := rfl

@[simp] theorem rightMul_one {n : ℕ} :
    rightMul (1 : Mₙ n) = (1 : HSOp n) := by
  ext X i j
  simp

@[simp] theorem rightMul_real_smul_one {n : ℕ} (r : ℝ) :
    rightMul (r • (1 : Mₙ n)) = r • (1 : HSOp n) := by
  ext X i j
  change (∑ x, X i x * ((r : ℂ) * (1 : Mₙ n) x j)) = (r : ℂ) * X i j
  calc
    (∑ x, X i x * ((r : ℂ) * (1 : Mₙ n) x j))
        = ∑ x, (X i x * (1 : Mₙ n) x j) * (r : ℂ) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ = (∑ x, X i x * (1 : Mₙ n) x j) * (r : ℂ) := by
          rw [Finset.sum_mul]
    _ = X i j * (r : ℂ) := by
          have hsum : (∑ x, X i x * (1 : Mₙ n) x j) = X i j := by
            simpa [Matrix.mul_apply] using congrFun₂ (Matrix.mul_one X) i j
          rw [hsum]
    _ = (r : ℂ) * X i j := by
          ring

@[simp] theorem rightMul_complex_smul_one {n : ℕ} (c : ℂ) :
    rightMul (c • (1 : Mₙ n)) = c • (1 : HSOp n) := by
  ext X i j
  change (∑ x, X i x * (c * (1 : Mₙ n) x j)) = c * X i j
  calc
    (∑ x, X i x * (c * (1 : Mₙ n) x j))
        = ∑ x, c * (X i x * (1 : Mₙ n) x j) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ = c * (∑ x, X i x * (1 : Mₙ n) x j) := by
          rw [Finset.mul_sum]
    _ = c * X i j := by
          have hsum : (∑ x, X i x * (1 : Mₙ n) x j) = X i j := by
            simpa [Matrix.mul_apply] using congrFun₂ (Matrix.mul_one X) i j
          rw [hsum]

private noncomputable def opStarMatrixStarAlgHom {n : ℕ} :
    Mₙ n →⋆ₐ[ℝ] (Mₙ n)ᵐᵒᵖ where
  toFun A := MulOpposite.op (star A)
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

private noncomputable def opStarMatrixAlgEquiv {n : ℕ} :
    Mₙ n ≃ₐ[ℝ] (Mₙ n)ᵐᵒᵖ where
  toFun A := MulOpposite.op (star A)
  invFun A := star (MulOpposite.unop A)
  left_inv A := by simp
  right_inv A := by simp
  map_mul' A B := by simp [star_mul]
  map_add' A B := by simp
  commutes' r := by
    apply congrArg MulOpposite.op
    simp [Algebra.algebraMap_eq_smul_one]

/-- A self-adjoint matrix remains self-adjoint after passing to the opposite algebra. -/
lemma opMatrix_isSelfAdjoint {n : ℕ} (A : Mₙ n) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (MulOpposite.op A : (Mₙ n)ᵐᵒᵖ) := by
  exact congrArg MulOpposite.op hA.star_eq

/-- The real spectrum of a self-adjoint matrix is unchanged in the opposite algebra. -/
lemma matrix_spectrum_op_eq {n : ℕ} (A : Mₙ n) (hA : IsSelfAdjoint A) :
    spectrum ℝ (MulOpposite.op A : (Mₙ n)ᵐᵒᵖ) = spectrum ℝ A := by
  have hopA : IsSelfAdjoint (MulOpposite.op A : (Mₙ n)ᵐᵒᵖ) :=
    opMatrix_isSelfAdjoint A hA
  simpa [opStarMatrixAlgEquiv, hA.star_eq, hopA.star_eq] using
    (AlgEquiv.spectrum_eq (opStarMatrixAlgEquiv (n := n)) A)

/--
Functional calculus in the opposite algebra is the opposite of matrix
functional calculus for a self-adjoint matrix.
-/
lemma matrix_cfc_op_eq_op_cfc {n : ℕ} (g : ℝ → ℝ) (A : Mₙ n)
    (hA : IsSelfAdjoint A) (hg : ContinuousOn g (spectrum ℝ A)) :
    cfc (R := ℝ) (A := (Mₙ n)ᵐᵒᵖ) (p := IsSelfAdjoint) g
        (MulOpposite.op A) =
      MulOpposite.op (LownerHeinzCore.cfcR (𝓐 := Mₙ n) g A) := by
  let φ : Mₙ n →⋆ₐ[ℝ] (Mₙ n)ᵐᵒᵖ := opStarMatrixStarAlgHom
  have hφ : Continuous φ := by
    change Continuous (fun A : Mₙ n => MulOpposite.op (star A))
    exact MulOpposite.continuous_op.comp continuous_star
  have hopA : IsSelfAdjoint (MulOpposite.op A : (Mₙ n)ᵐᵒᵖ) :=
    opMatrix_isSelfAdjoint A hA
  have hφA : IsSelfAdjoint (φ A) := hA.map φ
  have hcfcA :
      IsSelfAdjoint
        (cfc (R := ℝ) (A := Mₙ n) (p := IsSelfAdjoint) g A) := by
    simp [IsSelfAdjoint.cfc (f := g) (a := A)]
  have hopcfcA :
      IsSelfAdjoint
        (MulOpposite.op
          (cfc (R := ℝ) (A := Mₙ n) (p := IsSelfAdjoint) g A) : (Mₙ n)ᵐᵒᵖ) :=
    opMatrix_isSelfAdjoint
      (cfc (R := ℝ) (A := Mₙ n) (p := IsSelfAdjoint) g A) hcfcA
  have hmap := StarAlgHom.map_cfc (φ := φ) (f := g) (a := A)
    (hf := hg) (hφ := hφ) (ha := hA) (hφa := hφA)
  simpa [φ, opStarMatrixStarAlgHom, LownerHeinzCore.cfcR, hA.star_eq,
    hopA.star_eq, hcfcA.star_eq, hopcfcA.star_eq] using hmap.symm

/-! ### Rank-one trace bridge and condition (4) to condition (1) -/
/--
The rank-one trace component of the `Y = I` bridge.  It supplies a linear
square-matrix representative `R v` whose Hilbert--Schmidt right-multiplication
quadratic form is the AH1 vector quadratic form.
-/
def CarlenOpMontIRankOneTraceModel : Prop :=
  ∀ n : ℕ, ∃ R : (Fin n → ℂ) → Mₙ n,
    (∀ (θ : ℝ) (v w : Fin n → ℂ),
      R (positiveRayVectorConvexCombo θ v w) =
        matrixConvexCombo θ (R v) (R w)) ∧
    ∀ (A : Mₙ n) (v : Fin n → ℂ),
      hsQF (rightMul A) (R v) = positiveRayQForm A v

/-- A square rank-one representative of a vector, placed in a fixed row. -/
noncomputable def rankOneRowMatrix {n : ℕ} (i₀ : Fin n) (v : Fin n → ℂ) :
    Mₙ n :=
  fun i j => if i = i₀ then star (v j) else 0

/-- The fixed-row rank-one representative is linear for real convex combinations. -/
theorem rankOneRowMatrix_convexCombo {n : ℕ} (i₀ : Fin n)
    (θ : ℝ) (v w : Fin n → ℂ) :
    rankOneRowMatrix i₀ (positiveRayVectorConvexCombo θ v w) =
      matrixConvexCombo θ (rankOneRowMatrix i₀ v) (rankOneRowMatrix i₀ w) := by
  ext i j
  by_cases hi : i = i₀
  · subst i
    simp only [rankOneRowMatrix, positiveRayVectorConvexCombo, matrixConvexCombo,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ↓reduceIte]
    change star ((θ : ℂ) * v j + ((1 - θ : ℝ) : ℂ) * w j) =
      (θ : ℂ) * star (v j) + ((1 - θ : ℝ) : ℂ) * star (w j)
    simp [star_add, star_mul]
    ring_nf
  · simp only [rankOneRowMatrix, matrixConvexCombo, Matrix.add_apply,
      Matrix.smul_apply, hi, if_false, smul_eq_mul, mul_zero, add_zero]

/-- The Hilbert--Schmidt right-multiplication quadratic form of the fixed-row
rank-one representative is the vector quadratic form. -/
theorem hsQF_rightMul_rankOneRowMatrix {n : ℕ} (i₀ : Fin n)
    (A : Mₙ n) (v : Fin n → ℂ) :
    hsQF (rightMul A) (rankOneRowMatrix i₀ v) =
      positiveRayQForm A v := by
  classical
  unfold hsQF positiveRayQForm
  change Complex.re
      (Matrix.trace
        (Matrix.conjTranspose (rankOneRowMatrix i₀ v) *
          (rankOneRowMatrix i₀ v * A))) =
    Complex.re (dotProduct (star v) (A.mulVec v))
  congr 1
  simp only [Matrix.trace, Matrix.conjTranspose, RCLike.star_def, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, rankOneRowMatrix, ite_mul,
    zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, mul_ite, Finset.mul_sum,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, RingHomCompTriple.comp_apply,
    RingHom.id_apply, dotProduct, Pi.star_apply, Matrix.mulVec]
  rw [Finset.sum_comm]
  simp [mul_assoc, mul_comm, mul_left_comm]

/-- The rank-one trace component is supplied by a fixed-row representative. -/
theorem carlenOpMontIRankOneTraceModel :
    CarlenOpMontIRankOneTraceModel := by
  intro n
  cases n with
  | zero =>
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro θ v w
        ext i
        exact Fin.elim0 i
      · intro A v
        simp [hsQF, positiveRayQForm, rightMul]
  | succ m =>
      let i₀ : Fin (Nat.succ m) := 0
      refine ⟨rankOneRowMatrix i₀, ?_, ?_⟩
      · intro θ v w
        exact rankOneRowMatrix_convexCombo i₀ θ v w
      · intro A v
        exact hsQF_rightMul_rankOneRowMatrix i₀ A v

/--
The only further ingredient after specializing condition (4) to `Y = I` is
the rank-one model identifying Carlen's square-matrix quadratic form with AH1's
vector quadratic form; it is supplied in `reciprocal_qformJointConvex_of_condition4`
below.
-/
theorem reciprocal_qformJointConvex_of_condition4YOne_of_rankOneModel
    {f : ℝ → ℝ}
    (h4 : CarlenOpMontICondition4YOne f)
    (hmodel : CarlenOpMontIReciprocalRankOneModel f) :
    CarlenOpMontIReciprocalQFormJointConvex f := by
  intro n X Y v w θ hX hY hθ0 hθ1
  rcases hmodel n with ⟨R, hR_conv, hR_qform⟩
  have hX' : MatrixPosDef X := matrixPosDef_of_posDef hX
  have hY' : MatrixPosDef Y := matrixPosDef_of_posDef hY
  have hcombo' :
      MatrixPosDef (matrixConvexCombo θ X Y) :=
    matrixPosDef_matrixConvexCombo hX' hY' hθ0 hθ1
  have hcondition := h4 (X₀ := X) (X₁ := Y)
    (Z₀ := R v) (Z₁ := R w) (θ := θ) hX' hY' hθ0 hθ1
  have hcomboZ :
      matrixConvexCombo θ (R v) (R w) =
        R (positiveRayVectorConvexCombo θ v w) :=
    (hR_conv θ v w).symm
  rw [hcomboZ] at hcondition
  have hleft := hR_qform hcombo' (positiveRayVectorConvexCombo θ v w)
  have hrightX := hR_qform hX' v
  have hrightY := hR_qform hY' w
  rw [hleft, hrightX, hrightY] at hcondition
  simpa [CarlenOpMontIReciprocalQFormJointConvex,
    positiveRayMatrixConvexCombo, matrixConvexCombo] using hcondition

/--
Condition (4) itself gives the AH1 reciprocal quadratic-form convexity once the
rank-one realization of the `Y = I` quadratic form has been supplied.
-/
theorem reciprocal_qformJointConvex_of_condition4_of_rankOneModel
    {f : ℝ → ℝ}
    (h4 : CarlenOpMontICondition4 f)
    (hmodel : CarlenOpMontIReciprocalRankOneModel f) :
    CarlenOpMontIReciprocalQFormJointConvex f :=
  reciprocal_qformJointConvex_of_condition4YOne_of_rankOneModel
    (condition4_rank_one_specialization h4) hmodel

/--
If `G_f⁻¹` on the weighted block input acts blockwise on weighted block
vectors, then the weighted-block quadratic-form estimate of
`condition2_to_condition4_of_weightedBlockDiag_gInvQF_bound` is an ordinary trace
calculation.
-/
theorem weightedBlockDiag_gInvQF_eq_of_gOperatorInv_apply {n : ℕ} {f : ℝ → ℝ}
    {θ : ℝ} {X₀ X₁ Y₀ Y₁ Z₀ Z₁ : Mₙ n}
    (happly :
      gOperatorInv f (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁)
          (weightedBlockDiag θ Z₀ Z₁) =
        twoBlockReindex (n := n)
          (Matrix.fromBlocks
            (gOperatorInv f X₀ Y₀ Z₀) 0 0 (gOperatorInv f X₁ Y₁ Z₁))) :
    hsQF
        (gOperatorInv f (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
        (weightedBlockDiag θ Z₀ Z₁) =
      θ * gInvQF f X₀ Y₀ Z₀ + (1 - θ) * gInvQF f X₁ Y₁ Z₁ := by
  simpa [hsQF, gInvQF, happly] using
    hsQF_weightedBlockDiag_fromBlocks
      (n := n) θ
      (gOperatorInv f X₀ Y₀ Z₀)
      (gOperatorInv f X₁ Y₁ Z₁)
      Z₀ Z₁

/--
The blockwise action of the CFC factor of `G_f⁻¹`, together with the inverse
left-multiplication calculation for weighted blocks, gives the blockwise
action of the whole `G_f⁻¹`.
-/
theorem weightedBlockDiag_gOperatorInv_apply_of_hsCfcR_gArg_apply {n : ℕ}
    {f : ℝ → ℝ} {θ : ℝ} {X₀ X₁ Y₀ Y₁ Z₀ Z₁ : Mₙ n}
    (hY₀ : MatrixPosDef Y₀) (hY₁ : MatrixPosDef Y₁)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hcfc :
      hsCfcR (fun x : ℝ ↦ (f x)⁻¹)
          (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
          (twoBlockReindex (n := n)
            (Matrix.fromBlocks (posInv Y₀ * Z₀) 0 0 (posInv Y₁ * Z₁))) =
        twoBlockReindex (n := n)
          (Matrix.fromBlocks
            (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (gArg X₀ Y₀) (posInv Y₀ * Z₀))
            0 0
            (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (gArg X₁ Y₁) (posInv Y₁ * Z₁)))) :
    gOperatorInv f (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁)
        (weightedBlockDiag θ Z₀ Z₁) =
      twoBlockReindex (n := n)
        (Matrix.fromBlocks
          (gOperatorInv f X₀ Y₀ Z₀) 0 0 (gOperatorInv f X₁ Y₁ Z₁)) := by
  have hleft :
      (leftMul (posInv (weightedBlockDiag θ Y₀ Y₁)) : HSOp (n + n))
          (weightedBlockDiag θ Z₀ Z₁) =
        twoBlockReindex (n := n)
          (Matrix.fromBlocks (posInv Y₀ * Z₀) 0 0 (posInv Y₁ * Z₁)) :=
    leftMul_posInv_weightedBlockDiag_apply_weightedBlockDiag
      (n := n) (θ := θ) hY₀ hY₁ hθ0 hθ1
  calc
    gOperatorInv f (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁)
        (weightedBlockDiag θ Z₀ Z₁)
        =
      hsCfcR (fun x : ℝ ↦ (f x)⁻¹)
          (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
          ((leftMul (posInv (weightedBlockDiag θ Y₀ Y₁)) : HSOp (n + n))
            (weightedBlockDiag θ Z₀ Z₁)) := by
        simp [gOperatorInv, ContinuousLinearMap.mul_apply]
    _ =
      hsCfcR (fun x : ℝ ↦ (f x)⁻¹)
          (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
          (twoBlockReindex (n := n)
            (Matrix.fromBlocks (posInv Y₀ * Z₀) 0 0 (posInv Y₁ * Z₁))) := by
        rw [hleft]
    _ =
      twoBlockReindex (n := n)
        (Matrix.fromBlocks
          (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (gArg X₀ Y₀) (posInv Y₀ * Z₀))
          0 0
          (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (gArg X₁ Y₁) (posInv Y₁ * Z₁))) := hcfc
    _ =
      twoBlockReindex (n := n)
        (Matrix.fromBlocks
          (gOperatorInv f X₀ Y₀ Z₀) 0 0 (gOperatorInv f X₁ Y₁ Z₁)) := by
        simp only [gOperatorInv, ContinuousLinearMap.mul_apply]
        rw [show (leftMul (posInv Y₀) : HSOp n) Z₀ = posInv Y₀ * Z₀ by rfl]
        rw [show (leftMul (posInv Y₁) : HSOp n) Z₁ = posInv Y₁ * Z₁ by rfl]

end

end Quantum.TraceInequality.Loewner.HiaiPetz
