/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.KieferBound
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.KieferBoundRetained
import Quantum.TraceInequality.HansenPedersen.Core.Basic
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.RankOneBridge

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

/-- Right multiplication as a real `⋆`-algebra homomorphism out of the opposite matrix algebra. -/
noncomputable def rightMulMatrixStarAlgHom {n : ℕ} :
    (Mₙ n)ᵐᵒᵖ →⋆ₐ[ℝ] HSOp n where
  toFun := fun A => rightMul (MulOpposite.unop A)
  map_one' := by simp
  map_mul' := by
    intro A B
    ext X i j
    simp [Matrix.mul_assoc]
  map_zero' := by
    ext X i j
    simp
  map_add' := by
    intro A B
    ext X i j
    simp
  commutes' := by
    intro r
    have hunop :
        MulOpposite.unop ((algebraMap ℝ (Mₙ n)ᵐᵒᵖ) r) = r • (1 : Mₙ n) := by
      change MulOpposite.unop (MulOpposite.op ((algebraMap ℝ (Mₙ n)) r)) =
        r • (1 : Mₙ n)
      rw [MulOpposite.unop_op]
      exact Algebra.algebraMap_eq_smul_one r
    rw [hunop]
    change rightMul (r • (1 : Mₙ n)) = (algebraMap ℝ (HSOp n)) r
    rw [show (algebraMap ℝ (HSOp n)) r = r • (1 : HSOp n) from
      Algebra.algebraMap_eq_smul_one r]
    exact rightMul_real_smul_one (n := n) r
  map_star' := by
    intro A
    change rightMul (star (MulOpposite.unop A)) =
      star (rightMul (MulOpposite.unop A) : HSOp n)
    rw [rightMul_star]

@[simp] theorem rightMulMatrixStarAlgHom_apply {n : ℕ} (A : (Mₙ n)ᵐᵒᵖ) :
    rightMulMatrixStarAlgHom A = rightMul (MulOpposite.unop A) :=
  rfl

/-- Right multiplication as a complex `⋆`-algebra homomorphism out of the
opposite matrix algebra. -/
noncomputable def rightMulMatrixComplexStarAlgHom {n : ℕ} :
    (Mₙ n)ᵐᵒᵖ →⋆ₐ[ℂ] HSOp n where
  toFun := fun A => rightMul (MulOpposite.unop A)
  map_one' := by simp
  map_mul' := by
    intro A B
    ext X i j
    simp [Matrix.mul_assoc]
  map_zero' := by
    ext X i j
    simp
  map_add' := by
    intro A B
    ext X i j
    simp
  commutes' := by
    intro c
    have hunop :
        MulOpposite.unop ((algebraMap ℂ (Mₙ n)ᵐᵒᵖ) c) = c • (1 : Mₙ n) := by
      change MulOpposite.unop (MulOpposite.op ((algebraMap ℂ (Mₙ n)) c)) =
        c • (1 : Mₙ n)
      rw [MulOpposite.unop_op]
      exact Algebra.algebraMap_eq_smul_one c
    rw [hunop]
    change rightMul (c • (1 : Mₙ n)) = (algebraMap ℂ (HSOp n)) c
    rw [show (algebraMap ℂ (HSOp n)) c = c • (1 : HSOp n) from
      Algebra.algebraMap_eq_smul_one c]
    exact rightMul_complex_smul_one (n := n) c
  map_star' := by
    intro A
    change rightMul (star (MulOpposite.unop A)) =
      star (rightMul (MulOpposite.unop A) : HSOp n)
    rw [rightMul_star]

@[simp] theorem rightMulMatrixComplexStarAlgHom_apply {n : ℕ} (A : (Mₙ n)ᵐᵒᵖ) :
    rightMulMatrixComplexStarAlgHom A = rightMul (MulOpposite.unop A) :=
  rfl

private noncomputable def rightMulMatrixLinearMap {n : ℕ} :
    (Mₙ n)ᵐᵒᵖ →ₗ[ℝ] HSOp n where
  toFun := fun A => rightMul (MulOpposite.unop A)
  map_add' := by
    intro A B
    ext X i j
    simp
  map_smul' := by
    intro r A
    ext X i j
    change (∑ x, X i x * ((r : ℂ) * MulOpposite.unop A x j)) =
      (r : ℂ) * ∑ x, X i x * MulOpposite.unop A x j
    calc
      (∑ x, X i x * ((r : ℂ) * MulOpposite.unop A x j))
          = ∑ x, (r : ℂ) * (X i x * MulOpposite.unop A x j) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = (r : ℂ) * ∑ x, X i x * MulOpposite.unop A x j := by
            rw [Finset.mul_sum]

/--
Right multiplication intertwines the matrix functional calculus with the
Hilbert-Schmidt functional calculus: `rightMul (cfcR g A) = hsCfcR g
(rightMul A)` for a self-adjoint matrix `A` and `g` continuous on its
spectrum. This is the rank-one bridge between matrix-side and
operator-side CFC in Carlen's opmontI argument (Theorem 1.46 of
[carlen2022]).
-/
theorem rightMul_cfcR {n : ℕ} (g : ℝ → ℝ) (A : Mₙ n)
    (hA : IsSelfAdjoint A) (hg : ContinuousOn g (spectrum ℝ A)) :
    rightMul (LownerHeinzCore.cfcR (𝓐 := Mₙ n) g A) =
      hsCfcR g (rightMul A) := by
  let φ : (Mₙ n)ᵐᵒᵖ →⋆ₐ[ℂ] HSOp n := rightMulMatrixComplexStarAlgHom
  have hφ : Continuous φ := by
    letI : ContinuousLinearMapClass
        ((Mₙ n)ᵐᵒᵖ →⋆ₐ[ℂ] HSOp n) ℂ (Mₙ n)ᵐᵒᵖ (HSOp n) :=
      NonUnitalStarAlgHom.instContinuousLinearMapClassComplex
    exact map_continuous φ
  have hopA : IsSelfAdjoint (MulOpposite.op A : (Mₙ n)ᵐᵒᵖ) :=
    opMatrix_isSelfAdjoint A hA
  have hφA : IsSelfAdjoint (φ (MulOpposite.op A)) := hopA.map φ
  have hmap := StarAlgHom.map_cfc (R := ℝ) (S := ℂ)
    (φ := φ) (f := g) (a := MulOpposite.op A)
    (hf := by simpa [matrix_spectrum_op_eq A hA] using hg)
    (hφ := hφ) (ha := hopA) (hφa := hφA)
  have hopcfc :
      cfc (R := ℝ) (A := (Mₙ n)ᵐᵒᵖ) (p := IsSelfAdjoint) g
          (MulOpposite.op A) =
        MulOpposite.op (LownerHeinzCore.cfcR (𝓐 := Mₙ n) g A) :=
    matrix_cfc_op_eq_op_cfc g A hA hg
  simpa [φ, hsCfcR, rightMulMatrixComplexStarAlgHom, hopcfc] using hmap

/--
The Hilbert-Schmidt CFC of right multiplication by `X` is right multiplication
by the positive-ray matrix CFC of `1 / f`. This is the right-multiplication
CFC model used in Carlen's opmontI route [carlen2022].
-/
theorem hsCfcR_rightMul_eq_rightMul_positiveRayMatrixCfc {n : ℕ}
    {f : ℝ → ℝ} (hf : CarlenOpMontIFunctionHypothesis f)
    {X : Mₙ n} (hX : MatrixPosDef X) :
    hsCfcR (fun x : ℝ => (f x)⁻¹) (rightMul X) =
      rightMul (positiveRayMatrixCfc (fun x : ℝ => (f x)⁻¹) n X) := by
  have hXpos : X.PosDef := matrixPosDef_posDef hX
  have hspec : spectrum ℝ X ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    obtain ⟨i, rfl⟩ :=
      Set.ext_iff.mp hX.1.isHermitian.spectrum_real_eq_range_eigenvalues x |>.mp hx
    exact hXpos.eigenvalues_pos i
  have hcont :
      ContinuousOn (fun x : ℝ => (f x)⁻¹) (spectrum ℝ X) := by
    exact (hf.1.mono hspec).inv₀ (by
      intro x hx
      exact ne_of_gt (hf.2 (hspec hx)))
  have hcfc := rightMul_cfcR (n := n)
    (g := fun x : ℝ => (f x)⁻¹) X hX.1 hcont
  have hpositiveRay :
      positiveRayMatrixCfc (fun x : ℝ => (f x)⁻¹) n X =
        LownerHeinzCore.cfcR (𝓐 := Mₙ n) (fun x : ℝ => (f x)⁻¹) X :=
    positiveRayMatrixCfc_eq_cfcR_of_isHermitian X hX.1.isHermitian
  rw [hpositiveRay]
  exact hcfc.symm

/--
The packaged right-multiplication CFC model follows from the matrix/opposite
algebra bridge. This supplies the rank-one side of Carlen's opmontI argument
[carlen2022].
-/
theorem carlenOpMontIRightMulCfcModel {f : ℝ → ℝ}
    (hf : CarlenOpMontIFunctionHypothesis f) :
    CarlenOpMontIRightMulCfcModel f := by
  intro n X hX
  exact hsCfcR_rightMul_eq_rightMul_positiveRayMatrixCfc hf hX

/-- At `Y = I`, Carlen's `G_f` CFC argument is just right multiplication by `X`. -/
theorem gArg_one_eq_rightMul {n : ℕ} (X : Mₙ n) :
    gArg X (1 : Mₙ n) = rightMul X := by
  ext Z i j
  simp [gArg, posInv, ContinuousLinearMap.comp_apply]

/--
With `Y = I`, the endpoint factor in `G_f^{-1}` is the identity, so the inverse
perspective operator is the reciprocal CFC of right multiplication by `X`.
-/
theorem gOperatorInv_one_eq_hsCfcR_rightMul {n : ℕ} {f : ℝ → ℝ}
    (X : Mₙ n) :
    gOperatorInv f X (1 : Mₙ n) =
      hsCfcR (fun x : ℝ => (f x)⁻¹) (rightMul X) := by
  rw [gOperatorInv, gArg_one_eq_rightMul]
  have hleft : leftMul (posInv (1 : Mₙ n)) = (1 : HSOp n) := by
    ext Z i j
    change ((posInv (1 : Mₙ n)) * Z) i j = Z i j
    simp [posInv]
  rw [hleft, mul_one]

/--
The CFC naturality component and the rank-one trace component together produce
the rank-one model required by the `Y = I` specialization.
-/
theorem reciprocal_rankOneModel_of_rightMulCfc_of_traceModel
    {f : ℝ → ℝ}
    (hcfc : CarlenOpMontIRightMulCfcModel f)
    (htrace : CarlenOpMontIRankOneTraceModel) :
    CarlenOpMontIReciprocalRankOneModel f := by
  intro n
  rcases htrace n with ⟨R, hR_conv, hR_qform⟩
  refine ⟨R, hR_conv, ?_⟩
  intro X hX v
  rw [gInvQF, gOperatorInv_one_eq_hsCfcR_rightMul, hcfc hX]
  exact hR_qform (positiveRayMatrixCfc (fun x : ℝ => (f x)⁻¹) n X) v

/--
Condition (4) gives AH1 reciprocal quadratic-form convexity.  The rank-one
model is supplied internally by the right-multiplication CFC naturality and the
fixed-row rank-one trace computation.
-/
theorem reciprocal_qformJointConvex_of_condition4
    {f : ℝ → ℝ}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (h4 : CarlenOpMontICondition4 f) :
    CarlenOpMontIReciprocalQFormJointConvex f :=
  reciprocal_qformJointConvex_of_condition4_of_rankOneModel h4
    (reciprocal_rankOneModel_of_rightMulCfc_of_traceModel
      (carlenOpMontIRightMulCfcModel hf)
      carlenOpMontIRankOneTraceModel)

/--
Once the reciprocal AH1 vector quadratic form is jointly convex, AH1 gives
operator monotone decreasing for `1/f`, and reciprocal transport gives
condition (1) for `f`.
-/
theorem condition1_of_reciprocal_qformJointConvex {f : ℝ → ℝ}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hjoint : CarlenOpMontIReciprocalQFormJointConvex f) :
    CarlenOpMontICondition1 f := by
  have hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ (f x)⁻¹ := by
    intro x hx
    have hfx : 0 < f x := hf.2 (by simpa using hx)
    exact inv_nonneg.mpr (le_of_lt hfx)
  have hg :
      OperatorMonotoneDecreasingOnPositive (fun x : ℝ => (f x)⁻¹) :=
    _root_.Quantum.TraceInequality.Loewner.operatorMonotoneDecreasingOnPositive_of_qformJointConvex
      (g := fun x : ℝ => (f x)⁻¹) hjoint hnonneg
  exact
    _root_.Quantum.TraceInequality.Loewner.operatorMonotoneOnPositive_of_reciprocal_decreasing
      (f := f) (g := fun x : ℝ => (f x)⁻¹)
      (fun x hx => hf.2 hx)
      (fun _ _ => rfl)
      hg

/--
Condition (4) implies condition (1) by first passing to the AH1 reciprocal
quadratic-form convexity and then transporting reciprocal operator-monotone
decreasingness back to operator monotonicity of `f`.
-/
theorem condition4_to_condition1 {f : ℝ → ℝ}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (h4 : CarlenOpMontICondition4 f) :
    CarlenOpMontICondition1 f :=
  condition1_of_reciprocal_qformJointConvex hf
    (reciprocal_qformJointConvex_of_condition4 hf h4)

/-! ### Weighted-block reduction gates -/
/--
Condition (2) gives condition (4) once the weighted-block quadratic-form
estimate is available for interior weights.  For Carlen's functions this
estimate is established in the proof of `condition2_to_condition4_of_carlenFunction`
(`CFCTransport.lean`).
-/
theorem condition2_to_condition4_of_weightedBlockDiag_gInvQF_bound {f : ℝ → ℝ}
    (h2 : CarlenOpMontICondition2 f)
    (hblock :
      ∀ {n : ℕ} {θ : ℝ} {X₀ X₁ Y₀ Y₁ Z₀ Z₁ : Mₙ n},
        MatrixPosDef X₀ →
        MatrixPosDef X₁ →
        MatrixPosDef Y₀ →
        MatrixPosDef Y₁ →
        0 < θ →
        θ < 1 →
        hsQF
          (gOperatorInv f (weightedBlockDiag θ X₀ X₁)
            (weightedBlockDiag θ Y₀ Y₁))
          (weightedBlockDiag θ Z₀ Z₁)
          ≤
          θ * gInvQF f X₀ Y₀ Z₀ + (1 - θ) * gInvQF f X₁ Y₁ Z₁) :
    CarlenOpMontICondition4 f := by
  intro n X₀ X₁ Y₀ Y₁ Z₀ Z₁ θ hX₀ hX₁ hY₀ hY₁ hθ0 hθ1
  by_cases hθ_zero : θ = 0
  · subst θ
    simp [matrixConvexCombo]
  by_cases hθ_one : θ = 1
  · subst θ
    simp [matrixConvexCombo]
  have hθpos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθ_zero)
  have hθlt : θ < 1 := lt_of_le_of_ne hθ1 hθ_one
  exact
    (condition2_weightedBlockDiag_gInvQF_le
      (f := f) h2 hθpos hθlt hX₀ hX₁ hY₀ hY₁).trans
      (hblock
        (n := n) (θ := θ)
        (X₀ := X₀) (X₁ := X₁) (Y₀ := Y₀) (Y₁ := Y₁)
        (Z₀ := Z₀) (Z₁ := Z₁)
        hX₀ hX₁ hY₀ hY₁ hθpos hθlt)

/--
Condition (2) gives condition (4) once the blockwise action of `G_f⁻¹` on
weighted block inputs is supplied.  For Carlen's functions the implication is
`condition2_to_condition4_of_carlenFunction` (`CFCTransport.lean`).
-/
theorem condition2_to_condition4_of_weightedBlockDiag_gOperatorInv_apply {f : ℝ → ℝ}
    (h2 : CarlenOpMontICondition2 f)
    (happly :
      ∀ {n : ℕ} {θ : ℝ} {X₀ X₁ Y₀ Y₁ Z₀ Z₁ : Mₙ n},
        MatrixPosDef X₀ →
        MatrixPosDef X₁ →
        MatrixPosDef Y₀ →
        MatrixPosDef Y₁ →
        0 < θ →
        θ < 1 →
        gOperatorInv f (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁)
            (weightedBlockDiag θ Z₀ Z₁) =
          twoBlockReindex (n := n)
            (Matrix.fromBlocks
              (gOperatorInv f X₀ Y₀ Z₀) 0 0 (gOperatorInv f X₁ Y₁ Z₁))) :
    CarlenOpMontICondition4 f :=
  condition2_to_condition4_of_weightedBlockDiag_gInvQF_bound h2
    (by
      intro n θ X₀ X₁ Y₀ Y₁ Z₀ Z₁ hX₀ hX₁ hY₀ hY₁ hθ0 hθ1
      exact le_of_eq
        (weightedBlockDiag_gInvQF_eq_of_gOperatorInv_apply
          (f := f)
          (happly hX₀ hX₁ hY₀ hY₁ hθ0 hθ1)))

/--
Condition (2) gives condition (4) once the CFC factor of `G_f⁻¹` acts
blockwise on the weighted block input after the inverse-left-multiplication
normalization.
-/
theorem condition2_to_condition4_of_weightedBlockDiag_hsCfcR_gArg_apply {f : ℝ → ℝ}
    (h2 : CarlenOpMontICondition2 f)
    (hcfc :
      ∀ {n : ℕ} {θ : ℝ} {X₀ X₁ Y₀ Y₁ Z₀ Z₁ : Mₙ n},
        MatrixPosDef X₀ →
        MatrixPosDef X₁ →
        MatrixPosDef Y₀ →
        MatrixPosDef Y₁ →
        0 < θ →
        θ < 1 →
        hsCfcR (fun x : ℝ ↦ (f x)⁻¹)
            (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
            (twoBlockReindex (n := n)
              (Matrix.fromBlocks (posInv Y₀ * Z₀) 0 0 (posInv Y₁ * Z₁))) =
          twoBlockReindex (n := n)
            (Matrix.fromBlocks
              (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (gArg X₀ Y₀) (posInv Y₀ * Z₀))
              0 0
              (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (gArg X₁ Y₁) (posInv Y₁ * Z₁)))) :
    CarlenOpMontICondition4 f :=
  condition2_to_condition4_of_weightedBlockDiag_gOperatorInv_apply h2
    (by
      intro n θ X₀ X₁ Y₀ Y₁ Z₀ Z₁ hX₀ hX₁ hY₀ hY₁ hθ0 hθ1
      exact
        weightedBlockDiag_gOperatorInv_apply_of_hsCfcR_gArg_apply
          (f := f) hY₀ hY₁ hθ0 hθ1
          (hcfc hX₀ hX₁ hY₀ hY₁ hθ0 hθ1))

/--
Condition (2) gives condition (4) once the two diagonal blocks of the CFC
output are identified with the two smaller CFC outputs. The off-diagonal
blocks are already killed by the diagonal-subspace invariance theorem.
-/
theorem condition2_to_condition4_of_weightedBlockDiag_hsCfcR_gArg_diagonal_blocks
    {f : ℝ → ℝ}
    (h2 : CarlenOpMontICondition2 f)
    (hdiag :
      ∀ {n : ℕ} {θ : ℝ} {X₀ X₁ Y₀ Y₁ Z₀ Z₁ : Mₙ n},
        MatrixPosDef X₀ →
        MatrixPosDef X₁ →
        MatrixPosDef Y₀ →
        MatrixPosDef Y₁ →
        0 < θ →
        θ < 1 →
        (((twoBlockReindex (n := n)).symm
          (hsCfcR (fun x : ℝ ↦ (f x)⁻¹)
            (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
            (twoBlockReindex (n := n)
              (Matrix.fromBlocks (posInv Y₀ * Z₀) 0 0 (posInv Y₁ * Z₁))))).toBlocks₁₁ =
            hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (gArg X₀ Y₀) (posInv Y₀ * Z₀)) ∧
          (((twoBlockReindex (n := n)).symm
            (hsCfcR (fun x : ℝ ↦ (f x)⁻¹)
              (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
              (twoBlockReindex (n := n)
                (Matrix.fromBlocks (posInv Y₀ * Z₀) 0 0 (posInv Y₁ * Z₁))))).toBlocks₂₂ =
            hsCfcR (fun x : ℝ ↦ (f x)⁻¹) (gArg X₁ Y₁) (posInv Y₁ * Z₁))) :
    CarlenOpMontICondition4 f :=
  condition2_to_condition4_of_weightedBlockDiag_hsCfcR_gArg_apply h2
    (by
      intro n θ X₀ X₁ Y₀ Y₁ Z₀ Z₁ hX₀ hX₁ hY₀ hY₁ hθ0 hθ1
      exact
        hsCfcR_weightedBlockDiag_gArg_apply_fromBlocks_of_diagonal_blocks
          (n := n) (θ := θ) (X₀ := X₀) (X₁ := X₁) (Y₀ := Y₀) (Y₁ := Y₁)
          (V₀ := posInv Y₀ * Z₀) (V₁ := posInv Y₁ * Z₁)
          (fun x : ℝ ↦ (f x)⁻¹) hY₀ hY₁ hθ0 hθ1
          (hdiag hX₀ hX₁ hY₀ hY₁ hθ0 hθ1).1
          (hdiag hX₀ hX₁ hY₀ hY₁ hθ0 hθ1).2)

end

end Quantum.TraceInequality.Loewner.HiaiPetz
