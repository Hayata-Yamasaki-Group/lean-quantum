/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.RankOneBridgeRetained
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.CFCTransport
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.ConditionsRetained

/-!
# Carlen's `opmontI` conditions: CFC transport to condition (4)

This module contains the CFC restriction and direct-sum transport stage,
together with the final condition (2) to condition (4) implication in
Carlen 2022 Theorem 1.46.
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

/--
Condition (2) gives condition (4) once the CFC restriction principle for the
diagonal-block direct product of `gArg` operators is supplied.  For Carlen's
functions a self-adjoint form of this principle is supplied internally in
`condition2_to_condition4_of_carlenFunction` below.
-/
theorem condition2_to_condition4_of_weightedBlockDiag_hsCfcR_gArg_cfc_restriction
    {f : ℝ → ℝ}
    (h2 : CarlenOpMontICondition2 f)
    (hcfc_restrict :
      ∀ {n : ℕ} {T : HSOp (n + n)} {T₀ T₁ : HSOp n} {V₀ V₁ : Mₙ n}
        (k : ℝ → ℝ),
        (∀ W₀ W₁ : Mₙ n,
          T (twoBlockReindex (n := n) (Matrix.fromBlocks W₀ 0 0 W₁)) =
            twoBlockReindex (n := n)
              (Matrix.fromBlocks (T₀ W₀) 0 0 (T₁ W₁))) →
        (((twoBlockReindex (n := n)).symm
          (hsCfcR k T
            (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)))).toBlocks₁₁ =
            hsCfcR k T₀ V₀) ∧
          (((twoBlockReindex (n := n)).symm
            (hsCfcR k T
              (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)))).toBlocks₂₂ =
            hsCfcR k T₁ V₁)) :
    CarlenOpMontICondition4 f :=
  condition2_to_condition4_of_weightedBlockDiag_hsCfcR_gArg_diagonal_blocks h2
    (by
      intro n θ X₀ X₁ Y₀ Y₁ Z₀ Z₁ hX₀ hX₁ hY₀ hY₁ hθ0 hθ1
      exact
        weightedBlockDiag_hsCfcR_gArg_diagonal_blocks_of_cfc_restriction
          (n := n) (θ := θ) (X₀ := X₀) (X₁ := X₁) (Y₀ := Y₀) (Y₁ := Y₁)
          (V₀ := posInv Y₀ * Z₀) (V₁ := posInv Y₁ * Z₁)
          (fun x : ℝ ↦ (f x)⁻¹) hY₀ hY₁ hθ0 hθ1 hcfc_restrict)

private theorem opMontI_gArg_spectrum_subset_Ioi_of_matrixPosDef {n : ℕ} {X Y : Mₙ n}
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    spectrum ℝ (gArg X Y) ⊆ Set.Ioi (0 : ℝ) := by
  intro x hx
  exact
    @IsStrictlyPositive.spectrum_pos (HSOp n) ℝ
      inferInstance
      (instOpMontIBaseHSOpPartialOrder (n := n))
      inferInstance
      inferInstance
      inferInstance
      (instOpMontIBaseHSOpNonnegSpectrumClass (n := n))
      (gArg X Y)
      (opMontI_gArg_isStrictlyPositive_of_matrixPosDef hX hY) x hx

private theorem opMontI_inv_continuousOn_spectrum_gArg_of_carlenFunctionHypothesis
    {n : ℕ} {f : ℝ → ℝ} {X Y : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    ContinuousOn (fun x : ℝ ↦ (f x)⁻¹) (spectrum ℝ (gArg X Y)) := by
  have hσ : spectrum ℝ (gArg X Y) ⊆ Set.Ioi (0 : ℝ) :=
    opMontI_gArg_spectrum_subset_Ioi_of_matrixPosDef hX hY
  have hcont : ContinuousOn f (spectrum ℝ (gArg X Y)) :=
    hf.1.mono hσ
  have hnonzero : ∀ x ∈ spectrum ℝ (gArg X Y), f x ≠ 0 := by
    intro x hx
    exact ne_of_gt (hf.2 (hσ hx))
  exact hcont.inv₀ hnonzero

/--
Condition (2) gives condition (4) once the CFC restriction principle is known
for self-adjoint direct products. This is the actual form needed for positive
matrix inputs.
-/
theorem condition2_to_condition4_of_weightedBlockDiag_hsCfcR_gArg_selfadjoint_cfc_restriction
    {f : ℝ → ℝ}
    (h2 : CarlenOpMontICondition2 f)
    (hcfc_restrict :
      ∀ {n : ℕ} {T : HSOp (n + n)} {T₀ T₁ : HSOp n} {V₀ V₁ : Mₙ n}
        (k : ℝ → ℝ),
        IsSelfAdjoint T →
        IsSelfAdjoint T₀ →
        IsSelfAdjoint T₁ →
        (∀ W₀ W₁ : Mₙ n,
          T (twoBlockReindex (n := n) (Matrix.fromBlocks W₀ 0 0 W₁)) =
            twoBlockReindex (n := n)
              (Matrix.fromBlocks (T₀ W₀) 0 0 (T₁ W₁))) →
        (((twoBlockReindex (n := n)).symm
          (hsCfcR k T
            (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)))).toBlocks₁₁ =
            hsCfcR k T₀ V₀) ∧
          (((twoBlockReindex (n := n)).symm
            (hsCfcR k T
              (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)))).toBlocks₂₂ =
            hsCfcR k T₁ V₁)) :
    CarlenOpMontICondition4 f :=
  condition2_to_condition4_of_weightedBlockDiag_hsCfcR_gArg_diagonal_blocks h2
    (by
      intro n θ X₀ X₁ Y₀ Y₁ Z₀ Z₁ hX₀ hX₁ hY₀ hY₁ hθ0 hθ1
      exact
        weightedBlockDiag_hsCfcR_gArg_diagonal_blocks_of_selfadjoint_cfc_restriction
          (n := n) (θ := θ) (X₀ := X₀) (X₁ := X₁) (Y₀ := Y₀) (Y₁ := Y₁)
          (V₀ := posInv Y₀ * Z₀) (V₁ := posInv Y₁ * Z₁)
          (fun x : ℝ ↦ (f x)⁻¹) hX₀ hX₁ hY₀ hY₁ hθ0 hθ1 hcfc_restrict)

/--
Condition (2) gives condition (4) from the self-adjoint CFC restriction
principle in the only form needed for Carlen's argument: the CFC function is
`fun x ↦ (f x)⁻¹`, and Carlen's positivity/continuity hypothesis supplies
its continuity on the positive spectra of the weighted-block `gArg`.
-/
theorem condition2_to_condition4_of_carlenFunction_selfadjoint_cfc_restriction
    {f : ℝ → ℝ}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (h2 : CarlenOpMontICondition2 f)
    (hcfc_restrict :
      ∀ {n : ℕ} {T : HSOp (n + n)} {T₀ T₁ : HSOp n} {V₀ V₁ : Mₙ n},
        IsSelfAdjoint T →
        IsSelfAdjoint T₀ →
        IsSelfAdjoint T₁ →
        ContinuousOn (fun x : ℝ ↦ (f x)⁻¹) (spectrum ℝ T) →
        (∀ W₀ W₁ : Mₙ n,
          T (twoBlockReindex (n := n) (Matrix.fromBlocks W₀ 0 0 W₁)) =
            twoBlockReindex (n := n)
              (Matrix.fromBlocks (T₀ W₀) 0 0 (T₁ W₁))) →
        (((twoBlockReindex (n := n)).symm
          (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) T
            (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)))).toBlocks₁₁ =
            hsCfcR (fun x : ℝ ↦ (f x)⁻¹) T₀ V₀) ∧
          (((twoBlockReindex (n := n)).symm
            (hsCfcR (fun x : ℝ ↦ (f x)⁻¹) T
              (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)))).toBlocks₂₂ =
            hsCfcR (fun x : ℝ ↦ (f x)⁻¹) T₁ V₁)) :
    CarlenOpMontICondition4 f :=
  condition2_to_condition4_of_weightedBlockDiag_hsCfcR_gArg_diagonal_blocks h2
    (by
      intro n θ X₀ X₁ Y₀ Y₁ Z₀ Z₁ hX₀ hX₁ hY₀ hY₁ hθ0 hθ1
      have hX : MatrixPosDef (weightedBlockDiag θ X₀ X₁) :=
        weightedBlockDiag_matrixPosDef (n := n) (θ := θ) hX₀ hX₁ hθ0 hθ1
      have hY : MatrixPosDef (weightedBlockDiag θ Y₀ Y₁) :=
        weightedBlockDiag_matrixPosDef (n := n) (θ := θ) hY₀ hY₁ hθ0 hθ1
      exact
        hcfc_restrict
          (n := n)
          (T := gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
          (T₀ := gArg X₀ Y₀) (T₁ := gArg X₁ Y₁)
          (V₀ := posInv Y₀ * Z₀) (V₁ := posInv Y₁ * Z₁)
          (opMontI_gArg_isSelfAdjoint_of_matrixPosDef hX hY)
          (opMontI_gArg_isSelfAdjoint_of_matrixPosDef hX₀ hY₀)
          (opMontI_gArg_isSelfAdjoint_of_matrixPosDef hX₁ hY₁)
          (opMontI_inv_continuousOn_spectrum_gArg_of_carlenFunctionHypothesis hf hX hY)
          (by
            intro W₀ W₁
            exact
              weightedBlockDiag_gArg_apply_twoBlockReindex_fromBlocks
                (n := n) (θ := θ) (X₀ := X₀) (X₁ := X₁)
                (Y₀ := Y₀) (Y₁ := Y₁) (V₀ := W₀) (V₁ := W₁)
                hY₀ hY₁ hθ0 hθ1))

/--
Condition (2) implies condition (4) for Carlen's positive-continuous
functions. The remaining CFC restriction is internal: on the finite spectrum,
an arbitrary real function agrees with an interpolating polynomial, and
polynomial functional calculus preserves the direct-sum action on the diagonal
block subspace.
-/
theorem condition2_to_condition4_of_carlenFunction
    {f : ℝ → ℝ}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (h2 : CarlenOpMontICondition2 f) :
    CarlenOpMontICondition4 f :=
  condition2_to_condition4_of_carlenFunction_selfadjoint_cfc_restriction hf h2
    (by
      intro n T T₀ T₁ V₀ V₁ hT hT₀ hT₁ _hcont hdiag
      exact
        selfadjoint_cfc_restrict_of_direct_sum_action
          (n := n) (T := T) (T₀ := T₀) (T₁ := T₁)
          (V₀ := V₀) (V₁ := V₁)
          (fun x : ℝ ↦ (f x)⁻¹) hT hT₀ hT₁ hdiag)

end

end Quantum.TraceInequality.Loewner.HiaiPetz
