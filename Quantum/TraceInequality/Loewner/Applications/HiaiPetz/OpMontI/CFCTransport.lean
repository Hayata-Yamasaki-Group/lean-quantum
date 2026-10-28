/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.RankOneBridge
import Quantum.TraceInequality.HiaiPetz.BasicTheorems
import Quantum.TraceInequality.HiaiPetz.Core.Basic
import Quantum.TraceInequality.HiaiPetz.MatrixHilbert
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenKernel.FixedKernelOrder
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.Basic

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

/-! ### CFC restriction interfaces and direct-sum transport -/
/--
The CFC step can be phrased as a restriction principle: whenever the
weighted-block `gArg` restricts to the direct product of the two smaller
`gArg` operators on diagonal-block vectors, the same is true after applying
the real continuous functional calculus.  For Carlen's functions this CFC step is
carried out in `condition2_to_condition4_of_carlenFunction` below.
-/
theorem weightedBlockDiag_hsCfcR_gArg_diagonal_blocks_of_cfc_restriction
    {n : ℕ} {θ : ℝ} {X₀ X₁ Y₀ Y₁ V₀ V₁ : Mₙ n} (k : ℝ → ℝ)
    (hY₀ : MatrixPosDef Y₀) (hY₁ : MatrixPosDef Y₁)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
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
    (((twoBlockReindex (n := n)).symm
      (hsCfcR k
        (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
        (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)))).toBlocks₁₁ =
        hsCfcR k (gArg X₀ Y₀) V₀) ∧
      (((twoBlockReindex (n := n)).symm
        (hsCfcR k
          (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
          (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)))).toBlocks₂₂ =
        hsCfcR k (gArg X₁ Y₁) V₁) :=
  hcfc_restrict
    (n := n)
    (T := gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
    (T₀ := gArg X₀ Y₀) (T₁ := gArg X₁ Y₁)
    (V₀ := V₀) (V₁ := V₁) k
    (by
      intro W₀ W₁
      exact
        weightedBlockDiag_gArg_apply_twoBlockReindex_fromBlocks
          (n := n) (θ := θ) (X₀ := X₀) (X₁ := X₁)
          (Y₀ := Y₀) (Y₁ := Y₁) (V₀ := W₀) (V₁ := W₁)
          hY₀ hY₁ hθ0 hθ1)

private theorem opMontI_gArg_eq_rightMul_mul_leftMul {n : ℕ} (X Y : Mₙ n) :
    gArg X Y = (rightMul X : HSOp n) * leftMul (posInv Y) := by
  ext Z i j
  simp [gArg, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply]

theorem opMontI_gArg_isStrictlyPositive_of_matrixPosDef {n : ℕ} {X Y : Mₙ n}
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    IsStrictlyPositive (gArg X Y) := by
  have hright : IsStrictlyPositive (rightMul X : HSOp n) :=
    rightMul_isStrictlyPositive_of_matrix_posDef (matrixPosDef_posDef hX)
  have hleft : IsStrictlyPositive (leftMul (posInv Y) : HSOp n) :=
    leftMul_isStrictlyPositive_of_matrix_posDef (matrixPosDef_posInv_posDef hY)
  have hcomm : Commute (rightMul X : HSOp n) (leftMul (posInv Y)) :=
    (leftMul_commute_rightMul (posInv Y) X).symm
  have hprod : IsStrictlyPositive ((rightMul X : HSOp n) * leftMul (posInv Y)) :=
    (@IsStrictlyPositive.commute_iff (HSOp n)
      inferInstance
      (instOpMontIBaseHSOpPartialOrder (n := n))
      (instOpMontIBaseHSOpStarRing (n := n))
      (instOpMontIBaseHSOpStarOrderedRing (n := n))
      inferInstance
      inferInstance
      inferInstance
      (instOpMontIBaseHSOpNonnegSpectrumClass (n := n))
      (rightMul X : HSOp n) (leftMul (posInv Y)) hright hleft).mp hcomm
  simpa [opMontI_gArg_eq_rightMul_mul_leftMul X Y] using hprod

theorem opMontI_gArg_isSelfAdjoint_of_matrixPosDef {n : ℕ} {X Y : Mₙ n}
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y) :
    IsSelfAdjoint (gArg X Y) :=
  @IsStrictlyPositive.isSelfAdjoint (HSOp n)
    inferInstance
    (instOpMontIBaseHSOpPartialOrder (n := n))
    (instOpMontIBaseHSOpStarRing (n := n))
    (instOpMontIBaseHSOpStarOrderedRing (n := n))
    (gArg X Y)
    (opMontI_gArg_isStrictlyPositive_of_matrixPosDef hX hY)

/--
On the product of two Hilbert--Schmidt operator algebras, real continuous
functional calculus is componentwise.
-/
theorem prod_hsCfcR_eq {n : ℕ} (k : ℝ → ℝ) {T₀ T₁ : HSOp n}
    (hT₀ : IsSelfAdjoint T₀) (hT₁ : IsSelfAdjoint T₁)
    (hk : ContinuousOn k (spectrum ℝ T₀ ∪ spectrum ℝ T₁)) :
    cfc (R := ℝ) (A := HSOp n × HSOp n)
        (p := IsSelfAdjoint)
        k (T₀, T₁) =
      (hsCfcR k T₀, hsCfcR k T₁) := by
  have hpair : IsSelfAdjoint (T₀, T₁) := by
    ext <;> simp only [Prod.fst_star, Prod.snd_star]
    · rw [hT₀]
    · rw [hT₁]
  simpa [hsCfcR] using
    (cfc_map_prod (R := ℝ) (S := ℂ) (A := HSOp n) (B := HSOp n)
      (pab := IsSelfAdjoint)
      (pa := IsSelfAdjoint) (pb := IsSelfAdjoint)
      k T₀ T₁ hk hpair hT₀ hT₁)

/--
On the product of four Hilbert--Schmidt operator algebras, grouped as a
product of two products, real continuous functional calculus is still
componentwise.
-/
theorem prod_prod_hsCfcR_eq {n : ℕ} (k : ℝ → ℝ)
    {T₀₀ T₀₁ T₁₀ T₁₁ : HSOp n}
    (hT₀₀ : IsSelfAdjoint T₀₀) (hT₀₁ : IsSelfAdjoint T₀₁)
    (hT₁₀ : IsSelfAdjoint T₁₀) (hT₁₁ : IsSelfAdjoint T₁₁)
    (hk : ContinuousOn k
      ((spectrum ℝ T₀₀ ∪ spectrum ℝ T₀₁) ∪
        (spectrum ℝ T₁₀ ∪ spectrum ℝ T₁₁))) :
    cfc (R := ℝ) (A := (HSOp n × HSOp n) × (HSOp n × HSOp n))
        (p := IsSelfAdjoint)
        k ((T₀₀, T₀₁), (T₁₀, T₁₁)) =
      ((hsCfcR k T₀₀, hsCfcR k T₀₁),
        (hsCfcR k T₁₀, hsCfcR k T₁₁)) := by
  have hleft_sa : IsSelfAdjoint (T₀₀, T₀₁) :=
    Prod.ext hT₀₀ hT₀₁
  have hright_sa : IsSelfAdjoint (T₁₀, T₁₁) :=
    Prod.ext hT₁₀ hT₁₁
  have hpair_sa : IsSelfAdjoint ((T₀₀, T₀₁), (T₁₀, T₁₁)) :=
    Prod.ext hleft_sa hright_sa
  have hk_left : ContinuousOn k (spectrum ℝ T₀₀ ∪ spectrum ℝ T₀₁) := by
    exact hk.mono (by
      intro x hx
      exact Set.mem_union_left (spectrum ℝ T₁₀ ∪ spectrum ℝ T₁₁) hx)
  have hk_right : ContinuousOn k (spectrum ℝ T₁₀ ∪ spectrum ℝ T₁₁) := by
    exact hk.mono (by
      intro x hx
      exact Set.mem_union_right (spectrum ℝ T₀₀ ∪ spectrum ℝ T₀₁) hx)
  have hk_outer :
      ContinuousOn k
        (spectrum ℝ (T₀₀, T₀₁) ∪ spectrum ℝ (T₁₀, T₁₁)) := by
    refine hk.mono ?_
    intro x hx
    rw [Prod.spectrum_eq, Prod.spectrum_eq] at hx
    exact hx
  have hleft := prod_hsCfcR_eq (n := n) k hT₀₀ hT₀₁ hk_left
  have hright := prod_hsCfcR_eq (n := n) k hT₁₀ hT₁₁ hk_right
  have houter :
      cfc (R := ℝ) (A := (HSOp n × HSOp n) × (HSOp n × HSOp n))
          (p := IsSelfAdjoint)
          k ((T₀₀, T₀₁), (T₁₀, T₁₁)) =
        (cfc (R := ℝ) (A := HSOp n × HSOp n) (p := IsSelfAdjoint)
            k (T₀₀, T₀₁),
          cfc (R := ℝ) (A := HSOp n × HSOp n) (p := IsSelfAdjoint)
            k (T₁₀, T₁₁)) := by
    simpa using
      (cfc_map_prod (R := ℝ) (S := ℂ)
        (A := HSOp n × HSOp n) (B := HSOp n × HSOp n)
        (pab := IsSelfAdjoint)
        (pa := IsSelfAdjoint) (pb := IsSelfAdjoint)
        k (T₀₀, T₀₁) (T₁₀, T₁₁)
        hk_outer hpair_sa hleft_sa hright_sa)
  simpa [hleft, hright] using houter

/--
An isometric identification of Hilbert spaces transports real continuous
functional calculus of continuous operators by conjugation.
-/
theorem linearIsometryEquiv_cfc_conj_apply
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [CStarAlgebra (E →L[ℂ] E)] [CStarAlgebra (F →L[ℂ] F)]
    [ContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint]
    [ContinuousFunctionalCalculus ℝ (F →L[ℂ] F) IsSelfAdjoint]
    (e : E ≃ₗᵢ[ℂ] F) (k : ℝ → ℝ) (T : E →L[ℂ] E)
    (hk : ContinuousOn k (spectrum ℝ T))
    (hT : IsSelfAdjoint T) (x : E) :
    e ((cfc (R := ℝ) (A := E →L[ℂ] E) (p := IsSelfAdjoint) k T) x) =
      (cfc (R := ℝ) (A := F →L[ℂ] F) (p := IsSelfAdjoint)
        k (e.conjStarAlgEquiv T)) (e x) := by
  have hcont : Continuous (fun S : E →L[ℂ] E => e.conjStarAlgEquiv S) := by
    simpa [LinearIsometryEquiv.conjStarAlgEquiv] using
      (e.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous :
        Continuous (fun S : E →L[ℂ] E =>
          e.toContinuousLinearEquiv.conjContinuousAlgEquiv S))
  have hφa : IsSelfAdjoint (e.conjStarAlgEquiv T) := by
    exact hT.map e.conjStarAlgEquiv
  have hmap :
      e.conjStarAlgEquiv
        (cfc (R := ℝ) (A := E →L[ℂ] E) (p := IsSelfAdjoint) k T) =
        cfc (R := ℝ) (A := F →L[ℂ] F) (p := IsSelfAdjoint)
          k (e.conjStarAlgEquiv T) := by
    exact
      StarAlgHomClass.map_cfc
        (φ := e.conjStarAlgEquiv)
        (f := k) (a := T)
        (hf := hk)
        (hφ := hcont)
        (ha := hT)
        (hφa := hφa)
  have happly := congrArg (fun S : F →L[ℂ] F => S (e x)) hmap
  simpa using happly

/--
If the CFC of the large operator, after restricting to diagonal blocks and
reading the two blocks, agrees with the product-algebra CFC, then the two
diagonal blocks are the CFCs of the two smaller operators.
-/
theorem diagonal_blocks_hsCfcR_eq_of_product_cfc_transport {n : ℕ}
    {T : HSOp (n + n)} {T₀ T₁ : HSOp n} {V₀ V₁ : Mₙ n} (k : ℝ → ℝ)
    (hT₀ : IsSelfAdjoint T₀) (hT₁ : IsSelfAdjoint T₁)
    (hk : ContinuousOn k (spectrum ℝ T₀ ∪ spectrum ℝ T₁))
    (htransport :
      twoBlockDiagonalBlocks (n := n)
          (hsCfcR k T (twoBlockDiagonalEmbed (n := n) (V₀, V₁))) =
        (((cfc (R := ℝ) (A := HSOp n × HSOp n)
              (p := IsSelfAdjoint) k (T₀, T₁)).1) V₀,
          ((cfc (R := ℝ) (A := HSOp n × HSOp n)
              (p := IsSelfAdjoint) k (T₀, T₁)).2) V₁)) :
    (((twoBlockReindex (n := n)).symm
      (hsCfcR k T
        (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)))).toBlocks₁₁ =
        hsCfcR k T₀ V₀) ∧
      (((twoBlockReindex (n := n)).symm
        (hsCfcR k T
          (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)))).toBlocks₂₂ =
        hsCfcR k T₁ V₁) := by
  have hprod := prod_hsCfcR_eq (n := n) k hT₀ hT₁ hk
  have hblocks :
      twoBlockDiagonalBlocks (n := n)
          (hsCfcR k T (twoBlockDiagonalEmbed (n := n) (V₀, V₁))) =
        (hsCfcR k T₀ V₀, hsCfcR k T₁ V₁) := by
    simpa [hprod] using htransport
  constructor
  · have hfst := congrArg Prod.fst hblocks
    simpa [twoBlockDiagonalBlocks, twoBlockDiagonalEmbed] using hfst
  · have hsnd := congrArg Prod.snd hblocks
    simpa [twoBlockDiagonalBlocks, twoBlockDiagonalEmbed] using hsnd

/-! ### Self-adjoint CFC restriction and final condition (2) to condition (4) -/
/--
For the actual weighted-block `gArg` situation, it is enough to know the CFC
restriction principle for self-adjoint operators. Positive-definiteness of the
matrix inputs supplies the self-adjointness of the three `gArg` operators.
-/
theorem weightedBlockDiag_hsCfcR_gArg_diagonal_blocks_of_selfadjoint_cfc_restriction
    {n : ℕ} {θ : ℝ} {X₀ X₁ Y₀ Y₁ V₀ V₁ : Mₙ n} (k : ℝ → ℝ)
    (hX₀ : MatrixPosDef X₀) (hX₁ : MatrixPosDef X₁)
    (hY₀ : MatrixPosDef Y₀) (hY₁ : MatrixPosDef Y₁)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
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
    (((twoBlockReindex (n := n)).symm
      (hsCfcR k
        (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
        (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)))).toBlocks₁₁ =
        hsCfcR k (gArg X₀ Y₀) V₀) ∧
      (((twoBlockReindex (n := n)).symm
        (hsCfcR k
          (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
          (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)))).toBlocks₂₂ =
        hsCfcR k (gArg X₁ Y₁) V₁) := by
  have hX : MatrixPosDef (weightedBlockDiag θ X₀ X₁) :=
    weightedBlockDiag_matrixPosDef (n := n) (θ := θ) hX₀ hX₁ hθ0 hθ1
  have hY : MatrixPosDef (weightedBlockDiag θ Y₀ Y₁) :=
    weightedBlockDiag_matrixPosDef (n := n) (θ := θ) hY₀ hY₁ hθ0 hθ1
  exact
    hcfc_restrict
      (n := n)
      (T := gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
      (T₀ := gArg X₀ Y₀) (T₁ := gArg X₁ Y₁)
      (V₀ := V₀) (V₁ := V₁) k
      (opMontI_gArg_isSelfAdjoint_of_matrixPosDef hX hY)
      (opMontI_gArg_isSelfAdjoint_of_matrixPosDef hX₀ hY₀)
      (opMontI_gArg_isSelfAdjoint_of_matrixPosDef hX₁ hY₁)
      (by
        intro W₀ W₁
        exact
          weightedBlockDiag_gArg_apply_twoBlockReindex_fromBlocks
            (n := n) (θ := θ) (X₀ := X₀) (X₁ := X₁)
            (Y₀ := Y₀) (Y₁ := Y₁) (V₀ := W₀) (V₁ := W₁)
            hY₀ hY₁ hθ0 hθ1)

end

end Quantum.TraceInequality.Loewner.HiaiPetz
