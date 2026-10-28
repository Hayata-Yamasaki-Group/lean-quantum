/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.WeightedAction
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.ConditionsRetained
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.KieferBound

/-!
# Carlen's `opmontI` conditions: Kiefer bound and reciprocal target

This module contains the projection-invariance, Kiefer quadratic-form bound,
and condition (4) specialization stage of Carlen 2022 Theorem 1.46.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder

attribute [local instance]
  _root_.HiaiPetz.instMatrixNormedAddCommGroup
  _root_.HiaiPetz.instMatrixNormedSpace
  _root_.HiaiPetz.instMatrixInnerProductSpace
  _root_.HiaiPetz.instMatrixCompleteSpace
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
Applying condition (2) to the block-diagonal duplication map and the weighted
block-diagonal positive-definite inputs gives the Hilbert--Schmidt operator
inequality used in the joint-convexity proof.
-/
theorem condition2_weighted_blockDiagDuplicateMap_HSLE {n : ℕ} {f : ℝ → ℝ}
    (h2 : CarlenOpMontICondition2 f) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {X₀ X₁ Y₀ Y₁ : Mₙ n}
    (hX₀ : MatrixPosDef X₀) (hX₁ : MatrixPosDef X₁)
    (hY₀ : MatrixPosDef Y₀) (hY₁ : MatrixPosDef Y₁) :
    HSLE
      ((blockDiagDuplicateMap (n := n)).comp
        ((gOperatorInv f
            (hsAdjoint (blockDiagDuplicateMap (n := n))
              (weightedBlockDiag θ X₀ X₁))
            (hsAdjoint (blockDiagDuplicateMap (n := n))
              (weightedBlockDiag θ Y₀ Y₁))).comp
          (hsAdjoint (blockDiagDuplicateMap (n := n)))))
      (gOperatorInv f (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁)) := by
  classical
  let Φ : HSMap n (n + n) := blockDiagDuplicateMap (n := n)
  let X := weightedBlockDiag θ X₀ X₁
  let Y := weightedBlockDiag θ Y₀ Y₁
  have hΦ : IsUnitalTwoPositiveMap Φ := by
    simpa [Φ] using blockDiagDuplicateMap_unitalTwoPositive (n := n)
  have hX : MatrixPosDef X := by
    simpa [X] using
      weightedBlockDiag_matrixPosDef
        (n := n) (θ := θ) hX₀ hX₁ hθ0 hθ1
  have hY : MatrixPosDef Y := by
    simpa [Y] using
      weightedBlockDiag_matrixPosDef
        (n := n) (θ := θ) hY₀ hY₁ hθ0 hθ1
  have hΦX :
      hsAdjoint Φ X = matrixConvexCombo θ X₀ X₁ := by
    simpa [Φ, X] using
      hsAdjoint_blockDiagDuplicateMap_weightedBlockDiag
        (n := n) θ X₀ X₁
  have hΦY :
      hsAdjoint Φ Y = matrixConvexCombo θ Y₀ Y₁ := by
    simpa [Φ, Y] using
      hsAdjoint_blockDiagDuplicateMap_weightedBlockDiag
        (n := n) θ Y₀ Y₁
  have hΦX_pos : MatrixPosDef (hsAdjoint Φ X) := by
    simpa [hΦX] using
      matrixPosDef_matrixConvexCombo
        (θ := θ) hX₀ hX₁ (le_of_lt hθ0) (le_of_lt hθ1)
  have hΦY_pos : MatrixPosDef (hsAdjoint Φ Y) := by
    simpa [hΦY] using
      matrixPosDef_matrixConvexCombo
        (θ := θ) hY₀ hY₁ (le_of_lt hθ0) (le_of_lt hθ1)
  simpa [Φ, X, Y] using h2 Φ hΦ hX hY hΦX_pos hΦY_pos

/--
The weighted block application of condition (2), evaluated on the weighted
block vector, gives the first quadratic-form inequality in the joint-convexity
argument.
-/
theorem condition2_weightedBlockDiag_gInvQF_le {n : ℕ} {f : ℝ → ℝ}
    (h2 : CarlenOpMontICondition2 f) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {X₀ X₁ Y₀ Y₁ Z₀ Z₁ : Mₙ n}
    (hX₀ : MatrixPosDef X₀) (hX₁ : MatrixPosDef X₁)
    (hY₀ : MatrixPosDef Y₀) (hY₁ : MatrixPosDef Y₁) :
    gInvQF f
        (matrixConvexCombo θ X₀ X₁)
        (matrixConvexCombo θ Y₀ Y₁)
        (matrixConvexCombo θ Z₀ Z₁)
      ≤
      hsQF
        (gOperatorInv f (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
        (weightedBlockDiag θ Z₀ Z₁) := by
  let Δ : HSMap n (n + n) := blockDiagDuplicateMap (n := n)
  let X := weightedBlockDiag θ X₀ X₁
  let Y := weightedBlockDiag θ Y₀ Y₁
  let Z := weightedBlockDiag θ Z₀ Z₁
  have hHS :
      HSLE
        (Δ.comp
          ((gOperatorInv f (hsAdjoint Δ X) (hsAdjoint Δ Y)).comp
            (hsAdjoint Δ)))
        (gOperatorInv f X Y) := by
    simpa [Δ, X, Y] using
      condition2_weighted_blockDiagDuplicateMap_HSLE
        (n := n) (f := f) h2 hθ0 hθ1 hX₀ hX₁ hY₀ hY₁
  have hq := hsQF_le_of_HSLE hHS Z
  rw [hsQF_comp_adjoint] at hq
  simpa [gInvQF, Δ, X, Y, Z,
    hsAdjoint_blockDiagDuplicateMap_weightedBlockDiag] using hq

end

end Quantum.TraceInequality.Loewner.HiaiPetz
