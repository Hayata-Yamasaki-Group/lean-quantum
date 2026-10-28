/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenKernel
import Quantum.TraceInequality.Loewner.HalfLine.AH1
import Quantum.TraceInequality.Loewner.HalfLine.AH1Retained
import Quantum.TraceInequality.Loewner.HalfLine.Basic
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Lagrange
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.Conditions

/-!
# Carlen's `opmontI` conditions: local structure and weighted blocks

This module contains the first stage of Carlen 2022 Theorem 1.46 in the
`opmontI` route: local analytic structure, the two-block duplication map,
and weighted block positivity.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

universe u

open scoped MatrixOrder CStarAlgebra ComplexOrder FinMatrixCStar

/-! ### Local analytic structure and Carlen conditions -/
attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

attribute [local instance] instOpMontIBaseHSOpCStarAlgebra

attribute [local instance] instOpMontIBaseHSOpComplexAlgebra

attribute [local instance] instOpMontIBaseMatrixRealModule

attribute [local instance] instOpMontIBaseMatrixRealScalarTower

attribute [local instance] instOpMontIBaseMatrixRealNormedSpace

attribute [local instance] instOpMontIBaseMatrixRealFiniteDimensional

attribute [local instance] instOpMontIBaseHSOpRealAlgebra

attribute [local instance] instOpMontIBaseHSOpStarRing

attribute [local instance] instOpMontIBaseHSOpPartialOrder

attribute [local instance] instOpMontIBaseHSOpStarOrderedRing

attribute [local instance] instOpMontIBaseHSOpNonnegSpectrumClass

attribute [local instance] instOpMontIBaseHSOpRealCFC

attribute [local instance] instOpMontIBaseMatrixOppRealCFC

attribute [local instance] instOpMontIBaseHSOpProdCStarAlgebra

attribute [local instance] instOpMontIBaseHSOpProdRealCFC

attribute [local instance] instOpMontIBaseHSOpProdProdCStarAlgebra

attribute [local instance] instOpMontIBaseHSOpProdProdRealCFC

noncomputable section

/--
Condition (2): inverse data-processing inequality for Carlen's `G_f`, with
all positive-definiteness hypotheses for the displayed operators made
explicit.
-/
def CarlenOpMontICondition2 (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {X Y : Mₙ m},
    IsUnitalTwoPositiveMap Φ →
    MatrixPosDef X →
    MatrixPosDef Y →
    MatrixPosDef (hsAdjoint Φ X) →
    MatrixPosDef (hsAdjoint Φ Y) →
    HSLE
      (Φ.comp
        ((gOperatorInv f (hsAdjoint Φ X) (hsAdjoint Φ Y)).comp (hsAdjoint Φ)))
      (gOperatorInv f X Y)

/--
Condition (3): direct data-processing inequality for Carlen's `G_f`, with
the same positive-definiteness hypotheses as condition (2).
-/
def CarlenOpMontICondition3 (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {X Y : Mₙ m},
    IsUnitalTwoPositiveMap Φ →
    MatrixPosDef X →
    MatrixPosDef Y →
    MatrixPosDef (hsAdjoint Φ X) →
    MatrixPosDef (hsAdjoint Φ Y) →
    HSLE
      ((hsAdjoint Φ).comp ((gOperator f X Y).comp Φ))
      (gOperator f (hsAdjoint Φ X) (hsAdjoint Φ Y))

/-- The block-diagonal duplication map sends the identity to the identity. -/
theorem blockDiagDuplicateMap_unital {n : ℕ} :
    IsUnitalMap (blockDiagDuplicateMap (n := n)) := by
  change blockDiagDuplicateMap (n := n) (1 : Mₙ n) = (1 : Mₙ (n + n))
  change twoBlockReindex (Matrix.fromBlocks (1 : Mₙ n) 0 0 (1 : Mₙ n)) = 1
  simp [twoBlockReindex]

/--
Applying the block-diagonal duplication map entrywise to a `2 × 2` block
matrix is, after a fixed reindexing, the same as duplicating the flattened
block matrix on the block diagonal.
-/
theorem twoBlockMatrixFlatten_map_blockDiagDuplicateMap {n : ℕ}
    (M : Matrix (Fin 2) (Fin 2) (Mₙ n)) :
    twoBlockMatrixFlatten (M.map (blockDiagDuplicateMap (n := n))) =
      Matrix.reindexAlgEquiv ℂ ℂ (duplicateAmplificationIndexEquiv (n := n))
        (Matrix.fromBlocks (twoBlockMatrixFlatten M) 0 0 (twoBlockMatrixFlatten M)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    cases hi : (finSumFinEquiv (m := n) (n := n)).symm i <;>
      cases hj : (finSumFinEquiv (m := n) (n := n)).symm j <;>
        simp [twoBlockMatrixFlatten, duplicateAmplificationIndexEquiv, sumInterchange,
          Matrix.reindex_apply, blockDiagDuplicateMap_apply_entry, hi, hj]

/-- The block-diagonal duplication map is two-positive. -/
theorem blockDiagDuplicateMap_twoPositive {n : ℕ} :
    IsTwoPositiveMap (blockDiagDuplicateMap (n := n)) := by
  intro M hM
  change (twoBlockMatrixFlatten (M.map (blockDiagDuplicateMap (n := n)))).PosSemidef
  rw [twoBlockMatrixFlatten_map_blockDiagDuplicateMap]
  exact reindexAlgEquiv_posSemidef
    (duplicateAmplificationIndexEquiv (n := n))
    (fromBlocks_duplicate_posSemidef' hM)

/-- The block-diagonal duplication map is unital and two-positive. -/
theorem blockDiagDuplicateMap_unitalTwoPositive {n : ℕ} :
    IsUnitalTwoPositiveMap (blockDiagDuplicateMap (n := n)) :=
  ⟨blockDiagDuplicateMap_unital, blockDiagDuplicateMap_twoPositive⟩

end

end Quantum.TraceInequality.Loewner.HiaiPetz
