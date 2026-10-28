/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.FixedKernelGate
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.FixedKernelGateRetained
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.KernelG

/-!
# Carlen rectangle G-kernel stage

This module contains the G-kernel definitions, star bridge, positivity facts,
and the direct fixed-kernel DPI stage.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open MeasureTheory

open scoped Matrix.Norms.Frobenius MatrixOrder CStarAlgebra ComplexOrder

attribute [local instance]
  _root_.HiaiPetz.instMatrixNormedAddCommGroup
  _root_.HiaiPetz.instMatrixNormedSpace
  _root_.HiaiPetz.instMatrixInnerProductSpace
  _root_.HiaiPetz.instMatrixCompleteSpace
  instCarlenRectangleHSOpCStarAlgebra
  instCarlenRectangleHSOpPartialOrder
  instCarlenRectangleHSOpStarRing
  instCarlenRectangleHSOpStarOrderedRing
  instCarlenRectangleComplexCFC
  instCarlenRectangleRealCFC
  instCarlenRectangleHSOpNonnegSpectrumClass
  instCarlenRectangleHSOpSMulZeroClass
  instCarlenRectangleHSOpIsBoundedSMul
  instCarlenRectangleHSOpContinuousSMul
  instCarlenRectangleHSOpRealAlgebra
  instCarlenRectangleHSOpRealRealTower

noncomputable section

/--
Lieb--Ruskai supplies the inverse-form inequality for Carlen's direct fixed
kernel in the unital convention.
-/
theorem gKuboKernelInvForm_dpi_of_adjoint_liebRuskai_terms {n m : ℕ}
    (Ψ : HSMap n m) {t : ℝ} (ht : 0 ≤ t) {X Y : Mₙ m}
    (hunit : IsUnitalMap Ψ)
    (hadj_twoPositive : IsTwoPositiveMap (hsAdjoint Ψ))
    (hX : X.PosDef)
    (hY : Y.PosDef)
    (hΨX : (hsAdjoint Ψ X).PosDef)
    (hΨY : (hsAdjoint Ψ Y).PosDef) :
    HSLE
      (Ψ.comp
        ((gKuboKernelInvForm t (hsAdjoint Ψ X) (hsAdjoint Ψ Y)).comp
          (hsAdjoint Ψ)))
      (gKuboKernelInvForm t X Y) := by
  have htrace : _root_.HiaiPetz.TracePreserving (hsAdjoint Ψ) :=
    hsAdjoint_tracePreserving_of_isUnitalMap hunit
  have hright :
      HSLE
        (Ψ.comp ((rightMul (posInv (hsAdjoint Ψ X))).comp (hsAdjoint Ψ)))
        (rightMul (posInv X)) := by
    simpa [hsAdjoint_hsAdjoint] using
      (right_inverse_term_HSLE_of_matrix_inequality
        (Φ := hsAdjoint Ψ) (B := X) (B' := hsAdjoint Ψ X)
        htrace
        (fun Z => by
          simpa using
            (right_liebRuskai_inequality_of_isTwoPositiveMap
              (Ψ := hsAdjoint Ψ) (B := X) (X := Z)
              hadj_twoPositive hX hΨX)))
  have hleft :
      HSLE
        (Ψ.comp ((leftMul (posInv (hsAdjoint Ψ Y))).comp (hsAdjoint Ψ)))
        (leftMul (posInv Y)) := by
    simpa [hsAdjoint_hsAdjoint] using
      (left_inverse_term_HSLE_of_matrix_inequality
        (Φ := hsAdjoint Ψ) (A := Y) (A' := hsAdjoint Ψ Y)
        htrace
        (fun Z => by
          simpa [liebRuskaiSchur, posInv] using
            (liebRuskai_inequality_of_isTwoPositiveMap
              (Ψ := hsAdjoint Ψ) (C := Y) (X := Z)
              hadj_twoPositive hY hΨY)))
  rw [gKuboKernelInvForm_adjoint_comp_expand]
  change HSLE
    ((t : ℂ) •
        (Ψ.comp ((rightMul (posInv (hsAdjoint Ψ X))).comp (hsAdjoint Ψ))) +
      Ψ.comp ((leftMul (posInv (hsAdjoint Ψ Y))).comp (hsAdjoint Ψ)))
    ((t : ℂ) • rightMul (posInv X) + leftMul (posInv Y))
  exact HSLE_add (HSLE_smul_of_nonneg ht hright) hleft

/-- Direct Carlen fixed-kernel DPI for unital two-positive maps. -/
theorem gKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef
    {n m : ℕ} (Ψ : HSMap n m) {t : ℝ} (ht : 0 ≤ t) {X Y : Mₙ m}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hX : MatrixPosDef X)
    (hY : MatrixPosDef Y)
    (hΨX : MatrixPosDef (hsAdjoint Ψ X))
    (hΨY : MatrixPosDef (hsAdjoint Ψ Y)) :
    HSLE
      ((hsAdjoint Ψ).comp ((gKuboKernel t X Y).comp Ψ))
      (gKuboKernel t (hsAdjoint Ψ X) (hsAdjoint Ψ Y)) := by
  have hinv :
      HSLE
        (Ψ.comp
          ((gKuboKernelInvForm t (hsAdjoint Ψ X) (hsAdjoint Ψ Y)).comp
            (hsAdjoint Ψ)))
        (gKuboKernelInvForm t X Y) :=
    gKuboKernelInvForm_dpi_of_adjoint_liebRuskai_terms
      Ψ ht hΨ.1 (isTwoPositiveMap_hsAdjoint_of_isTwoPositiveMap hΨ.2)
      (matrixPosDef_posDef hX) (matrixPosDef_posDef hY)
      (matrixPosDef_posDef hΨX) (matrixPosDef_posDef hΨY)
  have hInvTA_sa : IsSelfAdjoint (gKuboKernelInvForm t X Y) :=
    gKuboKernelInvForm_isSelfAdjoint_of_matrixPosDef ht hX hY
  have hInvTΦ_sa :
      IsSelfAdjoint (gKuboKernelInvForm t (hsAdjoint Ψ X) (hsAdjoint Ψ Y)) :=
    gKuboKernelInvForm_isSelfAdjoint_of_matrixPosDef ht hΨX hΨY
  have hσInvTA :
      spectrum ℝ (gKuboKernelInvForm t X Y) ⊆ Set.Ioi (0 : ℝ) :=
    gKuboKernelInvForm_spectrum_subset_Ioi_of_matrixPosDef ht hX hY
  have hσInvTΦ :
      spectrum ℝ (gKuboKernelInvForm t (hsAdjoint Ψ X) (hsAdjoint Ψ Y)) ⊆
        Set.Ioi (0 : ℝ) :=
    gKuboKernelInvForm_spectrum_subset_Ioi_of_matrixPosDef ht hΨX hΨY
  have hTA_sa : IsSelfAdjoint (gKuboKernel t X Y) :=
    gKuboKernel_isSelfAdjoint_of_invForm_facts hInvTA_sa hσInvTA
  have hTΦ_sa :
      IsSelfAdjoint (gKuboKernel t (hsAdjoint Ψ X) (hsAdjoint Ψ Y)) :=
    gKuboKernel_isSelfAdjoint_of_invForm_facts hInvTΦ_sa hσInvTΦ
  have hσTA :
      spectrum ℝ (gKuboKernel t X Y) ⊆ Set.Ioi (0 : ℝ) :=
    gKuboKernel_spectrum_subset_Ioi_of_invForm_facts hInvTA_sa hσInvTA
  have hσTΦ :
      spectrum ℝ (gKuboKernel t (hsAdjoint Ψ X) (hsAdjoint Ψ Y)) ⊆
        Set.Ioi (0 : ℝ) :=
    gKuboKernel_spectrum_subset_Ioi_of_invForm_facts hInvTΦ_sa hσInvTΦ
  have hInvTA_unit : IsUnit (gKuboKernelInvForm t X Y) :=
    gKuboKernelInvForm_isUnit_of_matrixPosDef ht hX hY
  have hInvTΦ_unit :
      IsUnit (gKuboKernelInvForm t (hsAdjoint Ψ X) (hsAdjoint Ψ Y)) :=
    gKuboKernelInvForm_isUnit_of_matrixPosDef ht hΨX hΨY
  have hrect :
      HSLE
        (carlenRectInverseOp Ψ (gKuboKernel t (hsAdjoint Ψ X) (hsAdjoint Ψ Y)))
        (Ring.inverse (gKuboKernel t X Y)) := by
    have hInvTA :
        Ring.inverse (gKuboKernel t X Y) = gKuboKernelInvForm t X Y :=
      gKuboKernel_inverse_eq_invForm_of_isUnit t X Y hInvTA_unit
    have hInvTΦ :
        Ring.inverse (gKuboKernel t (hsAdjoint Ψ X) (hsAdjoint Ψ Y)) =
          gKuboKernelInvForm t (hsAdjoint Ψ X) (hsAdjoint Ψ Y) :=
      gKuboKernel_inverse_eq_invForm_of_isUnit
        t (hsAdjoint Ψ X) (hsAdjoint Ψ Y) hInvTΦ_unit
    simpa [carlenRectInverseOp, hInvTA, hInvTΦ] using hinv
  have hdirect :=
    carlenRectangle_inverse_to_direct
      Ψ hTA_sa hTΦ_sa hσTA hσTΦ hrect
  simpa [carlenRectDirectOp] using hdirect

end

end Quantum.TraceInequality.Loewner.HiaiPetz
