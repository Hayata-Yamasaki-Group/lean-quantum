/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenKernel
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.ConditionIToLoewner
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.LoewnerEntry
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.PositiveInverse
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.Surface.QuasiEntropyDPIAlignment
import Quantum.TraceInequality.Loewner.HalfLine.KuboAndo
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.Infrastructure
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.RectangleOrder
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.FixedKernelGate

-- positive-part decomposition for positive maps

/-!
# Carlen fixed-kernel gates

This module contains the fixed-kernel gate stage of the Carlen 2022 Theorem
1.46 argument: inverse-form fixed-kernel DPI gates, J-operator endpoint
assembly, and Hilbert--Schmidt order under Bochner integration.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open MeasureTheory

open scoped Matrix.Norms.Frobenius MatrixOrder CStarAlgebra ComplexOrder

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace
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
The fixed-kernel gate obtained by applying the square-root rectangle step to
the inverse-form Lieb--Ruskai DPI.  The fixed-kernel facts are kept explicit
here: adjoint two-positivity, the two kernel inverse formulae, and positive real
spectra for the two direct kernels.  They are supplied in the theorems below,
ending in `jKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef`.
-/
theorem jKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef_adjointSupplier_and_rectangle
    {n m : ℕ} (Ψ : HSMap n m) {t : ℝ} (ht : 0 ≤ t) {A B : Mₙ m}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hadj_twoPositive : IsUnitalTwoPositiveMap Ψ → IsTwoPositiveMap (hsAdjoint Ψ))
    (hA : MatrixPosDef A)
    (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B))
    (hTA_sa : IsSelfAdjoint (jKuboKernel t A B))
    (hTΦ_sa : IsSelfAdjoint (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)))
    (hσTA : spectrum ℝ (jKuboKernel t A B) ⊆ Set.Ioi (0 : ℝ))
    (hσTΦ :
      spectrum ℝ (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) ⊆ Set.Ioi (0 : ℝ))
    (hInvTA : Ring.inverse (jKuboKernel t A B) = jKuboKernelInvForm t A B)
    (hInvTΦ :
      Ring.inverse (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) =
        jKuboKernelInvForm t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :
    HSLE
      ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
      (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
  jKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef_adjointSupplier_and_flip
    Ψ ht hΨ hadj_twoPositive hA hB hΨA hΨB
    (fun hinv => by
      have hrect :
          HSLE
            (carlenRectInverseOp Ψ (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)))
            (Ring.inverse (jKuboKernel t A B)) := by
        simpa [carlenRectInverseOp, hInvTA, hInvTΦ] using hinv
      have hdirect :=
        carlenRectangle_inverse_to_direct
          Ψ hTA_sa hTΦ_sa hσTA hσTΦ hrect
      simpa [carlenRectDirectOp] using hdirect)

/--
Fixed-kernel DPI gate where the direct-kernel self-adjointness, positive
spectrum, and inverse formula are supplied by self-adjointness, positive
spectrum, and unitness of the two inverse-form kernels.
-/
theorem jKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef_adjointSupplier_and_invFormFacts
    {n m : ℕ} (Ψ : HSMap n m) {t : ℝ} (ht : 0 ≤ t) {A B : Mₙ m}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hadj_twoPositive : IsUnitalTwoPositiveMap Ψ → IsTwoPositiveMap (hsAdjoint Ψ))
    (hA : MatrixPosDef A)
    (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B))
    (hInvTA_sa : IsSelfAdjoint (jKuboKernelInvForm t A B))
    (hInvTΦ_sa : IsSelfAdjoint (jKuboKernelInvForm t (hsAdjoint Ψ A) (hsAdjoint Ψ B)))
    (hσInvTA : spectrum ℝ (jKuboKernelInvForm t A B) ⊆ Set.Ioi (0 : ℝ))
    (hσInvTΦ :
      spectrum ℝ (jKuboKernelInvForm t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) ⊆
        Set.Ioi (0 : ℝ))
    (hInvTA_unit : IsUnit (jKuboKernelInvForm t A B))
    (hInvTΦ_unit : IsUnit (jKuboKernelInvForm t (hsAdjoint Ψ A) (hsAdjoint Ψ B))) :
    HSLE
      ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
      (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
  jKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef_adjointSupplier_and_rectangle
    Ψ ht hΨ hadj_twoPositive hA hB hΨA hΨB
    (jKuboKernel_isSelfAdjoint_of_invForm_facts hInvTA_sa hσInvTA)
    (jKuboKernel_isSelfAdjoint_of_invForm_facts hInvTΦ_sa hσInvTΦ)
    (jKuboKernel_spectrum_subset_Ioi_of_invForm_facts hInvTA_sa hσInvTA)
    (jKuboKernel_spectrum_subset_Ioi_of_invForm_facts hInvTΦ_sa hσInvTΦ)
    (jKuboKernel_inverse_eq_invForm_of_invForm_facts hInvTA_unit)
    (jKuboKernel_inverse_eq_invForm_of_invForm_facts hInvTΦ_unit)

/--
Fixed-kernel DPI gate where theorem-facing matrix positivity supplies the
self-adjointness of the two inverse-form kernels.  The other inverse-form facts,
positive real spectra and unitness, are supplied from matrix positivity in
`jKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef_adjointSupplier` below.
-/
theorem jKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef_adjointSupplier_and_invFormSpectrumUnit
    {n m : ℕ} (Ψ : HSMap n m) {t : ℝ} (ht : 0 ≤ t) {A B : Mₙ m}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hadj_twoPositive : IsUnitalTwoPositiveMap Ψ → IsTwoPositiveMap (hsAdjoint Ψ))
    (hA : MatrixPosDef A)
    (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B))
    (hσInvTA : spectrum ℝ (jKuboKernelInvForm t A B) ⊆ Set.Ioi (0 : ℝ))
    (hσInvTΦ :
      spectrum ℝ (jKuboKernelInvForm t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) ⊆
        Set.Ioi (0 : ℝ))
    (hInvTA_unit : IsUnit (jKuboKernelInvForm t A B))
    (hInvTΦ_unit : IsUnit (jKuboKernelInvForm t (hsAdjoint Ψ A) (hsAdjoint Ψ B))) :
    HSLE
      ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
      (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
  jKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef_adjointSupplier_and_invFormFacts
    Ψ ht hΨ hadj_twoPositive hA hB hΨA hΨB
    (jKuboKernelInvForm_isSelfAdjoint_of_matrixPosDef hA hB)
    (jKuboKernelInvForm_isSelfAdjoint_of_matrixPosDef hΨA hΨB)
    hσInvTA hσInvTΦ hInvTA_unit hInvTΦ_unit

/--
Fixed-kernel DPI with theorem-facing matrix positivity and the inverse-form
strict-positivity facts supplied internally.  The only explicit input is the
two-positivity of the Hilbert--Schmidt adjoint, supplied by
`isTwoPositiveMap_hsAdjoint_of_isTwoPositiveMap` in
`jKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef` below.
-/
theorem jKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef_adjointSupplier
    {n m : ℕ} (Ψ : HSMap n m) {t : ℝ} (ht : 0 ≤ t) {A B : Mₙ m}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hadj_twoPositive : IsUnitalTwoPositiveMap Ψ → IsTwoPositiveMap (hsAdjoint Ψ))
    (hA : MatrixPosDef A)
    (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B)) :
    HSLE
      ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
      (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
  jKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef_adjointSupplier_and_invFormSpectrumUnit
    Ψ ht hΨ hadj_twoPositive hA hB hΨA hΨB
    (jKuboKernelInvForm_spectrum_subset_Ioi_of_matrixPosDef ht hA hB)
    (jKuboKernelInvForm_spectrum_subset_Ioi_of_matrixPosDef ht hΨA hΨB)
    (jKuboKernelInvForm_isUnit_of_matrixPosDef ht hA hB)
    (jKuboKernelInvForm_isUnit_of_matrixPosDef ht hΨA hΨB)

/--
Fixed-kernel DPI for unital two-positive maps, with the Hilbert--Schmidt
adjoint's two-positivity supplied by the finite-dimensional block-duality
argument.
-/
theorem jKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef
    {n m : ℕ} (Ψ : HSMap n m) {t : ℝ} (ht : 0 ≤ t) {A B : Mₙ m}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hA : MatrixPosDef A)
    (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B)) :
    HSLE
      ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
      (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
  jKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef_adjointSupplier
    Ψ ht hΨ (fun h => isTwoPositiveMap_hsAdjoint_of_isTwoPositiveMap h.2)
    hA hB hΨA hΨB

/--
Explicit Kubo--Ando expansion gate with the endpoint and slope Hilbert--Schmidt
terms supplied by Kadison--Choi Schwarz for a unital two-positive map.
-/
theorem jOperator_dpi_of_explicit_kubo_terms_and_isUnitalTwoPositiveMap
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} {A B : Mₙ m}
    {c b : ℝ} {KAB : HSOp m} {KΦ : HSOp n}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hkernel :
      HSLE ((hsAdjoint Ψ).comp (KAB.comp Ψ)) KΦ)
    (hJAB :
      jOperator f₀ A B =
        (c : ℂ) • rightMul B + (b : ℂ) • leftMul A + KAB)
    (hJΦ :
      jOperator f₀ (hsAdjoint Ψ A) (hsAdjoint Ψ B) =
        (c : ℂ) • rightMul (hsAdjoint Ψ B) +
          (b : ℂ) • leftMul (hsAdjoint Ψ A) + KΦ) :
    HSLE
      ((hsAdjoint Ψ).comp ((jOperator f₀ A B).comp Ψ))
      (jOperator f₀ (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
  jOperator_dpi_of_explicit_kubo_terms Ψ hc hb
    (rightMul_dpi_of_isUnitalTwoPositiveMap Ψ hΨ hB)
    (leftMul_dpi_of_isUnitalTwoPositiveMap Ψ hΨ hA)
    hkernel hJAB hJΦ

/--
Kubo--Ando representation gate for the direct strict DPI, once the
operator-level Kubo expansion and the integrated fixed-kernel inequality have
been supplied explicitly.

The endpoint coefficient is `f₀ 0`, so its nonnegativity is an explicit
hypothesis; it is not part of the raw `PositiveRayKuboAndoRep` structure.
-/
theorem jOperator_dpi_of_positiveRayKuboAndoRep_explicit_terms
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} {A B : Mₙ m}
    (rep : PositiveRayKuboAndoRep f₀)
    {KAB : HSOp m} {KΦ : HSOp n}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (h0 : 0 ≤ f₀ 0)
    (hkernel :
      HSLE ((hsAdjoint Ψ).comp (KAB.comp Ψ)) KΦ)
    (hJAB :
      jOperator f₀ A B =
        (f₀ 0 : ℂ) • rightMul B + ((rep.b : ℝ) : ℂ) • leftMul A + KAB)
    (hJΦ :
      jOperator f₀ (hsAdjoint Ψ A) (hsAdjoint Ψ B) =
        (f₀ 0 : ℂ) • rightMul (hsAdjoint Ψ B) +
          ((rep.b : ℝ) : ℂ) • leftMul (hsAdjoint Ψ A) + KΦ) :
    HSLE
      ((hsAdjoint Ψ).comp ((jOperator f₀ A B).comp Ψ))
      (jOperator f₀ (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
  jOperator_dpi_of_explicit_kubo_terms_and_isUnitalTwoPositiveMap
    Ψ hΨ hA hB h0 (by exact_mod_cast rep.b.property)
    hkernel hJAB hJΦ

/--
Kubo--Ando representation gate for the direct strict DPI when positivity on
the open positive half-line supplies the missing endpoint coefficient
nonnegativity.
-/
theorem jOperator_dpi_of_positiveRayKuboAndoRep_explicit_terms_of_pos
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} {A B : Mₙ m}
    (rep : PositiveRayKuboAndoRep f₀)
    {KAB : HSOp m} {KΦ : HSOp n}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hpos : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 < f₀ x)
    (hkernel :
      HSLE ((hsAdjoint Ψ).comp (KAB.comp Ψ)) KΦ)
    (hJAB :
      jOperator f₀ A B =
        (f₀ 0 : ℂ) • rightMul B + ((rep.b : ℝ) : ℂ) • leftMul A + KAB)
    (hJΦ :
      jOperator f₀ (hsAdjoint Ψ A) (hsAdjoint Ψ B) =
        (f₀ 0 : ℂ) • rightMul (hsAdjoint Ψ B) +
          ((rep.b : ℝ) : ℂ) • leftMul (hsAdjoint Ψ A) + KΦ) :
    HSLE
      ((hsAdjoint Ψ).comp ((jOperator f₀ A B).comp Ψ))
      (jOperator f₀ (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
  jOperator_dpi_of_positiveRayKuboAndoRep_explicit_terms
    Ψ rep hΨ hA hB
    (positiveRayKuboAndoRep_endpoint_nonneg_of_pos rep hpos)
    hkernel hJAB hJΦ

end

end Quantum.TraceInequality.Loewner.HiaiPetz
