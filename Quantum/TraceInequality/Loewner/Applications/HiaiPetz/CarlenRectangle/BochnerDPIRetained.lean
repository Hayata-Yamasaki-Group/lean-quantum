/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.PositiveRayExpansion
import
  Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.PositiveRayExpansionRetained
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.BochnerDPI
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.KernelGRetained

/-!
# Carlen rectangle Bochner DPI stage

This module contains conjugation through Bochner integrals, G-kernel Bochner
integral DPI, Kubo direct DPI, and strict J-DPI from Kubo--Ando expansions.
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
The pointwise fixed-kernel DPI gives the almost-everywhere weighted kernel
inequality needed by the Bochner integral gate, because the representing
measure is supported on the positive ray and hence `1 + t ≥ 0` almost
everywhere.
-/
theorem jKuboKernelIntegral_ae_weightedKernel_HSLE_of_unitalTwoPositive_matrixPosDef
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {A B : Mₙ m}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hA : MatrixPosDef A)
    (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B)) :
    ∀ᵐ t ∂(rep.ν : MeasureTheory.Measure ℝ),
      HSLE
        ((hsAdjoint Ψ).comp
          (((((1 + t : ℝ) : ℂ) • jKuboKernel t A B).comp Ψ)))
        (((1 + t : ℝ) : ℂ) •
          jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) := by
  have ht_pos_ae :
      ∀ᵐ t ∂(rep.ν : MeasureTheory.Measure ℝ), t ∈ Set.Ioi (0 : ℝ) :=
    (MeasureTheory.mem_ae_iff).mpr rep.support
  filter_upwards [ht_pos_ae] with t ht
  have ht_nonneg : 0 ≤ t := le_of_lt (by simpa using ht)
  have hfactor_nonneg : 0 ≤ 1 + t := by linarith
  have hkernel :
      HSLE
        ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
        (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
    jKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef
      Ψ ht_nonneg hΨ hA hB hΨA hΨB
  have hscaled :
      HSLE
        (((1 + t : ℝ) : ℂ) •
          ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ)))
        (((1 + t : ℝ) : ℂ) •
          jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
    HSLE_smul_of_nonneg hfactor_nonneg hkernel
  simpa [ContinuousLinearMap.comp_smul] using hscaled

/--
The fixed-kernel DPI and the Bochner integral gate combine to give the
integrated kernel DPI, once integrability and conjugation with the integral are
supplied explicitly.
-/
theorem jKuboKernelIntegral_HSLE_of_unitalTwoPositive_matrixPosDef
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {A B : Mₙ m}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hA : MatrixPosDef A)
    (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B))
    (hIntLeft :
      MeasureTheory.Integrable
        (fun t : ℝ =>
          (hsAdjoint Ψ).comp
            (((((1 + t : ℝ) : ℂ) • jKuboKernel t A B).comp Ψ)))
        (rep.ν : MeasureTheory.Measure ℝ))
    (hIntΦ :
      MeasureTheory.Integrable
        (fun t : ℝ =>
          (((1 + t : ℝ) : ℂ) •
            jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)))
        (rep.ν : MeasureTheory.Measure ℝ))
    (hconj :
      ((hsAdjoint Ψ).comp ((jKuboKernelIntegral rep A B).comp Ψ)) =
        ∫ t : ℝ,
          (hsAdjoint Ψ).comp
            (((((1 + t : ℝ) : ℂ) • jKuboKernel t A B).comp Ψ))
          ∂(rep.ν : MeasureTheory.Measure ℝ)) :
    HSLE
      ((hsAdjoint Ψ).comp ((jKuboKernelIntegral rep A B).comp Ψ))
      (jKuboKernelIntegral rep (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
  jKuboKernelIntegral_HSLE_of_ae_HSLE
    Ψ rep hIntLeft hIntΦ hconj
    (jKuboKernelIntegral_ae_weightedKernel_HSLE_of_unitalTwoPositive_matrixPosDef
      Ψ rep hΨ hA hB hΨA hΨB)

/--
Integrated kernel DPI with conjugation-through-integral supplied by
`ContinuousLinearMap.integral_comp_comm`.  The analytic inputs are the two raw
Bochner integrability facts for the weighted fixed-kernel integrands, supplied by
`weighted_jKuboKernel_integrable_of_positiveRayKuboAndoRep` (used in
`jOperator_dpi_of_positiveRayKuboAndoRep` below).
-/
theorem jKuboKernelIntegral_HSLE_of_unitalTwoPositive_matrixPosDef_kernelIntegrable
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {A B : Mₙ m}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hA : MatrixPosDef A)
    (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B))
    (hIntAB :
      MeasureTheory.Integrable
        (fun t : ℝ => (((1 + t : ℝ) : ℂ) • jKuboKernel t A B))
        (rep.ν : MeasureTheory.Measure ℝ))
    (hIntΦ :
      MeasureTheory.Integrable
        (fun t : ℝ =>
          (((1 + t : ℝ) : ℂ) •
            jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)))
        (rep.ν : MeasureTheory.Measure ℝ)) :
    HSLE
      ((hsAdjoint Ψ).comp ((jKuboKernelIntegral rep A B).comp Ψ))
      (jKuboKernelIntegral rep (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
  jKuboKernelIntegral_HSLE_of_unitalTwoPositive_matrixPosDef
    Ψ rep hΨ hA hB hΨA hΨB
    (jKuboKernelIntegral_conj_integrand_integrable Ψ rep hIntAB)
    hIntΦ
    (jKuboKernelIntegral_conj_integral Ψ rep hIntAB)

/--
The pointwise `G` fixed-kernel DPI gives the almost-everywhere weighted kernel
inequality needed by the Bochner integral gate.
-/
theorem gKuboKernelIntegral_ae_weightedKernel_HSLE_of_unitalTwoPositive_matrixPosDef
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {X Y : Mₙ m}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hX : MatrixPosDef X)
    (hY : MatrixPosDef Y)
    (hΨX : MatrixPosDef (hsAdjoint Ψ X))
    (hΨY : MatrixPosDef (hsAdjoint Ψ Y)) :
    ∀ᵐ t ∂(rep.ν : MeasureTheory.Measure ℝ),
      HSLE
        ((hsAdjoint Ψ).comp
          (((((1 + t : ℝ) : ℂ) • gKuboKernel t X Y).comp Ψ)))
        (((1 + t : ℝ) : ℂ) •
          gKuboKernel t (hsAdjoint Ψ X) (hsAdjoint Ψ Y)) := by
  have ht_pos_ae :
      ∀ᵐ t ∂(rep.ν : MeasureTheory.Measure ℝ), t ∈ Set.Ioi (0 : ℝ) :=
    (MeasureTheory.mem_ae_iff).mpr rep.support
  filter_upwards [ht_pos_ae] with t ht
  have ht_nonneg : 0 ≤ t := le_of_lt (by simpa using ht)
  have hfactor_nonneg : 0 ≤ 1 + t := by linarith
  have hkernel :
      HSLE
        ((hsAdjoint Ψ).comp ((gKuboKernel t X Y).comp Ψ))
        (gKuboKernel t (hsAdjoint Ψ X) (hsAdjoint Ψ Y)) :=
    gKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef
      Ψ ht_nonneg hΨ hX hY hΨX hΨY
  have hscaled :
      HSLE
        (((1 + t : ℝ) : ℂ) •
          ((hsAdjoint Ψ).comp ((gKuboKernel t X Y).comp Ψ)))
        (((1 + t : ℝ) : ℂ) •
          gKuboKernel t (hsAdjoint Ψ X) (hsAdjoint Ψ Y)) :=
    HSLE_smul_of_nonneg hfactor_nonneg hkernel
  simpa [ContinuousLinearMap.comp_smul] using hscaled

/--
The `G` fixed-kernel DPI and the Bochner integral gate combine to give the
integrated kernel DPI.
-/
theorem gKuboKernelIntegral_HSLE_of_unitalTwoPositive_matrixPosDef
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {X Y : Mₙ m}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hX : MatrixPosDef X)
    (hY : MatrixPosDef Y)
    (hΨX : MatrixPosDef (hsAdjoint Ψ X))
    (hΨY : MatrixPosDef (hsAdjoint Ψ Y))
    (hIntLeft :
      MeasureTheory.Integrable
        (fun t : ℝ =>
          (hsAdjoint Ψ).comp
            (((((1 + t : ℝ) : ℂ) • gKuboKernel t X Y).comp Ψ)))
        (rep.ν : MeasureTheory.Measure ℝ))
    (hIntΦ :
      MeasureTheory.Integrable
        (fun t : ℝ =>
          (((1 + t : ℝ) : ℂ) •
            gKuboKernel t (hsAdjoint Ψ X) (hsAdjoint Ψ Y)))
        (rep.ν : MeasureTheory.Measure ℝ))
    (hconj :
      ((hsAdjoint Ψ).comp ((gKuboKernelIntegral rep X Y).comp Ψ)) =
        ∫ t : ℝ,
          (hsAdjoint Ψ).comp
            (((((1 + t : ℝ) : ℂ) • gKuboKernel t X Y).comp Ψ))
          ∂(rep.ν : MeasureTheory.Measure ℝ)) :
    HSLE
      ((hsAdjoint Ψ).comp ((gKuboKernelIntegral rep X Y).comp Ψ))
      (gKuboKernelIntegral rep (hsAdjoint Ψ X) (hsAdjoint Ψ Y)) :=
  gKuboKernelIntegral_HSLE_of_ae_HSLE
    Ψ rep hIntLeft hIntΦ hconj
    (gKuboKernelIntegral_ae_weightedKernel_HSLE_of_unitalTwoPositive_matrixPosDef
      Ψ rep hΨ hX hY hΨX hΨY)

/--
Integrated `G` fixed-kernel DPI with conjugation-through-integral supplied by
`ContinuousLinearMap.integral_comp_comm`.
-/
theorem gKuboKernelIntegral_HSLE_of_unitalTwoPositive_matrixPosDef_kernelIntegrable
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {X Y : Mₙ m}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hX : MatrixPosDef X)
    (hY : MatrixPosDef Y)
    (hΨX : MatrixPosDef (hsAdjoint Ψ X))
    (hΨY : MatrixPosDef (hsAdjoint Ψ Y))
    (hIntXY :
      MeasureTheory.Integrable
        (fun t : ℝ => (((1 + t : ℝ) : ℂ) • gKuboKernel t X Y))
        (rep.ν : MeasureTheory.Measure ℝ))
    (hIntΦ :
      MeasureTheory.Integrable
        (fun t : ℝ =>
          (((1 + t : ℝ) : ℂ) •
            gKuboKernel t (hsAdjoint Ψ X) (hsAdjoint Ψ Y)))
        (rep.ν : MeasureTheory.Measure ℝ)) :
    HSLE
      ((hsAdjoint Ψ).comp ((gKuboKernelIntegral rep X Y).comp Ψ))
      (gKuboKernelIntegral rep (hsAdjoint Ψ X) (hsAdjoint Ψ Y)) :=
  gKuboKernelIntegral_HSLE_of_unitalTwoPositive_matrixPosDef
    Ψ rep hΨ hX hY hΨX hΨY
    (gKuboKernelIntegral_conj_integrand_integrable Ψ rep hIntXY)
    hIntΦ
    (gKuboKernelIntegral_conj_integral Ψ rep hIntXY)

/--
Positive-ray Kubo--Ando representations satisfy the strict direct `G`-DPI in
the Loewner-native Carlen formulation.
-/
theorem gOperator_dpi_of_positiveRayKuboAndoRep
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} {X Y : Mₙ m}
    (rep : PositiveRayKuboAndoRep f₀)
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hX : MatrixPosDef X) (hY : MatrixPosDef Y)
    (hΨX : MatrixPosDef (hsAdjoint Ψ X))
    (hΨY : MatrixPosDef (hsAdjoint Ψ Y))
    (hpos : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 < f₀ x) :
    HSLE
      ((hsAdjoint Ψ).comp ((gOperator f₀ X Y).comp Ψ))
      (gOperator f₀ (hsAdjoint Ψ X) (hsAdjoint Ψ Y)) :=
  gOperator_dpi_of_positiveRayKuboAndoRep_explicit_terms_of_pos
    Ψ rep hΨ hX hY hpos
    (gKuboKernelIntegral_HSLE_of_unitalTwoPositive_matrixPosDef_kernelIntegrable
      Ψ rep hΨ hX hY hΨX hΨY
      (weighted_gKuboKernel_integrable_of_positiveRayKuboAndoRep rep hX hY)
      (weighted_gKuboKernel_integrable_of_positiveRayKuboAndoRep rep hΨX hΨY))
    (gOperator_expansion_of_positiveRayKuboAndoRep rep hX hY)
    (gOperator_expansion_of_positiveRayKuboAndoRep rep hΨX hΨY)

/-! ### Strict J-DPI from Kubo--Ando expansions -/
/--
Kubo--Ando direct DPI gate with the kernel terms fixed to the Bochner integrals
canonically determined by the representation.
-/
theorem jOperator_dpi_of_positiveRayKuboAndoRep_kernelIntegral_expansions
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} {A B : Mₙ m}
    (rep : PositiveRayKuboAndoRep f₀)
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hpos : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 < f₀ x)
    (hkernel :
      HSLE
        ((hsAdjoint Ψ).comp ((jKuboKernelIntegral rep A B).comp Ψ))
        (jKuboKernelIntegral rep (hsAdjoint Ψ A) (hsAdjoint Ψ B)))
    (hJAB :
      jOperator f₀ A B =
        (f₀ 0 : ℂ) • rightMul B + ((rep.b : ℝ) : ℂ) • leftMul A +
          jKuboKernelIntegral rep A B)
    (hJΦ :
      jOperator f₀ (hsAdjoint Ψ A) (hsAdjoint Ψ B) =
        (f₀ 0 : ℂ) • rightMul (hsAdjoint Ψ B) +
          ((rep.b : ℝ) : ℂ) • leftMul (hsAdjoint Ψ A) +
            jKuboKernelIntegral rep (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :
    HSLE
      ((hsAdjoint Ψ).comp ((jOperator f₀ A B).comp Ψ))
      (jOperator f₀ (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
  jOperator_dpi_of_positiveRayKuboAndoRep_explicit_terms_of_pos
    Ψ rep hΨ hA hB hpos hkernel hJAB hJΦ

/--
Kubo--Ando direct DPI gate with the kernel inequality supplied from raw
Bochner integrability of the two weighted fixed-kernel integrands.
-/
theorem jOperator_dpi_of_positiveRayKuboAndoRep_kernelIntegrable_expansions
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} {A B : Mₙ m}
    (rep : PositiveRayKuboAndoRep f₀)
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B))
    (hpos : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 < f₀ x)
    (hIntAB :
      MeasureTheory.Integrable
        (fun t : ℝ => (((1 + t : ℝ) : ℂ) • jKuboKernel t A B))
        (rep.ν : MeasureTheory.Measure ℝ))
    (hIntΦ :
      MeasureTheory.Integrable
        (fun t : ℝ =>
          (((1 + t : ℝ) : ℂ) •
            jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)))
        (rep.ν : MeasureTheory.Measure ℝ))
    (hJAB :
      jOperator f₀ A B =
        (f₀ 0 : ℂ) • rightMul B + ((rep.b : ℝ) : ℂ) • leftMul A +
          jKuboKernelIntegral rep A B)
    (hJΦ :
      jOperator f₀ (hsAdjoint Ψ A) (hsAdjoint Ψ B) =
        (f₀ 0 : ℂ) • rightMul (hsAdjoint Ψ B) +
          ((rep.b : ℝ) : ℂ) • leftMul (hsAdjoint Ψ A) +
            jKuboKernelIntegral rep (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :
    HSLE
      ((hsAdjoint Ψ).comp ((jOperator f₀ A B).comp Ψ))
      (jOperator f₀ (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
  jOperator_dpi_of_positiveRayKuboAndoRep_kernelIntegral_expansions
    Ψ rep hΨ hA hB hpos
    (jKuboKernelIntegral_HSLE_of_unitalTwoPositive_matrixPosDef_kernelIntegrable
      Ψ rep hΨ hA hB hΨA hΨB hIntAB hIntΦ)
    hJAB hJΦ

/--
Kubo--Ando direct DPI gate where the two `J`-operator expansions are supplied
as pre-right CFC expansions.  The endpoint multiplication algebra is handled by
`jOperator_expansion_of_hsCfcR_preright_expansion`.
-/
theorem jOperator_dpi_of_positiveRayKuboAndoRep_kernelIntegrable_preright_expansions
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} {A B : Mₙ m}
    (rep : PositiveRayKuboAndoRep f₀)
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B))
    (hpos : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 < f₀ x)
    (hIntAB :
      MeasureTheory.Integrable
        (fun t : ℝ => (((1 + t : ℝ) : ℂ) • jKuboKernel t A B))
        (rep.ν : MeasureTheory.Measure ℝ))
    (hIntΦ :
      MeasureTheory.Integrable
        (fun t : ℝ =>
          (((1 + t : ℝ) : ℂ) •
            jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)))
        (rep.ν : MeasureTheory.Measure ℝ))
    (hCfcAB :
      hsCfcR f₀ (jArg A B) =
        (f₀ 0 : ℂ) • (1 : HSOp m) +
          ((rep.b : ℝ) : ℂ) • jArg A B +
            jKuboKernelIntegral rep A B * rightMul (posInv B))
    (hCfcΦ :
      hsCfcR f₀ (jArg (hsAdjoint Ψ A) (hsAdjoint Ψ B)) =
        (f₀ 0 : ℂ) • (1 : HSOp n) +
          ((rep.b : ℝ) : ℂ) • jArg (hsAdjoint Ψ A) (hsAdjoint Ψ B) +
            jKuboKernelIntegral rep (hsAdjoint Ψ A) (hsAdjoint Ψ B) *
              rightMul (posInv (hsAdjoint Ψ B))) :
    HSLE
      ((hsAdjoint Ψ).comp ((jOperator f₀ A B).comp Ψ))
      (jOperator f₀ (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
  jOperator_dpi_of_positiveRayKuboAndoRep_kernelIntegrable_expansions
    Ψ rep hΨ hA hB hΨA hΨB hpos hIntAB hIntΦ
    (jOperator_expansion_of_hsCfcR_preright_expansion rep hB hCfcAB)
    (jOperator_expansion_of_hsCfcR_preright_expansion rep hΨB hCfcΦ)

/--
Kubo--Ando direct DPI from uniform suppliers for two analytic facts: raw
Bochner integrability of the weighted fixed kernels and pre-right CFC expansions
of the positive-ray Kubo--Ando representation.  Both are supplied in
`jOperator_dpi_of_positiveRayKuboAndoRep` below.
-/
theorem jOperator_dpi_of_positiveRayKuboAndoRep_prerightExpansion_integrability_suppliers
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} {A B : Mₙ m}
    (rep : PositiveRayKuboAndoRep f₀)
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B))
    (hpos : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 < f₀ x)
    (hInt :
      ∀ {k : ℕ} {X Y : Mₙ k},
        MatrixPosDef X → MatrixPosDef Y →
          MeasureTheory.Integrable
            (fun t : ℝ => (((1 + t : ℝ) : ℂ) • jKuboKernel t X Y))
            (rep.ν : MeasureTheory.Measure ℝ))
    (hCfc :
      ∀ {k : ℕ} {X Y : Mₙ k},
        MatrixPosDef X → MatrixPosDef Y →
          hsCfcR f₀ (jArg X Y) =
            (f₀ 0 : ℂ) • (1 : HSOp k) +
              ((rep.b : ℝ) : ℂ) • jArg X Y +
                jKuboKernelIntegral rep X Y * rightMul (posInv Y)) :
    HSLE
      ((hsAdjoint Ψ).comp ((jOperator f₀ A B).comp Ψ))
      (jOperator f₀ (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
  jOperator_dpi_of_positiveRayKuboAndoRep_kernelIntegrable_preright_expansions
    Ψ rep hΨ hA hB hΨA hΨB hpos
    (hInt (X := A) (Y := B) hA hB)
    (hInt (X := hsAdjoint Ψ A) (Y := hsAdjoint Ψ B) hΨA hΨB)
    (hCfc (X := A) (Y := B) hA hB)
    (hCfc (X := hsAdjoint Ψ A) (Y := hsAdjoint Ψ B) hΨA hΨB)

/--
Positive-ray Kubo--Ando representations satisfy the strict direct
Hiai--Petz DPI in the Loewner-native Carlen formulation.
-/
theorem jOperator_dpi_of_positiveRayKuboAndoRep
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} {A B : Mₙ m}
    (rep : PositiveRayKuboAndoRep f₀)
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B))
    (hpos : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 < f₀ x) :
    HSLE
      ((hsAdjoint Ψ).comp ((jOperator f₀ A B).comp Ψ))
      (jOperator f₀ (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
  jOperator_dpi_of_positiveRayKuboAndoRep_prerightExpansion_integrability_suppliers
    Ψ rep hΨ hA hB hΨA hΨB hpos
    (by
      intro k X Y hX hY
      exact weighted_jKuboKernel_integrable_of_positiveRayKuboAndoRep rep hX hY)
    (by
      intro k X Y hX hY
      exact positiveRayKuboAndoRep_hsCfcR_preright_expansion rep hX hY)

end

end Quantum.TraceInequality.Loewner.HiaiPetz
