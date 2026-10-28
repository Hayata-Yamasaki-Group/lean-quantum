/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.PositiveRayExpansion
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenKernel.FixedKernelOrder

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

/-! ### Conjugation through Bochner integrals for J-kernels -/
/-- Conjugating a Hilbert--Schmidt operator by a fixed Hilbert--Schmidt map. -/
noncomputable def hsConjugateCLM {n m : ℕ} (Ψ : HSMap n m) : HSOp m →L[ℂ] HSOp n :=
  (ContinuousLinearMap.compL ℂ (Mₙ n) (Mₙ m) (Mₙ n) (hsAdjoint Ψ)).comp
    ((ContinuousLinearMap.compL ℂ (Mₙ n) (Mₙ m) (Mₙ m)).flip Ψ)

/-- The conjugation operator expands to composition by `Ψ†`, then `K`, then `Ψ`. -/
@[simp]
theorem hsConjugateCLM_apply {n m : ℕ} (Ψ : HSMap n m) (K : HSOp m) :
    hsConjugateCLM Ψ K = (hsAdjoint Ψ).comp (K.comp Ψ) := by
  ext X
  rfl

/--
The conjugated kernel integrand is integrable as soon as the un-conjugated
Bochner kernel integrand is integrable.
-/
theorem jKuboKernelIntegral_conj_integrand_integrable
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {A B : Mₙ m}
    (hInt :
      MeasureTheory.Integrable
        (fun t : ℝ => (((1 + t : ℝ) : ℂ) • jKuboKernel t A B))
        (rep.ν : MeasureTheory.Measure ℝ)) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        (hsAdjoint Ψ).comp
          (((((1 + t : ℝ) : ℂ) • jKuboKernel t A B).comp Ψ)))
      (rep.ν : MeasureTheory.Measure ℝ) := by
  simpa only [hsConjugateCLM_apply] using (hsConjugateCLM Ψ).integrable_comp hInt

/--
Conjugation by a fixed Hilbert--Schmidt map commutes with the Bochner kernel
integral.
-/
theorem jKuboKernelIntegral_conj_integral
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {A B : Mₙ m}
    (hInt :
      MeasureTheory.Integrable
        (fun t : ℝ => (((1 + t : ℝ) : ℂ) • jKuboKernel t A B))
        (rep.ν : MeasureTheory.Measure ℝ)) :
    ((hsAdjoint Ψ).comp ((jKuboKernelIntegral rep A B).comp Ψ)) =
      ∫ t : ℝ,
        (hsAdjoint Ψ).comp
          (((((1 + t : ℝ) : ℂ) • jKuboKernel t A B).comp Ψ))
        ∂(rep.ν : MeasureTheory.Measure ℝ) := by
  have hcomm :=
    (hsConjugateCLM Ψ).integral_comp_comm
      (μ := (rep.ν : MeasureTheory.Measure ℝ)) hInt
  simpa only [jKuboKernelIntegral, hsConjugateCLM_apply] using hcomm.symm

/--
Bochner integration preserves the kernel DPI once the weighted fixed-kernel
integrands are integrable and ordered almost everywhere in Hilbert--Schmidt
quadratic-form order.
-/
theorem jKuboKernelIntegral_HSLE_of_ae_HSLE
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {A B : Mₙ m}
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
          ∂(rep.ν : MeasureTheory.Measure ℝ))
    (hle :
      ∀ᵐ t ∂(rep.ν : MeasureTheory.Measure ℝ),
        HSLE
          ((hsAdjoint Ψ).comp
            (((((1 + t : ℝ) : ℂ) • jKuboKernel t A B).comp Ψ)))
          (((1 + t : ℝ) : ℂ) •
            jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B))) :
    HSLE
      ((hsAdjoint Ψ).comp ((jKuboKernelIntegral rep A B).comp Ψ))
      (jKuboKernelIntegral rep (hsAdjoint Ψ A) (hsAdjoint Ψ B)) := by
  have hkernel :=
    HSLE_integral_of_ae hIntLeft hIntΦ hle
  rw [← hconj] at hkernel
  simpa [jKuboKernelIntegral] using hkernel

/--
The pointwise fixed-kernel DPI gives the almost-everywhere weighted kernel
inequality needed by the Bochner integral gate.  This version keeps the
pointwise kernel DPI as an explicit input instead of deriving it from
two-positivity.
-/
theorem jKuboKernelIntegral_ae_weightedKernel_HSLE_of_pointwise_kernel
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {A B : Mₙ m}
    (hkernel :
      ∀ {t : ℝ}, 0 ≤ t →
        HSLE
          ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
          (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B))) :
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
  have hkernel_t :
      HSLE
        ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
        (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
    hkernel ht_nonneg
  have hscaled :
      HSLE
        (((1 + t : ℝ) : ℂ) •
          ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ)))
        (((1 + t : ℝ) : ℂ) •
          jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
    HSLE_smul_of_nonneg hfactor_nonneg hkernel_t
  simpa [ContinuousLinearMap.comp_smul] using hscaled

/--
The fixed-kernel DPI and the Bochner integral gate combine to give the
integrated kernel DPI when the pointwise fixed-kernel DPI is supplied
explicitly.
-/
theorem jKuboKernelIntegral_HSLE_of_pointwise_kernel_kernelIntegrable
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {A B : Mₙ m}
    (hkernel :
      ∀ {t : ℝ}, 0 ≤ t →
        HSLE
          ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
          (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)))
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
  jKuboKernelIntegral_HSLE_of_ae_HSLE
    Ψ rep
    (jKuboKernelIntegral_conj_integrand_integrable Ψ rep hIntAB)
    hIntΦ
    (jKuboKernelIntegral_conj_integral Ψ rep hIntAB)
    (jKuboKernelIntegral_ae_weightedKernel_HSLE_of_pointwise_kernel
      Ψ rep hkernel)

/-! ### G-kernel Bochner integral DPI and Kubo direct DPI -/
/-- The conjugated `G`-kernel integrand is integrable as soon as the
un-conjugated Bochner kernel integrand is integrable. -/
theorem gKuboKernelIntegral_conj_integrand_integrable
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {X Y : Mₙ m}
    (hInt :
      MeasureTheory.Integrable
        (fun t : ℝ => (((1 + t : ℝ) : ℂ) • gKuboKernel t X Y))
        (rep.ν : MeasureTheory.Measure ℝ)) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        (hsAdjoint Ψ).comp
          (((((1 + t : ℝ) : ℂ) • gKuboKernel t X Y).comp Ψ)))
      (rep.ν : MeasureTheory.Measure ℝ) := by
  simpa only [hsConjugateCLM_apply] using (hsConjugateCLM Ψ).integrable_comp hInt

/-- Conjugation by a fixed Hilbert--Schmidt map commutes with the Bochner
integral of the `G` fixed kernels. -/
theorem gKuboKernelIntegral_conj_integral
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {X Y : Mₙ m}
    (hInt :
      MeasureTheory.Integrable
        (fun t : ℝ => (((1 + t : ℝ) : ℂ) • gKuboKernel t X Y))
        (rep.ν : MeasureTheory.Measure ℝ)) :
    ((hsAdjoint Ψ).comp ((gKuboKernelIntegral rep X Y).comp Ψ)) =
      ∫ t : ℝ,
        (hsAdjoint Ψ).comp
          (((((1 + t : ℝ) : ℂ) • gKuboKernel t X Y).comp Ψ))
        ∂(rep.ν : MeasureTheory.Measure ℝ) := by
  have hcomm :=
    (hsConjugateCLM Ψ).integral_comp_comm
      (μ := (rep.ν : MeasureTheory.Measure ℝ)) hInt
  simpa only [gKuboKernelIntegral, hsConjugateCLM_apply] using hcomm.symm

/--
Bochner integration preserves the `G` fixed-kernel DPI once the weighted
integrands are integrable and ordered almost everywhere in
Hilbert--Schmidt quadratic-form order.
-/
theorem gKuboKernelIntegral_HSLE_of_ae_HSLE
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    {X Y : Mₙ m}
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
          ∂(rep.ν : MeasureTheory.Measure ℝ))
    (hle :
      ∀ᵐ t ∂(rep.ν : MeasureTheory.Measure ℝ),
        HSLE
          ((hsAdjoint Ψ).comp
            (((((1 + t : ℝ) : ℂ) • gKuboKernel t X Y).comp Ψ)))
          (((1 + t : ℝ) : ℂ) •
            gKuboKernel t (hsAdjoint Ψ X) (hsAdjoint Ψ Y))) :
    HSLE
      ((hsAdjoint Ψ).comp ((gKuboKernelIntegral rep X Y).comp Ψ))
      (gKuboKernelIntegral rep (hsAdjoint Ψ X) (hsAdjoint Ψ Y)) := by
  have hkernel :=
    HSLE_integral_of_ae hIntLeft hIntΦ hle
  rw [← hconj] at hkernel
  simpa [gKuboKernelIntegral] using hkernel

/--
Positive-ray Kubo--Ando direct DPI from a Schwarz endpoint input and an
explicit pointwise fixed-kernel DPI.  This separates the
Schur--Lieb--Ruskai-type pointwise kernel input from the endpoint and
Bochner-integral bookkeeping.  For unital two-positive maps this input is
`jKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef` (`FixedKernelGate.lean`).
-/
theorem jOperator_dpi_of_positiveRayKuboAndoRep_pointwiseKernel_schwarzMap
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} {A B : Mₙ m}
    (rep : PositiveRayKuboAndoRep f₀)
    (hSch : ∀ X : Mₙ n,
      Matrix.conjTranspose (Ψ X) * Ψ X ≤ Ψ (Matrix.conjTranspose X * X))
    (hstar : ∀ X : Mₙ n, Ψ (Matrix.conjTranspose X) = Matrix.conjTranspose (Ψ X))
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B))
    (hpos : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 < f₀ x)
    (hkernel :
      ∀ {t : ℝ}, 0 ≤ t →
        HSLE
          ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
          (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)))
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
  jOperator_dpi_of_positiveRayKuboAndoRep_explicit_terms_of_pos_and_schwarzMap
    Ψ rep hSch hstar hA hB hpos
    (jKuboKernelIntegral_HSLE_of_pointwise_kernel_kernelIntegrable
      Ψ rep hkernel
      (hInt (X := A) (Y := B) hA hB)
      (hInt (X := hsAdjoint Ψ A) (Y := hsAdjoint Ψ B) hΨA hΨB))
    (jOperator_expansion_of_hsCfcR_preright_expansion rep hB
      (hCfc (X := A) (Y := B) hA hB))
    (jOperator_expansion_of_hsCfcR_preright_expansion rep hΨB
      (hCfc (X := hsAdjoint Ψ A) (Y := hsAdjoint Ψ B) hΨA hΨB))

end

end Quantum.TraceInequality.Loewner.HiaiPetz
