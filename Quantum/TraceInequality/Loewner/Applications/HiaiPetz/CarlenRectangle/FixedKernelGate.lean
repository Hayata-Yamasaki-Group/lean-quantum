/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

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
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenKernel.FixedKernelOrder
import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenKernel.InverseTermReduction

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

/-! ### Fixed-kernel DPI gates from inverse-form inequalities -/
/--
Pointwise direct fixed-kernel DPI follows from the corresponding inverse-form
fixed-kernel DPI by the square-root rectangle step.  This version keeps the
inverse-form inequality explicit and uses only the positive-definite endpoint
facts for the two kernels.
-/
theorem jKuboKernel_dpi_of_invForm_HSLE_and_matrixPosDef
    {n m : ℕ} (Ψ : HSMap n m) {t : ℝ} (ht : 0 ≤ t) {A B : Mₙ m}
    (hA : MatrixPosDef A)
    (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B))
    (hinv :
      HSLE
        (Ψ.comp
          ((jKuboKernelInvForm t (hsAdjoint Ψ A) (hsAdjoint Ψ B)).comp
            (hsAdjoint Ψ)))
        (jKuboKernelInvForm t A B)) :
    HSLE
      ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
      (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) := by
  have hInvTA_sa : IsSelfAdjoint (jKuboKernelInvForm t A B) :=
    jKuboKernelInvForm_isSelfAdjoint_of_matrixPosDef hA hB
  have hInvTΦ_sa :
      IsSelfAdjoint (jKuboKernelInvForm t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
    jKuboKernelInvForm_isSelfAdjoint_of_matrixPosDef hΨA hΨB
  have hσInvTA : spectrum ℝ (jKuboKernelInvForm t A B) ⊆ Set.Ioi (0 : ℝ) :=
    jKuboKernelInvForm_spectrum_subset_Ioi_of_matrixPosDef ht hA hB
  have hσInvTΦ :
      spectrum ℝ (jKuboKernelInvForm t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) ⊆
        Set.Ioi (0 : ℝ) :=
    jKuboKernelInvForm_spectrum_subset_Ioi_of_matrixPosDef ht hΨA hΨB
  have hInvTA_unit : IsUnit (jKuboKernelInvForm t A B) :=
    jKuboKernelInvForm_isUnit_of_matrixPosDef ht hA hB
  have hInvTΦ_unit :
      IsUnit (jKuboKernelInvForm t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
    jKuboKernelInvForm_isUnit_of_matrixPosDef ht hΨA hΨB
  have hTA_sa : IsSelfAdjoint (jKuboKernel t A B) :=
    jKuboKernel_isSelfAdjoint_of_invForm_facts hInvTA_sa hσInvTA
  have hTΦ_sa :
      IsSelfAdjoint (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
    jKuboKernel_isSelfAdjoint_of_invForm_facts hInvTΦ_sa hσInvTΦ
  have hσTA : spectrum ℝ (jKuboKernel t A B) ⊆ Set.Ioi (0 : ℝ) :=
    jKuboKernel_spectrum_subset_Ioi_of_invForm_facts hInvTA_sa hσInvTA
  have hσTΦ :
      spectrum ℝ (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) ⊆ Set.Ioi (0 : ℝ) :=
    jKuboKernel_spectrum_subset_Ioi_of_invForm_facts hInvTΦ_sa hσInvTΦ
  have hInvTA : Ring.inverse (jKuboKernel t A B) = jKuboKernelInvForm t A B :=
    jKuboKernel_inverse_eq_invForm_of_invForm_facts hInvTA_unit
  have hInvTΦ :
      Ring.inverse (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) =
        jKuboKernelInvForm t (hsAdjoint Ψ A) (hsAdjoint Ψ B) :=
    jKuboKernel_inverse_eq_invForm_of_invForm_facts hInvTΦ_unit
  have hrect :
      HSLE
        (carlenRectInverseOp Ψ (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)))
        (Ring.inverse (jKuboKernel t A B)) := by
    simpa [carlenRectInverseOp, hInvTA, hInvTΦ] using hinv
  have hdirect :=
    carlenRectangle_inverse_to_direct
      Ψ hTA_sa hTΦ_sa hσTA hσTΦ hrect
  simpa [carlenRectDirectOp] using hdirect

/-! ### J-operator Kubo endpoints and explicit kernel assembly -/
/--
Algebraic Kubo--Ando expansion gate for the direct strict DPI.

Once `jOperator f₀ A B` and `jOperator f₀ (Ψ†A) (Ψ†B)` have been expanded into
endpoint, slope, and kernel parts, the direct DPI follows by adding the three
corresponding Hilbert--Schmidt quadratic-form inequalities.  The CFC/Bochner
calculation which supplies those two expansions is intentionally not hidden in
this theorem.
-/
theorem jOperator_dpi_of_explicit_kubo_terms
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} {A B : Mₙ m}
    {c b : ℝ} {KAB : HSOp m} {KΦ : HSOp n}
    (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hright :
      HSLE ((hsAdjoint Ψ).comp ((rightMul B).comp Ψ))
        (rightMul (hsAdjoint Ψ B)))
    (hleft :
      HSLE ((hsAdjoint Ψ).comp ((leftMul A).comp Ψ))
        (leftMul (hsAdjoint Ψ A)))
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
      (jOperator f₀ (hsAdjoint Ψ A) (hsAdjoint Ψ B)) := by
  have hright_scaled :
      HSLE
        ((c : ℂ) • ((hsAdjoint Ψ).comp ((rightMul B).comp Ψ)))
        ((c : ℂ) • rightMul (hsAdjoint Ψ B)) :=
    HSLE_smul_of_nonneg hc hright
  have hleft_scaled :
      HSLE
        ((b : ℂ) • ((hsAdjoint Ψ).comp ((leftMul A).comp Ψ)))
        ((b : ℂ) • leftMul (hsAdjoint Ψ A)) :=
    HSLE_smul_of_nonneg hb hleft
  have hsum :=
    HSLE_add (HSLE_add hright_scaled hleft_scaled) hkernel
  convert hsum using 1
  ext X i j
  simp only [hJAB, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]
  rw [map_add, map_add, map_smul, map_smul]

/--
Explicit Kubo--Ando expansion gate with the endpoint and slope terms supplied
directly by a Schwarz inequality for `Ψ`, plus conjugate-transpose preservation.
The fixed-kernel term remains an explicit input.
-/
theorem jOperator_dpi_of_explicit_kubo_terms_and_schwarzMap
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} {A B : Mₙ m}
    {c b : ℝ} {KAB : HSOp m} {KΦ : HSOp n}
    (hSch : ∀ X : Mₙ n,
      Matrix.conjTranspose (Ψ X) * Ψ X ≤ Ψ (Matrix.conjTranspose X * X))
    (hstar : ∀ X : Mₙ n, Ψ (Matrix.conjTranspose X) = Matrix.conjTranspose (Ψ X))
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
    (rightMul_dpi_of_schwarzMap Ψ hSch hB)
    (leftMul_dpi_of_schwarzMap_of_map_conjTranspose Ψ hSch hstar hA)
    hkernel hJAB hJΦ

/--
If a Kubo--Ando representative is strictly positive on the open positive
half-line, then its endpoint coefficient is nonnegative.  The proof uses the
right-continuity at `0` supplied by the Kubo--Ando representation.
-/
theorem positiveRayKuboAndoRep_endpoint_nonneg_of_pos
    {f₀ : ℝ → ℝ} (rep : PositiveRayKuboAndoRep f₀)
    (hpos : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 < f₀ x) :
    0 ≤ f₀ 0 := by
  have hclosed : OperatorMonotoneOnClosedPositive.{0} f₀ :=
    operatorMonotoneOnClosedPositive_of_positiveRayKuboAndoRep rep
  have hcont :=
    hclosed.right_continuous_at_zero
  have hev : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), f₀ x ∈ Set.Ici (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact le_of_lt (hpos hx)
  exact isClosed_Ici.mem_of_tendsto hcont hev

/--
Kubo--Ando representation gate for the direct strict DPI where the endpoint
terms are supplied by a Schwarz inequality and conjugate-transpose preservation,
while the integrated fixed-kernel inequality is kept as the only operator
inequality input beyond the representation expansion.
-/
theorem jOperator_dpi_of_positiveRayKuboAndoRep_explicit_terms_of_pos_and_schwarzMap
    {n m : ℕ} (Ψ : HSMap n m) {f₀ : ℝ → ℝ} {A B : Mₙ m}
    (rep : PositiveRayKuboAndoRep f₀)
    {KAB : HSOp m} {KΦ : HSOp n}
    (hSch : ∀ X : Mₙ n,
      Matrix.conjTranspose (Ψ X) * Ψ X ≤ Ψ (Matrix.conjTranspose X * X))
    (hstar : ∀ X : Mₙ n, Ψ (Matrix.conjTranspose X) = Matrix.conjTranspose (Ψ X))
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
  jOperator_dpi_of_explicit_kubo_terms_and_schwarzMap
    Ψ hSch hstar hA hB
    (positiveRayKuboAndoRep_endpoint_nonneg_of_pos rep hpos)
    (by exact_mod_cast rep.b.property)
    hkernel hJAB hJΦ

/-! ### Hilbert--Schmidt order under Bochner integration -/
/-- The real quadratic form associated with a test Hilbert--Schmidt matrix. -/
noncomputable def hsQuadraticFormCLM {n : ℕ} (X : Mₙ n) : HSOp n →L[ℝ] ℝ :=
  (RCLike.reCLM : ℂ →L[ℝ] ℝ).comp
    (((innerSL ℂ X).comp (ContinuousLinearMap.apply ℂ (Mₙ n) X)).restrictScalars ℝ)

/-- Bochner integration preserves the theorem-facing Hilbert--Schmidt order. -/
theorem HSLE_integral_of_ae {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {n : ℕ} {S T : α → HSOp n}
    (hS : MeasureTheory.Integrable S μ) (hT : MeasureTheory.Integrable T μ)
    (hle : ∀ᵐ a ∂μ, HSLE (S a) (T a)) :
    HSLE (∫ a, S a ∂μ) (∫ a, T a ∂μ) := by
  rw [HSLE]
  intro X
  let q : HSOp n →L[ℝ] ℝ := hsQuadraticFormCLM X
  have hD : MeasureTheory.Integrable (fun a : α => T a - S a) μ := hT.sub hS
  have hq_nonneg :
      0 ≤ᵐ[μ] fun a : α => q (T a - S a) := by
    filter_upwards [hle] with a ha
    have hqa : 0 ≤ Complex.re (Matrix.trace (Matrix.conjTranspose X * ((T a - S a) X))) :=
      ha X
    have htrace :
        q (T a - S a) =
          Complex.re (Matrix.trace (((T a - S a) X) * Matrix.conjTranspose X)) := by
      rfl
    rw [htrace]
    have htrace_comm :
        Matrix.trace (((T a - S a) X) * Matrix.conjTranspose X) =
          Matrix.trace (Matrix.conjTranspose X * ((T a - S a) X)) :=
      Matrix.trace_mul_comm _ _
    rw [htrace_comm]
    exact hqa
  have hq_integral_nonneg : 0 ≤ ∫ a, q (T a - S a) ∂μ :=
    MeasureTheory.integral_nonneg_of_ae hq_nonneg
  have hq_comm :
      ∫ a, q (T a - S a) ∂μ = q (∫ a, T a - S a ∂μ) :=
    q.integral_comp_comm hD
  have hdiff : (∫ a, T a ∂μ) - (∫ a, S a ∂μ) = ∫ a, T a - S a ∂μ := by
    rw [MeasureTheory.integral_sub hT hS]
  rw [hq_comm] at hq_integral_nonneg
  rw [hdiff]
  have htrace :
      q (∫ a, T a - S a ∂μ) =
        Complex.re
          (Matrix.trace
            (((∫ a, T a - S a ∂μ) X) * Matrix.conjTranspose X)) := by
    rfl
  rw [htrace] at hq_integral_nonneg
  have htrace_comm :
      Matrix.trace (((∫ a, T a - S a ∂μ) X) * Matrix.conjTranspose X) =
        Matrix.trace (Matrix.conjTranspose X * ((∫ a, T a - S a ∂μ) X)) :=
    Matrix.trace_mul_comm _ _
  rw [htrace_comm] at hq_integral_nonneg
  exact hq_integral_nonneg

/--
The Bochner-integrated fixed-kernel term determined by a positive-ray
Kubo--Ando representation.  The scalar factor `(1 + t)` converts the
positive-ray Kubo--Ando kernel into Carlen's fixed kernel after multiplying by
the right endpoint operator.
-/
noncomputable def jKuboKernelIntegral {n : ℕ} {f₀ : ℝ → ℝ}
    (rep : PositiveRayKuboAndoRep f₀) (A B : Mₙ n) : HSOp n :=
  ∫ t : ℝ, (((1 + t : ℝ) : ℂ) • jKuboKernel t A B)
    ∂(rep.ν : MeasureTheory.Measure ℝ)

end

end Quantum.TraceInequality.Loewner.HiaiPetz
