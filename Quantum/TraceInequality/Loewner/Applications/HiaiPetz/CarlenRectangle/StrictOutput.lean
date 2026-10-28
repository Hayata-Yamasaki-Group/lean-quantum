/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenRectangle.ConditionOne

/-!
# Carlen rectangle strict-output stage

This module contains the theorem-facing Carlen rectangle declarations moved
from the aggregate rectangle file.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

universe u

open MeasureTheory

open scoped Matrix.Norms.Frobenius MatrixOrder CStarAlgebra ComplexOrder FinMatrixCStar

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

/-! ### Positive maps, output positivity, and adjoint star preservation -/
/--
A theorem-facing positive-definite matrix is bounded below by a positive real
scalar multiple of the identity.
-/
theorem matrixPosDef_exists_pos_algebraMap_le {n : ℕ} {A : Mₙ n}
    (hA : MatrixPosDef A) :
    ∃ r > 0, algebraMap ℝ (Mₙ n) r ≤ A := by
  classical
  letI : PartialOrder (Mₙ n) := Matrix.instPartialOrder
  letI : StarOrderedRing (Mₙ n) := Matrix.instStarOrderedRing
  letI : ContinuousFunctionalCalculus ℂ (Mₙ n) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus ℝ (Mₙ n) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  by_cases hnon : Nonempty (Fin n)
  · letI : Nonempty (Fin n) := hnon
    letI : NonnegSpectrumClass ℝ (Mₙ n) :=
      @CStarAlgebra.instNonnegSpectrumClass (Mₙ n) inferInstance inferInstance inferInstance
    have hsynth : NonnegSpectrumClass ℝ (Mₙ n) := inferInstance
    have hstrict : IsStrictlyPositive A :=
      (matrixPosDef_posDef hA).isStrictlyPositive
    have hiff :=
      @CFC.exists_pos_algebraMap_le_iff (Mₙ n)
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        hsynth inferInstance inferInstance A hA.1
    exact hiff.mpr (fun x hx =>
      @IsStrictlyPositive.spectrum_pos (Mₙ n) ℝ
        inferInstance inferInstance inferInstance inferInstance inferInstance
        hsynth A hstrict x hx)
  · haveI : IsEmpty (Fin n) := not_nonempty_iff.mp hnon
    refine ⟨1, by norm_num, ?_⟩
    have hEq : algebraMap ℝ (Mₙ n) (1 : ℝ) = A := Subsingleton.elim _ _
    rw [hEq]

/--
A positive Hilbert--Schmidt map sends theorem-facing positive-definite inputs to
positive-definite outputs when the image of the identity is positive definite.
-/
theorem isPositiveMap_matrixPosDef_of_map_one_matrixPosDef {n m : ℕ}
    (Φ : HSMap n m)
    (hpos : IsPositiveMap Φ)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n)))
    {A : Mₙ n} (hA : MatrixPosDef A) :
    MatrixPosDef (Φ A) := by
  classical
  obtain ⟨r, hr_pos, hr_le⟩ := matrixPosDef_exists_pos_algebraMap_le hA
  have hmap_nonneg : 0 ≤ Φ (A - algebraMap ℝ (Mₙ n) r) :=
    hpos (sub_nonneg.mpr hr_le)
  have hmap_nonneg' : 0 ≤ Φ A - (r : ℂ) • Φ (1 : Mₙ n) := by
    simpa [ContinuousLinearMap.map_sub, Algebra.algebraMap_eq_smul_one,
      Complex.real_smul] using hmap_nonneg
  have hle : (r : ℂ) • Φ (1 : Mₙ n) ≤ Φ A :=
    sub_nonneg.mp hmap_nonneg'
  have hlower_posDef : ((r : ℝ) • Φ (1 : Mₙ n)).PosDef :=
    (matrixPosDef_posDef hΦ1).smul hr_pos
  have hlower_eq :
      ((r : ℝ) • Φ (1 : Mₙ n)) = (r : ℂ) • Φ (1 : Mₙ n) := by
    ext i j
    change r • (Φ (1 : Mₙ n)) i j = (r : ℂ) * (Φ (1 : Mₙ n)) i j
    rw [Complex.real_smul]
  have hlower_strict : IsStrictlyPositive ((r : ℂ) • Φ (1 : Mₙ n)) := by
    rw [← hlower_eq]
    exact hlower_posDef.isStrictlyPositive
  have hstrict : IsStrictlyPositive (Φ A) :=
    IsStrictlyPositive.of_le hlower_strict hle
  exact matrixPosDef_of_posDef ((Matrix.isStrictlyPositive_iff_posDef).mp hstrict)

/--
A theorem-facing positive Hilbert--Schmidt map preserves conjugate transpose.
The proof decomposes an arbitrary matrix into four positive elements in the
finite C*-algebra and applies positivity to each positive summand.
-/
theorem isPositiveMap_map_conjTranspose {n m : ℕ} {Φ : HSMap n m}
    (hΦ : IsPositiveMap Φ) (X : Mₙ n) :
    Φ (Matrix.conjTranspose X) = Matrix.conjTranspose (Φ X) := by
  classical
  letI : PartialOrder (Mₙ n) := Matrix.instPartialOrder
  letI : StarRing (Mₙ n) := Matrix.instStarRing
  letI : StarOrderedRing (Mₙ n) := Matrix.instStarOrderedRing
  let hpo : PartialOrder (Mₙ n) := Matrix.instPartialOrder
  let hsor : @StarOrderedRing (Mₙ n) inferInstance hpo inferInstance :=
    Matrix.instStarOrderedRing
  obtain ⟨P, hPpos, _hPnorm, hX⟩ :=
    @CStarAlgebra.exists_sum_four_nonneg (Mₙ n) inferInstance hpo hsor X
  have hPstar : ∀ i : Fin 4, Matrix.conjTranspose (P i) = P i := by
    intro i
    simpa using (hPpos i).star_eq
  have hΦPstar : ∀ i : Fin 4, Matrix.conjTranspose (Φ (P i)) = Φ (P i) := by
    intro i
    have hnon : 0 ≤ Φ (P i) := hΦ (hPpos i)
    simpa using hnon.star_eq
  have hXstar :
      Matrix.conjTranspose X =
        ∑ i : Fin 4, (-Complex.I) ^ (i : ℕ) • P i := by
    rw [hX]
    ext a b
    have hentry : ∀ i : Fin 4, star ((P i) b a) = (P i) a b := by
      intro i
      have h := congr_fun (congr_fun (hPstar i) a) b
      simpa [Matrix.conjTranspose_apply] using h
    change star ((∑ i : Fin 4, Complex.I ^ (i : ℕ) • P i) b a) =
      ∑ i : Fin 4, (-Complex.I) ^ (i : ℕ) * (P i) a b
    rw [Matrix.sum_apply, star_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    simp [Matrix.smul_apply, hentry i]
  have hmapX :
      Φ X = ∑ i : Fin 4, Complex.I ^ (i : ℕ) • Φ (P i) := by
    rw [hX]
    calc
      Φ (∑ i : Fin 4, Complex.I ^ (i : ℕ) • P i) =
          ∑ i : Fin 4, Φ (Complex.I ^ (i : ℕ) • P i) :=
        map_sum Φ.toLinearMap.toAddMonoidHom
          (fun i : Fin 4 => Complex.I ^ (i : ℕ) • P i) Finset.univ
      _ = ∑ i : Fin 4, Complex.I ^ (i : ℕ) • Φ (P i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Φ.map_smul (Complex.I ^ (i : ℕ)) (P i)
  calc
    Φ (Matrix.conjTranspose X)
        = ∑ i : Fin 4, (-Complex.I) ^ (i : ℕ) • Φ (P i) := by
          rw [hXstar]
          calc
            Φ (∑ i : Fin 4, (-Complex.I) ^ (i : ℕ) • P i) =
                ∑ i : Fin 4, Φ ((-Complex.I) ^ (i : ℕ) • P i) :=
              map_sum Φ.toLinearMap.toAddMonoidHom
                (fun i : Fin 4 => (-Complex.I) ^ (i : ℕ) • P i) Finset.univ
            _ = ∑ i : Fin 4, (-Complex.I) ^ (i : ℕ) • Φ (P i) := by
              apply Finset.sum_congr rfl
              intro i _
              exact Φ.map_smul ((-Complex.I) ^ (i : ℕ)) (P i)
    _ = Matrix.conjTranspose (Φ X) := by
          rw [hmapX]
          symm
          ext a b
          have hentry : ∀ i : Fin 4, star ((Φ (P i)) b a) = (Φ (P i)) a b := by
            intro i
            have h := congr_fun (congr_fun (hΦPstar i) a) b
            simpa [Matrix.conjTranspose_apply] using h
          change star ((∑ i : Fin 4, Complex.I ^ (i : ℕ) • Φ (P i)) b a) =
            ∑ i : Fin 4, (-Complex.I) ^ (i : ℕ) * (Φ (P i)) a b
          rw [Matrix.sum_apply, star_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          simp [Matrix.smul_apply, hentry i]

/--
If a theorem-facing positive Hilbert--Schmidt map preserves adjoints, then so
does its Hilbert--Schmidt adjoint.  This is the trace-pairing transfer used by
the strict-output surface.
-/
theorem hsAdjoint_map_conjTranspose_of_isPositiveMap {n m : ℕ}
    {Φ : HSMap n m} (hΦ : IsPositiveMap Φ) (Y : Mₙ m) :
    hsAdjoint Φ (Matrix.conjTranspose Y) = Matrix.conjTranspose (hsAdjoint Φ Y) := by
  classical
  rw [Matrix.ext_iff_trace_mul_left]
  intro X
  calc
    Matrix.trace (X * hsAdjoint Φ (Matrix.conjTranspose Y)) =
        Matrix.trace (Matrix.conjTranspose (Matrix.conjTranspose X) *
          hsAdjoint Φ (Matrix.conjTranspose Y)) := by
      simp
    _ = Matrix.trace (Matrix.conjTranspose (Φ (Matrix.conjTranspose X)) *
          Matrix.conjTranspose Y) :=
      trace_hsAdjoint_eq Φ (Matrix.conjTranspose X) (Matrix.conjTranspose Y)
    _ = Matrix.trace (Φ X * Matrix.conjTranspose Y) := by
      rw [isPositiveMap_map_conjTranspose hΦ X]
      simp
    _ = Matrix.trace (X * Matrix.conjTranspose (hsAdjoint Φ Y)) :=
      (trace_mul_hsAdjoint_conjTranspose' Φ X Y).symm

/-! ### Schwarz endpoint inversion and residual kernel input -/
/-- The ring inverse of left multiplication by a positive-definite matrix is left
multiplication by the theorem-facing matrix inverse. -/
theorem ringInverse_leftMul_eq_leftMul_posInv_of_matrixPosDef {n : ℕ}
    {A : Mₙ n} (hA : MatrixPosDef A) :
    Ring.inverse (leftMul A : HSOp n) = leftMul (posInv A) := by
  let u : (HSOp n)ˣ :=
    { val := leftMul A
      inv := leftMul (posInv A)
      val_inv := leftMul_mul_leftMul_posInv_of_matrixPosDef hA
      inv_val := leftMul_posInv_mul_leftMul_of_matrixPosDef hA }
  change Ring.inverse (↑u : HSOp n) = leftMul (posInv A)
  rw [Ring.inverse_unit u]
  rfl

/-- The ring inverse of right multiplication by a positive-definite matrix is
right multiplication by the theorem-facing matrix inverse. -/
theorem ringInverse_rightMul_eq_rightMul_posInv_of_matrixPosDef {n : ℕ}
    {B : Mₙ n} (hB : MatrixPosDef B) :
    Ring.inverse (rightMul B : HSOp n) = rightMul (posInv B) := by
  let u : (HSOp n)ˣ :=
    { val := rightMul B
      inv := rightMul (posInv B)
      val_inv := rightMul_mul_rightMul_posInv_of_matrixPosDef hB
      inv_val := rightMul_posInv_mul_rightMul_of_matrixPosDef hB }
  change Ring.inverse (↑u : HSOp n) = rightMul (posInv B)
  rw [Ring.inverse_unit u]
  rfl

/-- Positive real spectrum for a left multiplication endpoint. -/
theorem leftMul_spectrum_subset_Ioi_of_matrixPosDef {n : ℕ}
    {A : Mₙ n} (hA : MatrixPosDef A) :
    spectrum ℝ (leftMul A : HSOp n) ⊆ Set.Ioi (0 : ℝ) := by
  intro x hx
  exact
    @IsStrictlyPositive.spectrum_pos (HSOp n) ℝ
      inferInstance
      (instCarlenRectangleHSOpPartialOrder (n := n))
      inferInstance
      inferInstance
      inferInstance
      (instCarlenRectangleHSOpNonnegSpectrumClass (n := n))
      (leftMul A : HSOp n)
      (leftMul_isStrictlyPositive_of_matrix_posDef (matrixPosDef_posDef hA)) x hx

/-- Positive real spectrum for a right multiplication endpoint. -/
theorem rightMul_spectrum_subset_Ioi_of_matrixPosDef {n : ℕ}
    {B : Mₙ n} (hB : MatrixPosDef B) :
    spectrum ℝ (rightMul B : HSOp n) ⊆ Set.Ioi (0 : ℝ) := by
  intro x hx
  exact
    @IsStrictlyPositive.spectrum_pos (HSOp n) ℝ
      inferInstance
      (instCarlenRectangleHSOpPartialOrder (n := n))
      inferInstance
      inferInstance
      inferInstance
      (instCarlenRectangleHSOpNonnegSpectrumClass (n := n))
      (rightMul B : HSOp n)
      (rightMul_isStrictlyPositive_of_matrix_posDef (matrixPosDef_posDef hB)) x hx

/--
The Schwarz endpoint DPI for the Hilbert--Schmidt adjoint, after the Carlen
square-root rectangle reversal, supplies the left inverse endpoint DPI.
-/
theorem leftMul_posInv_dpi_of_hsAdjointSchwarz {n m : ℕ}
    (Φ : HSMap n m) {A : Mₙ n}
    (hSch : HSAdjointSchwarz Φ)
    (hstar : ∀ X : Mₙ m,
      (hsAdjoint Φ) (Matrix.conjTranspose X) =
        Matrix.conjTranspose ((hsAdjoint Φ) X))
    (hA : MatrixPosDef A) (hΦA : MatrixPosDef (Φ A)) :
    HSLE
      ((hsAdjoint Φ).comp ((leftMul (posInv (Φ A))).comp Φ))
      (leftMul (posInv A)) := by
  let Ψ : HSMap m n := hsAdjoint Φ
  have hSchΨ : ∀ X : Mₙ m,
      Matrix.conjTranspose (Ψ X) * Ψ X ≤ Ψ (Matrix.conjTranspose X * X) := by
    intro X
    simpa [Ψ, HSAdjointSchwarz] using hSch X
  have hstarΨ : ∀ X : Mₙ m,
      Ψ (Matrix.conjTranspose X) = Matrix.conjTranspose (Ψ X) := by
    intro X
    simpa [Ψ] using hstar X
  have hdirect :
      HSLE
        (Φ.comp ((leftMul A).comp (hsAdjoint Φ)))
        (leftMul (Φ A)) := by
    simpa [Ψ, hsAdjoint_hsAdjoint] using
      (leftMul_dpi_of_schwarzMap_of_map_conjTranspose Ψ hSchΨ hstarΨ hA)
  have hTA_sa : IsSelfAdjoint (leftMul A : HSOp n) :=
    leftMul_isSelfAdjoint_of_matrix_isSelfAdjoint hA.1
  have hTΦ_sa : IsSelfAdjoint (leftMul (Φ A) : HSOp m) :=
    leftMul_isSelfAdjoint_of_matrix_isSelfAdjoint hΦA.1
  have hσTA : spectrum ℝ (leftMul A : HSOp n) ⊆ Set.Ioi (0 : ℝ) :=
    leftMul_spectrum_subset_Ioi_of_matrixPosDef hA
  have hσTΦ : spectrum ℝ (leftMul (Φ A) : HSOp m) ⊆ Set.Ioi (0 : ℝ) :=
    leftMul_spectrum_subset_Ioi_of_matrixPosDef hΦA
  have hinv :
      HSLE
        (carlenRectInverseOp (hsAdjoint Φ) (leftMul (Φ A)))
        (Ring.inverse (leftMul A : HSOp n)) :=
    carlenRectangle_direct_to_inverse (hsAdjoint Φ) hTA_sa hTΦ_sa hσTA hσTΦ
      (by simpa [carlenRectDirectOp, hsAdjoint_hsAdjoint] using hdirect)
  have hInvTA : Ring.inverse (leftMul A : HSOp n) = leftMul (posInv A) :=
    ringInverse_leftMul_eq_leftMul_posInv_of_matrixPosDef hA
  have hInvTΦ : Ring.inverse (leftMul (Φ A) : HSOp m) = leftMul (posInv (Φ A)) :=
    ringInverse_leftMul_eq_leftMul_posInv_of_matrixPosDef hΦA
  simpa [carlenRectInverseOp, hInvTA, hInvTΦ, hsAdjoint_hsAdjoint] using hinv

/--
The Schwarz endpoint DPI for the Hilbert--Schmidt adjoint, after the Carlen
square-root rectangle reversal, supplies the right inverse endpoint DPI.
-/
theorem rightMul_posInv_dpi_of_hsAdjointSchwarz {n m : ℕ}
    (Φ : HSMap n m) {B : Mₙ n}
    (hSch : HSAdjointSchwarz Φ)
    (hB : MatrixPosDef B) (hΦB : MatrixPosDef (Φ B)) :
    HSLE
      ((hsAdjoint Φ).comp ((rightMul (posInv (Φ B))).comp Φ))
      (rightMul (posInv B)) := by
  let Ψ : HSMap m n := hsAdjoint Φ
  have hSchΨ : ∀ X : Mₙ m,
      Matrix.conjTranspose (Ψ X) * Ψ X ≤ Ψ (Matrix.conjTranspose X * X) := by
    intro X
    simpa [Ψ, HSAdjointSchwarz] using hSch X
  have hdirect :
      HSLE
        (Φ.comp ((rightMul B).comp (hsAdjoint Φ)))
        (rightMul (Φ B)) := by
    simpa [Ψ, hsAdjoint_hsAdjoint] using
      (rightMul_dpi_of_schwarzMap Ψ hSchΨ hB)
  have hTA_sa : IsSelfAdjoint (rightMul B : HSOp n) :=
    rightMul_isSelfAdjoint_of_matrix_isSelfAdjoint hB.1
  have hTΦ_sa : IsSelfAdjoint (rightMul (Φ B) : HSOp m) :=
    rightMul_isSelfAdjoint_of_matrix_isSelfAdjoint hΦB.1
  have hσTA : spectrum ℝ (rightMul B : HSOp n) ⊆ Set.Ioi (0 : ℝ) :=
    rightMul_spectrum_subset_Ioi_of_matrixPosDef hB
  have hσTΦ : spectrum ℝ (rightMul (Φ B) : HSOp m) ⊆ Set.Ioi (0 : ℝ) :=
    rightMul_spectrum_subset_Ioi_of_matrixPosDef hΦB
  have hinv :
      HSLE
        (carlenRectInverseOp (hsAdjoint Φ) (rightMul (Φ B)))
        (Ring.inverse (rightMul B : HSOp n)) :=
    carlenRectangle_direct_to_inverse (hsAdjoint Φ) hTA_sa hTΦ_sa hσTA hσTΦ
      (by simpa [carlenRectDirectOp, hsAdjoint_hsAdjoint] using hdirect)
  have hInvTA : Ring.inverse (rightMul B : HSOp n) = rightMul (posInv B) :=
    ringInverse_rightMul_eq_rightMul_posInv_of_matrixPosDef hB
  have hInvTΦ : Ring.inverse (rightMul (Φ B) : HSOp m) = rightMul (posInv (Φ B)) :=
    ringInverse_rightMul_eq_rightMul_posInv_of_matrixPosDef hΦB
  simpa [carlenRectInverseOp, hInvTA, hInvTΦ, hsAdjoint_hsAdjoint] using hinv

/--
The original strict-output Schwarz assumptions supply the residual pointwise
inverse-form fixed-kernel input.
-/
theorem pointwiseInvKernelInput_of_hsAdjointSchwarz {n m : ℕ}
    (Φ : HSMap n m) {A B : Mₙ n}
    (hpos : IsPositiveMap Φ)
    (_htrace : _root_.HiaiPetz.TracePreserving Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΦA : MatrixPosDef (Φ A)) (hΦB : MatrixPosDef (Φ B)) :
    ∀ {t : ℝ}, 0 ≤ t →
      HSLE
        ((hsAdjoint Φ).comp ((jKuboKernelInvForm t (Φ A) (Φ B)).comp Φ))
        (jKuboKernelInvForm t A B) := by
  intro t ht
  refine jKuboKernelInvForm_dpi_of_inverse_terms Φ ht ?_ ?_
  · exact leftMul_posInv_dpi_of_hsAdjointSchwarz Φ hSch
      (fun X ↦ hsAdjoint_map_conjTranspose_of_isPositiveMap hpos X) hA hΦA
  · exact rightMul_posInv_dpi_of_hsAdjointSchwarz Φ hSch hB hΦB

/--
The original strict-output positivity assumptions supply the residual
pointwise inverse-form fixed-kernel input.
-/
theorem pointwiseInvKernelInput_of_hsAdjointSchwarz_outputs {n m : ℕ}
    (Φ : HSMap n m) {A B : Mₙ n}
    (hpos : IsPositiveMap Φ)
    (htrace : _root_.HiaiPetz.TracePreserving Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    ∀ {t : ℝ}, 0 ≤ t →
      HSLE
        ((hsAdjoint Φ).comp ((jKuboKernelInvForm t (Φ A) (Φ B)).comp Φ))
        (jKuboKernelInvForm t A B) := by
  have hΦA : MatrixPosDef (Φ A) :=
    isPositiveMap_matrixPosDef_of_map_one_matrixPosDef Φ hpos hΦ1 hA
  have hΦB : MatrixPosDef (Φ B) :=
    isPositiveMap_matrixPosDef_of_map_one_matrixPosDef Φ hpos hΦ1 hB
  intro t ht
  exact pointwiseInvKernelInput_of_hsAdjointSchwarz
    Φ hpos htrace hSch hA hB hΦA hΦB (t := t) ht

/--
If the pointwise inverse-form fixed-kernel DPI is supplied explicitly, the
original strict-output hypotheses give both strict `J_f` data-processing
inequalities.  That input is `pointwiseInvKernelInput_of_hsAdjointSchwarz_outputs`
above; the version without it is
`strict_output_direct_inverse_dpi_of_conditionI_hsAdjoint_schwarz` below.
-/
theorem strict_output_direct_inverse_dpi_of_conditionI_hsAdjoint_schwarz_kernelInput
    {n m : ℕ} (Φ : HSMap n m) {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hI : ConditionI f)
    (hpos : IsPositiveMap Φ)
    (_htrace : _root_.HiaiPetz.TracePreserving Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n)))
    (hkernelInv :
      ∀ {t : ℝ}, 0 ≤ t →
        HSLE
          ((hsAdjoint Φ).comp
            ((jKuboKernelInvForm t (Φ A) (Φ B)).comp Φ))
          (jKuboKernelInvForm t A B)) :
    HSLE
        (Φ.comp ((jOperator f A B).comp (hsAdjoint Φ)))
        (jOperator f (Φ A) (Φ B)) ∧
      HSLE
        ((hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ))
        (jOperatorInv f A B) := by
  let Ψ : HSMap m n := hsAdjoint Φ
  have hΦA : MatrixPosDef (Φ A) :=
    isPositiveMap_matrixPosDef_of_map_one_matrixPosDef Φ hpos hΦ1 hA
  have hΦB : MatrixPosDef (Φ B) :=
    isPositiveMap_matrixPosDef_of_map_one_matrixPosDef Φ hpos hΦ1 hB
  have hΨA : MatrixPosDef (hsAdjoint Ψ A) := by
    simpa [Ψ, hsAdjoint_hsAdjoint] using hΦA
  have hΨB : MatrixPosDef (hsAdjoint Ψ B) := by
    simpa [Ψ, hsAdjoint_hsAdjoint] using hΦB
  have hSchΨ : ∀ X : Mₙ m,
      Matrix.conjTranspose (Ψ X) * Ψ X ≤ Ψ (Matrix.conjTranspose X * X) := by
    intro X
    simpa [Ψ, HSAdjointSchwarz] using hSch X
  have hstar : ∀ X : Mₙ m,
      Ψ (Matrix.conjTranspose X) = Matrix.conjTranspose (Ψ X) := by
    intro X
    simpa [Ψ] using hsAdjoint_map_conjTranspose_of_isPositiveMap hpos X
  have hkernelInvΨ :
      ∀ {t : ℝ}, 0 ≤ t →
        HSLE
          (Ψ.comp
            ((jKuboKernelInvForm t (hsAdjoint Ψ A) (hsAdjoint Ψ B)).comp
              (hsAdjoint Ψ)))
          (jKuboKernelInvForm t A B) := by
    intro t ht
    simpa [Ψ, hsAdjoint_hsAdjoint] using hkernelInv (t := t) ht
  have hdirectΨ :
      HSLE
        ((hsAdjoint Ψ).comp ((jOperator f A B).comp Ψ))
        (jOperator f (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
    jOperator_dpi_of_loewnerConditionI_pointwiseInvKernel_schwarzMap.{0}
      Ψ (conditionI_to_loewnerConditionI.{0}
        (fun {x} hx => le_of_lt (hf.2 (x := x) hx)) hI)
      hSchΨ hstar hA hB hΨA hΨB hf.2 hkernelInvΨ
  have hdirect :
      HSLE
        (Φ.comp ((jOperator f A B).comp (hsAdjoint Φ)))
        (jOperator f (Φ A) (Φ B)) := by
    simpa [Ψ, hsAdjoint_hsAdjoint] using hdirectΨ
  let TA : HSOp n := jOperator f A B
  let TΦ : HSOp m := jOperator f (Φ A) (Φ B)
  have hTA_sa : IsSelfAdjoint TA := by
    simpa [TA] using jOperator_isSelfAdjoint_of_carlenFunctionHypothesis hf hA hB
  have hTΦ_sa : IsSelfAdjoint TΦ := by
    simpa [TΦ] using jOperator_isSelfAdjoint_of_carlenFunctionHypothesis hf hΦA hΦB
  have hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ) := by
    simpa [TA] using jOperator_spectrum_subset_Ioi_of_carlenFunctionHypothesis hf hA hB
  have hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ) := by
    simpa [TΦ] using jOperator_spectrum_subset_Ioi_of_carlenFunctionHypothesis hf hΦA hΦB
  have hinverseRing :
      HSLE
        ((hsAdjoint Φ).comp
          ((Ring.inverse (jOperator f (Φ A) (Φ B))).comp Φ))
        (Ring.inverse (jOperator f A B)) := by
    have hrect : HSLE (carlenRectDirectOp (hsAdjoint Φ) TA) TΦ := by
      simpa [carlenRectDirectOp, TA, TΦ, hsAdjoint_hsAdjoint] using hdirect
    have hinv : HSLE (carlenRectInverseOp (hsAdjoint Φ) TΦ) (Ring.inverse TA) :=
      carlenRectangle_direct_to_inverse (hsAdjoint Φ) hTA_sa hTΦ_sa hσTA hσTΦ hrect
    simpa [carlenRectInverseOp, TA, TΦ, hsAdjoint_hsAdjoint] using hinv
  have hJΦ :
      jOperatorInv f (Φ A) (Φ B) =
        Ring.inverse (jOperator f (Φ A) (Φ B)) :=
    jOperatorInv_eq_ringInverse_of_carlenFunctionHypothesis hf hΦA hΦB
  have hJAB :
      jOperatorInv f A B = Ring.inverse (jOperator f A B) :=
    jOperatorInv_eq_ringInverse_of_carlenFunctionHypothesis hf hA hB
  refine ⟨hdirect, ?_⟩
  simpa [hJΦ, hJAB] using hinverseRing

/--
The original strict-output hypotheses give both strict `J_f` data-processing
inequalities.  The pointwise inverse-form fixed-kernel input is supplied from
`HSAdjointSchwarz` by the endpoint Schwarz DPI and Carlen rectangle reversal.
-/
theorem strict_output_direct_inverse_dpi_of_conditionI_hsAdjoint_schwarz
    {n m : ℕ} (Φ : HSMap n m) {f : ℝ → ℝ} {A B : Mₙ n}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hI : ConditionI f)
    (hpos : IsPositiveMap Φ)
    (htrace : _root_.HiaiPetz.TracePreserving Φ)
    (hSch : HSAdjointSchwarz Φ)
    (hA : MatrixPosDef A) (hB : MatrixPosDef B)
    (hΦ1 : MatrixPosDef (Φ (1 : Mₙ n))) :
    HSLE
        (Φ.comp ((jOperator f A B).comp (hsAdjoint Φ)))
        (jOperator f (Φ A) (Φ B)) ∧
      HSLE
        ((hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ))
        (jOperatorInv f A B) :=
  strict_output_direct_inverse_dpi_of_conditionI_hsAdjoint_schwarz_kernelInput
    Φ hf hI hpos htrace hSch hA hB hΦ1
    (pointwiseInvKernelInput_of_hsAdjointSchwarz_outputs
      Φ hpos htrace hSch hA hB hΦ1)

/--
In the strict-output regime, the direct Hiai--Petz inequality implies the
inverse inequality by the Carlen square-root rectangle reversal.
-/
theorem conditionIII_strict_to_conditionII_strict_of_carlenFunctionHypothesis
    {f : ℝ → ℝ}
    (hf : CarlenOpMontIFunctionHypothesis f) :
    ConditionIII_strict f → ConditionII_strict f := by
  intro hIII n m Φ A B hpos htrace hSch hA hB hΦ1
  have hΦA : MatrixPosDef (Φ A) :=
    isPositiveMap_matrixPosDef_of_map_one_matrixPosDef Φ hpos hΦ1 hA
  have hΦB : MatrixPosDef (Φ B) :=
    isPositiveMap_matrixPosDef_of_map_one_matrixPosDef Φ hpos hΦ1 hB
  let TA : HSOp n := jOperator f A B
  let TΦ : HSOp m := jOperator f (Φ A) (Φ B)
  have hTA_sa : IsSelfAdjoint TA := by
    simpa [TA] using jOperator_isSelfAdjoint_of_carlenFunctionHypothesis hf hA hB
  have hTΦ_sa : IsSelfAdjoint TΦ := by
    simpa [TΦ] using jOperator_isSelfAdjoint_of_carlenFunctionHypothesis hf hΦA hΦB
  have hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ) := by
    simpa [TA] using jOperator_spectrum_subset_Ioi_of_carlenFunctionHypothesis hf hA hB
  have hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ) := by
    simpa [TΦ] using jOperator_spectrum_subset_Ioi_of_carlenFunctionHypothesis hf hΦA hΦB
  have hdirect :
      HSLE (carlenRectDirectOp (hsAdjoint Φ) TA) TΦ := by
    have hraw := hIII Φ hpos htrace hSch hA hB hΦ1
    simpa [carlenRectDirectOp, TA, TΦ, hsAdjoint_hsAdjoint] using hraw
  have hinverseRing :
      HSLE (carlenRectInverseOp (hsAdjoint Φ) TΦ) (Ring.inverse TA) :=
    carlenRectangle_direct_to_inverse (hsAdjoint Φ) hTA_sa hTΦ_sa hσTA hσTΦ hdirect
  have hJΦ :
      jOperatorInv f (Φ A) (Φ B) =
        Ring.inverse (jOperator f (Φ A) (Φ B)) :=
    jOperatorInv_eq_ringInverse_of_carlenFunctionHypothesis hf hΦA hΦB
  have hJAB :
      jOperatorInv f A B = Ring.inverse (jOperator f A B) :=
    jOperatorInv_eq_ringInverse_of_carlenFunctionHypothesis hf hA hB
  simpa [carlenRectInverseOp, TA, TΦ, hJΦ, hJAB, hsAdjoint_hsAdjoint]
    using hinverseRing

/--
In the strict-output regime, the inverse Hiai--Petz inequality implies the
direct inequality by the Carlen square-root rectangle step.
-/
theorem conditionII_strict_to_conditionIII_strict_of_carlenFunctionHypothesis
    {f : ℝ → ℝ}
    (hf : CarlenOpMontIFunctionHypothesis f) :
    ConditionII_strict f → ConditionIII_strict f := by
  intro hII n m Φ A B hpos htrace hSch hA hB hΦ1
  have hΦA : MatrixPosDef (Φ A) :=
    isPositiveMap_matrixPosDef_of_map_one_matrixPosDef Φ hpos hΦ1 hA
  have hΦB : MatrixPosDef (Φ B) :=
    isPositiveMap_matrixPosDef_of_map_one_matrixPosDef Φ hpos hΦ1 hB
  let TA : HSOp n := jOperator f A B
  let TΦ : HSOp m := jOperator f (Φ A) (Φ B)
  have hTA_sa : IsSelfAdjoint TA := by
    simpa [TA] using jOperator_isSelfAdjoint_of_carlenFunctionHypothesis hf hA hB
  have hTΦ_sa : IsSelfAdjoint TΦ := by
    simpa [TΦ] using jOperator_isSelfAdjoint_of_carlenFunctionHypothesis hf hΦA hΦB
  have hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ) := by
    simpa [TA] using jOperator_spectrum_subset_Ioi_of_carlenFunctionHypothesis hf hA hB
  have hσTΦ : spectrum ℝ TΦ ⊆ Set.Ioi (0 : ℝ) := by
    simpa [TΦ] using jOperator_spectrum_subset_Ioi_of_carlenFunctionHypothesis hf hΦA hΦB
  have hJΦ :
      jOperatorInv f (Φ A) (Φ B) =
        Ring.inverse (jOperator f (Φ A) (Φ B)) :=
    jOperatorInv_eq_ringInverse_of_carlenFunctionHypothesis hf hΦA hΦB
  have hJAB :
      jOperatorInv f A B = Ring.inverse (jOperator f A B) :=
    jOperatorInv_eq_ringInverse_of_carlenFunctionHypothesis hf hA hB
  have hinverseRing :
      HSLE (carlenRectInverseOp (hsAdjoint Φ) TΦ) (Ring.inverse TA) := by
    have hraw := hII Φ hpos htrace hSch hA hB hΦ1
    simpa [carlenRectInverseOp, TA, TΦ, hJΦ, hJAB, hsAdjoint_hsAdjoint] using hraw
  have hdirect :
      HSLE (carlenRectDirectOp (hsAdjoint Φ) TA) TΦ :=
    carlenRectangle_inverse_to_direct (hsAdjoint Φ) hTA_sa hTΦ_sa hσTA hσTΦ hinverseRing
  simpa [carlenRectDirectOp, TA, TΦ, hsAdjoint_hsAdjoint] using hdirect

/--
The strict-output direct and inverse Hiai--Petz predicates are equivalent
under Carlen's positivity and continuity hypotheses for `f`.
-/
theorem conditionII_strict_iff_conditionIII_strict_of_carlenFunctionHypothesis
    {f : ℝ → ℝ}
    (hf : CarlenOpMontIFunctionHypothesis f) :
    ConditionII_strict f ↔ ConditionIII_strict f :=
  ⟨conditionII_strict_to_conditionIII_strict_of_carlenFunctionHypothesis hf,
    conditionIII_strict_to_conditionII_strict_of_carlenFunctionHypothesis hf⟩

/--
The theorem-facing strict-output formulation: Condition I implies the direct
and inverse strict-output predicates.
-/
theorem conditionI_to_conditionIII_and_conditionII_strict
    {f : ℝ → ℝ}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hI : ConditionI f) :
    ConditionIII_strict f ∧ ConditionII_strict f := by
  refine ⟨?_, ?_⟩
  · intro n m Φ A B hpos htrace hSch hA hB hΦ1
    exact (strict_output_direct_inverse_dpi_of_conditionI_hsAdjoint_schwarz
      Φ hf hI hpos htrace hSch hA hB hΦ1).1
  · intro n m Φ A B hpos htrace hSch hA hB hΦ1
    exact (strict_output_direct_inverse_dpi_of_conditionI_hsAdjoint_schwarz
      Φ hf hI hpos htrace hSch hA hB hΦ1).2

/--
The same strict-output forward direction, expressed on the theorem-facing HP62
surface aliases.
-/
theorem matrix_monotone_to_strict_direct_and_inverse_dpi
    {f : ℝ → ℝ}
    (hf : CarlenOpMontIFunctionHypothesis f)
    (hI : ConditionI f) :
    QuasiEntropyDPI.strictDirectDPICondition f ∧ QuasiEntropyDPI.strictInverseDPICondition f :=
  conditionI_to_conditionIII_and_conditionII_strict hf hI

/-- Hiai--Petz `ConditionI` supplies Carlen's operator-monotonicity
Condition (1). -/
theorem conditionI_to_carlenCondition1 {f : ℝ → ℝ}
    (hI : ConditionI f) :
    CarlenOpMontICondition1.{u} f :=
  conditionI_to_operatorMonotoneOnPositive.{u} hI

/-- Carlen's Condition (1) and the Hiai--Petz finite-dimensional Condition I
surface are equivalent. -/
theorem carlenCondition1_iff_conditionI {f : ℝ → ℝ} :
    CarlenOpMontICondition1.{u} f ↔ ConditionI f :=
  ⟨carlenCondition1_to_conditionI.{u}, conditionI_to_carlenCondition1.{u}⟩
end

end Quantum.TraceInequality.Loewner.HiaiPetz
