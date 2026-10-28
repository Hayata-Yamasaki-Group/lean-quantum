/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenKernel.InverseTermReduction
import
  Quantum.TraceInequality.Loewner.Applications.HiaiPetz.CarlenKernel.InverseTermReductionRetained
import Quantum.TraceInequality.TraceFunctionMonotonicity.Petz.CarlenKernel.BlockPositivity

/-!
# Carlen fixed-kernel DPI: block-positivity stage

This module contains the fixed-kernel DPI stage of Carlen 2022 covering block
positivity, adjoint inverse-form DPI, and the fixed-kernel flip/normalized
gates.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped Matrix.Norms.Frobenius MatrixOrder CStarAlgebra ComplexOrder

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace
  instCarlenKernelHSOpCStarAlgebra
  instCarlenKernelHSOpStarRing
  instCarlenKernelHSOpPartialOrder
  instCarlenKernelHSOpStarOrderedRing
  instCarlenKernelHSOpNonnegSpectrumClass

noncomputable section


/--
The right inverse-term matrix inequality follows from Lieb--Ruskai by applying
the left-form inequality to `X*` and using conjugate-transpose preservation.
-/
theorem right_liebRuskai_inequality_of_isTwoPositiveMap {n m : ℕ}
    {Ψ : HSMap n m} {B X : Mₙ n}
    (hΨ : IsTwoPositiveMap Ψ)
    (hB : B.PosDef)
    (hΨB : (Ψ B).PosDef) :
    (Ψ (X * posInv B * Matrix.conjTranspose X) -
      Ψ X * posInv (Ψ B) * Matrix.conjTranspose (Ψ X)).PosSemidef := by
  classical
  have hLR :=
    liebRuskai_inequality_of_isTwoPositiveMap
      (Ψ := Ψ) (C := B) (X := Matrix.conjTranspose X) hΨ hB hΨB
  have hstar : Ψ (Matrix.conjTranspose X) = Matrix.conjTranspose (Ψ X) :=
    map_conjTranspose_of_isTwoPositiveMap hΨ X
  simpa [liebRuskaiSchur, posInv, hstar, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc] using hLR

/--
Lieb--Ruskai supplies the two matrix inverse-term inequalities needed for the
inverse-form fixed-kernel DPI.
-/
theorem jKuboKernelInvForm_dpi_of_liebRuskai_terms {n m : ℕ} (Ψ : HSMap n m)
    {t : ℝ} (ht : 0 ≤ t) {A B : Mₙ n}
    (htrace : ∀ Z : Mₙ n, Matrix.trace (Ψ Z) = Matrix.trace Z)
    (hΨ : IsTwoPositiveMap Ψ)
    (hA : A.PosDef)
    (hB : B.PosDef)
    (hΨA : (Ψ A).PosDef)
    (hΨB : (Ψ B).PosDef) :
    HSLE ((hsAdjoint Ψ).comp ((jKuboKernelInvForm t (Ψ A) (Ψ B)).comp Ψ))
      (jKuboKernelInvForm t A B) := by
  refine jKuboKernelInvForm_dpi_of_matrix_inverse_terms Ψ ht htrace ?_ ?_
  · intro X
    simpa [liebRuskaiSchur, posInv] using
      (liebRuskai_inequality_of_isTwoPositiveMap
        (Ψ := Ψ) (C := A) (X := X) hΨ hA hΨA)
  · intro X
    simpa using
      (right_liebRuskai_inequality_of_isTwoPositiveMap
        (Ψ := Ψ) (B := B) (X := X) hΨ hB hΨB)

/--
Unitality supplies the trace-preserving hypothesis for the Hilbert--Schmidt
adjoint direction of the inverse-form fixed-kernel DPI.

The two-positivity of the adjoint map is left explicit: this node only aligns
Carlen's unital convention with the trace-preserving convention used by the
Lieb--Ruskai input theorem.
-/
theorem jKuboKernelInvForm_dpi_of_adjoint_liebRuskai_terms {n m : ℕ}
    (Ψ : HSMap n m) {t : ℝ} (ht : 0 ≤ t) {A B : Mₙ m}
    (hunit : IsUnitalMap Ψ)
    (hadj_twoPositive : IsTwoPositiveMap (hsAdjoint Ψ))
    (hA : A.PosDef)
    (hB : B.PosDef)
    (hΨA : (hsAdjoint Ψ A).PosDef)
    (hΨB : (hsAdjoint Ψ B).PosDef) :
    HSLE
      ((hsAdjoint (hsAdjoint Ψ)).comp
        ((jKuboKernelInvForm t (hsAdjoint Ψ A) (hsAdjoint Ψ B)).comp (hsAdjoint Ψ)))
      (jKuboKernelInvForm t A B) :=
  jKuboKernelInvForm_dpi_of_liebRuskai_terms (hsAdjoint Ψ) ht
    (hsAdjoint_tracePreserving_of_isUnitalMap hunit)
    hadj_twoPositive hA hB hΨA hΨB

/--
The same adjoint-direction inverse-form DPI, with the double adjoint reduced to
the original Hilbert--Schmidt map.
-/
theorem jKuboKernelInvForm_dpi_of_adjoint_liebRuskai_terms_normalized {n m : ℕ}
    (Ψ : HSMap n m) {t : ℝ} (ht : 0 ≤ t) {A B : Mₙ m}
    (hunit : IsUnitalMap Ψ)
    (hadj_twoPositive : IsTwoPositiveMap (hsAdjoint Ψ))
    (hA : A.PosDef)
    (hB : B.PosDef)
    (hΨA : (hsAdjoint Ψ A).PosDef)
    (hΨB : (hsAdjoint Ψ B).PosDef) :
    HSLE
      (Ψ.comp
        ((jKuboKernelInvForm t (hsAdjoint Ψ A) (hsAdjoint Ψ B)).comp (hsAdjoint Ψ)))
      (jKuboKernelInvForm t A B) := by
  simpa [hsAdjoint_hsAdjoint] using
    (jKuboKernelInvForm_dpi_of_adjoint_liebRuskai_terms
      Ψ ht hunit hadj_twoPositive hA hB hΨA hΨB)

/-! ### Fixed-Kernel Flip and Normalized Gates -/
/--
The trace-preserving fixed-kernel DPI follows from the inverse-form
Lieb--Ruskai DPI once the finite-dimensional flip lemma is supplied.

The flip step is deliberately an explicit hypothesis: this route does not
import the existing Hiai--Petz residual-equivalence proof.
-/
theorem jKuboKernel_dpi_of_liebRuskai_terms_and_flip {n m : ℕ} (Φ : HSMap n m)
    {t : ℝ} (ht : 0 ≤ t) {A B : Mₙ n}
    (htrace : ∀ Z : Mₙ n, Matrix.trace (Φ Z) = Matrix.trace Z)
    (hΦ : IsTwoPositiveMap Φ)
    (hA : A.PosDef)
    (hB : B.PosDef)
    (hΦA : (Φ A).PosDef)
    (hΦB : (Φ B).PosDef)
    (hflip :
      HSLE ((hsAdjoint Φ).comp ((jKuboKernelInvForm t (Φ A) (Φ B)).comp Φ))
        (jKuboKernelInvForm t A B) →
      HSLE (Φ.comp ((jKuboKernel t A B).comp (hsAdjoint Φ)))
        (jKuboKernel t (Φ A) (Φ B))) :
    HSLE (Φ.comp ((jKuboKernel t A B).comp (hsAdjoint Φ)))
      (jKuboKernel t (Φ A) (Φ B)) :=
  hflip
    (jKuboKernelInvForm_dpi_of_liebRuskai_terms
      Φ ht htrace hΦ hA hB hΦA hΦB)

/--
The Carlen unital convention version of the fixed-kernel DPI follows from the
adjoint-direction inverse-form DPI once the same flip step is supplied.

The two-positivity of the Hilbert--Schmidt adjoint remains explicit.
-/
theorem jKuboKernel_dpi_of_adjoint_liebRuskai_terms_and_flip {n m : ℕ}
    (Ψ : HSMap n m) {t : ℝ} (ht : 0 ≤ t) {A B : Mₙ m}
    (hunit : IsUnitalMap Ψ)
    (hadj_twoPositive : IsTwoPositiveMap (hsAdjoint Ψ))
    (hA : A.PosDef)
    (hB : B.PosDef)
    (hΨA : (hsAdjoint Ψ A).PosDef)
    (hΨB : (hsAdjoint Ψ B).PosDef)
    (hflip :
      HSLE
        (Ψ.comp
          ((jKuboKernelInvForm t (hsAdjoint Ψ A) (hsAdjoint Ψ B)).comp
            (hsAdjoint Ψ)))
        (jKuboKernelInvForm t A B) →
      HSLE
        ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
        (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B))) :
    HSLE
      ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
      (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
  hflip
    (jKuboKernelInvForm_dpi_of_adjoint_liebRuskai_terms_normalized
      Ψ ht hunit hadj_twoPositive hA hB hΨA hΨB)

/--
The Carlen unital two-positive convention reaches the fixed-kernel flip gate
once the two-positivity of the Hilbert--Schmidt adjoint is supplied explicitly.

This keeps the adjoint-positivity transfer separate from the finite-dimensional
flip lemma and does not import the existing Hiai--Petz proof route.
-/
theorem jKuboKernel_dpi_of_unitalTwoPositive_adjointSupplier_and_flip {n m : ℕ}
    (Ψ : HSMap n m) {t : ℝ} (ht : 0 ≤ t) {A B : Mₙ m}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hadj_twoPositive : IsUnitalTwoPositiveMap Ψ → IsTwoPositiveMap (hsAdjoint Ψ))
    (hA : A.PosDef)
    (hB : B.PosDef)
    (hΨA : (hsAdjoint Ψ A).PosDef)
    (hΨB : (hsAdjoint Ψ B).PosDef)
    (hflip :
      HSLE
        (Ψ.comp
          ((jKuboKernelInvForm t (hsAdjoint Ψ A) (hsAdjoint Ψ B)).comp
            (hsAdjoint Ψ)))
        (jKuboKernelInvForm t A B) →
      HSLE
        ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
        (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B))) :
    HSLE
      ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
      (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
  jKuboKernel_dpi_of_adjoint_liebRuskai_terms_and_flip
    Ψ ht hΨ.1 (hadj_twoPositive hΨ) hA hB hΨA hΨB hflip

/--
The same unital two-positive fixed-kernel gate, with the theorem-facing
positive-definite predicate used by the Hiai--Petz statement interface.
-/
theorem jKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef_adjointSupplier_and_flip
    {n m : ℕ} (Ψ : HSMap n m) {t : ℝ} (ht : 0 ≤ t) {A B : Mₙ m}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hadj_twoPositive : IsUnitalTwoPositiveMap Ψ → IsTwoPositiveMap (hsAdjoint Ψ))
    (hA : MatrixPosDef A)
    (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B))
    (hflip :
      HSLE
        (Ψ.comp
          ((jKuboKernelInvForm t (hsAdjoint Ψ A) (hsAdjoint Ψ B)).comp
            (hsAdjoint Ψ)))
        (jKuboKernelInvForm t A B) →
      HSLE
        ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
        (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B))) :
    HSLE
      ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
      (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
  jKuboKernel_dpi_of_unitalTwoPositive_adjointSupplier_and_flip
    Ψ ht hΨ hadj_twoPositive
    (matrixPosDef_posDef hA) (matrixPosDef_posDef hB)
    (matrixPosDef_posDef hΨA) (matrixPosDef_posDef hΨB) hflip

/--
The theorem-facing fixed-kernel gate with Carlen's normalized norm contraction
exposed.  The remaining normalization hypotheses are exactly the
square-root/inverse bookkeeping that turns the inverse-form kernel inequality
into a contraction bound for `V` and turns the resulting target-side norm bound
back into the fixed-kernel inequality.
-/
theorem jKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef_adjointSupplier_and_normalizedNormFlip
    {n m : ℕ} (Ψ : HSMap n m) {t : ℝ} (ht : 0 ≤ t) {A B : Mₙ m}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hadj_twoPositive : IsUnitalTwoPositiveMap Ψ → IsTwoPositiveMap (hsAdjoint Ψ))
    (hA : MatrixPosDef A)
    (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B))
    (V : HSMap m n)
    (hnormalize_inv :
      HSLE
        (Ψ.comp
          ((jKuboKernelInvForm t (hsAdjoint Ψ A) (hsAdjoint Ψ B)).comp
            (hsAdjoint Ψ)))
        (jKuboKernelInvForm t A B) →
      hsMapNorm V ≤ 1)
    (hnormalize_fixed :
      hsMapNorm V ≤ 1 →
      HSLE
        ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
        (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B))) :
    HSLE
      ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
      (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
  jKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef_adjointSupplier_and_flip
    Ψ ht hΨ hadj_twoPositive hA hB hΨA hΨB
    (fun hinv ↦ by
      exact hnormalize_fixed (hnormalize_inv hinv))

/--
The theorem-facing fixed-kernel gate with Carlen's normalized operator
contraction exposed.  The abstract Hilbert-space flip
`V† V ≤ 1 → V V† ≤ 1` is now proved by
`clm_self_comp_adjoint_le_one_of_adjoint_comp_self_le_one`; the remaining
normalization hypotheses are the concrete square-root/inverse bookkeeping.
-/
theorem jKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef_adjointSupplier_and_normalizedOperatorFlip
    {n m : ℕ} (Ψ : HSMap n m) {t : ℝ} (ht : 0 ≤ t) {A B : Mₙ m}
    (hΨ : IsUnitalTwoPositiveMap Ψ)
    (hadj_twoPositive : IsUnitalTwoPositiveMap Ψ → IsTwoPositiveMap (hsAdjoint Ψ))
    (hA : MatrixPosDef A)
    (hB : MatrixPosDef B)
    (hΨA : MatrixPosDef (hsAdjoint Ψ A))
    (hΨB : MatrixPosDef (hsAdjoint Ψ B))
    (V : HSMap m n)
    (hnormalize_inv :
      HSLE
        (Ψ.comp
          ((jKuboKernelInvForm t (hsAdjoint Ψ A) (hsAdjoint Ψ B)).comp
            (hsAdjoint Ψ)))
        (jKuboKernelInvForm t A B) →
      (hsAdjoint V).comp V ≤ 1)
    (hnormalize_fixed :
      V.comp (hsAdjoint V) ≤ 1 →
      HSLE
        ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
        (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B))) :
    HSLE
      ((hsAdjoint Ψ).comp ((jKuboKernel t A B).comp Ψ))
      (jKuboKernel t (hsAdjoint Ψ A) (hsAdjoint Ψ B)) :=
  jKuboKernel_dpi_of_unitalTwoPositive_matrixPosDef_adjointSupplier_and_flip
    Ψ ht hΨ hadj_twoPositive hA hB hΨA hΨB
    (fun hinv ↦ by
      have htarget_raw :=
        @clm_self_comp_adjoint_le_one_of_adjoint_comp_self_le_one
          (Mₙ m) (Mₙ n)
          (instMatrixNormedAddCommGroup (n := m))
          (instMatrixInnerProductSpace (n := m))
          (instMatrixCompleteSpace (n := m))
          (instMatrixNormedAddCommGroup (n := n))
          (instMatrixInnerProductSpace (n := n))
          (instMatrixCompleteSpace (n := n))
          V
          (by simpa [hsAdjoint] using hnormalize_inv hinv)
      have htarget : V.comp (hsAdjoint V) ≤ 1 := by
        simpa [hsAdjoint] using htarget_raw
      exact hnormalize_fixed htarget)


end

end Quantum.TraceInequality.Loewner.HiaiPetz
