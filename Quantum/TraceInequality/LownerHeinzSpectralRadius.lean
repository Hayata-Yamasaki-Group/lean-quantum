/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.Basic
import Quantum.TraceInequality.HiaiPetz.Basic

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A spectral-radius route to the Löwner--Heinz inequality

This file carries out the Hiai--Yanagi spectral-radius proof of the
Löwner--Heinz inequality for positive operators. It is intentionally kept
independent of `LownerHeinzTheorem` and `LownerHeinzCore`: the final proof in
this file must not appeal to the already-formalized Löwner--Heinz theorem or
to `CFC.rpow_le_rpow`.

## Main results

* `opRpow_calculus_of_nonneg_isUnit`: real-power algebra for positive
  invertible operators.
* `opRpow_order_midpoint_of_nonneg_isUnit`: the midpoint step in the
  spectral-radius argument.
* `lownerHeinz_of_spectralRadius`: Löwner--Heinz monotonicity for
  `p ∈ [0, 1]`, obtained by removing the invertibility hypothesis through
  `εI` regularization.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021,
  Theorem 5.1.1 and the spectral-radius facts in Section 3.1.
-/

open scoped Topology

namespace HansenPedersen
namespace LownerHeinzSpectralRadius

universe u

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial (L ℋ)]

/-- Hiai--Yanagi (3.1): the spectral radius is bounded by the operator norm. -/
theorem spectralRadius_le_nnnorm (T : L ℋ) :
    spectralRadius ℂ T ≤ ‖T‖₊ :=
  spectrum.spectralRadius_le_nnnorm T

omit [Nontrivial (L ℋ)] in
/-- Hiai--Yanagi Proposition 3.1.13 for normal operators. -/
theorem spectralRadius_eq_nnnorm_of_isStarNormal (T : L ℋ) [IsStarNormal T] :
    spectralRadius ℂ T = ‖T‖₊ :=
  IsStarNormal.spectralRadius_eq_nnnorm T

omit [Nontrivial (L ℋ)] in
/-- The self-adjoint special case of the normal spectral-radius formula. -/
theorem spectralRadius_eq_nnnorm_of_isSelfAdjoint {T : L ℋ} (hT : IsSelfAdjoint T) :
    spectralRadius ℂ T = ‖T‖₊ :=
  hT.spectralRadius_eq_nnnorm

omit [Nontrivial (L ℋ)] in
/-- Real-valued form of the self-adjoint spectral-radius formula. -/
theorem spectralRadius_toReal_eq_norm_of_isSelfAdjoint {T : L ℋ} (hT : IsSelfAdjoint T) :
    (spectralRadius ℂ T).toReal = ‖T‖ :=
  hT.toReal_spectralRadius_complex_eq_norm

omit [CompleteSpace ℋ] [Nontrivial (L ℋ)] in
/-- Hiai--Yanagi (3.2): nonzero spectra of `S * T` and `T * S` agree. -/
theorem spectrum_nonzero_mul_comm (S T : L ℋ) :
    spectrum ℂ (S * T) \ {0} = spectrum ℂ (T * S) \ {0} :=
  spectrum.nonzero_mul_comm S T

omit [CompleteSpace ℋ] [Nontrivial (L ℋ)] in
/-- Hiai--Yanagi (3.2): the spectral radius is invariant under cyclic products. -/
theorem spectralRadius_mul_comm (S T : L ℋ) :
    spectralRadius ℂ (S * T) = spectralRadius ℂ (T * S) := by
  apply le_antisymm
  · rw [spectralRadius]
    refine iSup₂_le fun z hz ↦ ?_
    by_cases hz0 : z = 0
    · simp [hz0]
    · have hz' : z ∈ spectrum ℂ (T * S) := by
        have hmem : z ∈ spectrum ℂ (S * T) \ {0} := ⟨hz, by simpa using hz0⟩
        exact ((Set.ext_iff.mp (spectrum_nonzero_mul_comm S T)) z).mp hmem |>.1
      exact le_iSup₂_of_le z hz' le_rfl
  · rw [spectralRadius]
    refine iSup₂_le fun z hz ↦ ?_
    by_cases hz0 : z = 0
    · simp [hz0]
    · have hz' : z ∈ spectrum ℂ (S * T) := by
        have hmem : z ∈ spectrum ℂ (T * S) \ {0} := ⟨hz, by simpa using hz0⟩
        exact ((Set.ext_iff.mp (spectrum_nonzero_mul_comm T S)) z).mp hmem |>.1
      exact le_iSup₂_of_le z hz' le_rfl

omit [Nontrivial (L ℋ)] in
/-- On positive operators, the local `opRpow` wrapper agrees with Mathlib's CFC `rpow`. -/
theorem opRpow_eq_cfc_rpow (r : ℝ) {A : L ℋ} (hA : 0 ≤ A) :
    opRpow (ℋ := ℋ) r A = A ^ r :=
  (CFC.rpow_eq_cfc_real (a := A) (y := r) hA).symm

omit [Nontrivial (L ℋ)] in
/-- Real powers of positive operators are self-adjoint. -/
theorem opRpow_isSelfAdjoint_of_nonneg (r : ℝ) {A : L ℋ} (hA : 0 ≤ A) :
    IsSelfAdjoint (opRpow (ℋ := ℋ) r A) := by
  rw [opRpow_eq_cfc_rpow r hA]
  exact IsSelfAdjoint.of_nonneg CFC.rpow_nonneg

omit [Nontrivial (L ℋ)] in
/-- Real powers of positive operators are fixed by the star operation. -/
theorem star_opRpow_of_nonneg (r : ℝ) {A : L ℋ} (hA : 0 ≤ A) :
    star (opRpow (ℋ := ℋ) r A) = opRpow r A :=
  (opRpow_isSelfAdjoint_of_nonneg r hA).star_eq

omit [Nontrivial (L ℋ)] in
/-- Real-power calculus for positive invertible operators. -/
theorem opRpow_mul_opRpow_of_nonneg_isUnit (r s : ℝ) {A : L ℋ}
    (hA : 0 ≤ A) (hAu : IsUnit A) :
    opRpow (ℋ := ℋ) r A * opRpow s A = opRpow (r + s) A := by
  change cfc (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ r) A *
      cfc (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) A =
    cfc (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (r + s)) A
  rw [← CFC.rpow_eq_cfc_real (a := A) (y := r) hA,
    ← CFC.rpow_eq_cfc_real (a := A) (y := s) hA,
    ← CFC.rpow_eq_cfc_real (a := A) (y := r + s) hA]
  exact (CFC.rpow_add (a := A) (x := r) (y := s) hAu).symm

omit [Nontrivial (L ℋ)] in
/-- The zero exponent gives the identity on positive operators. -/
theorem opRpow_zero_of_nonneg {A : L ℋ} (hA : 0 ≤ A) :
    opRpow (ℋ := ℋ) 0 A = 1 := by
  change cfc (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (0 : ℝ)) A = 1
  rw [← CFC.rpow_eq_cfc_real (a := A) (y := 0) hA]
  exact CFC.rpow_zero A hA

omit [Nontrivial (L ℋ)] in
/-- The first exponent gives the original positive operator. -/
theorem opRpow_one_of_nonneg {A : L ℋ} (hA : 0 ≤ A) :
    opRpow (ℋ := ℋ) 1 A = A := by
  change cfc (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 : ℝ)) A = A
  rw [← CFC.rpow_eq_cfc_real (a := A) (y := 1) hA]
  exact CFC.rpow_one A hA

omit [Nontrivial (L ℋ)] in
/-- A positive invertible real power times its negative power is the identity. -/
theorem opRpow_mul_neg_eq_one (r : ℝ) {A : L ℋ} (hA : 0 ≤ A) (hAu : IsUnit A) :
    opRpow (ℋ := ℋ) r A * opRpow (-r) A = 1 := by
  change cfc (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ r) A *
      cfc (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (-r)) A = 1
  rw [← CFC.rpow_eq_cfc_real (a := A) (y := r) hA,
    ← CFC.rpow_eq_cfc_real (a := A) (y := -r) hA]
  exact CFC.rpow_mul_rpow_neg (a := A) r hAu

omit [Nontrivial (L ℋ)] in
/-- The negative power times the corresponding positive power is the identity. -/
theorem opRpow_neg_mul_eq_one (r : ℝ) {A : L ℋ} (hA : 0 ≤ A) (hAu : IsUnit A) :
    opRpow (ℋ := ℋ) (-r) A * opRpow r A = 1 := by
  change cfc (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (-r)) A *
      cfc (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ r) A = 1
  rw [← CFC.rpow_eq_cfc_real (a := A) (y := -r) hA,
    ← CFC.rpow_eq_cfc_real (a := A) (y := r) hA]
  exact CFC.rpow_neg_mul_rpow (a := A) r hAu

omit [Nontrivial (L ℋ)] in
/-- The negative real power is the globally defined inverse of the corresponding positive power. -/
theorem opRpow_neg_eq_ringInverse_of_nonneg_isUnit (r : ℝ) {A : L ℋ}
    (hA : 0 ≤ A) (hAu : IsUnit A) :
    opRpow (ℋ := ℋ) (-r) A = Ring.inverse (opRpow r A) := by
  let u : (L ℋ)ˣ :=
    ⟨opRpow (ℋ := ℋ) r A, opRpow (-r) A,
      opRpow_mul_neg_eq_one r hA hAu, opRpow_neg_mul_eq_one r hA hAu⟩
  symm
  calc
    Ring.inverse (opRpow (ℋ := ℋ) r A) = Ring.inverse (u : L ℋ) := by simp [u]
    _ = (u⁻¹ : (L ℋ)ˣ) := Ring.inverse_unit u
    _ = opRpow (ℋ := ℋ) (-r) A := rfl

omit [Nontrivial (L ℋ)] in
/-- Real-power calculus for positive invertible operators. -/
theorem opRpow_calculus_of_nonneg_isUnit {A : L ℋ} (hA : 0 ≤ A) (hAu : IsUnit A) :
    (∀ r s : ℝ, opRpow (ℋ := ℋ) r A * opRpow s A = opRpow (r + s) A) ∧
      (∀ r : ℝ, star (opRpow (ℋ := ℋ) r A) = opRpow r A) ∧
        (∀ r : ℝ, opRpow (ℋ := ℋ) (-r) A = Ring.inverse (opRpow r A)) := by
  exact ⟨fun r s ↦ opRpow_mul_opRpow_of_nonneg_isUnit r s hA hAu,
    fun r ↦ star_opRpow_of_nonneg r hA,
    fun r ↦ opRpow_neg_eq_ringInverse_of_nonneg_isUnit r hA hAu⟩

omit [Nontrivial (L ℋ)] in
private theorem norm_le_one_of_star_mul_self_le_one {X : L ℋ}
    (hX : star X * X ≤ (1 : L ℋ)) : ‖X‖ ≤ 1 := by
  have hnorm2 : ‖star X * X‖ ≤ 1 := by
    simpa [one_smul] using
      (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg X)).2 hX
  rw [CStarRing.norm_star_mul_self] at hnorm2
  nlinarith [norm_nonneg X]

omit [Nontrivial (L ℋ)] in
/-- A power-order inequality gives the contraction estimate used in the spectral-radius proof. -/
theorem opRpow_order_contraction_of_nonneg_isUnit {A B : L ℋ} {p : ℝ}
    (hA : 0 ≤ A) (hAu : IsUnit A) (hB : 0 ≤ B) (hBu : IsUnit B)
    (hpow : opRpow (ℋ := ℋ) p A ≤ opRpow p B) :
    ‖opRpow (ℋ := ℋ) (p / 2) A * opRpow (-(p / 2)) B‖ ≤ 1 := by
  let X : L ℋ := opRpow (ℋ := ℋ) (p / 2) A * opRpow (-(p / 2)) B
  let C : L ℋ := opRpow (ℋ := ℋ) (-(p / 2)) B
  have hCstar : star C = C := by
    simp [C, star_opRpow_of_nonneg (ℋ := ℋ) (-(p / 2)) hB]
  have hconj : C * opRpow (ℋ := ℋ) p A * C ≤ C * opRpow p B * C := by
    simpa [C, hCstar] using star_left_conjugate_le_conjugate hpow C
  have hAhalf : opRpow (ℋ := ℋ) (p / 2) A * opRpow (p / 2) A = opRpow p A := by
    calc
      opRpow (ℋ := ℋ) (p / 2) A * opRpow (p / 2) A =
          opRpow ((p / 2) + (p / 2)) A := by
            exact opRpow_mul_opRpow_of_nonneg_isUnit (ℋ := ℋ) (p / 2) (p / 2) hA hAu
      _ = opRpow p A := by ring_nf
  have hBcollapse : C * opRpow (ℋ := ℋ) p B * C = 1 := by
    calc
      C * opRpow (ℋ := ℋ) p B * C =
          (opRpow (ℋ := ℋ) (-(p / 2)) B * opRpow p B) *
            opRpow (-(p / 2)) B := by simp [C, mul_assoc]
      _ = opRpow (ℋ := ℋ) (-(p / 2) + p) B * opRpow (-(p / 2)) B := by
            rw [opRpow_mul_opRpow_of_nonneg_isUnit (ℋ := ℋ) (-(p / 2)) p hB hBu]
      _ = opRpow (ℋ := ℋ) ((-(p / 2) + p) + (-(p / 2))) B := by
            rw [opRpow_mul_opRpow_of_nonneg_isUnit (ℋ := ℋ) (-(p / 2) + p)
              (-(p / 2)) hB hBu]
      _ = opRpow (ℋ := ℋ) 0 B := by ring_nf
      _ = 1 := opRpow_zero_of_nonneg (ℋ := ℋ) hB
  have hXstarX : star X * X = C * opRpow (ℋ := ℋ) p A * C := by
    calc
      star X * X = (C * opRpow (ℋ := ℋ) (p / 2) A) *
          (opRpow (p / 2) A * C) := by
            simp [X, C, star_mul, hCstar,
              star_opRpow_of_nonneg (ℋ := ℋ) (p / 2) hA, mul_assoc]
      _ = C * (opRpow (ℋ := ℋ) (p / 2) A * opRpow (p / 2) A) * C := by
            simp [mul_assoc]
      _ = C * opRpow (ℋ := ℋ) p A * C := by rw [hAhalf]
  have hXle : star X * X ≤ (1 : L ℋ) := by
    rw [hXstarX]
    exact hconj.trans_eq hBcollapse
  simpa [X] using norm_le_one_of_star_mul_self_le_one (ℋ := ℋ) hXle

omit [Nontrivial (L ℋ)] in
/-- Rotate the spectral radius of the mixed sandwich term to the symmetric one. -/
theorem spectralRadius_sandwich_rotation_of_nonneg_isUnit {A B : L ℋ} {p q : ℝ}
    (_hA : 0 ≤ A) (_hAu : IsUnit A) (hB : 0 ≤ B) (hBu : IsUnit B) :
    spectralRadius ℂ
        (opRpow (ℋ := ℋ) (-(p / 2)) B * opRpow ((p + q) / 2) A *
          opRpow (-(q / 2)) B) =
      spectralRadius ℂ
        (opRpow (ℋ := ℋ) (-(p + q) / 4) B * opRpow ((p + q) / 2) A *
          opRpow (-(p + q) / 4) B) := by
  let R : L ℋ := opRpow (ℋ := ℋ) ((q - p) / 4) B
  let S : L ℋ :=
    opRpow (ℋ := ℋ) (-(p + q) / 4) B * opRpow ((p + q) / 2) A *
      opRpow (-(q / 2)) B
  have hRS :
      R * S =
        opRpow (ℋ := ℋ) (-(p / 2)) B * opRpow ((p + q) / 2) A *
          opRpow (-(q / 2)) B := by
    calc
      R * S =
          (opRpow (ℋ := ℋ) ((q - p) / 4) B *
              opRpow (-(p + q) / 4) B) *
            opRpow ((p + q) / 2) A * opRpow (-(q / 2)) B := by
              simp [R, S, mul_assoc]
      _ = opRpow (ℋ := ℋ) (((q - p) / 4) + (-(p + q) / 4)) B *
            opRpow ((p + q) / 2) A * opRpow (-(q / 2)) B := by
              rw [opRpow_mul_opRpow_of_nonneg_isUnit (ℋ := ℋ) ((q - p) / 4)
                (-(p + q) / 4) hB hBu]
      _ = opRpow (ℋ := ℋ) (-(p / 2)) B * opRpow ((p + q) / 2) A *
            opRpow (-(q / 2)) B := by
              congr 2
              ring_nf
  have hSR :
      S * R =
        opRpow (ℋ := ℋ) (-(p + q) / 4) B * opRpow ((p + q) / 2) A *
          opRpow (-(p + q) / 4) B := by
    calc
      S * R =
          opRpow (ℋ := ℋ) (-(p + q) / 4) B * opRpow ((p + q) / 2) A *
            (opRpow (-(q / 2)) B * opRpow ((q - p) / 4) B) := by
              simp [R, S, mul_assoc]
      _ = opRpow (ℋ := ℋ) (-(p + q) / 4) B * opRpow ((p + q) / 2) A *
            opRpow (-(q / 2) + ((q - p) / 4)) B := by
              rw [opRpow_mul_opRpow_of_nonneg_isUnit (ℋ := ℋ) (-(q / 2))
                ((q - p) / 4) hB hBu]
      _ = opRpow (ℋ := ℋ) (-(p + q) / 4) B * opRpow ((p + q) / 2) A *
            opRpow (-(p + q) / 4) B := by
              congr 1
              ring_nf
  calc
    spectralRadius ℂ
        (opRpow (ℋ := ℋ) (-(p / 2)) B * opRpow ((p + q) / 2) A *
          opRpow (-(q / 2)) B) =
      spectralRadius ℂ (R * S) := by rw [hRS]
    _ = spectralRadius ℂ (S * R) := spectralRadius_mul_comm R S
    _ = spectralRadius ℂ
        (opRpow (ℋ := ℋ) (-(p + q) / 4) B * opRpow ((p + q) / 2) A *
          opRpow (-(p + q) / 4) B) := by rw [hSR]

omit [Nontrivial (L ℋ)] in
private theorem opRpow_nonneg_of_nonneg (r : ℝ) {A : L ℋ} (hA : 0 ≤ A) :
    0 ≤ opRpow (ℋ := ℋ) r A := by
  rw [opRpow_eq_cfc_rpow r hA]
  exact CFC.rpow_nonneg

private theorem spectralRadius_toReal_le_norm (T : L ℋ) :
    (spectralRadius ℂ T).toReal ≤ ‖T‖ := by
  exact ENNReal.toReal_le_coe_of_le_coe (spectralRadius_le_nnnorm T)

omit [Nontrivial (L ℋ)] in
private theorem opRpow_order_of_symmetric_sandwich_norm_le_one {A B : L ℋ} {r : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hBu : IsUnit B)
    (hnorm :
      ‖opRpow (ℋ := ℋ) (-(r / 2)) B * opRpow r A * opRpow (-(r / 2)) B‖ ≤ 1) :
    opRpow (ℋ := ℋ) r A ≤ opRpow r B := by
  let C : L ℋ := opRpow (ℋ := ℋ) (-(r / 2)) B
  let D : L ℋ := opRpow (ℋ := ℋ) (r / 2) B
  let T : L ℋ := C * opRpow (ℋ := ℋ) r A * C
  have hCstar : star C = C := by
    simp [C, star_opRpow_of_nonneg (ℋ := ℋ) (-(r / 2)) hB]
  have hDstar : star D = D := by
    simp [D, star_opRpow_of_nonneg (ℋ := ℋ) (r / 2) hB]
  have hTnonneg : 0 ≤ T := by
    simpa [T, C, hCstar, mul_assoc] using
      star_left_conjugate_nonneg (opRpow_nonneg_of_nonneg (ℋ := ℋ) r hA) C
  have hTnorm : ‖T‖ ≤ 1 := by
    simpa [T, C] using hnorm
  have hTle : T ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg T hTnonneg).1 hTnorm
  have hDC : D * C = (1 : L ℋ) := by
    calc
      D * C = opRpow (ℋ := ℋ) (r / 2) B * opRpow (-(r / 2)) B := by
        simp [D, C]
      _ = opRpow (ℋ := ℋ) ((r / 2) + (-(r / 2))) B := by
        exact opRpow_mul_opRpow_of_nonneg_isUnit (ℋ := ℋ) (r / 2) (-(r / 2)) hB hBu
      _ = opRpow (ℋ := ℋ) 0 B := by ring_nf
      _ = 1 := opRpow_zero_of_nonneg (ℋ := ℋ) hB
  have hCD : C * D = (1 : L ℋ) := by
    calc
      C * D = opRpow (ℋ := ℋ) (-(r / 2)) B * opRpow (r / 2) B := by
        simp [D, C]
      _ = opRpow (ℋ := ℋ) (-(r / 2) + (r / 2)) B := by
        exact opRpow_mul_opRpow_of_nonneg_isUnit (ℋ := ℋ) (-(r / 2)) (r / 2) hB hBu
      _ = opRpow (ℋ := ℋ) 0 B := by ring_nf
      _ = 1 := opRpow_zero_of_nonneg (ℋ := ℋ) hB
  have hconj : D * T * D ≤ D * (1 : L ℋ) * D := by
    simpa [hDstar] using star_left_conjugate_le_conjugate hTle D
  have hleft : D * T * D = opRpow (ℋ := ℋ) r A := by
    calc
      D * T * D = (D * C) * opRpow (ℋ := ℋ) r A * (C * D) := by
        simp [T, mul_assoc]
      _ = opRpow (ℋ := ℋ) r A := by
        simp [hDC, hCD]
  have hright : D * (1 : L ℋ) * D = opRpow (ℋ := ℋ) r B := by
    calc
      D * (1 : L ℋ) * D = D * D := by simp
      _ = opRpow (ℋ := ℋ) (r / 2) B * opRpow (r / 2) B := by simp [D]
      _ = opRpow (ℋ := ℋ) ((r / 2) + (r / 2)) B := by
        exact opRpow_mul_opRpow_of_nonneg_isUnit (ℋ := ℋ) (r / 2) (r / 2) hB hBu
      _ = opRpow (ℋ := ℋ) r B := by ring_nf
  calc
    opRpow (ℋ := ℋ) r A = D * T * D := hleft.symm
    _ ≤ D * (1 : L ℋ) * D := hconj
    _ = opRpow (ℋ := ℋ) r B := hright

omit [Nontrivial (L ℋ)] in
private theorem opRpow_symmetric_sandwich_nonneg {A B : L ℋ} {r s : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ opRpow (ℋ := ℋ) r B * opRpow s A * opRpow r B := by
  let C : L ℋ := opRpow (ℋ := ℋ) r B
  have hCstar : star C = C := by
    simp [C, star_opRpow_of_nonneg (ℋ := ℋ) r hB]
  simpa [C, hCstar, mul_assoc] using
    star_left_conjugate_nonneg (opRpow_nonneg_of_nonneg (ℋ := ℋ) s hA) C

/-- The power-order set in the spectral-radius proof is closed under midpoints. -/
theorem opRpow_order_midpoint_of_nonneg_isUnit {A B : L ℋ} {p q : ℝ}
    (hA : 0 ≤ A) (hAu : IsUnit A) (hB : 0 ≤ B) (hBu : IsUnit B)
    (hp : opRpow (ℋ := ℋ) p A ≤ opRpow p B)
    (hq : opRpow (ℋ := ℋ) q A ≤ opRpow q B) :
    opRpow (ℋ := ℋ) ((p + q) / 2) A ≤ opRpow ((p + q) / 2) B := by
  let X : L ℋ := opRpow (ℋ := ℋ) (p / 2) A * opRpow (-(p / 2)) B
  let Y : L ℋ := opRpow (ℋ := ℋ) (q / 2) A * opRpow (-(q / 2)) B
  let M : L ℋ :=
    opRpow (ℋ := ℋ) (-(p / 2)) B * opRpow ((p + q) / 2) A *
      opRpow (-(q / 2)) B
  let T : L ℋ :=
    opRpow (ℋ := ℋ) (-(p + q) / 4) B * opRpow ((p + q) / 2) A *
      opRpow (-(p + q) / 4) B
  have hXnorm : ‖X‖ ≤ 1 := by
    simpa [X] using
      opRpow_order_contraction_of_nonneg_isUnit (ℋ := ℋ) hA hAu hB hBu hp
  have hYnorm : ‖Y‖ ≤ 1 := by
    simpa [Y] using
      opRpow_order_contraction_of_nonneg_isUnit (ℋ := ℋ) hA hAu hB hBu hq
  have hM_eq : star X * Y = M := by
    calc
      star X * Y =
          (opRpow (ℋ := ℋ) (-(p / 2)) B * opRpow (p / 2) A) *
            (opRpow (q / 2) A * opRpow (-(q / 2)) B) := by
              simp [X, Y, star_mul, star_opRpow_of_nonneg (ℋ := ℋ) (p / 2) hA,
                star_opRpow_of_nonneg (ℋ := ℋ) (-(p / 2)) hB]
      _ = opRpow (ℋ := ℋ) (-(p / 2)) B *
            (opRpow (p / 2) A * opRpow (q / 2) A) *
              opRpow (-(q / 2)) B := by
              simp [mul_assoc]
      _ = opRpow (ℋ := ℋ) (-(p / 2)) B *
            opRpow ((p / 2) + (q / 2)) A * opRpow (-(q / 2)) B := by
              rw [opRpow_mul_opRpow_of_nonneg_isUnit (ℋ := ℋ) (p / 2) (q / 2)
                hA hAu]
      _ = M := by
              simp [M]
              congr 2
              ring_nf
  have hMnorm : ‖M‖ ≤ 1 := by
    have hmul : ‖star X * Y‖ ≤ ‖X‖ * ‖Y‖ := by
      simpa [norm_star] using norm_mul_le (star X) Y
    have hprod : ‖X‖ * ‖Y‖ ≤ 1 := by
      nlinarith [hXnorm, hYnorm, norm_nonneg X, norm_nonneg Y]
    have hstarY : ‖star X * Y‖ ≤ 1 := hmul.trans hprod
    simpa [hM_eq] using hstarY
  have hrot : spectralRadius ℂ M = spectralRadius ℂ T := by
    simpa [M, T] using
      spectralRadius_sandwich_rotation_of_nonneg_isUnit (ℋ := ℋ) hA hAu hB hBu
        (p := p) (q := q)
  have hTnonneg : 0 ≤ T := by
    simpa [T] using
      opRpow_symmetric_sandwich_nonneg (ℋ := ℋ) (A := A) (B := B)
        (r := -(p + q) / 4) (s := (p + q) / 2) hA hB
  have hTsa : IsSelfAdjoint T := IsSelfAdjoint.of_nonneg hTnonneg
  have hTnorm : ‖T‖ ≤ 1 := by
    have hspecM : (spectralRadius ℂ M).toReal ≤ 1 :=
      (spectralRadius_toReal_le_norm M).trans hMnorm
    have hspecT : (spectralRadius ℂ T).toReal ≤ 1 := by
      simpa [hrot] using hspecM
    simpa [spectralRadius_toReal_eq_norm_of_isSelfAdjoint hTsa] using hspecT
  refine
    opRpow_order_of_symmetric_sandwich_norm_le_one (ℋ := ℋ)
      (r := (p + q) / 2) hA hB hBu ?_
  have hexp : (-( ((p + q) / 2) / 2) : ℝ) = -(p + q) / 4 := by
    ring_nf
  simpa [T, hexp] using hTnorm

private theorem dyadic_grid_mem_of_midpointClosed {S : Set ℝ}
    (h0 : (0 : ℝ) ∈ S) (h1 : (1 : ℝ) ∈ S)
    (hmid : ∀ x ∈ S, ∀ y ∈ S, (x + y) / 2 ∈ S) :
    ∀ n k : ℕ, k ≤ 2 ^ n → ((k : ℝ) / (2 : ℝ) ^ n) ∈ S := by
  intro n
  induction n with
  | zero =>
      intro k hk
      have hk01 : k = 0 ∨ k = 1 :=
        Nat.le_one_iff_eq_zero_or_eq_one.mp (by simpa using hk)
      rcases hk01 with rfl | rfl
      · simpa using h0
      · simpa using h1
  | succ n ih =>
      intro k hk
      rcases Nat.mod_two_eq_zero_or_one k with hmod | hmod
      · let j : ℕ := k / 2
        have hk_eq : k = 2 * j := by
          have h := Nat.div_add_mod k 2
          rw [hmod] at h
          omega
        have hj : j ≤ 2 ^ n := by
          have hk' : 2 * j ≤ 2 * 2 ^ n := by
            simpa [hk_eq, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hk
          omega
        have hmem := ih j hj
        convert hmem using 1
        rw [hk_eq]
        field_simp [pow_succ]
        norm_num [Nat.cast_mul]
        ring_nf
      · let j : ℕ := k / 2
        have hk_eq : k = 2 * j + 1 := by
          have h := Nat.div_add_mod k 2
          rw [hmod] at h
          omega
        have hj : j ≤ 2 ^ n := by
          have hk' : 2 * j + 1 ≤ 2 * 2 ^ n := by
            simpa [hk_eq, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hk
          omega
        have hj1 : j + 1 ≤ 2 ^ n := by
          have hk' : 2 * j + 1 ≤ 2 * 2 ^ n := by
            simpa [hk_eq, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hk
          omega
        have hleft := ih j hj
        have hright := ih (j + 1) hj1
        have hmidmem :=
          hmid ((j : ℝ) / (2 : ℝ) ^ n) hleft
            (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) hright
        convert hmidmem using 1
        rw [hk_eq]
        field_simp [pow_succ]
        norm_num [Nat.cast_mul, Nat.cast_add]
        ring_nf

private theorem tendsto_dyadic_floor_hp {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Filter.Tendsto
      (fun n : ℕ => ((⌊x * (2 : ℝ) ^ n⌋₊ : ℕ) : ℝ) / (2 : ℝ) ^ n)
      Filter.atTop (nhds x) := by
  exact (tendsto_nat_floor_mul_div_atTop (R := ℝ) hx.1).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

/-- A closed midpoint-closed subset of `[0,1]` containing the endpoints is all of `[0,1]`. -/
theorem closed_midpointClosed_subset_Icc_eq_Icc {S : Set ℝ}
    (hsub : S ⊆ Set.Icc (0 : ℝ) 1) (hclosed : IsClosed S)
    (h0 : (0 : ℝ) ∈ S) (h1 : (1 : ℝ) ∈ S)
    (hmid : ∀ x ∈ S, ∀ y ∈ S, (x + y) / 2 ∈ S) :
    S = Set.Icc (0 : ℝ) 1 := by
  apply Set.Subset.antisymm hsub
  intro x hx
  let d : ℕ → ℝ := fun n => ((⌊x * (2 : ℝ) ^ n⌋₊ : ℕ) : ℝ) / (2 : ℝ) ^ n
  have hd_mem : ∀ n, d n ∈ S := by
    intro n
    have hk_le : ⌊x * (2 : ℝ) ^ n⌋₊ ≤ 2 ^ n := by
      apply Nat.floor_le_of_le
      have hpow_nonneg : 0 ≤ (2 : ℝ) ^ n := pow_nonneg (by norm_num) n
      calc
        x * (2 : ℝ) ^ n ≤ 1 * (2 : ℝ) ^ n := by
          exact mul_le_mul_of_nonneg_right hx.2 hpow_nonneg
        _ = (2 : ℝ) ^ n := by simp
        _ = ((2 ^ n : ℕ) : ℝ) := by norm_num
    have hdyadic :=
      dyadic_grid_mem_of_midpointClosed h0 h1 hmid n ⌊x * (2 : ℝ) ^ n⌋₊ hk_le
    simpa [d] using hdyadic
  have hd_tendsto : Filter.Tendsto d Filter.atTop (nhds x) := by
    simpa [d, mul_comm] using tendsto_dyadic_floor_hp (x := x) hx
  exact hclosed.mem_of_tendsto hd_tendsto (Filter.Eventually.of_forall hd_mem)

omit [Nontrivial (L ℋ)] in
private theorem spectrum_subset_Ioi_of_nonneg_isUnit {A : L ℋ}
    (hA : 0 ≤ A) (hAu : IsUnit A) :
    spectrum ℝ A ⊆ Set.Ioi (0 : ℝ) := by
  intro x hx
  have hx_nonneg : 0 ≤ x := spectrum_nonneg_of_nonneg hA hx
  have hx_ne : x ≠ 0 := by
    intro hx0
    have hzero : (0 : ℝ) ∈ spectrum ℝ A := by
      simpa [hx0] using hx
    exact (spectrum.zero_notMem ℝ hAu) hzero
  exact lt_of_le_of_ne hx_nonneg (Ne.symm hx_ne)

omit [Nontrivial (L ℋ)] in
private theorem tendstoUniformlyOn_rpow_exponent_spectrum {A : L ℋ} {r₀ : ℝ}
    (hA : 0 ≤ A) (hAu : IsUnit A) :
    TendstoUniformlyOn (fun r x : ℝ => x ^ r) (fun x : ℝ => x ^ r₀) (𝓝 r₀)
      (spectrum ℝ A) := by
  let s : Set ℝ := spectrum ℝ A
  have hspos : s ⊆ Set.Ioi (0 : ℝ) := spectrum_subset_Ioi_of_nonneg_isUnit hA hAu
  have hcont : ∀ r : ℝ, ContinuousOn (fun x : ℝ => x ^ r) s := by
    intro r
    exact continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (hspos hx)))
  let F : ℝ → C(s, ℝ) := fun r =>
    ⟨fun x : s => (x : ℝ) ^ r, (hcont r).restrict⟩
  have hFcont : Continuous F := by
    refine ContinuousMap.continuous_of_continuous_uncurry F ?_
    change Continuous (fun z : ℝ × s => (z.2 : ℝ) ^ z.1)
    exact (continuous_subtype_val.comp continuous_snd).rpow continuous_fst
      (fun z => Or.inl (ne_of_gt (hspos z.2.2)))
  have htendsto : Filter.Tendsto F (𝓝 r₀) (𝓝 (F r₀)) := hFcont.continuousAt
  exact ((hcont r₀).tendsto_restrict_iff_tendstoUniformlyOn (p := 𝓝 r₀)
    (hF := hcont)).mp (by
      simpa [F, s] using htendsto)

omit [Nontrivial (L ℋ)] in
@[fun_prop] private theorem continuous_opRpow_exponent_of_nonneg_isUnit {A : L ℋ}
    (hA : 0 ≤ A) (hAu : IsUnit A) :
    Continuous (fun r : ℝ => opRpow (ℋ := ℋ) r A) := by
  rw [continuous_iff_continuousAt]
  intro r₀
  change ContinuousAt
    (fun r : ℝ =>
      cfc (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ r) A) r₀
  refine continuousAt_cfc_fun (tendstoUniformlyOn_rpow_exponent_spectrum hA hAu) ?_
  filter_upwards with r
  exact continuousOn_id.rpow_const fun x hx =>
    Or.inl (ne_of_gt (spectrum_subset_Ioi_of_nonneg_isUnit hA hAu hx))

omit [Nontrivial (L ℋ)] in
private theorem opRpow_order_set_closed_of_nonneg_isUnit {A B : L ℋ}
    (hA : 0 ≤ A) (hAu : IsUnit A) (hB : 0 ≤ B) (hBu : IsUnit B) :
    IsClosed {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧
      opRpow (ℋ := ℋ) r A ≤ opRpow r B} := by
  exact isClosed_Icc.inter <|
    isClosed_le (continuous_opRpow_exponent_of_nonneg_isUnit hA hAu)
      (continuous_opRpow_exponent_of_nonneg_isUnit hB hBu)

/-- Positive-invertible Löwner--Heinz from the spectral-radius midpoint argument. -/
theorem lownerHeinz_invertible_of_spectralRadius {A B : L ℋ} {p : ℝ}
    (hA : 0 ≤ A) (hAu : IsUnit A) (hB : 0 ≤ B) (hBu : IsUnit B)
    (hAB : A ≤ B) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    opRpow (ℋ := ℋ) p A ≤ opRpow p B := by
  let Δ : Set ℝ := {r : ℝ | r ∈ Set.Icc (0 : ℝ) 1 ∧
    opRpow (ℋ := ℋ) r A ≤ opRpow r B}
  have hsub : Δ ⊆ Set.Icc (0 : ℝ) 1 := by
    intro r hr
    exact hr.1
  have hclosed : IsClosed Δ := by
    simpa [Δ] using opRpow_order_set_closed_of_nonneg_isUnit hA hAu hB hBu
  have h0 : (0 : ℝ) ∈ Δ := by
    refine ⟨by norm_num, ?_⟩
    rw [opRpow_zero_of_nonneg (ℋ := ℋ) hA, opRpow_zero_of_nonneg (ℋ := ℋ) hB]
  have h1 : (1 : ℝ) ∈ Δ := by
    refine ⟨by norm_num, ?_⟩
    simpa [opRpow_one_of_nonneg (ℋ := ℋ) hA, opRpow_one_of_nonneg (ℋ := ℋ) hB]
      using hAB
  have hmid : ∀ x ∈ Δ, ∀ y ∈ Δ, (x + y) / 2 ∈ Δ := by
    intro x hx y hy
    refine ⟨?_, ?_⟩
    · constructor <;> nlinarith [hx.1.1, hx.1.2, hy.1.1, hy.1.2]
    · exact opRpow_order_midpoint_of_nonneg_isUnit (ℋ := ℋ) hA hAu hB hBu hx.2 hy.2
  have hΔ : Δ = Set.Icc (0 : ℝ) 1 :=
    closed_midpointClosed_subset_Icc_eq_Icc hsub hclosed h0 h1 hmid
  have hpΔ : p ∈ Δ := by
    rw [hΔ]
    exact hp
  exact hpΔ.2

omit [Nontrivial (L ℋ)] in
private theorem isStrictlyPositive_pos_smul_one {ε : ℝ} (hε : 0 < ε) :
    IsStrictlyPositive (ε • (1 : L ℋ)) := by
  refine (CStarAlgebra.isStrictlyPositive_TFAE (A := L ℋ) (a := ε • (1 : L ℋ))).out
    0 7 |>.mpr ?_
  constructor
  · exact smul_nonneg hε.le zero_le_one
  · change IsUnit ((ε : ℂ) • (1 : L ℋ))
    rw [Algebra.smul_def]
    exact IsUnit.mul (IsUnit.map (algebraMap ℂ (L ℋ))
      (isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hε.ne'))) isUnit_one

omit [Nontrivial (L ℋ)] in
private theorem regularized_nonneg_isUnit {A : L ℋ} {ε : ℝ}
    (hA : 0 ≤ A) (hε : 0 < ε) :
    0 ≤ A + ε • (1 : L ℋ) ∧ IsUnit (A + ε • (1 : L ℋ)) := by
  have hstrict : IsStrictlyPositive (A + ε • (1 : L ℋ)) :=
    IsStrictlyPositive.nonneg_add hA (isStrictlyPositive_pos_smul_one (ℋ := ℋ) hε)
  exact ⟨hstrict.nonneg, hstrict.isUnit⟩

omit [Nontrivial (L ℋ)] in
/-- Continuity of the nonnegative power along the `εI` regularization, written with `cfc`. -/
private theorem tendsto_cfc_rpow_regularization {A : L ℋ} {p : ℝ}
    (hA : 0 ≤ A) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    Filter.Tendsto
      (fun ε : ℝ => cfc (fun x : NNReal => x ^ p) (A + ((Real.toNNReal ε : ℝ) • (1 : L ℋ))))
      (𝓝[>] (0 : ℝ)) (𝓝 (cfc (fun x : NNReal => x ^ p) A)) := by
  let Areg : ℝ → L ℋ := fun ε => A + ((Real.toNNReal ε : ℝ) • (1 : L ℋ))
  have hcont : Continuous fun ε : ℝ => Areg ε := by
    dsimp [Areg]
    fun_prop
  have hnonneg : ∀ ε : ℝ, 0 ≤ Areg ε := by
    intro ε
    dsimp [Areg]
    exact add_nonneg hA (smul_nonneg (Real.toNNReal ε).2 zero_le_one)
  have hcfc : Continuous fun ε : ℝ => cfc (fun x : NNReal => x ^ p) (Areg ε) := by
    refine Continuous.cfc_nnreal_of_mem_nhdsSet
      (f := fun x : NNReal => x ^ p) (s := Set.univ) ?_ hcont hnonneg ?_
    · simp
    · exact (NNReal.continuous_rpow_const hp.1).continuousOn
  have htendsto := (hcfc.continuousAt (x := (0 : ℝ))).tendsto
  have htarget : Areg 0 = A := by
    simp [Areg]
  have htendsto0 :
      Filter.Tendsto (fun ε : ℝ => cfc (fun x : NNReal => x ^ p) (Areg ε))
        (𝓝 (0 : ℝ)) (𝓝 (cfc (fun x : NNReal => x ^ p) A)) := by
    simpa [htarget] using htendsto
  exact htendsto0.mono_left nhdsWithin_le_nhds

omit [Nontrivial (L ℋ)] in
/-- For `ε > 0`, the power of the regularized operator agrees with the `cfc` form used in
`tendsto_cfc_rpow_regularization`. -/
private theorem opRpow_regularization_eq_cfc {A : L ℋ} {p ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    opRpow (ℋ := ℋ) p (A + ε • (1 : L ℋ)) =
      cfc (fun x : NNReal => x ^ p) (A + ((Real.toNNReal ε : ℝ) • (1 : L ℋ))) := by
  have hAε : 0 ≤ A + ε • (1 : L ℋ) := add_nonneg hA (smul_nonneg hε.le zero_le_one)
  rw [opRpow_eq_cfc_rpow (ℋ := ℋ) p hAε, CFC.rpow_def, Real.coe_toNNReal ε hε.le]

omit [Nontrivial (L ℋ)] in
/-- Positive powers are continuous under the right-sided `εI` regularization of a positive
operator. -/
theorem opRpow_regularization_tendsto_of_nonneg {A : L ℋ} {p : ℝ}
    (hA : 0 ≤ A) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    Filter.Tendsto (fun ε : ℝ => opRpow (ℋ := ℋ) p (A + ε • (1 : L ℋ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (opRpow p A)) := by
  have heq :
      (fun ε : ℝ => opRpow (ℋ := ℋ) p (A + ε • (1 : L ℋ))) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun ε : ℝ =>
          cfc (fun x : NNReal => x ^ p) (A + ((Real.toNNReal ε : ℝ) • (1 : L ℋ)))) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact opRpow_regularization_eq_cfc (ℋ := ℋ) hA hε
  have htarget_eq : opRpow (ℋ := ℋ) p A = cfc (fun x : NNReal => x ^ p) A := by
    rw [opRpow_eq_cfc_rpow (ℋ := ℋ) p hA]
    rw [CFC.rpow_def]
  rw [htarget_eq]
  exact (tendsto_cfc_rpow_regularization (ℋ := ℋ) hA hp).congr' heq.symm

omit [Nontrivial (L ℋ)] in
/-- Order inequalities are closed under right-sided limits. -/
theorem le_of_tendsto_nhdsGT_zero_of_eventually_le {F G : ℝ → L ℋ} {X Y : L ℋ}
    (hF : Filter.Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 X))
    (hG : Filter.Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 Y))
    (hle : ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε ≤ G ε) :
    X ≤ Y := by
  have hdiff :
      Filter.Tendsto (fun ε : ℝ => G ε - F ε) (𝓝[>] (0 : ℝ)) (𝓝 (Y - X)) :=
    hG.sub hF
  have hdiff_nonneg_eventually :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), G ε - F ε ∈ {Z : L ℋ | 0 ≤ Z} := by
    exact hle.mono fun ε hε => by simpa using sub_nonneg.mpr hε
  have hlimit_nonneg : 0 ≤ Y - X := by
    exact CStarAlgebra.isClosed_nonneg.mem_of_tendsto hdiff hdiff_nonneg_eventually
  exact sub_nonneg.mp hlimit_nonneg


omit [Nontrivial (L ℋ)] in
/-- The `εI` regularization package needed to remove the invertibility hypothesis. -/
theorem lownerHeinz_epsilon_regularization {A B : L ℋ} {p : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (∀ ε : ℝ, 0 < ε →
      0 ≤ A + ε • (1 : L ℋ) ∧ IsUnit (A + ε • (1 : L ℋ)) ∧
      0 ≤ B + ε • (1 : L ℋ) ∧ IsUnit (B + ε • (1 : L ℋ)) ∧
      A + ε • (1 : L ℋ) ≤ B + ε • (1 : L ℋ)) ∧
    Filter.Tendsto (fun ε : ℝ => opRpow (ℋ := ℋ) p (A + ε • (1 : L ℋ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (opRpow p A)) ∧
    Filter.Tendsto (fun ε : ℝ => opRpow (ℋ := ℋ) p (B + ε • (1 : L ℋ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (opRpow p B)) := by
  have hB : 0 ≤ B := hA.trans hAB
  refine ⟨?_, opRpow_regularization_tendsto_of_nonneg (ℋ := ℋ) hA hp,
    opRpow_regularization_tendsto_of_nonneg (ℋ := ℋ) hB hp⟩
  intro ε hε
  have hAreg := regularized_nonneg_isUnit (ℋ := ℋ) hA hε
  have hBreg := regularized_nonneg_isUnit (ℋ := ℋ) hB hε
  refine ⟨hAreg.1, hAreg.2, hBreg.1, hBreg.2, ?_⟩
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_left hAB (ε • (1 : L ℋ))

end LownerHeinzSpectralRadius

universe u

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial (L ℋ)]

/-- Löwner--Heinz on positive operators, proved by the Hiai--Yanagi spectral-radius route. -/
theorem lownerHeinz_of_spectralRadius {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    {A B : L ℋ} (hA0 : 0 ≤ A) (hAB : A ≤ B) :
    opRpow (ℋ := ℋ) p A ≤ opRpow (ℋ := ℋ) p B := by
  rcases LownerHeinzSpectralRadius.lownerHeinz_epsilon_regularization
      (ℋ := ℋ) hA0 hAB hp with ⟨hreg, hAtend, hBtend⟩
  refine LownerHeinzSpectralRadius.le_of_tendsto_nhdsGT_zero_of_eventually_le
    (ℋ := ℋ) hAtend hBtend ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hpack := hreg ε hε
  exact LownerHeinzSpectralRadius.lownerHeinz_invertible_of_spectralRadius
    (ℋ := ℋ) hpack.1 hpack.2.1 hpack.2.2.1 hpack.2.2.2.1 hpack.2.2.2.2 hp

end HansenPedersen
