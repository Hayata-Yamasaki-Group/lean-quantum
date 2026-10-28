/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances


/-!
# Positive functional calculus on Hilbert-Schmidt operators

This file packages the square-root and inverse-square-root functional calculus
for strictly positive Hilbert-Schmidt operators. The key assumption is that the
real spectrum is contained in `(0, ∞)`, so real powers with exponents `1 / 2`
and `-1 / 2` are continuous on the spectrum and multiply as expected.

## Main results

* `hsSqrtPos` and `hsInvSqrtPos`: square-root and inverse-square-root
  operators defined by real CFC.
* `hsSqrtPos_mul_invSqrtPos` and `hsInvSqrtPos_mul_sqrtPos`: the two inverse
  identities on positive spectrum.
* `hsSqrtPos_sq`, `hsInvSqrtPos_mul_self_eq_ringInverse`, and the conjugation
  identities used to normalize strict positive Hilbert-Schmidt forms.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Chapter 6, positive definite Hilbert-Schmidt
  calculus used around Definition 6.1.
-/

namespace HiaiPetz

open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- A nonnegative Hilbert-Schmidt operator that is a unit has strictly positive
real spectrum. -/
theorem hsSpectrumIoi_of_nonneg_isUnit
    {n : ℕ} {T : HSOp n}
    (hT0 : 0 ≤ T) (hTu : IsUnit T) :
    spectrum ℝ T ⊆ Set.Ioi (0 : ℝ) := by
  have hTpos : IsStrictlyPositive T := hTu.isStrictlyPositive hT0
  exact (CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mp hTpos).2

/-- Real powers are continuous on the real spectrum of a Hilbert-Schmidt
operator when that spectrum lies in `(0, ∞)`. -/
@[fun_prop] theorem continuousOn_rpow_const_of_spectrumIoi
    {n : ℕ} {T : HSOp n} {q : ℝ}
    (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    ContinuousOn (fun x : ℝ ↦ x ^ q) (spectrum ℝ T) := by
  intro x hx
  have hx0 : 0 < x := by
    simpa [Set.mem_Ioi] using hσT hx
  exact (Real.continuousAt_rpow_const x q (Or.inl (ne_of_gt hx0))).continuousWithinAt

/-- Positive square root of a Hilbert-Schmidt operator, defined as real
functional calculus of `x ↦ x ^ (1 / 2)`. -/
noncomputable def hsSqrtPos {n : ℕ} (T : HSOp n) : HSOp n :=
  hsCfcR (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) T

/-- Positive inverse square root of a Hilbert-Schmidt operator, defined as real
functional calculus of `x ↦ x ^ (-1 / 2)`. -/
noncomputable def hsInvSqrtPos {n : ℕ} (T : HSOp n) : HSOp n :=
  hsCfcR (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) T

/-- The positive square root of a self-adjoint Hilbert-Schmidt operator is
self-adjoint. -/
theorem hsSqrtPos_isSelfAdjoint
    {n : ℕ} {T : HSOp n} (_hT : IsSelfAdjoint T) :
    IsSelfAdjoint (hsSqrtPos T) := by
  change IsSelfAdjoint (hsCfcR (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) T)
  exact
    IsSelfAdjoint.cfc (R := ℝ) (A := HSOp n) (f := fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) (a := T)

/-- The positive inverse square root of a self-adjoint Hilbert-Schmidt operator
is self-adjoint. -/
theorem hsInvSqrtPos_isSelfAdjoint
    {n : ℕ} {T : HSOp n} (_hT : IsSelfAdjoint T) :
    IsSelfAdjoint (hsInvSqrtPos T) := by
  change IsSelfAdjoint (hsCfcR (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) T)
  exact
    IsSelfAdjoint.cfc (R := ℝ) (A := HSOp n) (f := fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (a := T)

/-- On positive real spectrum, the positive square root followed by the inverse
square root is the identity Hilbert-Schmidt operator. -/
theorem hsSqrtPos_mul_invSqrtPos
    {n : ℕ} {T : HSOp n}
    (hT : IsSelfAdjoint T)
    (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    hsSqrtPos T * hsInvSqrtPos T = (1 : HSOp n) := by
  have hcont_sqrt :
      ContinuousOn (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) (spectrum ℝ T) :=
    continuousOn_rpow_const_of_spectrumIoi (T := T) (q := (1 : ℝ) / 2) hσT
  have hcont_inv :
      ContinuousOn (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (spectrum ℝ T) :=
    continuousOn_rpow_const_of_spectrumIoi (T := T) (q := (-1 : ℝ) / 2) hσT
  calc
    hsSqrtPos T * hsInvSqrtPos T
        = hsCfcR
            (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2) * x ^ ((-1 : ℝ) / 2)) T := by
              simpa [hsSqrtPos, hsInvSqrtPos, hsCfcR] using
                (cfc_mul (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
                  (f := fun x : ℝ ↦ x ^ ((1 : ℝ) / 2))
                  (g := fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2))
                  (a := T) hcont_sqrt hcont_inv).symm
    _ = hsCfcR (fun _ : ℝ ↦ (1 : ℝ)) T := by
          apply cfc_congr
          intro x hx
          have hx0 : 0 < x := by
            simpa [Set.mem_Ioi] using hσT hx
          have hpow := Real.rpow_add hx0 ((1 : ℝ) / 2) ((-1 : ℝ) / 2)
          have hsum : ((1 : ℝ) / 2 + (-1 : ℝ) / 2 : ℝ) = 0 := by ring
          rw [hsum, Real.rpow_zero] at hpow
          simpa using hpow.symm
    _ = (1 : HSOp n) := by
          simpa [hsCfcR] using
            (cfc_const_one (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint) (a := T) (ha := hT))

/-- On positive real spectrum, the inverse square root followed by the positive
square root is the identity Hilbert-Schmidt operator. -/
theorem hsInvSqrtPos_mul_sqrtPos
    {n : ℕ} {T : HSOp n}
    (hT : IsSelfAdjoint T)
    (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    hsInvSqrtPos T * hsSqrtPos T = (1 : HSOp n) := by
  have hcont_sqrt :
      ContinuousOn (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) (spectrum ℝ T) :=
    continuousOn_rpow_const_of_spectrumIoi (T := T) (q := (1 : ℝ) / 2) hσT
  have hcont_inv :
      ContinuousOn (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (spectrum ℝ T) :=
    continuousOn_rpow_const_of_spectrumIoi (T := T) (q := (-1 : ℝ) / 2) hσT
  calc
    hsInvSqrtPos T * hsSqrtPos T
        = hsCfcR
            (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2)) T := by
              simpa [hsSqrtPos, hsInvSqrtPos, hsCfcR] using
                (cfc_mul (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
                  (f := fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2))
                  (g := fun x : ℝ ↦ x ^ ((1 : ℝ) / 2))
                  (a := T) hcont_inv hcont_sqrt).symm
    _ = hsCfcR (fun _ : ℝ ↦ (1 : ℝ)) T := by
          apply cfc_congr
          intro x hx
          have hx0 : 0 < x := by
            simpa [Set.mem_Ioi] using hσT hx
          have hpow := Real.rpow_add hx0 ((-1 : ℝ) / 2) ((1 : ℝ) / 2)
          have hsum : (((-1 : ℝ) / 2) + (1 : ℝ) / 2 : ℝ) = 0 := by ring
          rw [hsum, Real.rpow_zero] at hpow
          simpa using hpow.symm
    _ = (1 : HSOp n) := by
          simpa [hsCfcR] using
            (cfc_const_one (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint) (a := T) (ha := hT))

/-- On positive real spectrum, the square of the positive square root recovers
the original Hilbert-Schmidt operator. -/
theorem hsSqrtPos_sq
    {n : ℕ} {T : HSOp n}
    (hT : IsSelfAdjoint T)
    (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    hsSqrtPos T * hsSqrtPos T = T := by
  have hcont_sqrt :
      ContinuousOn (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) (spectrum ℝ T) :=
    continuousOn_rpow_const_of_spectrumIoi (T := T) (q := (1 : ℝ) / 2) hσT
  calc
    hsSqrtPos T * hsSqrtPos T
        = hsCfcR
            (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2)) T := by
              simpa [hsSqrtPos, hsCfcR] using
                (cfc_mul (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
                  (f := fun x : ℝ ↦ x ^ ((1 : ℝ) / 2))
                  (g := fun x : ℝ ↦ x ^ ((1 : ℝ) / 2))
                  (a := T) hcont_sqrt hcont_sqrt).symm
    _ = hsCfcR (fun x : ℝ ↦ x) T := by
          apply cfc_congr
          intro x hx
          have hx0 : 0 < x := by
            simpa [Set.mem_Ioi] using hσT hx
          have hpow := Real.rpow_add hx0 ((1 : ℝ) / 2) ((1 : ℝ) / 2)
          have hsum : (((1 : ℝ) / 2) + (1 : ℝ) / 2 : ℝ) = 1 := by ring
          rw [hsum, Real.rpow_one] at hpow
          simpa using hpow.symm
    _ = T := by
          simpa [hsCfcR] using (cfc_id' (R := ℝ) (a := T) (ha := hT))

/-- Functional calculus of `x ↦ x⁻¹` agrees with the ring inverse for a
self-adjoint Hilbert-Schmidt operator with positive real spectrum. -/
theorem hsCfcR_inv_eq_ringInverse
    {n : ℕ} {T : HSOp n}
    (hT : IsSelfAdjoint T)
    (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    hsCfcR (fun x : ℝ ↦ x⁻¹) T = Ring.inverse T := by
  dsimp [hsCfcR]
  simpa [cfc_id' (R := ℝ) (a := T) (ha := hT)] using
    (cfc_inv (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint) (f := fun x : ℝ ↦ x)
      (a := T) (fun x hx ↦ ne_of_gt (by simpa [Set.mem_Ioi] using hσT hx)) (ha := hT))

/-- The square of the inverse square root is the ring inverse on positive real
spectrum. -/
theorem hsInvSqrtPos_mul_self_eq_ringInverse
    {n : ℕ} {T : HSOp n}
    (hT : IsSelfAdjoint T)
    (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    hsInvSqrtPos T * hsInvSqrtPos T = Ring.inverse T := by
  have hcont_inv :
      ContinuousOn (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (spectrum ℝ T) :=
    continuousOn_rpow_const_of_spectrumIoi (T := T) (q := (-1 : ℝ) / 2) hσT
  calc
    hsInvSqrtPos T * hsInvSqrtPos T
        = hsCfcR
            (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2) * x ^ ((-1 : ℝ) / 2)) T := by
              simpa [hsInvSqrtPos, hsCfcR] using
                (cfc_mul (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
                  (f := fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2))
                  (g := fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2))
                  (a := T) hcont_inv hcont_inv).symm
    _ = hsCfcR (fun x : ℝ ↦ x⁻¹) T := by
          apply cfc_congr
          intro x hx
          have hx0 : 0 < x := by
            simpa [Set.mem_Ioi] using hσT hx
          have hpow := Real.rpow_add hx0 ((-1 : ℝ) / 2) ((-1 : ℝ) / 2)
          have hsum : (((-1 : ℝ) / 2) + (-1 : ℝ) / 2 : ℝ) = -1 := by ring
          rw [hsum, Real.rpow_neg_one] at hpow
          simpa using hpow.symm
    _ = Ring.inverse T := hsCfcR_inv_eq_ringInverse hT hσT

/-- Conjugating a positive Hilbert-Schmidt operator by its inverse square root
normalizes it to the identity. -/
theorem hsInvSqrtPos_mul_self_mul_invSqrtPos_eq_one
    {n : ℕ} {T : HSOp n}
    (hT : IsSelfAdjoint T)
    (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    hsInvSqrtPos T * T * hsInvSqrtPos T = (1 : HSOp n) := by
  calc
    hsInvSqrtPos T * T * hsInvSqrtPos T
        = hsInvSqrtPos T * (hsSqrtPos T * hsSqrtPos T) *
            hsInvSqrtPos T := by
              rw [hsSqrtPos_sq hT hσT]
    _ = (hsInvSqrtPos T * hsSqrtPos T) *
          (hsSqrtPos T * hsInvSqrtPos T) := by
            simp [mul_assoc]
    _ = (1 : HSOp n) := by
          simp [hsInvSqrtPos_mul_sqrtPos hT hσT,
            hsSqrtPos_mul_invSqrtPos hT hσT]

/-- Conjugating the ring inverse by the positive square root normalizes it to
the identity. -/
theorem hsSqrtPos_mul_ringInverse_mul_sqrtPos_eq_one
    {n : ℕ} {T : HSOp n}
    (hT : IsSelfAdjoint T)
    (hσT : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    hsSqrtPos T * Ring.inverse T * hsSqrtPos T = (1 : HSOp n) := by
  rw [← hsInvSqrtPos_mul_self_eq_ringInverse hT hσT]
  calc
    hsSqrtPos T * (hsInvSqrtPos T * hsInvSqrtPos T) *
        hsSqrtPos T
        = (hsSqrtPos T * hsInvSqrtPos T) *
            (hsInvSqrtPos T * hsSqrtPos T) := by
              simp [mul_assoc]
    _ = (1 : HSOp n) := by
          simp [hsSqrtPos_mul_invSqrtPos hT hσT,
            hsInvSqrtPos_mul_sqrtPos hT hσT]

end MatrixScopedInstances

end HiaiPetz

namespace HiaiPetz.PositiveCFC

section

open HiaiPetz Matrix Unitary
open scoped MatrixOrder ComplexOrder CStarAlgebra

/-- Right-hand reconstruction identity: `TA^(-1/2) 1 TA^(-1/2)` is
`TA⁻¹` under the positive-spectrum hypothesis. -/
theorem hsInvSqrtPos_mul_one_mul_self_eq_ringInverse
    {k : ℕ}
    {TA : HSOp (Nat.succ k)}
    (hTA_sa : IsSelfAdjoint TA)
    (hσTA : spectrum ℝ TA ⊆ Set.Ioi (0 : ℝ)) :
    hsInvSqrtPos TA * (1 : HSOp (Nat.succ k)) * hsInvSqrtPos TA =
      Ring.inverse TA := by
  let invSqrtTA : HSOp (Nat.succ k) := hsInvSqrtPos TA
  have hInvSqTA : invSqrtTA.comp invSqrtTA = Ring.inverse TA := by
    simpa [invSqrtTA] using hsInvSqrtPos_mul_self_eq_ringInverse hTA_sa hσTA
  calc
    hsInvSqrtPos TA * (1 : HSOp (Nat.succ k)) * hsInvSqrtPos TA
        = invSqrtTA * invSqrtTA := by
            simp [hsInvSqrtPos, invSqrtTA]
    _ = invSqrtTA.comp invSqrtTA := rfl
    _ = Ring.inverse TA := hInvSqTA

end

end HiaiPetz.PositiveCFC
