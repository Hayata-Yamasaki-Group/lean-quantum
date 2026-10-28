/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.CompressionInequality.SpectralBounds

/-!
# Contraction inequality implies ratio monotonicity

This module proves the implication from the Jensen contraction inequality to
monotonicity of the ratio function `t ↦ f t / t` on the positive part of the
half-open ray.  The proof uses real functional calculus for square roots and
inverse square roots of strictly positive operators, converts `A ≤ B` into a
contraction, and conjugates the condition-II inequality by inverse square
roots.

## Main results

* `sqrtPos` and `invSqrtPos`: functional-calculus square root and inverse
  square root on positive-spectrum operators.
* `ratio_cfc_eq_invSqrtPos_mul_cfcR_mul_invSqrtPos`: CFC expression for the
  ratio function.
* `conditionII_implies_conditionV`: condition II implies ratio monotonicity.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021,
  Section 5.1.
-/

namespace HansenPedersen

universe u v

open CFC MeasureTheory
open scoped Topology
open Filter

section NormalCFC517

namespace ConvexityCharacterization

section ConditionIItoV

open scoped ComplexOrder

variable {K : Type u}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
private lemma spectrum_subset_Ioi_of_positiveOpenRay {α : WithTop ℝ} {A : L K}
    (hσA : spectrum ℝ A ⊆ positiveOpenRay α) :
    spectrum ℝ A ⊆ Set.Ioi (0 : ℝ) := by
  intro x hx
  simpa [Set.mem_Ioi] using (hσA hx).1

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
/-- A positive-half-open spectral bound also gives the corresponding
half-open spectral bound after forgetting strict positivity at zero. -/
lemma spectrum_subset_halfOpenRay_of_positiveOpenRay {α : WithTop ℝ} {A : L K}
    (hσA : spectrum ℝ A ⊆ positiveOpenRay α) :
    spectrum ℝ A ⊆ halfOpenRay α := by
  intro x hx
  exact ⟨le_of_lt (hσA hx).1, (hσA hx).2⟩

omit [Nontrivial (L K)] in
/-- A self-adjoint operator whose real spectrum lies in the positive half-open
ray is nonnegative. -/
lemma nonneg_of_spectrum_subset_positiveOpenRay {α : WithTop ℝ} {A : L K}
    (hA : IsSelfAdjoint A)
    (hσA : spectrum ℝ A ⊆ positiveOpenRay α) :
    0 ≤ A :=
  HansenPedersen.nonneg_of_isSelfAdjoint_of_spectrum_subset_Ici hA <| by
    intro x hx
    exact le_of_lt ((hσA hx).1)

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
@[fun_prop] private lemma continuousOn_rpow_const_of_positiveSpectrum
    {α : WithTop ℝ} {A : L K} {q : ℝ}
    (hσA : spectrum ℝ A ⊆ positiveOpenRay α) :
    ContinuousOn (fun x : ℝ ↦ x ^ q) (spectrum ℝ A) := by
  intro x hx
  have hx0 : 0 < x := (hσA hx).1
  exact (Real.continuousAt_rpow_const x q (Or.inl (ne_of_gt hx0))).continuousWithinAt

/-- Positive square root of an operator, realized by real functional calculus
with the scalar function `x ↦ x^(1/2)`. -/
noncomputable def sqrtPos {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    (A : L K) : L K :=
  cfcR (ℋ := K) (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) A

/-- Inverse positive square root of an operator, realized by real functional
calculus with the scalar function `x ↦ x^(-1/2)`. -/
noncomputable def invSqrtPos {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]
    (A : L K) : L K :=
  cfcR (ℋ := K) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) A

/-- The positive square root obtained by real CFC is self-adjoint. -/
lemma sqrtPos_selfAdjoint {A : L K} :
    IsSelfAdjoint (sqrtPos A) := by
  simp [sqrtPos, cfcR]

/-- The inverse positive square root obtained by real CFC is self-adjoint. -/
lemma invSqrtPos_selfAdjoint {A : L K} :
    IsSelfAdjoint (invSqrtPos A) := by
  simp [invSqrtPos, cfcR]

/-- On positive spectrum, the square root followed by the inverse square root
is the identity. -/
lemma sqrtPos_mul_invSqrtPos {α : WithTop ℝ} {A : L K}
    (hA : IsSelfAdjoint A)
    (hσA : spectrum ℝ A ⊆ positiveOpenRay α) :
    sqrtPos A * invSqrtPos A = (1 : L K) := by
  have hcont_sqrt :
      ContinuousOn (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) (spectrum ℝ A) :=
    continuousOn_rpow_const_of_positiveSpectrum (A := A) (q := (1 : ℝ) / 2) hσA
  have hcont_inv :
      ContinuousOn (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (spectrum ℝ A) :=
    continuousOn_rpow_const_of_positiveSpectrum (A := A) (q := (-1 : ℝ) / 2) hσA
  calc
    sqrtPos A * invSqrtPos A
        = cfcR (ℋ := K)
            (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2) * x ^ ((-1 : ℝ) / 2)) A := by
              dsimp [sqrtPos, invSqrtPos, cfcR]
              rw [← cfc_mul _ _ A hcont_sqrt hcont_inv]
    _ = cfcR (ℋ := K) (fun _ : ℝ ↦ (1 : ℝ)) A := by
          apply cfc_congr
          intro x hx
          have hx0 : 0 < x := (hσA hx).1
          dsimp only
          rw [← Real.rpow_add hx0,
            show ((1 : ℝ) / 2 + (-1) / 2 : ℝ) = 0 from by ring, Real.rpow_zero]
    _ = (1 : L K) := by
          simpa [cfcR] using
            (cfc_const_one (R := ℝ) (A := L K) (p := IsSelfAdjoint) (a := A) (ha := hA))

/-- On positive spectrum, the inverse square root followed by the square root
is the identity. -/
lemma invSqrtPos_mul_sqrtPos {α : WithTop ℝ} {A : L K}
    (hA : IsSelfAdjoint A)
    (hσA : spectrum ℝ A ⊆ positiveOpenRay α) :
    invSqrtPos A * sqrtPos A = (1 : L K) := by
  have hcont_sqrt :
      ContinuousOn (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) (spectrum ℝ A) :=
    continuousOn_rpow_const_of_positiveSpectrum (A := A) (q := (1 : ℝ) / 2) hσA
  have hcont_inv :
      ContinuousOn (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (spectrum ℝ A) :=
    continuousOn_rpow_const_of_positiveSpectrum (A := A) (q := (-1 : ℝ) / 2) hσA
  calc
    invSqrtPos A * sqrtPos A
        = cfcR (ℋ := K)
            (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2)) A := by
              dsimp [sqrtPos, invSqrtPos, cfcR]
              rw [← cfc_mul _ _ A hcont_inv hcont_sqrt]
    _ = cfcR (ℋ := K) (fun _ : ℝ ↦ (1 : ℝ)) A := by
          apply cfc_congr
          intro x hx
          have hx0 : 0 < x := (hσA hx).1
          dsimp only
          rw [← Real.rpow_add hx0,
            show ((-1 : ℝ) / 2 + (1 : ℝ) / 2 : ℝ) = 0 from by ring, Real.rpow_zero]
    _ = (1 : L K) := by
          simpa [cfcR] using
            (cfc_const_one (R := ℝ) (A := L K) (p := IsSelfAdjoint) (a := A) (ha := hA))

/-- On positive spectrum, the square of `sqrtPos A` recovers `A`. -/
lemma sqrtPos_sq {α : WithTop ℝ} {A : L K}
    (hA : IsSelfAdjoint A)
    (hσA : spectrum ℝ A ⊆ positiveOpenRay α) :
    sqrtPos A * sqrtPos A = A := by
  have hcont_sqrt :
      ContinuousOn (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) (spectrum ℝ A) :=
    continuousOn_rpow_const_of_positiveSpectrum (A := A) (q := (1 : ℝ) / 2) hσA
  calc
    sqrtPos A * sqrtPos A
        = cfcR (ℋ := K) (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2)) A := by
            dsimp [sqrtPos, cfcR]
            rw [← cfc_mul _ _ A hcont_sqrt hcont_sqrt]
    _ = cfcR (ℋ := K) (fun x : ℝ ↦ x) A := by
          apply cfc_congr
          intro x hx
          have hx0 : 0 < x := (hσA hx).1
          dsimp only
          rw [← Real.rpow_add hx0,
            show ((1 : ℝ) / 2 + (1 : ℝ) / 2 : ℝ) = 1 from by ring, Real.rpow_one]
    _ = A := by
          simpa [cfcR] using (cfc_id' (R := ℝ) (a := A) (ha := hA))

/-- Conjugating a positive-spectrum operator by its inverse positive square
root gives the identity. -/
lemma invSqrtPos_mul_self_mul_invSqrtPos_eq_one {α : WithTop ℝ} {A : L K}
    (hA : IsSelfAdjoint A)
    (hσA : spectrum ℝ A ⊆ positiveOpenRay α) :
    invSqrtPos A * A * invSqrtPos A = (1 : L K) := by
  calc
    invSqrtPos A * A * invSqrtPos A
        = invSqrtPos A * (sqrtPos A * sqrtPos A) * invSqrtPos A := by
            rw [sqrtPos_sq (K := K) hA hσA]
    _ = (invSqrtPos A * sqrtPos A) * (sqrtPos A * invSqrtPos A) := by
          simp [mul_assoc]
    _ = (1 : L K) := by
          rw [invSqrtPos_mul_sqrtPos (K := K) hA hσA, one_mul,
            sqrtPos_mul_invSqrtPos (K := K) hA hσA]

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
private lemma norm_le_one_of_mul_star_le_one {C : L K}
    (hC : C * star C ≤ (1 : L K)) :
    ‖C‖ ≤ 1 := by
  have hnorm_sq : ‖C * star C‖ ≤ 1 := by
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (mul_star_self_nonneg C)).2 hC
  have hnorm_mul : ‖C * star C‖ = ‖C‖ * ‖C‖ := by
    simpa [norm_star] using (CStarRing.norm_star_mul_self (x := star C))
  rw [hnorm_mul] at hnorm_sq
  nlinarith [norm_nonneg C]

/-- The CFC of `t ↦ f t / t` is the conjugate of `cfcR f A` by the inverse
positive square root of `A`. -/
lemma ratio_cfc_eq_invSqrtPos_mul_cfcR_mul_invSqrtPos
    {α : WithTop ℝ} {f : ℝ → ℝ} {A : L K}
    (hf : ContinuousOn f (halfOpenRay α))
    (hσA : spectrum ℝ A ⊆ positiveOpenRay α) :
    cfcR (ℋ := K) (fun t : ℝ ↦ f t / t) A =
      invSqrtPos A * cfcR (ℋ := K) f A * invSqrtPos A := by
  have hcont_inv :
      ContinuousOn (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (spectrum ℝ A) :=
    continuousOn_rpow_const_of_positiveSpectrum (A := A) (q := (-1 : ℝ) / 2) hσA
  have hcont_f : ContinuousOn f (spectrum ℝ A) :=
    hf.mono (spectrum_subset_halfOpenRay_of_positiveOpenRay (A := A) hσA)
  have hcont_ratio :
      ContinuousOn (fun t : ℝ ↦ f t / t) (spectrum ℝ A) := by
    exact hcont_f.div continuousOn_id (by
      intro x hx
      exact ne_of_gt ((hσA hx).1))
  calc
    cfcR (ℋ := K) (fun t : ℝ ↦ f t / t) A
        = cfcR (ℋ := K)
            (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2) * f x * x ^ ((-1 : ℝ) / 2)) A := by
              apply cfc_congr
              intro x hx
              have hx0 : 0 < x := (hσA hx).1
              have hxne : x ≠ 0 := ne_of_gt hx0
              have hxinv : x ^ (-1 : ℝ) = x⁻¹ := by
                simpa [hxne] using (Real.rpow_neg_one x)
              calc
                f x / x = f x * x ^ (-1 : ℝ) := by
                  rw [div_eq_mul_inv, ← hxinv]
                _ = f x * (x ^ ((-1 : ℝ) / 2) * x ^ ((-1 : ℝ) / 2)) := by
                  congr 1
                  rw [← Real.rpow_add hx0,
                    show ((-1 : ℝ) / 2 + (-1 : ℝ) / 2 : ℝ) = -1 from by ring]
                _ = x ^ ((-1 : ℝ) / 2) * f x * x ^ ((-1 : ℝ) / 2) := by ring
    _ = invSqrtPos A * cfcR (ℋ := K) f A * invSqrtPos A := by
          calc
            cfcR (ℋ := K)
                (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2) * f x * x ^ ((-1 : ℝ) / 2)) A
                =
                  cfcR (ℋ := K) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2) * f x) A *
                    invSqrtPos A := by
                      dsimp [invSqrtPos, cfcR]
                      simpa [mul_assoc] using
                        (cfc_mul (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2) * f x)
                          (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) A
                          (hcont_inv.mul hcont_f) hcont_inv)
            _ = invSqrtPos A * cfcR (ℋ := K) f A * invSqrtPos A := by
                  dsimp [invSqrtPos, cfcR]
                  simpa [mul_assoc] using
                    congrArg (fun T => T * cfc (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) A)
                      (cfc_mul (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) f A hcont_inv hcont_f)

omit [Nontrivial (L K)] in
private lemma self_mul_ratio_cfcR_eq_cfcR
    {α : WithTop ℝ} {f : ℝ → ℝ} {A : L K}
    (hf : ContinuousOn f (halfOpenRay α))
    (hA : IsSelfAdjoint A)
    (hσA : spectrum ℝ A ⊆ positiveOpenRay α) :
    A * cfcR (ℋ := K) (fun t : ℝ ↦ f t / t) A = cfcR (ℋ := K) f A := by
  have hcont_f : ContinuousOn f (spectrum ℝ A) :=
    hf.mono (spectrum_subset_halfOpenRay_of_positiveOpenRay (A := A) hσA)
  have hcont_ratio :
      ContinuousOn (fun t : ℝ ↦ f t / t) (spectrum ℝ A) := by
    exact hcont_f.div continuousOn_id (by
      intro x hx
      exact ne_of_gt ((hσA hx).1))
  have hId : cfcR (ℋ := K) (fun x : ℝ ↦ x) A = A := by
    simpa [cfcR] using (cfc_id' (R := ℝ) (a := A) (ha := hA))
  calc
    A * cfcR (ℋ := K) (fun t : ℝ ↦ f t / t) A
        = cfcR (ℋ := K) (fun x : ℝ ↦ x) A * cfcR (ℋ := K) (fun t : ℝ ↦ f t / t) A := by
            rw [hId]
    _ = cfcR (ℋ := K) (fun x : ℝ ↦ x * (f x / x)) A := by
          rw [← cfc_mul (fun x : ℝ ↦ x) (fun t : ℝ ↦ f t / t) A
            continuousOn_id hcont_ratio]
    _ = cfcR (ℋ := K) f A := by
          apply cfc_congr
          intro x hx
          have hxne : x ≠ 0 := ne_of_gt ((hσA hx).1)
          field_simp [hxne]

omit [Nontrivial (L K)] in
/-- Right multiplication by `A` cancels the CFC of the ratio function,
recovering the CFC of `f` on positive spectrum. -/
lemma ratio_cfcR_mul_self_eq_cfcR
    {α : WithTop ℝ} {f : ℝ → ℝ} {A : L K}
    (hf : ContinuousOn f (halfOpenRay α))
    (hA : IsSelfAdjoint A)
    (hσA : spectrum ℝ A ⊆ positiveOpenRay α) :
    cfcR (ℋ := K) (fun t : ℝ ↦ f t / t) A * A = cfcR (ℋ := K) f A := by
  have hcont_f : ContinuousOn f (spectrum ℝ A) :=
    hf.mono (spectrum_subset_halfOpenRay_of_positiveOpenRay (A := A) hσA)
  have hcont_ratio :
      ContinuousOn (fun t : ℝ ↦ f t / t) (spectrum ℝ A) := by
    exact hcont_f.div continuousOn_id (by
      intro x hx
      exact ne_of_gt ((hσA hx).1))
  have hId : cfcR (ℋ := K) (fun x : ℝ ↦ x) A = A := by
    simpa [cfcR] using (cfc_id' (R := ℝ) (a := A) (ha := hA))
  calc
    cfcR (ℋ := K) (fun t : ℝ ↦ f t / t) A * A
        = cfcR (ℋ := K) (fun t : ℝ ↦ f t / t) A * cfcR (ℋ := K) (fun x : ℝ ↦ x) A := by
            rw [hId]
    _ = cfcR (ℋ := K) (fun x : ℝ ↦ (f x / x) * x) A := by
          rw [← cfc_mul (fun t : ℝ ↦ f t / t) (fun x : ℝ ↦ x) A
            hcont_ratio continuousOn_id]
    _ = cfcR (ℋ := K) f A := by
          apply cfc_congr
          intro x hx
          have hxne : x ≠ 0 := ne_of_gt ((hσA hx).1)
          field_simp [hxne]

/-- Fixed-Hilbert-space form of condition II implying monotonicity of
`t ↦ f t / t` on positive-spectrum operators.  The proof factors
`A ≤ B` through the contraction `B^{-1/2} A^{1/2}`.
Source: Hiai--Yanagi, Theorem 5.1.7. -/
theorem cfcR_div_le_cfcR_div_of_conditionII {α : WithTop ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (halfOpenRay α))
    (hII : ConditionII.{u} α f)
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [ContinuousFunctionalCalculus ℝ (L H) IsSelfAdjoint] [Nontrivial (L H)]
    {A B : L H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hσA : spectrum ℝ A ⊆ positiveOpenRay α)
    (hσB : spectrum ℝ B ⊆ positiveOpenRay α)
    (hAB : A ≤ B) :
    cfcR (ℋ := H) (fun t : ℝ ↦ f t / t) A ≤
      cfcR (ℋ := H) (fun t : ℝ ↦ f t / t) B := by
  let sqrtA : L H := sqrtPos A
  let sqrtB : L H := sqrtPos B
  let invSqrtA : L H := invSqrtPos A
  let invSqrtB : L H := invSqrtPos B
  let C : L H := invSqrtB * sqrtA
  have hsqrtA_sa : IsSelfAdjoint sqrtA := by
    simpa [sqrtA] using sqrtPos_selfAdjoint (K := H) (A := A)
  have hsqrtB_sa : IsSelfAdjoint sqrtB := by
    simpa [sqrtB] using sqrtPos_selfAdjoint (K := H) (A := B)
  have hinvA_sa : IsSelfAdjoint invSqrtA := by
    simpa [invSqrtA] using invSqrtPos_selfAdjoint (K := H) (A := A)
  have hinvB_sa : IsSelfAdjoint invSqrtB := by
    simpa [invSqrtB] using invSqrtPos_selfAdjoint (K := H) (A := B)
  have hsqrtA_sq : sqrtA * sqrtA = A := by
    simpa [sqrtA] using sqrtPos_sq (K := H) hA hσA
  have hsqrtB_sq : sqrtB * sqrtB = B := by
    simpa [sqrtB] using sqrtPos_sq (K := H) hB hσB
  have hinvA_mul_sqrtA : invSqrtA * sqrtA = (1 : L H) := by
    simpa [sqrtA, invSqrtA] using invSqrtPos_mul_sqrtPos (K := H) hA hσA
  have hsqrtA_mul_invA : sqrtA * invSqrtA = (1 : L H) := by
    simpa [sqrtA, invSqrtA] using sqrtPos_mul_invSqrtPos (K := H) hA hσA
  have hinvB_mul_sqrtB : invSqrtB * sqrtB = (1 : L H) := by
    simpa [sqrtB, invSqrtB] using invSqrtPos_mul_sqrtPos (K := H) hB hσB
  have hsqrtB_mul_invB : sqrtB * invSqrtB = (1 : L H) := by
    simpa [sqrtB, invSqrtB] using sqrtPos_mul_invSqrtPos (K := H) hB hσB
  have hCstarBC : star C * B * C = A := by
    dsimp [C]
    rw [show star (invSqrtB * sqrtA) = sqrtA * invSqrtB by
      simp [hinvB_sa.star_eq, hsqrtA_sa.star_eq]]
    calc
      sqrtA * invSqrtB * B * (invSqrtB * sqrtA)
          = sqrtA * (invSqrtB * B * invSqrtB) * sqrtA := by
              simp [mul_assoc]
      _ = sqrtA * (1 : L H) * sqrtA := by
            rw [← hsqrtB_sq]
            simp [mul_assoc, hinvB_mul_sqrtB, hsqrtB_mul_invB]
      _ = A := by simpa [mul_assoc] using hsqrtA_sq
  have hCCstar : C * star C ≤ (1 : L H) := by
    have hconj : star invSqrtB * A * invSqrtB ≤ star invSqrtB * B * invSqrtB := by
      exact star_left_conjugate_le_conjugate hAB invSqrtB
    have hrhs : star invSqrtB * B * invSqrtB = (1 : L H) := by
      rw [hinvB_sa.star_eq, ← hsqrtB_sq]
      simp [mul_assoc, hinvB_mul_sqrtB, hsqrtB_mul_invB]
    have hlhs : star invSqrtB * A * invSqrtB = C * star C := by
      rw [hinvB_sa.star_eq]
      dsimp [C]
      rw [show star (invSqrtB * sqrtA) = sqrtA * invSqrtB by
        simp [hinvB_sa.star_eq, hsqrtA_sa.star_eq]]
      rw [← hsqrtA_sq]
      simp [mul_assoc]
    calc
      C * star C = star invSqrtB * A * invSqrtB := by simp [hlhs]
      _ ≤ star invSqrtB * B * invSqrtB := hconj
      _ = (1 : L H) := hrhs
  have hCnorm : ‖C‖ ≤ 1 := norm_le_one_of_mul_star_le_one (K := H) hCCstar
  have hmain := hII (K := H) (A := B) (C := C) hB
    (spectrum_subset_halfOpenRay_of_positiveOpenRay (A := B) hσB) hCnorm
  have hconj :
      invSqrtA * cfcR (ℋ := H) f A * invSqrtA ≤
        invSqrtA * (star C * cfcR (ℋ := H) f B * C) * invSqrtA := by
    have hbase : cfcR (ℋ := H) f A ≤ star C * cfcR (ℋ := H) f B * C := by
      simpa [hCstarBC] using hmain
    simpa [hinvA_sa.star_eq, mul_assoc] using star_left_conjugate_le_conjugate hbase invSqrtA
  have hright :
      invSqrtA * (star C * cfcR (ℋ := H) f B * C) * invSqrtA =
        invSqrtB * cfcR (ℋ := H) f B * invSqrtB := by
    dsimp [C]
    rw [show star (invSqrtB * sqrtA) = sqrtA * invSqrtB by
      simp [hinvB_sa.star_eq, hsqrtA_sa.star_eq]]
    calc
      invSqrtA * ((sqrtA * invSqrtB) * cfcR (ℋ := H) f B * (invSqrtB * sqrtA)) * invSqrtA
          = ((invSqrtA * sqrtA) * invSqrtB) * cfcR (ℋ := H) f B *
              (invSqrtB * (sqrtA * invSqrtA)) := by
                simp_rw [mul_assoc]
      _ = ((1 : L H) * invSqrtB) * cfcR (ℋ := H) f B * (invSqrtB * (1 : L H)) := by
            rw [hinvA_mul_sqrtA, hsqrtA_mul_invA]
      _ = invSqrtB * cfcR (ℋ := H) f B * invSqrtB := by
            simp [mul_assoc]
  have hratioA := ratio_cfc_eq_invSqrtPos_mul_cfcR_mul_invSqrtPos
    (K := H) hf hσA
  have hratioB := ratio_cfc_eq_invSqrtPos_mul_cfcR_mul_invSqrtPos
    (K := H) hf hσB
  rw [← hratioA, hright, ← hratioB] at hconj
  exact hconj

/-- Condition II implies condition V, the ratio-monotonicity part of the
compression inequality characterization.
Source: Hiai--Yanagi, Theorem 5.1.7. -/
theorem conditionII_implies_conditionV {α : WithTop ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (halfOpenRay α))
    (hII : ConditionII.{u} α f) :
    ConditionV.{u} α f := by
  intro H _ _ _ _ _ A B hA hB hσA hσB hAB
  exact cfcR_div_le_cfcR_div_of_conditionII (H := H) hf hII hA hB hσA hσB hAB

end ConditionIItoV

end ConvexityCharacterization

end NormalCFC517

end HansenPedersen
