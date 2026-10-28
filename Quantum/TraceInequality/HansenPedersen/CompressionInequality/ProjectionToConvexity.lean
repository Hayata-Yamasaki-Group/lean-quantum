/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.CompressionInequality.RotatedBlockCompression

/-!
# Projection compression implies operator convexity

This module proves the final return implication in the compression
characterization: the projection compression inequality forces operator
convexity on the positive half-open ray and supplies the endpoint condition
`f 0 ≤ 0`.  The proof uses a two-by-two rotation, compresses the rotated
diagonal block, and reads off the first diagonal entry.

## Main results

* `conditionIV_implies_f0_nonpos_fixed`: the projection inequality at the zero
  projection gives `f 0 ≤ 0`.
* `conditionIV_implies_convex_fixed`: condition IV gives operator convexity on
  each Hilbert space.
* `conditionIV_implies_conditionI`: condition IV implies condition I.

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

section ProjectionToConvexity

open scoped ComplexOrder

private abbrev ScalarHilbert : Type u := ULift.{u} (EuclideanSpace ℂ (Fin 1))

private noncomputable instance : InnerProductSpace ℂ ScalarHilbert where
  inner x y := inner ℂ x.down y.down
  norm_sq_eq_re_inner x := by
    simpa using (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (x := x.down))
  conj_inner_symm x y := by
    simp
  add_left x y z := by
    simp
  smul_left x y r := by
    change inner ℂ (r • x.down) y.down = (starRingEnd ℂ) r * inner ℂ x.down y.down
    rw [InnerProductSpace.smul_left]

private lemma diagProjection_selfAdjoint {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    IsSelfAdjoint
      (HansenPedersen.Internal.diagMapCLM (K := H) (L' := H) (1 : L H) 0) := by
  exact HansenPedersen.Internal.isSelfAdjoint_diagMapCLM
    (IsSelfAdjoint.one _) (IsSelfAdjoint.zero _)

private lemma diagProjection_idempotent {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    HansenPedersen.Internal.diagMapCLM (K := H) (L' := H) (1 : L H) 0 *
        HansenPedersen.Internal.diagMapCLM (K := H) (L' := H) (1 : L H) 0 =
      HansenPedersen.Internal.diagMapCLM (K := H) (L' := H) (1 : L H) 0 := by
  ext x
  apply WithLp.ofLp_injective
  ext <;> simp [HansenPedersen.Internal.diagMapCLM_apply]

private lemma convexCombination_isSelfAdjoint {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A B : L H} {t : ℝ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint ((1 - t) • A + t • B) := by
  change star (((1 - t) : ℝ) • A + (t : ℝ) • B) = (((1 - t) : ℝ) • A + (t : ℝ) • B)
  simp [hA.star_eq, hB.star_eq, sub_eq_add_neg, add_comm]

private lemma convexCombination_cfc_isSelfAdjoint {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [ContinuousFunctionalCalculus ℝ (L H) IsSelfAdjoint] [Nontrivial (L H)]
    {f : ℝ → ℝ} {A B : L H} {t : ℝ} :
    IsSelfAdjoint ((1 - t) • cfcR (ℋ := H) f A + t • cfcR (ℋ := H) f B) := by
  have hcfA : star (cfcR (ℋ := H) f A) = cfcR (ℋ := H) f A :=
    (HansenPedersen.isSelfAdjoint_cfcR (K := H) (f := f) (A := A)).star_eq
  have hcfB : star (cfcR (ℋ := H) f B) = cfcR (ℋ := H) f B :=
    (HansenPedersen.isSelfAdjoint_cfcR (K := H) (f := f) (A := B)).star_eq
  change
    star (((1 - t) : ℝ) • cfcR (ℋ := H) f A + (t : ℝ) • cfcR (ℋ := H) f B) =
      (((1 - t) : ℝ) • cfcR (ℋ := H) f A + (t : ℝ) • cfcR (ℋ := H) f B)
  simp [hcfA, hcfB, sub_eq_add_neg, add_comm]

/-- Applying condition IV to the zero operator and zero projection forces the
scalar endpoint inequality `f 0 ≤ 0` on a nontrivial Hilbert space. -/
lemma conditionIV_implies_f0_nonpos_fixed {α : WithTop ℝ} {f : ℝ → ℝ}
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] [Nontrivial K]
    (hα : (0 : WithTop ℝ) < α)
    (hIV : ConditionIV.{u} α f) :
    f 0 ≤ 0 := by
  have hIVK :
      ∀ {A P : L K},
        IsSelfAdjoint A →
        IsSelfAdjoint P →
        P * P = P →
        spectrum ℝ A ⊆ halfOpenRay α →
        cfcR (ℋ := K) f (P * A * P) ≤ P * cfcR (ℋ := K) f A * P := by
    intro A P hA hP hPP hσA
    exact hIV (K := K) (A := A) (P := P) hA hP hPP hσA
  have h0 := hIVK (A := (0 : L K)) (P := (0 : L K))
    (IsSelfAdjoint.zero _) (IsSelfAdjoint.zero _) (by
      simp : (0 : L K) * (0 : L K) = 0)
    (HansenPedersen.ConvexityCharacterization.spectrum_zero_subset_halfOpenRay (K := K) hα)
  have hcf0_nonpos : cfcR (ℋ := K) f (0 : L K) ≤ 0 := by
    simpa using h0
  have hpos : (((-(f 0 : ℂ)) • (1 : L K))).IsPositive := by
    simpa [ContinuousLinearMap.le_def, cfcR, cfc_zero,
      Algebra.algebraMap_eq_smul_one, sub_eq_add_neg] using hcf0_nonpos
  have hcoeff_nonneg : (0 : ℂ) ≤ -(f 0 : ℂ) := by
    open scoped ComplexOrder in
      rw [← LinearMap.isPositive_one.isPositive_smul_iff (E := K)
        (one_ne_zero' (K →ₗ[ℂ] K))]
    open scoped ComplexOrder in
      simpa using hpos.toLinearMap
  have hreal_nonneg : (0 : ℝ) ≤ -f 0 := by
    exact_mod_cast hcoeff_nonneg
  linarith

private lemma conditionIV_implies_convex_fixed_point {α : WithTop ℝ} {f : ℝ → ℝ}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [ContinuousFunctionalCalculus ℝ (L H) IsSelfAdjoint] [Nontrivial (L H)]
    (hf : ContinuousOn f (halfOpenRay α))
    (hα : (0 : WithTop ℝ) < α)
    (hIV : ConditionIV.{u} α f)
    {A B : L H} {t : ℝ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hσA : spectrum ℝ A ⊆ halfOpenRay α)
    (hσB : spectrum ℝ B ⊆ halfOpenRay α) :
    cfcR (ℋ := H) f ((1 - t) • A + t • B) ≤
      (1 - t) • cfcR (ℋ := H) f A + t • cfcR (ℋ := H) f B := by
  haveI : Nontrivial H := HansenPedersen.nontrivial_of_nontrivial_L
  haveI : Nontrivial (WithLp 2 (H × H)) := inferInstance
  have hs_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  let s : ℂ := Real.sqrt (1 - t)
  let r : ℂ := Real.sqrt t
  let X : L (WithLp 2 (H × H)) := HansenPedersen.Internal.diagMapCLM A B
  let P : L (WithLp 2 (H × H)) := HansenPedersen.Internal.diagMapCLM (1 : L H) 0
  let U0 : L (WithLp 2 (H × H)) :=
    blockCLM ((s : ℂ) • (1 : L H)) (-((r : ℂ) • (1 : L H)))
      ((r : ℂ) • (1 : L H)) ((s : ℂ) • (1 : L H))
  have hU0_mem : U0 ∈ unitary (L (WithLp 2 (H × H))) :=
    rotated_block_mem_unitary (K := H) ht0 ht1
  let U : unitary (L (WithLp 2 (H × H))) := ⟨U0, hU0_mem⟩
  let Y : L (WithLp 2 (H × H)) :=
    star (↑U : L (WithLp 2 (H × H))) * X * (↑U : L (WithLp 2 (H × H)))
  let M : L H := (1 - t) • A + t • B
  let N : L H := (1 - t) • cfcR (ℋ := H) f A + t • cfcR (ℋ := H) f B
  have hXself : IsSelfAdjoint X := HansenPedersen.Internal.isSelfAdjoint_diagMapCLM hA hB
  have hσX : spectrum ℝ X ⊆ halfOpenRay α :=
    HansenPedersen.ConvexityCharacterization.spectrum_diagMapCLM_subset_halfOpenRay
      (K := H) hA hB hσA hσB
  have hYself : IsSelfAdjoint Y := by
    exact hXself.conjugate' _
  have hσY : spectrum ℝ Y ⊆ halfOpenRay α := by
    rw [Unitary.spectrum_star_left_conjugate (R := ℝ) (a := X) (U := U)]
    exact hσX
  have hPself : IsSelfAdjoint P := by
    exact diagProjection_selfAdjoint (H := H)
  have hPidem : P * P = P := by
    exact diagProjection_idempotent (H := H)
  have hmain := hIV (WithLp 2 (H × H)) hYself hPself hPidem hσY
  have hPM : P * Y * P = HansenPedersen.Internal.diagMapCLM M 0 := by
    exact compress_rotated_diag (K := H) (S := A) (T := B) ht0 ht1
  have hσM : spectrum ℝ M ⊆ halfOpenRay α := by
    simpa [M] using
      HansenPedersen.ConvexityCharacterization.convex_combination_spectrum_subset_halfOpenRay
        (K := H) hα hA hB ht0 ht1 hσA hσB
  have hMself : IsSelfAdjoint M := by
    simpa [M] using convexCombination_isSelfAdjoint (H := H) (t := t) hA hB
  have hcfPM :
      cfcR (ℋ := WithLp 2 (H × H)) f (P * Y * P) =
        HansenPedersen.Internal.diagMapCLM (cfcR (ℋ := H) f M) (cfcR (ℋ := H) f 0) := by
    rw [hPM]
    simpa using cfcR_diagMapCLM (K := H) hf
      hMself (IsSelfAdjoint.zero _) hσM
        (HansenPedersen.ConvexityCharacterization.spectrum_zero_subset_halfOpenRay (K := H) hα)
  have hcfX :
      cfcR (ℋ := WithLp 2 (H × H)) f X =
        HansenPedersen.Internal.diagMapCLM (cfcR (ℋ := H) f A) (cfcR (ℋ := H) f B) := by
    dsimp [X]
    simpa using cfcR_diagMapCLM (K := H) hf hA hB hσA hσB
  have hright :
      P * cfcR (ℋ := WithLp 2 (H × H)) f Y * P =
        HansenPedersen.Internal.diagMapCLM N 0 := by
    have hconj :
        cfcR (ℋ := WithLp 2 (H × H)) f Y =
          star (↑U : L (WithLp 2 (H × H))) *
            cfcR (ℋ := WithLp 2 (H × H)) f X * (↑U : L (WithLp 2 (H × H))) := by
      exact cfcR_unitary_conj (K := WithLp 2 (H × H)) hf hXself hσX U
    rw [hconj, hcfX]
    exact compress_rotated_diag (K := H) (S := cfcR (ℋ := H) f A)
      (T := cfcR (ℋ := H) f B) ht0 ht1
  have hcfMself : IsSelfAdjoint (cfcR (ℋ := H) f M) := by
    exact HansenPedersen.isSelfAdjoint_cfcR (K := H) (f := f) (A := M)
  have hNself : IsSelfAdjoint N := by
    simpa [N] using convexCombination_cfc_isSelfAdjoint (H := H) (f := f) (t := t)
  have hdiag :
      HansenPedersen.Internal.diagMapCLM (cfcR (ℋ := H) f M) (cfcR (ℋ := H) f 0) ≤
        HansenPedersen.Internal.diagMapCLM N 0 := by
    simpa [hcfPM, hright] using hmain
  exact HansenPedersen.ConvexityCharacterization.diagMapCLM_fst_le_of_le hcfMself hNself hdiag

/-- Fixed-Hilbert-space form of the implication from projection compression to
operator convexity on `halfOpenRay α`.  The proof realizes a convex combination
as the upper-left compression of a unitary rotation of `diag(A, B)`.
Source: Hiai--Yanagi, Theorem 5.1.7. -/
theorem conditionIV_implies_convex_fixed {α : WithTop ℝ} {f : ℝ → ℝ}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [ContinuousFunctionalCalculus ℝ (L H) IsSelfAdjoint] [Nontrivial (L H)]
    (hf : ContinuousOn f (halfOpenRay α))
    (hα : (0 : WithTop ℝ) < α)
    (hIV : ConditionIV.{u} α f) :
    HOperatorConvexOnInterval H (halfOpenRay α) f := by
  intro A B t hA hB ht0 ht1 hσA hσB
  exact conditionIV_implies_convex_fixed_point hf hα hIV hA hB ht0 ht1 hσA hσB

/-- Condition IV implies condition I: it yields operator convexity on every
Hilbert space and the scalar endpoint inequality `f 0 ≤ 0`.
Source: Hiai--Yanagi, Theorem 5.1.7. -/
theorem conditionIV_implies_conditionI {α : WithTop ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (halfOpenRay α))
    (hα : (0 : WithTop ℝ) < α)
    (hIV : ConditionIV.{u} α f) :
    ConditionI.{u} α f := by
  constructor
  · intro H _ _ _ _ _
    exact conditionIV_implies_convex_fixed (H := H) hf hα hIV
  · exact conditionIV_implies_f0_nonpos_fixed (K := ScalarHilbert) hα hIV

end ProjectionToConvexity

end ConvexityCharacterization

end NormalCFC517

end HansenPedersen
