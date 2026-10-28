/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.CompressionInequality.BlockMatrix

/-!
# Spectral bounds for compression inequalities

This file collects the spectral-domain lemmas used in the proof of
Hiai–Yanagi Theorem 5.1.7.  The key point is that contractions, contractive
rows, block diagonal maps, and scalar convex combinations preserve membership
in the half-open interval where the real CFC of `f` is allowed.

## Main results

* `spectrum_diagMapCLM_subset_halfOpenRay`: block diagonal maps inherit the
  half-open spectral bound from their components.
* `compressed_sum_spectrum_subset_halfOpenRay`: the spectrum of a two-variable
  contractive-row compression remains in the same interval.
* `convex_combination_spectrum_subset_halfOpenRay`: convex combinations of
  two self-adjoint operators stay in the interval.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1, Theorem 5.1.7.
-/

namespace HansenPedersen

universe u

open CFC MeasureTheory
open scoped Topology
open Filter

section NormalCFC517

namespace ConvexityCharacterization

section SpectralBounds

variable {K : Type u}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] in
/-- The real spectrum of the zero operator lies in `halfOpenRay α` whenever
`α` is strictly positive. -/
lemma spectrum_zero_subset_halfOpenRay {α : WithTop ℝ}
    (hα : (0 : WithTop ℝ) < α) :
    spectrum ℝ (0 : L K) ⊆ halfOpenRay α := by
  intro x hx
  have hx0 : x = 0 := by
    simpa [spectrum.zero_eq] using hx
  subst hx0
  exact ⟨le_rfl, hα⟩

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
/-- A block diagonal operator has real spectrum in `halfOpenRay α` when both
diagonal entries do.  This is the interval-control lemma for `diagMapCLM`. -/
lemma spectrum_diagMapCLM_subset_halfOpenRay {α : WithTop ℝ} {a b : L K}
    (_ha : IsSelfAdjoint a) (_hb : IsSelfAdjoint b)
    (hσa : spectrum ℝ a ⊆ halfOpenRay α)
    (hσb : spectrum ℝ b ⊆ halfOpenRay α) :
    spectrum ℝ (HansenPedersen.Internal.diagMapCLM a b) ⊆ halfOpenRay α := by
  let Φ := HansenPedersen.Internal.diagStarAlgHom (K := K) (L' := K)
  intro x hx
  have hx' : x ∈ spectrum ℝ (a, b) := by
    exact AlgHom.spectrum_apply_subset
      (((Φ : (L K × L K) →⋆ₐ[ℂ] L (WithLp 2 (K × K))).restrictScalars ℝ)) (a, b) hx
  rw [Prod.spectrum_eq] at hx'
  rcases hx' with hxa | hxb
  · exact hσa hxa
  · exact hσb hxb

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
/-- Order comparison of block diagonal operators implies the corresponding
order comparison of their first diagonal entries. -/
lemma diagMapCLM_fst_le_of_le {a b c d : L K}
    (ha : IsSelfAdjoint a) (hc : IsSelfAdjoint c)
    (h : HansenPedersen.Internal.diagMapCLM a b ≤ HansenPedersen.Internal.diagMapCLM c d) :
    a ≤ c := by
  rw [ContinuousLinearMap.le_def] at h ⊢
  rw [ContinuousLinearMap.isPositive_iff']
  constructor
  · exact hc.sub ha
  · intro x
    have hx := h.inner_nonneg_left (WithLp.toLp 2 (x, 0))
    simpa [HansenPedersen.Internal.diagMapCLM_sub,
      HansenPedersen.Internal.diagMapCLM_apply, WithLp.prod_inner_apply] using hx

/-- Spectral stability for the two-variable compression in Theorem 5.1.7.  If
`A` and `B` have spectrum in `halfOpenRay α` and the row `(C, D)` is
contractive, then `C* A C + D* B D` has spectrum in the same interval. -/
lemma compressed_sum_spectrum_subset_halfOpenRay {α : WithTop ℝ}
    {A B C D : L K} (hα : (0 : WithTop ℝ) < α)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hσA : spectrum ℝ A ⊆ halfOpenRay α)
    (hσB : spectrum ℝ B ⊆ halfOpenRay α)
    (hCD : star C * C + star D * D ≤ (1 : L K)) :
    spectrum ℝ (star C * A * C + star D * B * D) ⊆ halfOpenRay α := by
  have hA0 : 0 ≤ A := by
    exact HansenPedersen.nonneg_of_isSelfAdjoint_of_spectrum_subset_Ici hA (by
      intro x hx
      exact (hσA hx).1)
  have hB0 : 0 ≤ B := by
    exact HansenPedersen.nonneg_of_isSelfAdjoint_of_spectrum_subset_Ici hB (by
      intro x hx
      exact (hσB hx).1)
  have hA_norm_mem : ‖A‖ ∈ spectrum ℝ A := CStarAlgebra.norm_mem_spectrum_of_nonneg hA0
  have hB_norm_mem : ‖B‖ ∈ spectrum ℝ B := CStarAlgebra.norm_mem_spectrum_of_nonneg hB0
  have hA_norm_lt : ((‖A‖ : ℝ) : WithTop ℝ) < α := (hσA hA_norm_mem).2
  have hB_norm_lt : ((‖B‖ : ℝ) : WithTop ℝ) < α := (hσB hB_norm_mem).2
  have hA_le : A ≤ (‖A‖ : ℝ) • (1 : L K) := by
    simpa [Algebra.algebraMap_eq_smul_one] using hA.le_algebraMap_norm_self
  have hB_le : B ≤ (‖B‖ : ℝ) • (1 : L K) := by
    simpa [Algebra.algebraMap_eq_smul_one] using hB.le_algebraMap_norm_self
  let β : ℝ := max ‖A‖ ‖B‖
  have hAβ : ‖A‖ ≤ β := le_max_left _ _
  have hBβ : ‖B‖ ≤ β := le_max_right _ _
  have hβ_lt : ((β : ℝ) : WithTop ℝ) < α := by
    by_cases htop : α = ⊤
    · simp [htop]
    · rcases WithTop.ne_top_iff_exists.mp htop with ⟨a, rfl⟩
      exact WithTop.coe_lt_coe.mpr (max_lt_iff.mpr
        ⟨WithTop.coe_lt_coe.mp hA_norm_lt, WithTop.coe_lt_coe.mp hB_norm_lt⟩)
  have hM0 : (0 : L K) ≤ star C * A * C + star D * B * D := by
    exact add_nonneg (star_left_conjugate_nonneg hA0 C) (star_left_conjugate_nonneg hB0 D)
  have hMself : IsSelfAdjoint (star C * A * C + star D * B * D) := IsSelfAdjoint.of_nonneg hM0
  have hCA : star C * A * C ≤ (‖A‖ : ℝ) • (star C * C) := by
    simpa [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_assoc] using
      star_left_conjugate_le_conjugate hA_le C
  have hDB : star D * B * D ≤ (‖B‖ : ℝ) • (star D * D) := by
    simpa [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_assoc] using
      star_left_conjugate_le_conjugate hB_le D
  have hAβ' : (‖A‖ : ℝ) • (star C * C) ≤ (β : ℝ) • (star C * C) := by
    exact smul_le_smul_of_nonneg_right hAβ (star_mul_self_nonneg C)
  have hBβ' : (‖B‖ : ℝ) • (star D * D) ≤ (β : ℝ) • (star D * D) := by
    exact smul_le_smul_of_nonneg_right hBβ (star_mul_self_nonneg D)
  have hMβ_aux :
      star C * A * C + star D * B * D ≤ (β : ℝ) • (star C * C + star D * D) := by
    calc
      star C * A * C + star D * B * D ≤
          (‖A‖ : ℝ) • (star C * C) + (‖B‖ : ℝ) • (star D * D) := by
        exact add_le_add hCA hDB
      _ ≤ (β : ℝ) • (star C * C) + (β : ℝ) • (star D * D) := add_le_add hAβ' hBβ'
      _ = (β : ℝ) • (star C * C + star D * D) := by simp [smul_add]
  have hMβ : star C * A * C + star D * B * D ≤ (β : ℝ) • (1 : L K) := by
    calc
      star C * A * C + star D * B * D ≤ (β : ℝ) • (star C * C + star D * D) := hMβ_aux
      _ ≤ (β : ℝ) • (1 : L K) := by
          exact smul_le_smul_of_nonneg_left hCD (le_trans (norm_nonneg _) (le_max_left _ _))
  intro x hx
  have hxIcc := HansenPedersen.spectrum_subset_Icc_of_order_bounds_clm
    (α := 0) (β := β) hMself
    (by simpa [Algebra.algebraMap_eq_smul_one] using hM0)
    (by simpa [Algebra.algebraMap_eq_smul_one] using hMβ) hx
  refine ⟨?_, ?_⟩
  · exact hxIcc.1
  · exact lt_of_le_of_lt (by exact_mod_cast hxIcc.2) hβ_lt

/-- Spectral stability for scalar convex combinations.  It is obtained by
viewing `(1 - t) • A + t • B` as a two-variable compression with scalar
contractions `sqrt (1 - t)` and `sqrt t`. -/
lemma convex_combination_spectrum_subset_halfOpenRay {α : WithTop ℝ}
    {A B : L K} {t : ℝ}
    (hα : (0 : WithTop ℝ) < α)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hσA : spectrum ℝ A ⊆ halfOpenRay α)
    (hσB : spectrum ℝ B ⊆ halfOpenRay α) :
    spectrum ℝ ((1 - t) • A + t • B) ⊆ halfOpenRay α := by
  have hs_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  let C0 : L K := (Real.sqrt (1 - t) : ℂ) • (1 : L K)
  let D0 : L K := (Real.sqrt t : ℂ) • (1 : L K)
  have hsqtR : Real.sqrt t * Real.sqrt t = t := by
    simpa [pow_two] using Real.sq_sqrt ht0
  have hsqsR : Real.sqrt (1 - t) * Real.sqrt (1 - t) = 1 - t := by
    simpa [pow_two] using Real.sq_sqrt hs_nonneg
  have hCD :
      star C0 * C0 + star D0 * D0 ≤ (1 : L K) := by
    have hCD_eq :
        star C0 * C0 + star D0 * D0 = (1 : L K) := by
      ext x
      have hsumR :
          Real.sqrt (1 - t) * Real.sqrt (1 - t) + Real.sqrt t * Real.sqrt t = (1 : ℝ) := by
        nlinarith [Real.sq_sqrt ht0, Real.sq_sqrt hs_nonneg]
      simpa [C0, D0, smul_smul, add_smul] using congrArg (fun z : ℝ => z • x) hsumR
    rw [hCD_eq]
  have hM_eq :
      star C0 * A * C0 + star D0 * B * D0 = (1 - t) • A + t • B := by
    ext x
    have hsqtC : ((Real.sqrt t : ℂ) * (Real.sqrt t : ℂ)) = (t : ℂ) := by
      exact_mod_cast hsqtR
    have hsqsC : ((Real.sqrt (1 - t) : ℂ) * (Real.sqrt (1 - t) : ℂ)) =
        ((1 - t : ℝ) : ℂ) := by
      exact_mod_cast hsqsR
    have hsqtStar : star (Real.sqrt t : ℂ) = (Real.sqrt t : ℂ) := by
      exact Complex.conj_ofReal _
    have hsqsStar : star (Real.sqrt (1 - t) : ℂ) = (Real.sqrt (1 - t) : ℂ) := by
      exact Complex.conj_ofReal _
    have hCterm : (star C0) (A (C0 x)) = ((1 - t) • A) x := by
      simp only [C0, star_smul, star_one]
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
      rw [A.map_smul, smul_smul, hsqsStar, hsqsC]
      rfl
    have hDterm : (star D0) (B (D0 x)) = (t • B) x := by
      simp only [D0, star_smul, star_one]
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
      rw [B.map_smul, smul_smul, hsqtStar, hsqtC]
      rfl
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_mul', Function.comp_apply]
    rw [hCterm, hDterm]
  rw [← hM_eq]
  exact compressed_sum_spectrum_subset_halfOpenRay (K := K) hα hA hB hσA hσB hCD

end SpectralBounds

end ConvexityCharacterization

end NormalCFC517

end HansenPedersen
