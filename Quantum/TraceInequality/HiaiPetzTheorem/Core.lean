/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.BasicTheorems
import Quantum.TraceInequality.HiaiPetz.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheorem
import Quantum.TraceInequality.HiaiPetz.OperatorCore
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Core lemmas for the Hansen–Pedersen development

Shared entry-level lemmas for the Hiai–Yanagi Chapter 5.1 formalization:
adapters between the foundational `LownerHeinzTheorem.OperatorMonotoneOn`
and the book-faithful `OperatorMonotoneOnInterval`, together with the
Löwner–Heinz power monotonicity `opRpow_le_opRpow` and spectrum-based
order bounds used throughout the chapter.

## Main results

* `opRpow_le_opRpow`: `0 ≤ A ≤ B` implies `A ^ p ≤ B ^ p` for `p ∈ [0, 1]`
  (Löwner–Heinz).
* `operatorMonotoneOnInterval_of_operatorMonotoneOn_Ici` /
  `..._Ioi`: hypothesis-order adapters from the foundational predicate.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1.
-/

namespace HansenPedersen

universe u

open CFC MeasureTheory
open scoped Topology CStarAlgebra
open Filter

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

/-- For a self-adjoint continuous linear endomorphism `T` of `K` whose real
spectrum is contained in `Set.Icc α β`, the scalar order bounds
`α • 1 ≤ T ≤ β • 1` hold. -/
theorem order_bounds_of_spectrum_subset_Icc_clm
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    {T : K →L[ℂ] K} {α β : ℝ} (hT : IsSelfAdjoint T)
    (hσ : spectrum ℝ T ⊆ Set.Icc α β) :
    (α : ℂ) • (1 : K →L[ℂ] K) ≤ T ∧ T ≤ (β : ℂ) • (1 : K →L[ℂ] K) := by
  constructor
  · exact (algebraMap_le_iff_le_spectrum (R := ℝ) (A := K →L[ℂ] K) (p := IsSelfAdjoint)
      (r := α) (a := T) (ha := hT)).2 (by intro x hx; exact (hσ hx).1)
  · exact (le_algebraMap_iff_spectrum_le (R := ℝ) (A := K →L[ℂ] K) (p := IsSelfAdjoint)
      (r := β) (a := T) (ha := hT)).2 (by intro x hx; exact (hσ hx).2)

/-- Converse of `order_bounds_of_spectrum_subset_Icc_clm`: for a self-adjoint
endomorphism `T` of `K`, the scalar order bounds `α • 1 ≤ T` and
`T ≤ β • 1` imply that the real spectrum of `T` is contained in
`Set.Icc α β`. -/
theorem spectrum_subset_Icc_of_order_bounds_clm
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)]
    {T : K →L[ℂ] K} {α β : ℝ} (hT : IsSelfAdjoint T)
    (hlow : (α : ℂ) • (1 : K →L[ℂ] K) ≤ T)
    (hupp : T ≤ (β : ℂ) • (1 : K →L[ℂ] K)) :
    spectrum ℝ T ⊆ Set.Icc α β := by
  intro x hx
  constructor
  · exact (algebraMap_le_iff_le_spectrum (R := ℝ) (A := K →L[ℂ] K) (p := IsSelfAdjoint)
      (r := α) (a := T) (ha := hT)).1 hlow x hx
  · exact (le_algebraMap_iff_spectrum_le (R := ℝ) (A := K →L[ℂ] K) (p := IsSelfAdjoint)
      (r := β) (a := T) (ha := hT)).1 hupp x hx

namespace Internal

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L' : Type*} [NormedAddCommGroup L'] [InnerProductSpace ℂ L'] [CompleteSpace L']

/-- For a self-adjoint endomorphism `T`, the real functional calculus of `f`
agrees with the complex (normal) functional calculus of `z ↦ f z.re`. -/
theorem realCfc_eq_normalCfc_of_selfAdjoint
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℂ (K →L[ℂ] K) IsStarNormal]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    {f : ℝ → ℝ} {T : K →L[ℂ] K} (hT : IsSelfAdjoint T) :
    cfc (R := ℝ) f T = cfc (R := ℂ) (fun z : ℂ => (f z.re : ℂ)) T := by
  simpa using cfc_real_eq_complex (A := K →L[ℂ] K) (f := f) (a := T) hT

omit [CompleteSpace K] [CompleteSpace L'] in
/-- The block-diagonal map is additive in its blocks: the difference of two
block-diagonal maps is the block-diagonal map of the blockwise differences. -/
lemma diagMapCLM_sub (a₁ a₂ : K →L[ℂ] K) (b₁ b₂ : L' →L[ℂ] L') :
    diagMapCLM a₁ b₁ - diagMapCLM a₂ b₂ = diagMapCLM (a₁ - a₂) (b₁ - b₂) := by
  ext x
  apply WithLp.ofLp_injective
  ext <;> simp [diagMapCLM_apply]

open scoped ComplexOrder in
/-- Monotonicity of the block-diagonal map: blockwise order bounds `a₁ ≤ a₂` and
`b₁ ≤ b₂` imply `diagMapCLM a₁ b₁ ≤ diagMapCLM a₂ b₂`. -/
theorem diagMapCLM_mono
    {a₁ a₂ : K →L[ℂ] K} {b₁ b₂ : L' →L[ℂ] L'}
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    diagMapCLM a₁ b₁ ≤ diagMapCLM a₂ b₂ := by
  rw [ContinuousLinearMap.le_def, diagMapCLM_sub, ContinuousLinearMap.isPositive_iff']
  constructor
  · exact isSelfAdjoint_diagMapCLM
      (ContinuousLinearMap.IsPositive.isSelfAdjoint ((ContinuousLinearMap.le_def _ _).mp ha))
      (ContinuousLinearMap.IsPositive.isSelfAdjoint ((ContinuousLinearMap.le_def _ _).mp hb))
  · intro x
    have hapos : (a₂ - a₁).IsPositive := (ContinuousLinearMap.le_def _ _).mp ha
    have hbpos : (b₂ - b₁).IsPositive := (ContinuousLinearMap.le_def _ _).mp hb
    rw [diagMapCLM_apply, WithLp.prod_inner_apply]
    exact add_nonneg (hapos.inner_nonneg_left x.fst) (hbpos.inner_nonneg_left x.snd)

attribute [gcongr] diagMapCLM_mono

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- For a self-adjoint `T : L ℋ` whose real spectrum is contained in
`Set.Icc α β`, the complex spectrum is contained in the image
`Complex.ofReal '' Set.Icc α β`. -/
theorem complex_spectrum_subset_of_real_Icc
    {T : L ℋ} {α β : ℝ} (hT : IsSelfAdjoint T)
    (hσ : spectrum ℝ T ⊆ Set.Icc α β) :
    spectrum ℂ T ⊆ Complex.ofReal '' Set.Icc α β := by
  intro z hz
  rw [← hT.spectrumRestricts.algebraMap_image] at hz
  rcases hz with ⟨x, hx, rfl⟩
  exact ⟨x, hσ hx, rfl⟩

end Internal

end HansenPedersen
