/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.Core
import Quantum.TraceInequality.HiaiPetz.OperatorCore

import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Quantum.TraceInequality.HiaiPetzTheorem.Basic

/-!
# Block-matrix identities for functional calculus

This file supplies the block-operator calculations used in the
Hansen--Pedersen proof of the normal-CFC identities. The private off-diagonal
operator from `HansenPedersen.Internal` packages the usual `2 × 2` block argument,
while the public lemmas
record how continuous functional calculus behaves under block diagonals,
unitary conjugation, and the `A f(A* A) = f(A A*) A` intertwining identity.

## Main results

* `cfcR_diagMapCLM_union`: real CFC of a block diagonal operator is blockwise
  CFC.
* `cfcNormal_unitary_conj`: normal CFC commutes with unitary conjugation.
* `cfcR_star_mul_self_intertwine`: the block-matrix intertwining identity for
  `A* A` and `A A*`.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021,
  Lemma 5.1.6.
-/

namespace HansenPedersen

universe u

open CFC MeasureTheory
open scoped Topology
open Filter

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

section NormalCFC516

open Internal

private noncomputable def unitaryConjStarAlgHom (U : unitary (L ℋ)) :
    L ℋ →⋆ₐ[ℂ] L ℋ :=
  StarAlgHomClass.toStarAlgHom (Unitary.conjStarAlgAut ℂ (L ℋ) (star U))

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
@[simp] private lemma unitaryConjStarAlgHom_apply (U : unitary (L ℋ)) (A : L ℋ) :
    unitaryConjStarAlgHom U A = star (↑U : L ℋ) * A * (↑U : L ℋ) := by
  simp [unitaryConjStarAlgHom]

omit [Nontrivial (L ℋ)] in
/-- Real CFC of a block diagonal operator is computed on the two diagonal blocks,
provided `f` is continuous on the union of the two real spectra. -/
theorem cfcR_diagMapCLM_union {f : ℝ → ℝ} {a b : L ℋ}
    (hf : ContinuousOn f (spectrum ℝ a ∪ spectrum ℝ b))
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    cfc (R := ℝ) f (HansenPedersen.Internal.diagMapCLM a b) =
      HansenPedersen.Internal.diagMapCLM (cfc (R := ℝ) f a) (cfc (R := ℝ) f b) := by
  letI : ContinuousFunctionalCalculus ℂ (L ℋ × L ℋ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus ℝ (L ℋ × L ℋ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have hab : IsSelfAdjoint (a, b) := by
    change star (a, b) = (a, b)
    ext <;> simp [ha.star_eq, hb.star_eq]
  have hfab : ContinuousOn f (spectrum ℝ (a, b)) := by
    rwa [Prod.spectrum_eq]
  let Φ : (L ℋ × L ℋ) →⋆ₐ[ℂ]
      ((WithLp 2 (ℋ × ℋ)) →L[ℂ] (WithLp 2 (ℋ × ℋ))) :=
    HansenPedersen.Internal.diagStarAlgHom (K := ℋ) (L' := ℋ)
  have hmap := StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) Φ f (a, b)
    (hf := hfab)
    (hφ := by
      let e : WithLp 2 (ℋ × ℋ) ≃L[ℂ] ℋ × ℋ :=
        WithLp.prodContinuousLinearEquiv 2 ℂ ℋ ℋ
      let eCLM : WithLp 2 (ℋ × ℋ) →L[ℂ] ℋ × ℋ := e.toContinuousLinearMap
      let es : ℋ × ℋ →L[ℂ] WithLp 2 (ℋ × ℋ) := e.symm
      have hprod : Continuous fun ab : L ℋ × L ℋ => ab.1.prodMap ab.2 := by
        simpa using (Continuous.prod_mapL (𝕜 := ℂ) continuous_fst continuous_snd)
      have hinner : Continuous fun ab : L ℋ × L ℋ => (ab.1.prodMap ab.2).comp eCLM := by
        simpa [eCLM] using hprod.clm_comp continuous_const
      have houter :
          Continuous fun ab : L ℋ × L ℋ =>
            es.comp ((ab.1.prodMap ab.2).comp eCLM) := by
        simpa [es] using continuous_const.clm_comp hinner
      simpa [HansenPedersen.Internal.diagStarAlgHom, HansenPedersen.Internal.diagMapCLM, eCLM, es]
        using houter)
    (ha := hab)
  have hprod : cfc (R := ℝ) f (a, b) = (cfc (R := ℝ) f a, cfc (R := ℝ) f b) := by
    simpa using cfc_map_prod (R := ℝ) (S := ℝ) (A := L ℋ) (B := L ℋ)
      f a b (hf := hf) (hab := hab) (ha := ha) (hb := hb)
  simpa [Φ, cfcR] using hmap.symm.trans (congrArg Φ hprod)

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] in
private theorem spectrum_star_mul_self_subset_Icc_norm_sq (A : L ℋ) :
    spectrum ℝ ((star A) * A) ⊆ Set.Icc (0 : ℝ) (‖A‖ ^ 2) := by
  intro x hx
  constructor
  · exact spectrum_star_mul_self_nonneg x hx
  · have hxnorm := spectrum.norm_le_norm_of_mem hx
    have hxnonneg : 0 ≤ x := spectrum_star_mul_self_nonneg x hx
    simpa [Real.norm_eq_abs, abs_of_nonneg hxnonneg, CStarRing.norm_star_mul_self, pow_two] using
      hxnorm

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] in
private theorem spectrum_mul_star_self_subset_Icc_norm_sq (A : L ℋ) :
    spectrum ℝ (A * star A) ⊆ Set.Icc (0 : ℝ) (‖A‖ ^ 2) := by
  intro x hx
  have hx' : x ∈ spectrum ℝ (star (star A) * star A) := by
    simpa [star_star] using hx
  constructor
  · have : 0 ≤ x := by
      exact spectrum_star_mul_self_nonneg (b := star A) x hx'
    exact this
  · have hxnorm := spectrum.norm_le_norm_of_mem hx
    have hxnonneg : 0 ≤ x := by
      exact spectrum_star_mul_self_nonneg (b := star A) x hx'
    have hbound : x ≤ ‖A * star A‖ := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hxnonneg] using hxnorm
    calc
      x ≤ ‖A * star A‖ := hbound
      _ = ‖A‖ * ‖A‖ := by
        simpa [star_star, norm_star] using (CStarRing.norm_star_mul_self (x := star A))
      _ = ‖A‖ ^ 2 := by rw [pow_two]

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- **Lemma 5.1.6 (1)**: unitary conjugation commutes with the functional calculus.
Source: Hiai–Yanagi, Lemma 5.1.6. -/
theorem cfcNormal_unitary_conj :
    ∀ {A : L ℋ} (U : unitary (L ℋ)) {f : ℂ → ℂ},
      IsStarNormal A →
      ContinuousOn f (spectrum ℂ A) →
      cfcNormal (ℋ := ℋ) f (star (↑U : L ℋ) * A * (↑U : L ℋ)) =
        star (↑U : L ℋ) * cfcNormal (ℋ := ℋ) f A * (↑U : L ℋ) := by
  intro A U f hA hf
  let Φ : L ℋ →⋆ₐ[ℂ] L ℋ := unitaryConjStarAlgHom U
  have hΦA : IsStarNormal (Φ A) := by
    simpa [Φ] using hA.map Φ
  have hmap := StarAlgHomClass.map_cfc (R := ℂ) (S := ℂ) Φ f A
    (hf := hf)
    (hφ := by
      have hcont : Continuous fun X : L ℋ => star (↑U : L ℋ) * X * (↑U : L ℋ) := by
        simpa using
          (ContinuousLinearMap.mulLeftRight ℂ (L ℋ) (star (↑U : L ℋ))
            (↑U : L ℋ)).continuous
      change Continuous fun X : L ℋ => unitaryConjStarAlgHom U X
      simpa using hcont)
    (ha := hA) (hφa := hΦA)
  simpa [Φ, cfcNormal, mul_assoc] using hmap.symm


/-- **Lemma 5.1.6 (2)**: intertwining identity `A f(A* A) = f(AA*) A`.
Source: Hiai–Yanagi, Lemma 5.1.6. -/
theorem cfcR_star_mul_self_intertwine :
    ∀ {A : L ℋ} {f : ℝ → ℝ},
      ContinuousOn f (Set.Icc (0 : ℝ) (‖A‖ ^ 2)) →
      A * cfcR (ℋ := ℋ) f ((star A) * A) = cfcR (ℋ := ℋ) f (A * star A) * A := by
  intro A f hf
  let T : (WithLp 2 (ℋ × ℋ)) →L[ℂ] (WithLp 2 (ℋ × ℋ)) :=
    Internal.offDiagCLM (star A) A
  have hσ₁ : spectrum ℝ ((star A) * A) ⊆ Set.Icc (0 : ℝ) (‖A‖ ^ 2) :=
    spectrum_star_mul_self_subset_Icc_norm_sq A
  have hσ₂ : spectrum ℝ (A * star A) ⊆ Set.Icc (0 : ℝ) (‖A‖ ^ 2) :=
    spectrum_mul_star_self_subset_Icc_norm_sq A
  have hσdiag :
      spectrum ℝ ((star A) * A) ∪ spectrum ℝ (A * star A) ⊆
        Set.Icc (0 : ℝ) (‖A‖ ^ 2) := by
    intro x hx
    rcases hx with hx | hx
    · exact hσ₁ hx
    · exact hσ₂ hx
  have hT2 : T ^ 2 =
      HansenPedersen.Internal.diagMapCLM ((star A) * A) (A * star A) := by
    simpa [T, pow_two] using
      Internal.offDiagCLM_mul_offDiagCLM (star A) A (star A) A
  have hdiag :
      cfc (R := ℝ) f (T ^ 2) =
        HansenPedersen.Internal.diagMapCLM
          (cfc (R := ℝ) f ((star A) * A)) (cfc (R := ℝ) f (A * star A)) := by
    rw [hT2]
    exact cfcR_diagMapCLM_union (f := f) (hf := hf.mono hσdiag)
      (ha := IsSelfAdjoint.star_mul_self A) (hb := IsSelfAdjoint.mul_star_self A)
  have hT2T : Commute (T ^ 2) T := (Commute.refl T).pow_left 2
  have hcomm : Commute (cfc (R := ℝ) f (T ^ 2)) T := hT2T.cfc_real f
  have hEq :
      cfc (R := ℝ) f (T ^ 2) * T = T * cfc (R := ℝ) f (T ^ 2) := hcomm.eq
  have hOff :
      Internal.offDiagCLM
          (cfc (R := ℝ) f ((star A) * A) * star A)
          (cfc (R := ℝ) f (A * star A) * A) =
        Internal.offDiagCLM
          (star A * cfc (R := ℝ) f (A * star A))
          (A * cfc (R := ℝ) f ((star A) * A)) := by
    simpa [T, hdiag, Internal.diagMapCLM_mul_offDiagCLM,
      Internal.offDiagCLM_mul_diagMapCLM] using hEq
  rcases Internal.offDiagCLM_inj hOff with ⟨hfst, hsnd⟩
  simpa [cfcR] using hsnd.symm

end NormalCFC516

end HansenPedersen
