/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.CompressionInequality.SpectralBounds
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!
# Rotated block compressions for Hansen–Pedersen inequalities

This file isolates the block-rotation algebra used in the proof of
Hiai–Yanagi Theorem 5.1.7.  The main ingredients are unitary covariance of the
real continuous functional calculus and an explicit compression identity for
the scalar rotation block.

## Main results

* `unitaryConjStarAlgHom`: star-algebra homomorphism for unitary conjugation.
* `cfcR_unitary_conj`: real CFC commutes with conjugation by a unitary.
* `compress_rotated_diag`: the rotated diagonal block compresses to a convex
  combination on the first summand.
* `rotated_block_mem_unitary`: the scalar rotation block is unitary for
  `0 ≤ t ≤ 1`.

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

section RotatedBlockCompression

variable {K : Type*}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]

/-- Star-algebra homomorphism implementing conjugation by a unitary.  It is the
transport map used to move real CFC expressions through block rotations. -/
noncomputable def unitaryConjStarAlgHom (U : unitary (L K)) : L K →⋆ₐ[ℂ] L K :=
  StarAlgHomClass.toStarAlgHom (Unitary.conjStarAlgAut ℂ (L K) (star U))

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
/-- Evaluates `unitaryConjStarAlgHom` as the concrete conjugation
`A ↦ U* A U`. -/
@[simp] lemma unitaryConjStarAlgHom_apply (U : unitary (L K)) (A : L K) :
    unitaryConjStarAlgHom U A = star (↑U : L K) * A * (↑U : L K) := by
  simp [unitaryConjStarAlgHom]

omit [Nontrivial (L K)] in
/-- Real functional calculus commutes with unitary conjugation for
self-adjoint operators whose spectrum lies in the half-open domain of `f`. -/
theorem cfcR_unitary_conj {α : WithTop ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (halfOpenRay α))
    {A : L K} (hA : IsSelfAdjoint A) (hσA : spectrum ℝ A ⊆ halfOpenRay α)
    (U : unitary (L K)) :
    cfcR (ℋ := K) f (star (↑U : L K) * A * (↑U : L K)) =
      star (↑U : L K) * cfcR (ℋ := K) f A * (↑U : L K) := by
  let Φ : L K →⋆ₐ[ℂ] L K := unitaryConjStarAlgHom U
  have hΦA : IsSelfAdjoint (Φ A) := by
    simpa [Φ] using hA.map Φ
  have hmap := StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) Φ f A
    (hf := hf.mono hσA)
    (hφ := by
      have hcont : Continuous fun X : L K => star (↑U : L K) * X * (↑U : L K) := by
        simpa using
          (ContinuousLinearMap.mulLeftRight ℂ (L K) (star (↑U : L K)) (↑U : L K)).continuous
      change Continuous fun X : L K => unitaryConjStarAlgHom U X
      simpa using hcont)
    (ha := hA) (hφa := hΦA)
  simpa [Φ, cfcR, mul_assoc] using hmap.symm

-- The rotated compression identity expands a full `2 × 2` block conjugation.
omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
/-- Compressing a rotated diagonal block to the first summand gives the convex
combination `(1 - t) • S + t • T` when `0 ≤ t ≤ 1`. -/
lemma compress_rotated_diag
    {S T : L K} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let s : ℂ := Real.sqrt (1 - t)
    let r : ℂ := Real.sqrt t
    let P : L (WithLp 2 (K × K)) := HansenPedersen.Internal.diagMapCLM (1 : L K) 0
    let U0 : L (WithLp 2 (K × K)) :=
      blockCLM (s • (1 : L K)) (-(r • (1 : L K)))
        (r • (1 : L K)) (s • (1 : L K))
    P * (star U0 * HansenPedersen.Internal.diagMapCLM S T * U0) * P =
      HansenPedersen.Internal.diagMapCLM ((1 - t) • S + t • T) 0 := by
  have hs_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hsqtR : Real.sqrt t * Real.sqrt t = t := by
    simpa [pow_two] using Real.sq_sqrt ht0
  have hsqsR : Real.sqrt (1 - t) * Real.sqrt (1 - t) = 1 - t := by
    simpa [pow_two] using Real.sq_sqrt hs_nonneg
  have hsqtC : ((Real.sqrt t : ℂ) * (Real.sqrt t : ℂ)) = (t : ℂ) := by
    exact_mod_cast hsqtR
  have hsqsC : ((Real.sqrt (1 - t) : ℂ) * (Real.sqrt (1 - t) : ℂ)) = ((1 - t : ℝ) : ℂ) := by
    exact_mod_cast hsqsR
  have hsqsR' : Real.sqrt (-t + 1) * Real.sqrt (-t + 1) = (-t + 1 : ℝ) := by
    simpa [sub_eq_add_neg, add_comm] using hsqsR
  have hsqsC' :
      ((Real.sqrt (-t + 1) : ℂ) * (Real.sqrt (-t + 1) : ℂ)) =
        ((-t + 1 : ℝ) : ℂ) := by
    exact_mod_cast hsqsR'
  have hsmul_apply_real (c : ℝ) (f : L K) (y : K) : (c • f) y = c • f y := by
    rfl
  have hsmul_real_as_complex (c : ℝ) (y : K) : ((c : ℂ) • y) = c • y := by
    rfl
  dsimp
  rw [blockCLM_star]
  ext x
  apply WithLp.ofLp_injective
  ext
  · simp only [star_smul, star_trivial, star_one, star_neg, ContinuousLinearMap.coe_mul',
      Function.comp_apply, Internal.diagMapCLM_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.zero_apply, blockCLM_apply, WithLp.toLp_fst, WithLp.toLp_snd,
      ContinuousLinearMap.neg_apply, map_zero, add_zero,
      ContinuousLinearMap.add_apply]
    calc
      ((Real.sqrt (1 - t) : ℂ) • (1 : L K))
          (S (((Real.sqrt (1 - t) : ℂ) • (1 : L K)) x.fst)) +
          ((Real.sqrt t : ℂ) • (1 : L K)) (T (((Real.sqrt t : ℂ) • (1 : L K)) x.fst))
          = (((Real.sqrt (1 - t) : ℂ) * (Real.sqrt (1 - t) : ℂ)) • S x.fst) +
              (((Real.sqrt t : ℂ) * (Real.sqrt t : ℂ)) • T x.fst) := by
              congr 1
              · calc
                  ((Real.sqrt (1 - t) : ℂ) • (1 : L K))
                      (S (((Real.sqrt (1 - t) : ℂ) • (1 : L K)) x.fst))
                      = (Real.sqrt (1 - t) : ℂ) •
                          S (((Real.sqrt (1 - t) : ℂ) • (1 : L K)) x.fst) := by
                          rw [ContinuousLinearMap.smul_apply]
                          simp [ContinuousLinearMap.one_apply]
                  _ = (Real.sqrt (1 - t) : ℂ) • S ((Real.sqrt (1 - t) : ℂ) • x.fst) := by
                          rw [ContinuousLinearMap.smul_apply]
                          simp [ContinuousLinearMap.one_apply]
                  _ = (Real.sqrt (1 - t) : ℂ) • ((Real.sqrt (1 - t) : ℂ) • S x.fst) := by
                          rw [S.map_smul]
                  _ = (((Real.sqrt (1 - t) : ℂ) * (Real.sqrt (1 - t) : ℂ)) • S x.fst) := by
                          rw [smul_smul]
              · calc
                  ((Real.sqrt t : ℂ) • (1 : L K))
                      (T (((Real.sqrt t : ℂ) • (1 : L K)) x.fst))
                      = (Real.sqrt t : ℂ) • T (((Real.sqrt t : ℂ) • (1 : L K)) x.fst) := by
                          rw [ContinuousLinearMap.smul_apply]
                          simp [ContinuousLinearMap.one_apply]
                  _ = (Real.sqrt t : ℂ) • T ((Real.sqrt t : ℂ) • x.fst) := by
                          rw [ContinuousLinearMap.smul_apply]
                          simp [ContinuousLinearMap.one_apply]
                  _ = (Real.sqrt t : ℂ) • ((Real.sqrt t : ℂ) • T x.fst) := by
                          rw [T.map_smul]
                  _ = (((Real.sqrt t : ℂ) * (Real.sqrt t : ℂ)) • T x.fst) := by
                          rw [smul_smul]
      _ = ((1 - t) • S) x.fst + (t • T) x.fst := by
            have hT :
                (((Real.sqrt t : ℂ) * (Real.sqrt t : ℂ)) • T x.fst) = (t • T) x.fst := by
              rw [hsqtC]
              rfl
            have hS :
                (((Real.sqrt (1 - t) : ℂ) * (Real.sqrt (1 - t) : ℂ)) • S x.fst) =
                  ((1 - t) • S) x.fst := by
              rw [hsqsC]
              rw [hsmul_real_as_complex, hsmul_apply_real]
            rw [hT, hS]
  · simp only [star_smul, star_trivial, star_one, star_neg, ContinuousLinearMap.coe_mul',
      Function.comp_apply, Internal.diagMapCLM_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.zero_apply, blockCLM_apply, WithLp.toLp_fst, WithLp.toLp_snd,
      ContinuousLinearMap.neg_apply, map_zero, add_zero,
      ContinuousLinearMap.add_apply]

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
/-- A `2 × 2` rotation block with self-conjugate scalar entries `s`, `r` satisfying
`s * s + r * r = 1` is unitary. -/
private lemma scalar_rotation_block_mem_unitary {s r : ℂ}
    (hs : star s = s) (hr : star r = r) (h : s * s + r * r = 1) :
    blockCLM (s • (1 : L K)) (-(r • (1 : L K))) (r • (1 : L K)) (s • (1 : L K)) ∈
      unitary (L (WithLp 2 (K × K))) := by
  have hm (x y : ℂ) : (x • (1 : L K)) * (y • (1 : L K)) = (x * y) • (1 : L K) := by
    rw [smul_mul_smul_comm, one_mul]
  have hss : star (s • (1 : L K)) = s • (1 : L K) := by rw [star_smul, star_one, hs]
  have hrr : star (r • (1 : L K)) = r • (1 : L K) := by rw [star_smul, star_one, hr]
  have hd : (s • (1 : L K)) * (s • (1 : L K)) + (r • (1 : L K)) * (r • (1 : L K)) = 1 := by
    rw [hm, hm, ← add_smul, h, one_smul]
  have hd' : (r • (1 : L K)) * (r • (1 : L K)) + (s • (1 : L K)) * (s • (1 : L K)) = 1 := by
    rw [add_comm]; exact hd
  have ho : (s • (1 : L K)) * (r • (1 : L K)) = (r • (1 : L K)) * (s • (1 : L K)) := by
    rw [hm, hm, mul_comm]
  rw [Unitary.mem_iff, blockCLM_star, blockCLM_mul, blockCLM_mul, star_neg, hss, hrr]
  simp only [mul_neg, neg_mul, neg_neg, hd, hd', ho, neg_add_cancel, add_neg_cancel]
  exact ⟨blockCLM_one, blockCLM_one⟩

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
/-- The scalar `2 × 2` rotation block with entries `sqrt (1 - t)` and
`sqrt t` is unitary for `0 ≤ t ≤ 1`. -/
lemma rotated_block_mem_unitary {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let s : ℂ := Real.sqrt (1 - t)
    let r : ℂ := Real.sqrt t
    let U0 : L (WithLp 2 (K × K)) :=
      blockCLM (s • (1 : L K)) (-(r • (1 : L K)))
        (r • (1 : L K)) (s • (1 : L K))
    U0 ∈ unitary (L (WithLp 2 (K × K))) := by
  have hsum : Real.sqrt (1 - t) * Real.sqrt (1 - t) + Real.sqrt t * Real.sqrt t = 1 := by
    rw [Real.mul_self_sqrt (sub_nonneg.mpr ht1), Real.mul_self_sqrt ht0]
    ring
  exact scalar_rotation_block_mem_unitary (Complex.conj_ofReal _) (Complex.conj_ofReal _)
    (by exact_mod_cast hsum)

end RotatedBlockCompression

end ConvexityCharacterization

end NormalCFC517

end HansenPedersen
