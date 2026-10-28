/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.PetzTraceClassification.GSLCore
import Quantum.QuantumEntropy.CFCDeriv
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Quantum.QuantumEntropy.Common.TraceRe

/-!
# Exponent calculus for support-aware powers

This module supplies the fixed-positive-operator exponent calculus for
`petzSupportRpow`.  Unlike `CFC.rpow`, its value at exponent zero is the
orthogonal support projection, so the exponent path stays continuous and
differentiable for singular positive operators.
-/

namespace OPT

open QuantumState
open SandwichedRenyiRelativeEntropy
open MeasureTheory
open scoped Topology UniformConvergence

universe u

noncomputable section

variable {H : Type u} [Qudit H] [Nontrivial H]

omit [Nontrivial H] in
/-- The support projection of `A` acts as the identity on a nonnegative `B`
whose kernel contains the kernel of `A`. -/
theorem petzSupportRpow_zero_mul_eq_of_ker_le
    {A B : L H} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hker : LinearMap.ker A ≤ LinearMap.ker B) :
    petzSupportRpow A 0 * B = B := by
  have hAs : A.IsSymmetric :=
    ((LinearMap.nonneg_iff_isPositive A).mp hA).isSymmetric
  have hBs : B.IsSymmetric :=
    ((LinearMap.nonneg_iff_isPositive B).mp hB).isSymmetric
  have hrange : LinearMap.range B ≤ LinearMap.range A := by
    have ho := Submodule.orthogonal_le hker
    simpa [LinearMap.orthogonal_ker, hAs.adjoint_eq, hBs.adjoint_eq] using ho
  rw [petzSupportRpow_zero]
  ext x
  change (LinearMap.range A).starProjection (B x) = B x
  exact Submodule.starProjection_eq_self_iff.mpr (hrange ⟨x, rfl⟩)

omit [Nontrivial H] in
/-- The corresponding right-action identity for the support projection. -/
theorem mul_petzSupportRpow_zero_eq_of_ker_le
    {A B : L H} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hker : LinearMap.ker A ≤ LinearMap.ker B) :
    B * petzSupportRpow A 0 = B := by
  have hleft := petzSupportRpow_zero_mul_eq_of_ker_le hA hB hker
  have hPsa : IsSelfAdjoint (petzSupportRpow A 0) :=
    IsSelfAdjoint.of_nonneg (petzSupportRpow_nonneg A 0)
  have hBsa : IsSelfAdjoint B := IsSelfAdjoint.of_nonneg hB
  calc
    B * petzSupportRpow A 0 =
        star (petzSupportRpow A 0 * B) := by
      rw [star_mul, hPsa.star_eq, hBsa.star_eq]
    _ = star B := by rw [hleft]
    _ = B := hBsa.star_eq

/-- A nonzero product of two nonnegative finite-dimensional operators has
strictly positive real trace. -/
theorem trace_re_pos_mul_of_nonneg_of_ne_zero
    {X Y : L H} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hXY : X * Y ≠ 0) :
    0 < (Tr (X * Y)).re := by
  let Z : L H := CFC.sqrt X * CFC.sqrt Y
  have hZ_ne : Z ≠ 0 := by
    intro hZ
    apply hXY
    calc
      X * Y = (CFC.sqrt X * CFC.sqrt X) *
          (CFC.sqrt Y * CFC.sqrt Y) := by
        rw [CFC.sqrt_mul_sqrt_self X hX, CFC.sqrt_mul_sqrt_self Y hY]
      _ = CFC.sqrt X * (CFC.sqrt X * CFC.sqrt Y) * CFC.sqrt Y := by
        simp only [mul_assoc]
      _ = 0 := by rw [show CFC.sqrt X * CFC.sqrt Y = 0 from hZ]; simp
  have hstarZ_ne : star Z * Z ≠ 0 :=
    not_congr (CStarRing.star_mul_self_eq_zero_iff Z) |>.mpr hZ_ne
  have htrace_pos := QuantumEntropy.trace_re_pos_of_ne_zero
    (star_mul_self_nonneg Z) hstarZ_ne
  have hsx_sa : IsSelfAdjoint (CFC.sqrt X) :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg X)
  have hsy_sa : IsSelfAdjoint (CFC.sqrt Y) :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg Y)
  have htrace : Tr (star Z * Z) = Tr (X * Y) := by
    dsimp [Z]
    calc
      Tr (star (CFC.sqrt X * CFC.sqrt Y) *
          (CFC.sqrt X * CFC.sqrt Y)) =
          Tr ((CFC.sqrt Y * CFC.sqrt X) *
            (CFC.sqrt X * CFC.sqrt Y)) := by
        rw [star_mul, hsx_sa.star_eq, hsy_sa.star_eq]
      _ = Tr (CFC.sqrt Y *
          ((CFC.sqrt X * CFC.sqrt X) * CFC.sqrt Y)) := by
        simp only [mul_assoc]
      _ = Tr (CFC.sqrt Y * (X * CFC.sqrt Y)) := by
        rw [CFC.sqrt_mul_sqrt_self X hX]
      _ = Tr ((X * CFC.sqrt Y) * CFC.sqrt Y) :=
        LinearMap.trace_mul_comm ℂ (CFC.sqrt Y) (X * CFC.sqrt Y)
      _ = Tr (X * (CFC.sqrt Y * CFC.sqrt Y)) := by rw [mul_assoc]
      _ = Tr (X * Y) := by rw [CFC.sqrt_mul_sqrt_self Y hY]
  rwa [htrace] at htrace_pos

/-- Joint continuity of positive real powers on a norm-bounded part of the
positive cone.  The exponent is allowed to vary, which is the public order
continuity input missing from the fixed-exponent CFC API. -/
theorem continuousOn_cfcRpow_positive_bounded (R : ℝ) :
    ContinuousOn (fun p : L H × ℝ => CFC.rpow p.1 p.2)
      ({A : L H | 0 ≤ A ∧ ‖A‖ ≤ R} ×ˢ Set.Ioi 0) := by
  classical
  intro z hz
  have hzpos : 0 < z.2 := hz.2
  let c : ℝ := z.2 / 2
  have hc : 0 < c := by
    dsimp [c]
    linarith
  let s : Set ℝ := Set.Icc 0 R
  have hsCompact : IsCompact s := isCompact_Icc
  let f : ℝ → ℝ → ℝ := fun p x => x ^ max p c
  have hfJoint : Continuous (fun q : ℝ × s => f q.1 q.2) := by
    rw [continuous_iff_continuousAt]
    intro q
    have hpow := Real.continuousAt_rpow (q.2.1, max q.1 c)
      (Or.inr (lt_of_lt_of_le hc (le_max_right _ _)))
    have hpair : ContinuousAt
        (fun q : ℝ × s => (q.2.1, max q.1 c)) q :=
      ((continuous_subtype_val.comp continuous_snd).continuousAt).prodMk
        ((continuous_fst.max continuous_const).continuousAt)
    exact hpow.tendsto.comp hpair
  have hfOn (p : ℝ) : ContinuousOn (f p) s := by
    rw [continuousOn_iff_continuous_restrict]
    have hp : Continuous (fun x : s => (p, x)) :=
      continuous_const.prodMk continuous_id
    simpa [Function.comp_def, Set.restrict] using hfJoint.comp hp
  let F : ℝ → UniformOnFun ℝ ℝ {s} := fun p => UniformOnFun.ofFun {s} (f p)
  have hF : Continuous F := by
    apply (ContinuousOn.continuous_restrict_iff_continuous_uniformOnFun hfOn).mp
    apply ContinuousMap.continuous_of_continuous_uncurry
    simpa [Function.uncurry] using hfJoint
  let g : (L H × ℝ) → UniformOnFun ℝ ℝ {s} × L H := fun p => (F p.2, p.1)
  have hg : Continuous g := (hF.comp continuous_snd).prodMk continuous_fst
  have hmap : Set.MapsTo g
      ({A : L H | 0 ≤ A ∧ ‖A‖ ≤ R} ×ˢ Set.univ)
      ({q : UniformOnFun ℝ ℝ {s} | ContinuousOn (UniformOnFun.toFun {s} q) s} ×ˢ
        {A : L H | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ s}) := by
    rintro ⟨A, p⟩ ⟨hA, _⟩
    refine ⟨hfOn p, (IsSelfAdjoint.of_nonneg hA.1), ?_⟩
    intro x hx
    refine ⟨spectrum_nonneg_of_nonneg hA.1 hx, ?_⟩
    have hnorm := spectrum.norm_le_norm_of_mem hx
    rw [Real.norm_eq_abs, abs_of_nonneg (spectrum_nonneg_of_nonneg hA.1 hx)] at hnorm
    exact hnorm.trans hA.2
  have hmod : ContinuousOn
      (fun p : L H × ℝ => cfc (f p.2) p.1)
      ({A : L H | 0 ≤ A ∧ ‖A‖ ≤ R} ×ˢ Set.univ) := by
    have h := (continuousOn_cfc_setProd (A := L H) hsCompact).comp
      hg.continuousOn hmap
    simpa [g, F, f, s] using h
  have hbase := hmod z ⟨hz.1, Set.mem_univ _⟩
  have heq : (fun p : L H × ℝ => CFC.rpow p.1 p.2) =ᶠ[
      𝓝[{A : L H | 0 ≤ A ∧ ‖A‖ ≤ R} ×ˢ Set.Ioi 0] z]
      (fun p : L H × ℝ => cfc (f p.2) p.1) := by
    have hnear : ∀ᶠ p : L H × ℝ in 𝓝 z, c < p.2 :=
      continuousAt_snd.eventually (eventually_gt_nhds (by dsimp [c]; linarith))
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with p hp hpmem
    have hA : 0 ≤ p.1 := hpmem.1.1
    rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hA]
    apply cfc_congr
    intro x _
    simp only [f, max_eq_left hp.le]
  exact hbase.mono (Set.prod_mono (Set.Subset.rfl) (Set.subset_univ _)) |>.congr_of_eventuallyEq
    heq (by
      rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hz.1.1]
      apply cfc_congr
      intro x _
      change x ^ z.2 = x ^ max z.2 c
      rw [max_eq_left (by dsimp [c]; linarith)])

/-- Local composition rule for a simultaneously varying nonnegative base and
positive exponent. -/
theorem continuousWithinAt_cfcRpow_of_pos
    {X : Type*} [TopologicalSpace X] {A : X → L H} {p : X → ℝ}
    {t : Set X} {x : X}
    (hA : ContinuousWithinAt A t x) (hp : ContinuousWithinAt p t x)
    (hAnonneg : ∀ᶠ y in 𝓝[t] x, 0 ≤ A y)
    (hppos : ∀ᶠ y in 𝓝[t] x, 0 < p y)
    (hAx : 0 ≤ A x) (hpx : 0 < p x) :
    ContinuousWithinAt (fun y => CFC.rpow (A y) (p y)) t x := by
  let R : ℝ := ‖A x‖ + 1
  let D : Set (L H × ℝ) :=
    {B : L H | 0 ≤ B ∧ ‖B‖ ≤ R} ×ˢ Set.Ioi 0
  have htarget : (A x, p x) ∈ D := by
    refine ⟨⟨hAx, ?_⟩, hpx⟩
    dsimp [R]
    linarith
  have hnorm : ∀ᶠ y in 𝓝[t] x, ‖A y‖ < R := by
    have hlt : ‖A x‖ < R := by dsimp [R]; linarith
    exact hA.norm.tendsto.eventually (eventually_lt_nhds hlt)
  have hpairWithin : Filter.Tendsto (fun y => (A y, p y)) (𝓝[t] x)
      (𝓝[D] (A x, p x)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(hA.prodMk hp).tendsto, ?_⟩
    filter_upwards [hAnonneg, hppos, hnorm] with y hyA hyp hynorm
    exact ⟨⟨hyA, hynorm.le⟩, hyp⟩
  exact ((continuousOn_cfcRpow_positive_bounded (H := H) R)
    (A x, p x) htarget).tendsto.comp hpairWithin

end

end OPT
