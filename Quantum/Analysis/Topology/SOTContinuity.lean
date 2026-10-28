/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Basic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Strong-operator continuity of real functional calculus

This file proves the self-adjoint, real-CFC form of strong-operator continuity
needed by the positive-ray Loewner bridge.
-/

namespace Quantum.TraceInequality.Loewner

open CFC Filter
open scoped Topology

private lemma sot_mul_of_uniformBound
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {ι : Type*} {l : Filter ι}
    {Aγ Bγ : ι → HansenPedersen.L K} {A B : HansenPedersen.L K}
    (hA : ∀ x, Tendsto (fun i => Aγ i x) l (𝓝 (A x)))
    (hB : ∀ x, Tendsto (fun i => Bγ i x) l (𝓝 (B x)))
    (hbound : ∃ M > 0, ∀ i, ‖Aγ i‖ ≤ M) :
    ∀ x, Tendsto (fun i => (Aγ i * Bγ i) x) l (𝓝 ((A * B) x)) := by
  rcases hbound with ⟨M, hMpos, hM⟩
  intro x
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hBx : Tendsto (fun i => Bγ i x - B x) l (𝓝 (0 : K)) := by
    simpa using
      (hB x).sub (tendsto_const_nhds : Tendsto (fun _ : ι => B x) l (𝓝 (B x)))
  have hterm1 : Tendsto (fun i => Aγ i (Bγ i x - B x)) l (𝓝 (0 : K)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbound' : ∀ i, ‖Aγ i (Bγ i x - B x)‖ ≤ M * ‖Bγ i x - B x‖ := by
      intro i
      calc
        ‖Aγ i (Bγ i x - B x)‖ ≤ ‖Aγ i‖ * ‖Bγ i x - B x‖ := (Aγ i).le_opNorm _
        _ ≤ M * ‖Bγ i x - B x‖ := by
          gcongr
          exact hM i
    have hlim : Tendsto (fun i => M * ‖Bγ i x - B x‖) l (𝓝 (0 : ℝ)) := by
      simpa using (tendsto_norm.comp hBx).const_mul M
    exact squeeze_zero (fun _ => norm_nonneg _) hbound' hlim
  have hterm2 : Tendsto (fun i => (Aγ i - A) (B x)) l (𝓝 (0 : K)) := by
    simpa using
      (hA (B x)).sub
        (tendsto_const_nhds : Tendsto (fun _ : ι => A (B x)) l (𝓝 (A (B x))))
  have hsum := hterm1.add hterm2
  have hEq :
      (fun i => (Aγ i * Bγ i) x - (A * B) x) =
        fun i => Aγ i (Bγ i x - B x) + (Aγ i - A) (B x) := by
    funext i
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  simpa [hEq] using (tendsto_norm.comp hsum)

private lemma norm_cfcHomSuperset_sub_apply_le
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    [Nontrivial (HansenPedersen.L K)]
    {Ω : Set ℝ} [CompactSpace Ω] {T : HansenPedersen.L K}
    (hT : IsSelfAdjoint T) (hσT : spectrum ℝ T ⊆ Ω)
    (g p : C(Ω, ℝ)) (x : K) :
    ‖cfcHomSuperset hT hσT g x - cfcHomSuperset hT hσT p x‖ ≤
      ‖g - p‖ * ‖x‖ := by
  have hnorm : ‖cfcHomSuperset hT hσT (g - p)‖ ≤ ‖g - p‖ := by
    rw [cfcHomSuperset_apply]
    rw [isometry_cfcHom (R := ℝ) _ hT
      |>.norm_map_of_map_zero (map_zero (cfcHom hT))]
    rw [ContinuousMap.norm_le _ (norm_nonneg _)]
    intro z
    exact ContinuousMap.norm_coe_le_norm (g - p) ⟨z, hσT z.2⟩
  calc
    ‖cfcHomSuperset hT hσT g x - cfcHomSuperset hT hσT p x‖ =
        ‖(cfcHomSuperset hT hσT (g - p)) x‖ := by
      rw [map_sub]
      rfl
    _ ≤ ‖cfcHomSuperset hT hσT (g - p)‖ * ‖x‖ :=
      (cfcHomSuperset hT hσT (g - p)).le_opNorm x
    _ ≤ ‖g - p‖ * ‖x‖ := by
      gcongr

private lemma norm_cfcHomSuperset_le
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    {Ω : Set ℝ} [CompactSpace Ω] {T : HansenPedersen.L K}
    (hT : IsSelfAdjoint T) (hσT : spectrum ℝ T ⊆ Ω) (g : C(Ω, ℝ)) :
    ‖cfcHomSuperset hT hσT g‖ ≤ ‖g‖ := by
  rw [cfcHomSuperset_apply]
  rw [isometry_cfcHom (R := ℝ) _ hT
    |>.norm_map_of_map_zero (map_zero (cfcHom hT))]
  rw [ContinuousMap.norm_le _ (norm_nonneg _)]
  intro z
  exact ContinuousMap.norm_coe_le_norm g ⟨z, hσT z.2⟩

/-- The approximation step of `cfcR_tendsto_sot_of_Icc`: strong convergence of the superset
functional calculus passes from functions frequently near `g` to `g` itself. -/
private lemma tendsto_cfcHomSuperset_of_frequently
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    [Nontrivial (HansenPedersen.L K)]
    {ι : Type*} [Preorder ι] {Ω : Set ℝ} [CompactSpace Ω]
    {Aγ : ι → HansenPedersen.L K} {A : HansenPedersen.L K}
    (hAγ : ∀ i, IsSelfAdjoint (Aγ i)) (hA : IsSelfAdjoint A)
    (hσAγ : ∀ i, spectrum ℝ (Aγ i) ⊆ Ω) (hσA : spectrum ℝ A ⊆ Ω) (g : C(Ω, ℝ))
    (hg : ∃ᶠ p in 𝓝 g, ∀ x, Tendsto (fun i => cfcHomSuperset (hAγ i) (hσAγ i) p x)
      Filter.atTop (𝓝 (cfcHomSuperset hA hσA p x))) :
    ∀ x, Tendsto (fun i => cfcHomSuperset (hAγ i) (hσAγ i) g x)
      Filter.atTop (𝓝 (cfcHomSuperset hA hσA g x)) := by
  intro x
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  let R : ℝ := max ‖x‖ 1
  have hRpos : 0 < R := by
    dsimp [R]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hδ : 0 < ε / (3 * R) := by
    positivity
  obtain ⟨p, hpclose, hpconv⟩ := frequently_iff.mp hg
    (Metric.closedBall_mem_nhds g hδ)
  have hpclose' : ‖g - p‖ ≤ ε / (3 * R) := by
    simpa [dist_eq_norm, norm_sub_rev] using hpclose
  have hxR : ‖x‖ ≤ R := by
    dsimp [R]
    exact le_max_left _ _
  have hscale : (ε / (3 * R)) * R = ε / 3 := by
    field_simp [ne_of_gt hRpos]
  have hsource : ∀ i,
      ‖cfcHomSuperset (hAγ i) (hσAγ i) g x -
          cfcHomSuperset (hAγ i) (hσAγ i) p x‖ ≤ ε / 3 := by
    intro i
    calc
      ‖cfcHomSuperset (hAγ i) (hσAγ i) g x -
          cfcHomSuperset (hAγ i) (hσAγ i) p x‖ ≤ ‖g - p‖ * ‖x‖ :=
        norm_cfcHomSuperset_sub_apply_le (hAγ i) (hσAγ i) g p x
      _ ≤ (ε / (3 * R)) * R := by
        gcongr
      _ = ε / 3 := hscale
  have htarget :
      ‖cfcHomSuperset hA hσA g x - cfcHomSuperset hA hσA p x‖ ≤ ε / 3 := by
    calc
      ‖cfcHomSuperset hA hσA g x - cfcHomSuperset hA hσA p x‖ ≤
          ‖g - p‖ * ‖x‖ :=
        norm_cfcHomSuperset_sub_apply_le hA hσA g p x
      _ ≤ (ε / (3 * R)) * R := by
        gcongr
      _ = ε / 3 := hscale
  have hpconv' := Metric.tendsto_nhds.mp (hpconv x) (ε / 3) (by positivity)
  filter_upwards [hpconv'] with i hi
  have htri :
      ‖cfcHomSuperset (hAγ i) (hσAγ i) g x - cfcHomSuperset hA hσA g x‖ ≤
        ‖cfcHomSuperset (hAγ i) (hσAγ i) g x -
            cfcHomSuperset (hAγ i) (hσAγ i) p x‖ +
        ‖cfcHomSuperset (hAγ i) (hσAγ i) p x - cfcHomSuperset hA hσA p x‖ +
        ‖cfcHomSuperset hA hσA p x - cfcHomSuperset hA hσA g x‖ := by
    calc
      ‖cfcHomSuperset (hAγ i) (hσAγ i) g x - cfcHomSuperset hA hσA g x‖ ≤
          ‖cfcHomSuperset (hAγ i) (hσAγ i) g x -
              cfcHomSuperset (hAγ i) (hσAγ i) p x‖ +
          ‖cfcHomSuperset (hAγ i) (hσAγ i) p x - cfcHomSuperset hA hσA g x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤
          ‖cfcHomSuperset (hAγ i) (hσAγ i) g x -
              cfcHomSuperset (hAγ i) (hσAγ i) p x‖ +
          (‖cfcHomSuperset (hAγ i) (hσAγ i) p x - cfcHomSuperset hA hσA p x‖ +
            ‖cfcHomSuperset hA hσA p x - cfcHomSuperset hA hσA g x‖) := by
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = _ := by ring
  have htarget' :
      ‖cfcHomSuperset hA hσA p x - cfcHomSuperset hA hσA g x‖ ≤ ε / 3 := by
    simpa only [norm_sub_rev] using htarget
  have hi' :
      ‖cfcHomSuperset (hAγ i) (hσAγ i) p x - cfcHomSuperset hA hσA p x‖ <
        ε / 3 := by
    simpa only [dist_eq_norm] using hi
  have hfinal :
      ‖cfcHomSuperset (hAγ i) (hσAγ i) g x - cfcHomSuperset hA hσA g x‖ < ε := by
    linarith [htri, hsource i, hi', htarget']
  simpa only [dist_eq_norm] using hfinal

/-- Real continuous functional calculus on one compact interval preserves strong-operator
convergence of a net of self-adjoint operators with spectra in that interval. -/
theorem cfcR_tendsto_sot_of_Icc
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    [Nontrivial (HansenPedersen.L K)]
    {ι : Type*} [Preorder ι] [NeBot (Filter.atTop : Filter ι)]
    {f : ℝ → ℝ} {Aγ : ι → HansenPedersen.L K}
    {A : HansenPedersen.L K} {α β : ℝ}
    (hf : ContinuousOn f (Set.Icc α β))
    (hAγ : ∀ i, IsSelfAdjoint (Aγ i))
    (hA : IsSelfAdjoint A)
    (hσAγ : ∀ i, spectrum ℝ (Aγ i) ⊆ Set.Icc α β)
    (hσA : spectrum ℝ A ⊆ Set.Icc α β)
    (hconv : ∀ x, Tendsto (fun i => Aγ i x) Filter.atTop (𝓝 (A x))) :
    ∀ x, Tendsto
      (fun i => HansenPedersen.cfcR f (Aγ i) x)
      Filter.atTop (𝓝 (HansenPedersen.cfcR f A x)) := by
  let fΩ : C(Set.Icc α β, ℝ) := ⟨_, hf.restrict⟩
  have hΩ : IsCompact (Set.Icc α β) := isCompact_Icc
  letI : CompactSpace (Set.Icc α β) := by
    rwa [isCompact_iff_compactSpace] at hΩ
  have hP : ∀ g : C(Set.Icc α β, ℝ),
      ∀ x, Tendsto (fun i => cfcHomSuperset (hAγ i) (hσAγ i) g x)
        Filter.atTop (𝓝 (cfcHomSuperset hA hσA g x)) := by
    intro g
    induction g using ContinuousMap.induction_on_of_compact with
    | const c =>
        intro x
        have : ContinuousMap.const (Set.Icc α β) c =
            algebraMap ℝ C(Set.Icc α β, ℝ) c := rfl
        simpa only [this, AlgHomClass.commutes] using tendsto_const_nhds
    | id =>
        intro x
        simpa only [cfcHomSuperset_id] using hconv x
    | star_id =>
        intro x
        have hstar :
            star (ContinuousMap.restrict (Set.Icc α β) (ContinuousMap.id ℝ)) =
              ContinuousMap.restrict (Set.Icc α β) (ContinuousMap.id ℝ) := by
          ext z
          simp
        simpa only [hstar, cfcHomSuperset_id] using hconv x
    | add g p hg hp =>
        intro x
        simpa only [map_add] using (hg x).add (hp x)
    | mul g p hg hp =>
        have hbound : ∃ M > 0,
            ∀ i, ‖cfcHomSuperset (hAγ i) (hσAγ i) g‖ ≤ M :=
          ⟨‖g‖ + 1, by positivity, fun i =>
            (norm_cfcHomSuperset_le (hAγ i) (hσAγ i) g).trans (by linarith)⟩
        simpa only [map_mul] using
          sot_mul_of_uniformBound hg hp hbound
    | frequently g hg =>
        exact tendsto_cfcHomSuperset_of_frequently hAγ hA hσAγ hσA g hg
  intro x
  have hx := hP fΩ x
  have hx' :
      Tendsto (fun i => HansenPedersen.cfcR f (Aγ i) x) Filter.atTop
        (𝓝 (cfcHomSuperset hA hσA fΩ x)) := by
    refine hx.congr' ?_
    exact .of_forall fun i => by
      have hcfc : cfcHomSuperset (hAγ i) (hσAγ i) fΩ = cfc f (Aγ i) := by
        dsimp [fΩ]
        symm
        simpa [cfcHomSuperset_apply, Set.restrict_apply] using
          (cfc_apply (f := f) (a := Aγ i) (ha := hAγ i) (hf := hf.mono (hσAγ i)))
      simpa [HansenPedersen.cfcR] using congrArg (fun T => T x) hcfc
  have hcfcA : cfcHomSuperset hA hσA fΩ = HansenPedersen.cfcR f A := by
    dsimp [fΩ, HansenPedersen.cfcR]
    symm
    simpa [cfcHomSuperset_apply, Set.restrict_apply] using
      (cfc_apply (f := f) (a := A) (ha := hA) (hf := hf.mono hσA))
  simpa [hcfcA] using hx'

end Quantum.TraceInequality.Loewner
