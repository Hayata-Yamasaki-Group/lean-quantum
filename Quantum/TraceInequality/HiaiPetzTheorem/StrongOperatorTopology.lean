/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetzTheorem.Core
import Quantum.TraceInequality.HiaiPetz.OperatorCore

import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Quantum.TraceInequality.HiaiPetzTheorem.Basic

/-!
# Strong-operator continuity for normal functional calculus

This file develops the strong-operator-topology tools needed for the
Hansen--Pedersen route. It records pointwise strong convergence of bounded
operators, proves the elementary stability properties used by the
Stone--Weierstrass argument, and then proves preservation of strong
convergence by normal continuous functional calculus on a fixed compact
spectral set.

## Main results

* `SOTTendstoAlong`: strong-operator convergence along an arbitrary filter.
* `SOTTendsto`: strong-operator convergence along a nondegenerate `Filter.atTop`.
* `SOTTendsto_mul_of_uniformBound`: multiplication is continuous when the
  left factor is uniformly norm-bounded.
* `SOTTendsto.cfcNormal`: normal CFC preserves strong-operator convergence.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021,
  Lemma 5.1.4.
-/

namespace HansenPedersen

universe u

open CFC MeasureTheory
open scoped Topology
open Filter

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

section NormalCFC514

/-- Strong operator convergence along an arbitrary filter. -/
def SOTTendstoAlong {ι : Type*} (l : Filter ι) (Aγ : ι → L ℋ) (A : L ℋ) : Prop :=
  ∀ x : ℋ, Tendsto (fun i => Aγ i x) l (nhds (A x))

/-- Strong operator convergence along `Filter.atTop`.  The `NeBot` assumption records
explicitly that the indexing preorder is nonempty and directed, so convergence is not
vacuous through a degenerate `atTop` filter. -/
def SOTTendsto {ι : Type*} [Preorder ι] [NeBot (atTop : Filter ι)]
    (Aγ : ι → L ℋ) (A : L ℋ) : Prop :=
  SOTTendstoAlong (ℋ := ℋ) atTop Aγ A

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Strong-operator convergence along a filter is stable under pointwise addition. -/
lemma SOTTendstoAlong.add {ι : Type*} {l : Filter ι}
    {Aγ Bγ : ι → L ℋ} {A B : L ℋ}
    (hA : SOTTendstoAlong (ℋ := ℋ) l Aγ A)
    (hB : SOTTendstoAlong (ℋ := ℋ) l Bγ B) :
    SOTTendstoAlong (ℋ := ℋ) l (fun i => Aγ i + Bγ i) (A + B) := by
  intro x
  simpa using (hA x).add (hB x)

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Strong-operator convergence along `atTop` is stable under pointwise addition. -/
lemma SOTTendsto_add {ι : Type*} [Preorder ι] [NeBot (atTop : Filter ι)]
    {Aγ Bγ : ι → L ℋ} {A B : L ℋ}
    (hA : SOTTendsto (ℋ := ℋ) Aγ A) (hB : SOTTendsto (ℋ := ℋ) Bγ B) :
    SOTTendsto (ℋ := ℋ) (fun i => Aγ i + Bγ i) (A + B) :=
  hA.add hB

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Strong-operator convergence along a filter is stable under scalar multiplication. -/
lemma SOTTendstoAlong.smul {ι : Type*} {l : Filter ι}
    {Aγ : ι → L ℋ} {A : L ℋ}
    (hA : SOTTendstoAlong (ℋ := ℋ) l Aγ A) (c : ℂ) :
    SOTTendstoAlong (ℋ := ℋ) l (fun i => c • Aγ i) (c • A) := by
  intro x
  simpa using (hA x).const_smul c

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Strong-operator convergence along `atTop` is stable under scalar multiplication. -/
lemma SOTTendsto_smul {ι : Type*} [Preorder ι] [NeBot (atTop : Filter ι)]
    {Aγ : ι → L ℋ} {A : L ℋ} (c : ℂ)
    (hA : SOTTendsto (ℋ := ℋ) Aγ A) :
    SOTTendsto (ℋ := ℋ) (fun i => c • Aγ i) (c • A) :=
  hA.smul c

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Strong-operator convergence along a filter is stable under pointwise subtraction. -/
lemma SOTTendstoAlong.sub {ι : Type*} {l : Filter ι}
    {Aγ Bγ : ι → L ℋ} {A B : L ℋ}
    (hA : SOTTendstoAlong (ℋ := ℋ) l Aγ A)
    (hB : SOTTendstoAlong (ℋ := ℋ) l Bγ B) :
    SOTTendstoAlong (ℋ := ℋ) l (fun i => Aγ i - Bγ i) (A - B) := by
  simpa [sub_eq_add_neg] using hA.add (hB.smul (-1))

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Strong-operator convergence along `atTop` is stable under pointwise subtraction. -/
lemma SOTTendsto_sub {ι : Type*} [Preorder ι] [NeBot (atTop : Filter ι)]
    {Aγ Bγ : ι → L ℋ} {A B : L ℋ}
    (hA : SOTTendsto (ℋ := ℋ) Aγ A) (hB : SOTTendsto (ℋ := ℋ) Bγ B) :
    SOTTendsto (ℋ := ℋ) (fun i => Aγ i - Bγ i) (A - B) :=
  hA.sub hB

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] in
private lemma exists_uniformBound_of_isCompact_of_spectrumSubset {ι : Type*}
    {Ω : Set ℂ} {Aγ : ι → L ℋ}
    (hΩ : IsCompact Ω) (hAγ : ∀ i, IsStarNormal (Aγ i))
    (hσAγ : ∀ i, spectrum ℂ (Aγ i) ⊆ Ω) :
    ∃ M > 0, ∀ i, ‖Aγ i‖ ≤ M := by
  obtain ⟨M, hMpos, hΩM⟩ := hΩ.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  refine ⟨M, hMpos, ?_⟩
  intro i
  rcases (IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum
      (𝕜 := ℂ) (A := L ℋ) (p := IsStarNormal) (a := Aγ i) (ha := hAγ i)).1 with
      ⟨z, hzσ, hzEq⟩
  have hzM : ‖z‖ ≤ M := by
    simpa [mem_closedBall_iff_norm] using hΩM (hσAγ i hzσ)
  simpa [hzEq] using hzM

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Multiplication preserves strong convergence along a filter when the left approximants are
uniformly bounded in operator norm. -/
lemma SOTTendstoAlong.mul {ι : Type*} {l : Filter ι}
    {Aγ Bγ : ι → L ℋ} {A B : L ℋ}
    (hA : SOTTendstoAlong (ℋ := ℋ) l Aγ A)
    (hB : SOTTendstoAlong (ℋ := ℋ) l Bγ B)
    (hbound : ∃ M > 0, ∀ i, ‖Aγ i‖ ≤ M) :
    SOTTendstoAlong (ℋ := ℋ) l (fun i => Aγ i * Bγ i) (A * B) := by
  rcases hbound with ⟨M, hMpos, hM⟩
  intro x
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hBx : Tendsto (fun i => Bγ i x - B x) l (𝓝 (0 : ℋ)) := by
    simpa using
      (hB x).sub (tendsto_const_nhds : Tendsto (fun _ : ι => B x) l (𝓝 (B x)))
  have hterm1 : Tendsto (fun i => Aγ i (Bγ i x - B x)) l (𝓝 (0 : ℋ)) := by
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
  have hterm2 : Tendsto (fun i => (Aγ i - A) (B x)) l (𝓝 (0 : ℋ)) := by
    simpa using
      (hA (B x)).sub (tendsto_const_nhds : Tendsto (fun _ : ι => A (B x)) l (𝓝 (A (B x))))
  have hsum := hterm1.add hterm2
  have hEq :
      (fun i => (Aγ i * Bγ i) x - (A * B) x) =
        fun i => Aγ i (Bγ i x - B x) + (Aγ i - A) (B x) := by
    funext i
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  simpa [hEq] using (tendsto_norm.comp hsum)

omit [CompleteSpace ℋ] [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
  [Nontrivial (L ℋ)] in
/-- Multiplication preserves strong convergence along `atTop` when the left approximants are
uniformly bounded in operator norm. -/
lemma SOTTendsto_mul_of_uniformBound {ι : Type*} [Preorder ι]
    [NeBot (atTop : Filter ι)] {Aγ Bγ : ι → L ℋ} {A B : L ℋ}
    (hA : SOTTendsto (ℋ := ℋ) Aγ A) (hB : SOTTendsto (ℋ := ℋ) Bγ B)
    (hbound : ∃ M > 0, ∀ i, ‖Aγ i‖ ≤ M) :
    SOTTendsto (ℋ := ℋ) (fun i => Aγ i * Bγ i) (A * B) :=
  hA.mul hB hbound

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
private lemma sottendstoAlong_star_of_normal {ι : Type*} {l : Filter ι}
    {Aγ : ι → L ℋ} {A : L ℋ}
    (hAγ : ∀ i, IsStarNormal (Aγ i)) (hA : IsStarNormal A)
    (hconv : SOTTendstoAlong (ℋ := ℋ) l Aγ A) :
    SOTTendstoAlong (ℋ := ℋ) l (fun i => star (Aγ i)) (star A) := by
  intro x
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let u : ι → ℋ := fun i => (star (Aγ i)) x
  let v : ℋ := (star A) x
  have hweak : ∀ y : ℋ,
      Tendsto (fun i => inner ℂ (u i) y) l (𝓝 (inner ℂ v y)) := by
    intro y
    simpa [u, v, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left] using
      (tendsto_const_nhds : Tendsto (fun _ : ι => x) l (𝓝 x)).inner (hconv y)
  have hnorm_u :
      Tendsto (fun i => ‖u i‖) l (𝓝 ‖v‖) := by
    have hnormA : Tendsto (fun i => ‖Aγ i x‖) l (𝓝 ‖A x‖) :=
      tendsto_norm.comp (hconv x)
    have hu_eq : ∀ i, ‖u i‖ = ‖Aγ i x‖ := by
      intro i
      simpa [u, ContinuousLinearMap.star_eq_adjoint] using
        (ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mp (hAγ i) x).symm
    have hv_eq : ‖v‖ = ‖A x‖ := by
      simpa [v, ContinuousLinearMap.star_eq_adjoint] using
        (ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mp hA x).symm
    have hnormU' : Tendsto (fun i => ‖u i‖) l (𝓝 ‖A x‖) := by
      refine hnormA.congr' ?_
      exact .of_forall fun i => (hu_eq i).symm
    simpa [hv_eq] using hnormU'
  have hinner_v : Tendsto (fun i => inner ℂ (u i) v) l (𝓝 (inner ℂ v v)) := hweak v
  have hsq :
      Tendsto (fun i => ‖u i - v‖ ^ 2) l (𝓝 (0 : ℝ)) := by
    have h1 : Tendsto (fun i => ‖u i‖ ^ 2) l (𝓝 (‖v‖ ^ 2)) := hnorm_u.pow 2
    have h2 : Tendsto (fun i => (2 : ℝ) * Complex.re (inner ℂ (u i) v)) l
        (𝓝 ((2 : ℝ) * Complex.re (inner ℂ v v))) :=
      tendsto_const_nhds.mul (Complex.continuous_re.continuousAt.tendsto.comp hinner_v)
    have h3 :
        Tendsto (fun i => ‖u i‖ ^ 2 - (2 : ℝ) * Complex.re (inner ℂ (u i) v) + ‖v‖ ^ 2)
          l (𝓝 (‖v‖ ^ 2 - (2 : ℝ) * Complex.re (inner ℂ v v) + ‖v‖ ^ 2)) :=
      h1.sub h2 |>.add tendsto_const_nhds
    have hsq' : Tendsto (fun i => ‖u i - v‖ ^ 2) l
        (𝓝 (‖v‖ ^ 2 - (2 : ℝ) * ((↑‖v‖ ^ 2 : ℂ).re) + ‖v‖ ^ 2)) := by
      convert h3 using 1
      · funext i
        exact norm_sub_sq (𝕜 := ℂ) (u i) v
      · simp
    have hv0 : ‖v‖ ^ 2 - (2 : ℝ) * ((↑‖v‖ ^ 2 : ℂ).re) + ‖v‖ ^ 2 = 0 := by
      have hreal : ((↑‖v‖ : ℂ) ^ 2).re = ‖v‖ ^ 2 := by
        simp [pow_two]
      nlinarith [hreal]
    simpa [hv0] using hsq'
  have hsqrt :
      Tendsto (fun i => Real.sqrt (‖u i - v‖ ^ 2)) l (𝓝 (Real.sqrt (0 : ℝ))) :=
    (Real.continuous_sqrt.tendsto 0).comp hsq
  have hnormsub : Tendsto (fun i => ‖u i - v‖) l (𝓝 (0 : ℝ)) := by
    simpa using hsqrt
  simpa [u, v] using hnormsub

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- The superset continuous functional calculus of a normal operator is norm-nonincreasing. -/
private theorem norm_cfcHomSuperset_le {Ω : Set ℂ} [CompactSpace Ω] {B : L ℋ}
    (hB : IsStarNormal B) (hσB : spectrum ℂ B ⊆ Ω) (g : C(Ω, ℂ)) :
    ‖cfcHomSuperset hB hσB g‖ ≤ ‖g‖ := by
  rw [cfcHomSuperset_apply]
  rw [isometry_cfcHom (R := ℂ) _ hB |>.norm_map_of_map_zero (map_zero (cfcHom hB))]
  rw [ContinuousMap.norm_le _ (norm_nonneg _)]
  intro z
  exact ContinuousMap.norm_coe_le_norm g ⟨z, hσB z.2⟩

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- The superset continuous functional calculus of a normal operator, applied to a vector,
is norm-nonincreasing in the function. -/
private theorem norm_cfcHomSuperset_sub_apply_le {Ω : Set ℂ} [CompactSpace Ω] {B : L ℋ}
    (hB : IsStarNormal B) (hσB : spectrum ℂ B ⊆ Ω) (g p : C(Ω, ℂ)) (x : ℋ) :
    ‖cfcHomSuperset hB hσB g x - cfcHomSuperset hB hσB p x‖ ≤ ‖g - p‖ * ‖x‖ := by
  calc
    ‖cfcHomSuperset hB hσB g x - cfcHomSuperset hB hσB p x‖
        = ‖(cfcHomSuperset hB hσB (g - p)) x‖ := by
          rw [map_sub]
          rfl
    _ ≤ ‖cfcHomSuperset hB hσB (g - p)‖ * ‖x‖ := (cfcHomSuperset hB hσB (g - p)).le_opNorm x
    _ ≤ ‖g - p‖ * ‖x‖ := by gcongr; exact norm_cfcHomSuperset_le (ℋ := ℋ) hB hσB (g - p)

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)] in
/-- The approximation step of `SOTTendstoAlong.cfcNormal`: strong convergence of the superset
functional calculus passes from functions frequently near `g` to `g` itself. -/
private theorem sotTendstoAlong_cfcHomSuperset_of_frequently {ι : Type*} (l : Filter ι)
    {Ω : Set ℂ} [CompactSpace Ω] {A : L ℋ} {Aγ : ι → L ℋ}
    (hAγ : ∀ i, IsStarNormal (Aγ i)) (hA : IsStarNormal A)
    (hσAγ : ∀ i, spectrum ℂ (Aγ i) ⊆ Ω) (hσA : spectrum ℂ A ⊆ Ω) (g : C(Ω, ℂ))
    (hg : ∃ᶠ p in 𝓝 g,
      SOTTendstoAlong (ℋ := ℋ) l (fun i => cfcHomSuperset (hAγ i) (hσAγ i) p)
        (cfcHomSuperset hA hσA p)) :
    SOTTendstoAlong (ℋ := ℋ) l (fun i => cfcHomSuperset (hAγ i) (hσAγ i) g)
      (cfcHomSuperset hA hσA g) := by
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
  /- Step 4: Control the approximation error, uniformly for the varying operators Aγ
  and at the limiting operator A. -/
  have hfac : ‖g - p‖ * ‖x‖ ≤ ε / 3 := by
    have hxR : ‖x‖ ≤ R := by
      dsimp [R]
      exact le_max_left _ _
    calc
      ‖g - p‖ * ‖x‖ ≤ (ε / (3 * R)) * R := by gcongr
      _ = ε / 3 := by field_simp
  have hsource :
      ∀ i, ‖cfcHomSuperset (hAγ i) (hσAγ i) g x -
          cfcHomSuperset (hAγ i) (hσAγ i) p x‖ ≤ ε / 3 := fun i =>
    (norm_cfcHomSuperset_sub_apply_le (ℋ := ℋ) (hAγ i) (hσAγ i) g p x).trans hfac
  /- Step 5: The same bound at the limiting operator A. -/
  have htarget :
      ‖cfcHomSuperset hA hσA g x - cfcHomSuperset hA hσA p x‖ ≤ ε / 3 :=
    (norm_cfcHomSuperset_sub_apply_le (ℋ := ℋ) hA hσA g p x).trans hfac
  have hpconv' := Metric.tendsto_nhds.mp (hpconv x) (ε / 3) (by positivity)
  /- Step 6: Combine both approximation bounds with polynomial convergence. -/
  filter_upwards [hpconv'] with i hi
  have htri :
      ‖cfcHomSuperset (hAγ i) (hσAγ i) g x - cfcHomSuperset hA hσA g x‖
        ≤
          ‖cfcHomSuperset (hAγ i) (hσAγ i) g x -
              cfcHomSuperset (hAγ i) (hσAγ i) p x‖ +
          ‖cfcHomSuperset (hAγ i) (hσAγ i) p x - cfcHomSuperset hA hσA p x‖ +
          ‖cfcHomSuperset hA hσA p x - cfcHomSuperset hA hσA g x‖ := by
    calc
      ‖cfcHomSuperset (hAγ i) (hσAγ i) g x - cfcHomSuperset hA hσA g x‖
        ≤
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
      ‖cfcHomSuperset (hAγ i) (hσAγ i) p x - cfcHomSuperset hA hσA p x‖ < ε / 3 := by
    simpa only [dist_eq_norm] using hi
  have hfinal :
      ‖cfcHomSuperset (hAγ i) (hσAγ i) g x - cfcHomSuperset hA hσA g x‖ < ε := by
    linarith [htri, hsource i, hi', htarget']
  simpa only [dist_eq_norm] using hfinal

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] in
/-- Strong-operator convergence is preserved by normal continuous functional calculus.
Source: Hiai–Yanagi, Lemma 5.1.4. -/
protected theorem SOTTendstoAlong.cfcNormal {ι : Type*} (l : Filter ι) {Ω : Set ℂ}
    {f : ℂ → ℂ} {A : L ℋ} {Aγ : ι → L ℋ}
    (hΩ : IsCompact Ω) (hAγ : ∀ i, IsStarNormal (Aγ i))
    (hA : IsStarNormal A) (hσAγ : ∀ i, spectrum ℂ (Aγ i) ⊆ Ω)
    (hσA : spectrum ℂ A ⊆ Ω) (hf : ContinuousOn f Ω)
    (hconv : SOTTendstoAlong (ℋ := ℋ) l Aγ A) :
    SOTTendstoAlong (ℋ := ℋ) l (fun i => cfcNormal (ℋ := ℋ) f (Aγ i))
      (cfcNormal (ℋ := ℋ) f A) := by
  /- Step 1: Restrict f to the common compact spectral set so CFC can be treated inside C(Ω). -/
  let fΩ : C(Ω, ℂ) := ⟨_, hf.restrict⟩
  haveI : CompactSpace Ω := by
    rwa [isCompact_iff_compactSpace] at hΩ
  have hboundAγ := exists_uniformBound_of_isCompact_of_spectrumSubset (ℋ := ℋ) hΩ hAγ hσAγ
  /- Step 2: Prove SOT convergence on the compact coordinate algebra. -/
  have hP : ∀ g : C(Ω, ℂ),
      SOTTendstoAlong (ℋ := ℋ) l (fun i => cfcHomSuperset (hAγ i) (hσAγ i) g)
        (cfcHomSuperset hA hσA g) := by
    intro g
    induction g using ContinuousMap.induction_on_of_compact with
    | const c =>
        intro x
        have : ContinuousMap.const Ω c = algebraMap ℂ C(Ω, ℂ) c := rfl
        simpa only [this, AlgHomClass.commutes] using tendsto_const_nhds
    | id =>
        intro x
        simpa only [cfcHomSuperset_id] using hconv x
    | star_id =>
        intro x
        simpa only [map_star, cfcHomSuperset_id] using
          sottendstoAlong_star_of_normal (ℋ := ℋ) hAγ hA hconv x
    | add g h hg hh =>
        simpa [map_add] using hg.add hh
    | mul g h hg hh =>
        have hbound_g : ∃ M > 0, ∀ i, ‖cfcHomSuperset (hAγ i) (hσAγ i) g‖ ≤ M :=
          ⟨‖g‖ + 1, by positivity, fun i =>
            (norm_cfcHomSuperset_le (ℋ := ℋ) (hAγ i) (hσAγ i) g).trans (by linarith)⟩
        simpa [map_mul] using hg.mul hh hbound_g
    /- Step 3: Extend by splitting source, polynomial, and target errors (Steps 4–6 are in
    `sotTendstoAlong_cfcHomSuperset_of_frequently`). -/
    | frequently g hg =>
        exact sotTendstoAlong_cfcHomSuperset_of_frequently (ℋ := ℋ) l hAγ hA hσAγ hσA g hg
  /- Step 7: Identify cfcHomSuperset convergence with normal CFC convergence. -/
  intro x
  have hx := hP fΩ x
  have hx' :
      Tendsto (fun i => cfcNormal (ℋ := ℋ) f (Aγ i) x) l
        (𝓝 (cfcHomSuperset hA hσA fΩ x)) := by
    refine hx.congr' ?_
    exact .of_forall fun i => by
      have hcfc : cfcHomSuperset (hAγ i) (hσAγ i) fΩ = cfc f (Aγ i) := by
        dsimp [fΩ]
        symm
        simpa [cfcHomSuperset_apply, Set.restrict_apply] using
          (cfc_apply (f := f) (a := Aγ i) (ha := hAγ i) (hf := hf.mono (hσAγ i)))
      simpa [cfcNormal] using congrArg (fun T => T x) hcfc
  have hcfcA : cfcHomSuperset hA hσA fΩ = cfcNormal (ℋ := ℋ) f A := by
    dsimp [fΩ, cfcNormal]
    symm
    simpa [cfcHomSuperset_apply, Set.restrict_apply] using
      (cfc_apply (f := f) (a := A) (ha := hA) (hf := hf.mono hσA))
  simpa [hcfcA] using hx'

omit [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] in
/-- Strong-operator convergence along a nondegenerate `atTop` filter is preserved by normal
continuous functional calculus.  This is the directed-net wrapper around
`SOTTendstoAlong.cfcNormal`. -/
protected theorem SOTTendsto.cfcNormal {ι : Type*} [Preorder ι]
    [NeBot (atTop : Filter ι)] {Ω : Set ℂ} {f : ℂ → ℂ} {A : L ℋ} {Aγ : ι → L ℋ}
    (hΩ : IsCompact Ω) (hAγ : ∀ i, IsStarNormal (Aγ i))
    (hA : IsStarNormal A) (hσAγ : ∀ i, spectrum ℂ (Aγ i) ⊆ Ω)
    (hσA : spectrum ℂ A ⊆ Ω) (hf : ContinuousOn f Ω)
    (hconv : SOTTendsto (ℋ := ℋ) Aγ A) :
    SOTTendsto (ℋ := ℋ) (fun i => cfcNormal (ℋ := ℋ) f (Aγ i))
      (cfcNormal (ℋ := ℋ) f A) :=
  SOTTendstoAlong.cfcNormal (ℋ := ℋ) atTop hΩ hAγ hA hσAγ hσA hf hconv

end NormalCFC514

end HansenPedersen
