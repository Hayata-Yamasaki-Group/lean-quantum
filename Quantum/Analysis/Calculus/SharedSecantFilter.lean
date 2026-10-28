import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Shared punctured-secant filter facts

This module contains the route-neutral filter lemmas shared by the finite-order
and operator-monotone secant arguments.
-/

namespace Quantum.TraceInequality.Loewner

noncomputable section

open Filter

open scoped Topology

/--
Shared form of `chapter20_punctured_metric_ball_mem_nhdsWithin_Ioo` and
`chapter3_punctured_metric_ball_mem_nhdsWithin_Ioo`.
-/
lemma punctured_metric_ball_mem_nhdsWithin_Ioo {x δ : ℝ} (hδ : 0 < δ) :
    ({y : ℝ | y ∈ Set.Ioo (-1 : ℝ) 1 ∧ y ≠ x ∧ dist y x < δ} : Set ℝ) ∈
      𝓝[Set.Ioo (-1 : ℝ) 1 \ {x}] x := by
  have hball : Metric.ball x δ ∈ 𝓝 x := Metric.ball_mem_nhds x hδ
  have hmem :
      (Set.Ioo (-1 : ℝ) 1 \ {x}) ∩ Metric.ball x δ ∈
        𝓝[Set.Ioo (-1 : ℝ) 1 \ {x}] x :=
    inter_mem_nhdsWithin (Set.Ioo (-1 : ℝ) 1 \ {x}) hball
  refine Filter.mem_of_superset hmem ?_
  intro y hy
  rcases hy with ⟨hyS, hyball⟩
  exact ⟨hyS.1, by simpa using hyS.2, by simpa [Metric.mem_ball, dist_comm] using hyball⟩

/--
Shared form of `chapter20_secant_localOscillation_of_crossSecants` and
`chapter3_secant_localOscillation_of_crossSecants`.
-/
theorem secant_localOscillation_of_crossSecants
    {f : ℝ → ℝ} {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hcross :
      ∀ η > 0, ∃ δ > 0,
        ∀ {y z : ℝ},
          y ∈ Set.Ioo (-1 : ℝ) x →
          z ∈ Set.Ioo x (1 : ℝ) →
          dist y x < δ →
          dist z x < δ →
            dist (slope f x y) (slope f x z) < η) :
    ∀ ε > 0,
      ∃ U ∈ 𝓝[Set.Ioo (-1 : ℝ) 1 \ {x}] x,
        ∀ y ∈ U, ∀ z ∈ U,
          dist (slope f x y) (slope f x z) < ε := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases hcross (ε / 2) hε2 with ⟨δc, hδc, hcrossδ⟩
  let ρ : ℝ := min δc (min ((x + 1) / 2) ((1 - x) / 2))
  have hρ_pos : 0 < ρ := by
    have hxleft : 0 < (x + 1) / 2 := by linarith [hx.1]
    have hxright : 0 < (1 - x) / 2 := by linarith [hx.2]
    exact lt_min hδc (lt_min hxleft hxright)
  have hρ_le_δc : ρ ≤ δc := min_le_left _ _
  have hρ_le_leftGap : ρ ≤ (x + 1) / 2 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ_le_rightGap : ρ ≤ (1 - x) / 2 :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  let l : ℝ := x - ρ / 2
  let r : ℝ := x + ρ / 2
  have hl_lt_x : l < x := by
    dsimp [l]
    linarith
  have hx_lt_r : x < r := by
    dsimp [r]
    linarith
  have hneg_one_lt_l : -1 < l := by
    dsimp [l]
    linarith
  have hr_lt_one : r < 1 := by
    dsimp [r]
    linarith
  have hlI : l ∈ Set.Ioo (-1 : ℝ) x := ⟨hneg_one_lt_l, hl_lt_x⟩
  have hrI : r ∈ Set.Ioo x (1 : ℝ) := ⟨hx_lt_r, hr_lt_one⟩
  have hdist_l_ρ : dist l x < ρ := by
    rw [Real.dist_eq]
    have hl_sub : l - x = -ρ / 2 := by
      dsimp [l]
      ring
    rw [hl_sub]
    have hnonpos : -ρ / 2 ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos]
    linarith
  have hdist_r_ρ : dist r x < ρ := by
    rw [Real.dist_eq]
    have hr_sub : r - x = ρ / 2 := by
      dsimp [r]
      ring
    rw [hr_sub]
    have hnonneg : 0 ≤ ρ / 2 := by linarith
    rw [abs_of_nonneg hnonneg]
    linarith
  have hdist_l_δc : dist l x < δc := lt_of_lt_of_le hdist_l_ρ hρ_le_δc
  have hdist_r_δc : dist r x < δc := lt_of_lt_of_le hdist_r_ρ hρ_le_δc
  let U : Set ℝ := {y : ℝ | y ∈ Set.Ioo (-1 : ℝ) 1 ∧ y ≠ x ∧ dist y x < ρ}
  refine ⟨U, punctured_metric_ball_mem_nhdsWithin_Ioo hρ_pos, ?_⟩
  intro y hy z hz
  rcases hy with ⟨hyI, hyne, hydistρ⟩
  rcases hz with ⟨hzI, hzne, hzdistρ⟩
  have hydistδ : dist y x < δc := lt_of_lt_of_le hydistρ hρ_le_δc
  have hzdistδ : dist z x < δc := lt_of_lt_of_le hzdistρ hρ_le_δc
  rcases lt_or_gt_of_ne hyne with hylt | hygt
  · have hyL : y ∈ Set.Ioo (-1 : ℝ) x := ⟨hyI.1, hylt⟩
    rcases lt_or_gt_of_ne hzne with hzlt | hzgt
    · have hzL : z ∈ Set.Ioo (-1 : ℝ) x := ⟨hzI.1, hzlt⟩
      have hy_anchor :
          dist (slope f x y) (slope f x r) < ε / 2 :=
        hcrossδ hyL hrI hydistδ hdist_r_δc
      have hz_anchor :
          dist (slope f x z) (slope f x r) < ε / 2 :=
        hcrossδ hzL hrI hzdistδ hdist_r_δc
      calc
        dist (slope f x y) (slope f x z)
            ≤ dist (slope f x y) (slope f x r) +
                dist (slope f x r) (slope f x z) :=
          dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by
          exact add_lt_add hy_anchor (by simpa [dist_comm] using hz_anchor)
        _ = ε := by ring
    · have hzR : z ∈ Set.Ioo x (1 : ℝ) := ⟨hzgt, hzI.2⟩
      have h := hcrossδ hyL hzR hydistδ hzdistδ
      linarith
  · have hyR : y ∈ Set.Ioo x (1 : ℝ) := ⟨hygt, hyI.2⟩
    rcases lt_or_gt_of_ne hzne with hzlt | hzgt
    · have hzL : z ∈ Set.Ioo (-1 : ℝ) x := ⟨hzI.1, hzlt⟩
      have h := hcrossδ hzL hyR hzdistδ hydistδ
      simpa [dist_comm] using (lt_trans h (by linarith : ε / 2 < ε))
    · have hzR : z ∈ Set.Ioo x (1 : ℝ) := ⟨hzgt, hzI.2⟩
      have hy_anchor :
          dist (slope f x l) (slope f x y) < ε / 2 :=
        hcrossδ hlI hyR hdist_l_δc hydistδ
      have hz_anchor :
          dist (slope f x l) (slope f x z) < ε / 2 :=
        hcrossδ hlI hzR hdist_l_δc hzdistδ
      calc
        dist (slope f x y) (slope f x z)
            ≤ dist (slope f x y) (slope f x l) +
                dist (slope f x l) (slope f x z) :=
          dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by
          exact add_lt_add (by simpa [dist_comm] using hy_anchor) hz_anchor
        _ = ε := by ring

/--
Shared form of `chapter20_secant_punctured_Ioo_neBot` and
`chapter3_secant_punctured_Ioo_neBot`.
-/
lemma secant_punctured_Ioo_neBot {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Filter.NeBot (𝓝[Set.Ioo (-1 : ℝ) 1 \ {x}] x) := by
  have hright : Filter.NeBot (𝓝[Set.Ioo x (1 : ℝ)] x) :=
    left_nhdsWithin_Ioo_neBot hx.2
  have hsubset : Set.Ioo x (1 : ℝ) ⊆ Set.Ioo (-1 : ℝ) 1 \ {x} := by
    intro y hy
    exact ⟨⟨lt_trans hx.1 hy.1, hy.2⟩, hy.1.ne'⟩
  exact Filter.neBot_of_le (nhdsWithin_mono x hsubset)

/--
Shared form of `chapter20_secant_tendsto_of_localOscillation` and
`chapter3_secant_tendsto_of_localOscillation`.
-/
lemma secant_tendsto_of_localOscillation
    {f : ℝ → ℝ} {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hloc :
      ∀ ε > 0,
        ∃ U ∈ 𝓝[Set.Ioo (-1 : ℝ) 1 \ {x}] x,
          ∀ y ∈ U, ∀ z ∈ U,
            dist (slope f x y) (slope f x z) < ε) :
    ∃ D : ℝ,
      Filter.Tendsto (slope f x)
        (𝓝[Set.Ioo (-1 : ℝ) 1 \ {x}] x) (𝓝 D) := by
  let F : Filter ℝ := 𝓝[Set.Ioo (-1 : ℝ) 1 \ {x}] x
  have hne : Filter.NeBot F := secant_punctured_Ioo_neBot hx
  have hcauchy : Cauchy (Filter.map (slope f x) F) := by
    refine Metric.cauchy_iff.2 ⟨?_, ?_⟩
    · exact hne.map (slope f x)
    · intro ε hε
      rcases hloc ε hε with ⟨U, hU, hosc⟩
      refine ⟨(slope f x) '' U, Filter.image_mem_map hU, ?_⟩
      intro a ha b hb
      rcases ha with ⟨y, hy, rfl⟩
      rcases hb with ⟨z, hz, rfl⟩
      exact hosc y hy z hz
  haveI : Filter.NeBot F := hne
  exact cauchy_map_iff_exists_tendsto.mp hcauchy

end

end Quantum.TraceInequality.Loewner
