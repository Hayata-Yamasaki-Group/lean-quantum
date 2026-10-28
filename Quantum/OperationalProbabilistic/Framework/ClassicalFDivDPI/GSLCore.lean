/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.ClassicalFDivergence.GSLCore
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open Filter Set
open scoped ENNReal NNReal Topology BigOperators

/-!
# Laws of the closed perspective of a classical f-divergence

The closed perspective of an `FDivGenerator` is positively homogeneous and subadditive,
including the three boundary regimes `(0,0)`, `(0,b)`, and `(a,0)`, proved by positive
regularization (`eps`).  Finite subadditivity gives nonnegativity of the raw `EReal` sum
(`classicalFDivSum_nonnegative`).  Cf. Gour, *Resources of the Quantum World*
(arXiv:2402.05474v2), Definition 5.2.
-/

namespace OPT

noncomputable section


private def eps (n : ℕ) : ℝ≥0 :=
  ⟨(((n + 1 : ℕ) : ℝ))⁻¹, by positivity⟩

@[simp] private theorem eps_coe (n : ℕ) :
    (eps n : ℝ) = (((n + 1 : ℕ) : ℝ))⁻¹ := rfl

private theorem eps_pos (n : ℕ) : 0 < eps n := by
  change 0 < (((n + 1 : ℕ) : ℝ))⁻¹
  positivity

private theorem tendsto_eps_gt :
    Tendsto (fun n : ℕ => (eps n : ℝ)) atTop (𝓝[>] 0) := by
  have hcast : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  simpa only [eps_coe] using tendsto_inv_atTop_nhdsGT_zero.comp hcast

private theorem tendsto_eps :
    Tendsto (fun n : ℕ => (eps n : ℝ)) atTop (𝓝 0) :=
  tendsto_eps_gt.mono_right inf_le_left

private theorem add_eps_ne_zero (a : ℝ≥0) (n : ℕ) : a + eps n ≠ 0 :=
  ne_of_gt (add_pos_of_nonneg_of_pos a.2 (eps_pos n))

private theorem tendsto_ratio_zero_left (b : ℝ≥0) (hb : b ≠ 0) :
    Tendsto (fun n : ℕ => (eps n : ℝ) / ((b + eps n : ℝ≥0) : ℝ))
      atTop (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    have hden : Tendsto (fun n : ℕ => (b : ℝ) + (eps n : ℝ))
        atTop (𝓝 ((b : ℝ) + 0)) := tendsto_const_nhds.add tendsto_eps
    simpa only [NNReal.coe_add, eps_coe, zero_div] using
      tendsto_eps.div hden (by simpa using hbR)
  · exact Filter.Eventually.of_forall fun n => by
      change 0 < (eps n : ℝ) / ((b : ℝ) + (eps n : ℝ))
      apply div_pos (by exact_mod_cast eps_pos n)
      exact add_pos_of_pos_of_nonneg
        (by exact_mod_cast (pos_iff_ne_zero.mpr hb)) (by exact_mod_cast (eps n).2)

private theorem tendsto_ratio_interior (a b : ℝ≥0) (hb : b ≠ 0) :
    Tendsto (fun n : ℕ => ((a + eps n : ℝ≥0) : ℝ) /
      ((b + eps n : ℝ≥0) : ℝ)) atTop (𝓝 (((a : ℝ) / (b : ℝ)))) := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hnum : Tendsto (fun n : ℕ => (a : ℝ) + (eps n : ℝ))
      atTop (𝓝 ((a : ℝ) + 0)) := tendsto_const_nhds.add tendsto_eps
  have hden : Tendsto (fun n : ℕ => (b : ℝ) + (eps n : ℝ))
      atTop (𝓝 ((b : ℝ) + 0)) := tendsto_const_nhds.add tendsto_eps
  simpa only [NNReal.coe_add, eps_coe, Pi.div_apply, add_zero] using
    hnum.div hden (by simpa using hbR)

private theorem tendsto_ratio_recession (a : ℝ≥0) (ha : a ≠ 0) :
    Tendsto (fun n : ℕ => ((a + eps n : ℝ≥0) : ℝ) / (eps n : ℝ))
      atTop atTop := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr ha)
  have hcast : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hmain : Tendsto (fun n : ℕ => (a : ℝ) * (((n + 1 : ℕ) : ℝ)))
      atTop atTop := hcast.const_mul_atTop haR
  apply (hmain.atTop_add tendsto_const_nhds).congr'
  exact Filter.Eventually.of_forall fun n => by
    change (a : ℝ) * (((n + 1 : ℕ) : ℝ)) + 1 =
      ((a : ℝ) + (((n + 1 : ℕ) : ℝ))⁻¹) / (((n + 1 : ℕ) : ℝ))⁻¹
    field_simp

private theorem tendsto_closedPerspective_add_eps
    (g : FDivGenerator) (a b : ℝ≥0) :
    Tendsto (fun n : ℕ => closedPerspective g (a + eps n) (b + eps n))
      atTop (𝓝 (closedPerspective g a b)) := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      rw [closedPerspective_zero_zero]
      apply tendsto_const_nhds.congr'
      exact Filter.Eventually.of_forall fun n => by
        change (0 : EReal) = closedPerspective g (0 + eps n) (0 + eps n)
        symm
        rw [closedPerspective_of_ne_zero g _ _
          (add_eps_ne_zero 0 n) (add_eps_ne_zero 0 n)]
        simp only [zero_add]
        have he : (eps n : ℝ) ≠ 0 := by exact_mod_cast (eps_pos n).ne'
        rw [div_self he, g.map_one, mul_zero, EReal.coe_zero]
    · have hratio := tendsto_ratio_zero_left b hb
      have hgen := g.tendsto_zeroValue.comp hratio
      have hcoefR : Tendsto (fun n : ℕ => ((b + eps n : ℝ≥0) : ℝ))
          atTop (𝓝 (b : ℝ)) := by
        have hc : Tendsto (fun _ : ℕ => (b : ℝ)) atTop (𝓝 (b : ℝ)) :=
          tendsto_const_nhds
        simpa only [NNReal.coe_add, add_zero] using hc.add tendsto_eps
      have hcoef : Tendsto (fun n : ℕ =>
          ((((b + eps n : ℝ≥0) : ℝ)) : EReal)) atTop (𝓝 ((b : ℝ) : EReal)) :=
        EReal.tendsto_coe.mpr hcoefR
      have hbR0 : ((b : ℝ) : EReal) ≠ 0 := by
        simp only [ne_eq, EReal.coe_eq_zero]
        exact_mod_cast hb
      have hmul := EReal.Tendsto.mul hcoef hgen
        (Or.inl hbR0) (Or.inl hbR0)
        (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
      rw [closedPerspective_zero_left g b hb]
      apply hmul.congr'
      exact Filter.Eventually.of_forall fun n => by
        simp only [Function.comp_apply]
        symm
        rw [closedPerspective_of_ne_zero g _ _
          (add_eps_ne_zero 0 n) (add_eps_ne_zero b n)]
        simp only [zero_add, ← EReal.coe_mul, NNReal.coe_add]
  · by_cases hb : b = 0
    · subst b
      have hratio := tendsto_ratio_recession a ha
      have hgen := g.tendsto_recessionSlope.comp hratio
      have hcoefR : Tendsto (fun n : ℕ => ((a + eps n : ℝ≥0) : ℝ))
          atTop (𝓝 (a : ℝ)) := by
        have hc : Tendsto (fun _ : ℕ => (a : ℝ)) atTop (𝓝 (a : ℝ)) :=
          tendsto_const_nhds
        simpa only [NNReal.coe_add, add_zero] using hc.add tendsto_eps
      have hcoef : Tendsto (fun n : ℕ =>
          ((((a + eps n : ℝ≥0) : ℝ)) : EReal)) atTop (𝓝 ((a : ℝ) : EReal)) :=
        EReal.tendsto_coe.mpr hcoefR
      have haR0 : ((a : ℝ) : EReal) ≠ 0 := by
        simp only [ne_eq, EReal.coe_eq_zero]
        exact_mod_cast ha
      have hmul := EReal.Tendsto.mul hcoef hgen
        (Or.inl haR0) (Or.inl haR0)
        (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
      rw [closedPerspective_zero_right g a ha]
      apply hmul.congr'
      exact Filter.Eventually.of_forall fun n => by
        simp only [Function.comp_apply]
        symm
        rw [closedPerspective_of_ne_zero g _ _
          (add_eps_ne_zero a n) (add_eps_ne_zero 0 n)]
        simp only [zero_add, ← EReal.coe_mul, EReal.coe_eq_coe_iff,
          NNReal.coe_add]
        have he : (eps n : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast eps_pos n)
        field_simp
    · have hratio := tendsto_ratio_interior a b hb
      have hratioPos : 0 < (a : ℝ) / (b : ℝ) := by
        exact div_pos (by exact_mod_cast pos_iff_ne_zero.mpr ha)
          (by exact_mod_cast pos_iff_ne_zero.mpr hb)
      have hratioWithin : Tendsto (fun n : ℕ =>
          ((a + eps n : ℝ≥0) : ℝ) / ((b + eps n : ℝ≥0) : ℝ))
          atTop (𝓝[Set.Ioi 0] ((a : ℝ) / (b : ℝ))) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hratio, Filter.Eventually.of_forall fun n => ?_⟩
        change 0 < ((a : ℝ) + (eps n : ℝ)) / ((b : ℝ) + (eps n : ℝ))
        positivity
      have hfcont : ContinuousWithinAt g.f (Ioi 0) ((a : ℝ) / (b : ℝ)) :=
        (g.convexOn_pos.continuousOn isOpen_Ioi) _ hratioPos
      have hgenR : Tendsto (fun n : ℕ => g.f
          (((a + eps n : ℝ≥0) : ℝ) / ((b + eps n : ℝ≥0) : ℝ)))
          atTop (𝓝 (g.f ((a : ℝ) / (b : ℝ)))) :=
        hfcont.tendsto.comp hratioWithin
      have hcoefR : Tendsto (fun n : ℕ => ((b + eps n : ℝ≥0) : ℝ))
          atTop (𝓝 (b : ℝ)) := by
        have hc : Tendsto (fun _ : ℕ => (b : ℝ)) atTop (𝓝 (b : ℝ)) :=
          tendsto_const_nhds
        simpa only [NNReal.coe_add, add_zero] using hc.add tendsto_eps
      have hprodR := hcoefR.mul hgenR
      have hprod : Tendsto (fun n : ℕ =>
          ((((b + eps n : ℝ≥0) : ℝ) * g.f
            (((a + eps n : ℝ≥0) : ℝ) /
              ((b + eps n : ℝ≥0) : ℝ)) : ℝ) : EReal))
          atTop (𝓝 ((((b : ℝ) * g.f ((a : ℝ) / (b : ℝ)) : ℝ) : EReal))) :=
        EReal.tendsto_coe.mpr hprodR
      rw [closedPerspective_of_ne_zero g a b ha hb]
      apply hprod.congr'
      exact Filter.Eventually.of_forall fun n => by
        change ((((b + eps n : ℝ≥0) : ℝ) * g.f
            (((a + eps n : ℝ≥0) : ℝ) /
              ((b + eps n : ℝ≥0) : ℝ)) : ℝ) : EReal) =
          closedPerspective g (a + eps n) (b + eps n)
        symm
        rw [closedPerspective_of_ne_zero g _ _
          (add_eps_ne_zero a n) (add_eps_ne_zero b n)]

private theorem closedPerspective_add_le_of_ne_zero
    (g : FDivGenerator) (a₁ b₁ a₂ b₂ : ℝ≥0)
    (ha₁ : a₁ ≠ 0) (hb₁ : b₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hb₂ : b₂ ≠ 0) :
    closedPerspective g (a₁ + a₂) (b₁ + b₂) ≤
      closedPerspective g a₁ b₁ + closedPerspective g a₂ b₂ := by
  have ha12 : a₁ + a₂ ≠ 0 := add_ne_zero.mpr (Or.inl ha₁)
  have hb12 : b₁ + b₂ ≠ 0 := add_ne_zero.mpr (Or.inl hb₁)
  rw [closedPerspective_of_ne_zero g _ _ ha12 hb12,
    closedPerspective_of_ne_zero g _ _ ha₁ hb₁,
    closedPerspective_of_ne_zero g _ _ ha₂ hb₂, ← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  let A₁ : ℝ := a₁
  let B₁ : ℝ := b₁
  let A₂ : ℝ := a₂
  let B₂ : ℝ := b₂
  have hA₁ : 0 < A₁ := by exact_mod_cast pos_iff_ne_zero.mpr ha₁
  have hB₁ : 0 < B₁ := by exact_mod_cast pos_iff_ne_zero.mpr hb₁
  have hA₂ : 0 < A₂ := by exact_mod_cast pos_iff_ne_zero.mpr ha₂
  have hB₂ : 0 < B₂ := by exact_mod_cast pos_iff_ne_zero.mpr hb₂
  have hB : 0 < B₁ + B₂ := add_pos hB₁ hB₂
  have hw₁ : 0 ≤ B₁ / (B₁ + B₂) := div_nonneg hB₁.le hB.le
  have hw₂ : 0 ≤ B₂ / (B₁ + B₂) := div_nonneg hB₂.le hB.le
  have hwsum : B₁ / (B₁ + B₂) + B₂ / (B₁ + B₂) = 1 := by
    rw [← add_div]
    exact div_self hB.ne'
  have harg : B₁ / (B₁ + B₂) * (A₁ / B₁) +
      B₂ / (B₁ + B₂) * (A₂ / B₂) =
        (A₁ + A₂) / (B₁ + B₂) := by
    field_simp [hB₁.ne', hB₂.ne', hB.ne']
  have hj := g.convexOn_pos.2
    (show A₁ / B₁ ∈ Ioi 0 from div_pos hA₁ hB₁)
    (show A₂ / B₂ ∈ Ioi 0 from div_pos hA₂ hB₂)
    hw₁ hw₂ hwsum
  simp only [smul_eq_mul] at hj
  rw [harg] at hj
  have hmul := mul_le_mul_of_nonneg_left hj hB.le
  change (B₁ + B₂) * g.f ((A₁ + A₂) / (B₁ + B₂)) ≤
    B₁ * g.f (A₁ / B₁) + B₂ * g.f (A₂ / B₂)
  calc
    (B₁ + B₂) * g.f ((A₁ + A₂) / (B₁ + B₂)) ≤
        (B₁ + B₂) * (B₁ / (B₁ + B₂) * g.f (A₁ / B₁) +
          B₂ / (B₁ + B₂) * g.f (A₂ / B₂)) := hmul
    _ = B₁ * g.f (A₁ / B₁) + B₂ * g.f (A₂ / B₂) := by
      field_simp [hB.ne']

private theorem halfIndex_tendsto :
    Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  exact ⟨b, fun a ha => by omega⟩

private theorem eps_half_add (n : ℕ) :
    eps (2 * n + 1) + eps (2 * n + 1) = eps n := by
  apply NNReal.eq
  simp only [NNReal.coe_add, eps_coe, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  field_simp
  ring

/-- Positive homogeneity of the closed perspective, including zero masses
and extended endpoint values.  It is used with kernel coefficients in the
finite Jensen proof of Gour, Theorem 5.1. -/
theorem closedPerspective_smul (g : FDivGenerator) (c a b : ℝ≥0) :
    closedPerspective g (c * a) (c * b) =
      (((c : ℝ) : EReal)) * closedPerspective g a b := by
  by_cases hc : c = 0
  · subst c
    simp
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      simp
    · have hcb : c * b ≠ 0 := mul_ne_zero hc hb
      simp only [mul_zero]
      rw [closedPerspective_zero_left g _ hcb,
        closedPerspective_zero_left g b hb]
      simp only [NNReal.coe_mul]
      rw [EReal.coe_mul, mul_assoc]
  · by_cases hb : b = 0
    · subst b
      have hca : c * a ≠ 0 := mul_ne_zero hc ha
      rw [mul_zero, closedPerspective_zero_right g _ hca,
        closedPerspective_zero_right g a ha]
      simp only [NNReal.coe_mul]
      rw [EReal.coe_mul, mul_assoc]
    · have hca : c * a ≠ 0 := mul_ne_zero hc ha
      have hcb : c * b ≠ 0 := mul_ne_zero hc hb
      rw [closedPerspective_of_ne_zero g _ _ hca hcb,
        closedPerspective_of_ne_zero g _ _ ha hb]
      simp only [NNReal.coe_mul, ← EReal.coe_mul, EReal.coe_eq_coe_iff]
      have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
      field_simp

/-- Binary Jensen/subadditivity for the closed perspective, with all zero
boundary branches obtained as limits of strictly positive regularizations.
This is the analytic core of Gour, Theorem 5.1. -/
theorem closedPerspective_add_le (g : FDivGenerator)
    (a₁ b₁ a₂ b₂ : ℝ≥0) :
    closedPerspective g (a₁ + a₂) (b₁ + b₂) ≤
      closedPerspective g a₁ b₁ + closedPerspective g a₂ b₂ := by
  let k : ℕ → ℕ := fun n => 2 * n + 1
  have hk : Tendsto k atTop atTop := halfIndex_tendsto
  have h₁ := (tendsto_closedPerspective_add_eps g a₁ b₁).comp hk
  have h₂ := (tendsto_closedPerspective_add_eps g a₂ b₂).comp hk
  have hleft := tendsto_closedPerspective_add_eps g (a₁ + a₂) (b₁ + b₂)
  have hleft' : Tendsto (fun n : ℕ =>
      closedPerspective g ((a₁ + eps (k n)) + (a₂ + eps (k n)))
        ((b₁ + eps (k n)) + (b₂ + eps (k n))))
      atTop (𝓝 (closedPerspective g (a₁ + a₂) (b₁ + b₂))) := by
    apply hleft.congr'
    exact Filter.Eventually.of_forall fun n => by
      simp only [k]
      rw [add_add_add_comm, eps_half_add, add_add_add_comm, eps_half_add]
  have hright : Tendsto (fun n : ℕ =>
      closedPerspective g (a₁ + eps (k n)) (b₁ + eps (k n)) +
        closedPerspective g (a₂ + eps (k n)) (b₂ + eps (k n)))
      atTop (𝓝 (closedPerspective g a₁ b₁ + closedPerspective g a₂ b₂)) := by
    exact (EReal.continuousAt_add
      (Or.inr (closedPerspective_ne_bot g a₂ b₂))
      (Or.inl (closedPerspective_ne_bot g a₁ b₁))).tendsto.comp
        (h₁.prodMk_nhds h₂)
  apply le_of_tendsto_of_tendsto hleft' hright
  exact Filter.Eventually.of_forall fun n =>
    closedPerspective_add_le_of_ne_zero g _ _ _ _
      (add_eps_ne_zero a₁ (k n)) (add_eps_ne_zero b₁ (k n))
      (add_eps_ne_zero a₂ (k n)) (add_eps_ne_zero b₂ (k n))

/-- Finite Jensen/subadditivity for the endpoint-closed perspective. -/
theorem closedPerspective_finset_sum_le {ι : Type*} (g : FDivGenerator)
    (s : Finset ι) (a b : ι → ℝ≥0) :
    closedPerspective g (∑ i ∈ s, a i) (∑ i ∈ s, b i) ≤
      ∑ i ∈ s, closedPerspective g (a i) (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      simp only [Finset.sum_insert, hx, not_false_eq_true]
      exact (closedPerspective_add_le g (a x) (b x)
        (∑ i ∈ s, a i) (∑ i ∈ s, b i)).trans (add_le_add_right ih _)

private theorem pmf_toNNReal_sum {ι : Type} [Fintype ι] (p : PMF ι) :
    ∑ i, (p i).toNNReal = 1 := by
  rw [← ENNReal.toNNReal_sum (s := Finset.univ)
    (fun i _hi => p.apply_ne_top i)]
  have hsum : ∑ i, p i = 1 := by
    simpa only [tsum_fintype] using p.tsum_coe
  rw [hsum]
  simp

/-- The raw `EReal` f-divergence is mathematically nonnegative by finite
Jensen, not merely by projection to `ENNReal`.  This is the divergence
nonnegativity asserted after Gour, Definition 5.2, and proved using Theorem 5.1. -/
theorem classicalFDivSum_nonnegative {ι : Type} [Fintype ι]
    (g : FDivGenerator) (p q : PMF ι) :
    0 ≤ classicalFDivSum g p q := by
  classical
  have h := closedPerspective_finset_sum_le g Finset.univ
    (fun i => (p i).toNNReal) (fun i => (q i).toNNReal)
  rw [pmf_toNNReal_sum p, pmf_toNNReal_sum q,
    closedPerspective_self] at h
  simpa only [classicalFDivSum] using h

end

end OPT
