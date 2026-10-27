/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.Convex.Integral
import Quantum.TraceInequality.GeneralizedPerspectiveFunction

/-!
# Joint Jensen inequalities for Bochner integrals

A continuous jointly convex or concave real-valued function on a product of closed convex
sets satisfies Jensen's inequality for integrable maps into a real Banach space.
-/

open MeasureTheory

namespace GeneralizedPerspectiveFunction

/-- Jointly convex Jensen inequality for Bochner integrals in a real Banach space,
with a probability measure and closed convex domains.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
theorem JointlyConvexOn.map_integral_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {S T : Set E} (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hSc : IsClosed S) (hTc : IsClosed T)
    {f : E → E → ℝ}
    (hf_conv : JointlyConvexOn S T f)
    (hf_cont : ContinuousOn (Function.uncurry f) (S ×ˢ T))
    {g₁ g₂ : α → E}
    (hg₁ : ∀ᵐ x ∂μ, g₁ x ∈ S)
    (hg₂ : ∀ᵐ x ∂μ, g₂ x ∈ T)
    (hg₁_int : Integrable g₁ μ) (hg₂_int : Integrable g₂ μ)
    (hfg_int : Integrable (fun x => f (g₁ x) (g₂ x)) μ) :
    f (∫ x, g₁ x ∂μ) (∫ x, g₂ x ∂μ) ≤ ∫ x, f (g₁ x) (g₂ x) ∂μ := by
  have hF : ConvexOn ℝ (S ×ˢ T) (Function.uncurry f) := by
    constructor
    · exact hS.prod hT
    · rintro ⟨a₁, b₁⟩ ⟨ha₁, hb₁⟩ ⟨a₂, b₂⟩ ⟨ha₂, hb₂⟩ c d hc hd hcd
      change f (c • a₁ + d • a₂) (c • b₁ + d • b₂) ≤
        c • f a₁ b₁ + d • f a₂ b₂
      have hcd' : c = 1 - d := by linarith
      rw [hcd']
      exact hf_conv ha₁ ha₂ hb₁ hb₂ hd (by linarith)
  have key := hF.map_integral_le hf_cont (hSc.prod hTc)
    (hg₁.mp (hg₂.mono fun x h₂ h₁ => ⟨h₁, h₂⟩))
    (hg₁_int.prodMk hg₂_int) hfg_int
  simp only [Function.uncurry_apply_pair, integral_pair hg₁_int hg₂_int] at key
  exact key

/-- Jointly concave Jensen inequality for Bochner integrals in a real Banach space,
with a probability measure and closed convex domains.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
theorem JointlyConcaveOn.le_map_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {S T : Set E} (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hSc : IsClosed S) (hTc : IsClosed T)
    {f : E → E → ℝ}
    (hf_conc : JointlyConcaveOn S T f)
    (hf_cont : ContinuousOn (Function.uncurry f) (S ×ˢ T))
    {g₁ g₂ : α → E}
    (hg₁ : ∀ᵐ x ∂μ, g₁ x ∈ S)
    (hg₂ : ∀ᵐ x ∂μ, g₂ x ∈ T)
    (hg₁_int : Integrable g₁ μ) (hg₂_int : Integrable g₂ μ)
    (hfg_int : Integrable (fun x => f (g₁ x) (g₂ x)) μ) :
    (∫ x, f (g₁ x) (g₂ x) ∂μ) ≤ f (∫ x, g₁ x ∂μ) (∫ x, g₂ x ∂μ) := by
  have hF : ConcaveOn ℝ (S ×ˢ T) (Function.uncurry f) := by
    constructor
    · exact hS.prod hT
    · rintro ⟨a₁, b₁⟩ ⟨ha₁, hb₁⟩ ⟨a₂, b₂⟩ ⟨ha₂, hb₂⟩ c d hc hd hcd
      change c • f a₁ b₁ + d • f a₂ b₂ ≤
        f (c • a₁ + d • a₂) (c • b₁ + d • b₂)
      have hcd' : c = 1 - d := by linarith
      rw [hcd']
      exact hf_conc ha₁ ha₂ hb₁ hb₂ hd (by linarith)
  have key := hF.le_map_integral hf_cont (hSc.prod hTc)
    (hg₁.mp (hg₂.mono fun x h₂ h₁ => ⟨h₁, h₂⟩))
    (hg₁_int.prodMk hg₂_int) hfg_int
  simp only [Function.uncurry_apply_pair, integral_pair hg₁_int hg₂_int] at key
  exact key

end GeneralizedPerspectiveFunction
