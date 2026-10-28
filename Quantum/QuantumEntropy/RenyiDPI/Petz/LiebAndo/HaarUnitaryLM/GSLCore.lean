/-
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCoreGeneralizedStein
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCore
import Quantum.TraceInequality.LiebAndo.LiebTrace.Bridge
import Quantum.TraceInequality.LiebTrace.Bridge
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Algebra.Central.End
import Quantum.QuantumEntropy.TensorCFCUmegaki
import Quantum.QuantumEntropy.TensorCFC
import Quantum.QuantumMechanics.OperatorInstances
import Mathlib.Analysis.CStarAlgebra.Unitary.Span

-- Haar measure on locally compact groups

-- IsTopologicalGroup instance for unitary groups

-- Jensen's inequality for convex/concave functions under probability measures

-- Haar-invariant integrals (integral_mul_left_eq_self)

-- Trace of rank-one operators and inner product

-- finrank_eq_card_basis

-- IsCentral for End, center of endomorphism algebras

-- rTensorStarAlgHom, lTensorStarAlgHom, map_eq_rTensor_mul_lTensor

/-!
# Haar measure on the unitary group and tools for Theorem 1

Infrastructure for the normalized (probability) Haar measure on the finite-dimensional
unitary group, the twirl identity, and Jensen-type inequalities for jointly convex /
concave operator functions under Haar integration.

These are the measure-theoretic ingredients needed to derive monotonicity of the
sandwiched Rényi relative entropy (Theorem 1 of Frank–Lieb, arXiv:1306.5358) from
Proposition 3 (joint convexity / concavity of the sandwiched quasi-relative entropy).

## Convention

We write `Tr₂` for `QuantumChannel.Tr₂`, which traces out the **first** tensor factor:
  `Tr₂ : L(ℋ₁ ⊗ ℋ₂) → L ℋ₂`.
When the first factor is the "environment" ℋ_env and the second is the main system ℋ,
`Tr₂` computes the partial trace over the environment. This matches the Stinespring
convention `E(γ) = Tr₂(U (τ ⊗ γ) U*)` where τ is the environment state on ℋ₁ and
γ is the input state on ℋ₂.
-/

open QuantumState QuantumChannel TensorCFC
open MeasureTheory MeasureTheory.Measure
open GeneralizedPerspectiveFunction
open scoped ComplexOrder TensorProduct

namespace HaarUnitary

universe u

/-! ## Section 4: Jensen inequality for jointly convex/concave operator functions -/

section Jensen

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

omit [Nontrivial ℋ] in
/-- **Jensen's inequality for jointly concave functions under probability measure**.
    If f : L ℋ → L ℋ → ℝ is jointly concave on S × T, then
    ∫ f(g₁(u), g₂(u)) dμ ≤ f(∫ g₁ dμ, ∫ g₂ dμ). -/
theorem jointly_concave_le_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {S T : Set (L ℋ)} (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hSc : IsClosed S) (hTc : IsClosed T)
    {f : L ℋ → L ℋ → ℝ}
    (hf_conc : JointlyConcaveOn S T f)
    (hf_cont : ContinuousOn (Function.uncurry f) (S ×ˢ T))
    {g₁ g₂ : α → L ℋ}
    (hg₁ : ∀ᵐ x ∂μ, g₁ x ∈ S)
    (hg₂ : ∀ᵐ x ∂μ, g₂ x ∈ T)
    (hg₁_int : Integrable g₁ μ) (hg₂_int : Integrable g₂ μ)
    (hfg_int : Integrable (fun x => f (g₁ x) (g₂ x)) μ)
    (_hmem₁ : ∫ x, g₁ x ∂μ ∈ S) (_hmem₂ : ∫ x, g₂ x ∂μ ∈ T) :
    (∫ x, f (g₁ x) (g₂ x) ∂μ) ≤ f (∫ x, g₁ x ∂μ) (∫ x, g₂ x ∂μ) := by
  have hF : ConcaveOn ℝ (S ×ˢ T) (Function.uncurry f) := by
    constructor
    · exact hS.prod hT
    · rintro ⟨a₁, b₁⟩ ⟨ha₁, hb₁⟩ ⟨a₂, b₂⟩ ⟨ha₂, hb₂⟩ c d hc hd hcd
      change c • f a₁ b₁ + d • f a₂ b₂ ≤ f (c • a₁ + d • a₂) (c • b₁ + d • b₂)
      have : c = 1 - d := by linarith
      rw [this]; exact hf_conc ha₁ ha₂ hb₁ hb₂ hd (by linarith)
  have key := hF.le_map_integral hf_cont (hSc.prod hTc)
    (hg₁.mp (hg₂.mono fun x h₂ h₁ => ⟨h₁, h₂⟩))
    (hg₁_int.prodMk hg₂_int) hfg_int
  simp only [Function.uncurry_apply_pair, integral_pair hg₁_int hg₂_int] at key
  exact key

end Jensen

end HaarUnitary
