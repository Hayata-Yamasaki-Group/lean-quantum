/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.QuantumState
import Quantum.QuantumMechanics.OperatorInstances

/-!
This proof-support layer connects linear endomorphisms to bounded operators.
It provides the canonical star-algebra equivalence used by proofs
that apply Mathlib's bounded-operator analysis.
-/

namespace QuantumChannel

open QuantumState

universe u

/-- The canonical star-algebra equivalence from linear to continuous endomorphisms. -/
noncomputable def linearToContinuousEndStarAlgEquiv
    (ℋ : Type*) [Qudit ℋ] :
    L ℋ ≃⋆ₐ[ℂ] (ℋ →L[ℂ] ℋ) where
  toFun := LinearMap.toContinuousLinearMap
  invFun := ContinuousLinearMap.toLinearMap
  left_inv := by intro A; rfl
  right_inv := by intro A; ext x; rfl
  map_mul' := by intro A B; rfl
  map_add' := by intro A B; rfl
  map_smul' := by intro c A; rfl
  map_star' := by
    intro A
    simpa using (LinearMap.adjoint_toContinuousLinearMap (A := A))

end QuantumChannel

namespace QuantumChannel

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u
variable {ℋ : Type u} [Qudit ℋ]

/-- Conjugation by a self-adjoint operator preserves positivity: A * B * A ≥ 0 when A† = A,
  B ≥
  0. -/
lemma isPositive_conj {A : L ℋ} (hA : IsSelfAdjoint A) {B : L ℋ} (hB : B.IsPositive) :
    (A * B * A).IsPositive := by
  have hadj : LinearMap.adjoint A = A := by
    rw [← LinearMap.star_eq_adjoint]; exact hA.star_eq
  have h := hB.conj_adjoint A
  rw [hadj] at h
  exact h

end

end QuantumChannel

namespace QuantumChannel

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u

private lemma nonneg_apply_eq_zero_of_inner_self_eq_zero_lm
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : 0 ≤ A) {x : ℋ}
    (h_inner : RCLike.re (inner ℂ (A x) x) = 0) :
    A x = 0 := by
  set s : L ℋ := CFC.sqrt A with hs_def
  have hs_nn : (0 : L ℋ) ≤ s := CFC.sqrt_nonneg A
  have hs_sq : s * s = A := CFC.sqrt_mul_sqrt_self A
  have hs_pos : s.IsPositive := (LinearMap.nonneg_iff_isPositive s).mp hs_nn
  have hs_sym : s.IsSymmetric := hs_pos.1
  have h_s_apply : s (s x) = A x := by
    have : (s * s) x = A x := by rw [hs_sq]
    exact this
  have h_norm_sq : ‖s x‖ ^ 2 = RCLike.re (inner ℂ (A x) x) := by
    have h1 : inner ℂ (s x) (s x) = inner ℂ (s (s x)) x := (hs_sym (s x) x).symm
    have h2 : inner ℂ (s (s x)) x = inner ℂ (A x) x := by rw [h_s_apply]
    have h3 : (inner ℂ (s x) (s x) : ℂ) = inner ℂ (A x) x := h1.trans h2
    rw [← @inner_self_eq_norm_sq ℂ ℋ, h3]
  rw [h_inner] at h_norm_sq
  have h_sx_norm : ‖s x‖ = 0 := by
    have h_pow : ‖s x‖ ^ 2 = 0 := h_norm_sq
    exact pow_eq_zero_iff two_ne_zero |>.mp h_pow
  have h_sx : s x = 0 := norm_eq_zero.mp h_sx_norm
  rw [← h_s_apply, h_sx, map_zero]

end

end QuantumChannel

namespace QuantumChannel

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u

private lemma nonneg_eq_zero_of_le_of_apply_eq_zero_lm
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A B : L ℋ} (hA : 0 ≤ A) (hAB : A ≤ B) {x : ℋ} (hx : B x = 0) :
    A x = 0 := by
  have hBA : 0 ≤ B - A := sub_nonneg.mpr hAB
  have hA_pos : A.IsPositive := (LinearMap.nonneg_iff_isPositive A).mp hA
  have hBA_pos : (B - A).IsPositive :=
    (LinearMap.nonneg_iff_isPositive _).mp hBA
  have h_A_nn : (0 : ℝ) ≤ RCLike.re (inner ℂ (A x) x) := hA_pos.2 x
  have h_BA_nn : (0 : ℝ) ≤ RCLike.re (inner ℂ ((B - A) x) x) := hBA_pos.2 x
  have hsub_x : (B - A) x = -A x := by
    change B x - A x = -A x
    rw [hx, zero_sub]
  have h_BA_eq : RCLike.re (inner ℂ ((B - A) x) x) =
      -RCLike.re (inner ℂ (A x) x) := by
    rw [hsub_x, inner_neg_left, map_neg]
  rw [h_BA_eq] at h_BA_nn
  have h_A_zero : RCLike.re (inner ℂ (A x) x) = 0 :=
    le_antisymm (by linarith) h_A_nn
  exact nonneg_apply_eq_zero_of_inner_self_eq_zero_lm hA h_A_zero

end

end QuantumChannel

namespace QuantumChannel

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u

/-- For a non-negative operator `A`, `re ⟨A x, x⟩ = 0` implies `A x = 0`.

    **Proof**: For positive `A`, take `s := CFC.sqrt A`. Then `s` is symmetric,
    `s * s = A`, and `re ⟨A x, x⟩ = re ⟨s (s x), x⟩ = re ⟨s x, s x⟩ = ‖s x‖² = 0`.
    Hence `s x = 0` and `A x = s (s x) = 0`. -/
lemma nonneg_apply_eq_zero_of_inner_self_eq_zero
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : 0 ≤ A) {x : ℋ}
    (h_inner : RCLike.re (inner ℂ (A x) x) = 0) :
    A x = 0 := by
  exact nonneg_apply_eq_zero_of_inner_self_eq_zero_lm hA h_inner

end

end QuantumChannel

namespace QuantumChannel

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u

/-- For non-negative `A ≤ B`, `B x = 0 ⇒ A x = 0`.

    **Proof**: From `A ≤ B`, `0 ≤ A`, and `B x = 0`, derive `re ⟨A x, x⟩ = 0`, then
    apply `nonneg_apply_eq_zero_of_inner_self_eq_zero`. -/
lemma nonneg_eq_zero_of_le_of_apply_eq_zero
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A B : L ℋ} (hA : 0 ≤ A) (hAB : A ≤ B) {x : ℋ} (hx : B x = 0) :
    A x = 0 := by
  exact nonneg_eq_zero_of_le_of_apply_eq_zero_lm hA hAB hx

end

end QuantumChannel

namespace QuantumChannel

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u
variable {ℋ : Type u} [Qudit ℋ]

/-- From `ρ ≤ (lam:ℂ) • σ` we get `re ⟨ρ x, x⟩ ≤ lam * re ⟨σ x, x⟩`. -/
lemma re_inner_le_of_le_smul {ρ σ : L ℋ} {lam : ℝ}
    (h : ρ ≤ (lam : ℂ) • σ) (x : ℋ) :
    RCLike.re (inner ℂ (ρ x) x) ≤ lam * RCLike.re (inner ℂ (σ x) x) := by
  rw [LinearMap.le_def] at h
  obtain ⟨_, h2⟩ := h
  have hx := h2 x
  change 0 ≤ RCLike.re (inner ℂ (((lam : ℂ) • σ - ρ) x) x) at hx
  have heq : ((lam : ℂ) • σ - ρ) x = (lam : ℂ) • σ x - ρ x := by
    rfl
  rw [heq, inner_sub_left, inner_smul_left, Complex.conj_ofReal, map_sub] at hx
  have hre : RCLike.re ((lam : ℂ) * inner ℂ (σ x) x) = lam * RCLike.re (inner ℂ (σ x)
    x) := by
    change (((lam : ℂ) * inner ℂ (σ x) x)).re = _
    rw [Complex.re_ofReal_mul]; rfl
  rw [hre] at hx
  linarith

end

end QuantumChannel

namespace QuantumChannel

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u
variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

/-- For nonneg `ρ ≠ 0`, there is `x` with `re ⟨ρ x, x⟩ > 0`. -/
lemma exists_re_inner_pos_of_ne_zero {ρ : L ℋ} (hρ : 0 ≤ ρ) (hρ0 : ρ ≠ 0) :
    ∃ x, 0 < RCLike.re (inner ℂ (ρ x) x) := by
  by_contra h
  push_neg at h
  apply hρ0
  have hρ_pos : ρ.IsPositive := (LinearMap.nonneg_iff_isPositive ρ).mp hρ
  ext x
  have hle : RCLike.re (inner ℂ (ρ x) x) ≤ 0 := h x
  have hge : 0 ≤ RCLike.re (inner ℂ (ρ x) x) := hρ_pos.2 x
  have heq : RCLike.re (inner ℂ (ρ x) x) = 0 := le_antisymm hle hge
  have hzero := QuantumChannel.nonneg_apply_eq_zero_of_inner_self_eq_zero hρ heq
  rw [LinearMap.zero_apply]; exact hzero

end

end QuantumChannel

namespace QuantumChannel

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u

/-- If the kernel of `A` is contained in the kernel of a symmetric operator `B`,
then a matrix coefficient of `B` vanishes whenever either eigenvalue of `A` does. -/
lemma inner_apply_eq_zero_of_ker_le
    {ℋ : Type u} [Qudit ℋ]
    {A B : ℋ →L[ℂ] ℋ}
    (hB : B.IsSymmetric)
    {ι : Type*}
    (v : ι → ℋ) (μ : ι → ℝ)
    (hAv : ∀ k, A (v k) = (μ k : ℂ) • v k)
    (hker :
      LinearMap.ker (A : L ℋ) ≤ LinearMap.ker (B : L ℋ))
    {i j : ι}
    (hzero : μ i = 0 ∨ μ j = 0) :
    inner ℂ (v j) (B (v i)) = 0 := by
  have hBv : ∀ k, μ k = 0 → B (v k) = 0 := by
    intro k hk
    apply hker
    rw [LinearMap.mem_ker]
    change A (v k) = 0
    rw [hAv k, hk]
    simp
  rcases hzero with hi | hj
  · rw [hBv i hi]
    simp
  · rw [show inner ℂ (v j) (B (v i)) = inner ℂ (B (v j)) (v i) from
        (hB (v j) (v i)).symm, hBv j hj]
    simp

end

end QuantumChannel
