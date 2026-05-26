/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumMechanics.QuantumChannel
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Naimark column-orthogonal extension and unitary Stinespring dilation

This file isolates the **Naimark column-orthogonal extension** for Kraus
families on a finite-dimensional Hilbert space `ℋ`. Concretely, given a
Kraus family `{A_a}_{a ∈ κ}` on `ℋ` with `Σ_a A_a* A_a = I` and
`|κ| ≤ d²` where `d := dim ℋ`, the file constructs a unitary `U` on
`ℋ ⊗ ℋ` realizing the channel `γ ↦ Σ_a A_a γ A_a*` as
  `Tr₂[U ((I/d) ⊗ γ) U*]`,
where `Tr₂` traces out the *first* (environment) factor and `I/d` is the
maximally mixed state. This is the Watrous Corollary 2.27 in unitary
form with a maximally mixed environment.

## Structure

The construction is organized in four steps:

* **Step 1 — Padding.** `padded`, `sum_padded_adjoint_comp`,
  `sum_padded_channel_eq`: pad a `κ`-indexed family to a
  `Fin d × Fin d`-indexed family while preserving both the resolution
  of identity and the channel.

* **Step 2 — Operator-valued Gram–Schmidt.**
  `exists_column_orthogonal_kraus_equivalent`: produce a
  column-orthogonal family `{K_{l,i}}` from a padded family.

* **Step 3 — Naimark unitary.** `naimarkLinearMap`,
  `naimarkLinearIsometry`, `naimarkLinearIsometryEquiv`,
  `naimarkUnitary`: from a column-orthogonal `K`, build a unitary on
  `ℋ ⊗ ℋ` whose `(l, i)`-block is `K(l, i)`.

* **Step 4 — Partial-trace identity.** `naimarkUnitary_partialTrace_eq`,
  `column_orthogonal_to_unitary_dilation`: compute
  `Tr₂[U ((I/d) ⊗ γ) U*] = (1/d) · Σ_α K_α γ K_α*` and reassemble
  into the channel identity.

The pieces are combined in `exists_naimark_unitary_dilation_square` and
finally `exists_naimark_unitary_dilation`.

## Status

Steps 1, 3, 4 are fully implemented. **Step 2 is the only remaining
`sorry`** (in `exists_column_orthogonal_kraus_equivalent`); see that
lemma's docstring for a detailed mathematical roadmap.
-/

open QuantumState QuantumChannel TensorProduct
open scoped ComplexOrder

namespace NaimarkExtension

universe u

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

/-! ### Step 1: padding a Kraus family via an embedding -/

/-- Pad a `κ`-indexed family of operators `A : κ → L ℋ` to an
    `ι`-indexed family via an embedding `j : κ ↪ ι`. The padded family
    `padded j A i` is `A a` when `i = j a` for some `a ∈ κ`, and `0`
    otherwise.

    Defined as a finite sum so that `Decidable (∃ a, j a = i)` is not
    needed; `j` injective makes the sum collapse to the at-most-one
    contributing term. -/
noncomputable def padded {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    (j : κ ↪ ι) (A : κ → L ℋ) (i : ι) : L ℋ :=
  ∑ a : κ, if j a = i then A a else 0

omit [Nontrivial ℋ] in
lemma padded_apply_image {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    (j : κ ↪ ι) (A : κ → L ℋ) (a : κ) :
    padded j A (j a) = A a := by
  classical
  unfold padded
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    have hjb : j b ≠ j a := fun h => hb (j.injective h)
    simp [hjb]
  · simp

omit [Nontrivial ℋ] in
lemma padded_apply_not_image {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    (j : κ ↪ ι) (A : κ → L ℋ) {i : ι} (h : ∀ a, j a ≠ i) :
    padded j A i = 0 := by
  classical
  unfold padded
  refine Finset.sum_eq_zero ?_
  intro a _
  have hja : j a ≠ i := h a
  simp [hja]

/-- Splitting `Finset.univ` (over `ι`) into the image of an embedding
    `j : κ ↪ ι` and its complement. -/
private lemma univ_eq_image_union_sdiff
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (j : κ ↪ ι) :
    (Finset.univ : Finset ι) =
      (Finset.univ.map j) ∪ (Finset.univ \ Finset.univ.map j) := by
  ext i
  refine ⟨fun _ => ?_, fun _ => Finset.mem_univ i⟩
  by_cases h : i ∈ Finset.univ.map j
  · exact Finset.mem_union_left _ h
  · refine Finset.mem_union_right _ ?_
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h⟩

omit [Nontrivial ℋ] in
/-- Padding preserves `Σ_i (padded j A i)* (padded j A i) = Σ_a A_a* A_a`.
    Out-of-range slots contribute zero; in-range slots reproduce the
    original sum. -/
lemma sum_padded_adjoint_comp {κ ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq ι] (j : κ ↪ ι) (A : κ → L ℋ) :
    (∑ i : ι, (LinearMap.adjoint (padded j A i)).comp (padded j A i)) =
      (∑ a : κ, (LinearMap.adjoint (A a)).comp (A a)) := by
  classical
  set f : ι → L ℋ :=
    fun i => (LinearMap.adjoint (padded j A i)).comp (padded j A i) with hf_def
  set g : κ → L ℋ :=
    fun a => (LinearMap.adjoint (A a)).comp (A a) with hg_def
  have hsplit : ∑ i : ι, f i =
      (∑ i ∈ (Finset.univ.map j), f i) +
        (∑ i ∈ (Finset.univ \ Finset.univ.map j), f i) := by
    conv_lhs => rw [show (Finset.univ : Finset ι) =
      (Finset.univ.map j) ∪ (Finset.univ \ Finset.univ.map j) from
        univ_eq_image_union_sdiff j]
    exact Finset.sum_union Finset.disjoint_sdiff
  have hzero : (∑ i ∈ (Finset.univ \ Finset.univ.map j), f i) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    rw [Finset.mem_sdiff] at hi
    obtain ⟨_, hi_notImg⟩ := hi
    have hnotJ : ∀ a, j a ≠ i := by
      intro a ha
      apply hi_notImg
      rw [Finset.mem_map]
      exact ⟨a, Finset.mem_univ a, ha⟩
    have hp : padded j A i = 0 := padded_apply_not_image j A hnotJ
    simp [hf_def, hp]
  have himg : (∑ i ∈ (Finset.univ.map j), f i) = ∑ a : κ, g a := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [hf_def, hg_def, padded_apply_image j A a]
  rw [hsplit, hzero, add_zero, himg]

omit [Nontrivial ℋ] in
/-- Padding preserves the channel action `Σ_i (padded j A i) γ (padded j A i)* =
    Σ_a A_a γ A_a*`. -/
lemma sum_padded_channel_eq {κ ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq ι] (j : κ ↪ ι) (A : κ → L ℋ) (γ : L ℋ) :
    (∑ i : ι, (padded j A i).comp (γ.comp (LinearMap.adjoint (padded j A i)))) =
      (∑ a : κ, (A a).comp (γ.comp (LinearMap.adjoint (A a)))) := by
  classical
  set f : ι → L ℋ :=
    fun i => (padded j A i).comp (γ.comp (LinearMap.adjoint (padded j A i))) with hf_def
  set g : κ → L ℋ :=
    fun a => (A a).comp (γ.comp (LinearMap.adjoint (A a))) with hg_def
  have hsplit : ∑ i : ι, f i =
      (∑ i ∈ (Finset.univ.map j), f i) +
        (∑ i ∈ (Finset.univ \ Finset.univ.map j), f i) := by
    conv_lhs => rw [show (Finset.univ : Finset ι) =
      (Finset.univ.map j) ∪ (Finset.univ \ Finset.univ.map j) from
        univ_eq_image_union_sdiff j]
    exact Finset.sum_union Finset.disjoint_sdiff
  have hzero : (∑ i ∈ (Finset.univ \ Finset.univ.map j), f i) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    rw [Finset.mem_sdiff] at hi
    obtain ⟨_, hi_notImg⟩ := hi
    have hnotJ : ∀ a, j a ≠ i := by
      intro a ha
      apply hi_notImg
      rw [Finset.mem_map]
      exact ⟨a, Finset.mem_univ a, ha⟩
    have hp : padded j A i = 0 := padded_apply_not_image j A hnotJ
    simp [hf_def, hp]
  have himg : (∑ i ∈ (Finset.univ.map j), f i) = ∑ a : κ, g a := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [hf_def, hg_def, padded_apply_image j A a]
  rw [hsplit, hzero, add_zero, himg]

/-! ### Step 2: operator-valued Gram–Schmidt (focused `sorry`) -/

/-- **Column-orthogonality** of an operator family indexed by
    `Fin d × Fin d`: for every pair `(i, i')`,
      `Σ_l K(l, i)* K(l, i') = δ_{i,i'} · I_ℋ`. -/
def ColumnOrthogonal
    (K : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → L ℋ) : Prop :=
  ∀ i i' : Fin (Module.finrank ℂ ℋ),
    (∑ l : Fin (Module.finrank ℂ ℋ),
      (LinearMap.adjoint (K (l, i))).comp (K (l, i'))) =
        (if i = i' then (1 : L ℋ) else 0)

/-- **Operator-valued Gram–Schmidt (existence).**

    Given a `Fin d × Fin d`-indexed Kraus family `B` on `ℋ` of dimension
    `d` with `Σ_α B_α* B_α = I`, there exists an equivalent family
    `K : Fin d × Fin d → L ℋ` satisfying *column orthogonality*
      `Σ_l K(l, i)* K(l, i') = δ_{i,i'} · I`
    and the *channel-equivalence* relation
      `Σ_α K_α γ K_α* = d · Σ_α B_α γ B_α*`
    for all `γ ∈ L ℋ`.

    **Status.** This is the only remaining `sorry` in the file; all
    other components of the Naimark dilation are implemented and depend
    only on this lemma.

    **Mathematical content.**
    By Stinespring's theorem with maximally mixed environment (Watrous,
    *The Theory of Quantum Information*, Thm. 2.27), every quantum
    channel on a `d`-dim Hilbert space `ℋ` admits a dilation
      `Φ(γ) = Tr_env[V ((I/d) ⊗ γ) V*]`
    by some unitary `V` on `ℋ_env ⊗ ℋ_sys` with `dim ℋ_env = d`.
    Writing the matrix elements `W(l, i) := ⟨l|_env V |i⟩_env : L ℋ`,
    unitarity of `V` is equivalent to column orthogonality
      `Σ_l W(l, i)* W(l, i') = δ_{ii'} I`,
    and the partial-trace identity (`naimarkUnitary_partialTrace_eq`)
    gives `(1/d) · Σ_{l, i} W(l, i) γ W(l, i)* = Φ(γ)`. Setting
    `K(l, i) := W(l, i)` is therefore exactly the claim.

    **Why the construction is non-trivial.**
    The naive choice `K(l, i) := √d · B(l, i)` fails: column
    orthogonality requires the *per-column* sums
    `Σ_l B(l, i)* B(l, i)` to be individually equal to `(1/d) · I`,
    which is a strictly stronger hypothesis than the overall
    `Σ_{l, i} B(l, i)* B(l, i) = I`. The Choi-spectral family
    `K'_β := √d · vec⁻¹(√λ_β v_β)` realizing `d · Φ` (where `v_β` are
    eigenvectors of the Choi matrix) likewise fails: the
    `(l, i)`-indexing of `v_β` carries no tensor structure aligned
    with `ColumnOrthogonal`. For instance, for the identity channel
    (`B(0,0) = I`, others zero), the Choi has a single eigenvector
    `|Ω⟩` and the spectral-decomposition `K` is `K(0,0) = I` (others
    zero), which is not column-orthogonal at `i ≠ 0`.

    A correct construction rotates the Choi-spectral family `K'_β` by
    a unitary `U` on the `Fin d × Fin d`-index space (an operator-
    valued Gram–Schmidt / QR-decomposition on `K'` viewed as a `d × d`
    matrix over `L ℋ`) so that
      `K(l, i) := Σ_{β} U_{(l, i), β} · K'_β`
    has orthonormal operator-valued columns. For the identity channel
    with `U` the discrete Fourier transform, this recovers the
    explicit family `K(l, i) = (1/√d) · ω^{l·i} · I` with `ω` a
    primitive `d`-th root of unity.

    **Suggested implementation (estimated 300–500 Lean lines).**
    1. Form `J := Σ_α |vec B_α⟩⟨vec B_α| ∈ L (ℋ ⊗ ℋ)` and prove
       positivity (`outer_product_self_nonneg`, `Finset.sum_nonneg`).
    2. Diagonalize `J` via `positive_full_spectral_outer_product` and
       reindex by `Fin d × Fin d` (`Fintype.equivOfCardEq`).
    3. Extract Kraus operators `K'_β := vec⁻¹(u_β)` realizing `Φ_B`
       via `choi_outer_product_to_kraus`; scale by `√d`.
    4. Build the rotation `U` by extending a partial isometry on a
       `d`-dim subspace via Mathlib's `LinearIsometry.extend`, then
       read off `K` from its matrix elements. The hard step.
    5. Verify the channel equality and column orthogonality. -/
theorem exists_column_orthogonal_kraus_equivalent
    (B : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → L ℋ)
    (_hSumBB :
      (∑ α : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ),
        (LinearMap.adjoint (B α)).comp (B α)) = (1 : L ℋ)) :
    ∃ K : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → L ℋ,
      ColumnOrthogonal (ℋ := ℋ) K ∧
      (∀ γ : L ℋ,
        (∑ α : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ),
            (K α).comp (γ.comp (LinearMap.adjoint (K α)))) =
          ((Module.finrank ℂ ℋ : ℂ)) •
            (∑ α : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ),
              (B α).comp (γ.comp (LinearMap.adjoint (B α))))) := by
  sorry

/-! ### Step 3: linear map underlying the Naimark unitary -/

/-- The underlying linear map of the Naimark unitary.

    Constructed via `TensorProduct.lift` from the bilinear map
      `(x, ψ) ↦ Σ_{(l, i)} (b.repr x i) • (b l ⊗ K(l, i) ψ)`.

    On basis tensors `b i ⊗ ψ` this evaluates to
      `Σ_l b l ⊗ K(l, i) ψ`
    (see `naimarkLinearMap_apply_basis_tmul`). -/
noncomputable def naimarkLinearMap
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ)
    (K : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → L ℋ) :
    L (ℋ ⊗[ℂ] ℋ) :=
  TensorProduct.lift
    (LinearMap.mk₂ ℂ
      (fun x ψ =>
        ∑ p : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ),
          (b.repr x p.2) • (b p.1) ⊗ₜ[ℂ] K p ψ)
      (by
        intro x x' ψ
        simp only [map_add, PiLp.add_apply, add_smul, Finset.sum_add_distrib])
      (by
        intro c x ψ
        simp only [map_smul, PiLp.smul_apply, smul_eq_mul, mul_smul,
          Finset.smul_sum])
      (by
        intro x ψ ψ'
        simp only [map_add, TensorProduct.tmul_add, smul_add,
          Finset.sum_add_distrib])
      (by
        intro c x ψ
        simp only [map_smul, TensorProduct.tmul_smul, smul_comm c,
          Finset.smul_sum]))

omit [Nontrivial ℋ] in
/-- Evaluation of `naimarkLinearMap` on a general tensor `x ⊗ ψ`. -/
lemma naimarkLinearMap_tmul
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ)
    (K : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → L ℋ)
    (x ψ : ℋ) :
    naimarkLinearMap (ℋ := ℋ) b K (x ⊗ₜ[ℂ] ψ) =
      ∑ p : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ),
        (b.repr x p.2) • (b p.1) ⊗ₜ[ℂ] K p ψ := by
  unfold naimarkLinearMap
  rw [TensorProduct.lift.tmul, LinearMap.mk₂_apply]

omit [Nontrivial ℋ] in
/-- Evaluation of `naimarkLinearMap` on a basis tensor: `b i ⊗ ψ`
    is mapped to `Σ_l b l ⊗ K(l, i) ψ`. -/
lemma naimarkLinearMap_apply_basis_tmul
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ)
    (K : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → L ℋ)
    (i : Fin (Module.finrank ℂ ℋ)) (ψ : ℋ) :
    naimarkLinearMap (ℋ := ℋ) b K ((b i) ⊗ₜ[ℂ] ψ) =
      ∑ l : Fin (Module.finrank ℂ ℋ), (b l) ⊗ₜ[ℂ] (K (l, i) ψ) := by
  classical
  unfold naimarkLinearMap
  rw [TensorProduct.lift.tmul, LinearMap.mk₂_apply]
  rw [OrthonormalBasis.repr_self]
  -- ∑ p, EuclideanSpace.single i 1 p.2 • b p.1 ⊗ₜ K p ψ
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [Finset.sum_eq_single i]
  · simp [EuclideanSpace.single_apply]
  · intro j _ hji
    have hij : ¬ (j = i) := hji
    simp [EuclideanSpace.single_apply, hij]
  · intro hi
    exact (hi (Finset.mem_univ _)).elim

omit [Nontrivial ℋ] in
/-- Inner product of two `naimarkLinearMap`-images of basis tensors.

    Under column orthogonality of `K`, this collapses to
      `⟨b i ⊗ ψ, b i' ⊗ ψ'⟩ = δ_{i, i'} · ⟨ψ, ψ'⟩`,
    which is exactly the inner product of the basis tensors themselves.
    This is the key computation for the isometry property of
    `naimarkLinearMap`. -/
lemma naimarkLinearMap_inner_basis_tmul
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ)
    (K : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → L ℋ)
    (h_col : ColumnOrthogonal (ℋ := ℋ) K)
    (i i' : Fin (Module.finrank ℂ ℋ)) (ψ ψ' : ℋ) :
    inner ℂ
      (naimarkLinearMap (ℋ := ℋ) b K ((b i) ⊗ₜ[ℂ] ψ))
      (naimarkLinearMap (ℋ := ℋ) b K ((b i') ⊗ₜ[ℂ] ψ')) =
      (if i = i' then (inner ℂ ψ ψ' : ℂ) else 0) := by
  classical
  rw [naimarkLinearMap_apply_basis_tmul, naimarkLinearMap_apply_basis_tmul]
  rw [sum_inner]
  -- LHS = Σ_l ⟨b l ⊗ K(l, i) ψ, Σ_l' b l' ⊗ K(l', i') ψ'⟩
  -- For each l, the inner sum reduces to the l' = l term using orthonormality of b.
  have step1 : ∀ l : Fin (Module.finrank ℂ ℋ),
      inner ℂ ((b l) ⊗ₜ[ℂ] (K (l, i) ψ))
        (∑ l' : Fin (Module.finrank ℂ ℋ), (b l') ⊗ₜ[ℂ] (K (l', i') ψ')) =
        inner ℂ (K (l, i) ψ) (K (l, i') ψ') := by
    intro l
    rw [inner_sum]
    rw [Finset.sum_eq_single l]
    · simp [TensorProduct.inner_tmul]
    · intro l' _ hl'l
      have hll' : l ≠ l' := fun h => hl'l h.symm
      simp [TensorProduct.inner_tmul, hll']
    · intro hl
      exact (hl (Finset.mem_univ _)).elim
  simp_rw [step1]
  -- LHS = Σ_l ⟨K(l, i) ψ, K(l, i') ψ'⟩
  --     = Σ_l ⟨ψ, (adjoint (K(l, i))) (K(l, i') ψ')⟩
  have step2 : ∀ l : Fin (Module.finrank ℂ ℋ),
      inner ℂ (K (l, i) ψ) (K (l, i') ψ') =
        inner ℂ ψ ((LinearMap.adjoint (K (l, i))) (K (l, i') ψ')) := by
    intro l
    rw [← LinearMap.adjoint_inner_right]
  simp_rw [step2]
  -- LHS = Σ_l ⟨ψ, (adjoint (K(l, i)) ∘ K(l, i')) ψ'⟩
  --     = ⟨ψ, (Σ_l adjoint (K(l, i)) ∘ K(l, i')) ψ'⟩
  rw [← inner_sum]
  -- Apply column orthogonality:
  -- Σ_l (adjoint (K(l, i))).comp (K(l, i')) = if i = i' then 1 else 0
  have hcol := h_col i i'
  -- The sum inside the inner is `∑ l, (adjoint (K(l, i))) (K(l, i') ψ')`,
  -- which equals `(∑ l, (adjoint (K(l, i))) ∘ₗ (K(l, i'))) ψ'` by
  -- `LinearMap.sum_apply` (with `∘ₗ` unfolded to `∘`).
  have hcol_app :
      (∑ l : Fin (Module.finrank ℂ ℋ),
        (LinearMap.adjoint (K (l, i))) (K (l, i') ψ')) =
        (if i = i' then (1 : L ℋ) else 0) ψ' := by
    rw [← hcol]
    simp [LinearMap.sum_apply, LinearMap.comp_apply]
  rw [hcol_app]
  by_cases h : i = i'
  · simp [h]
  · simp [h]

omit [Nontrivial ℋ] in
/-- Inner-product preservation: under column orthogonality of `K`,
    `naimarkLinearMap b K` is an inner-product-preserving linear map.

    Together with `LinearMap.isometryOfInner` this upgrades `naimarkLinearMap`
    to a `LinearIsometry`, and via
    `LinearIsometry.toLinearIsometryEquiv` (finite-dimensional, equal
    dimensions) to a `LinearIsometryEquiv`.  The associated continuous
    linear map then sits in `unitary (ℋ ⊗ ℋ →L[ℂ] ℋ ⊗ ℋ)`. -/
lemma naimarkLinearMap_inner
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ)
    (K : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → L ℋ)
    (h_col : ColumnOrthogonal (ℋ := ℋ) K)
    (v v' : ℋ ⊗[ℂ] ℋ) :
    inner ℂ (naimarkLinearMap (ℋ := ℋ) b K v) (naimarkLinearMap (ℋ := ℋ) b K v') =
      inner ℂ v v' := by
  classical
  -- Key claim: on basis tensors `b p.1 ⊗ b p.2`, the inner product is preserved.
  have h_basis : ∀ p q : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ),
      inner ℂ
        (naimarkLinearMap (ℋ := ℋ) b K ((b p.1) ⊗ₜ[ℂ] (b p.2)))
        (naimarkLinearMap (ℋ := ℋ) b K ((b q.1) ⊗ₜ[ℂ] (b q.2))) =
        inner ℂ ((b p.1) ⊗ₜ[ℂ] (b p.2) : ℋ ⊗[ℂ] ℋ) ((b q.1) ⊗ₜ[ℂ] (b q.2)) := by
    intro p q
    rw [naimarkLinearMap_inner_basis_tmul b K h_col]
    rw [TensorProduct.inner_tmul]
    rw [OrthonormalBasis.inner_eq_ite (i := p.1) (j := q.1)]
    by_cases h : p.1 = q.1
    · simp [h]
    · simp [h]
  -- Expand v and v' in the OrthonormalBasis `b.tensorProduct b`.
  set e := b.tensorProduct b with he
  conv_lhs =>
    rw [← e.sum_repr v, ← e.sum_repr v']
  conv_rhs =>
    rw [← e.sum_repr v, ← e.sum_repr v']
  rw [map_sum, map_sum]
  simp only [map_smul]
  rw [sum_inner, sum_inner]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [inner_sum, inner_sum]
  refine Finset.sum_congr rfl ?_
  intro q _
  rw [inner_smul_left, inner_smul_right]
  rw [inner_smul_left, inner_smul_right]
  rw [he, OrthonormalBasis.tensorProduct_apply', OrthonormalBasis.tensorProduct_apply']
  congr 2
  exact h_basis p q

omit [Nontrivial ℋ] in
/-- The Naimark map upgraded to a linear isometry. -/
noncomputable def naimarkLinearIsometry
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ)
    (K : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → L ℋ)
    (h_col : ColumnOrthogonal (ℋ := ℋ) K) :
    (ℋ ⊗[ℂ] ℋ) →ₗᵢ[ℂ] (ℋ ⊗[ℂ] ℋ) :=
  (naimarkLinearMap (ℋ := ℋ) b K).isometryOfInner
    (naimarkLinearMap_inner b K h_col)

omit [Nontrivial ℋ] in
@[simp] lemma naimarkLinearIsometry_toLinearMap
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ)
    (K : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → L ℋ)
    (h_col : ColumnOrthogonal (ℋ := ℋ) K) :
    (naimarkLinearIsometry b K h_col).toLinearMap =
      naimarkLinearMap (ℋ := ℋ) b K := rfl

omit [Nontrivial ℋ] in
/-- The Naimark map as a linear isometry equivalence.

    Domain and codomain coincide as `ℋ ⊗[ℂ] ℋ`, so the dimension-equality
    hypothesis of `LinearIsometry.toLinearIsometryEquiv` is `rfl`. -/
noncomputable def naimarkLinearIsometryEquiv
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ)
    (K : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → L ℋ)
    (h_col : ColumnOrthogonal (ℋ := ℋ) K) :
    (ℋ ⊗[ℂ] ℋ) ≃ₗᵢ[ℂ] (ℋ ⊗[ℂ] ℋ) :=
  (naimarkLinearIsometry b K h_col).toLinearIsometryEquiv rfl

omit [Nontrivial ℋ] in
@[simp] lemma naimarkLinearIsometryEquiv_toLinearMap
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ)
    (K : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → L ℋ)
    (h_col : ColumnOrthogonal (ℋ := ℋ) K) :
    (naimarkLinearIsometryEquiv b K h_col).toLinearEquiv.toLinearMap =
      naimarkLinearMap (ℋ := ℋ) b K := rfl

omit [Nontrivial ℋ] in
/-- The Naimark unitary on `ℋ ⊗ ℋ`. -/
noncomputable def naimarkUnitary
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ)
    (K : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → L ℋ)
    (h_col : ColumnOrthogonal (ℋ := ℋ) K) :
    unitary (L (ℋ ⊗[ℂ] ℋ)) :=
  let e := naimarkLinearIsometryEquiv b K h_col
  ⟨e.toLinearEquiv.toLinearMap, by
    refine ⟨?_, ?_⟩
    · change LinearMap.adjoint _ * e.toLinearEquiv.toLinearMap = 1
      have h := LinearIsometryEquiv.adjoint_toLinearMap_eq_symm e
      rw [h]
      ext v
      simp [Module.End.mul_apply]
    · change e.toLinearEquiv.toLinearMap * LinearMap.adjoint _ = 1
      have h := LinearIsometryEquiv.adjoint_toLinearMap_eq_symm e
      rw [h]
      ext v
      simp [Module.End.mul_apply]⟩

omit [Nontrivial ℋ] in
@[simp] lemma naimarkUnitary_coe
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ)
    (K : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → L ℋ)
    (h_col : ColumnOrthogonal (ℋ := ℋ) K) :
    (naimarkUnitary b K h_col : L (ℋ ⊗[ℂ] ℋ)) =
      naimarkLinearMap (ℋ := ℋ) b K := rfl

/-! ### Helpers: `outer_product` and `Tr₂ ∘ TensorProduct.map` -/

omit [Nontrivial ℋ] in
/-- Evaluation of `outer_product`: `(outer_product u v) x = ⟨u, x⟩ • v`. -/
lemma outer_product_apply (u v x : ℋ) :
    outer_product u v x = inner ℂ u x • v := by
  simp [outer_product, dualTensorHom_apply]

omit [Nontrivial ℋ] in
/-- The adjoint of `outer_product u v` is `outer_product v u`. -/
lemma outer_product_adjoint (u v : ℋ) :
    LinearMap.adjoint (outer_product u v) = outer_product v u := by
  refine LinearMap.ext fun y => ?_
  refine ext_inner_left ℂ fun x => ?_
  rw [LinearMap.adjoint_inner_right, outer_product_apply, outer_product_apply,
    inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]

omit [Nontrivial ℋ] in
/-- Composition formula for outer products:
    `(outer u v) ∘ (outer u' v') = ⟨u, v'⟩ • outer u' v`. -/
lemma outer_product_comp_outer_product (u v u' v' : ℋ) :
    (outer_product u v).comp (outer_product u' v') =
      inner ℂ u v' • outer_product u' v := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, outer_product_apply, LinearMap.smul_apply,
    map_smul, smul_smul]
  ring_nf

omit [Nontrivial ℋ] in
/-- Multiplication formula for outer products in `L ℋ`:
    `(outer u v) * (outer u' v') = ⟨u, v'⟩ • outer u' v`. -/
lemma outer_product_mul_outer_product (u v u' v' : ℋ) :
    (outer_product u v) * (outer_product u' v') =
      inner ℂ u v' • outer_product u' v := by
  rw [Module.End.mul_eq_comp, outer_product_comp_outer_product]

omit [Nontrivial ℋ] in
/-- `Tr₂ (TensorProduct.map X Y) = (Tr X) • Y`. -/
lemma Tr₂_TensorProduct_map (X Y : L ℋ) :
    Tr₂ (TensorProduct.map X Y : L (ℋ ⊗[ℂ] ℋ)) = (Tr X) • Y := by
  rw [← l_tensor_equiv_symm_tmul]
  exact Tr₂_l_tensor_equiv_symm_tmul X Y

/-! ### Tensor decomposition of `naimarkLinearMap` -/

omit [Nontrivial ℋ] in
/-- Tensor decomposition of `naimarkLinearMap` into a sum of
    `TensorProduct.map`s, one per index `(l, i)`. This is the key
    structural identity used to compute the partial trace. -/
lemma naimarkLinearMap_eq_sum_map
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ)
    (K : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → L ℋ) :
    naimarkLinearMap (ℋ := ℋ) b K =
      ∑ p : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ),
        TensorProduct.map (outer_product (b p.2) (b p.1)) (K p) := by
  refine TensorProduct.ext' fun x ψ => ?_
  rw [LinearMap.sum_apply]
  unfold naimarkLinearMap
  rw [TensorProduct.lift.tmul, LinearMap.mk₂_apply]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [TensorProduct.map_tmul, outer_product_apply, OrthonormalBasis.repr_apply_apply,
    TensorProduct.smul_tmul']

omit [Nontrivial ℋ] in
/-- Tensor decomposition of the *adjoint* of `naimarkLinearMap`. -/
lemma naimarkLinearMap_adjoint_eq_sum
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ)
    (K : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → L ℋ) :
    LinearMap.adjoint (naimarkLinearMap (ℋ := ℋ) b K) =
      ∑ p : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ),
        TensorProduct.map
          (outer_product (b p.1) (b p.2)) (LinearMap.adjoint (K p)) := by
  rw [naimarkLinearMap_eq_sum_map b K, map_sum]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [TensorProduct.adjoint_map, outer_product_adjoint]

omit [Nontrivial ℋ] in
theorem naimarkUnitary_partialTrace_eq
    (b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ)
    (K : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → L ℋ)
    (h_col : ColumnOrthogonal (ℋ := ℋ) K) (γ : L ℋ) :
    Tr₂ ((naimarkUnitary b K h_col : L (ℋ ⊗[ℂ] ℋ)) *
        TensorProduct.map
          (((Module.finrank ℂ ℋ : ℂ)⁻¹) • (1 : L ℋ)) γ *
        star (naimarkUnitary b K h_col : L (ℋ ⊗[ℂ] ℋ))) =
      ((Module.finrank ℂ ℋ : ℂ)⁻¹) •
        (∑ α : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ),
          (K α).comp (γ.comp (LinearMap.adjoint (K α)))) := by
  classical
  rw [show (naimarkUnitary b K h_col : L (ℋ ⊗[ℂ] ℋ)) =
        naimarkLinearMap (ℋ := ℋ) b K from rfl]
  rw [show star (naimarkLinearMap (ℋ := ℋ) b K) =
        LinearMap.adjoint (naimarkLinearMap (ℋ := ℋ) b K) from rfl]
  -- Expand adjoint first, then the remaining occurrence.
  rw [naimarkLinearMap_adjoint_eq_sum b K, naimarkLinearMap_eq_sum_map b K]
  rw [Finset.sum_mul, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [map_sum]
  simp_rw [map_sum, ← TensorProduct.map_mul, Tr₂_TensorProduct_map]
  simp_rw [Algebra.mul_smul_comm, mul_one, Algebra.smul_mul_assoc,
    outer_product_mul_outer_product, smul_smul, map_smul, smul_eq_mul,
    trace_outer_product, OrthonormalBasis.inner_eq_ite]
  -- Convert RHS .comp to *.
  have hcomp_to_mul : ∀ α : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ),
      (K α) ∘ₗ γ ∘ₗ LinearMap.adjoint (K α) =
        (K α) * γ * (LinearMap.adjoint (K α)) := by
    intro α
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.comp_assoc]
  simp_rw [hcomp_to_mul]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [Finset.sum_eq_single p]
  · -- value at q = p
    simp [mul_assoc]
  · -- value at q ≠ p
    intro q _ hqp
    -- Coefficient is `(d⁻¹) * (if p.2 = q.2 then 1 else 0) * (if q.1 = p.1 then 1 else 0)`.
    -- It is zero since q ≠ p implies p.2 ≠ q.2 or q.1 ≠ p.1.
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h2 => hqp (Prod.ext h1.symm h2.symm)
      simp [h2]
    · have h1' : q.1 ≠ p.1 := fun h => h1 h.symm
      simp [h1']
  · intro hp
    exact (hp (Finset.mem_univ _)).elim

omit [Nontrivial ℋ] in
theorem column_orthogonal_to_unitary_dilation
    (K : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → L ℋ)
    (h_col_orth : ColumnOrthogonal (ℋ := ℋ) K) :
    ∃ U : unitary (L (ℋ ⊗[ℂ] ℋ)), ∀ γ : L ℋ,
      Tr₂ ((U : L (ℋ ⊗[ℂ] ℋ)) *
          TensorProduct.map
            (((Module.finrank ℂ ℋ : ℂ)⁻¹) • (1 : L ℋ)) γ *
          star (U : L (ℋ ⊗[ℂ] ℋ))) =
        ((Module.finrank ℂ ℋ : ℂ)⁻¹) •
          (∑ α : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ),
            (K α).comp (γ.comp (LinearMap.adjoint (K α)))) := by
  let b : OrthonormalBasis (Fin (Module.finrank ℂ ℋ)) ℂ ℋ := stdOrthonormalBasis ℂ ℋ
  refine ⟨naimarkUnitary b K h_col_orth, ?_⟩
  intro γ
  exact naimarkUnitary_partialTrace_eq b K h_col_orth γ

/-! ### Square-index case: assembled from Step 2 and Step 3–4 -/

/-- **Naimark column-orthogonal extension for a *padded* family.**

    Specialization of `exists_naimark_unitary_dilation` to the case
    where the index set is exactly `Fin d × Fin d` (no padding needed).
    The general case reduces to this one via the `padded` construction
    of Step 1.

    Assembled from `exists_column_orthogonal_kraus_equivalent` (Step 2)
    and `column_orthogonal_to_unitary_dilation` (Steps 3–4), together
    with the cancellation `d · d⁻¹ = 1`. The only remaining `sorry` is
    inside `exists_column_orthogonal_kraus_equivalent`. -/
theorem exists_naimark_unitary_dilation_square
    (B : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ) → L ℋ)
    (hSumBB :
      (∑ α : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ),
        (LinearMap.adjoint (B α)).comp (B α)) = (1 : L ℋ)) :
    ∃ U : unitary (L (ℋ ⊗[ℂ] ℋ)), ∀ γ : L ℋ,
      (∑ α : Fin (Module.finrank ℂ ℋ) × Fin (Module.finrank ℂ ℋ),
        (B α).comp (γ.comp (LinearMap.adjoint (B α)))) =
        Tr₂ ((U : L (ℋ ⊗[ℂ] ℋ)) *
            TensorProduct.map
              (((Module.finrank ℂ ℋ : ℂ)⁻¹) • (1 : L ℋ)) γ *
            star (U : L (ℋ ⊗[ℂ] ℋ))) := by
  -- Step 2: operator Gram–Schmidt produces a column-orthogonal family
  -- `K` whose channel scales `Σ B γ B*` by a factor of `d`.
  obtain ⟨K, h_col, h_eq⟩ :=
    exists_column_orthogonal_kraus_equivalent (ℋ := ℋ) B hSumBB
  -- Step 3–4: the column-orthogonal `K` yields a unitary `U` whose
  -- partial trace with the maximally mixed state realizes
  -- `(1/d) · Σ K γ K*`.
  obtain ⟨U, hU⟩ :=
    column_orthogonal_to_unitary_dilation (ℋ := ℋ) K h_col
  refine ⟨U, fun γ => ?_⟩
  -- Combine: `Tr₂[...] = (1/d) Σ K γ K* = (1/d) · d · Σ B γ B* = Σ B γ B*`.
  rw [hU γ, h_eq γ]
  have hd_ne_c : ((Module.finrank ℂ ℋ : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [smul_smul, inv_mul_cancel₀ hd_ne_c, one_smul]

/-- **Naimark column-orthogonal extension (existence) — general case.**

    Given a finite Kraus family `A : κ → L ℋ` on a finite-dimensional
    qudit `ℋ` of dimension `d := finrank ℂ ℋ` with
      `Σ_a A_a* A_a = I_ℋ`
    and the size bound `|κ| ≤ d²`, there exists a unitary
    `U ∈ unitary (L (ℋ ⊗ ℋ))` realizing the channel
      `γ ↦ Σ_a A_a γ A_a*`
    as the partial trace of `U ((I/d) ⊗ γ) U*` over the *first*
    (environment) factor:
      `Σ_a A_a γ A_a* = Tr₂ (U · ((I/d) ⊗ γ) · U*)`.

    This is the *unitary form* of the Stinespring/Watrous Cor. 2.27
    dilation with a maximally mixed environment state.

    **Implementation.** Step 1 (padding) is fully discharged inline
    using `padded`, `sum_padded_adjoint_comp`, and
    `sum_padded_channel_eq`; the result is reduced to the square-index
    case `exists_naimark_unitary_dilation_square`. The only remaining
    `sorry` is the operator-valued Gram–Schmidt of Step 2 (see
    `exists_column_orthogonal_kraus_equivalent`). -/
theorem exists_naimark_unitary_dilation
    {κ : Type*} [Fintype κ]
    (A : κ → L ℋ)
    (hSumAA : (∑ a : κ, (LinearMap.adjoint (A a)).comp (A a)) = (1 : L ℋ))
    (hκ_card_le :
      Fintype.card κ ≤ Module.finrank ℂ ℋ * Module.finrank ℂ ℋ) :
    ∃ U : unitary (L (ℋ ⊗[ℂ] ℋ)), ∀ γ : L ℋ,
      (∑ a : κ, (A a).comp (γ.comp (LinearMap.adjoint (A a)))) =
        Tr₂ ((U : L (ℋ ⊗[ℂ] ℋ)) *
            TensorProduct.map
              (((Module.finrank ℂ ℋ : ℂ)⁻¹) • (1 : L ℋ)) γ *
            star (U : L (ℋ ⊗[ℂ] ℋ))) := by
  classical
  -- Step 1: pad `A : κ → L ℋ` to `B : Fin d × Fin d → L ℋ` using an
  -- embedding `j : κ ↪ Fin d × Fin d` (which exists by the cardinality
  -- bound `hκ_card_le`).
  set d : ℕ := Module.finrank ℂ ℋ with hd_def
  obtain ⟨j⟩ : Nonempty (κ ↪ Fin d × Fin d) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa [Fintype.card_prod, Fintype.card_fin] using hκ_card_le
  set B : Fin d × Fin d → L ℋ := padded j A with hB_def
  -- Step 1 (continued): the padded family inherits the resolution of
  -- identity and channel.
  have hSumBB :
      (∑ α : Fin d × Fin d, (LinearMap.adjoint (B α)).comp (B α)) =
        (1 : L ℋ) := by
    simpa [hB_def] using
      (sum_padded_adjoint_comp (ℋ := ℋ) j A).trans hSumAA
  have hChan : ∀ γ : L ℋ,
      (∑ a : κ, (A a).comp (γ.comp (LinearMap.adjoint (A a)))) =
        ∑ α : Fin d × Fin d, (B α).comp (γ.comp (LinearMap.adjoint (B α))) := by
    intro γ
    simpa [hB_def] using
      (sum_padded_channel_eq (ℋ := ℋ) j A γ).symm
  -- Steps 2–4: reduce to the square-index case, which contains the
  -- focused remaining `sorry`.
  obtain ⟨U, hU⟩ := exists_naimark_unitary_dilation_square (ℋ := ℋ) B hSumBB
  refine ⟨U, fun γ => ?_⟩
  rw [hChan γ, hU γ]

end NaimarkExtension
