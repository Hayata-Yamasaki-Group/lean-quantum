import Quantum.QuantumEntropy.Common.Support

namespace SandwichedRenyiRelativeEntropy

open GeneralizedPerspectiveFunction QuantumState QuantumChannel MeasureTheory TensorProduct
open scoped ComplexOrder NNReal Topology

universe u

/-- For non-negative `ρ, σ` in finite dimension with `ker σ ≤ ker ρ`, there
    exists `lam > 0` with `ρ ≤ lam • σ`.

    **Proof**: Case split on `σ = 0` (then `ρ = 0` by `SupportLE`) vs `σ ≠ 0`.
    For `σ ≠ 0`, use the spectral decomposition of `σ`: let `b` be an orthonormal
    eigenbasis with eigenvalues `eig i ≥ 0`. Let `S = {i | eig i > 0}` (nonempty
    since `σ ≠ 0`) and `s_min = min over S of eig`. By `SupportLE`, `ρ` annihilates
    eigenvectors with zero eigenvalue. Then for any `x`, expanding in the eigenbasis,
    `re ⟨x, ρ x⟩ ≤ ‖ρ‖ · ∑_{i ∈ S} |⟨b i, x⟩|² ≤ (‖ρ‖ / s_min) ·
      re ⟨x, σ x⟩`.
    Hence `ρ ≤ (‖ρ‖ / s_min + 1) • σ`.

    **Status**: Fully proven. -/
lemma nonneg_le_smul_of_suppLE
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (h : SupportLE ρ σ) :
    ∃ lam > (0 : ℝ), ρ ≤ (lam : ℂ) • σ := by
  by_cases hσ_zero : σ = 0
  · -- `σ = 0`: then `ker σ = ⊤`, by `SupportLE` also `ker ρ = ⊤`, so `ρ = 0`.
    -- Take `lam = 1`.
    have hker_σ : LinearMap.ker σ = ⊤ := by
      rw [hσ_zero]
      exact LinearMap.ker_zero
    have hker_ρ : LinearMap.ker ρ = ⊤ := eq_top_iff.mpr (hker_σ ▸ h)
    have hρ_zero : ρ = 0 := by
      ext x
      have : x ∈ LinearMap.ker ρ := by rw [hker_ρ]; trivial
      exact this
    exact ⟨1, one_pos, by rw [hρ_zero, hσ_zero]; simp⟩
  · -- `σ ≠ 0`: spectral argument.
    classical
    have hρ_pos : ρ.IsPositive := (LinearMap.nonneg_iff_isPositive ρ).mp hρ
    have hσ_pos : σ.IsPositive := (LinearMap.nonneg_iff_isPositive σ).mp hσ
    have hσ_sym : σ.IsSymmetric := hσ_pos.isSymmetric
    have hρ_sym : ρ.IsSymmetric := hρ_pos.isSymmetric
    set n := Module.finrank ℂ ℋ with hn_def
    have hn : Module.finrank ℂ ℋ = n := rfl
    set b : OrthonormalBasis (Fin n) ℂ ℋ := hσ_sym.eigenvectorBasis hn with hb_def
    set eig : Fin n → ℝ := hσ_sym.eigenvalues hn with heig_def
    have h_eig_nn : ∀ i, (0:ℝ) ≤ eig i :=
      fun i => hσ_pos.nonneg_eigenvalues hn i
    have h_eig_apply : ∀ i, σ (b i) = ((eig i : ℝ) : ℂ) • (b i : ℋ) :=
      hσ_sym.apply_eigenvectorBasis hn
    -- Show ∃ i, 0 < eig i (using σ ≠ 0).
    have h_exists_pos : ∃ i, 0 < eig i := by
      by_contra h_all
      push_neg at h_all
      have h_all_zero : ∀ i, eig i = 0 := fun i => le_antisymm (h_all i) (h_eig_nn i)
      apply hσ_zero
      ext v
      have hv : v = ∑ i, b.repr v i • (b i : ℋ) := (b.sum_repr v).symm
      conv_lhs => rw [hv]
      rw [map_sum]
      refine Finset.sum_eq_zero ?_
      intro i _
      rw [map_smul, h_eig_apply i, h_all_zero i]
      simp
    -- Define `S := {i | 0 < eig i}` and `s_min := min over S`.
    set S : Finset (Fin n) := Finset.univ.filter (fun i => 0 < eig i) with hS_def
    have hS_nonempty : S.Nonempty := by
      obtain ⟨i, hi⟩ := h_exists_pos
      exact ⟨i, by simp [S, hi]⟩
    set s_min : ℝ := S.inf' hS_nonempty eig with hs_min_def
    have hs_min_pos : 0 < s_min := by
      apply (Finset.lt_inf'_iff hS_nonempty).mpr
      intro j hj
      exact (Finset.mem_filter.mp hj).2
    have hs_min_le : ∀ i ∈ S, s_min ≤ eig i := fun i hi => Finset.inf'_le _ hi
    -- Characterize membership in S: `i ∈ S ↔ 0 < eig i ↔ eig i ≠ 0`.
    have h_mem_S : ∀ i, i ∈ S ↔ eig i ≠ 0 := by
      intro i
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hi; exact ne_of_gt hi
      · intro hi
        rcases eq_or_lt_of_le (h_eig_nn i) with h_eq | h_lt
        · exact absurd h_eq.symm hi
        · exact h_lt
    -- For `i ∉ S`, `ρ (b i) = 0` (from `SupportLE`).
    have h_ρ_ker : ∀ i, i ∉ S → ρ (b i) = 0 := by
      intro i hi
      have h_eig_i_zero : eig i = 0 := by
        simpa using (not_congr (h_mem_S i)).mp hi
      have h_σ_bi : σ (b i) = 0 := by
        rw [h_eig_apply i, h_eig_i_zero]; simp
      have h_bi_ker : b i ∈ LinearMap.ker σ := h_σ_bi
      exact h h_bi_ker
    -- Set `lam := ‖ρ‖ / s_min + 1`.
    refine ⟨‖ρ‖ / s_min + 1, by positivity, ?_⟩
    -- Show `ρ ≤ lam • σ` via `IsPositive (lam • σ - ρ)`.
    rw [← sub_nonneg, LinearMap.nonneg_iff_isPositive]
    refine ⟨?_, ?_⟩
    · -- Symmetry of `lam • σ - ρ`.
      exact (hσ_sym.smul (by simp)).sub hρ_sym
    · -- `0 ≤ re ⟨(lam • σ - ρ) x, x⟩` for all x.
      intro x
      -- Step 1: `⟨b i, σ x⟩ = eig i * ⟨b i, x⟩`.
      have h_σ_inner : ∀ i, inner ℂ (b i : ℋ) (σ x) =
          ((eig i : ℝ) : ℂ) * inner ℂ (b i : ℋ) x := by
        intro i
        have h1 : inner ℂ (b i : ℋ) (σ x) = inner ℂ (σ (b i)) x := (hσ_sym (b i) x).symm
        rw [h1, h_eig_apply i, inner_smul_left, Complex.conj_ofReal]
      -- Step 2: `re ⟨x, σ x⟩ = ∑ i, eig i * ‖⟨b i, x⟩‖²`.
      have h_re_σ : RCLike.re (inner ℂ x (σ x)) =
          ∑ i, eig i * ‖inner ℂ (b i : ℋ) x‖^2 := by
        rw [← b.sum_inner_mul_inner x (σ x), map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [h_σ_inner i]
        rw [show inner ℂ x (b i : ℋ) =
              (starRingEnd ℂ) (inner ℂ (b i : ℋ) x) from (inner_conj_symm x (b i : ℋ)).symm]
        rw [show (starRingEnd ℂ) (inner ℂ (b i : ℋ) x) *
              (((eig i : ℝ) : ℂ) * inner ℂ (b i : ℋ) x) =
              ((eig i : ℝ) : ℂ) *
                ((starRingEnd ℂ) (inner ℂ (b i : ℋ) x) * inner ℂ (b i : ℋ) x) by ring]
        rw [show (starRingEnd ℂ) (inner ℂ (b i : ℋ) x) * inner ℂ (b i : ℋ) x =
              ((‖inner ℂ (b i : ℋ) x‖^2 : ℝ) : ℂ) by
                rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]]
        rw [show ((eig i : ℝ) : ℂ) * ((‖inner ℂ (b i : ℋ) x‖^2 : ℝ) : ℂ) =
              ((eig i * ‖inner ℂ (b i : ℋ) x‖^2 : ℝ) : ℂ) by push_cast; ring]
        exact Complex.ofReal_re _
      -- Step 3: each term in re ⟨x, σ x⟩ is nonneg, so re ⟨x, σ x⟩ ≥ 0 and
      -- the sum restricted to S is bounded: s_min * (∑ S terms) ≤ re ⟨x, σ x⟩.
      have h_sum_S_le : s_min * (∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2) ≤
          RCLike.re (inner ℂ x (σ x)) := by
        rw [h_re_σ, Finset.mul_sum]
        -- ∑ i ∈ S, s_min * ‖⟨b i, x⟩‖² ≤ ∑ i, eig i * ‖⟨b i, x⟩‖²
        have h_le_full : (∑ i ∈ S, s_min * ‖inner ℂ (b i : ℋ) x‖^2) ≤
            ∑ i ∈ S, eig i * ‖inner ℂ (b i : ℋ) x‖^2 := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_mul_of_nonneg_right (hs_min_le i hi) (sq_nonneg _)
        refine h_le_full.trans ?_
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        intros j _ hj
        rw [show eig j = 0 from by
          by_contra h_ne; exact hj ((h_mem_S j).mpr h_ne)]
        simp
      -- Step 4: bound `re ⟨ρ x, x⟩ ≤ ‖ρ‖ * ∑ i ∈ S, ‖⟨b i, x⟩‖²`.
      -- Define xS := ∑ i ∈ S, ⟨b i, x⟩ • b i.
      set xS : ℋ := ∑ i ∈ S, inner ℂ (b i : ℋ) x • (b i : ℋ) with hxS_def
      have hx_decomp : x = ∑ i, inner ℂ (b i : ℋ) x • (b i : ℋ) :=
        (b.sum_repr' x).symm
      -- `ρ x = ρ xS` (using `h_ρ_ker`).
      have h_ρ_x_eq : ρ x = ρ xS := by
        rw [hx_decomp, map_sum, hxS_def, map_sum]
        refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
        intros i _ hi
        rw [map_smul, h_ρ_ker i hi, smul_zero]
      -- `inner ℂ (ρ x) x = inner ℂ (ρ xS) xS`:
      -- use orthogonality `⟨ρ xS, b i⟩ = ⟨xS, ρ b i⟩ = 0` for `i ∉ S`.
      have h_inner_ρ_eq : inner ℂ (ρ x) x = inner ℂ (ρ xS) xS := by
        calc
          inner ℂ (ρ x) x = inner ℂ (ρ xS) x := by rw [h_ρ_x_eq]
          _ = inner ℂ xS (ρ x) := hρ_sym xS x
          _ = inner ℂ xS (ρ xS) := by rw [h_ρ_x_eq]
          _ = inner ℂ (ρ xS) xS := (hρ_sym xS xS).symm
      -- Operator-norm bound: `re ⟨ρ xS, xS⟩ ≤ ‖ρ‖ * ‖xS‖²`.
      have h_op_bound : RCLike.re (inner ℂ (ρ xS) xS) ≤ ‖ρ‖ * ‖xS‖^2 := by
        have h1 : RCLike.re (inner ℂ (ρ xS) xS) ≤ ‖inner ℂ (ρ xS) xS‖ :=
          RCLike.re_le_norm _
        have h2 : ‖inner ℂ (ρ xS) xS‖ ≤ ‖ρ xS‖ * ‖xS‖ := norm_inner_le_norm _ _
        have h3 : ‖ρ xS‖ ≤ ‖ρ‖ * ‖xS‖ := by
          have := ρ.toContinuousLinearMap.le_opNorm xS
          simpa using this
        calc RCLike.re (inner ℂ (ρ xS) xS) ≤ ‖inner ℂ (ρ xS) xS‖ := h1
          _ ≤ ‖ρ xS‖ * ‖xS‖ := h2
          _ ≤ (‖ρ‖ * ‖xS‖) * ‖xS‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
          _ = ‖ρ‖ * ‖xS‖^2 := by ring
      -- ‖xS‖² = ∑ i ∈ S, ‖⟨b i, x⟩‖² (orthonormality + ‖∑ a_i e_i‖² =
      -- ∑ ‖a_i‖²).
      have h_xS_norm_sq : ‖xS‖^2 = ∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2 := by
        rw [hxS_def, @norm_sq_eq_re_inner ℂ, b.orthonormal.inner_sum, map_sum]
        simp only [RCLike.conj_mul]
        norm_cast
      -- Step 5: combine into final inequality `re ⟨(lam • σ - ρ) x, x⟩ ≥ 0`.
      have h_sum_nn : (0 : ℝ) ≤ ∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have h_ρ_bound : RCLike.re (inner ℂ (ρ x) x) ≤
          ‖ρ‖ * ∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2 := by
        rw [h_inner_ρ_eq, ← h_xS_norm_sq]
        exact h_op_bound
      have h_σ_bound : s_min * (∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2) ≤
          RCLike.re (inner ℂ (σ x) x) := by
        rw [show inner ℂ (σ x) x = inner ℂ x (σ x) from hσ_sym x x]
        exact h_sum_S_le
      have h_σ_nn : (0 : ℝ) ≤ RCLike.re (inner ℂ (σ x) x) := hσ_pos.2 x
      have h_ρ_norm_nn : (0 : ℝ) ≤ ‖ρ‖ := norm_nonneg _
      change (0 : ℝ) ≤ RCLike.re
        (inner ℂ ((((‖ρ‖ / s_min + 1 : ℝ) : ℂ) • σ - ρ) x) x)
      have h_unfold_sub : (((‖ρ‖ / s_min + 1 : ℝ) : ℂ) • σ - ρ) x =
          ((‖ρ‖ / s_min + 1 : ℝ) : ℂ) • σ x - ρ x := by
        rw [LinearMap.sub_apply, LinearMap.smul_apply]
      rw [h_unfold_sub, inner_sub_left, inner_smul_left, Complex.conj_ofReal, map_sub]
      have h_re_eq : RCLike.re (((‖ρ‖ / s_min + 1 : ℝ) : ℂ) * inner ℂ (σ x) x) =
          (‖ρ‖ / s_min + 1) * RCLike.re (inner ℂ (σ x) x) := by
        change ((((‖ρ‖ / s_min + 1 : ℝ) : ℂ) * inner ℂ (σ x) x)).re = _
        rw [Complex.re_ofReal_mul]
        rfl
      rw [h_re_eq]
      -- Goal: 0 ≤ (‖ρ‖/s_min + 1) * re ⟨σ x, x⟩ - re ⟨ρ x, x⟩
      have h_combine : RCLike.re (inner ℂ (ρ x) x) ≤
          (‖ρ‖ / s_min + 1) * RCLike.re (inner ℂ (σ x) x) := by
        have h1 : ‖ρ‖ * (∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2) =
            (‖ρ‖ / s_min) * (s_min * (∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2)) := by
          field_simp
        have h2 : (‖ρ‖ / s_min) * (s_min * (∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2)) ≤
            (‖ρ‖ / s_min) * RCLike.re (inner ℂ (σ x) x) :=
          mul_le_mul_of_nonneg_left h_σ_bound (div_nonneg h_ρ_norm_nn hs_min_pos.le)
        have h3 : (‖ρ‖ / s_min) * RCLike.re (inner ℂ (σ x) x) ≤
            (‖ρ‖ / s_min + 1) * RCLike.re (inner ℂ (σ x) x) := by
          have h_le : ‖ρ‖ / s_min ≤ ‖ρ‖ / s_min + 1 := by linarith
          exact mul_le_mul_of_nonneg_right h_le h_σ_nn
        linarith
      linarith

@[deprecated (since := "2026-09-05")]
alias nonneg_apply_eq_zero_of_inner_self_eq_zero :=
  QuantumChannel.nonneg_apply_eq_zero_of_inner_self_eq_zero

@[deprecated (since := "2026-09-05")]
alias nonneg_eq_zero_of_le_of_apply_eq_zero := QuantumChannel.nonneg_eq_zero_of_le_of_apply_eq_zero

end SandwichedRenyiRelativeEntropy
