import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.SandwichedRenyiBase.NonNeg.Continuity
import Quantum.QuantumEntropy.TensorCFCLMCompat.GSLCore
import Quantum.QuantumEntropy.Common.OperatorCFC


open scoped Quantum.TraceInequality.Loewner

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

private lemma s14_rpow_conj_tendsto_faithful_clm
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα_gt : 1 < α) {A B : ℋ →L[ℂ] ℋ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hsupp : SupportLE (B : L ℋ) (A : L ℋ))
    {cσ cρ : ℝ} (hcσ : 0 < cσ) (hcρ : 0 ≤ cρ) :
    Filter.Tendsto
      (fun lam : ℝ =>
        CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ))
          ((1-α)/(2*α))
          * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ))
          * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ))
            ((1-α)/(2*α)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (CFC.rpow A ((1-α)/(2*α)) * B * CFC.rpow A ((1-α)/(2*α)))) := by
  classical
  set β : ℝ := (1-α)/(2*α) with hβ
  have hαpos : 0 < α := by linarith
  have hβneg : β < 0 := by
    rw [hβ]; apply div_neg_of_neg_of_pos (by linarith) (by positivity)
  have h2β : (1:ℝ) + 2*β = 1/α := by rw [hβ]; field_simp; ring
  have hα_inv_pos : (0:ℝ) < 1/α := one_div_pos.mpr hαpos
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  have hA_pos : A.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive A).mp hA
  have hA_sym : A.IsSymmetric := hA_pos.isSymmetric
  have hB_sym : B.IsSymmetric := ((ContinuousLinearMap.nonneg_iff_isPositive B).mp hB).isSymmetric
  change LinearMap.ker (A : L ℋ) ≤ LinearMap.ker (B : L ℋ) at hsupp
  set b := hA_sym.eigenvectorBasis hn with hb
  set eig := hA_sym.eigenvalues hn with heig
  have h_eig_nn : ∀ i, 0 ≤ eig i := fun i => hA_pos.toLinearMap.nonneg_eigenvalues hn i
  have h_eig_apply : ∀ i, A (b i) = ((eig i : ℝ):ℂ) • b i :=
    hA_sym.apply_eigenvectorBasis hn
  have h_supp_zero : ∀ i j, (eig i = 0 ∨ eig j = 0) → inner ℂ (b j) (B (b i)) = (0:ℂ)
    := by
    exact fun i j hij =>
      QuantumChannel.inner_apply_eq_zero_of_ker_le hB_sym b eig h_eig_apply hsupp hij
  -- eigenvalue of the perturbed operator `Pσ λ`.
  set ν : ℝ → Fin n → ℝ := fun lam i => (1-lam)*eig i + lam*cσ with hν
  have hPσ_app : ∀ (lam : ℝ) k,
      (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ)) (b k) = ((ν lam k
        : ℝ):ℂ) • b k := by
    intro lam k
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, h_eig_apply k,
      ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, smul_smul, ← add_smul, hν]
    push_cast; ring_nf
  have hν_le : ∀ (lam : ℝ), 0 < lam → lam ≤ 1 → ∀ k, lam*cσ ≤ ν lam k := by
    intro lam hlam0 hlam1 k
    rw [hν]
    linarith [mul_nonneg (show 0 ≤ 1 - lam by linarith) (h_eig_nn k)]
  have hM0 : ∀ i, (CFC.rpow A β * B * CFC.rpow A β) (b i)
      = ∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j := by
    intro i; simpa using rpow_conj_affine_apply_eigenbasis b hA eig h_eig_apply β 1 0 i
  -- per-λ formula for `Pσ^β Pρ Pσ^β (b i)`.
  have hMlam : ∀ (lam : ℝ), 0 < lam → lam ≤ 1 → ∀ i,
      (CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ)) β
        * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ))
        * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ)) β) (b i)
      = (∑ j, (((1-lam : ℝ):ℂ) * (((ν lam i)^β * (ν lam j)^β : ℝ):ℂ)
            * inner ℂ (b j) (B (b i))) • b j)
        + (((lam*cρ * ((ν lam i)^β)^2 : ℝ)):ℂ) • b i := by
    intro lam hlam0 hlam1 i
    have hPσ_nn : (0 : ℋ →L[ℂ] ℋ) ≤
        ((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ) :=
      add_nonneg (smul_nonneg (Complex.zero_le_real.mpr (by linarith)) hA)
        (smul_nonneg (Complex.zero_le_real.mpr (by positivity)) zero_le_one)
    exact rpow_conj_affine_apply_eigenbasis b hPσ_nn (ν lam) (hPσ_app lam)
      β (1 - lam) (lam * cρ) i
  -- `ν lam k → eig k` as `λ → 0⁺`.
  have hν_tendsto : ∀ k, Filter.Tendsto (fun lam : ℝ => ν lam k)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (eig k)) := by
    intro k
    have hcont : Continuous (fun lam : ℝ => ν lam k) := by rw [hν]; fun_prop
    simpa [hν] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hIio : Set.Iio (1 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
  -- extra-term scalar `λ·cρ·(ν λ i)^{2β} → 0`.
  have hextra : ∀ i, Filter.Tendsto (fun lam : ℝ => (((lam*cρ * ((ν lam i)^β)^2 : ℝ))
    : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro i
    apply singular_rpow_sq_tendsto (by linarith [hβneg]) h2β hα_inv_pos hcσ hcρ
      (fun lam => ν lam i)
    filter_upwards [self_mem_nhdsWithin, hIio] with lam hlam hlam1
    exact hν_le lam hlam (le_of_lt hlam1) i
  -- per-i vector convergence.
  have key : ∀ i, Filter.Tendsto
      (fun lam : ℝ =>
        (CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ)) β
          * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ))
          * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ)) β)
            (b i))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((CFC.rpow A β * B * CFC.rpow A β) (b i))) := by
    intro i
    rw [hM0 i]
    have hEq : (fun lam : ℝ =>
        (CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ)) β
          * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ))
          * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:ℋ →L[ℂ] ℋ)) β)
            (b i))
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun lam => (∑ j, (((1-lam : ℝ):ℂ) * (((ν lam i)^β * (ν lam j)^β : ℝ):ℂ)
            * inner ℂ (b j) (B (b i))) • b j)
          + (((lam*cρ * ((ν lam i)^β)^2 : ℝ)):ℂ) • b i) := by
      filter_upwards [self_mem_nhdsWithin, hIio] with lam hlam hlam1
      exact hMlam lam hlam (le_of_lt hlam1) i
    refine Filter.Tendsto.congr' hEq.symm ?_
    rw [show (∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j)
        = (∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j)
          + (0:ℋ) from
        (add_zero _).symm]
    apply Filter.Tendsto.add
    · apply tendsto_finset_sum
      intro j _
      by_cases hzero : eig i = 0 ∨ eig j = 0
      · have hin0 := h_supp_zero i j hzero
        rw [hin0]
        simp only [mul_zero, zero_smul]
        exact tendsto_const_nhds
      · obtain ⟨hi, hj⟩ := not_or.mp hzero
        have hsc : Filter.Tendsto
            (fun lam : ℝ => ((1-lam : ℝ):ℂ) * (((ν lam i)^β * (ν lam j)^β : ℝ):ℂ)
              * inner ℂ (b j) (B (b i)))
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i)))) := by
          have hone : Filter.Tendsto (fun lam : ℝ => ((1-lam : ℝ):ℂ))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
            have hc : Continuous (fun lam : ℝ => ((1-lam : ℝ):ℂ)) := by fun_prop
            simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
          exact tendsto_rpow_pair_coeff hν_tendsto _ hone hi hj
            (inner ℂ (b j) (B (b i)))
        simpa using hsc.smul_const (b j)
    · rw [show (0:ℋ) = (0:ℂ) • b i from (zero_smul ℂ (b i)).symm]
      exact (hextra i).smul_const (b i)
  exact tendsto_continuousLinearMap_of_apply_orthonormalBasis b _ _ key

theorem rpow_conj_tendsto_faithful_gt :
∀ {H : Type u} [Qudit H] [Nontrivial H]
  {α : ℝ} {A B : L H}, 1 < α → 0 ≤ A → 0 ≤ B → SupportLE B A →
  ∀ {cσ cρ : ℝ}, 0 < cσ → 0 ≤ cρ →
  Filter.Tendsto
    (fun lam : ℝ =>
      CFC.rpow (((1 - lam : ℝ) : ℂ) • A + ((lam * cσ : ℝ) : ℂ) • (1 : L H))
        ((1 - α) / (2 * α)) *
      (((1 - lam : ℝ) : ℂ) • B + ((lam * cρ : ℝ) : ℂ) • (1 : L H)) *
      CFC.rpow (((1 - lam : ℝ) : ℂ) • A + ((lam * cσ : ℝ) : ℂ) • (1 : L H))
        ((1 - α) / (2 * α)))
    (𝓝[>] (0 : ℝ))
    (𝓝 (CFC.rpow A ((1 - α) / (2 * α)) * B *
      CFC.rpow A ((1 - α) / (2 * α)))) := by
  intro H _ _ α A B hα hA hB hsupp cσ cρ hcσ hcρ
  have hAc : (0 : QuantumState.B H) ≤ A.toContinuousLinearMap :=
    (ContinuousLinearMap.coe_le_coe_iff _ _).mp hA
  have hBc : (0 : QuantumState.B H) ≤ B.toContinuousLinearMap :=
    (ContinuousLinearMap.coe_le_coe_iff _ _).mp hB
  have h := s14_rpow_conj_tendsto_faithful_clm hα hAc hBc hsupp hcσ hcρ
  have hc : Continuous (fun T : QuantumState.B H => T.toLinearMap) :=
    (StarAlgEquiv.isometry (linearToContinuousEndStarAlgEquiv H).symm).continuous
  have ht := (hc.tendsto _).comp h
  have hrpow (T : QuantumState.B H) (p : ℝ) :
      (CFC.rpow T p).toLinearMap = CFC.rpow T.toLinearMap p :=
    TensorCFC.rpow_toLinearMap_lm T p
  simpa only [Function.comp_def, ContinuousLinearMap.coe_mul,
    ContinuousLinearMap.coe_add, ContinuousLinearMap.coe_smul,
    hrpow] using ht

end RenyiDPI
