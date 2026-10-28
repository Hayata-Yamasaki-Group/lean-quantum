import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneSupport

/-!
# Additional support-domain alpha-one leaves

Source: main.tex:219; Müller-Lennert et al. (2013), alpha-one analysis.
This module records proved residual leaves. It does not assert the general
support-domain limit.
-/

open QuantumState QuantumChannel GeneralizedPerspectiveFunction MeasureTheory
open scoped ComplexOrder NNReal Topology UniformConvergence
namespace SandwichedRenyiRelativeEntropy.AlphaOneSupport
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]

/-- A nonzero real exponent kills a zero eigenvector, of either exponent sign. -/
lemma rpow_apply_eq_zero_of_mem_ker {A : L H} (hA : 0 ≤ A) {x : H}
    (hx : x ∈ LinearMap.ker A) {t : ℝ} (ht : t ≠ 0) : CFC.rpow A t x = 0 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have he : A.toContinuousLinearMap x = ((0 : ℝ) : ℂ) • x := by simpa using hx
  change (CFC.rpow A t).toContinuousLinearMap x = 0
  rw [CFCTransport.cfc_rpow_toCLM]
  have hh := TensorCFC.rpow_apply_eigenvector A.toContinuousLinearMap hA t x 0 he
    (TensorCFC.mem_spectrum_real_of_eigenvector hx0 he)
  simpa only [Real.zero_rpow ht, map_zero, zero_smul] using hh


/-- The sandwich remains supported. Zero exponent uses I, not the support projection. -/
lemma sandwich_support {ρ σ : L H} (hσ : 0 ≤ σ) (hsupp : SupportLE ρ σ)
    (t : ℝ) : SupportLE (CFC.rpow σ t * ρ * CFC.rpow σ t) σ := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · intro x hx
    change CFC.rpow σ t (ρ (CFC.rpow σ t x)) = 0
    rw [rpow_apply_eq_zero_of_mem_ker hσ hx (ne_of_lt ht), map_zero, map_zero]
  · rw [ht, show CFC.rpow σ 0 = 1 from CFC.rpow_zero σ hσ, one_mul, mul_one]
    exact hsupp
  · intro x hx
    change CFC.rpow σ t (ρ (CFC.rpow σ t x)) = 0
    rw [rpow_apply_eq_zero_of_mem_ker hσ hx (ne_of_gt ht), map_zero, map_zero]


/-- A continuous extension in the spectral variable, agreeing with x^s log x for x≥0. -/
noncomputable def weightedScalar (s x : ℝ) : ℝ :=
  (|x| ^ s * Real.log (|x| ^ s)) / s

lemma weightedScalar_eq {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) :
    weightedScalar s x = x ^ s * Real.log x := by
  unfold weightedScalar
  rw [abs_of_nonneg hx]
  rcases eq_or_lt_of_le hx with hx | hx
  · subst x
    simp [Real.zero_rpow (ne_of_gt hs)]
  · rw [Real.log_rpow hx]
    field_simp

/-- Zero is included: continuity follows from the globally continuous y log y. -/
lemma continuousAt_weightedScalar {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × ℝ => weightedScalar q.1 q.2) p := by
  have hr : ContinuousAt (fun q : ℝ × ℝ => |q.2| ^ q.1) p :=
    continuousAt_snd.abs.rpow continuousAt_fst (Or.inr hp)
  exact (Real.continuous_mul_log.continuousAt.comp hr).div continuousAt_fst (ne_of_gt hp)

lemma continuous_weightedScalar {s : ℝ} (hs : 0 < s) :
    Continuous (weightedScalar s) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (continuousAt_weightedScalar (p := (s, x)) hs).comp
    (continuousAt_const.prodMk continuousAt_id)

/-- Compact spectral intervals give local uniform convergence as the exponent approaches one. -/
lemma tendstoUniformlyOn_weightedScalar {S : Set ℝ} (hS : IsCompact S) :
    TendstoUniformlyOn weightedScalar (weightedScalar 1) (𝓝 1) S := by
  have hc : ContinuousOn (fun q : ℝ × ℝ => weightedScalar q.1 q.2)
      (Set.Icc (1 / 2 : ℝ) (3 / 2) ×ˢ S) := by
    intro q hq
    exact (continuousAt_weightedScalar (lt_of_lt_of_le (by norm_num) hq.1.1)).continuousWithinAt
  have hu := (isCompact_Icc.prod hS).uniformContinuousOn_of_continuous hc
  have ht := UniformContinuousOn.tendstoUniformlyOn (F := weightedScalar) hu
    (show (1 : ℝ) ∈ Set.Icc (1 / 2) (3 / 2) by norm_num)
  have hn : Set.Icc (1 / 2 : ℝ) (3 / 2) ∈ 𝓝 (1 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  simpa only [nhdsWithin_eq_nhds.mpr hn] using ht

omit [Nontrivial H] in
/-- Weighted logarithm is one CFC; log itself need not be continuous. -/
lemma cfc_weightedScalar_eq {K : B H} (hK : 0 ≤ K) {s : ℝ} (hs : 0 < s) :
    cfc (weightedScalar s) K = CFC.rpow K s * CFC.log K := by
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hK]
  change _ = cfc (fun x : ℝ => x ^ s) K * cfc Real.log K
  rw [← cfc_mul (fun x : ℝ => x ^ s) Real.log K
    ((TensorCFC.spectrum_real_finite K).continuousOn _)
    ((TensorCFC.spectrum_real_finite K).continuousOn _)]
  apply cfc_congr
  intro x hx
  exact weightedScalar_eq (spectrum_nonneg_of_nonneg hK hx) hs


/-- For a fixed PSD matrix the weighted log trace is continuous in all exponents.
Zero eigenvalues contribute zero even at exponent zero, because log 0 = 0. -/
lemma continuous_trace_rpow_log_of_nonneg {K : B H} (hK : 0 ≤ K) :
    Continuous (fun s : ℝ => (Tr ((CFC.rpow K s * CFC.log K : B H) : L H)).re) := by
  classical
  have hpos := (ContinuousLinearMap.nonneg_iff_isPositive K).mp hK
  let b := hpos.isSymmetric.eigenvectorBasis rfl
  let eig := hpos.isSymmetric.eigenvalues rfl
  have heig (i) : K (b i) = (eig i : ℂ) • b i :=
    hpos.isSymmetric.apply_eigenvectorBasis rfl i
  have hnn (i) : 0 ≤ eig i := hpos.toLinearMap.nonneg_eigenvalues rfl i
  have hpow (s : ℝ) (i) : CFC.rpow K s (b i) = ((eig i ^ s : ℝ) : ℂ) • b i :=
    TensorCFC.rpow_apply_eigenvector K hK s (b i) (eig i) (heig i)
      (TensorCFC.mem_spectrum_real_of_eigenvector (b.orthonormal.ne_zero i) (heig i))
  have hlog (i) : CFC.log K (b i) = ((Real.log (eig i) : ℝ) : ℂ) • b i :=
    TensorCFC.cfc_real_apply_eigenvector (IsSelfAdjoint.of_nonneg hK) Real.log (heig i)
      (TensorCFC.mem_spectrum_real_of_eigenvector (b.orthonormal.ne_zero i) (heig i))
  have htrace (s : ℝ) : (Tr ((CFC.rpow K s * CFC.log K : B H) : L H)).re =
      ∑ i, eig i ^ s * Real.log (eig i) := by
    rw [LinearMap.trace_eq_sum_inner
      (T := (CFC.rpow K s * CFC.log K).toLinearMap) b, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (inner ℂ (b i) (CFC.rpow K s (CFC.log K (b i)))).re = _
    rw [hlog, map_smul, hpow, smul_smul, inner_smul_right, b.inner_eq_one, mul_one]
    simp only [← Complex.ofReal_mul, Complex.ofReal_re, mul_comm]
  simp_rw [htrace]
  apply continuous_finset_sum
  intro i _
  rcases eq_or_lt_of_le (hnn i) with hi | hi
  · simp only [← hi, Real.log_zero, mul_zero]
    exact continuous_const
  · rw [continuous_iff_continuousAt]
    intro s
    exact (Real.hasStrictDerivAt_const_rpow hi s).hasDerivAt.continuousAt.mul continuousAt_const

/-- Local FTC: every exponent on [1, alpha] is positive when alpha > 0. -/
lemma trace_rpow_sub_eq_integral_of_nonneg {K : B H} (hK : 0 ≤ K)
    {α : ℝ} (hα : 0 < α) :
    (Tr ((CFC.rpow K α : B H) : L H)).re - (Tr (K : L H)).re =
      ∫ s in (1 : ℝ)..α, (Tr ((CFC.rpow K s * CFC.log K : B H) : L H)).re := by
  have hd : ∀ s ∈ Set.uIcc (1 : ℝ) α,
      HasDerivAt (fun t : ℝ => (Tr ((CFC.rpow K t : B H) : L H)).re)
        (Tr ((CFC.rpow K s * CFC.log K : B H) : L H)).re s := by
    intro s hs
    apply hasDerivAt_trace_rpow_of_nonneg hK
    exact lt_of_lt_of_le (lt_min (by norm_num) hα) hs.1
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_trace_rpow_log_of_nonneg hK).intervalIntegrable 1 α)
  rw [show CFC.rpow K 1 = K from CFC.rpow_one K hK] at ht
  exact ht.symm

/-- Conditional Part A assembly. The open C04 obligation is an explicit hypothesis. -/
lemma hasDerivAt_partA_of_joint_continuity {ρ σ : B H} (hρ : 0 ≤ ρ) (hσ : σ ∈ pdSet)
    (hjoint : ContinuousAt (fun p : ℝ × ℝ =>
      (Tr ((CFC.rpow (CFC.rpow σ ((1 - p.1) / (2 * p.1)) * ρ *
        CFC.rpow σ ((1 - p.1) / (2 * p.1))) p.2 *
        CFC.log (CFC.rpow σ ((1 - p.1) / (2 * p.1)) * ρ *
          CFC.rpow σ ((1 - p.1) / (2 * p.1))) : B H) : L H)).re) (1, 1)) :
    HasDerivAt (fun α =>
      (sandwichedQuasi α (ρ : L H) (σ : L H)).re -
        (Tr ((ρ * CFC.rpow σ ((1 - α) / α) : B H) : L H)).re)
      (Tr ((ρ * CFC.log ρ : B H) : L H)).re 1 := by
  let K : ℝ → B H := fun α => CFC.rpow σ ((1 - α) / (2 * α)) * ρ *
    CFC.rpow σ ((1 - α) / (2 * α))
  have hK (α : ℝ) : 0 ≤ K α := conjugate_nonneg_of_nonneg hρ CFC.rpow_nonneg
  let g : ℝ → ℝ → ℝ := fun α s =>
    (Tr ((CFC.rpow (K α) s * CFC.log (K α) : B H) : L H)).re
  have hK1 : K 1 = ρ := by
    change CFC.rpow σ ((1 - (1 : ℝ)) / (2 * 1)) * ρ *
      CFC.rpow σ ((1 - (1 : ℝ)) / (2 * 1)) = ρ
    rw [show ((1 : ℝ) - 1) / (2 * 1) = 0 by norm_num,
      show CFC.rpow σ 0 = 1 from CFC.rpow_zero σ
        (GeneralizedPerspectiveFunction.isStrictlyPositive_of_pdSet hσ).nonneg, one_mul, mul_one]
  have hg11 : g 1 1 = (Tr ((ρ * CFC.log ρ : B H) : L H)).re := by
    change (Tr ((CFC.rpow (K 1) 1 * CFC.log (K 1) : B H) : L H)).re = _
    rw [hK1, show CFC.rpow ρ 1 = ρ from CFC.rpow_one ρ hρ]
  have hint : ∀ α : ℝ, IntervalIntegrable (g α) volume 1 α := fun α =>
    (continuous_trace_rpow_log_of_nonneg (hK α)).intervalIntegrable 1 α
  have havg := tendsto_average_of_continuousAt (g := g) hjoint hint
  have hF : HasDerivAt (fun α => ∫ s in (1 : ℝ)..α, g α s) (g 1 1) 1 := by
    rw [hasDerivAt_iff_tendsto_slope]
    have he : slope (fun α => ∫ s in (1 : ℝ)..α, g α s) 1 =
        fun α => (α - 1)⁻¹ * ∫ s in (1 : ℝ)..α, g α s := by
      funext α
      rw [slope_def_field, intervalIntegral.integral_same, sub_zero, div_eq_inv_mul]
    rw [he]
    exact havg
  rw [hg11] at hF
  apply hF.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with α hα
  rw [sandwichedQuasi_eq_clm_direct, trace_conj_eq_trace_mul_rpow hσ α]
  exact trace_rpow_sub_eq_integral_of_nonneg (hK α) hα

/-- Conditional C05 assembly, preserving the singular PSD input and using Part B. -/
lemma quasi_derivative_psd_pd_of_joint_continuity {ρ σ : L H} (hρ : 0 ≤ ρ)
    (hσ : σ ∈ pdSetLM)
    (hjoint : ContinuousAt (fun p : ℝ × ℝ =>
      (Tr ((CFC.rpow
        (CFC.rpow σ.toContinuousLinearMap ((1 - p.1) / (2 * p.1)) *
          ρ.toContinuousLinearMap *
          CFC.rpow σ.toContinuousLinearMap ((1 - p.1) / (2 * p.1))) p.2 *
        CFC.log (CFC.rpow σ.toContinuousLinearMap ((1 - p.1) / (2 * p.1)) *
          ρ.toContinuousLinearMap *
          CFC.rpow σ.toContinuousLinearMap ((1 - p.1) / (2 * p.1))) : B H) : L H)).re)
      (1, 1)) :
    HasDerivAt (fun α => (sandwichedQuasi α ρ σ).re)
      (Tr (ρ * (CFC.log ρ - CFC.log σ))).re 1 := by
  have hA := hasDerivAt_partA_of_joint_continuity
    (show 0 ≤ ρ.toContinuousLinearMap from hρ)
    (show σ.toContinuousLinearMap ∈ pdSet from hσ) hjoint
  have hB := hasDerivAt_partB (ρ := ρ.toContinuousLinearMap)
    (show σ.toContinuousLinearMap ∈ pdSet from hσ)
  have ht := hA.add hB
  convert ht using 1
  · funext α
    change (sandwichedQuasi α ρ σ).re =
      ((sandwichedQuasi α ρ σ).re -
        (Tr ((ρ.toContinuousLinearMap *
          CFC.rpow σ.toContinuousLinearMap ((1 - α) / α) : B H) : L H)).re) +
        (Tr ((ρ.toContinuousLinearMap *
          CFC.rpow σ.toContinuousLinearMap ((1 - α) / α) : B H) : L H)).re
    exact (sub_add_cancel _ _).symm
  · rw [← CFCTransport.cfc_log_toCLM ρ, ← CFCTransport.cfc_log_toCLM σ]
    change (Tr (ρ * (CFC.log ρ - CFC.log σ))).re =
      (Tr (ρ * CFC.log ρ)).re + -(Tr (ρ * CFC.log σ)).re
    rw [mul_sub, map_sub, Complex.sub_re, sub_eq_add_neg]



end SandwichedRenyiRelativeEntropy.AlphaOneSupport
