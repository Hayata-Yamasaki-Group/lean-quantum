import Quantum.QuantumEntropy.SandwichedRenyi.Umegaki.AlphaOneLinear

import Quantum.QuantumEntropy.CFCTransport

section EigenvectorTransport
open QuantumState

private lemma rpow_apply_eigenvector_clm_support {ℋ : Type*} [Qudit ℋ]
    (T : B ℋ) (hT : 0 ≤ T) (p : ℝ) (v : ℋ) (μ : ℝ)
    (hv : T v = (algebraMap ℝ ℂ μ) • v) (hμ : μ ∈ spectrum ℝ T) :
    CFC.rpow T p v = (algebraMap ℝ ℂ (μ ^ p)) • v := by
  letI : IsScalarTower ℝ ℂ (B ℋ) := RestrictScalars.isScalarTower ℝ ℂ (B ℋ)
  letI : IsScalarTower ℝ ℂ (L ℋ) := RestrictScalars.isScalarTower ℝ ℂ (L ℋ)
  have hμL : μ ∈ spectrum ℝ (T : L ℋ) := by
    rw [← spectrum.preimage_algebraMap ℂ (R := ℝ)] at hμ ⊢
    simpa only [ContinuousLinearMap.spectrum_eq] using hμ
  have hp := congrArg (fun A : B ℋ => A v)
    (CFCTransport.cfc_rpow_toCLM (T : L ℋ) p)
  change CFC.rpow (T : L ℋ) p v = CFC.rpow T p v at hp
  rw [← hp]
  exact TensorCFC.rpow_apply_eigenvector_linear (T : L ℋ)
    ((ContinuousLinearMap.coe_le_coe_iff _ _).mpr hT) p v μ hv hμL

end EigenvectorTransport

/-!
# Support-domain alpha-one proof leaves

Source: arXiv:2607.05492v1, Section 1.5; Müller-Lennert et al. (2013), alpha-one analysis.
This module proves derivative and compression lemmas for the support domain.
The general limit is proved in AlphaOneSupportLimit.lean as
`tendsto_sandwichedRenyiDiv_umegakiNorm_of_supportLE`.
-/

open QuantumState QuantumChannel GeneralizedPerspectiveFunction
open scoped ComplexOrder NNReal Topology

namespace SandwichedRenyiRelativeEntropy
namespace AlphaOneSupport
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]

/-- The scalar exponent derivative includes the zero eigenvalue at positive exponents. -/
lemma hasDerivAt_scalar_rpow {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => x ^ t) (x ^ s * Real.log x) s := by
  rcases eq_or_lt_of_le hx with hx | hx
  · subst x
    simp only [Real.log_zero, mul_zero]
    refine (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_gt_nhds hs] with t ht
    exact Real.zero_rpow (ne_of_gt ht)
  · exact (Real.hasStrictDerivAt_const_rpow hx s).hasDerivAt

/-- The fixed-base trace-power derivative for a possibly singular PSD operator. -/
lemma hasDerivAt_trace_rpow_of_nonneg {K : B H} (hK : 0 ≤ K) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => (Tr ((CFC.rpow K t : B H) : L H)).re)
      (Tr ((CFC.rpow K s * CFC.log K : B H) : L H)).re s := by
  classical
  have hpos := (ContinuousLinearMap.nonneg_iff_isPositive K).mp hK
  let b := hpos.isSymmetric.eigenvectorBasis rfl
  let eig := hpos.isSymmetric.eigenvalues rfl
  have heig (i) : K (b i) = (eig i : ℂ) • b i :=
    hpos.isSymmetric.apply_eigenvectorBasis rfl i
  have hnn (i) : 0 ≤ eig i := hpos.toLinearMap.nonneg_eigenvalues rfl i
  have hpow (t : ℝ) (i) : CFC.rpow K t (b i) = ((eig i ^ t : ℝ) : ℂ) • b i :=
    rpow_apply_eigenvector_clm_support K hK t (b i) (eig i) (heig i)
      (TensorCFC.mem_spectrum_real_of_eigenvector (b.orthonormal.ne_zero i) (heig i))
  have hlog (i) : CFC.log K (b i) = ((Real.log (eig i) : ℝ) : ℂ) • b i :=
    TensorCFC.cfc_real_apply_eigenvector (IsSelfAdjoint.of_nonneg hK) Real.log (heig i)
      (TensorCFC.mem_spectrum_real_of_eigenvector (b.orthonormal.ne_zero i) (heig i))
  have htrace (t : ℝ) : (Tr ((CFC.rpow K t : B H) : L H)).re = ∑ i, eig i ^ t := by
    rw [LinearMap.trace_eq_sum_inner (T := (CFC.rpow K t).toLinearMap) b, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (inner ℂ (b i) (CFC.rpow K t (b i))).re = _
    rw [hpow, inner_smul_right, b.inner_eq_one, mul_one, Complex.ofReal_re]
  have htraceLog : (Tr ((CFC.rpow K s * CFC.log K : B H) : L H)).re =
      ∑ i, eig i ^ s * Real.log (eig i) := by
    rw [LinearMap.trace_eq_sum_inner
      (T := (CFC.rpow K s * CFC.log K).toLinearMap) b, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (inner ℂ (b i) (CFC.rpow K s (CFC.log K (b i)))).re = _
    rw [hlog, map_smul, hpow, smul_smul, inner_smul_right, b.inner_eq_one, mul_one]
    simp only [← Complex.ofReal_mul, Complex.ofReal_re, mul_comm]
  simp_rw [htrace, htraceLog]
  exact HasDerivAt.fun_sum fun i _ => hasDerivAt_scalar_rpow (hnn i) hs

/-- Under support inclusion a nonzero PSD input has nonzero quasi-entropy for every alpha > 0. -/
lemma quasi_re_ne_zero_of_support {ρ σ : L H} (hρ : 0 ≤ ρ) (hρ0 : ρ ≠ 0)
    (hσ : 0 ≤ σ) (hsupp : SupportLE ρ σ) {α : ℝ} (hα : 0 < α) :
    (sandwichedQuasi α ρ σ).re ≠ 0 := by
  intro hz
  have hzero := (sandwichedQuasi_re_eq_zero_iff hα hρ).mp hz
  let β : ℝ := (1 - α) / (2 * α)
  let P : L H := CFC.rpow σ β
  have hP : P.IsSymmetric :=
    ((LinearMap.nonneg_iff_isPositive P).mp CFC.rpow_nonneg).isSymmetric
  have hpos := (LinearMap.nonneg_iff_isPositive σ).mp hσ
  let b := hpos.isSymmetric.eigenvectorBasis rfl
  let eig := hpos.isSymmetric.eigenvalues rfl
  have heig (i) : σ (b i) = (eig i : ℂ) • b i :=
    hpos.isSymmetric.apply_eigenvectorBasis rfl i
  have hpow (i) : P (b i) = ((eig i ^ β : ℝ) : ℂ) • b i := by
    change (CFC.rpow σ β).toContinuousLinearMap (b i) = _
    rw [CFCTransport.cfc_rpow_toCLM]
    exact rpow_apply_eigenvector_clm_support σ.toContinuousLinearMap hσ β (b i) (eig i)
      (heig i) (TensorCFC.mem_spectrum_real_of_eigenvector
        (b.orthonormal.ne_zero i) (heig i))
  have hkill (i) : ρ (b i) = 0 := by
    by_cases hi : eig i = 0
    · apply hsupp
      change σ (b i) = 0
      simp [heig i, hi]
    · have hp : 0 < eig i := lt_of_le_of_ne
        (hpos.nonneg_eigenvalues rfl i) (Ne.symm hi)
      have hPP : P (ρ (P (b i))) = 0 :=
        congrArg (fun A : L H => A (b i)) hzero
      have hin : RCLike.re (inner ℂ (ρ (P (b i))) (P (b i))) = 0 := by
        rw [← hP, hPP, inner_zero_left]
        rfl
      have hk := QuantumChannel.nonneg_apply_eq_zero_of_inner_self_eq_zero hρ hin
      rw [hpow, map_smul] at hk
      exact (smul_eq_zero.mp hk).resolve_left
        (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos hp β)))
  apply hρ0
  ext x
  rw [LinearMap.zero_apply, ← b.sum_repr x, map_sum]
  exact Finset.sum_eq_zero fun i _ => by rw [map_smul, hkill, smul_zero]

/-- The NN/EReal and real-valued branches agree for all positive exponents on this domain. -/
lemma nn_eq_real_of_support {ρ σ : L H} (hρ : 0 ≤ ρ) (hρ0 : ρ ≠ 0)
    (hσ : 0 ≤ σ) (hsupp : SupportLE ρ σ) {α : ℝ} (hα : 0 < α) :
    sandwichedRenyiDivNN α ρ σ = (sandwichedRenyiDiv α ρ σ : EReal) := by
  have hQ := quasi_re_ne_zero_of_support hρ hρ0 hσ hsupp hα
  simp only [sandwichedRenyiDivNN, hsupp, not_true_eq_false, and_false, hQ,
    false_or, if_false]

/-- Equality holds on a two-sided punctured neighborhood, including alpha > 1. -/
lemma nn_eventually_eq_real_of_support {ρ σ : L H} (hρ : 0 ≤ ρ) (hρ0 : ρ ≠ 0)
    (hσ : 0 ≤ σ) (hsupp : SupportLE ρ σ) :
    ∀ᶠ α : ℝ in 𝓝[≠] (1 : ℝ),
      sandwichedRenyiDivNN α ρ σ = (sandwichedRenyiDiv α ρ σ : EReal) := by
  filter_upwards [(eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    nhdsWithin_le_nhds] with α hα
  exact nn_eq_real_of_support hρ hρ0 hσ hsupp hα

/-- Turn the explicit log derivative into the two-sided punctured limit. -/
lemma tendsto_of_log_derivative {ρ σ : L H} (hρ : 0 ≤ ρ) (hρ0 : ρ ≠ 0)
    (hσ : 0 ≤ σ)
    (hd : HasDerivAt (fun α => Real.log (sandwichedQuasi α ρ σ).re)
      (umegakiNorm ρ σ) 1) :
    Filter.Tendsto (fun α => sandwichedRenyiDiv α ρ σ) (𝓝[≠] (1 : ℝ))
      (𝓝 (umegakiNorm ρ σ)) := by
  have hTr := QuantumEntropy.trace_re_pos_of_ne_zero hρ hρ0
  have hQ1 : (sandwichedQuasi 1 ρ σ).re = (Tr ρ).re :=
    sandwichedQuasi_one_re ρ.toContinuousLinearMap σ.toContinuousLinearMap hσ hρ
  have he : ∀ᶠ α : ℝ in 𝓝 (1 : ℝ),
      (sandwichedQuasi α ρ σ).re ≠ 0 ∨ Real.log (Tr ρ).re = 0 := by
    by_cases hlog : Real.log (Tr ρ).re = 0
    · exact Filter.Eventually.of_forall fun _ => Or.inr hlog
    · have hn : Real.log (sandwichedQuasi 1 ρ σ).re ≠ 0 := by rwa [hQ1]
      filter_upwards [hd.continuousAt.eventually (eventually_ne_nhds hn)] with α hα
      exact Or.inl fun hz => hα (by rw [hz, Real.log_zero])
  refine hd.tendsto_slope.congr' ?_
  filter_upwards [he.filter_mono nhdsWithin_le_nhds] with α hα
  have hlogdiv : Real.log ((sandwichedQuasi α ρ σ).re / (Tr ρ).re) =
      Real.log (sandwichedQuasi α ρ σ).re - Real.log (Tr ρ).re := by
    by_cases hQ : (sandwichedQuasi α ρ σ).re = 0
    · simp [hQ, hα.resolve_left (not_not.mpr hQ)]
    · exact Real.log_div hQ (ne_of_gt hTr)
  rw [slope_def_field, hQ1, sandwichedRenyiDiv, hlogdiv]
  ring

@[reducible] noncomputable def subspaceQudit (S : Submodule ℂ H) : Qudit S :=
  { toNormedAddCommGroup := S.normedAddCommGroup
    toInnerProductSpace := S.innerProductSpace
    toCompleteSpace := @IsClosed.completeSpace_coe H _ _ (S : Set H)
      S.closed_of_finiteDimensional
    fg_top := Module.Finite.fg_top }

attribute [local instance] subspaceQudit

noncomputable abbrev supportSpace (σ : L H) := (LinearMap.ker σ)ᗮ

noncomputable def compress (σ A : L H) : L (supportSpace σ) :=
  (supportSpace σ).orthogonalProjection.toLinearMap ∘ₗ A ∘ₗ (supportSpace σ).subtype

noncomputable def lift (σ : L H) (A : L (supportSpace σ)) : L H :=
  (supportSpace σ).subtype ∘ₗ A ∘ₗ (supportSpace σ).orthogonalProjection.toLinearMap

/-- The image of a self-adjoint input with support inclusion lies in the sigma support. -/
lemma apply_mem_supportSpace {ρ σ : L H} (hρ : 0 ≤ ρ) (hsupp : SupportLE ρ σ)
    (x : H) : ρ x ∈ supportSpace σ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  have hsym := ((LinearMap.nonneg_iff_isPositive ρ).mp hρ).isSymmetric
  rw [← hsym, show ρ y = 0 from hsupp hy, inner_zero_left]

/-- Applying a compression agrees with the original operator on the support. -/
lemma coe_compress_apply {ρ σ : L H} (hρ : 0 ≤ ρ) (hsupp : SupportLE ρ σ)
    (x : supportSpace σ) : (compress σ ρ x : H) = ρ x := by
  exact (supportSpace σ).starProjection_eq_self_iff.mpr (apply_mem_supportSpace hρ hsupp x)

/-- A supported operator annihilates the discarded component of every vector. -/
lemma apply_starProjection {ρ σ : L H} (hsupp : SupportLE ρ σ) (x : H) :
    ρ ((supportSpace σ).starProjection x) = ρ x := by
  have hm := (supportSpace σ).sub_starProjection_mem_orthogonal x
  have hk : x - (supportSpace σ).starProjection x ∈ LinearMap.ker σ := by
    simpa only [supportSpace, Submodule.orthogonal_orthogonal] using hm
  have hz : ρ (x - (supportSpace σ).starProjection x) = 0 := hsupp hk
  exact (sub_eq_zero.mp (by simpa only [map_sub] using hz)).symm

/-- Exact recovery by extension by zero from the support corner. -/
lemma lift_compress {ρ σ : L H} (hρ : 0 ≤ ρ) (hsupp : SupportLE ρ σ) :
    lift σ (compress σ ρ) = ρ := by
  ext x
  change (compress σ ρ ((supportSpace σ).orthogonalProjection x) : H) = ρ x
  rw [coe_compress_apply hρ hsupp]
  exact apply_starProjection hsupp x

omit [Nontrivial H] in
/-- Orthogonal compression preserves nonnegativity, also on a trivial corner. -/
lemma compress_nonneg {ρ σ : L H} (hρ : 0 ≤ ρ) : 0 ≤ compress σ ρ := by
  rw [LinearMap.nonneg_iff_isPositive]
  have hp := (LinearMap.nonneg_iff_isPositive ρ).mp hρ
  constructor
  · intro x y
    change inner ℂ ((supportSpace σ).orthogonalProjection (ρ x)) y =
      inner ℂ x ((supportSpace σ).orthogonalProjection (ρ y))
    rw [Submodule.inner_orthogonalProjection_eq_of_mem_right,
      Submodule.inner_orthogonalProjection_eq_of_mem_left]
    exact hp.isSymmetric x y
  · intro x
    change 0 ≤ RCLike.re (inner ℂ ((supportSpace σ).orthogonalProjection (ρ x)) x)
    rw [Submodule.inner_orthogonalProjection_eq_of_mem_right]
    exact hp.2 x

/-- The sigma corner is nontrivial and PD; rho stays nonzero PSD. -/
lemma compression_domain {ρ σ : L H} (hρ : 0 ≤ ρ) (hρ0 : ρ ≠ 0)
    (hσ : 0 ≤ σ) (hsupp : SupportLE ρ σ) :
    ∃ hS : Nontrivial (supportSpace σ),
      letI := hS
      0 ≤ compress σ ρ ∧ compress σ ρ ≠ 0 ∧ compress σ σ ∈ pdSetLM := by
  have hn : compress σ ρ ≠ 0 := by
    intro hz
    apply hρ0
    rw [← lift_compress hρ hsupp, hz]
    ext x
    rfl
  haveI : Nontrivial (supportSpace σ) := by
    by_contra h
    haveI : Subsingleton (supportSpace σ) := not_nontrivial_iff_subsingleton.mp h
    exact hn (Subsingleton.elim _ _)
  refine ⟨inferInstance, compress_nonneg hρ, hn, ?_⟩
  apply (pdSetLM_strictPositivity_certificate _).mpr
  refine ⟨compress_nonneg hσ, (LinearMap.isUnit_iff_ker_eq_bot _).mpr ?_⟩
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have hk : (x : H) ∈ LinearMap.ker σ := by
    change σ x = 0
    rw [← coe_compress_apply hσ (le_refl (LinearMap.ker σ)) x, hx]
    rfl
  have hi : inner ℂ (x : H) (x : H) = 0 :=
    ((LinearMap.ker σ).mem_orthogonal x).mp x.property x hk
  apply Subtype.ext
  exact inner_self_eq_zero.mp hi

/-- Totalized log vanishes on the kernel; this explicitly uses Real.log 0 = 0. -/
lemma log_apply_eq_zero_of_mem_ker {A : L H} (hA : 0 ≤ A) {x : H}
    (hx : x ∈ LinearMap.ker A) : CFC.log A x = 0 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have he : A.toContinuousLinearMap x = ((0 : ℝ) : ℂ) • x := by
    simpa using hx
  have hh := TensorCFC.cfc_real_apply_eigenvector
    (show IsSelfAdjoint A.toContinuousLinearMap from IsSelfAdjoint.of_nonneg hA)
    Real.log he (TensorCFC.mem_spectrum_real_of_eigenvector hx0 he)
  change (CFC.log A).toContinuousLinearMap x = 0
  rw [CFCTransport.cfc_log_toCLM]
  simpa only [Real.log_zero, Complex.ofReal_zero, zero_smul] using hh

omit [Nontrivial H] in
/-- Extension by zero preserves trace, without any self-adjointness assumption. -/
lemma trace_lift (σ : L H) (A : L (supportSpace σ)) : Tr (lift σ A) = Tr A := by
  unfold lift
  rw [LinearMap.trace_comp_comm' (A ∘ₗ (supportSpace σ).orthogonalProjection.toLinearMap)
    (supportSpace σ).subtype]
  congr 1
  ext x
  change (A ((supportSpace σ).orthogonalProjection (x : H)) : H) = (A x : H)
  rw [Submodule.orthogonalProjection_mem_subspace_eq_self]

/-- The trace of a supported PSD input agrees with its actual support compression. -/
lemma trace_compress {ρ σ : L H} (hρ : 0 ≤ ρ) (hsupp : SupportLE ρ σ) :
    Tr (compress σ ρ) = Tr ρ := by
  rw [← trace_lift, lift_compress hρ hsupp]

/-- Range and kernel conditions give exact extension by zero, without a positivity assumption. -/
lemma lift_compress_of_range_ker {A σ : L H}
    (hrange : ∀ x, A x ∈ supportSpace σ) (hker : SupportLE A σ) :
    lift σ (compress σ A) = A := by
  ext x
  change (supportSpace σ).starProjection
    (A ((supportSpace σ).starProjection x)) = A x
  rw [(supportSpace σ).starProjection_eq_self_iff.mpr (hrange _)]
  exact apply_starProjection hker x

/-- The Umegaki logarithmic product has no contribution on the discarded kernel.
This is an operator identity, prior to the remaining CFC transport inside the corner. -/
lemma umegaki_product_eq_lift_compress {ρ σ : L H} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hsupp : SupportLE ρ σ) :
    ρ * (CFC.log ρ - CFC.log σ) =
      lift σ (compress σ (ρ * (CFC.log ρ - CFC.log σ))) := by
  symm
  apply lift_compress_of_range_ker
  · intro x
    exact apply_mem_supportSpace hρ hsupp _
  · intro x hx
    change ρ (CFC.log ρ x - CFC.log σ x) = 0
    rw [log_apply_eq_zero_of_mem_ker hρ (hsupp hx), log_apply_eq_zero_of_mem_ker hσ hx,
      sub_self, map_zero]

end AlphaOneSupport
end SandwichedRenyiRelativeEntropy
