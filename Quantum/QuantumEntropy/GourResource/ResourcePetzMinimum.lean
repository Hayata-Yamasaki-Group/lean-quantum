/-
Lower semicontinuity of the Petz–Rényi divergence D_α(ρ‖·) (1<α) in its second argument, including points where the support changes (gsl_y58a); used for gsl_y58.
-/
/-
Right lower semicontinuity of Petz and the min over the free set.
-/
import Quantum.QuantumEntropy.GourResource.KWCarrierBridge
import Quantum.OperationalProbabilistic.Framework.TestingRegionHockeyStick.GSLCore
import Quantum.OperationalProbabilistic.OperationalFidelity.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesDecouplingNorm.GSLCoreRetained
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesMinDefinitions.GSLCore
import Quantum.QuantumModel.HighInterfaces.GSLCoreRetained
import Quantum.QuantumModel.NativeFidelity.GSLCoreRetained
import Quantum.QuantumModel.SupportFaceDictionary.GSLCore

open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower ℝ ℂ (L H) :=
  RestrictScalars.isScalarTower ℝ ℂ (L H)

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private noncomputable def spectralBasis
    {A : Type u} [Qudit A] (σ : State A) :
    OrthonormalBasis (Fin (Module.finrank ℂ A)) ℂ A :=
  σ.2.1.isSymmetric.eigenvectorBasis rfl

private noncomputable def stateEigenvalue
    {A : Type u} [Qudit A] (σ : State A) : Fin (Module.finrank ℂ A) → ℝ :=
  σ.2.1.isSymmetric.eigenvalues rfl

private theorem spectral_apply
    {A : Type u} [Qudit A] (σ : State A) (i : Fin (Module.finrank ℂ A)) :
    σ.1 (spectralBasis σ i) = (stateEigenvalue σ i : ℂ) • spectralBasis σ i :=
  σ.2.1.isSymmetric.apply_eigenvectorBasis rfl i

private theorem spectral_mem
    {A : Type u} [Qudit A] [Nontrivial A]
    (σ : State A) (i : Fin (Module.finrank ℂ A)) :
    stateEigenvalue σ i ∈ spectrum ℝ σ.1 := by
  rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage]
  exact (σ.2.1.isSymmetric.hasEigenvalue_eigenvalues rfl i).mem_spectrum

private theorem rpow_apply
    {A : Type u} [Qudit A] [Nontrivial A]
    {X : L A} (hX : 0 ≤ X) (p : ℝ) {v : A} {t : ℝ}
    (hv : X v = (t : ℂ) • v) (ht : t ∈ spectrum ℝ X) :
    CFC.rpow X p v = (t ^ p : ℝ) • v := by
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hX]
  simpa only [Complex.coe_smul] using
    SandwichedRenyiRelativeEntropy.cfc_real_apply_eigenvector_lm (IsSelfAdjoint.of_nonneg hX)
      (fun x : ℝ => x ^ p) hv ht

private theorem rpow_zero_iff
    {A : Type u} [Qudit A] [Nontrivial A]
    {X : L A} (hX : 0 ≤ X) {p : ℝ} (hp : 0 < p) (v : A) :
    CFC.rpow X p v = 0 ↔ X v = 0 := by
  have hback : CFC.rpow (CFC.rpow X p) p⁻¹ = X := by
    simp only [CFC.rpow_eq_pow]
    rw [CFC.rpow_rpow_of_exponent_nonneg X p p⁻¹ hp.le (inv_nonneg.mpr hp.le) hX,
      mul_inv_cancel₀ hp.ne', CFC.rpow_one X hX]
  have hzero {Y : L A} (hY : 0 ≤ Y) {q : ℝ} (hq : q ≠ 0)
      (h : Y v = 0) : CFC.rpow Y q v = 0 := by
    by_cases hv : v = 0
    · simp [hv]
    have hs : (0 : ℝ) ∈ spectrum ℝ Y :=
      SandwichedRenyiRelativeEntropy.mem_spectrum_real_of_eigenvector_lm hv (by simpa using h)
    simpa [Real.zero_rpow hq] using
      rpow_apply hY q (show Y v = ((0 : ℝ) : ℂ) • v by simpa using h) hs
  constructor
  · intro h
    rw [← hback]
    exact hzero CFC.rpow_nonneg (inv_ne_zero hp.ne') h
  · exact hzero hX hp.ne'

private noncomputable def spectralWeight
    {A : Type u} [Qudit A] (ρ σ : State A) (α : ℝ)
    (i : Fin (Module.finrank ℂ A)) : ℝ :=
  (inner ℂ (spectralBasis σ i) (CFC.rpow ρ.1 α (spectralBasis σ i))).re

private theorem weight_nonneg
    {A : Type u} [Qudit A] (ρ σ : State A) (α : ℝ)
    (i : Fin (Module.finrank ℂ A)) : 0 ≤ spectralWeight ρ σ α i :=
  ((LinearMap.nonneg_iff_isPositive (CFC.rpow ρ.1 α)).mp
    CFC.rpow_nonneg).re_inner_nonneg_right (spectralBasis σ i)

private theorem weight_zero_iff
    {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : State A) {α : ℝ} (hα : 0 < α) (i : Fin (Module.finrank ℂ A)) :
    spectralWeight ρ σ α i = 0 ↔ ρ.1 (spectralBasis σ i) = 0 := by
  rw [← rpow_zero_iff ((LinearMap.nonneg_iff_isPositive _).mpr ρ.2.1) hα]
  constructor
  · intro h
    apply QuantumChannel.nonneg_apply_eq_zero_of_re_inner_eq_zero CFC.rpow_nonneg
    simpa only [inner_re_symm] using h
  · intro h
    simp only [spectralWeight, h, inner_zero_right, Complex.zero_re]

private theorem trace_cfc_spectral
    {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : State A) (α : ℝ) (f : ℝ → ℝ) :
    (Tr (CFC.rpow ρ.1 α * cfc f σ.1)).re =
      ∑ i, spectralWeight ρ σ α i * f (stateEigenvalue σ i) := by
  classical
  change (LinearMap.trace ℂ A (CFC.rpow ρ.1 α * cfc f σ.1)).re = _
  rw [LinearMap.trace_eq_sum_inner
    (T := CFC.rpow ρ.1 α * cfc f σ.1) (spectralBasis σ), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he := SandwichedRenyiRelativeEntropy.cfc_real_apply_eigenvector_lm
    (IsSelfAdjoint.of_nonneg ((LinearMap.nonneg_iff_isPositive _).mpr σ.2.1))
    f (spectral_apply σ i) (spectral_mem σ i)
  rw [Module.End.mul_apply, he, map_smul, inner_smul_right]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_comm _ _

private theorem support_iff_weights
    {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : State A) {α : ℝ} (hα : 0 < α) :
    SandwichedRenyiRelativeEntropy.suppLE ρ.1 σ.1 ↔
      ∀ i, stateEigenvalue σ i = 0 → spectralWeight ρ σ α i = 0 := by
  classical
  constructor
  · intro h i hi
    apply (weight_zero_iff ρ σ hα i).mpr
    apply h
    simp only [LinearMap.mem_ker, spectral_apply, hi, Complex.ofReal_zero, zero_smul]
  · intro h x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← (spectralBasis σ).sum_repr' x, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul]
    by_cases hi : stateEigenvalue σ i = 0
    · rw [(weight_zero_iff ρ σ hα i).mp (h i hi), smul_zero]
    · have hc : inner ℂ (spectralBasis σ i) x = 0 := by
        have hz := congrArg (fun y => inner ℂ (spectralBasis σ i) y) hx
        dsimp only at hz
        rw [← σ.2.1.isSymmetric _ _, spectral_apply, inner_smul_left,
          Complex.conj_ofReal, inner_zero_right] at hz
        exact (mul_eq_zero.mp hz).resolve_left (Complex.ofReal_ne_zero.mpr hi)
      rw [hc, zero_smul]

/- Cut off small eigenvalues before taking the negative power. For each positive δ,
this scalar function is continuous on all of ℝ, including at zero. -/
private noncomputable def cutoffTrace
    {A : Type u} [Qudit A] (ρ σ : State A) (α δ : ℝ) : ℝ :=
  (Tr (CFC.rpow ρ.1 α * cfc (fun x : ℝ => (max x δ) ^ (1 - α)) σ.1)).re

private theorem cutoff_continuous
    {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun σ : State A => cutoffTrace ρ σ α δ) := by
  have hf : Continuous (fun x : ℝ => (max x δ) ^ (1 - α)) :=
    (continuous_id.max continuous_const).rpow_const
      (fun x => Or.inl (ne_of_gt (lt_of_lt_of_le hδ (le_max_right x δ))))
  have hc : Continuous (fun σ : State A =>
      cfc (fun x : ℝ => (max x δ) ^ (1 - α)) σ.1) :=
    Continuous.cfc_of_mem_nhdsSet _ (s := Set.univ) Filter.univ_mem
      continuous_subtype_val
      (fun σ => IsSelfAdjoint.of_nonneg ((LinearMap.nonneg_iff_isPositive _).mpr σ.2.1))
      hf.continuousOn
  exact QuantumState.continuous_re_trace_lm.comp (continuous_const.mul hc)

private theorem raw_trace_spectral
    {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : State A) {α : ℝ} (hα : 1 < α) :
    OPT.petzSupportTracePower α ρ.1 σ.1 =
      ∑ i, spectralWeight ρ σ α i * (stateEigenvalue σ i) ^ (1 - α) := by
  rw [OPT.petzSupportTracePower,
    OPT.petzSupportRpow_of_ne_zero _ (lt_trans zero_lt_one hα).ne',
    OPT.petzSupportRpow_of_ne_zero _ (sub_ne_zero.mpr hα.ne)]
  have hpow : CFC.rpow σ.1 (1 - α) = cfc (fun x : ℝ => x ^ (1 - α)) σ.1 := by
    rw [CFC.rpow_eq_pow]
    exact CFC.rpow_eq_cfc_real ((LinearMap.nonneg_iff_isPositive σ.1).mpr σ.2.1)
  rw [hpow]
  exact trace_cfc_spectral ρ σ α _

private theorem cutoff_le_raw
    {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : State A) {α : ℝ} (hα : 1 < α) {δ : ℝ}
    (hs : SandwichedRenyiRelativeEntropy.suppLE ρ.1 σ.1) :
    cutoffTrace ρ σ α δ ≤ OPT.petzSupportTracePower α ρ.1 σ.1 := by
  rw [cutoffTrace, trace_cfc_spectral, raw_trace_spectral ρ σ hα]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : stateEigenvalue σ i = 0
  · rw [(support_iff_weights ρ σ (lt_trans zero_lt_one hα)).mp hs i hi]
    simp only [zero_mul, le_refl]
  · apply mul_le_mul_of_nonneg_left _ (weight_nonneg ρ σ α i)
    exact Real.rpow_le_rpow_of_nonpos
      (lt_of_le_of_ne (σ.2.1.nonneg_eigenvalues rfl i) (Ne.symm hi))
      (le_max_left _ _) (sub_nonpos.mpr hα.le)

/- Under support inclusion, zero eigenvalues have zero weight. A cutoff below the
least positive eigenvalue therefore gives the original trace exactly. -/
private theorem cutoff_eq_raw_for_some
    {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : State A) {α : ℝ} (hα : 1 < α)
    (hs : SandwichedRenyiRelativeEntropy.suppLE ρ.1 σ.1) :
    ∃ δ : ℝ, 0 < δ ∧ cutoffTrace ρ σ α δ = OPT.petzSupportTracePower α ρ.1 σ.1 := by
  classical
  let s := Finset.univ.filter (fun i => 0 < stateEigenvalue σ i)
  have hfloor : ∃ δ : ℝ, 0 < δ ∧ ∀ i, 0 < stateEigenvalue σ i → δ ≤ stateEigenvalue σ i := by
    by_cases hne : s.Nonempty
    · obtain ⟨j, hj, hmin⟩ := s.exists_min_image (stateEigenvalue σ) hne
      exact ⟨stateEigenvalue σ j, (Finset.mem_filter.mp hj).2,
        fun i hi => hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)⟩
    · refine ⟨1, zero_lt_one, fun i hi => ?_⟩
      exact (hne ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩).elim
  obtain ⟨δ, hδ, hf⟩ := hfloor
  refine ⟨δ, hδ, ?_⟩
  rw [cutoffTrace, trace_cfc_spectral, raw_trace_spectral ρ σ hα]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : stateEigenvalue σ i = 0
  · rw [(support_iff_weights ρ σ (lt_trans zero_lt_one hα)).mp hs i hi]
    simp only [zero_mul]
  · rw [max_eq_left (hf i
      (lt_of_le_of_ne (σ.2.1.nonneg_eigenvalues rfl i) (Ne.symm hi)))]

/- A support mismatch supplies a zero eigenvalue with positive weight. Its single
contribution tends to infinity, while every other contribution is nonnegative. -/
private theorem cutoff_unbounded
    {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : State A) {α : ℝ} (hα : 1 < α)
    (hs : ¬ SandwichedRenyiRelativeEntropy.suppLE ρ.1 σ.1) (R : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ R < cutoffTrace ρ σ α δ := by
  classical
  obtain ⟨i, hi, hw⟩ : ∃ i, stateEigenvalue σ i = 0 ∧ spectralWeight ρ σ α i ≠ 0 := by
    simpa only [support_iff_weights ρ σ (lt_trans zero_lt_one hα), not_forall,
      exists_prop] using hs
  have hwpos : 0 < spectralWeight ρ σ α i :=
    lt_of_le_of_ne (weight_nonneg ρ σ α i) (Ne.symm hw)
  have ht := (tendsto_rpow_neg_nhdsGT_zero (sub_neg.mpr hα)).const_mul_atTop hwpos
  have hδevent : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  have he : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      0 < δ ∧ R < spectralWeight ρ σ α i * δ ^ (1 - α) :=
    hδevent.and (ht.eventually_gt_atTop R)
  obtain ⟨δ, hδ, hR⟩ := he.exists
  refine ⟨δ, hδ, hR.trans_le ?_⟩
  rw [cutoffTrace, trace_cfc_spectral]
  have hle := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin (Module.finrank ℂ A)))) =>
      mul_nonneg (weight_nonneg ρ σ α j)
        (Real.rpow_nonneg (le_trans hδ.le (le_max_right (stateEigenvalue σ j) δ)) (1 - α)))
    (Finset.mem_univ i)
  simpa only [hi, max_eq_right hδ.le] using hle

private noncomputable def extendedTrace
    {A : Type u} [Qudit A] (ρ σ : State A) (α : ℝ) : ENNReal :=
  ⨆ δ : {x : ℝ // 0 < x}, ENNReal.ofReal (cutoffTrace ρ σ α δ.1)

private theorem extendedTrace_of_support
    {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : State A) {α : ℝ} (hα : 1 < α)
    (hs : SandwichedRenyiRelativeEntropy.suppLE ρ.1 σ.1) :
    extendedTrace ρ σ α = ENNReal.ofReal (OPT.petzSupportTracePower α ρ.1 σ.1) := by
  apply le_antisymm
  · exact iSup_le fun δ => ENNReal.ofReal_le_ofReal (cutoff_le_raw ρ σ hα hs)
  · obtain ⟨δ, hδ, he⟩ := cutoff_eq_raw_for_some ρ σ hα hs
    rw [← he]
    exact le_iSup_of_le ⟨δ, hδ⟩ le_rfl

private theorem extendedTrace_of_not_support
    {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : State A) {α : ℝ} (hα : 1 < α)
    (hs : ¬ SandwichedRenyiRelativeEntropy.suppLE ρ.1 σ.1) :
    extendedTrace ρ σ α = ⊤ := by
  apply (iSup_eq_top _).mpr
  intro b hb
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_of_lt hb)
  obtain ⟨δ, hδ, hR⟩ := cutoff_unbounded ρ σ hα hs (n : ℝ)
  refine ⟨⟨δ, hδ⟩, ?_⟩
  have hn' : b < ENNReal.ofReal (n : ℝ) := by simpa only [ENNReal.ofReal_natCast] using hn
  exact hn'.trans ((ENNReal.ofReal_lt_ofReal_iff
    (lt_of_le_of_lt (Nat.cast_nonneg n) hR)).mpr hR)

private theorem extendedTrace_lowerSemicontinuous
    {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) (α : ℝ) :
    LowerSemicontinuous (fun σ : State A => extendedTrace ρ σ α) := by
  apply lowerSemicontinuous_iSup
  intro δ
  exact (ENNReal.continuous_ofReal.comp (cutoff_continuous ρ α δ.2)).lowerSemicontinuous

/- Identify the original EReal divergence before applying logarithmic calculus.
The support mismatch branch is retained as top; no toReal operation is used. -/
private theorem petz_extendedTrace
    {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : State A) {α : ℝ} (hα : 1 < α) :
    petz α ρ.1 σ.1 =
      (((α - 1)⁻¹ / Real.log 2 : ℝ) : EReal) * ENNReal.log (extendedTrace ρ σ α) := by
  classical
  have ha : 0 < α := lt_trans zero_lt_one hα
  have hc : 0 < (α - 1)⁻¹ / Real.log 2 :=
    div_pos (inv_pos.mpr (sub_pos.mpr hα)) (Real.log_pos (by norm_num))
  simp only [petz, dif_pos ha.le, dif_pos ρ.2, dif_pos σ.2,
    OPT.petzQuantumRenyiDivergenceFinite, OPT.w26PetzQuantumRenyiDivergenceFinite,
    dif_neg ha.ne', dif_neg hα.ne']
  by_cases hs : SandwichedRenyiRelativeEntropy.suppLE ρ.1 σ.1
  · rw [dif_pos (Or.inl hs), extendedTrace_of_support ρ σ hα hs,
      ENNReal.log_ofReal_of_pos
        (OPT.petzSupportTracePower_pos_of_suppLE α ρ.1 σ.1 ρ.2 σ.2 hs),
      ← EReal.coe_mul]
    congr 1
    dsimp only
    rw [Real.logb]
    ring
  · rw [dif_neg (by simp only [hs, not_lt.mpr hα.le, false_and, or_self, not_false_eq_true]),
      extendedTrace_of_not_support ρ σ hα hs, ENNReal.log_top, EReal.coe_mul_top_of_pos hc]

private theorem continuous_positive_mul {k : ℝ} (hk : 0 < k) :
    Continuous (fun x : EReal => (k : EReal) * x) := by
  have hk0 : (k : EReal) ≠ 0 := by exact_mod_cast hk.ne'
  rw [continuous_iff_continuousAt]
  intro x
  exact (EReal.continuousAt_mul (Or.inl hk0) (Or.inl hk0)
    (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).comp
    (continuous_const.continuousAt.prodMk continuous_id.continuousAt)

theorem gsl_y58a :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A]
  (ρ : State.{u} A) (α : ℝ), 1 < α →
    LowerSemicontinuous (fun σ : State.{u} A => petz.{u} α ρ.1 σ.1)
:= by
  intro A _ _ ρ α hα
  simp_rw [petz_extendedTrace ρ _ hα]
  have hc : 0 < (α - 1)⁻¹ / Real.log 2 :=
    div_pos (inv_pos.mpr (sub_pos.mpr hα)) (Real.log_pos (by norm_num))
  have hl := ENNReal.continuous_log.comp_lowerSemicontinuous
    (extendedTrace_lowerSemicontinuous ρ α) ENNReal.logOrderIso.monotone
  exact (continuous_positive_mul hc).comp_lowerSemicontinuous hl
    (fun _ _ h => mul_le_mul_of_nonneg_left h (EReal.coe_nonneg.mpr hc.le))

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem compact_min_from_lsc
    {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (α : ℝ)
    (h : LowerSemicontinuous (fun σ : State.{u} A => petz.{u} α ρ.1 σ.1))
    (S : Set (L.{u} A)) (hne : S.Nonempty) (hclosed : IsClosed S)
    (hsub : S ⊆ {X | IsDensity.{u} X}) :
    ∃ σ ∈ S, petz.{u} α ρ.1 σ = res.{u} (petz.{u} α) ρ.1 S ∧
      IsLeast ((fun τ => petz.{u} α ρ.1 τ) '' S) (petz.{u} α ρ.1 σ) := by
  have hcompact : IsCompact S :=
    (GourResource.gsl_b01.2.2 (A := A)).1.of_isClosed_subset hclosed hsub
  have hdensity : LowerSemicontinuousOn (fun σ : L.{u} A => petz.{u} α ρ.1 σ)
      {X | IsDensity.{u} X} := lowerSemicontinuous_restrict_iff.mp h
  obtain ⟨σ, hσ, hmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn hne hcompact (hdensity.mono hsub)
  refine ⟨σ, hσ, le_antisymm ?_ ?_, ?_⟩
  · exact le_iInf fun τ => le_iInf fun hτ => hmin hτ
  · exact iInf_le_of_le σ (iInf_le_of_le hσ le_rfl)
  · refine ⟨⟨σ, hσ, rfl⟩, ?_⟩
    rintro _ ⟨τ, hτ, rfl⟩
    exact hmin hτ

private theorem positive_trace_continuous
    {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (α : ℝ) (ha : 0 < α) (hb : α < 1) :
    Continuous (fun σ : State.{u} A => OPT.petzSupportTracePower α ρ.1 σ.1) := by
  have hpow : Continuous (fun σ : State.{u} A => CFC.rpow σ.1 (1 - α)) := by
    rw [continuous_iff_continuousAt]
    intro σ
    rw [← continuousWithinAt_univ]
    exact OPT.continuousWithinAt_cfcRpow_of_pos
      continuous_subtype_val.continuousWithinAt continuous_const.continuousWithinAt
      (Filter.Eventually.of_forall fun τ =>
        (LinearMap.nonneg_iff_isPositive τ.1).mpr τ.2.1)
      (Filter.Eventually.of_forall fun _ => sub_pos.mpr hb)
      ((LinearMap.nonneg_iff_isPositive σ.1).mpr σ.2.1) (sub_pos.mpr hb)
  have htrace : Continuous (fun σ : State.{u} A =>
      (Tr (CFC.rpow ρ.1 α * CFC.rpow σ.1 (1 - α))).re) :=
    QuantumState.continuous_re_trace_lm.comp (continuous_const.mul hpow)
  simpa only [OPT.petzSupportTracePower,
    OPT.petzSupportRpow_of_ne_zero _ ha.ne',
    OPT.petzSupportRpow_of_ne_zero _ (sub_pos.mpr hb).ne'] using htrace

private theorem petz_log_representation_lt_one
    {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ σ : State.{u} A) (α : ℝ) (ha : 0 < α) (hb : α < 1) :
    petz.{u} α ρ.1 σ.1 =
      (((α - 1)⁻¹ / Real.log 2 : ℝ) : EReal) *
        ENNReal.log (ENNReal.ofReal (OPT.petzSupportTracePower α ρ.1 σ.1)) := by
  classical
  have hc : (α - 1)⁻¹ / Real.log 2 < 0 :=
    div_neg_of_neg_of_pos (inv_neg''.mpr (sub_neg.mpr hb)) (Real.log_pos (by norm_num))
  simp only [petz, dif_pos ha.le, dif_pos ρ.2, dif_pos σ.2,
    OPT.petzQuantumRenyiDivergenceFinite, OPT.w26PetzQuantumRenyiDivergenceFinite,
    dif_neg ha.ne', dif_neg hb.ne]
  by_cases hm : ρ.1 * σ.1 = 0
  · have hq := (OPT.petzTraceExpression_eq_some_zero_of_lt_one_of_mul_eq_zero
      α ρ.1 σ.1 ha.le ρ.2 σ.2 hb hm).2.1
    have hs : ¬ SandwichedRenyiRelativeEntropy.suppLE ρ.1 σ.1 := by
      intro hs
      have hpos := OPT.petzSupportTracePower_pos_of_suppLE α ρ.1 σ.1 ρ.2 σ.2 hs
      rw [hq] at hpos
      exact lt_irrefl 0 hpos
    simp only [hs, hm, ne_eq, not_true_eq_false, and_false, or_self, dite_false,
      hq, ENNReal.ofReal_zero, ENNReal.log_zero, EReal.coe_mul_bot_of_neg hc]
  · have hq := OPT.petzSupportTracePower_pos_of_lt_one_of_mul_ne_zero
      α ρ.1 σ.1 ρ.2 σ.2 hb hm
    rw [dif_pos (Or.inr ⟨hb, hm⟩), ENNReal.log_ofReal_of_pos hq, ← EReal.coe_mul]
    congr 1
    dsimp only
    rw [Real.logb]
    ring

private theorem petz_continuous_lt_one
    {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (α : ℝ) (ha : 0 < α) (hb : α < 1) :
    Continuous (fun σ : State.{u} A => petz.{u} α ρ.1 σ.1) := by
  simp_rw [petz_log_representation_lt_one ρ _ α ha hb]
  have hc : (((α - 1)⁻¹ / Real.log 2 : ℝ) : EReal) ≠ 0 := by
    norm_cast
    exact div_ne_zero (inv_ne_zero (sub_ne_zero.mpr hb.ne))
      (Real.log_pos (by norm_num)).ne'
  have hlog : Continuous (fun σ : State.{u} A =>
      ENNReal.log (ENNReal.ofReal (OPT.petzSupportTracePower α ρ.1 σ.1))) :=
    ENNReal.continuous_log.comp
      (ENNReal.continuous_ofReal.comp (positive_trace_continuous ρ α ha hb))
  rw [continuous_iff_continuousAt]
  intro σ
  exact (EReal.continuousAt_mul (Or.inl hc) (Or.inl hc)
    (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).comp
      (continuous_const.continuousAt.prodMk hlog.continuousAt)

theorem gsl_y58 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (α : ℝ),
  0 < α → α ≠ 1 →
  LowerSemicontinuous (fun σ : State.{u} A => petz.{u} α ρ.1 σ.1) ∧
  ∀ S : Set (L.{u} A), S.Nonempty → IsClosed S → S ⊆ {X | IsDensity.{u} X} →
    ∃ σ ∈ S, petz.{u} α ρ.1 σ = res.{u} (petz.{u} α) ρ.1 S ∧
      IsLeast ((fun τ => petz.{u} α ρ.1 τ) '' S) (petz.{u} α ρ.1 σ)
:= by
  intro A _ _ ρ α ha hb
  have h : LowerSemicontinuous (fun σ : State.{u} A => petz.{u} α ρ.1 σ.1) := by
    rcases lt_or_gt_of_ne hb with hlt | hlt
    · exact (petz_continuous_lt_one ρ α ha hlt).lowerSemicontinuous
    · exact GourResource.gsl_y58a.{u} ρ α hlt
  exact ⟨h, fun S hne hclosed hsub => compact_min_from_lsc ρ α h S hne hclosed hsub⟩

end GourResource

