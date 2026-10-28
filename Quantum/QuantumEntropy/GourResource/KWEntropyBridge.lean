/-
Identifies the Umegaki relative entropy du, the Petz–Rényi divergence petz and the sandwiched Rényi divergence sand with the quantities of the finite-dimensional model, shows their invariance under isometric transport, and obtains the upper bounds dh ≤ sand + α/(α−1)·log₂(1/(1−ε)) and (1−ε)·dh ≤ du + hb(ε) with the binary entropy hb (gsl_b03).
-/
import Quantum.QuantumEntropy.GourResource.KWTestingBridge
import Quantum.QuantumEntropy.GourResource.TestingSDP
import Quantum.QuantumModel.KW.Distances.HypothesisTestingBounds.RelativeEntropy.GSLCore
import Quantum.QuantumModel.KW.Distances.HypothesisTestingCore.Basic

open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower NNReal ℂ (L H) :=
  RestrictScalars.isScalarTower NNReal ℂ (L H)
open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower ℝ ℂ (L H) :=
  RestrictScalars.isScalarTower ℝ ℂ (L H)

namespace GourResource


open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem b03_density
    (S : QuantumModel.Sys)
    (ρ : QuantumModel.DensityMatrix S) :
    IsDensity ρ.operator :=
  ⟨(LinearMap.nonneg_iff_isPositive _).mp ρ.nonneg, ρ.trace_one⟩

private theorem b03_du_native
    (S : QuantumModel.Sys)
    (ρ σ : QuantumModel.DensityMatrix S) :
    du ρ.operator σ.operator =
      QuantumModel.NativeHypothesisTesting.umegakiRelEntropyBits
        ρ σ.operator := by
  change ((1 / Real.log 2 : ℝ) : EReal) *
      SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN ρ.operator σ.operator =
    SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN ρ.operator σ.operator /
      ((Real.log 2 : ℝ) : EReal)
  rw [one_div, EReal.coe_inv, EReal.div_eq_inv_mul]

private theorem b03_sand_formula {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : L A) (hρ : IsDensity ρ) (hσ : IsDensity σ) (α : ℝ) (hα : 1 < α) :
    sand α ρ σ = ((1 / Real.log 2 : ℝ) : EReal) *
      SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN α ρ σ := by
  classical
  have hα0 : 0 ≤ α := le_trans zero_le_one hα.le
  have hαhalf : (1 / 2 : ℝ) ≤ α := by linarith
  rw [sand, dif_pos hρ, dif_pos hσ,
    SandwichedRenyiRelativeEntropy.gourSandwichedRenyiBits_standard_order]
  · rw [ENNReal.toReal_ofReal hα0]
    unfold SandwichedRenyiRelativeEntropy.standardSandwichedRenyiBitsFinite
      SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN
    rw [if_neg (ne_of_gt hα)]
    split_ifs
    · exact (EReal.coe_mul_top_of_pos
        (one_div_pos.mpr (Real.log_pos (by norm_num)))).symm
    · rw [← EReal.coe_mul]
      congr 1
      unfold SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv
      rw [Real.logb]
      ring
  · exact ENNReal.ofReal_ne_zero_iff.mpr (lt_trans zero_lt_one hα)
  · exact fun h => (ne_of_gt hα) (by
      simpa only [ENNReal.toReal_ofReal hα0, ENNReal.toReal_one]
        using congrArg ENNReal.toReal h)
  · exact ENNReal.ofReal_ne_top
  · simpa only [ENNReal.toReal_ofReal hα0] using hαhalf

private theorem b03_sand_native
    (S : QuantumModel.Sys)
    (ρ σ : QuantumModel.DensityMatrix S)
    (α : ℝ) (hα : 1 < α) :
    sand α ρ.operator σ.operator =
      QuantumModel.NativeHypothesisTesting.sandwichedRenyiDivBits
        α ρ σ.operator := by
  rw [b03_sand_formula _ _ (b03_density S ρ) (b03_density S σ) α hα]
  change ((1 / Real.log 2 : ℝ) : EReal) *
      SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN α ρ.operator σ.operator =
    SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN α ρ.operator σ.operator /
      ((Real.log 2 : ℝ) : EReal)
  rw [one_div, EReal.coe_inv, EReal.div_eq_inv_mul]

private theorem b03_petz_formula {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : L A) (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (α : ℝ) (hα : α ∈ Set.Ioo 0 1) :
    petz α ρ σ =
      if OPT.petzSupportTracePower α ρ σ = 0 then ⊤
      else ((Real.logb 2 (OPT.petzSupportTracePower α ρ σ) / (α - 1) : ℝ) : EReal) := by
  classical
  rw [petz, dif_pos hα.1.le, dif_pos hρ, dif_pos hσ]
  unfold OPT.petzQuantumRenyiDivergenceFinite OPT.w26PetzQuantumRenyiDivergenceFinite
  rw [dif_neg (ne_of_gt hα.1), dif_neg (ne_of_lt hα.2)]
  by_cases hm : ρ * σ = 0
  · have hq := (OPT.petzTraceExpression_eq_some_zero_of_lt_one_of_mul_eq_zero
      α ρ σ hα.1.le hρ hσ hα.2 hm).2.1
    have hs : ¬ SandwichedRenyiRelativeEntropy.suppLE ρ σ := by
      intro hs
      have hp := OPT.petzSupportTracePower_pos_of_suppLE α ρ σ hρ hσ hs
      rw [hq] at hp
      exact (lt_irrefl 0) hp
    simp [hs, hm, hq]
  · have hq := OPT.petzSupportTracePower_pos_of_lt_one_of_mul_ne_zero
      α ρ σ hρ hσ hα.2 hm
    rw [dif_pos (Or.inr ⟨hα.2, hm⟩), if_neg (ne_of_gt hq)]
    dsimp only
    congr 1
    ring

private theorem b03_petz_power {A : Type u} [Qudit A]
    (ρ σ : L A) (α : ℝ) (hα : α ∈ Set.Ioo 0 1) :
    OPT.petzSupportTracePower α ρ σ =
      (Tr (CFC.rpow ρ α * CFC.rpow σ (1 - α))).re := by
  unfold OPT.petzSupportTracePower
  rw [OPT.petzSupportRpow_of_ne_zero _ (ne_of_gt hα.1),
    OPT.petzSupportRpow_of_ne_zero _ (ne_of_gt (sub_pos.mpr hα.2))]

private theorem b03_petz_native
    (S : QuantumModel.Sys)
    (ρ σ : QuantumModel.DensityMatrix S)
    (α : ℝ) (hα : α ∈ Set.Ioo 0 1) :
    petz α ρ.operator σ.operator =
      QuantumModel.NativeHypothesisTesting.petzRenyiDivBits
        α ρ σ.operator := by
  rw [b03_petz_formula _ _ (b03_density S ρ) (b03_density S σ) α hα,
    b03_petz_power _ _ α hα]
  rfl

private noncomputable def b03_conj {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) : L A ≃⋆ₐ[ℂ] L B :=
  (linearToContinuousEndStarAlgEquiv A).trans
    (U.conjStarAlgEquiv.trans (linearToContinuousEndStarAlgEquiv B).symm)

private theorem b03_trace {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (X : L A) : Tr (b03_conj U X) = Tr X :=
  LinearMap.trace_conj' X U.toLinearEquiv

private theorem b03_rpow {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (X : L A) (p : ℝ) :
    b03_conj U (CFC.rpow X p) = CFC.rpow (b03_conj U X) p := by
  let φ := b03_conj U
  let f : NNReal → NNReal := fun x => x ^ p
  change φ (cfc f X) = cfc f (φ X)
  have hn : 0 ≤ φ X ↔ 0 ≤ X := by
    conv_lhs => rw [show (0 : L B) = φ 0 from (map_zero φ).symm]
    exact OrderIsoClass.map_le_map_iff φ
  have hs : spectrum NNReal (φ X) = spectrum NNReal X :=
    AlgEquiv.spectrum_eq (φ.restrictScalars NNReal).toAlgEquiv X
  by_cases h : (0 ≤ X) ∧ ContinuousOn f (spectrum NNReal X)
  · exact StarAlgHomClass.map_cfc (S := ℂ) φ f X h.2
      (map_continuous φ) h.1 (hn.mpr h.1)
  · rw [cfc_apply_of_not_and X h, map_zero, cfc_apply_of_not_and]
    rwa [hn, hs]

private theorem b03_log {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (X : L A) :
    b03_conj U (CFC.log X) = CFC.log (b03_conj U X) := by
  let φ := b03_conj U
  change φ (cfc Real.log X) = cfc Real.log (φ X)
  have hn : IsSelfAdjoint (φ X) ↔ IsSelfAdjoint X := by
    constructor
    · intro h
      simpa only [φ.symm_apply_apply] using h.map φ.symm
    · exact fun h => h.map φ
  have hs : spectrum ℝ (φ X) = spectrum ℝ X :=
    AlgEquiv.spectrum_eq (φ.restrictScalars ℝ).toAlgEquiv X
  by_cases h : IsSelfAdjoint X ∧ ContinuousOn Real.log (spectrum ℝ X)
  · exact StarAlgHomClass.map_cfc (S := ℂ) φ Real.log X h.2
      (map_continuous φ) h.1 (hn.mpr h.1)
  · rw [cfc_apply_of_not_and X h, map_zero, cfc_apply_of_not_and]
    rwa [hn, hs]

private theorem b03_umegaki_norm_push {A : Type u} [Qudit A] [Nontrivial A]
    {B : Type} [Qudit B] [Nontrivial B] (U : A ≃ₗᵢ[ℂ] B) (ρ σ : L A) :
    SandwichedRenyiRelativeEntropy.umegakiNorm (b03_conj U ρ) (b03_conj U σ) =
      SandwichedRenyiRelativeEntropy.umegakiNorm ρ σ := by
  unfold SandwichedRenyiRelativeEntropy.umegakiNorm
  rw [← b03_log, ← b03_log, ← map_sub, ← map_mul, b03_trace, b03_trace]

private theorem b03_quasi_push {A : Type u} [Qudit A]
    {B : Type} [Qudit B] (U : A ≃ₗᵢ[ℂ] B) (ρ σ : L A) (α : ℝ) :
    SandwichedRenyiRelativeEntropy.sandwichedQuasi α (b03_conj U ρ) (b03_conj U σ) =
      SandwichedRenyiRelativeEntropy.sandwichedQuasi α ρ σ := by
  unfold SandwichedRenyiRelativeEntropy.sandwichedQuasi
  rw [← b03_rpow, ← map_mul, ← map_mul, ← b03_rpow, b03_trace]

private theorem b03_du_push {A : Type u} [Qudit A] [Nontrivial A]
    (S : QuantumModel.Sys)
    (U : A ≃ₗᵢ[ℂ] QuantumModel.Space S) (ρ σ : State A) :
    du (push0 U ρ.1) (push0 U σ.1) = du ρ.1 σ.1 := by
  have hs := ((GourResource.gsl_b01.2.1 S U).2 ρ.1 σ.1).2.2.2
  unfold du SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN
  simp only [SandwichedRenyiRelativeEntropy.suppLE] at hs
  rw [← hs]
  congr 1
  split_ifs
  · exact congrArg (fun x : ℝ => (x : EReal)) (b03_umegaki_norm_push U ρ.1 σ.1)
  · rfl

private theorem b03_sand_push {A : Type u} [Qudit A] [Nontrivial A]
    (S : QuantumModel.Sys)
    (U : A ≃ₗᵢ[ℂ] QuantumModel.Space S)
    (ρ σ : State A) (α : ℝ) (hα : 1 < α) :
    sand α (push0 U ρ.1) (push0 U σ.1) = sand α ρ.1 σ.1 := by
  have hρ := (((GourResource.gsl_b01.2.1 S U).2 ρ.1 σ.1).1).mp ρ.2
  have hσ := (((GourResource.gsl_b01.2.1 S U).2 σ.1 ρ.1).1).mp σ.2
  have hs := ((GourResource.gsl_b01.2.1 S U).2 ρ.1 σ.1).2.2.2
  rw [b03_sand_formula _ _ hρ hσ α hα, b03_sand_formula _ _ ρ.2 σ.2 α hα]
  congr 1
  unfold SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN
  by_cases hs' : SandwichedRenyiRelativeEntropy.suppLE ρ.1 σ.1
  · rw [if_neg (by
      rintro (⟨_, hn⟩ | ⟨hlt, _⟩)
      · exact hn (hs.mp hs')
      · exact (not_lt_of_ge hα.le) hlt)]
    rw [if_neg (by
      rintro (⟨_, hn⟩ | ⟨hlt, _⟩)
      · exact hn hs'
      · exact (not_lt_of_ge hα.le) hlt)]
    change (SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv
        α (b03_conj U ρ.1) (b03_conj U σ.1) : EReal) = _
    unfold SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv
    rw [b03_quasi_push, b03_trace]
  · rw [if_pos (Or.inl ⟨hα, fun h => hs' (hs.mpr h)⟩),
      if_pos (Or.inl ⟨hα, hs'⟩)]

private theorem b03_petz_power_push {A : Type u} [Qudit A]
    {B : Type} [Qudit B] (U : A ≃ₗᵢ[ℂ] B) (ρ σ : L A)
    (α : ℝ) (hα : α ∈ Set.Ioo 0 1) :
    OPT.petzSupportTracePower α (b03_conj U ρ) (b03_conj U σ) =
      OPT.petzSupportTracePower α ρ σ := by
  rw [b03_petz_power _ _ α hα, b03_petz_power _ _ α hα,
    ← b03_rpow, ← b03_rpow, ← map_mul, b03_trace]

private theorem b03_petz_push {A : Type u} [Qudit A] [Nontrivial A]
    (S : QuantumModel.Sys)
    (U : A ≃ₗᵢ[ℂ] QuantumModel.Space S)
    (ρ σ : State A) (α : ℝ) (hα : α ∈ Set.Ioo 0 1) :
    petz α (push0 U ρ.1) (push0 U σ.1) = petz α ρ.1 σ.1 := by
  have hρ := (((GourResource.gsl_b01.2.1 S U).2 ρ.1 σ.1).1).mp ρ.2
  have hσ := (((GourResource.gsl_b01.2.1 S U).2 σ.1 ρ.1).1).mp σ.2
  rw [b03_petz_formula _ _ hρ hσ α hα, b03_petz_formula _ _ ρ.2 σ.2 α hα]
  have hq := b03_petz_power_push U ρ.1 σ.1 α hα
  change OPT.petzSupportTracePower α (push0 U ρ.1) (push0 U σ.1) = _ at hq
  rw [hq]

private theorem b03_sand_bound_native
    (S : QuantumModel.Sys)
    (ρ σ : QuantumModel.DensityMatrix S)
    (ε α : ℝ) (hε : ε ∈ Set.Ico 0 1) (hα : 1 < α) :
    dh ρ.operator σ.operator ε ≤ sand α ρ.operator σ.operator +
      ((α / (α - 1) * Real.logb 2 (1 / (1 - ε)) : ℝ) : EReal) := by
  let e : OPT.ProbabilityLevel := ⟨ε, hε.1, hε.2.le⟩
  have h :=
    QuantumModel.NativeHypothesisTesting.hypothesisTestingDiv_le_sandwichedRenyi
      α hα e hε.2 ρ σ.operator σ.nonneg
  rw [← (GourResource.gsl_b02.{0}.1 S ρ σ e).2.1, ← b03_sand_native S ρ σ α hα] at h
  exact h

private theorem b03_umegaki_bound_native
    (S : QuantumModel.Sys)
    (ρ σ : QuantumModel.DensityMatrix S)
    (ε : ℝ) (hε : ε ∈ Set.Ioo 0 1) :
    ((1 - ε : ℝ) : EReal) * dh ρ.operator σ.operator ε ≤
      du ρ.operator σ.operator + ((hb ε : ℝ) : EReal) := by
  let e : OPT.ProbabilityLevel := ⟨ε, hε.1.le, hε.2.le⟩
  have hσ0 : σ.operator ≠ 0 := by
    intro hzero
    have ht := σ.trace_one
    rw [hzero, map_zero] at ht
    exact zero_ne_one ht
  have hb' :
      QuantumModel.NativeHypothesisTesting.binaryEntropyBits e =
        hb ε := by
    unfold QuantumModel.NativeHypothesisTesting.binaryEntropyBits
    rw [if_neg (by exact not_or.mpr ⟨ne_of_gt hε.1, ne_of_lt hε.2⟩)]
    rfl
  have h :=
    QuantumModel.NativeHypothesisTesting.hypothesisTestingDiv_le_umegaki
      e hε.2 ρ σ.operator σ.nonneg hσ0
  rw [← (GourResource.gsl_b02.{0}.1 S ρ σ e).2.1, ← b03_du_native S ρ σ, hb',
    σ.trace_one] at h
  simp only [Complex.one_re, Real.logb_one, mul_zero, EReal.coe_zero, add_zero] at h
  have hscale : (0 : EReal) ≤ ((1 - ε : ℝ) : EReal) :=
    EReal.coe_nonneg.mpr (sub_nonneg.mpr hε.2.le)
  have hh := mul_le_mul_of_nonneg_left h hscale
  have hc : (1 - ε) * (1 / (1 - ε)) = (1 : ℝ) := by
    exact mul_one_div_cancel (ne_of_gt (sub_pos.mpr hε.2))
  rw [← mul_assoc, ← EReal.coe_mul, hc, EReal.coe_one, one_mul] at hh
  exact hh

private theorem b03_dh_push {A : Type u} [Qudit A] [Nontrivial A]
    (S : QuantumModel.Sys)
    (U : A ≃ₗᵢ[ℂ] QuantumModel.Space S)
    (ρ σ : State A) (ε : ℝ) (hε : ε ∈ Set.Ico 0 1) :
    dh (push0 U ρ.1) (push0 U σ.1) ε = dh ρ.1 σ.1 ε := by
  unfold dh
  rw [GourResource.gsl_b02.2.1 S U ρ σ ε hε]

private theorem b03_sand_bound {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : State A) (ε α : ℝ) (hε : ε ∈ Set.Ico 0 1) (hα : 1 < α) :
    dh ρ.1 σ.1 ε ≤ sand α ρ.1 σ.1 +
      ((α / (α - 1) * Real.logb 2 (1 / (1 - ε)) : ℝ) : EReal) := by
  obtain ⟨S, _, ⟨U⟩⟩ := GourResource.gsl_b01.1 (A := A)
  obtain ⟨e, he⟩ := (GourResource.gsl_b01.2.1 S U).1
  have h := b03_sand_bound_native S (e ρ) (e σ) ε α hε hα
  rw [he ρ, he σ, b03_dh_push S U ρ σ ε hε,
    b03_sand_push S U ρ σ α hα] at h
  exact h

private theorem b03_umegaki_bound {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : State A) (ε : ℝ) (hε : ε ∈ Set.Ioo 0 1) :
    ((1 - ε : ℝ) : EReal) * dh ρ.1 σ.1 ε ≤ du ρ.1 σ.1 + ((hb ε : ℝ) : EReal) := by
  obtain ⟨S, _, ⟨U⟩⟩ := GourResource.gsl_b01.1 (A := A)
  obtain ⟨e, he⟩ := (GourResource.gsl_b01.2.1 S U).1
  have h := b03_umegaki_bound_native S (e ρ) (e σ) ε hε
  rw [he ρ, he σ, b03_dh_push S U ρ σ ε ⟨hε.1.le, hε.2⟩,
    b03_du_push S U ρ σ] at h
  exact h

/-- Correspondence with the finite-dimensional model for Rényi-type relative entropies (a
foundation): the Umegaki relative entropy `du`, the sandwiched Rényi divergence `sand` for
`α > 1` and the Petz–Rényi divergence `petz` for `0 < α < 1` agree with the model's
quantities and are invariant under isometric transport. Moreover
`dh ≤ sand + α/(α-1) · log₂ (1/(1-ε))` for `ε ∈ [0, 1)` and `α > 1`, and
`(1 - ε) · dh ≤ du + hb ε` for `ε ∈ (0, 1)`, where `hb` is the binary entropy. -/
theorem gsl_b03 :
(∀ (S : QuantumModel.Sys) (ρ σ :
  QuantumModel.DensityMatrix S),
  du ρ.operator σ.operator =
    QuantumModel.NativeHypothesisTesting.umegakiRelEntropyBits ρ
    σ.operator ∧
  (∀ α : ℝ, 1 < α →
    sand α ρ.operator σ.operator =
      QuantumModel.NativeHypothesisTesting.sandwichedRenyiDivBits α ρ
      σ.operator) ∧
  (∀ α : ℝ, α ∈ Set.Ioo 0 1 →
    petz α ρ.operator σ.operator =
      QuantumModel.NativeHypothesisTesting.petzRenyiDivBits α ρ
      σ.operator)) ∧
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (S : QuantumModel.Sys) (U : A
  ≃ₗᵢ[ℂ] QuantumModel.Space S) (ρ σ : State.{u} A),
  du (push0.{u} U ρ.1) (push0.{u} U σ.1) = du ρ.1 σ.1 ∧
  (∀ α : ℝ, 1 < α → sand α (push0.{u} U ρ.1) (push0.{u} U σ.1) = sand α ρ.1 σ.1) ∧
  (∀ α : ℝ, α ∈ Set.Ioo 0 1 → petz α (push0.{u} U ρ.1) (push0.{u} U σ.1) = petz α ρ.1 σ.1)) ∧
((∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (ε α : ℝ), ε ∈ Set.Ico 0 1 → 1 <
  α →
  dh.{u} ρ.1 σ.1 ε ≤ sand.{u} α ρ.1 σ.1 +
    ((α/(α-1)*Real.logb 2 (1/(1-ε)) : ℝ) : EReal))) ∧
((∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (ε : ℝ), ε ∈ Set.Ioo 0 1 →
  ((1-ε : ℝ) : EReal) * dh.{u} ρ.1 σ.1 ε ≤ du.{u} ρ.1 σ.1 + ((hb ε : ℝ) : EReal)))
:= by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S ρ σ
    exact ⟨b03_du_native S ρ σ, b03_sand_native S ρ σ, b03_petz_native S ρ σ⟩
  · intro A _ _ S U ρ σ
    exact ⟨b03_du_push S U ρ σ, b03_sand_push S U ρ σ, b03_petz_push S U ρ σ⟩
  · exact b03_sand_bound
  · exact b03_umegaki_bound

end GourResource

