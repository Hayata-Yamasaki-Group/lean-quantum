/-
Lower bound of the hypothesis-testing relative entropy by the Petz–Rényi divergence of order α ∈ (0,1) (gsl_c10); compared with the constant −α/(1−α)·log₂(1/ε), the bound gains the additive term hb(α)/(1−α).
-/
/-
States the upper bound of dh by the sandwiched Rényi divergence (α > 1) and the Petz lower bound above (0 < α < 1) together for the same ε∈(0,1) (gsl_h01).
-/
import Quantum.QuantumEntropy.GourResource.TestingSDP
import Quantum.QuantumEntropy.GourResource.KWEntropyBridge
import Quantum.QuantumEntropy.GourResource.KWAudenaertBridge
import Mathlib.Analysis.MeanInequalities
import Quantum.QuantumModel.KW.Entropies.RenyiAnalysis.GSLCoreRetained
import Quantum.QuantumModel.POVMObservationBridge.GSLCore

open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower ℝ ℂ (L H) :=
  RestrictScalars.isScalarTower ℝ ℂ (L H)

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem c10_trace_positivePart {A : Type u} [Qudit A] (X : L A) :
    (Tr (positivePart X)).re = ((Tr X).re + w40T₁ X) / 2 := by
  simp only [positivePart, w40T₁, LinearMap.map_smul_of_tower, map_add, Complex.add_re,
    Complex.smul_re, smul_eq_mul]
  ring

-- The scaling law for `CFC.rpow`, stated over an abstract C⋆-algebra so that the `cfc`
-- rewriting is elaborated without the costly `L A` instance searches.
private theorem c10_rpow_scale_aux {R : Type*} [CStarAlgebra R] [PartialOrder R]
    [StarOrderedRing R] (X : R) (hX : 0 ≤ X) (c a : ℝ) (hc : 0 ≤ c) (ha : 0 < a) :
    CFC.rpow (c • X) a = (c ^ a) • CFC.rpow X a := by
  have hscaled : 0 ≤ c • X := smul_nonneg hc hX
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_pow]
  rw [CFC.rpow_eq_cfc_real (ha := hscaled), CFC.rpow_eq_cfc_real (ha := hX)]
  rw [← cfc_comp_smul (R := ℝ) c (fun x : ℝ => x ^ a) X
      (hf := (Real.continuous_rpow_const ha.le).continuousOn),
    ← cfc_smul (R := ℝ) (c ^ a) (fun x : ℝ => x ^ a) X
      (hf := (Real.continuous_rpow_const ha.le).continuousOn)]
  apply cfc_congr
  intro x hx
  exact Real.mul_rpow hc (spectrum_nonneg_of_nonneg hX hx)

private theorem c10_rpow_scale {A : Type u} [Qudit A]
    (X : L A) (hX : 0 ≤ X) (c a : ℝ) (hc : 0 ≤ c) (ha : 0 < a) :
    CFC.rpow (c • X) a = (c ^ a) • CFC.rpow X a :=
  c10_rpow_scale_aux X hX c a hc ha

private theorem c10_petz_finite {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : State A) (a : ℝ) (ha : a ∈ Set.Ioo 0 1)
    (hq : 0 < (Tr (CFC.rpow ρ.1 a * CFC.rpow σ.1 (1 - a))).re) :
    petz a ρ.1 σ.1 =
      ((Real.logb 2 (Tr (CFC.rpow ρ.1 a * CFC.rpow σ.1 (1 - a))).re /
        (a - 1) : ℝ) : EReal) := by
  have hpower : OPT.petzSupportTracePower a ρ.1 σ.1 =
      (Tr (CFC.rpow ρ.1 a * CFC.rpow σ.1 (1 - a))).re := by
    simp only [OPT.petzSupportTracePower,
      OPT.petzSupportRpow_of_ne_zero _ ha.1.ne',
      OPT.petzSupportRpow_of_ne_zero _ (sub_pos.mpr ha.2).ne']
  have hmul : ρ.1 * σ.1 ≠ 0 := by
    apply (OPT.petzSupportRpowMul_ne_zero_iff a ρ.1 σ.1 ρ.2 σ.2).mp
    intro hz
    have hq' : 0 < OPT.petzSupportTracePower a ρ.1 σ.1 := hpower.symm ▸ hq
    simp only [OPT.petzSupportTracePower, hz, map_zero, Complex.zero_re] at hq'
    exact (lt_irrefl 0) hq'
  have hadm : SandwichedRenyiRelativeEntropy.suppLE ρ.1 σ.1 ∨
      a < 1 ∧ ρ.1 * σ.1 ≠ 0 := Or.inr ⟨ha.2, hmul⟩
  simp only [petz, dif_pos ha.1.le, dif_pos ρ.2, dif_pos σ.2,
    OPT.petzQuantumRenyiDivergenceFinite, OPT.w26PetzQuantumRenyiDivergenceFinite,
    dif_neg ha.1.ne', dif_neg ha.2.ne, dif_pos hadm, hpower]
  congr 1
  ring

private theorem c10_scalar_bound (a ε q t : ℝ) (ha : a ∈ Set.Ioo 0 1)
    (hε : 0 < ε) (hq : 0 < q) (ht : 0 ≤ t) :
    -ε * t + t ^ a * q ≤
      (1 - a) * (q / (ε / a) ^ a) ^ (1 / (1 - a) : ℝ) := by
  let k := ε / a
  let B := (q / k ^ a) ^ (1 / (1 - a) : ℝ)
  have hk : 0 < k := div_pos hε ha.1
  have hka : 0 < k ^ a := Real.rpow_pos_of_pos hk _
  have hbase : 0 < q / k ^ a := div_pos hq hka
  have hB : 0 < B := Real.rpow_pos_of_pos hbase _
  have hBpow : B ^ (1 - a) = q / k ^ a := by
    dsimp only [B]
    rw [← Real.rpow_mul hbase.le, one_div,
      inv_mul_cancel₀ (sub_pos.mpr ha.2).ne', Real.rpow_one]
  have hAM := Real.geom_mean_le_arith_mean2_weighted ha.1.le
    (sub_pos.mpr ha.2).le (mul_nonneg hk.le ht) hB.le (by ring)
  have hprod : (k * t) ^ a * B ^ (1 - a) = t ^ a * q := by
    rw [Real.mul_rpow hk.le ht, hBpow]
    field_simp
  rw [hprod] at hAM
  have hkε : a * (k * t) = ε * t := by
    dsimp only [k]
    field_simp [ha.1.ne']
  rw [hkε] at hAM
  change -ε * t + t ^ a * q ≤ (1 - a) * B
  linarith

private theorem c10_log_radius (a ε q : ℝ) (ha : a ∈ Set.Ioo 0 1)
    (hε : 0 < ε) (hq : 0 < q) :
    Real.logb 2 q / (a - 1) +
        a / (1 - a) * (hb a / a - Real.logb 2 (1 / ε)) =
      -Real.logb 2 ((1 - a) * (q / (ε / a) ^ a) ^ (1 / (1 - a) : ℝ)) := by
  have hk : 0 < ε / a := div_pos hε ha.1
  have hka : 0 < (ε / a) ^ a := Real.rpow_pos_of_pos hk _
  have hbase : 0 < q / (ε / a) ^ a := div_pos hq hka
  have hB : 0 < (q / (ε / a) ^ a) ^ (1 / (1 - a) : ℝ) :=
    Real.rpow_pos_of_pos hbase _
  rw [Real.logb_mul (sub_pos.mpr ha.2).ne' hB.ne',
    Real.logb_rpow_eq_mul_logb_of_pos hbase,
    Real.logb_div hq.ne' hka.ne',
    Real.logb_rpow_eq_mul_logb_of_pos hk,
    Real.logb_div hε.ne' ha.1.ne']
  rw [one_div, Real.logb_inv]
  unfold hb
  field_simp [ha.1.ne', (sub_pos.mpr ha.2).ne', (sub_neg.mpr ha.2).ne]
  ring

private theorem c10_scalar_log (a ε q b t : ℝ) (ha : a ∈ Set.Ioo 0 1)
    (hε : 0 < ε) (hq : 0 < q) (hb : 0 < b) (ht : 0 ≤ t)
    (hbound : b ≤ -ε * t + t ^ a * q) :
    Real.logb 2 q / (a - 1) +
        a / (1 - a) * (GourResource.hb a / a - Real.logb 2 (1 / ε)) ≤
      -Real.logb 2 b := by
  rw [c10_log_radius a ε q ha hε hq]
  exact neg_le_neg (Real.logb_le_logb_of_le (by norm_num) hb
    (hbound.trans (c10_scalar_bound a ε q t ha hε hq ht)))

private theorem c10_scaled_trace {A : Type u} [Qudit A]
    (ρ σ : State A) (a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) :
    (Tr (CFC.rpow (t • ρ.1) a * CFC.rpow σ.1 (1 - a))).re =
      t ^ a * (Tr (CFC.rpow ρ.1 a * CFC.rpow σ.1 (1 - a))).re := by
  rw [c10_rpow_scale ρ.1 ((LinearMap.nonneg_iff_isPositive _).mpr ρ.2.1)
    t a ht ha, smul_mul_assoc, LinearMap.map_smul_of_tower, Complex.smul_re, smul_eq_mul]

private theorem c10_density_trace_scale {A : Type u} [Qudit A]
    (ρ : State A) (t : ℝ) : (Tr (t • ρ.1)).re = t := by
  rw [LinearMap.map_smul_of_tower, ρ.2.2, Complex.smul_re]
  simp

theorem gsl_c10 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (ε α : ℝ), ε ∈ Set.Ioo 0 1 → α ∈
  Set.Ioo 0 1 →
  petz.{u} α ρ.1 σ.1 + ((α/(1-α)*(hb α/α-Real.logb 2 (1/ε)) : ℝ) : EReal)
    ≤ dh.{u} ρ.1 σ.1 ε)
:= by
  intro A _ _ ρ σ ε α hε hα
  by_cases hb : beta ρ.1 σ.1 ε ≤ 0
  · have htop : dh ρ.1 σ.1 ε = ⊤ := by
      rw [dh, Real.toNNReal_of_nonpos hb, OPT.binaryNegLog2_zero]
    rw [htop]
    exact le_top
  have hbpos : 0 < beta ρ.1 σ.1 ε := lt_of_not_ge hb
  obtain ⟨t, W, ht, hW, hfeas, hdual⟩ := GourResource.gsl_c07b.{u} ρ σ ε hε
  have hρ : 0 ≤ ρ.1 := (LinearMap.nonneg_iff_isPositive _).mpr ρ.2.1
  have hσ : 0 ≤ σ.1 := (LinearMap.nonneg_iff_isPositive _).mpr σ.2.1
  have htρ : 0 ≤ t • ρ.1 := smul_nonneg ht hρ
  have hsym : (t • ρ.1 - σ.1).IsSymmetric :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr
      ((IsSelfAdjoint.of_nonneg htρ).sub (IsSelfAdjoint.of_nonneg hσ))
  have htrW : (Tr (positivePart (t • ρ.1 - σ.1))).re ≤ (Tr W).re := by
    apply (GourResource.gsl_c06.{u} (t • ρ.1 - σ.1) hsym).2
    refine ⟨W, hW, ?_, rfl⟩
    convert hfeas using 1
    abel
  have hAud := GourResource.gsl_b07.{u} (t • ρ.1) σ.1 (1 - α)
    ((LinearMap.nonneg_iff_isPositive _).mp htρ) σ.2.1
    ⟨(sub_pos.mpr hα.2).le, by linarith [hα.1]⟩
  rw [sub_sub_cancel, c10_scaled_trace ρ σ α t hα.1 ht,
    c10_density_trace_scale, σ.2.2] at hAud
  have htrpart := c10_trace_positivePart (t • ρ.1 - σ.1)
  rw [map_sub, Complex.sub_re, c10_density_trace_scale, σ.2.2] at htrpart
  let q := (Tr (CFC.rpow ρ.1 α * CFC.rpow σ.1 (1 - α))).re
  have hbound : beta ρ.1 σ.1 ε ≤ -ε * t + t ^ α * q := by
    dsimp only [q]
    simp only [Complex.one_re] at hAud htrpart
    nlinarith [hAud, htrpart, htrW, hdual]
  have hq : 0 < q := by
    by_contra h
    have hprod := mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg ht α)
      (le_of_not_gt h)
    have hεt := mul_nonneg hε.1.le ht
    linarith
  have hscalar := c10_scalar_log α ε q (beta ρ.1 σ.1 ε) t
    hα hε.1 hq hbpos ht hbound
  have hpetz := c10_petz_finite ρ σ α hα hq
  have hdh : dh ρ.1 σ.1 ε = ((-Real.logb 2 (beta ρ.1 σ.1 ε) : ℝ) : EReal) := by
    have hne : Real.toNNReal (beta ρ.1 σ.1 ε) ≠ 0 := by
      rw [ne_eq, Real.toNNReal_eq_zero]
      exact hb
    rw [dh, OPT.binaryNegLog2, if_neg hne, Real.coe_toNNReal _ hbpos.le]
  rw [hpetz, hdh, ← EReal.coe_add]
  exact EReal.coe_le_coe_iff.mpr hscalar

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_h01 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (ε : ℝ), ε ∈ Set.Ioo 0 1 →
  (∀ α : ℝ, 1 < α → dh.{u} ρ.1 σ.1 ε ≤ sand.{u} α ρ.1 σ.1 +
    ((α/(α-1)*Real.logb 2 (1/(1-ε)) : ℝ) : EReal)) ∧
  (∀ α : ℝ, α ∈ Set.Ioo 0 1 →
    petz.{u} α ρ.1 σ.1 + ((α/(1-α)*(hb α/α-Real.logb 2 (1/ε)) : ℝ) : EReal)
      ≤ dh.{u} ρ.1 σ.1 ε))
:= by
  intro A _ _ ρ σ ε hε
  exact And.intro
    (fun α hα => GourResource.gsl_b03.{u}.2.2.1 ρ σ ε α ⟨le_of_lt hε.1, hε.2⟩ hα)
    (fun α hα => GourResource.gsl_c10.{u} ρ σ ε α hε hα)

end GourResource

