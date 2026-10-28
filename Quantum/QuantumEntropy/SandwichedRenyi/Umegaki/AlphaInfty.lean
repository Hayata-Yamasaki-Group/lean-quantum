/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.SandwichedRenyiNonNeg
import Quantum.QuantumEntropy.SandwichedRenyi.NonNeg.Approximation
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.QuasiJensen.Cone
import Quantum.QuantumEntropy.Common.TraceReGeneralizedStein
import Quantum.QuantumEntropy.Common.TraceRe

/-!
# Max-relative entropy as the α = ∞ limit

The Frank-Lieb limiting argument as `α → ∞`, including the positive-definite and
positive-semidefinite data-processing inequalities for max-relative entropy.
-/
namespace SandwichedRenyiRelativeEntropy

open GeneralizedPerspectiveFunction QuantumState QuantumChannel MeasureTheory
open scoped ComplexOrder NNReal Topology

universe u

section Umegaki

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

omit [Nontrivial ℋ] in
private lemma alphaInfty_toCLM_toLinearMap (f : B ℋ) :
    (f : L ℋ).toContinuousLinearMap = f := by
  ext x
  rfl

omit [Nontrivial ℋ] in
private lemma alphaInfty_rpow_toContinuousLinearMap (A : L ℋ) (p : ℝ) :
    (CFC.rpow A p).toContinuousLinearMap = CFC.rpow A.toContinuousLinearMap p := by
  let e : L ℋ ≃⋆ₐ[ℂ] B ℋ :=
    { LinearMap.toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      map_star' := fun A => by
        simpa using (LinearMap.adjoint_toContinuousLinearMap (A := A)) }
  letI : IsScalarTower ℝ≥0 ℂ (L ℋ) :=
    ⟨fun r c x => by
      change ((r : ℂ) * c) • x = (r : ℂ) • c • x
      rw [mul_smul]⟩
  letI : IsScalarTower ℝ≥0 ℂ (B ℋ) :=
    ⟨fun r c x => by
      change ((r : ℂ) * c) • x = (r : ℂ) • c • x
      rw [mul_smul]⟩
  let eNN : L ℋ ≃ₐ[ℝ≥0] B ℋ := e.toAlgEquiv.restrictScalars ℝ≥0
  change e (cfc (fun x : ℝ≥0 => x ^ p) A) = cfc (fun x : ℝ≥0 => x ^ p) (e A)
  by_cases hA : 0 ≤ A
  · have heA : (0 : B ℋ) ≤ e A := by
      exact (ContinuousLinearMap.coe_le_coe_iff
        (0 : B ℋ) A.toContinuousLinearMap).mp hA
    by_cases hf : ContinuousOn (fun x : ℝ≥0 => x ^ p) (spectrum ℝ≥0 A)
    · exact StarAlgHomClass.map_cfc (R := ℝ≥0) (S := ℂ) e _ A hf
        (StarAlgEquiv.isometry e).continuous hA heA
    · have hf' : ¬ ContinuousOn (fun x : ℝ≥0 => x ^ p)
          (spectrum ℝ≥0 (e A)) := by
        rw [show e A = eNN A from rfl, AlgEquiv.spectrum_eq eNN A]
        exact hf
      rw [cfc_apply_of_not_continuousOn A hf,
        cfc_apply_of_not_continuousOn (e A) hf', map_zero]
  · have heA : ¬ (0 : B ℋ) ≤ e A := by
      intro heA
      exact hA ((ContinuousLinearMap.coe_le_coe_iff
        (0 : B ℋ) A.toContinuousLinearMap).mpr heA)
    rw [cfc_apply_of_not_predicate A hA,
      cfc_apply_of_not_predicate (e A) heA, map_zero]

omit [Nontrivial ℋ] in
private lemma alphaInfty_rpow_toLinearMap (A : B ℋ) (p : ℝ) :
    ((CFC.rpow A p : B ℋ) : L ℋ) =
      CFC.rpow (A : L ℋ) p := by
  have h := alphaInfty_rpow_toContinuousLinearMap (A : L ℋ) p
  rw [alphaInfty_toCLM_toLinearMap] at h
  simpa using (congrArg ContinuousLinearMap.toLinearMap h).symm

omit [Nontrivial ℋ] in
private lemma alphaInfty_sandwichedQuasi_eq_clm_direct
    (a : ℝ) (rho sigma : B ℋ) :
    sandwichedQuasi a (rho : L ℋ) (sigma : L ℋ) =
      Tr ((CFC.rpow
        (CFC.rpow sigma ((1 - a) / (2 * a)) * rho *
          CFC.rpow sigma ((1 - a) / (2 * a))) a : B ℋ) : L ℋ) := by
  rw [sandwichedQuasi_eq_direct]
  change Tr (CFC.rpow
      (CFC.rpow (sigma : L ℋ) ((1 - a) / (2 * a)) * (rho : L ℋ) *
        CFC.rpow (sigma : L ℋ) ((1 - a) / (2 * a))) a) =
    Tr ((CFC.rpow
      (CFC.rpow sigma ((1 - a) / (2 * a)) * rho *
        CFC.rpow sigma ((1 - a) / (2 * a))) a : QuantumState.B ℋ) : L ℋ)
  rw [alphaInfty_rpow_toLinearMap]
  change _ = Tr (CFC.rpow
    (((CFC.rpow sigma ((1 - a) / (2 * a)) : QuantumState.B ℋ) : L ℋ) *
      (rho : L ℋ) *
      ((CFC.rpow sigma ((1 - a) / (2 * a)) : QuantumState.B ℋ) : L ℋ)) a)
  rw [alphaInfty_rpow_toLinearMap]

/-! ### α = ∞ as the `α → ∞` limit (Frank–Lieb limiting argument)

Following the same limiting strategy as the `α = 1` case, we show the sandwiched
Rényi divergence converges, as `α → ∞`, to the max-relative entropy
`log ‖σ^{-1/2} ρ σ^{-1/2}‖`, and re-derive its data-processing inequality from the
finite-`α` monotonicity (`RenyiDPI.sandwichedRenyiDivNN_monotone`) by passing to the limit.

The convergence rests on the elementary squeeze `‖B‖^α ≤ Tr(B^α) ≤ d·‖B‖^α` for a
non-negative operator `B` (with `d = dim ℋ`), i.e. the `ℓ^α → ℓ^∞` collapse of the
spectrum. -/

private lemma norm_le_re_trace_lm {C : L ℋ} (hC : 0 ≤ C) :
    ‖C‖ ≤ (Tr C).re := by
  have hCc : (0 : B ℋ) ≤ C.toContinuousLinearMap :=
    (ContinuousLinearMap.coe_le_coe_iff _ _).mp (by simpa using hC)
  simpa using QuantumEntropy.norm_le_re_trace hCc

omit [Nontrivial ℋ] in
private lemma re_trace_le_finrank_norm_lm {C : L ℋ} (hC : 0 ≤ C) :
    (Tr C).re ≤ (Module.finrank ℂ ℋ : ℝ) * ‖C‖ := by
  have hCc : (0 : B ℋ) ≤ C.toContinuousLinearMap :=
    (ContinuousLinearMap.coe_le_coe_iff _ _).mp (by simpa using hC)
  simpa using QuantumEntropy.re_trace_le_finrank_norm hCc

/-- **The `α → ∞` limit.** For positive-definite `ρ, σ`, the sandwiched Rényi
    divergence converges, as `α → ∞`, to the max-relative entropy `maxRelEntropyNN ρ σ`
    (`= log ‖σ^{-1/2} ρ σ^{-1/2}‖`). -/
lemma sandwichedRenyiDiv_tendsto_maxRel
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    Filter.Tendsto (fun α => ((sandwichedRenyiDiv α
      ρ σ : ℝ) : EReal)) Filter.atTop
      (𝓝 (maxRelEntropyNN ρ σ)) := by
  have hρ_sp : IsStrictlyPositive ρ := (pdSetLM_strictPositivity_certificate ρ).1 hρ
  have hσ_sp : IsStrictlyPositive σ := (pdSetLM_strictPositivity_certificate σ).1 hσ
  have hρ_nn := hρ_sp.nonneg
  have hσ_nn := hσ_sp.nonneg
  have hρ0 : ρ ≠ 0 := hρ_sp.isUnit.ne_zero
  have hsupp : SupportLE ρ σ := suppLE_of_pdSetLM_right _ hσ
  rw [maxRelEntropyNN_eq_log_norm hsupp]
  refine EReal.tendsto_coe.mpr ?_
  have hr_pos : 0 < (Tr ρ).re := QuantumEntropy.trace_re_pos_of_ne_zero hρ_nn hρ0
  set r := (Tr ρ).re with hr
  set d := (Module.finrank ℂ ℋ : ℝ) with hd
  have hd_pos : 0 < d := by rw [hd]; exact_mod_cast Module.finrank_pos
  set nA := ‖CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2))‖ with hnA
  have hnA_pos : 0 < nA := by
    rw [hnA, ← sInf_maxRelSet_eq_norm hρ_nn hσ_nn hsupp]
    exact sInf_maxRelSet_pos hρ_nn hσ_nn hρ0 hsupp
  have hM_tendsto : Filter.Tendsto
      (fun α : ℝ => CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α)))
      Filter.atTop (𝓝 (CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2)))) :=
    ((tendsto_rpow_exponent_atTop hσ_nn).mul tendsto_const_nhds).mul
      (tendsto_rpow_exponent_atTop hσ_nn)
  have hm_tendsto : Filter.Tendsto
      (fun α : ℝ => ‖CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 *
        α))‖)
      Filter.atTop (𝓝 nA) := by rw [hnA]; exact hM_tendsto.norm
  have h_logm : Filter.Tendsto
      (fun α : ℝ => Real.log ‖CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 -
        α) / (2 * α))‖)
      Filter.atTop (𝓝 (Real.log nA)) :=
    (Real.continuousAt_log (ne_of_gt hnA_pos)).tendsto.comp hm_tendsto
  have h_inv : Filter.Tendsto (fun α : ℝ => 1 / (α - 1)) Filter.atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds <| by
      simpa using Filter.tendsto_atTop_add_const_right Filter.atTop (-1) Filter.tendsto_id
  have h_ratio : Filter.Tendsto (fun α : ℝ => α / (α - 1)) Filter.atTop (𝓝 1) := by
    have heq : (fun α : ℝ => α / (α - 1)) =ᶠ[Filter.atTop] (fun α => 1 + 1 / (α - 1)) := by
      filter_upwards [Filter.eventually_gt_atTop (1:ℝ)] with α hα
      field_simp [sub_ne_zero.mpr (ne_of_gt hα)]; ring
    rw [Filter.tendsto_congr' heq]
    simpa using tendsto_const_nhds.add h_inv
  set Lf : ℝ → ℝ := fun α =>
    α / (α - 1) * Real.log ‖CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α)
      / (2 * α))‖
      - 1 / (α - 1) * Real.log r with hLf
  set Uf : ℝ → ℝ := fun α =>
    α / (α - 1) * Real.log ‖CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α)
      / (2 * α))‖
      + 1 / (α - 1) * (Real.log d - Real.log r) with hUf
  have hL : Filter.Tendsto Lf Filter.atTop (𝓝 (Real.log nA)) := by
    rw [hLf]; simpa using (h_ratio.mul h_logm).sub (h_inv.mul_const (Real.log r))
  have hU : Filter.Tendsto Uf Filter.atTop (𝓝 (Real.log nA)) := by
    rw [hUf]; simpa using (h_ratio.mul h_logm).add (h_inv.mul_const (Real.log d - Real.log r))
  have hbounds : ∀ᶠ α : ℝ in Filter.atTop,
      Lf α ≤ sandwichedRenyiDiv α ρ σ ∧ sandwichedRenyiDiv α ρ σ ≤ Uf α := by
    filter_upwards [Filter.eventually_gt_atTop (1:ℝ)] with α hα1
    have hα0 : 0 < α := by linarith
    have hαm1 : 0 < α - 1 := by linarith
    have hinv_nn : 0 ≤ 1 / (α - 1) := le_of_lt (div_pos one_pos hαm1)
    set Mα := CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α)) with
      hMαdef
    have hMα_sp : IsStrictlyPositive Mα :=
      ⟨conjugate_nonneg_of_nonneg hρ_nn CFC.rpow_nonneg,
        (((hσ_sp.rpow).isUnit.mul hρ_sp.isUnit).mul (hσ_sp.rpow).isUnit)⟩
    have hMα_nn : (0 : L ℋ) ≤ Mα := hMα_sp.nonneg
    have hm_pos : 0 < ‖Mα‖ := norm_pos_iff.mpr hMα_sp.isUnit.ne_zero
    have hCnn : (0 : L ℋ) ≤ CFC.rpow Mα α := CFC.rpow_nonneg
    have hnorm_eq : ‖CFC.rpow Mα α‖ = ‖Mα‖ ^ α := CFC.norm_rpow Mα hα0 hMα_nn
    set q := (sandwichedQuasi α ρ σ).re with hq
    have hq_eq : q = (Tr (CFC.rpow Mα α)).re := by
      rw [hq, sandwichedQuasi_eq_direct]
    have hq_lo : ‖Mα‖ ^ α ≤ q := by
      rw [hq_eq, ← hnorm_eq]; exact norm_le_re_trace_lm hCnn
    have hq_hi : q ≤ d * ‖Mα‖ ^ α := by
      rw [hq_eq, ← hnorm_eq]; exact re_trace_le_finrank_norm_lm hCnn
    have hmα_pos : 0 < ‖Mα‖ ^ α := Real.rpow_pos_of_pos hm_pos α
    have hq_pos : 0 < q := lt_of_lt_of_le hmα_pos hq_lo
    have hlogq_lo : α * Real.log ‖Mα‖ ≤ Real.log q := by
      rw [← Real.log_rpow hm_pos]; exact Real.log_le_log hmα_pos hq_lo
    have hlogq_hi : Real.log q ≤ Real.log d + α * Real.log ‖Mα‖ := by
      have h := Real.log_le_log hq_pos hq_hi
      rwa [Real.log_mul (ne_of_gt hd_pos) (ne_of_gt hmα_pos), Real.log_rpow hm_pos] at h
    have hD : sandwichedRenyiDiv α ρ σ =
        1 / (α - 1) * (Real.log q - Real.log r) := by
      unfold sandwichedRenyiDiv
      rw [← hq, ← hr, Real.log_div (ne_of_gt hq_pos) (ne_of_gt hr_pos)]
    refine ⟨?_, ?_⟩
    · simp only [hLf]; rw [← hMαdef, hD]
      have hstep := mul_le_mul_of_nonneg_left (sub_le_sub_right hlogq_lo (Real.log r)) hinv_nn
      calc α / (α - 1) * Real.log ‖Mα‖ - 1 / (α - 1) * Real.log r
            = 1 / (α - 1) * (α * Real.log ‖Mα‖ - Real.log r) := by ring
        _ ≤ 1 / (α - 1) * (Real.log q - Real.log r) := hstep
    · simp only [hUf]; rw [← hMαdef, hD]
      have hstep := mul_le_mul_of_nonneg_left (sub_le_sub_right hlogq_hi (Real.log r)) hinv_nn
      calc 1 / (α - 1) * (Real.log q - Real.log r)
            ≤ 1 / (α - 1) * ((Real.log d + α * Real.log ‖Mα‖) - Real.log r) := hstep
        _ = α / (α - 1) * Real.log ‖Mα‖ + 1 / (α - 1) * (Real.log d - Real.log r) := by
            ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

/-- **Data-processing for the max-relative entropy, via the `α → ∞` limit**
    (Frank–Lieb's limiting argument; positive-definite case). An alternative proof of
    `maxRelEntropyNN_monotone`: the finite-`α` monotonicity passes to the limit. -/
theorem maxRelEntropyNN_monotone_via_limit
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ))
    (hEρ : E.toFun ρ ∈ pdSetLM (ℋ := 𝒦))
    (hEσ : E.toFun σ ∈ pdSetLM (ℋ := 𝒦)) :
    maxRelEntropyNN (E.toFun ρ) (E.toFun σ) ≤ maxRelEntropyNN ρ σ := by
  have hlim1 := sandwichedRenyiDiv_tendsto_maxRel hEρ hEσ
  have hlim2 := sandwichedRenyiDiv_tendsto_maxRel hρ hσ
  refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ)] with α hα1
  have hρ_nn : 0 ≤ ρ := nonneg_of_pdSetLM hρ
  have hσ_nn : 0 ≤ σ := nonneg_of_pdSetLM hσ
  have hsupp : SupportLE ρ σ := suppLE_of_pdSetLM_right _ hσ
  have hEsupp : SupportLE (E.toFun ρ) (E.toFun σ) :=
    suppLE_of_pdSetLM_right _ hEσ
  have hval : ∀ {ℋ'' : Type u} [Qudit ℋ''] [Nontrivial ℋ'']
      (ρ'' σ'' : L ℋ''),
      SupportLE ρ'' σ'' →
      sandwichedRenyiDivNN α ρ'' σ'' =
        ((sandwichedRenyiDiv α ρ'' σ'' : ℝ) : EReal) := by
    intro ℋ'' _ _ ρ'' σ'' hs
    unfold sandwichedRenyiDivNN
    rw [if_neg]
    rintro (⟨_, hns⟩ | ⟨hlt, _⟩)
    · exact hns hs
    · linarith
  have hmono := RenyiDPI.sandwichedRenyiDivNN_monotone E (by linarith) (ne_of_gt hα1)
    hρ_nn hσ_nn
  rw [hval _ _ hEsupp, hval _ _ hsupp] at hmono
  exact hmono

/-! ### Positive-semidefinite α = ∞ limit and DPI -/
/-- **The `α → ∞` limit, positive-semidefinite case.** For non-negative `ρ, σ` with
    `SupportLE ρ σ` and `ρ ≠ 0`, the sandwiched Rényi divergence converges, as `α →
      ∞`, to
    the max-relative entropy `maxRelEntropyNN ρ σ` (`= log ‖σ^{-1/2} ρ σ^{-1/2}‖`,
    Moore–Penrose power). The pd proof carries over: exponent-continuity
    `tendsto_rpow_exponent_atTop` holds even at singular `σ`, and `‖M_α‖ > 0` holds
    *eventually* (it converges to `‖A‖ > 0`). -/
lemma sandwichedRenyiDiv_tendsto_maxRel_nn
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hsupp : SupportLE ρ σ) (hρ0 : ρ ≠ 0) :
    Filter.Tendsto (fun α => ((sandwichedRenyiDiv α
      ρ σ : ℝ) : EReal)) Filter.atTop
      (𝓝 (maxRelEntropyNN ρ σ)) := by
  rw [maxRelEntropyNN_eq_log_norm hsupp]
  refine EReal.tendsto_coe.mpr ?_
  have hr_pos : 0 < (Tr ρ).re := QuantumEntropy.trace_re_pos_of_ne_zero hρ hρ0
  set r := (Tr ρ).re with hr
  set d := (Module.finrank ℂ ℋ : ℝ) with hd
  have hd_pos : 0 < d := by rw [hd]; exact_mod_cast Module.finrank_pos
  set nA := ‖CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2))‖ with hnA
  have hnA_pos : 0 < nA := by
    rw [hnA, ← sInf_maxRelSet_eq_norm hρ hσ hsupp]
    exact sInf_maxRelSet_pos hρ hσ hρ0 hsupp
  have hM_tendsto : Filter.Tendsto
      (fun α : ℝ => CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α)))
      Filter.atTop (𝓝 (CFC.rpow σ (-(1/2)) * ρ * CFC.rpow σ (-(1/2)))) :=
    ((tendsto_rpow_exponent_atTop hσ).mul tendsto_const_nhds).mul (tendsto_rpow_exponent_atTop hσ)
  have hm_tendsto : Filter.Tendsto
      (fun α : ℝ => ‖CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 *
        α))‖)
      Filter.atTop (𝓝 nA) := by rw [hnA]; exact hM_tendsto.norm
  have h_logm : Filter.Tendsto
      (fun α : ℝ => Real.log ‖CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 -
        α) / (2 * α))‖)
      Filter.atTop (𝓝 (Real.log nA)) :=
    (Real.continuousAt_log (ne_of_gt hnA_pos)).tendsto.comp hm_tendsto
  have hev_pos : ∀ᶠ α : ℝ in Filter.atTop,
      0 < ‖CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α))‖ :=
    hm_tendsto.eventually (eventually_gt_nhds hnA_pos)
  have h_inv : Filter.Tendsto (fun α : ℝ => 1 / (α - 1)) Filter.atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds <| by
      simpa using Filter.tendsto_atTop_add_const_right Filter.atTop (-1) Filter.tendsto_id
  have h_ratio : Filter.Tendsto (fun α : ℝ => α / (α - 1)) Filter.atTop (𝓝 1) := by
    have heq : (fun α : ℝ => α / (α - 1)) =ᶠ[Filter.atTop] (fun α => 1 + 1 / (α - 1)) := by
      filter_upwards [Filter.eventually_gt_atTop (1:ℝ)] with α hα
      field_simp [sub_ne_zero.mpr (ne_of_gt hα)]; ring
    rw [Filter.tendsto_congr' heq]
    simpa using tendsto_const_nhds.add h_inv
  set Lf : ℝ → ℝ := fun α =>
    α / (α - 1) * Real.log ‖CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α)
      / (2 * α))‖
      - 1 / (α - 1) * Real.log r with hLf
  set Uf : ℝ → ℝ := fun α =>
    α / (α - 1) * Real.log ‖CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α)
      / (2 * α))‖
      + 1 / (α - 1) * (Real.log d - Real.log r) with hUf
  have hL : Filter.Tendsto Lf Filter.atTop (𝓝 (Real.log nA)) := by
    rw [hLf]; simpa using (h_ratio.mul h_logm).sub (h_inv.mul_const (Real.log r))
  have hU : Filter.Tendsto Uf Filter.atTop (𝓝 (Real.log nA)) := by
    rw [hUf]; simpa using (h_ratio.mul h_logm).add (h_inv.mul_const (Real.log d - Real.log r))
  have hbounds : ∀ᶠ α : ℝ in Filter.atTop,
      Lf α ≤ sandwichedRenyiDiv α ρ σ ∧ sandwichedRenyiDiv α ρ σ ≤ Uf α := by
    filter_upwards [Filter.eventually_gt_atTop (1:ℝ), hev_pos] with α hα1 hm_pos
    have hα0 : 0 < α := by linarith
    have hαm1 : 0 < α - 1 := by linarith
    have hinv_nn : 0 ≤ 1 / (α - 1) := le_of_lt (div_pos one_pos hαm1)
    set Mα := CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α)) with
      hMαdef
    have hMα_nn : (0 : L ℋ) ≤ Mα := conjugate_nonneg_of_nonneg hρ CFC.rpow_nonneg
    have hCnn : (0 : L ℋ) ≤ CFC.rpow Mα α := CFC.rpow_nonneg
    have hnorm_eq : ‖CFC.rpow Mα α‖ = ‖Mα‖ ^ α := CFC.norm_rpow Mα hα0 hMα_nn
    set q := (sandwichedQuasi α ρ σ).re with hq
    have hq_eq : q = (Tr (CFC.rpow Mα α)).re := by
      rw [hq, sandwichedQuasi_eq_direct]
    have hq_lo : ‖Mα‖ ^ α ≤ q := by
      rw [hq_eq, ← hnorm_eq]; exact norm_le_re_trace_lm hCnn
    have hq_hi : q ≤ d * ‖Mα‖ ^ α := by
      rw [hq_eq, ← hnorm_eq]; exact re_trace_le_finrank_norm_lm hCnn
    have hmα_pos : 0 < ‖Mα‖ ^ α := Real.rpow_pos_of_pos hm_pos α
    have hq_pos : 0 < q := lt_of_lt_of_le hmα_pos hq_lo
    have hlogq_lo : α * Real.log ‖Mα‖ ≤ Real.log q := by
      rw [← Real.log_rpow hm_pos]; exact Real.log_le_log hmα_pos hq_lo
    have hlogq_hi : Real.log q ≤ Real.log d + α * Real.log ‖Mα‖ := by
      have h := Real.log_le_log hq_pos hq_hi
      rwa [Real.log_mul (ne_of_gt hd_pos) (ne_of_gt hmα_pos), Real.log_rpow hm_pos] at h
    have hD : sandwichedRenyiDiv α ρ σ =
        1 / (α - 1) * (Real.log q - Real.log r) := by
      unfold sandwichedRenyiDiv
      rw [← hq, ← hr, Real.log_div (ne_of_gt hq_pos) (ne_of_gt hr_pos)]
    refine ⟨?_, ?_⟩
    · simp only [hLf]; rw [← hMαdef, hD]
      have hstep := mul_le_mul_of_nonneg_left (sub_le_sub_right hlogq_lo (Real.log r)) hinv_nn
      calc α / (α - 1) * Real.log ‖Mα‖ - 1 / (α - 1) * Real.log r
            = 1 / (α - 1) * (α * Real.log ‖Mα‖ - Real.log r) := by ring
        _ ≤ 1 / (α - 1) * (Real.log q - Real.log r) := hstep
    · simp only [hUf]; rw [← hMαdef, hD]
      have hstep := mul_le_mul_of_nonneg_left (sub_le_sub_right hlogq_hi (Real.log r)) hinv_nn
      calc 1 / (α - 1) * (Real.log q - Real.log r)
            ≤ 1 / (α - 1) * ((Real.log d + α * Real.log ‖Mα‖) - Real.log r) := hstep
        _ = α / (α - 1) * Real.log ‖Mα‖ + 1 / (α - 1) * (Real.log d - Real.log r) := by ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

-- The support hypothesis is kept so that the public type is unchanged, even though the
-- stronger direct monotonicity theorem does not need it.
/-- **Data-processing for the max-relative entropy, positive-semidefinite case.**
    For non-negative `ρ, σ` with `SupportLE ρ σ` and a CPTP map `E`,
    `maxRelEntropyNN (Eρ) (Eσ) ≤ maxRelEntropyNN ρ σ`. This is a specialization of the
    stronger direct monotonicity theorem `maxRelEntropyNN_monotone`, which does not need the
    support hypothesis. The name and the hypothesis `hsupp` are kept for compatibility of the
    public type; this wrapper itself does not take a limit in `α`. -/
theorem maxRelEntropyNN_monotone_via_limit_nn
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (_hsupp : SupportLE ρ σ) :
    maxRelEntropyNN (E.toFun ρ) (E.toFun σ) ≤ maxRelEntropyNN ρ σ := by
  exact maxRelEntropyNN_monotone E hρ hσ


end Umegaki

end SandwichedRenyiRelativeEntropy
