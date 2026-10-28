/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.SandwichedRenyiBase.NonNeg.Continuity
import Quantum.QuantumEntropy.CFCTransport
import Quantum.QuantumMechanics.BridgeCertificates
import Quantum.QuantumEntropy.Common.Umegaki.GSLCore

/-!
# Umegaki relative entropy at α = 1

Definitions, the derivative calculation at `α = 1`, and the positive-definite
data-processing inequality for the Umegaki boundary case.
-/
namespace SandwichedRenyiRelativeEntropy

open GeneralizedPerspectiveFunction QuantumState QuantumChannel MeasureTheory
open scoped ComplexOrder NNReal Topology

universe u

section Umegaki

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

omit [Nontrivial ℋ] in
private lemma alphaOne_toCLM_toLinearMap (f : B ℋ) :
    (f : L ℋ).toContinuousLinearMap = f := by
  ext x
  rfl

omit [Nontrivial ℋ] in
private lemma alphaOne_rpow_toContinuousLinearMap (A : L ℋ) (p : ℝ) :
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
private lemma alphaOne_rpow_toLinearMap (A : B ℋ) (p : ℝ) :
    ((CFC.rpow A p : B ℋ) : L ℋ) =
      CFC.rpow (A : L ℋ) p := by
  have h := alphaOne_rpow_toContinuousLinearMap (A : L ℋ) p
  rw [alphaOne_toCLM_toLinearMap] at h
  simpa using (congrArg ContinuousLinearMap.toLinearMap h).symm

omit [Nontrivial ℋ] in
private lemma alphaOne_sandwichedQuasi_eq_clm_direct
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
        CFC.rpow sigma ((1 - a) / (2 * a))) a : B ℋ) : L ℋ)
  rw [alphaOne_rpow_toLinearMap]
  change _ = Tr (CFC.rpow
    (((CFC.rpow sigma ((1 - a) / (2 * a)) : B ℋ) : L ℋ) * (rho : L ℋ) *
      ((CFC.rpow sigma ((1 - a) / (2 * a)) : B ℋ) : L ℋ)) a)
  rw [alphaOne_rpow_toLinearMap]


/-! ### α = 1 derivative calculation and positive-definite DPI -/

omit [Nontrivial ℋ] in
/-- The quasi-entropy at `α = 1` is `Tr ρ`: the conjugating power
    `σ^{(1−1)/(2·1)} = σ^0 = 1`, leaving `(1 ρ 1)^1 = ρ`. -/
lemma sandwichedQuasi_one_re (ρ σ : B ℋ) (hσ : 0 ≤ σ) (hρ : 0 ≤ ρ) :
    (sandwichedQuasi 1 (ρ : L ℋ) (σ : L ℋ)).re =
      (Tr (ρ : L ℋ)).re := by
  have h : sandwichedQuasi 1 (ρ : L ℋ) (σ : L ℋ) =
      Tr (ρ : L ℋ) := by
    rw [alphaOne_sandwichedQuasi_eq_clm_direct]
    have hz : CFC.rpow σ ((1 - (1 : ℝ)) / (2 * 1)) = 1 := by
      rw [show ((1 - (1 : ℝ)) / (2 * 1)) = 0 by norm_num]
      exact CFC.rpow_zero σ hσ
    rw [hz, one_mul, mul_one, show CFC.rpow ρ 1 = ρ from CFC.rpow_one ρ hρ]
  rw [h]

omit [Nontrivial ℋ] in
private lemma alphaOne_trace_sub (A B : ℋ →L[ℂ] ℋ) :
    Tr ((A - B : ℋ →L[ℂ] ℋ) : L ℋ) =
      Tr (A : L ℋ) - Tr (B : L ℋ) := by
  change traceCLM (A - B) = traceCLM A - traceCLM B
  exact map_sub traceCLM A B

omit [Nontrivial ℋ] in
private lemma alphaOne_trace_neg (A : B ℋ) :
    Tr ((-A : B ℋ) : L ℋ) = -Tr (A : L ℋ) := by
  change traceCLM (-A) = -traceCLM A
  exact map_neg traceCLM A

omit [Nontrivial ℋ] in
/-- **Part B (proven): the conjugating-power contribution.** Differentiating the
    `α = 1` slice `α ↦ Re Tr(ρ · σ^{(1−α)/α})` (fixed base `σ`, exponent
    `(1−α)/α` with derivative `−1` at `α = 1`) gives `−Re Tr(ρ log σ)`.

    Proven from the fixed-base exponent derivative `CFC.hasDerivAt_rpow_exponent`
    (`CFCDeriv`), the chain rule, and `hasDerivAt_reTrace_mul_left`. -/
lemma hasDerivAt_partB {ρ σ : B ℋ} (hσ : σ ∈ pdSet (ℋ := ℋ)) :
    HasDerivAt (fun α =>
      (Tr ((ρ * CFC.rpow σ ((1 - α) / α) : B ℋ) : L ℋ)).re)
      (-(Tr ((ρ * CFC.log σ : B ℋ) : L ℋ)).re) 1 := by
  have hσsp : IsStrictlyPositive σ := GeneralizedPerspectiveFunction.isStrictlyPositive_of_pdSet hσ
  have hσnn : (0 : B ℋ) ≤ σ := hσsp.nonneg
  have ht : HasDerivAt (fun α : ℝ => (1 - α) / α) (-1) 1 := by
    have hu : HasDerivAt (fun α : ℝ => 1 - α) (-1) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).const_sub 1
    have hv : HasDerivAt (fun α : ℝ => α) (1) 1 := hasDerivAt_id 1
    simpa using hu.div hv (by norm_num)
  have hchain := CFC.hasDerivAt_rpow_exponent_comp hσsp ht
  have htr := hasDerivAt_reTrace_mul_left ρ hchain
  convert htr using 1
  have h0 : ((1 : ℝ) - 1) / 1 = 0 := by norm_num
  rw [h0, show CFC.rpow σ 0 = 1 from CFC.rpow_zero σ hσnn, one_mul]
  rw [show ((-1 : ℝ) • CFC.log σ) = -(CFC.log σ) from by simp]
  rw [mul_neg]
  change -(Tr ((ρ * CFC.log σ : B ℋ) : L ℋ)).re =
      (Tr ((-(ρ * CFC.log σ) : B ℋ) : L ℋ)).re
  rw [alphaOne_trace_neg, Complex.neg_re]

omit [Nontrivial ℋ] in
/-- **Cyclicity** identifying `Tr(ρ σ^{(1−α)/α})` with the trace of the inner operator
    `K(α) = σ^{(1−α)/(2α)} ρ σ^{(1−α)/(2α)}` of `sandwichedQuasi`. -/
lemma trace_conj_eq_trace_mul_rpow {ρ σ : B ℋ}
    (hσ : σ ∈ pdSet (ℋ := ℋ)) (α : ℝ) :
    Tr ((ρ * CFC.rpow σ ((1 - α) / α) : B ℋ) : L ℋ) =
      Tr ((CFC.rpow σ ((1 - α) / (2 * α)) * ρ *
          CFC.rpow σ ((1 - α) / (2 * α)) : B ℋ) : L ℋ) := by
  set c := (1 - α) / (2 * α) with hc
  have hσu : IsUnit σ := (GeneralizedPerspectiveFunction.isStrictlyPositive_of_pdSet hσ).isUnit
  have hsum : (1 - α) / α = c + c := by rw [hc]; ring
  rw [hsum, show CFC.rpow σ (c + c) = CFC.rpow σ c * CFC.rpow σ c from CFC.rpow_add hσu]
  change Tr ((ρ : L ℋ) *
      (((CFC.rpow σ c : B ℋ) : L ℋ) * ((CFC.rpow σ c : B ℋ) : L ℋ))) =
    Tr ((((CFC.rpow σ c : B ℋ) : L ℋ) * (ρ : L ℋ)) *
      ((CFC.rpow σ c : B ℋ) : L ℋ))
  rw [← mul_assoc, LinearMap.trace_mul_comm, ← mul_assoc]

omit [Nontrivial ℋ] in
/-- **Fixed-base FTC building block.** For a strictly positive `K`, `s ↦ Re Tr(K^s)`
    has derivative `Re Tr(K^s · log K)` (cornerstone + `hasDerivAt_reTrace_mul_left`). -/
lemma hasDerivAt_trace_rpow_fixed {K : B ℋ} (hK : IsStrictlyPositive K) (s₀ : ℝ) :
    HasDerivAt (fun s =>
      (Tr ((CFC.rpow K s : B ℋ) : L ℋ)).re)
      ((Tr ((CFC.rpow K s₀ * CFC.log K : B ℋ) : L ℋ)).re) s₀ := by
  have hd := CFC.hasDerivAt_rpow_exponent hK s₀
  simpa using hasDerivAt_reTrace_mul_left (1 : B ℋ) hd

/-- **Averaging lemma** (general real analysis): if `g` is jointly continuous at `(a, a)`
    with value `L` and each `g α` is interval-integrable on `[a, α]`, then the average
    `(α − a)⁻¹ ∫_a^α g α s ds` tends to `L` as `α → a`. -/
lemma tendsto_average_of_continuousAt {g : ℝ → ℝ → ℝ} {a L : ℝ}
    (hcont : Filter.Tendsto (fun p : ℝ × ℝ => g p.1 p.2) (𝓝 (a, a)) (𝓝 L))
    (hint : ∀ α : ℝ, IntervalIntegrable (g α) volume a α) :
    Filter.Tendsto (fun α => (α - a)⁻¹ * ∫ s in a..α, g α s) (𝓝[≠] a) (𝓝 L) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  rw [Metric.tendsto_nhds_nhds] at hcont
  obtain ⟨δ, hδ, hball⟩ := hcont (ε / 2) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro α hα hdist
  have hαa : α - a ≠ 0 := sub_ne_zero.mpr hα
  have hsplit : ∫ s in a..α, g α s
      = (∫ s in a..α, (g α s - L)) + (α - a) * L := by
    rw [intervalIntegral.integral_sub (hint α) (intervalIntegral.intervalIntegrable_const),
        intervalIntegral.integral_const, smul_eq_mul]; ring
  have hbound : ∀ s ∈ Set.uIoc a α, ‖g α s - L‖ ≤ ε / 2 := by
    intro s hs
    have hs_dist : |s - a| ≤ |α - a| := by
      rcases Set.mem_uIoc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith)]; linarith
    have hp_dist : dist (α, s) (a, a) < δ := by
      rw [Prod.dist_eq]; simp only [max_lt_iff, Real.dist_eq]
      exact ⟨hdist, lt_of_le_of_lt hs_dist (by rwa [Real.dist_eq] at hdist)⟩
    have hb := hball hp_dist
    rw [Real.dist_eq] at hb
    exact le_of_lt hb
  have hint_bound : ‖∫ s in a..α, (g α s - L)‖ ≤ (ε / 2) * |α - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hval : (α - a)⁻¹ * (∫ s in a..α, g α s) - L
      = (α - a)⁻¹ * (∫ s in a..α, (g α s - L)) := by
    rw [hsplit]; field_simp; ring
  rw [Real.dist_eq, hval, abs_mul, abs_inv]
  have hpos : (0 : ℝ) < |α - a| := abs_pos.mpr hαa
  calc |α - a|⁻¹ * |∫ s in a..α, (g α s - L)|
      ≤ |α - a|⁻¹ * ((ε / 2) * |α - a|) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rwa [← Real.norm_eq_abs]
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

omit [Nontrivial ℋ] in
/-- **FTC step.** For a strictly positive `K`, `Re Tr(K^α − K^1)` is the integral of
    `s ↦ Re Tr(K^s · log K)` over `[1, α]` (operator FTC + pushing `Re ∘ Tr` through). -/
lemma trace_rpow_sub_eq_integral {K : B ℋ} (hK : IsStrictlyPositive K) (α : ℝ) :
    (Tr ((CFC.rpow K α - CFC.rpow K 1 : B ℋ) : L ℋ)).re =
      ∫ s in (1:ℝ)..α,
        (Tr ((CFC.rpow K s * CFC.log K : B ℋ) : L ℋ)).re := by
  have hcont : Continuous (fun s : ℝ => CFC.rpow K s * CFC.log K) :=
    (CFC.continuous_rpow_exponent hK).mul continuous_const
  have hop : (∫ s in (1:ℝ)..α, CFC.rpow K s * CFC.log K)
      = CFC.rpow K α - CFC.rpow K 1 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro s _; exact CFC.hasDerivAt_rpow_exponent hK s
    · exact hcont.intervalIntegrable _ _
  rw [← hop]
  have hii : IntervalIntegrable (fun s : ℝ => CFC.rpow K s * CFC.log K) volume 1 α :=
    hcont.intervalIntegrable 1 α
  have hcomm := (reTraceMulLeft (1 : B ℋ)).toContinuousLinearMap.intervalIntegral_comp_comm hii
  have key : ∀ X : B ℋ,
      (reTraceMulLeft (1 : B ℋ)).toContinuousLinearMap X =
        (Tr (X : L ℋ)).re := by
    intro X; simp [reTraceMulLeft]
  calc (Tr (((∫ s in (1:ℝ)..α, CFC.rpow K s * CFC.log K) : B ℋ) : L ℋ)).re
      = (reTraceMulLeft (1 : B ℋ)).toContinuousLinearMap
          (∫ s in (1:ℝ)..α, CFC.rpow K s * CFC.log K) := (key _).symm
    _ = ∫ s in (1:ℝ)..α,
          (reTraceMulLeft (1 : B ℋ)).toContinuousLinearMap
            (CFC.rpow K s * CFC.log K) := hcomm.symm
    _ = ∫ s in (1:ℝ)..α,
        (Tr ((CFC.rpow K s * CFC.log K : B ℋ) : L ℋ)).re := by simp_rw [key]

omit [Nontrivial ℋ] in
/-- **Joint continuity** at `(1, 1)` of the FTC integrand
    `(α, s) ↦ Re Tr(K(α)^s · log K(α))`, `K(α) = σ^{(1−α)/(2α)} ρ σ^{(1−α)/(2α)}`.
    Proved via the exponential representation `K(α)^s = exp(s • log K(α))`
    (`CFC.rpow_eq_normedSpace_exp_smul_log`): this turns the cfc joint continuity into
    `(continuity of s • log K(α))` composed with the global continuity of `exp`,
    using `CFC.continuousOn_log` for the (element) continuity of `log K(α)`. -/
lemma continuousAt_quasiIntegrand {ρ σ : B ℋ}
    (hρ : ρ ∈ pdSet (ℋ := ℋ)) (hσ : σ ∈ pdSet (ℋ := ℋ)) :
    ContinuousAt (fun p : ℝ × ℝ =>
      (Tr ((CFC.rpow (CFC.rpow σ ((1 - p.1) / (2 * p.1)) * ρ
                * CFC.rpow σ ((1 - p.1) / (2 * p.1))) p.2
            * CFC.log (CFC.rpow σ ((1 - p.1) / (2 * p.1)) * ρ
                * CFC.rpow σ ((1 - p.1) / (2 * p.1))) : B ℋ) : L ℋ)).re)
      (1, 1) := by
  set K : ℝ → B ℋ := fun α =>
    CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α)) with hKdef
  have hKpd : ∀ α, K α ∈ pdSet (ℋ := ℋ) := by
    intro α
    rw [hKdef]
    have hPsp : IsStrictlyPositive (CFC.rpow σ ((1 - α) / (2 * α))) :=
      (GeneralizedPerspectiveFunction.isStrictlyPositive_of_pdSet hσ).rpow
    apply (pdSet_membership_certificate _).2
    change IsStrictlyPositive (CFC.rpow σ ((1 - α) / (2 * α)) * ρ *
      CFC.rpow σ ((1 - α) / (2 * α)))
    exact ⟨conjugate_nonneg_of_nonneg
        (GeneralizedPerspectiveFunction.isStrictlyPositive_of_pdSet hρ).nonneg
        CFC.rpow_nonneg,
      ((hPsp.isUnit.mul (GeneralizedPerspectiveFunction.isStrictlyPositive_of_pdSet hρ).isUnit).mul
        hPsp.isUnit)⟩
  have hKsp : ∀ α, IsStrictlyPositive (K α) := fun α =>
    GeneralizedPerspectiveFunction.isStrictlyPositive_of_pdSet (hKpd α)
  have hc : ContinuousAt (fun α : ℝ => (1 - α) / (2 * α)) 1 := by
    apply ContinuousAt.div <;> [fun_prop; fun_prop; norm_num]
  have hrpow : ContinuousAt (fun α : ℝ => CFC.rpow σ ((1 - α) / (2 * α))) 1 :=
    (CFC.continuous_rpow_exponent
      (GeneralizedPerspectiveFunction.isStrictlyPositive_of_pdSet hσ)).continuousAt.comp hc
  have hK : ContinuousAt K 1 := (hrpow.mul continuousAt_const).mul hrpow
  have hmemS : ∀ α, K α ∈ {a : B ℋ | IsSelfAdjoint a ∧ IsUnit a} := fun α =>
    ⟨(hKsp α).1.isSelfAdjoint, (hKsp α).2⟩
  have hlogK : ContinuousAt (fun α => CFC.log (K α)) 1 := by
    have htend : Filter.Tendsto K (𝓝 1)
        (𝓝[{a : B ℋ | IsSelfAdjoint a ∧ IsUnit a}] (K 1)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hK
        (Filter.Eventually.of_forall hmemS)
    exact (CFC.continuousOn_log (K 1) (hmemS 1)).tendsto.comp htend
  have hfeq : (fun p : ℝ × ℝ =>
      (Tr ((CFC.rpow (K p.1) p.2 * CFC.log (K p.1) : B ℋ) : L ℋ)).re)
      = (fun p : ℝ × ℝ =>
          (Tr ((NormedSpace.exp (p.2 • CFC.log (K p.1)) *
            CFC.log (K p.1) : B ℋ) : L ℋ)).re) := by
    funext p; rw [CFC.rpow_eq_normedSpace_exp_smul_log (hKsp p.1)]
  change ContinuousAt (fun p : ℝ × ℝ =>
    (Tr ((CFC.rpow (K p.1) p.2 * CFC.log (K p.1) : B ℋ) : L ℋ)).re) (1, 1)
  rw [hfeq]
  have h1 : ContinuousAt (fun p : ℝ × ℝ => CFC.log (K p.1)) (1, 1) :=
    ContinuousAt.comp (g := fun α => CFC.log (K α)) (f := Prod.fst)
      (x := ((1 : ℝ), (1 : ℝ))) hlogK continuousAt_fst
  exact QuantumState.continuous_re_trace.continuousAt.comp
    ((QuantumState.continuous_normedSpace_exp.continuousAt.comp
      (continuousAt_snd.smul h1)).mul h1)

omit [Nontrivial ℋ] in
/-- **Part A** (proven): the outer-power contribution
    `α ↦ Re Tr(K(α)^α) − Re Tr(K(α))` (with `K(α) = σ^{(1−α)/(2α)} ρ
      σ^{(1−α)/(2α)}`,
    whose trace equals `Re Tr(ρ σ^{(1−α)/α})` by cyclicity) has derivative
    `Re Tr(ρ log ρ)` at `α = 1`.

    Fixed-base FTC + averaging (no Duhamel): `Re Tr(K(α)^α) − Re Tr(K(α))` is the
    integral of `g(α, s) := Re Tr(K(α)^s log K(α))` over `[1, α]`
    (`trace_rpow_sub_eq_integral`), so the difference quotient is the average of `g`,
    which tends to `g(1, 1) = Re Tr(ρ log ρ)` by `tendsto_average_of_continuousAt`
    and the joint continuity `continuousAt_quasiIntegrand`. -/
lemma hasDerivAt_partA {ρ σ : B ℋ}
    (hρ : ρ ∈ pdSet (ℋ := ℋ)) (hσ : σ ∈ pdSet (ℋ := ℋ)) :
    HasDerivAt (fun α =>
        (sandwichedQuasi α (ρ : L ℋ) (σ : L ℋ)).re -
        (Tr ((ρ * CFC.rpow σ ((1 - α) / α) : B ℋ) : L ℋ)).re)
      ((Tr ((ρ * CFC.log ρ : B ℋ) : L ℋ)).re) 1 := by
  set K : ℝ → B ℋ := fun α =>
    CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α)) with hKdef
  have hKpd : ∀ α, K α ∈ pdSet (ℋ := ℋ) := by
    intro α
    rw [hKdef]
    have hPsp : IsStrictlyPositive (CFC.rpow σ ((1 - α) / (2 * α))) :=
      (GeneralizedPerspectiveFunction.isStrictlyPositive_of_pdSet hσ).rpow
    apply (pdSet_membership_certificate _).2
    change IsStrictlyPositive (CFC.rpow σ ((1 - α) / (2 * α)) * ρ *
      CFC.rpow σ ((1 - α) / (2 * α)))
    exact ⟨conjugate_nonneg_of_nonneg
        (GeneralizedPerspectiveFunction.isStrictlyPositive_of_pdSet hρ).nonneg
        CFC.rpow_nonneg,
      ((hPsp.isUnit.mul (GeneralizedPerspectiveFunction.isStrictlyPositive_of_pdSet hρ).isUnit).mul
        hPsp.isUnit)⟩
  have hKsp : ∀ α, IsStrictlyPositive (K α) := fun α =>
    GeneralizedPerspectiveFunction.isStrictlyPositive_of_pdSet (hKpd α)
  set g : ℝ → ℝ → ℝ := fun α s =>
    (Tr ((CFC.rpow (K α) s * CFC.log (K α) : B ℋ) : L ℋ)).re with hgdef
  have hK1 : K 1 = ρ := by
    have hP1 : CFC.rpow σ ((1 - (1:ℝ)) / (2 * 1)) = 1 := by
      rw [show ((1 - (1:ℝ)) / (2 * 1)) = 0 by norm_num]
      exact CFC.rpow_zero σ (GeneralizedPerspectiveFunction.isStrictlyPositive_of_pdSet hσ).nonneg
    rw [hKdef]
    change CFC.rpow σ ((1 - (1:ℝ)) / (2 * 1)) * ρ * CFC.rpow σ ((1 - (1:ℝ)) / (2 * 1)) = ρ
    rw [hP1, one_mul, mul_one]
  have hg11 : g 1 1 =
      (Tr ((ρ * CFC.log ρ : B ℋ) : L ℋ)).re := by
    simp only [hgdef, hK1]
    rw [show CFC.rpow ρ 1 = ρ from
      CFC.rpow_one ρ (GeneralizedPerspectiveFunction.isStrictlyPositive_of_pdSet hρ).nonneg]
  -- joint continuity of g at (1,1)
  have hjoint : ContinuousAt (fun p : ℝ × ℝ => g p.1 p.2) (1, 1) := by
    have := continuousAt_quasiIntegrand hρ hσ
    rwa [hgdef]
  -- integrability of g α
  have hint : ∀ α : ℝ, IntervalIntegrable (g α) volume 1 α := by
    intro α
    apply Continuous.intervalIntegrable
    rw [hgdef]
    exact QuantumState.continuous_re_trace.comp
      ((CFC.continuous_rpow_exponent (hKsp α)).mul continuous_const)
  -- averaging: the difference quotient tends to g 1 1
  have havg := tendsto_average_of_continuousAt hjoint hint
  -- HasDerivAt of the integral form
  have hF : HasDerivAt (fun α => ∫ s in (1:ℝ)..α, g α s) (g 1 1) 1 := by
    rw [hasDerivAt_iff_tendsto_slope]
    have hslope : slope (fun α => ∫ s in (1:ℝ)..α, g α s) 1
        = fun α => (α - 1)⁻¹ * ∫ s in (1:ℝ)..α, g α s := by
      funext α
      rw [slope_def_field, intervalIntegral.integral_same, sub_zero, div_eq_inv_mul]
    rw [hslope]; exact havg
  -- the Part A function equals the integral form
  have hfunc : (fun α =>
      (sandwichedQuasi α (ρ : L ℋ) (σ : L ℋ)).re -
      (Tr ((ρ * CFC.rpow σ ((1 - α) / α) : B ℋ) : L ℋ)).re)
      = (fun α => ∫ s in (1:ℝ)..α, g α s) := by
    funext α
    have hsq : (sandwichedQuasi α (ρ : L ℋ) (σ : L ℋ)).re =
        (Tr ((CFC.rpow (K α) α : B ℋ) : L ℋ)).re := by
      rw [alphaOne_sandwichedQuasi_eq_clm_direct]
    have hcyc : (Tr ((ρ * CFC.rpow σ ((1 - α) / α) : B ℋ) : L ℋ)).re =
        (Tr ((CFC.rpow (K α) 1 : B ℋ) : L ℋ)).re := by
      rw [trace_conj_eq_trace_mul_rpow hσ α,
        show CFC.rpow (K α) 1 = K α from CFC.rpow_one (K α) (hKsp α).nonneg, hKdef]
    rw [hsq, hcyc, ← Complex.sub_re]
    have htrace := trace_rpow_sub_eq_integral (hKsp α) α
    rw [show Tr ((CFC.rpow (K α) α : B ℋ) : L ℋ) -
        Tr ((CFC.rpow (K α) 1 : B ℋ) : L ℋ) =
        Tr ((CFC.rpow (K α) α - CFC.rpow (K α) 1 : B ℋ) : L ℋ) by
          exact (alphaOne_trace_sub _ _).symm,
      htrace, hgdef]
  rw [hfunc, ← hg11]
  exact hF

omit [Nontrivial ℋ] in
/-- The derivative at `α = 1` of the real quasi-entropy
    `α ↦ Re Tr((σ^{(1−α)/(2α)} ρ σ^{(1−α)/(2α)})^α)` is `Re Tr(ρ (log ρ −
      log σ))`.

    Assembled from Part A (`hasDerivAt_partA`) and Part B (`hasDerivAt_partB`):
    the quasi-entropy splits as `(Q − Tr K) + Tr K`, whose derivatives are
    `Re Tr(ρ log ρ)` and `−Re Tr(ρ log σ)`. -/
lemma hasDerivAt_sandwichedQuasi_re_one
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    HasDerivAt (fun α => (sandwichedQuasi α ρ σ).re)
      (Tr (((ρ.toContinuousLinearMap *
        (CFC.log ρ.toContinuousLinearMap - CFC.log σ.toContinuousLinearMap) : B ℋ) : L
          ℋ))).re 1
          := by
  let ρc : B ℋ := ρ.toContinuousLinearMap
  let σc : B ℋ := σ.toContinuousLinearMap
  change HasDerivAt (fun α => (sandwichedQuasi α (ρc : L ℋ) (σc : L ℋ)).re)
    ((Tr ((ρc * (CFC.log ρc - CFC.log σc) : B ℋ) : L ℋ)).re) 1
  have hB := hasDerivAt_partB (ρ := ρc)
    (show σc ∈ pdSet (ℋ := ℋ) from hσ)
  have hA := hasDerivAt_partA
    (show ρc ∈ pdSet (ℋ := ℋ) from hρ)
    (show σc ∈ pdSet (ℋ := ℋ) from hσ)
  have hsum := hA.add hB
  change HasDerivAt
    ((fun α =>
      (sandwichedQuasi α (ρc : L ℋ) (σc : L ℋ)).re -
      (Tr ((ρc * CFC.rpow σc ((1 - α) / α) : B ℋ) : L ℋ)).re) +
    (fun α => (Tr ((ρc * CFC.rpow σc ((1 - α) / α) : B ℋ) : L ℋ)).re))
    ((Tr ((ρc * CFC.log ρc : B ℋ) : L ℋ)).re +
      -(Tr ((ρc * CFC.log σc : B ℋ) : L ℋ)).re) 1 at hsum
  have heq : (fun α =>
      (sandwichedQuasi α (ρc : L ℋ) (σc : L ℋ)).re)
      = (fun α =>
          (sandwichedQuasi α (ρc : L ℋ) (σc : L ℋ)).re -
          (Tr ((ρc * CFC.rpow σc ((1 - α) / α) : B ℋ) : L ℋ)).re) +
        (fun α => (Tr ((ρc * CFC.rpow σc ((1 - α) / α) : B ℋ) : L ℋ)).re) := by
    funext α
    simp only [Pi.add_apply]
    ring
  rw [heq]
  convert hsum using 1
  rw [mul_sub, alphaOne_trace_sub, Complex.sub_re]
  ring

private lemma sandwichedRenyiDiv_tendsto_umegaki_clm
    {ρ σ : B ℋ} (hρ : ρ ∈ pdSet (ℋ := ℋ)) (hσ : σ ∈ pdSet (ℋ := ℋ)) :
    Filter.Tendsto (fun α => sandwichedRenyiDiv α (ρ : L ℋ) (σ : L ℋ))
      (𝓝[>] (1 : ℝ)) (𝓝 (umegakiNorm (ρ : L ℋ) (σ : L ℋ))) := by
  have hρ_nn := (GeneralizedPerspectiveFunction.isStrictlyPositive_of_pdSet hρ).nonneg
  have hσ_nn := (GeneralizedPerspectiveFunction.isStrictlyPositive_of_pdSet hσ).nonneg
  have hρ0 : ρ ≠ 0 := (GeneralizedPerspectiveFunction.isStrictlyPositive_of_pdSet hρ).isUnit.ne_zero
  have hTrρ_pos : 0 < (Tr (ρ : L ℋ)).re :=
    trace_re_pos_of_ne_zero_clm hρ_nn hρ0
  have hQ1 : (sandwichedQuasi 1 (ρ : L ℋ) (σ : L ℋ)).re =
      (Tr (ρ : L ℋ)).re :=
    sandwichedQuasi_one_re ρ σ hσ_nn hρ_nn
  have hQ1_ne : (sandwichedQuasi 1 (ρ : L ℋ) (σ : L ℋ)).re ≠ 0 := by
    rw [hQ1]
    exact ne_of_gt hTrρ_pos
  have hderiv_logf : HasDerivAt (fun α => Real.log ((sandwichedQuasi α
      (ρ : L ℋ) (σ : L ℋ)).re))
      (umegakiNorm (ρ : L ℋ) (σ : L ℋ)) 1 := by
    convert (hasDerivAt_sandwichedQuasi_re_one
      (show (ρ : L ℋ) ∈ pdSetLM (ℋ := ℋ) from by simpa [pdSetLM] using hρ)
      (show (σ : L ℋ) ∈ pdSetLM (ℋ := ℋ) from by simpa [pdSetLM] using hσ)).log
        hQ1_ne using 1
    rw [hQ1, umegakiNorm_eq_toContinuousLinearMap]
  have h_slope := (hasDerivAt_iff_tendsto_slope.mp hderiv_logf).mono_left <|
    nhdsWithin_mono _ fun _ hx => ne_of_gt hx
  refine h_slope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with α hα
  have hα1 : (1 : ℝ) < α := hα
  have hα0 : (0 : ℝ) < α := by linarith
  have hfα_ne : (sandwichedQuasi α (ρ : L ℋ) (σ : L ℋ)).re ≠ 0 :=
    sandwichedQuasi_re_ne_zero_of_pdSetLM hα0 hρ hσ
  change slope (fun α => Real.log ((sandwichedQuasi α
    (ρ : L ℋ) (σ : L ℋ)).re)) 1 α =
      sandwichedRenyiDiv α (ρ : L ℋ) (σ : L ℋ)
  rw [slope_def_field]
  unfold sandwichedRenyiDiv
  rw [hQ1, Real.log_div hfα_ne (ne_of_gt hTrρ_pos), one_div]
  ring

/-- **The `α → 1⁺` limit of the sandwiched Rényi divergence is the normalized
    Umegaki relative entropy**, for positive-definite `ρ, σ`.

    The limit is `umegakiNorm ρ σ = Tr(ρ(log ρ − log σ)).re / (Tr ρ).re`.

    Fully proven as a difference-quotient limit: with `Q(α) := (Q_α ρ σ).re` and
    `Q(1) = (Tr ρ).re`, one has
    `D_α(ρ‖σ) = (log Q(α) − log Q(1)) / (α − 1) = slope (log ∘ Q) 1 α`, and this
    slope tends to `(log ∘ Q)'(1) = umegakiNorm ρ σ` (by `hasDerivAt_iff_tendsto_slope`,
    restricted to `𝓝[>] 1`). The single derivative input is
    `hasDerivAt_sandwichedQuasi_re_one`. -/
lemma sandwichedRenyiDiv_tendsto_umegaki
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    Filter.Tendsto (fun α => sandwichedRenyiDiv α ρ σ) (𝓝[>] (1 : ℝ))
      (𝓝 (umegakiNorm ρ σ)) := by
  let ρc : B ℋ := ρ.toContinuousLinearMap
  let σc : B ℋ := σ.toContinuousLinearMap
  have hlim := sandwichedRenyiDiv_tendsto_umegaki_clm
    (show ρc ∈ pdSet (ℋ := ℋ) from hρ)
    (show σc ∈ pdSet (ℋ := ℋ) from hσ)
  simpa [ρc, σc] using hlim

end Umegaki

end SandwichedRenyiRelativeEntropy
