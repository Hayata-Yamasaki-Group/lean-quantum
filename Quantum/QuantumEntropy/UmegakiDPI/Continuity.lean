/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.CFCDeriv
import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneDefinitions
import Quantum.QuantumEntropy.Common.FaithfulApproximation
import Quantum.QuantumEntropy.Common.TraceNonnegativeLinear

/-!
# Umegaki continuity and faithful-approximation reduction

Singular-boundary continuity for `umegakiNorm` and the faithful-approximation
reduction from positive-definite to non-negative data processing.

The analytic helper declarations imported from the sandwiched-Renyi tree are
independent of finite `alpha`: they concern only faithful channel approximation,
support preservation, trace positivity, and finite-dimensional CFC eigenvectors.
-/
namespace UmegakiDPI

open GeneralizedPerspectiveFunction QuantumState QuantumChannel MeasureTheory
open SandwichedRenyiRelativeEntropy
open scoped ComplexOrder Topology

universe u

section Umegaki

/-- A trace-preserving channel cannot annihilate a nonzero nonnegative input. -/
private lemma continuity_cptp_toFun_ne_zero
    {H K : Type u} [Qudit H] [Nontrivial H] [Qudit K] [Nontrivial K]
    (Φ : CPTP H K) {rho : L H} (hrho : 0 ≤ rho) (hrho0 : rho ≠ 0) :
    Φ.toFun rho ≠ 0 := by
  intro hzero
  have htrace := Φ.trace_map rho
  have htr : (Tr rho).re = 0 := by
    rw [htrace, hzero]
    simp
  exact absurd htr (ne_of_gt (by
    simpa using QuantumEntropy.trace_re_pos_of_ne_zero hrho hrho0))

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

omit [Nontrivial ℋ] in
private lemma reduction_trace_sub (A B : ℋ →L[ℂ] ℋ) :
    Tr ((A - B : ℋ →L[ℂ] ℋ) : L ℋ) =
      Tr (A : L ℋ) -
        Tr (B : L ℋ) := by
  change traceCLM (A - B) = traceCLM A - traceCLM B
  exact map_sub traceCLM A B

omit [Nontrivial ℋ] in
private lemma reduction_toCLM_toLinearMap (f : B ℋ) :
    (f : L ℋ).toContinuousLinearMap = f := by
  ext x
  rfl

/-! ### Singular-boundary continuity for Umegaki norm -/
/-- Boundary continuity of the cross term `Re Tr((ρ+ε)·log(σ+ε)) → Re Tr(ρ·log σ)`
    for nonneg `ρ, σ` with `supp ρ ⊆ supp σ` (finite at singular `σ` since `ρ` kills
    `ker σ`, so the divergent `log ε` on `ker σ` enters only via `ε·log ε → 0`). -/
lemma tendsto_tr_perturb_mul_log_perturb {ρ σ : B ℋ}
    (hσ : 0 ≤ σ)
    (hsupp : SupportLE (ρ : L ℋ) (σ : L ℋ)) :
    Filter.Tendsto (fun ε : ℝ =>
      (Tr (((ρ + (ε : ℂ) • 1) *
        CFC.log (σ + (ε : ℂ) • 1) : B ℋ) : L ℋ)).re)
      (𝓝[>] (0:ℝ))
      (𝓝 ((Tr ((ρ * CFC.log σ : B ℋ) : L ℋ)).re)) := by
  change Filter.Tendsto (fun ε : ℝ =>
      (Tr (ContinuousLinearMap.toLinearMap
        ((ρ + (ε : ℂ) • 1) * CFC.log (σ + (ε : ℂ) • 1)))).re)
    (𝓝[>] (0 : ℝ))
    (𝓝 ((Tr (ContinuousLinearMap.toLinearMap (ρ * CFC.log σ))).re))
  classical
  have hσ_sa : IsSelfAdjoint σ := IsSelfAdjoint.of_nonneg hσ
  have hσ_pos : σ.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive σ).mp hσ
  have hσ_sym := hσ_pos.isSymmetric
  change LinearMap.ker σ.toLinearMap ≤ LinearMap.ker ρ.toLinearMap at hsupp
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  set b := hσ_sym.eigenvectorBasis hn with hb
  set eig := hσ_sym.eigenvalues hn with heig
  have h_eig_apply : ∀ i, σ (b i) = ((eig i : ℝ) : ℂ) • b i :=
    hσ_sym.apply_eigenvectorBasis hn
  have hb_ne : ∀ i, b i ≠ 0 := fun i => b.orthonormal.ne_zero i
  have hbb : ∀ i, inner ℂ (b i) (b i) = (1 : ℂ) := fun i => b.inner_eq_one i
  set c : Fin n → ℝ := fun i => (inner ℂ (b i) (ρ (b i))).re with hc_def
  have hc0 : ∀ i, eig i = 0 → c i = 0 := by
    intro i hi
    have hρb : ρ (b i) = 0 := hsupp <| by
      rw [LinearMap.mem_ker]; change σ (b i) = 0; rw [h_eig_apply i, hi]; simp
    simp only [hc_def, hρb, inner_zero_right, Complex.zero_re]
  have hev : ∀ (ε : ℝ) (i),
      (σ + (ε : ℂ) • (1 : B ℋ)) (b i) = ((eig i + ε : ℝ) : ℂ) • b i := by
    intro ε i
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, h_eig_apply i]
    rw [← add_smul]; norm_cast
  have hsa : ∀ (ε : ℝ),
      IsSelfAdjoint (σ + (ε : ℂ) • (1 : B ℋ)) := by
    intro ε
    rw [IsSelfAdjoint, star_add, hσ_sa.star_eq, star_smul, star_one, Complex.star_def,
      Complex.conj_ofReal]
  have hlog_apply : ∀ (ε : ℝ) (i),
      CFC.log (σ + (ε : ℂ) • 1) (b i) = ((Real.log (eig i + ε) : ℝ) : ℂ) • b i := by
    intro ε i
    exact TensorCFC.cfc_real_apply_eigenvector (hsa ε) Real.log (hev ε i)
      (TensorCFC.mem_spectrum_real_of_eigenvector (hb_ne i) (hev ε i))
  have hinner : ∀ (ε : ℝ) (i),
      (inner ℂ (b i) ((ρ + (ε : ℂ) • 1) (b i))).re = c i + ε := by
    intro ε i
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, inner_add_right, inner_smul_right, hbb i, mul_one,
      Complex.add_re, hc_def, Complex.ofReal_re]
  have hexpand : ∀ ε : ℝ,
      (Tr (ContinuousLinearMap.toLinearMap
        ((ρ + (ε : ℂ) • 1) * CFC.log (σ + (ε : ℂ) • 1)))).re =
        ∑ i, Real.log (eig i + ε) * (c i + ε) := by
    intro ε
    change (Tr (((ρ + (ε : ℂ) • 1) *
      CFC.log (σ + (ε : ℂ) • 1)).toLinearMap)).re = _
    rw [LinearMap.trace_eq_sum_inner
      (T := ((ρ + (ε : ℂ) • 1) * CFC.log (σ + (ε : ℂ) • 1)).toLinearMap) b,
      Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (inner ℂ (b i)
      (((ρ + (ε : ℂ) • 1) * CFC.log (σ + (ε : ℂ) • 1)) (b i))).re = _
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, hlog_apply ε i,
      map_smul, inner_smul_right, Complex.re_ofReal_mul, hinner ε i]
  have hlimval :
      (Tr (ContinuousLinearMap.toLinearMap (ρ * CFC.log σ))).re =
        ∑ i, Real.log (eig i) * c i := by
    simpa only [Complex.ofReal_zero, zero_smul, add_zero] using hexpand 0
  rw [hlimval, show (fun ε : ℝ =>
      (Tr (ContinuousLinearMap.toLinearMap
        ((ρ + (ε : ℂ) • 1) * CFC.log (σ + (ε : ℂ) • 1)))).re) =
        (fun ε => ∑ i, Real.log (eig i + ε) * (c i + ε)) from funext hexpand]
  apply tendsto_finset_sum
  intro i _
  have haddci : Filter.Tendsto (fun ε : ℝ => c i + ε) (𝓝[>] (0:ℝ)) (𝓝 (c i)) := by
    have : Filter.Tendsto (fun ε : ℝ => c i + ε) (𝓝 (0:ℝ)) (𝓝 (c i + 0)) :=
      (continuous_const.add continuous_id).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  by_cases hi : eig i = 0
  · rw [hi, hc0 i hi]
    simp only [Real.log_zero, mul_zero, zero_add]
    have hnml : Filter.Tendsto (fun ε : ℝ => Real.log ε * ε) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa [Real.negMulLog, mul_comm] using
        (Real.continuous_negMulLog.tendsto 0).neg.mono_left nhdsWithin_le_nhds
    exact hnml
  · have heig_pos : 0 < eig i :=
      lt_of_le_of_ne (hσ_pos.toLinearMap.nonneg_eigenvalues hn i) (Ne.symm hi)
    have hlog : Filter.Tendsto (fun ε : ℝ => Real.log (eig i + ε)) (𝓝[>] (0:ℝ))
        (𝓝 (Real.log (eig i))) := by
      simpa using ((Real.continuousAt_log (by simpa using ne_of_gt heig_pos)).comp
        ((continuous_const.add continuous_id).tendsto 0)).mono_left nhdsWithin_le_nhds
    exact hlog.mul haddci

omit [Nontrivial ℋ] in
/-- `Re Tr(ρ + ε•1) → Re Tr ρ` as `ε → 0⁺`. -/
lemma tendsto_tr_perturb {ρ : B ℋ} :
    Filter.Tendsto (fun ε : ℝ =>
      (Tr ((ρ + (ε : ℂ) • 1 : B ℋ) : L ℋ)).re) (𝓝[>] (0:ℝ))
      (𝓝 (Tr (ρ : L ℋ)).re) := by
  change Filter.Tendsto (fun ε : ℝ =>
      (Tr (ContinuousLinearMap.toLinearMap
        (ρ + (ε : ℂ) • 1))).re) (𝓝[>] (0 : ℝ))
    (𝓝 (Tr (ContinuousLinearMap.toLinearMap ρ)).re)
  have key : (Tr (ContinuousLinearMap.toLinearMap ρ)).re =
      (Tr (ContinuousLinearMap.toLinearMap
        (ρ + ((0 : ℝ) : ℂ) • (1 : B ℋ)))).re := by simp
  rw [key]
  exact ((QuantumState.continuous_re_trace.comp
    (by fun_prop : Continuous fun ε : ℝ =>
      ρ + (ε : ℂ) • (1 : B ℋ))).tendsto 0).mono_left
    nhdsWithin_le_nhds

/-- **Boundary continuity (H1)**: `umegakiNorm (ρ+ε) (σ+ε) → umegakiNorm ρ σ` as `ε
  → 0⁺`,
    for nonneg `ρ ≠ 0`, `σ` with `supp ρ ⊆ supp σ`. Assembles the cross-term continuity
    (numerator) with trace continuity (denominator) via `Tendsto.div`. -/
private lemma tendsto_umegakiNorm_perturb_clm {ρ σ : B ℋ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0)
    (hsupp : SupportLE (ρ : L ℋ) (σ : L ℋ)) :
    Filter.Tendsto (fun ε : ℝ => umegakiNorm
      ((ρ + (ε : ℂ) • 1 : B ℋ) : L ℋ) ((σ + (ε : ℂ) • 1 : B ℋ) : L ℋ))
      (𝓝[>] (0:ℝ)) (𝓝 (umegakiNorm (ρ : L ℋ) (σ : L ℋ))) := by
  have hcrossρ := tendsto_tr_perturb_mul_log_perturb (ρ := ρ) (σ := ρ) hρ (le_refl _)
  have hcrossσ := tendsto_tr_perturb_mul_log_perturb (ρ := ρ) (σ := σ) hσ hsupp
  have hnum : Filter.Tendsto
      (fun ε : ℝ => (Tr (ContinuousLinearMap.toLinearMap
        ((ρ + (ε : ℂ) • 1) *
          (CFC.log (ρ + (ε : ℂ) • 1) - CFC.log (σ + (ε : ℂ) • 1))))).re)
      (𝓝[>] (0:ℝ)) (𝓝 ((Tr (ContinuousLinearMap.toLinearMap
        (ρ * (CFC.log ρ - CFC.log σ)))).re)) := by
    have heqf : (fun ε : ℝ => (Tr (ContinuousLinearMap.toLinearMap
        ((ρ + (ε : ℂ) • 1) *
          (CFC.log (ρ + (ε : ℂ) • 1) - CFC.log (σ + (ε : ℂ) • 1))))).re) =
        (fun ε : ℝ =>
          (Tr (ContinuousLinearMap.toLinearMap
            ((ρ + (ε : ℂ) • 1) * CFC.log (ρ + (ε : ℂ) • 1)))).re -
          (Tr (ContinuousLinearMap.toLinearMap
            ((ρ + (ε : ℂ) • 1) * CFC.log (σ + (ε : ℂ) • 1)))).re) := by
      funext ε
      simp only [mul_sub, reduction_trace_sub, Complex.sub_re]
    rw [heqf, show (Tr (ContinuousLinearMap.toLinearMap
          (ρ * (CFC.log ρ - CFC.log σ)))).re =
          (Tr (ContinuousLinearMap.toLinearMap (ρ * CFC.log ρ))).re -
            (Tr (ContinuousLinearMap.toLinearMap (ρ * CFC.log σ))).re from by
        simp only [mul_sub, reduction_trace_sub, Complex.sub_re]]
    exact hcrossρ.sub hcrossσ
  have hden0 : (Tr (ContinuousLinearMap.toLinearMap ρ)).re ≠ 0 :=
    ne_of_gt (QuantumEntropy.trace_re_pos_of_ne_zero
      ((ContinuousLinearMap.coe_le_coe_iff _ _).mpr hρ)
      (fun h => hρ0 (by ext x; exact congrArg (fun A : L _ => A x) h)))
  have hres := hnum.div (tendsto_tr_perturb (ρ := ρ)) hden0
  simpa only [umegakiNorm_eq_toContinuousLinearMap, reduction_toCLM_toLinearMap] using hres

lemma tendsto_umegakiNorm_perturb {ρ σ : L ℋ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0)
    (hsupp : SupportLE ρ σ) :
    Filter.Tendsto (fun ε : ℝ => umegakiNorm (ρ + (ε : ℂ) • 1) (σ + (ε : ℂ) • 1))
      (𝓝[>] (0:ℝ)) (𝓝 (umegakiNorm ρ σ)) := by
  let ρc : B ℋ := ρ.toContinuousLinearMap
  let σc : B ℋ := σ.toContinuousLinearMap
  have hρc : 0 ≤ ρc := (ContinuousLinearMap.coe_le_coe_iff 0 ρc).mp hρ
  have hσc : 0 ≤ σc := (ContinuousLinearMap.coe_le_coe_iff 0 σc).mp hσ
  have hρc0 : ρc ≠ 0 := by
    intro h
    apply hρ0
    exact LinearMap.toContinuousLinearMap.injective h
  have hlim := tendsto_umegakiNorm_perturb_clm hρc hσc hρc0 hsupp
  simpa [ρc, σc] using hlim

/-! ### Faithful-approximation reduction to non-negative Umegaki DPI -/
/-- **Continuity of `umegakiNorm` along a path into the strictly-positive operators**
    (no singularity): if `a ε → a₀`, `b ε → b₀` with `a ε, b ε` eventually
    self-adjoint units and `a₀, b₀` self-adjoint units (`Re Tr a₀ ≠ 0`), then
    `umegakiNorm (a ε) (b ε) → umegakiNorm a₀ b₀`. Uses `CFC.continuousOn_log`. -/
private lemma tendsto_umegakiNorm_within_clm {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {a b : ℝ → B 𝒦} {a₀ b₀ : B 𝒦} {l : Filter ℝ}
    (ha : Filter.Tendsto a l (𝓝 a₀)) (hb : Filter.Tendsto b l (𝓝 b₀))
    (ha_mem : ∀ᶠ ε in l, IsSelfAdjoint (a ε) ∧ IsUnit (a ε))
    (hb_mem : ∀ᶠ ε in l, IsSelfAdjoint (b ε) ∧ IsUnit (b ε))
    (ha0 : IsSelfAdjoint a₀ ∧ IsUnit a₀) (hb0 : IsSelfAdjoint b₀ ∧ IsUnit b₀)
    (hTra0 : (Tr (a₀ : L 𝒦)).re ≠ 0) :
    Filter.Tendsto (fun ε => umegakiNorm (a ε : L 𝒦) (b ε : L 𝒦)) l
      (𝓝 (umegakiNorm (a₀ : L 𝒦) (b₀ : L 𝒦))) := by
  have hloga : Filter.Tendsto (fun ε => CFC.log (a ε)) l (𝓝 (CFC.log a₀)) :=
    (CFC.continuousOn_log a₀ ha0).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ha ha_mem)
  have hlogb : Filter.Tendsto (fun ε => CFC.log (b ε)) l (𝓝 (CFC.log b₀)) :=
    (CFC.continuousOn_log b₀ hb0).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hb hb_mem)
  have hnum : Filter.Tendsto (fun ε =>
      (Tr (ContinuousLinearMap.toLinearMap
        (a ε * (CFC.log (a ε) - CFC.log (b ε))))).re) l
      (𝓝 ((Tr (ContinuousLinearMap.toLinearMap
        (a₀ * (CFC.log a₀ - CFC.log b₀)))).re)) :=
    (QuantumState.continuous_re_trace.tendsto _).comp (ha.mul (hloga.sub hlogb))
  have hden : Filter.Tendsto (fun ε =>
      (Tr (ContinuousLinearMap.toLinearMap (a ε))).re) l
      (𝓝 (Tr (ContinuousLinearMap.toLinearMap a₀)).re) :=
    (QuantumState.continuous_re_trace.tendsto _).comp ha
  simpa only [umegakiNorm_eq_toContinuousLinearMap, reduction_toCLM_toLinearMap] using
    hnum.div hden hTra0

/-- L-endpoint form of continuity of `umegakiNorm` along a path of self-adjoint units. -/
lemma tendsto_umegakiNorm_within {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {a b : ℝ → L 𝒦} {a₀ b₀ : L 𝒦} {l : Filter ℝ}
    (ha : Filter.Tendsto a l (𝓝 a₀)) (hb : Filter.Tendsto b l (𝓝 b₀))
    (ha_mem : ∀ᶠ ε in l, IsSelfAdjoint (a ε) ∧ IsUnit (a ε))
    (hb_mem : ∀ᶠ ε in l, IsSelfAdjoint (b ε) ∧ IsUnit (b ε))
    (ha0 : IsSelfAdjoint a₀ ∧ IsUnit a₀) (hb0 : IsSelfAdjoint b₀ ∧ IsUnit b₀)
    (hTra0 : (Tr a₀).re ≠ 0) :
    Filter.Tendsto (fun ε => umegakiNorm (a ε) (b ε)) l (𝓝 (umegakiNorm a₀ b₀)) := by
  let e : L 𝒦 ≃⋆ₐ[ℂ] B 𝒦 :=
    { LinearMap.toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      map_star' := fun A => by
        simpa using (LinearMap.adjoint_toContinuousLinearMap (A := A)) }
  have he : Continuous e := by fun_prop
  have hsa {A : L 𝒦} (hA : IsSelfAdjoint A) : IsSelfAdjoint (e A) := by
    rw [IsSelfAdjoint] at hA ⊢
    change ContinuousLinearMap.adjoint A.toContinuousLinearMap = A.toContinuousLinearMap
    rw [← LinearMap.adjoint_toContinuousLinearMap]
    exact congrArg LinearMap.toContinuousLinearMap hA
  have hu {A : L 𝒦} (hA : IsUnit A) : IsUnit (e A) := hA.map e
  have ha' : Filter.Tendsto (fun ε => e (a ε)) l (𝓝 (e a₀)) :=
    (he.tendsto a₀).comp ha
  have hb' : Filter.Tendsto (fun ε => e (b ε)) l (𝓝 (e b₀)) :=
    (he.tendsto b₀).comp hb
  have ha_mem' : ∀ᶠ ε in l, IsSelfAdjoint (e (a ε)) ∧ IsUnit (e (a ε)) := by
    filter_upwards [ha_mem] with ε hε
    exact ⟨hsa hε.1, hu hε.2⟩
  have hb_mem' : ∀ᶠ ε in l, IsSelfAdjoint (e (b ε)) ∧ IsUnit (e (b ε)) := by
    filter_upwards [hb_mem] with ε hε
    exact ⟨hsa hε.1, hu hε.2⟩
  have hlim := tendsto_umegakiNorm_within_clm ha' hb' ha_mem' hb_mem'
    ⟨hsa ha0.1, hu ha0.2⟩ ⟨hsa hb0.1, hu hb0.2⟩ hTra0
  simpa [e] using hlim

lemma tendsto_uloglu : Filter.Tendsto (fun u : ℝ => u * Real.log u) (𝓝[>] (0:ℝ)) (𝓝
  0) := by
  have hc0 := (Real.continuous_negMulLog.tendsto 0)
  simp only [Real.negMulLog_zero] at hc0
  have h := hc0.neg
  simp only [neg_zero] at h
  refine (h.mono_left nhdsWithin_le_nhds).congr (fun u => ?_)
  simp [Real.negMulLog]

lemma tendsto_lam_log_lam_mul {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun lam : ℝ => lam * Real.log (lam * c)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hu : Filter.Tendsto (fun lam : ℝ => lam * c) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using ((continuous_mul_const c).tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with lam hlam
      exact mul_pos hlam hc
  have hcomp := (tendsto_uloglu.comp hu).const_mul (c⁻¹)
  simp only [mul_zero] at hcomp
  refine hcomp.congr fun lam => ?_
  simp only [Function.comp_apply]
  field_simp

lemma tendsto_tr_faithful_cross {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    {A B : 𝒦 →L[ℂ] 𝒦} (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hsupp : SupportLE (B : L 𝒦) (A : L 𝒦))
    {cA cB : ℝ} (hcA : 0 < cA) :
    Filter.Tendsto (fun lam : ℝ =>
        (Tr (((((1 - lam : ℝ) : ℂ) • B + ((lam * cB : ℝ) : ℂ) • 1) *
            CFC.log (((1 - lam : ℝ) : ℂ) • A +
              ((lam * cA : ℝ) : ℂ) • 1) : 𝒦 →L[ℂ] 𝒦) : L 𝒦)).re)
      (𝓝[>] (0:ℝ))
      (𝓝 ((Tr ((B * CFC.log A : 𝒦 →L[ℂ] 𝒦) : L 𝒦)).re)) := by
  change Filter.Tendsto (fun lam : ℝ =>
      (Tr (ContinuousLinearMap.toLinearMap
        ((((1 - lam : ℝ) : ℂ) • B + ((lam * cB : ℝ) : ℂ) • 1) *
          CFC.log (((1 - lam : ℝ) : ℂ) • A +
            ((lam * cA : ℝ) : ℂ) • 1)))).re)
    (𝓝[>] (0 : ℝ))
    (𝓝 ((Tr (ContinuousLinearMap.toLinearMap (B * CFC.log A))).re))
  classical
  have hA_sa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  have hA_pos : A.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive A).mp hA
  have hA_sym := hA_pos.isSymmetric
  change LinearMap.ker A.toLinearMap ≤ LinearMap.ker B.toLinearMap at hsupp
  set n := Module.finrank ℂ 𝒦 with hn_def
  have hn : Module.finrank ℂ 𝒦 = n := rfl
  set b := hA_sym.eigenvectorBasis hn with hb
  set eig := hA_sym.eigenvalues hn with heig
  have h_eig_apply : ∀ i, A (b i) = ((eig i : ℝ) : ℂ) • b i :=
    hA_sym.apply_eigenvectorBasis hn
  have hb_ne : ∀ i, b i ≠ 0 := fun i => b.orthonormal.ne_zero i
  have hbb : ∀ i, inner ℂ (b i) (b i) = (1 : ℂ) := fun i => b.inner_eq_one i
  set d : Fin n → ℝ := fun i => (inner ℂ (b i) (B (b i))).re with hd_def
  have hd0 : ∀ i, eig i = 0 → d i = 0 := by
    intro i hi
    have hBb : B (b i) = 0 := hsupp <| by
      rw [LinearMap.mem_ker]; change A (b i) = 0; rw [h_eig_apply i, hi]; simp
    simp only [hd_def, hBb, inner_zero_right, Complex.zero_re]
  have hev : ∀ (lam : ℝ) (i),
      (((1 - lam : ℝ) : ℂ) • A +
        ((lam * cA : ℝ) : ℂ) • (1 : 𝒦 →L[ℂ] 𝒦)) (b i)
        = (((1 - lam) * eig i + lam * cA : ℝ) : ℂ) • b i := by
    intro lam i
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, h_eig_apply i, smul_smul]
    rw [← add_smul]; push_cast; ring_nf
  have hsa : ∀ (lam : ℝ), IsSelfAdjoint
      (((1 - lam : ℝ) : ℂ) • A +
        ((lam * cA : ℝ) : ℂ) • (1 : 𝒦 →L[ℂ] 𝒦)) := by
    intro lam
    rw [IsSelfAdjoint, star_add, star_smul, hA_sa.star_eq, star_smul, star_one,
      Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal]
  have hlog_apply : ∀ (lam : ℝ) (i),
      CFC.log (((1 - lam : ℝ) : ℂ) • A + ((lam * cA : ℝ) : ℂ) • 1) (b i)
        = ((Real.log ((1 - lam) * eig i + lam * cA) : ℝ) : ℂ) • b i := by
    intro lam i
    exact TensorCFC.cfc_real_apply_eigenvector (hsa lam) Real.log (hev lam i)
      (TensorCFC.mem_spectrum_real_of_eigenvector (hb_ne i) (hev lam i))
  have hinner : ∀ (lam : ℝ) (i),
      (inner ℂ (b i) ((((1 - lam : ℝ) : ℂ) • B + ((lam * cB : ℝ) : ℂ) • 1) (b i))).re
        = (1 - lam) * d i + lam * cB := by
    intro lam i
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      inner_add_right, inner_smul_right, inner_smul_right, hbb i, mul_one, Complex.add_re,
      Complex.re_ofReal_mul, Complex.ofReal_re, hd_def]
  have hexpand : ∀ lam : ℝ,
      (Tr (ContinuousLinearMap.toLinearMap
        ((((1 - lam : ℝ) : ℂ) • B + ((lam * cB : ℝ) : ℂ) • 1) *
          CFC.log (((1 - lam : ℝ) : ℂ) • A +
            ((lam * cA : ℝ) : ℂ) • 1)))).re
        = ∑ i, Real.log ((1 - lam) * eig i + lam * cA) * ((1 - lam) * d i + lam * cB) := by
    intro lam
    change (Tr (((((1 - lam : ℝ) : ℂ) • B + ((lam * cB : ℝ) : ℂ) • 1) *
      CFC.log (((1 - lam : ℝ) : ℂ) • A +
        ((lam * cA : ℝ) : ℂ) • 1)).toLinearMap)).re = _
    rw [LinearMap.trace_eq_sum_inner
        (T := ((((1 - lam : ℝ) : ℂ) • B + ((lam * cB : ℝ) : ℂ) • 1) *
          CFC.log (((1 - lam : ℝ) : ℂ) • A +
            ((lam * cA : ℝ) : ℂ) • 1)).toLinearMap) b, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (inner ℂ (b i)
      (((((1 - lam : ℝ) : ℂ) • B + ((lam * cB : ℝ) : ℂ) • 1) *
        CFC.log (((1 - lam : ℝ) : ℂ) • A +
          ((lam * cA : ℝ) : ℂ) • 1)) (b i))).re = _
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, hlog_apply lam i,
      map_smul, inner_smul_right, Complex.re_ofReal_mul, hinner lam i]
  have hlimval :
      (Tr (ContinuousLinearMap.toLinearMap (B * CFC.log A))).re =
        ∑ i, Real.log (eig i) * d i := by
    simpa only [sub_zero, Complex.ofReal_one, one_smul, zero_mul, Complex.ofReal_zero, zero_smul,
      add_zero, one_mul] using hexpand 0
  rw [hlimval, show (fun lam : ℝ =>
        (Tr (ContinuousLinearMap.toLinearMap
          ((((1 - lam : ℝ) : ℂ) • B + ((lam * cB : ℝ) : ℂ) • 1) *
            CFC.log (((1 - lam : ℝ) : ℂ) • A +
              ((lam * cA : ℝ) : ℂ) • 1)))).re)
      = (fun lam => ∑ i, Real.log ((1 - lam) * eig i + lam * cA) * ((1 - lam) * d i + lam * cB))
        from funext hexpand]
  apply tendsto_finset_sum
  intro i _
  by_cases hi : eig i = 0
  · rw [hi, hd0 i hi]
    simp only [mul_zero, zero_add, Real.log_zero]
    -- term = log(lam*cA) * (lam*cB) → 0 ; target log 0 * 0 = 0
    simpa only [mul_zero] using
      ((tendsto_lam_log_lam_mul hcA).const_mul cB).congr (fun lam => by ring)
  · have heig_pos : 0 < eig i :=
      lt_of_le_of_ne (hA_pos.toLinearMap.nonneg_eigenvalues hn i) (Ne.symm hi)
    have hlogt : Filter.Tendsto (fun lam : ℝ => Real.log ((1 - lam) * eig i + lam * cA))
        (𝓝[>] (0:ℝ)) (𝓝 (Real.log (eig i))) := by
      have hin : Filter.Tendsto (fun lam : ℝ => (1 - lam) * eig i + lam * cA) (𝓝 (0:ℝ))
          (𝓝 (eig i)) := by
        simpa using
          (by fun_prop : Continuous fun lam : ℝ => (1 - lam) * eig i + lam * cA).tendsto 0
      exact ((Real.continuousAt_log (ne_of_gt heig_pos)).tendsto.comp hin).mono_left
        nhdsWithin_le_nhds
    have hdt : Filter.Tendsto (fun lam : ℝ => (1 - lam) * d i + lam * cB) (𝓝[>] (0:ℝ))
        (𝓝 (d i)) := by
      simpa using ((by fun_prop : Continuous fun lam : ℝ =>
        (1 - lam) * d i + lam * cB).tendsto 0).mono_left nhdsWithin_le_nhds
    exact hlogt.mul hdt

omit [Nontrivial ℋ] in
/-- Tr of a nonneg operator is real. -/
lemma tr_eq_re {τ : L ℋ} (hτ : 0 ≤ τ) :
    Tr τ = ((Tr τ).re : ℂ) := by
  have hsym := ((LinearMap.nonneg_iff_isPositive τ).mp hτ).isSymmetric
  have h : Tr τ =
      ((∑ i, hsym.eigenvalues (rfl : Module.finrank ℂ ℋ = _) i : ℝ) : ℂ) := by
    exact hsym.trace_eq_sum_eigenvalues rfl
  apply Complex.ext
  · rw [Complex.ofReal_re]
  · rw [h]; simp

-- `faithfulApprox` in explicit bundled-CPTP form.
lemma faithfulApprox_toFun_eq {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    {τ : L ℋ} (hτ : 0 ≤ τ) :
    (faithfulApprox Φ lam hlam0 hlam1).toFun τ =
      ((1 - lam : ℝ) : ℂ) • Φ.toFun τ +
        ((lam * ((Tr τ).re /
          (Module.finrank ℂ 𝒦 : ℝ)) : ℝ) : ℂ) • (1 : L 𝒦) := by
  have hdepol : ((lam : ℝ) : ℂ) •
      (depolarizingChannel ℋ 𝒦).toFun τ =
        ((lam * ((Tr τ).re /
          (Module.finrank ℂ 𝒦 : ℝ)) : ℝ) : ℂ) • (1 : L 𝒦) := by
    change ((lam : ℝ) : ℂ) •
      ((Tr τ /
        (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)) = _
    rw [smul_smul]
    congr 1
    nth_rewrite 1 [tr_eq_re hτ]
    push_cast
    ring
  change ((1 - lam : ℝ) : ℂ) • Φ.toFun τ +
    ((lam : ℝ) : ℂ) •
      (depolarizingChannel ℋ 𝒦).toFun τ = _
  rw [hdepol]

theorem tendsto_umegakiNorm_faithful_real
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0)
    (hsupp : SupportLE ρ σ) :
    Filter.Tendsto
      (fun lam : ℝ =>
        umegakiNorm
          (((1 - lam : ℝ) : ℂ) • Φ.toFun ρ +
            ((lam * ((Tr ρ).re /
              (Module.finrank ℂ 𝒦 : ℝ)) : ℝ) : ℂ) • 1)
          (((1 - lam : ℝ) : ℂ) • Φ.toFun σ +
            ((lam * ((Tr σ).re /
              (Module.finrank ℂ 𝒦 : ℝ)) : ℝ) : ℂ) • 1))
      (𝓝[>] (0:ℝ)) (𝓝 (umegakiNorm
        (Φ.toFun ρ)
        (Φ.toFun σ))) := by
  have hΦρ : (0 : L 𝒦) ≤ Φ.toFun ρ :=
    map_nonneg Φ.toCompletelyPositiveMap hρ
  have hΦσ : (0 : L 𝒦) ≤ Φ.toFun σ :=
    map_nonneg Φ.toCompletelyPositiveMap hσ
  have hΦsupp := supportLE_map_of_cptp Φ hρ hσ hsupp
  have hΦρ0 : Φ.toFun ρ ≠ 0 :=
    continuity_cptp_toFun_ne_zero Φ hρ hρ0
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    obtain ⟨_, _, h⟩ := nonneg_le_smul_of_suppLE hρ hσ hsupp
    exact hρ0 (le_antisymm (by simpa using h) hρ)
  have hd_pos : (0 : ℝ) < (Module.finrank ℂ 𝒦 : ℝ) := by exact_mod_cast Module.finrank_pos
  have hcρ : 0 < (Tr ρ).re /
      (Module.finrank ℂ 𝒦 : ℝ) :=
    div_pos (QuantumEntropy.trace_re_pos_of_ne_zero hρ hρ0) hd_pos
  have hcσ : 0 < (Tr σ).re /
      (Module.finrank ℂ 𝒦 : ℝ) :=
    div_pos (QuantumEntropy.trace_re_pos_of_ne_zero hσ hσ0) hd_pos
  set cρ := (Tr ρ).re /
    (Module.finrank ℂ 𝒦 : ℝ) with hcρ_def
  set cσ := (Tr σ).re /
    (Module.finrank ℂ 𝒦 : ℝ) with hcσ_def
  let Eρc : B 𝒦 := (Φ.toFun ρ).toContinuousLinearMap
  let Eσc : B 𝒦 := (Φ.toFun σ).toContinuousLinearMap
  have hΦρc : 0 ≤ Eρc := (ContinuousLinearMap.coe_le_coe_iff 0 Eρc).mp hΦρ
  have hΦσc : 0 ≤ Eσc := (ContinuousLinearMap.coe_le_coe_iff 0 Eσc).mp hΦσ
  have hΦρc0 : Eρc ≠ 0 := by
    intro h
    apply hΦρ0
    exact LinearMap.toContinuousLinearMap.injective h
  have hxlogx := tendsto_tr_faithful_cross hΦρc hΦρc (le_refl _)
    (cA := cρ) (cB := cρ) hcρ
  have hcross := tendsto_tr_faithful_cross hΦσc hΦρc hΦsupp
    (cA := cσ) (cB := cρ) hcσ
  have hden : Filter.Tendsto
      (fun lam : ℝ => (Tr (ContinuousLinearMap.toLinearMap
        (((1 - lam : ℝ) : ℂ) • Eρc +
          ((lam * cρ : ℝ) : ℂ) • 1))).re)
      (𝓝[>] (0:ℝ)) (𝓝 (Tr (ContinuousLinearMap.toLinearMap
        Eρc)).re) := by
    have key : (Tr (ContinuousLinearMap.toLinearMap
        Eρc)).re =
      (Tr (ContinuousLinearMap.toLinearMap
        (((1 - (0 : ℝ) : ℝ) : ℂ) • Eρc +
          (((0 : ℝ) * cρ : ℝ) : ℂ) • 1))).re := by simp
    rw [key]
    exact ((QuantumState.continuous_re_trace.comp
      (by fun_prop : Continuous fun lam : ℝ =>
        ((1 - lam : ℝ) : ℂ) • Eρc +
          ((lam * cρ : ℝ) : ℂ) • 1)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have hnum : Filter.Tendsto
      (fun lam : ℝ => (Tr (ContinuousLinearMap.toLinearMap
        ((((1 - lam : ℝ) : ℂ) • Eρc +
            ((lam * cρ : ℝ) : ℂ) • 1) *
          (CFC.log (((1 - lam : ℝ) : ℂ) •
              Eρc +
                ((lam * cρ : ℝ) : ℂ) • 1) -
            CFC.log (((1 - lam : ℝ) : ℂ) •
              Eσc +
                ((lam * cσ : ℝ) : ℂ) • 1))))).re)
      (𝓝[>] (0:ℝ))
      (𝓝 ((Tr (ContinuousLinearMap.toLinearMap
        (Eρc * (CFC.log Eρc - CFC.log Eσc)))).re)) := by
    simpa only [mul_sub, reduction_trace_sub, Complex.sub_re] using
      hxlogx.sub hcross
  have hden0 : (Tr (ContinuousLinearMap.toLinearMap
      Eρc)).re ≠ 0 :=
    ne_of_gt (QuantumEntropy.trace_re_pos_of_ne_zero
      ((ContinuousLinearMap.coe_le_coe_iff _ _).mpr hΦρc)
      (fun h => hΦρc0 (by ext x; exact congrArg (fun A : L _ => A x) h)))
  simpa only [umegakiNorm_eq_toContinuousLinearMap, Eρc, Eσc] using hnum.div hden hden0

theorem tendsto_umegakiNorm_faithful
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (Φ : CPTP ℋ 𝒦)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0)
    (hsupp : SupportLE ρ σ) :
    Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        umegakiNorm
          ((faithfulApprox Φ l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox Φ l.val l.property.1.le l.property.2).toFun σ))
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (𝓝[>] (0:ℝ)))
      (𝓝 (umegakiNorm (Φ.toFun ρ)
        (Φ.toFun σ))) := by
  have heq : (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        umegakiNorm
          ((faithfulApprox Φ l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox Φ l.val l.property.1.le l.property.2).toFun σ))
      = (fun lam : ℝ =>
          umegakiNorm
            (((1 - lam : ℝ) : ℂ) • Φ.toFun ρ +
              ((lam * ((Tr ρ).re /
                (Module.finrank ℂ 𝒦 : ℝ)) : ℝ) : ℂ) • 1)
            (((1 - lam : ℝ) : ℂ) • Φ.toFun σ +
              ((lam * ((Tr σ).re /
                (Module.finrank ℂ 𝒦 : ℝ)) : ℝ) : ℂ) • 1))
        ∘ (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) := by
    funext l
    have hρ_eq := faithfulApprox_toFun_eq Φ l.property.1.le l.property.2 hρ
    have hσ_eq := faithfulApprox_toFun_eq Φ l.property.1.le l.property.2 hσ
    simp only [Function.comp_apply, hρ_eq, hσ_eq]
  rw [heq]
  exact (tendsto_umegakiNorm_faithful_real Φ hρ hσ hρ0 hsupp).comp
    Filter.tendsto_comap

end Umegaki

end UmegakiDPI
