/-
Obtains the additive error a of DU by domination toward a full-support right argument.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
/-
The liminfs of the normalized DU sequences before and after rounding agree.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesTypicalityTensorFoundation.GSLCore
import Quantum.QuantumEntropy.GourResource.SpectralRounding


open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower ℝ ℂ (L H) :=
  RestrictScalars.isScalarTower ℝ ℂ (L H)

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem y23_strictlyPositive {A : Type u} [Qudit.{u} A]
    {σ : L.{u} A} (hσ : IsPositiveDefinite σ) : IsStrictlyPositive σ := by
  apply IsUnit.isStrictlyPositive
  · exact (LinearMap.isUnit_iff_isUnit_det σ).mpr (isUnit_iff_ne_zero.mpr hσ.2)
  · exact (LinearMap.nonneg_iff_isPositive σ).mpr hσ.1

private theorem y23_du_finite {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (σ : L.{u} A) (hσ : IsPositiveDefinite σ) :
    du ρ.1 σ =
      (((Tr (ρ.1 * (CFC.log ρ.1 - CFC.log σ))).re / Real.log 2 : ℝ) : EReal) := by
  have hker : LinearMap.ker σ = ⊥ := by
    by_contra hne
    exact hσ.2 (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hne)
  have hsupp : SandwichedRenyiRelativeEntropy.suppLE ρ.1 σ := by
    rw [SandwichedRenyiRelativeEntropy.suppLE, SandwichedRenyiRelativeEntropy.SupportLE, hker]
    exact bot_le
  simp only [du, SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN,
    if_pos hsupp, SandwichedRenyiRelativeEntropy.umegakiNorm, ρ.2.2,
    Complex.one_re, div_one, ← EReal.coe_mul]
  congr 1
  ring

private theorem y23_trace_mono {A : Type u} [Qudit.{u} A]
    {ρ X Y : L.{u} A} (hρ : 0 ≤ ρ) (hXY : X ≤ Y) :
    (Tr (ρ * X)).re ≤ (Tr (ρ * Y)).re := by
  have hs := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg ρ)
  have hp : 0 ≤ CFC.sqrt ρ * (Y - X) * CFC.sqrt ρ := by
    simpa only [hs.star_eq] using
      star_left_conjugate_nonneg (sub_nonneg.mpr hXY) (CFC.sqrt ρ)
  have ht := ((LinearMap.nonneg_iff_isPositive _).mp hp).trace_nonneg
  have he : Tr (CFC.sqrt ρ * (Y - X) * CFC.sqrt ρ) = Tr (ρ * (Y - X)) := by
    rw [LinearMap.trace_mul_cycle, CFC.sqrt_mul_sqrt_self ρ hρ]
  rw [he] at ht
  have hr := (Complex.nonneg_iff.mp ht).1
  simpa only [mul_sub, map_sub, Complex.sub_re, sub_nonneg] using hr

private theorem y23_log_domination {A : Type u} [Qudit.{u} A]
    {σ τ : L.{u} A} (a : ℝ) (hσ : IsPositiveDefinite σ)
    (hdom : (Real.rpow 2 (-a) : ℝ) • σ ≤ τ) :
    (-a * Real.log 2) • (1 : L.{u} A) + CFC.log σ ≤ CFC.log τ := by
  have hr : 0 < Real.rpow 2 (-a) := Real.rpow_pos_of_pos (by norm_num) _
  have hp := y23_strictlyPositive hσ
  have hl := CFC.log_le_log hdom (IsStrictlyPositive.smul hr hp)
  rwa [CFC.log_smul' σ hr hp, Real.rpow_eq_pow,
    Real.log_rpow (show (0 : ℝ) < 2 by norm_num), Algebra.algebraMap_eq_smul_one] at hl

theorem gsl_y23 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ τ : State.{u} A) (a : ℝ),
  0 ≤ a → IsPositiveDefinite.{u} σ.1 → IsPositiveDefinite.{u} τ.1 →
  (Real.rpow 2 (-a) : ℝ) • σ.1 ≤ τ.1 →
    du.{u} ρ.1 τ.1 ≤ du.{u} ρ.1 σ.1 + (a : EReal)
:= by
  intro A _ _ ρ σ τ a _ha hσ hτ hdom
  have ht := y23_trace_mono ((LinearMap.nonneg_iff_isPositive ρ.1).mpr ρ.2.1)
    (y23_log_domination a hσ hdom)
  simp only [mul_add, mul_smul_comm, mul_one, map_add, LinearMap.map_smul_of_tower,
    ρ.2.2, Complex.add_re, Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one] at ht
  rw [y23_du_finite ρ τ.1 hτ, y23_du_finite ρ σ.1 hσ, ← EReal.coe_add,
    EReal.coe_le_coe_iff]
  simp only [mul_sub, map_sub, Complex.sub_re]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ hlog).mpr
  rw [add_mul, div_mul_cancel₀ _ hlog.ne']
  linarith

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem positive_of_lower_bound {A : Type u} [Qudit A] [Nontrivial A]
    (X : L A) (c : ℝ) (hc : 0 < c) (hX : c • (1 : L A) ≤ X) :
    IsPositiveDefinite X := by
  apply (OPT.isPositiveDefinite_iff_mem_pdSetLM X).mpr
  have hp : c • (1 : L A) ∈ SandwichedRenyiRelativeEntropy.pdSetLM := by
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using
      (SandwichedRenyiRelativeEntropy.pos_smul_one_pdSetLM (ℋ := A) hc)
  simpa only [sub_add_cancel] using
    SandwichedRenyiRelativeEntropy.pdSetLM_add_nonneg (sub_nonneg.mpr hX) hp

private theorem normalized_le {x y : EReal} {a : ℝ} {n : ℕ}
    (h : x ≤ y + (a : EReal)) :
    ((1 / (n : ℝ) : ℝ) : EReal) * x ≤
      ((1 / (n : ℝ) : ℝ) : EReal) * y + ((a / (n : ℝ) : ℝ) : EReal) := by
  have hn : (0 : EReal) ≤ ((1 / (n : ℝ) : ℝ) : EReal) := by positivity
  have hm := mul_le_mul_of_nonneg_left h hn
  rw [EReal.left_distrib_of_nonneg_of_ne_top hn (EReal.coe_ne_top _) y a,
    ← EReal.coe_mul] at hm
  simpa only [one_div, inv_mul_eq_div] using hm

private theorem liminf_le_of_vanishing_error (f g : ℕ → EReal) (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0))
    (h : ∀ᶠ n in atTop, f n ≤ g n + (e n : EReal)) :
    Filter.liminf f atTop ≤ Filter.liminf g atTop := by
  have hz : Filter.limsup (fun n => (e n : EReal)) atTop = 0 :=
    (EReal.tendsto_coe.mpr he).limsup_eq
  have ha := EReal.liminf_add_le (u := fun n => (e n : EReal)) (v := g)
    (f := atTop) (Or.inl (by rw [hz]; exact EReal.coe_ne_bot 0))
    (Or.inl (by rw [hz]; exact EReal.coe_ne_top 0))
  have hb : Filter.liminf f atTop ≤
      Filter.liminf ((fun n => (e n : EReal)) + g) atTop :=
    Filter.liminf_le_liminf (h.mono fun n hn => hn.trans_eq (add_comm _ _))
  exact hb.trans (by simpa only [hz, zero_add] using ha)

theorem gsl_y24 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (S : OpSeq.{u} A) (lam : ℝ),
  lam ∈ Set.Ioc 0 1 →
  (∀ n : ℕ, 0 < n → IsDensity.{u} (S n) ∧
    (lam^n/3 : ℝ) • (1 : L.{u} (Copy.{u} A n)) ≤ S n) →
  Filter.liminf (seqRate.{u} ρ S) atTop =
    Filter.liminf (seqRate.{u} ρ (fun n => rounded.{u} lam n (S n))) atTop
:= by
  intro A _ _ ρ S lam hlam hS
  obtain ⟨hc, hlim⟩ := GourResource.gsl_y14 lam hlam
  have hboth : ∀ᶠ n in atTop,
      seqRate ρ S n ≤ seqRate ρ (fun k => rounded lam k (S k)) n +
        ((cBits lam n / (n : ℝ) : ℝ) : EReal) ∧
      seqRate ρ (fun k => rounded lam k (S k)) n ≤ seqRate ρ S n +
        ((cBits lam n / (n : ℝ) : ℝ) : EReal) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    obtain ⟨hSn, hbound⟩ := hS n hn
    let σ : State (Copy A n) := ⟨S n, hSn⟩
    obtain ⟨hr, hrpos, hlo, hhi⟩ := GourResource.gsl_y19.{u} σ lam n hlam hn hbound
    let τ : State (Copy A n) := ⟨rounded lam n (S n), hr⟩
    let ρn : State (Copy A n) := ⟨pow ρ n, (w42_tensor_spectral_dictionary.1 ρ n).2.1⟩
    have hpos : IsPositiveDefinite σ.1 :=
      positive_of_lower_bound (S n) (lam ^ n / 3)
        (div_pos (pow_pos hlam.1 n) (by norm_num)) hbound
    have hrev : (Real.rpow 2 (-cBits lam n) : ℝ) • τ.1 ≤ σ.1 := by
      have hcancel : Real.rpow 2 (-cBits lam n) * Real.rpow 2 (cBits lam n) = 1 := by
        change (2 : ℝ) ^ (-cBits lam n) * (2 : ℝ) ^ (cBits lam n) = 1
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
      calc
        (Real.rpow 2 (-cBits lam n) : ℝ) • τ.1 ≤
            (Real.rpow 2 (-cBits lam n) : ℝ) •
              ((Real.rpow 2 (cBits lam n) : ℝ) • σ.1) :=
          smul_le_smul_of_nonneg_left hhi (Real.rpow_nonneg (by norm_num) _)
        _ = σ.1 := by rw [smul_smul, hcancel, one_smul]
    have hforward := normalized_le (n := n) (GourResource.gsl_y23.{u} ρn σ τ (cBits lam n)
      (hc n).le hpos hrpos hlo)
    have hbackward := normalized_le (n := n) (GourResource.gsl_y23.{u} ρn τ σ (cBits lam n)
      (hc n).le hrpos hpos hrev)
    simpa only [seqRate, rate, if_neg (Nat.ne_of_gt hn)] using And.intro hbackward hforward
  apply le_antisymm
  · exact liminf_le_of_vanishing_error _ _ _ hlim (hboth.mono fun _ h => h.1)
  · exact liminf_le_of_vanishing_error _ _ _ hlim (hboth.mono fun _ h => h.2)

end GourResource

