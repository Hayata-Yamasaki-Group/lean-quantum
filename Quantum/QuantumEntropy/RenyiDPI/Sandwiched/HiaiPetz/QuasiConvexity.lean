import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.SigmaTerm
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.QuasiContinuity
import Quantum.QuantumEntropy.Common.PositiveDefinitePerturbation

open scoped Quantum.TraceInequality.Loewner

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

private lemma trace_mul_convexCombo_re {H : Type u} [Qudit H]
    (Z ρ₁ ρ₂ : L H) (θ : ℝ) :
    (Tr (Z * ((1 - θ) • ρ₁ + θ • ρ₂))).re =
      (1 - θ) * (Tr (Z * ρ₁)).re + θ * (Tr (Z * ρ₂)).re := by
  simp only [mul_add, mul_smul_comm, map_add, LinearMap.map_smul_of_tower,
    Complex.add_re, Complex.real_smul, Complex.re_ofReal_mul]

private lemma linear_sub_concave {α θ r₁ r₂ s₁ s₂ s : ℝ}
    (hα : 1 < α) (hs : (1 - θ) * s₁ + θ * s₂ ≤ s) :
    α * ((1 - θ) * r₁ + θ * r₂) - (α - 1) * s ≤
      (1 - θ) * (α * r₁ - (α - 1) * s₁) +
        θ * (α * r₂ - (α - 1) * s₂) := by
  have hscaled := mul_le_mul_of_nonneg_left hs (le_of_lt (sub_pos.mpr hα))
  nlinarith only [hscaled]

theorem quasiVar_jointlyConvex_pd_hiaiPetz :
∀ {H : Type u} [Qudit H] [Nontrivial H] {α : ℝ} {Z : L H},
  1 < α → Z ∈ pdSetLM (ℋ := H) →
  JointlyConvexOn (pdSetLM (ℋ := H)) (pdSetLM (ℋ := H))
    (fun ρ σ => (quasiVar α ρ σ Z).re) := by
  intro H _ _ α Z hα hZ ρ₁ ρ₂ σ₁ σ₂ θ _hρ₁ _hρ₂ hσ₁ hσ₂ hθ0 hθ1
  have hσ := (RenyiDPI.sigmaTerm_concave_hiaiPetz hα hZ).2 hσ₁ hσ₂ (sub_nonneg.mpr hθ1) hθ0
    (sub_add_cancel 1 θ)
  simp only [smul_eq_mul] at hσ
  simp only [quasiVar_eq_direct, Complex.sub_re, Complex.re_ofReal_mul, smul_eq_mul]
  rw [trace_mul_convexCombo_re]
  exact linear_sub_concave hα hσ

private theorem s06_regularization_continuous {H : Type u} [Qudit H] (A B : L H) :
    Continuous (fun ε : ℝ => (A + (ε : ℂ) • 1, B + (ε : ℂ) • 1)) := by
  have hsmul : Continuous (fun ε : ℝ => (ε : ℂ) • (1 : L H)) :=
    Complex.continuous_ofReal.smul continuous_const
  exact (continuous_const.add hsmul).prodMk (continuous_const.add hsmul)

private theorem s06_regularization_pair {H : Type u} [Qudit H] [Nontrivial H]
    (A B : L H) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Filter.Tendsto (fun ε : ℝ => (A + (ε : ℂ) • 1, B + (ε : ℂ) • 1))
      (𝓝[>] (0 : ℝ))
      (𝓝[({X : L H | 0 ≤ X} ×ˢ {X : L H | 0 ≤ X})] (A, B)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · simpa using
      ((s06_regularization_continuous A B).tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hn : (0 : L H) ≤ (ε : ℂ) • (1 : L H) :=
      nonneg_of_pdSetLM (pos_smul_one_pdSetLM hε)
    exact ⟨add_nonneg hA hn, add_nonneg hB hn⟩

private theorem s06_regularization_limit {H : Type u} [Qudit H] [Nontrivial H]
    (f : L H → L H → ℝ) (A B : L H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcont : ContinuousOn (Function.uncurry f)
      ({X : L H | 0 ≤ X} ×ˢ {X : L H | 0 ≤ X})) :
    Filter.Tendsto ((Function.uncurry f).comp
      (fun ε : ℝ => (A + (ε : ℂ) • 1, B + (ε : ℂ) • 1)))
      (𝓝[>] (0 : ℝ)) (𝓝 (Function.uncurry f (A, B))) := by
  exact (hcont (A, B) ⟨hA, hB⟩).tendsto.comp (s06_regularization_pair A B hA hB)

private theorem s06_regularization_combo {H : Type u} [Qudit H]
    (A B : L H) (θ ε : ℝ) :
    ((1 - θ) • A + θ • B) + (ε : ℂ) • 1 =
      (1 - θ) • (A + (ε : ℂ) • 1) + θ • (B + (ε : ℂ) • 1) := by
  have h1 : (1 - θ) • ((ε : ℂ) • (1 : L H)) +
      θ • ((ε : ℂ) • (1 : L H)) = (ε : ℂ) • (1 : L H) := by
    rw [← add_smul]
    simp only [sub_add_cancel, one_smul]
  simp only [smul_add]
  rw [show (1 - θ) • A + (1 - θ) • ((ε : ℂ) • (1 : L H)) +
      (θ • B + θ • ((ε : ℂ) • (1 : L H))) =
      ((1 - θ) • A + θ • B) +
        ((1 - θ) • ((ε : ℂ) • (1 : L H)) + θ • ((ε : ℂ) • (1 : L H)))
      from by abel, h1]

private theorem s06_jointlyConvex_nonneg_of_pd
    {H : Type u} [Qudit H] [Nontrivial H] (f : L H → L H → ℝ)
    (hcont : ContinuousOn (Function.uncurry f)
      ({A : L H | 0 ≤ A} ×ˢ {A : L H | 0 ≤ A}))
    (hpd : JointlyConvexOn (pdSetLM (ℋ := H)) (pdSetLM (ℋ := H)) f) :
    JointlyConvexOn {A : L H | 0 ≤ A} {A : L H | 0 ≤ A} f := by
  intro ρ₁ ρ₂ σ₁ σ₂ θ hρ₁ hρ₂ hσ₁ hσ₂ hθ0 hθ1
  have hρc : (0 : L H) ≤ (1 - θ) • ρ₁ + θ • ρ₂ :=
    add_nonneg (smul_nonneg (sub_nonneg.mpr hθ1) hρ₁) (smul_nonneg hθ0 hρ₂)
  have hσc : (0 : L H) ≤ (1 - θ) • σ₁ + θ • σ₂ :=
    add_nonneg (smul_nonneg (sub_nonneg.mpr hθ1) hσ₁) (smul_nonneg hθ0 hσ₂)
  refine le_of_tendsto_of_tendsto (s06_regularization_limit f _ _ hρc hσc hcont)
    (((s06_regularization_limit f ρ₁ σ₁ hρ₁ hσ₁ hcont).const_smul (1 - θ)).add
      ((s06_regularization_limit f ρ₂ σ₂ hρ₂ hσ₂ hcont).const_smul θ)) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change f (((1 - θ) • ρ₁ + θ • ρ₂) + (ε : ℂ) • 1)
      (((1 - θ) • σ₁ + θ • σ₂) + (ε : ℂ) • 1) ≤
    (1 - θ) • f (ρ₁ + (ε : ℂ) • 1) (σ₁ + (ε : ℂ) • 1) +
      θ • f (ρ₂ + (ε : ℂ) • 1) (σ₂ + (ε : ℂ) • 1)
  rw [s06_regularization_combo ρ₁ ρ₂ θ ε, s06_regularization_combo σ₁ σ₂ θ ε]
  exact hpd (nonneg_add_pos_smul_one_pdSetLM hρ₁ hε)
    (nonneg_add_pos_smul_one_pdSetLM hρ₂ hε)
    (nonneg_add_pos_smul_one_pdSetLM hσ₁ hε)
    (nonneg_add_pos_smul_one_pdSetLM hσ₂ hε) hθ0 hθ1

theorem quasiVar_jointlyConvex_nonneg_hiaiPetz :
∀ {H : Type u} [Qudit H] [Nontrivial H] {α : ℝ} {Z : L H},
  1 < α → Z ∈ pdSetLM (ℋ := H) →
  JointlyConvexOn {A : L H | 0 ≤ A} {A : L H | 0 ≤ A}
    (fun ρ σ => (quasiVar α ρ σ Z).re) := by
  intro H _ _ α Z hα hZ
  exact s06_jointlyConvex_nonneg_of_pd (fun ρ σ => (quasiVar α ρ σ Z).re)
    (RenyiDPI.quasiVar_continuousOn_nonneg_gt hα (nonneg_of_pdSetLM hZ))
    (RenyiDPI.quasiVar_jointlyConvex_pd_hiaiPetz hα hZ)

end RenyiDPI
