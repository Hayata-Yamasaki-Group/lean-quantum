/-
Finiteness of the free relative entropy.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 5; Hayashi–Yamasaki, Theorem 4.
-/
/-
Subadditivity of the free relative entropy.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 5; Hayashi–Yamasaki, Theorem 4.
-/
/-
Finiteness and subadditivity for free states.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 5; Hayashi–Yamasaki, Theorem 4.
-/
import Quantum.QuantumEntropy.GourResource.TensorSeed
import Quantum.QuantumEntropy.Gour.UmegakiDPIAdapter.GSLCore
import Quantum.QuantumEntropy.GourResource.RelativeCompact


namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem c47_du_nonneg {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ σ : L.{u} A) (hρ : IsDensity.{u} ρ) (hσ : IsDensity.{u} σ) :
    0 ≤ du.{u} ρ σ := by
  let D : OPT.GourMatrixStateDivergence.{u} :=
    fun ρ σ hρ hσ => OPT.petzQuantumRenyiDivergence OPT.petzRenyiOrderOne ρ σ hρ hσ
  have hP := OPT.petzOrderOneLaws_from_umegakiDPI.{u, u}
  have hD : OPT.GourMatrixRelativeEntropyLaws.{u} D :=
    ⟨hP.dataProcessing, fun {_ _} _ _ _ _ _ => hP.tensorAdditivity,
      hP.binaryNormalization⟩
  have hn := (w37_relative_diagonal_calibration D hD).1 ⟨ρ, hρ⟩ ⟨σ, hσ⟩
  simpa only [D, OPT.petzQuantumRenyiDivergence_one_eq_umegakiRelEntropyNN,
    du] using hn

private theorem c47_du_finite {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ σ : L.{u} A) (hσ : IsPositiveDefinite.{u} σ) :
    ∃ x : ℝ, du.{u} ρ σ = (x : EReal) := by
  have hsupp : SandwichedRenyiRelativeEntropy.suppLE ρ σ :=
    SandwichedRenyiRelativeEntropy.suppLE_of_pdSetLM_right ρ
      ((OPT.isPositiveDefinite_iff_mem_pdSetLM σ).mp hσ)
  refine ⟨(1 / Real.log 2) * SandwichedRenyiRelativeEntropy.umegakiNorm ρ σ, ?_⟩
  simp only [du, SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN,
    if_pos hsupp, EReal.coe_mul]

theorem gsl_c47 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ n : ℕ, 0 < n → ∃ x : ℝ, 0 ≤ x ∧ res.{u} du.{u} (pow.{u} ρ n) (F n) = (x : EReal))
:= by
  intro A _ _ ρ F hF n hn
  obtain ⟨γ, lam, _, _, hγ⟩ := GourResource.gsl_y06.{u} ρ F hF
  obtain ⟨hmem, _, _, hpd⟩ := hγ n hn
  have hρn : IsDensity.{u} (pow.{u} ρ n) :=
    (w42_tensor_spectral_dictionary.{u}.1 ρ n).2.1
  have hnonneg : 0 ≤ res.{u} du.{u} (pow.{u} ρ n) (F n) := by
    apply le_iInf
    intro σ
    apply le_iInf
    intro hσ
    exact c47_du_nonneg _ _ hρn (hF.1 n hn hσ)
  obtain ⟨b, hb⟩ := c47_du_finite (pow.{u} ρ n) (pow.{u} γ n) hpd
  have hle : res.{u} du.{u} (pow.{u} ρ n) (F n) ≤ (b : EReal) := by
    exact iInf_le_of_le (pow.{u} γ n) (iInf_le_of_le hmem hb.le)
  have htop : res.{u} du.{u} (pow.{u} ρ n) (F n) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hle (EReal.coe_lt_top b))
  have hbot : res.{u} du.{u} (pow.{u} ρ n) (F n) ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hnonneg)
  obtain ⟨x, hx⟩ := EReal.canLift.prf _ ⟨htop, hbot⟩
  refine ⟨x, ?_, hx.symm⟩
  exact EReal.coe_nonneg.mp (hx.symm ▸ hnonneg)

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem c48_du_push_le
    {A B : Type u} [Qudit A] [Qudit B] [Nontrivial A] [Nontrivial B]
    (U : A ≃ₗᵢ[ℂ] B) (X Y : L A) (hX : IsDensity X) (hY : IsDensity Y) :
    du (push U X) (push U Y) ≤ du X Y := by
  obtain ⟨N, hN⟩ := GourSemiCausal.gourMemory_isometry_channel U.toLinearIsometry
  have h := w38_vn_spectral_dictionary.2.2.1.dataProcessing N X Y hX hY
  change du (N.toLinearMap X) (N.toLinearMap Y) ≤ du X Y at h
  rw [hN] at h
  change du (krausTerm U.toLinearMap X) (krausTerm U.toLinearMap Y) ≤ du X Y at h
  simpa only [push, krausTerm, LinearMap.coe_mk, AddHom.coe_mk,
    LinearIsometryEquiv.adjoint_toLinearMap_eq_symm] using h

private theorem c48_du_tensor
    {A B : Type u} [Qudit A] [Qudit B] [Nontrivial A] [Nontrivial B]
    [Nontrivial (A ⊗[ℂ] B)]
    (X Y : L A) (Z T : L B)
    (hX : IsDensity X) (hY : IsDensity Y) (hZ : IsDensity Z) (hT : IsDensity T) :
    du (TensorProduct.map X Z) (TensorProduct.map Y T) = du X Y + du Z T := by
  exact w38_vn_spectral_dictionary.2.2.1.tensorAdditivity X Y Z T hX hY hZ hT

theorem gsl_c48 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ n m : ℕ, 0 < n → 0 < m →
    res.{u} du.{u} (pow.{u} ρ (n+m)) (F (n+m)) ≤
      res.{u} du.{u} (pow.{u} ρ n) (F n) + res.{u} du.{u} (pow.{u} ρ m) (F m))
:= by
  classical
  intro A _ _ ρ F hF n m hn hm
  obtain ⟨γ, lam, _, _, hγ⟩ := GourResource.gsl_y06.{u} ρ F hF
  have hρn := (w42_tensor_spectral_dictionary.1 ρ n).2.1
  have hρm := (w42_tensor_spectral_dictionary.1 ρ m).2.1
  obtain ⟨X, hX, hminX⟩ := GourResource.gsl_y57.{u} ⟨pow ρ n, hρn⟩ (F n)
    ⟨pow γ n, (hγ n hn).1⟩ (hF.2.1 n hn).1 (hF.1 n hn)
  obtain ⟨Y, hY, hminY⟩ := GourResource.gsl_y57.{u} ⟨pow ρ m, hρm⟩ (F m)
    ⟨pow γ m, (hγ m hm).1⟩ (hF.2.1 m hm).1 (hF.1 m hm)
  have hXd : IsDensity X := hF.1 n hn hX
  have hYd : IsDensity Y := hF.1 m hm hY
  calc
    res du (pow ρ (n+m)) (F (n+m)) ≤
        du (pow ρ (n+m)) (join ρ n m X Y) :=
      iInf_le_of_le (join ρ n m X Y) (iInf_le _ (hF.2.2.1 n m hn hm X hX Y hY))
    _ ≤ du (pow ρ n) X + du (pow ρ m) Y := by
      rw [← (GourResource.gsl_y05.{u} ρ ρ n m).1]
      exact (c48_du_push_le (w44TensorJoin ρ n m)
        (TensorProduct.map (pow ρ n) (pow ρ m)) (TensorProduct.map X Y)
        (OPT.isDensity_tensorProduct _ _ hρn hρm)
        (OPT.isDensity_tensorProduct _ _ hXd hYd)).trans_eq
          (c48_du_tensor _ _ _ _ hρn hXd hρm hYd)
    _ = res du (pow ρ n) (F n) + res du (pow ρ m) (F m) := by
      rw [hminX, hminY]

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_c21 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  (∀ n : ℕ, 0 < n → ∃ x : ℝ, 0 ≤ x ∧
    res.{u} du.{u} (pow.{u} ρ n) (F n) = (x : EReal)) ∧
  (∀ n m : ℕ, 0 < n → 0 < m →
    res.{u} du.{u} (pow.{u} ρ (n+m)) (F (n+m)) ≤
    res.{u} du.{u} (pow.{u} ρ n) (F n) + res.{u} du.{u} (pow.{u} ρ m) (F m)))
:= by
  intro A instQudit instNontrivial ρ F hValid
  exact And.intro (GourResource.gsl_c47.{u} ρ F hValid) (GourResource.gsl_c48.{u} ρ F hValid)

end GourResource

