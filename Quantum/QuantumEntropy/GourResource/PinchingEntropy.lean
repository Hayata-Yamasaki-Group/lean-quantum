/-
Shows the additive Pythagorean identity of Umegaki for pinching in EReal.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
/-
Bounds the DU loss by pinching by log₂(number of eigenvalues).
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
import Quantum.QuantumEntropy.GourResource.Definitions
import Quantum.QuantumEntropy.Gour.UmegakiDPIAdapter.GSLCore


namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem du_of_support {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ σ : L A) (h : SandwichedRenyiRelativeEntropy.suppLE ρ σ) :
    du ρ σ = (((1 / Real.log 2) *
      SandwichedRenyiRelativeEntropy.umegakiNorm ρ σ : ℝ) : EReal) := by
  simp [du, SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN, h, EReal.coe_mul]

private theorem du_of_not_support {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ σ : L A) (h : ¬ SandwichedRenyiRelativeEntropy.suppLE ρ σ) :
    du ρ σ = ⊤ := by
  rw [du, SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN, if_neg h]
  exact EReal.coe_mul_top_of_pos (one_div_pos.mpr (Real.log_pos (by norm_num)))

private theorem trace_log_pin {A : Type u} [Qudit.{u} A]
    (σ ρ X : L A) (hσ : σ.IsSymmetric) (hX : Commute X σ) :
    Tr (ρ * CFC.log X) = Tr (pin σ ρ * CFC.log X) := by
  have hfix : (spectralPinchingChannel σ hσ).toFun (CFC.log X) = CFC.log X :=
    (spectralPinchingChannel_eq_iff_commute σ hσ _).mpr (hX.cfc_real Real.log)
  rw [LinearMap.trace_mul_comm ℂ ρ, LinearMap.trace_mul_comm ℂ (pin σ ρ)]
  exact trace_mul_eq_trace_mul_spectralPinching_of_fixed σ hσ (CFC.log X) ρ hfix

theorem gsl_y21 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A),
  du.{u} ρ.1 σ.1 =
    du.{u} ρ.1 (pin.{u} σ.1 ρ.1) + du.{u} (pin.{u} σ.1 ρ.1) σ.1
:= by
  classical
  intro A _ _ ρ σ
  have hρ : 0 ≤ ρ.1 := (LinearMap.nonneg_iff_isPositive _).mpr ρ.2.1
  have hσ : 0 ≤ σ.1 := (LinearMap.nonneg_iff_isPositive _).mpr σ.2.1
  have hpin : IsDensity (pin σ.1 ρ.1) :=
    spectralPinchingChannel_isDensity σ.1 σ.2.1.isSymmetric ρ.1 ρ.2
  have hsuppPin : SandwichedRenyiRelativeEntropy.suppLE ρ.1 (pin σ.1 ρ.1) := by
    intro x hx
    apply QuantumChannel.nonneg_eq_zero_of_le_of_apply_eq_zero hρ
      (le_card_spectralPinching σ.1 σ.2.1.isSymmetric ρ.1 hρ)
    change ((Fintype.card (spectralEigenvalue σ.1) : ℂ) • pin σ.1 ρ.1) x = 0
    rw [LinearMap.smul_apply, LinearMap.mem_ker.mp hx, smul_zero]
  rw [du_of_support _ _ hsuppPin]
  by_cases hsupp : SandwichedRenyiRelativeEntropy.suppLE ρ.1 σ.1
  · have hfix : (spectralPinchingChannel σ.1 σ.2.1.isSymmetric).toFun σ.1 = σ.1 :=
      (spectralPinchingChannel_eq_iff_commute σ.1 σ.2.1.isSymmetric σ.1).mpr
        (Commute.refl _)
    have hpinSupp : SandwichedRenyiRelativeEntropy.suppLE (pin σ.1 ρ.1) σ.1 := by
      have h := SandwichedRenyiRelativeEntropy.suppLE_of_CPTP
        (spectralPinchingChannel σ.1 σ.2.1.isSymmetric) hρ hσ hsupp
      rwa [hfix] at h
    rw [du_of_support _ _ hsupp, du_of_support _ _ hpinSupp, ← EReal.coe_add]
    apply congrArg (fun r : ℝ => (r : EReal))
    have hlogPin := trace_log_pin σ.1 ρ.1 (pin σ.1 ρ.1) σ.2.1.isSymmetric
      (spectralPinchingChannel_commute σ.1 σ.2.1.isSymmetric ρ.1)
    have hlogSigma := trace_log_pin σ.1 ρ.1 σ.1 σ.2.1.isSymmetric (Commute.refl _)
    simp only [SandwichedRenyiRelativeEntropy.umegakiNorm, ρ.2.2, hpin.2,
      Complex.one_re, div_one, mul_sub, map_sub, Complex.sub_re, hlogPin, hlogSigma]
    ring
  · rw [du_of_not_support _ _ hsupp,
      du_of_not_support (pin σ.1 ρ.1) σ.1
        (spectralPinching_not_supportLE ρ.1 σ.1 ρ.2 σ.2 hsupp)]
    exact (EReal.coe_add_top _).symm

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_y22 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A),
  du.{u} ρ.1 (pin.{u} σ.1 ρ.1) ≤
    ((Real.logb 2 (Fintype.card (spectralEigenvalue.{u} σ.1)) : ℝ) : EReal)
:= by
  intro A _ _ ρ σ
  have hρ : (0 : L A) ≤ ρ.1 :=
    (LinearMap.nonneg_iff_isPositive ρ.1).mpr ρ.2.1
  have hpin := le_card_spectralPinching σ.1 σ.2.1.isSymmetric ρ.1 hρ
  have hd : 0 < (Fintype.card (spectralEigenvalue σ.1) : ℝ) := by
    apply Nat.cast_pos.mpr
    apply Nat.pos_of_ne_zero
    intro hzero
    apply IsDensity.ne_zero ρ.2
    exact le_antisymm (by simpa only [hzero, Nat.cast_zero, zero_smul] using hpin) hρ
  have hpinDensity : IsDensity (pin σ.1 ρ.1) :=
    spectralPinchingChannel_isDensity σ.1 σ.2.1.isSymmetric ρ.1 ρ.2
  let D : OPT.GourMatrixStateDivergence.{u} :=
    fun ρ σ hρ hσ => OPT.petzQuantumRenyiDivergence OPT.petzRenyiOrderOne ρ σ hρ hσ
  have hP := OPT.petzOrderOneLaws_from_umegakiDPI.{u, u}
  have hD : OPT.GourMatrixRelativeEntropyLaws.{u} D :=
    ⟨hP.dataProcessing, fun {_ _} _ _ _ _ _ => hP.tensorAdditivity,
      hP.binaryNormalization⟩
  have hupper := (OPT.gourQuantumRelativeEntropy_min_max_bounds hD
    ⟨ρ.1, ρ.2⟩ ⟨pin σ.1 ρ.1, hpinDensity⟩).2
  have hdu : du ρ.1 (pin σ.1 ρ.1) ≤
      OPT.quantumMaxRelativeEntropyBits ⟨ρ.1, ρ.2⟩
        ⟨pin σ.1 ρ.1, hpinDensity⟩ := by
    simpa only [D, OPT.petzQuantumRenyiDivergence_one_eq_umegakiRelEntropyNN,
      du] using hupper
  apply hdu.trans
  apply OPT.OrderedCone.maxRelEntropy_le_of_domination
  rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1) hd]
  simpa only [pin, ← Complex.coe_smul, Complex.ofReal_natCast] using hpin

end GourResource

