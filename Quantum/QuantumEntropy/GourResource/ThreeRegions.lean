/-
Adds the weighted traces over the three regions I−P, P−Q, Q and obtains an upper bound on DU for finite n.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
import Quantum.OperationalProbabilistic.Framework.TestingRegionDecisionDefinitions.GSLCore
import Quantum.QuantumEntropy.GourResource.WeightedLog
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificatesGeneralizedStein


namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem du_eq_logWeight_one {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ σ : State.{u} A) (hσ : IsPositiveDefinite σ.1) :
    du ρ.1 σ.1 = ((logWeight ρ.1 σ.1 1 : ℝ) : EReal) := by
  have hpd : σ.1 ∈ SandwichedRenyiRelativeEntropy.pdSetLM :=
    SandwichedRenyiRelativeEntropy.pdSetLM_of_nonneg_isUnit
      ((LinearMap.nonneg_iff_isPositive _).mpr hσ.1)
      ((LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hσ.2))
  have hs := SandwichedRenyiRelativeEntropy.suppLE_of_pdSetLM_right ρ.1 hpd
  simp only [du, SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN, if_pos hs,
    ← EReal.coe_mul, SandwichedRenyiRelativeEntropy.umegakiNorm, ρ.2.2,
    Complex.one_re, div_one, logWeight, mul_one]
  congr 1
  ring

private theorem logWeight_sub {A : Type u} [Qudit.{u} A]
    (ρ σ E F : L.{u} A) :
    logWeight ρ σ (E - F) = logWeight ρ σ E - logWeight ρ σ F := by
  simp only [logWeight, mul_sub, sub_mul, map_sub, Complex.sub_re, sub_div]
  ring

private theorem pairing_sub {A : Type u} [Qudit.{u} A] (ρ E F : L.{u} A) :
    pairing ρ (E - F) = pairing ρ E - pairing ρ F := by
  simp only [pairing, mul_sub, map_sub, Complex.sub_re]

theorem gsl_y38 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (a b c : ℝ),
  IsPositiveDefinite.{u} σ.1 → Commute ρ.1 σ.1 → a ≤ b → b ≤ c →
  (Real.rpow 2 (-c) : ℝ) • (1 : L.{u} A) ≤ σ.1 →
  du.{u} ρ.1 σ.1 ≤
    ((a + (b-a)*testMass.{u} ρ.1 σ.1 a +
      (c-b)*testMass.{u} ρ.1 σ.1 b : ℝ) : EReal)
:= by
  intro A _ _ ρ σ a b c hσ hcomm hab _hbc hcap
  let P := testHi ρ.1 σ.1 a
  let Q := testHi ρ.1 σ.1 b
  obtain ⟨_hQP_le, hcommPQ, hIpos, hDpos, hQpos, _hID, hDQ, _hIQ,
    hPP, hQQ, _hPsym, _hQsym, hPρ, hPσ, hQρ, hQσ⟩ := GourResource.gsl_y35.{u} ρ σ a b hcomm hab
  change (P - Q) * Q = 0 at hDQ
  change P * P = P at hPP
  change Q * Q = Q at hQQ
  have hPQ : P * Q = Q := by
    rw [sub_mul, hQQ] at hDQ
    exact sub_eq_zero.mp hDQ
  have hQP : Q * P = Q := hcommPQ.eq.symm.trans hPQ
  have hII : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hPP]; abel
  have hDD : (P - Q) * (P - Q) = P - Q := by
    calc
      (P - Q) * (P - Q) = P * P - P * Q - Q * P + Q * Q := by noncomm_ring
      _ = P - Q := by rw [hPP, hPQ, hQP, hQQ]; abel
  have hIρ : Commute (1 - P) ρ.1 := (Commute.one_left _).sub_left hPρ
  have hIσ : Commute (1 - P) σ.1 := (Commute.one_left _).sub_left hPσ
  have hDρ : Commute (P - Q) ρ.1 := hPρ.sub_left hQρ
  have hDσ : Commute (P - Q) σ.1 := hPσ.sub_left hQσ
  have hPle : P ≤ 1 := by
    exact sub_nonneg.mp ((LinearMap.nonneg_iff_isPositive _).mpr hIpos)
  have hDle : P - Q ≤ 1 - Q := sub_le_sub_right hPle Q
  have ha := GourResource.gsl_y36.{u} ρ σ a hσ hcomm (1 - P) hIpos hII hIρ hIσ le_rfl
  have hb := GourResource.gsl_y36.{u} ρ σ b hσ hcomm (P - Q) hDpos hDD hDρ hDσ hDle
  have hc := GourResource.gsl_y37.{u} ρ σ c hσ hcomm hcap Q hQpos hQQ hQρ hQσ
  have hmass : pairing ρ.1 1 = 1 := by
    simp only [pairing, mul_one, ρ.2.2, Complex.one_re]
  rw [logWeight_sub, pairing_sub, hmass] at ha
  rw [logWeight_sub, pairing_sub] at hb
  rw [du_eq_logWeight_one ρ σ hσ]
  apply EReal.coe_le_coe_iff.mpr
  change logWeight ρ.1 σ.1 1 ≤ a + (b - a) * pairing ρ.1 P + (c - b) * pairing ρ.1 Q
  nlinarith [ha, hb, hc]

end GourResource

