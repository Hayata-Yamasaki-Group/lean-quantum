/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.KW.Entropies.SteinPrerequisites
import Quantum.QuantumModel.KW.Entropies.SteinPrerequisitesRetained
import Quantum.OperationalProbabilistic.Framework.QuantumRelativeEntropyLaws.GSLCoreRetained
import Quantum.OperationalProbabilistic.OperationalFidelity.GSLCore
import Quantum.QuantumEntropy.Common.TensorDensitySupport.GSLCoreGeneralizedStein
import Quantum.QuantumModel.NativeFidelity.GSLCoreRetained
import Quantum.QuantumModel.POVMObservationBridge.GSLCore

/-!
# Quantum Stein lemma

The achievable rate and strong-converse rate equal the Umegaki relative entropy.
Reference: Khatri--Wilde, arXiv:2011.04672v2, `entropies.tex:7242--7345`;
the finite-support argument is at `entropies.tex:7263--7305`, and the
singular-support argument at `entropies.tex:7251--7261`.

Logarithms have base two. Finite divergences are embedded into the real rate
carrier with `toReal`; support mismatch retains the extended value `top`.
-/

noncomputable section

open QuantumState
open scoped ENNReal NNReal ComplexOrder MatrixOrder Topology

namespace QuantumModel
namespace NativeStein

open NativeHypothesisTesting
open Filter

private theorem umegakiRelEntropyBits_eq_coe_of_supportLE
    {A : Sys} (rho sigma : DensityMatrix A)
    (hsupp : DensityMatrix.SupportLE rho sigma) :
    umegakiRelEntropyBits rho sigma.operator =
      (((SandwichedRenyiRelativeEntropy.umegakiNorm
        rho.operator sigma.operator / Real.log 2 : ℝ)) : EReal) := by
  unfold umegakiRelEntropyBits
  rw [SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN,
    if_pos ((DensityMatrix.supportLE_iff_suppLE rho sigma).1 hsupp),
    ← EReal.coe_div]

private theorem umegakiRelEntropyBits_toReal_nonneg_of_supportLE
    {A : Sys} (rho sigma : DensityMatrix A)
    (hsupp : DensityMatrix.SupportLE rho sigma) :
    0 ≤ (umegakiRelEntropyBits rho sigma.operator).toReal := by
  have hnormE :=
    NativeMeasuredRelativeEntropy.umegakiRelEntropyNN_density_nonneg rho sigma
  rw [SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN,
    if_pos ((DensityMatrix.supportLE_iff_suppLE rho sigma).1 hsupp),
    EReal.coe_nonneg] at hnormE
  rw [umegakiRelEntropyBits_eq_coe_of_supportLE rho sigma hsupp,
    EReal.toReal_coe]
  exact div_nonneg hnormE
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

private theorem binaryNegLog2_antitone : Antitone OPT.binaryNegLog2 := by
  intro p q hpq
  by_cases hp : p = 0
  · rw [hp, OPT.binaryNegLog2_zero]
    exact le_top
  by_cases hq : q = 0
  · have hp0 : p = 0 := nonpos_iff_eq_zero.mp (hq ▸ hpq)
    exact (hp hp0).elim
  simp only [OPT.binaryNegLog2, if_neg hp, if_neg hq,
    EReal.coe_le_coe_iff]
  apply neg_le_neg
  exact Real.logb_le_logb_of_le (b := 2) (by norm_num)
    (by exact_mod_cast (pos_iff_ne_zero.mpr hp)) hpq

private theorem binaryNegLog2_orderReflecting
    {p q : ℝ≥0}
    (h : OPT.binaryNegLog2 q ≤ OPT.binaryNegLog2 p) :
    p ≤ q := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp only [OPT.binaryNegLog2, if_pos hq, if_neg hp] at h
    exact False.elim ((not_le_of_gt (EReal.coe_lt_top _)) h)
  simp only [OPT.binaryNegLog2, if_neg hp, if_neg hq,
    EReal.coe_le_coe_iff] at h
  apply NNReal.coe_le_coe.mp
  apply (Real.logb_le_logb (b := 2) (by norm_num)
    (by exact_mod_cast (pos_iff_ne_zero.mpr hp))
    (by exact_mod_cast (pos_iff_ne_zero.mpr hq))).mp
  linarith

private theorem beta_le_binaryExponentProbability_of_le_binaryNegLog2
    {x : ℝ} {p : ℝ≥0}
    (h : (x : EReal) ≤ OPT.binaryNegLog2 p) :
    p ≤ OPT.binaryExponentProbability x := by
  apply binaryNegLog2_orderReflecting
  rw [OPT.binaryNegLog2_binaryExponentProbability]
  exact h

private theorem betaEpsilon_le_feasible_objective
    {A : Sys} (epsilon : OPT.ProbabilityLevel)
    (rho : DensityMatrix A) (sigma : Operator A)
    (Q : FeasibleTest epsilon rho) :
    betaEpsilon epsilon rho sigma ≤
      Real.toNNReal (testValue Q.1 sigma) := by
  unfold betaEpsilon
  apply csInf_le
  · exact ⟨0, fun _ _ ↦ bot_le⟩
  · exact ⟨Q, rfl⟩

/-- The finite Umegaki divergence itself is an achievable Stein rate when
the alternative state supports the null state.

The proof selects `alpha ∈ (0,1)` from the Petz one-sided limit, applies
Petz tensor-power additivity and the one-shot hypothesis-testing lower bound
for every sufficiently large positive copy number, and turns an exact
`betaEpsilon` optimizer into the required protocol.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:7263--7305`. -/
theorem isAchievableRate_umegaki_of_supportLE
    {A : Sys} (rho sigma : DensityMatrix A)
    (hsupp : DensityMatrix.SupportLE rho sigma) :
    IsAchievableRate rho sigma
      (umegakiRelEntropyBits rho sigma.operator).toReal := by
  let D : ℝ := (umegakiRelEntropyBits rho sigma.operator).toReal
  have hDnonneg : 0 ≤ D :=
    umegakiRelEntropyBits_toReal_nonneg_of_supportLE rho sigma hsupp
  refine ⟨hDnonneg, ?_⟩
  intro epsilon hepsilon delta hdelta
  have hDcoe := umegakiRelEntropyBits_eq_coe_of_supportLE rho sigma hsupp
  have hDtop : umegakiRelEntropyBits rho sigma.operator ≠ ⊤ := by
    rw [hDcoe]
    exact EReal.coe_ne_top _
  have hDbot : umegakiRelEntropyBits rho sigma.operator ≠ ⊥ := by
    rw [hDcoe]
    exact EReal.coe_ne_bot _
  have hlim := petzRenyiDivBits_tendsto_umegaki rho sigma
  have hlimReal : Tendsto
      (fun alpha : ℝ ↦
        (petzRenyiDivBits alpha rho sigma.operator).toReal)
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds D) := by
    exact (EReal.tendsto_toReal hDtop hDbot).comp hlim
  have hmargin : ∀ᶠ alpha in nhdsWithin (1 : ℝ) (Set.Iio 1),
      D - delta / 2 <
        (petzRenyiDivBits alpha rho sigma.operator).toReal :=
    hlimReal.eventually
      (Ioi_mem_nhds (sub_lt_self D (half_pos hdelta)))
  have halpha0Eventually :
      ∀ᶠ alpha in nhdsWithin (1 : ℝ) (Set.Iio 1), 0 < alpha :=
    Filter.Eventually.filter_mono inf_le_left
      (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hfiniteTop :
      ∀ᶠ alpha in nhdsWithin (1 : ℝ) (Set.Iio 1),
      petzRenyiDivBits alpha rho sigma.operator ≠ ⊤ :=
    (hlim.eventually (Iio_mem_nhds (lt_top_iff_ne_top.mpr hDtop))).mono
      (fun _ h ↦ ne_of_lt h)
  have hfiniteBot :
      ∀ᶠ alpha in nhdsWithin (1 : ℝ) (Set.Iio 1),
      petzRenyiDivBits alpha rho sigma.operator ≠ ⊥ :=
    (hlim.eventually (Ioi_mem_nhds (bot_lt_iff_ne_bot.mpr hDbot))).mono
      (fun _ h ↦ ne_of_gt h)
  obtain ⟨alpha, ⟨⟨⟨⟨hmarginAlpha, halpha0⟩, halpha1⟩,
      hAlphaTop⟩, hAlphaBot⟩⟩ :=
    (hmargin.and halpha0Eventually |>.and self_mem_nhdsWithin |>.and
      hfiniteTop |>.and hfiniteBot).exists
  let c : ℝ :=
    (alpha / (alpha - 1)) * Real.logb 2 (1 / epsilon.1)
  have hpenalty : ∀ᶠ n : ℕ in atTop,
      -c ≤ (n : ℝ) * (delta / 2) :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const
      (half_pos hdelta)).eventually_ge_atTop (-c)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hpenalty] with
      n hn hpenaltyN
  have hnReal : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlinear :
      (n : ℝ) * (D - delta) ≤
        (n : ℝ) *
          (petzRenyiDivBits alpha rho sigma.operator).toReal + c := by
    nlinarith
  have hnSub : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have htensor :
      petzRenyiDivBits alpha (densityTensorPow rho n)
          (densityTensorPow sigma n).operator =
        ((((n : ℕ) : ℝ) *
          (petzRenyiDivBits alpha rho sigma.operator).toReal : ℝ) : EReal) := by
    calc
      petzRenyiDivBits alpha (densityTensorPow rho n)
          (densityTensorPow sigma n).operator =
          ((((n : ℕ) : ℝ) : EReal) *
            petzRenyiDivBits alpha rho sigma.operator) := by
        have ht := petzRenyiDivBits_densityTensorPow
          alpha halpha0 halpha1 rho sigma (n - 1)
        rw [hnSub] at ht
        exact ht
      _ = ((((n : ℕ) : ℝ) *
          (petzRenyiDivBits alpha rho sigma.operator).toReal : ℝ) : EReal) := by
        rw [← EReal.coe_toReal hAlphaTop hAlphaBot]
        exact (EReal.coe_mul (n : ℝ)
          (petzRenyiDivBits alpha rho sigma.operator).toReal).symm
  have hlower := petzRenyiDivBits_le_hypothesisTestingDiv
    alpha halpha0 halpha1 epsilon hepsilon
    (densityTensorPow rho n) (densityTensorPow sigma n).operator
    (densityTensorPow sigma n).nonneg
  have hdiv :
      (((n : ℝ) *
          (petzRenyiDivBits alpha rho sigma.operator).toReal + c : ℝ) : EReal) ≤
        hypothesisTestingDiv epsilon (densityTensorPow rho n)
          (densityTensorPow sigma n).operator := by
    rw [htensor] at hlower
    simpa only [c, ← EReal.coe_add] using hlower
  have htarget :
      (((n : ℝ) * (D - delta) : ℝ) : EReal) ≤
        hypothesisTestingDiv epsilon (densityTensorPow rho n)
          (densityTensorPow sigma n).operator :=
    (EReal.coe_le_coe_iff.mpr hlinear).trans hdiv
  obtain ⟨Q, hQoptimal, hQaccept⟩ :=
    exists_betaOptimal_acceptance_eq epsilon (densityTensorPow rho n)
      (densityTensorPow sigma n).operator
      (densityTensorPow sigma n).nonneg
  refine ⟨⟨Q, ?_, ?_⟩⟩
  · rw [hQoptimal.2]
    apply beta_le_binaryExponentProbability_of_le_binaryNegLog2
    simpa only [hypothesisTestingDiv] using htarget
  · rw [hQaccept]
    change Real.toNNReal (1 - (1 - (epsilon.1 : ℝ))) ≤
      ⟨epsilon.1, epsilon.2.1⟩
    rw [show 1 - (1 - (epsilon.1 : ℝ)) = epsilon.1 by ring,
      Real.toNNReal_of_nonneg epsilon.2.1]

end NativeStein
end QuantumModel

namespace QuantumModel
namespace NativeStein

open NativeHypothesisTesting
open Filter

/-- The finite Umegaki divergence itself is a strong-converse Stein rate
when the alternative state supports the null state.

The proof selects `alpha > 1` from the sandwiched Renyi one-sided limit.
Every putative protocol supplies a feasible hypothesis test, whose
type-II exponent contradicts the sandwiched hypothesis-testing upper bound
after tensor-power additivity and a strict asymptotic penalty estimate.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:7307--7336`. -/
theorem isStrongConverseRate_umegaki_of_supportLE
    {A : Sys} (rho sigma : DensityMatrix A)
    (hsupp : DensityMatrix.SupportLE rho sigma) :
    IsStrongConverseRate rho sigma
      (umegakiRelEntropyBits rho sigma.operator).toReal := by
  let D : ℝ := (umegakiRelEntropyBits rho sigma.operator).toReal
  have hDnonneg : 0 ≤ D :=
    umegakiRelEntropyBits_toReal_nonneg_of_supportLE rho sigma hsupp
  refine ⟨hDnonneg, ?_⟩
  intro epsilon hepsilon delta hdelta
  have hDcoe := umegakiRelEntropyBits_eq_coe_of_supportLE rho sigma hsupp
  have hDtop : umegakiRelEntropyBits rho sigma.operator ≠ ⊤ := by
    rw [hDcoe]
    exact EReal.coe_ne_top _
  have hDbot : umegakiRelEntropyBits rho sigma.operator ≠ ⊥ := by
    rw [hDcoe]
    exact EReal.coe_ne_bot _
  have hlim := sandwichedRenyiDivBits_tendsto_umegaki rho sigma
  have hlimReal : Tendsto
      (fun alpha : ℝ ↦
        (sandwichedRenyiDivBits alpha rho sigma.operator).toReal)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds D) := by
    exact (EReal.tendsto_toReal hDtop hDbot).comp hlim
  have hmargin : ∀ᶠ alpha in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      (sandwichedRenyiDivBits alpha rho sigma.operator).toReal <
        D + delta / 2 :=
    hlimReal.eventually
      (Iio_mem_nhds (lt_add_of_pos_right D (half_pos hdelta)))
  have hfiniteTop :
      ∀ᶠ alpha in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      sandwichedRenyiDivBits alpha rho sigma.operator ≠ ⊤ :=
    (hlim.eventually (Iio_mem_nhds (lt_top_iff_ne_top.mpr hDtop))).mono
      (fun _ h ↦ ne_of_lt h)
  have hfiniteBot :
      ∀ᶠ alpha in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      sandwichedRenyiDivBits alpha rho sigma.operator ≠ ⊥ :=
    (hlim.eventually (Ioi_mem_nhds (bot_lt_iff_ne_bot.mpr hDbot))).mono
      (fun _ h ↦ ne_of_gt h)
  obtain ⟨alpha, ⟨⟨⟨hmarginAlpha, halpha⟩,
      hAlphaTop⟩, hAlphaBot⟩⟩ :=
    (hmargin.and self_mem_nhdsWithin |>.and hfiniteTop |>.and
      hfiniteBot).exists
  let c : ℝ :=
    (alpha / (alpha - 1)) * Real.logb 2 (1 / (1 - epsilon.1))
  have hpenalty : ∀ᶠ n : ℕ in atTop,
      c < (n : ℝ) * (delta / 2) :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const
      (half_pos hdelta)).eventually_gt_atTop c
  filter_upwards [eventually_ge_atTop (1 : ℕ), hpenalty] with
      n hn hpenaltyN
  rintro ⟨P⟩
  have htestLeOne :
      testValue P.test (densityTensorPow rho n).operator ≤ 1 := by
    have hnonneg : 0 ≤ testValue
        (⟨1 - P.test.1, P.test.2.2, by simpa using P.test.2.1⟩ :
          Effect (systemPow A n))
        (densityTensorPow rho n).operator := by
      unfold testValue
      apply MatrixHockeyStick.trace_mul_re_nonneg_of_posSemidef
        P.test.2.2
      exact Matrix.nonneg_iff_posSemidef.mp
        ((QuantumChannel.starAlgEquiv_nonneg_iff
          (operatorEquivMatrix (systemPow A n))).mpr
            (densityTensorPow rho n).nonneg)
    unfold testValue MatrixHockeyStick.pairing at hnonneg ⊢
    have htrace : Matrix.trace
        (operatorEquivMatrix (systemPow A n)
          (densityTensorPow rho n).operator) =
        Tr (densityTensorPow rho n).operator := by
      rw [LinearMap.trace_eq_matrix_trace (R := ℂ)
        (b := spaceBasis (systemPow A n))]
      rfl
    rw [Matrix.sub_mul, Matrix.trace_sub, one_mul, Complex.sub_re,
      htrace, (densityTensorPow rho n).trace_one] at hnonneg
    norm_num at hnonneg
    exact hnonneg
  have herrorNonneg :
      0 ≤ 1 - testValue P.test (densityTensorPow rho n).operator :=
    sub_nonneg.mpr htestLeOne
  have herrorReal :
      1 - testValue P.test (densityTensorPow rho n).operator ≤ epsilon.1 := by
    calc
      1 - testValue P.test (densityTensorPow rho n).operator =
          (Real.toNNReal
            (1 - testValue P.test
              (densityTensorPow rho n).operator) : ℝ) :=
        (Real.coe_toNNReal _ herrorNonneg).symm
      _ ≤ epsilon.1 := by exact_mod_cast P.typeI_le
  let Q : FeasibleTest epsilon (densityTensorPow rho n) :=
    ⟨P.test, by linarith⟩
  have hbeta :
      betaEpsilon epsilon (densityTensorPow rho n)
          (densityTensorPow sigma n).operator ≤
        Real.toNNReal
          (testValue P.test (densityTensorPow sigma n).operator) :=
    betaEpsilon_le_feasible_objective epsilon (densityTensorPow rho n)
      (densityTensorPow sigma n).operator Q
  have hbetaExponent :
      betaEpsilon epsilon (densityTensorPow rho n)
          (densityTensorPow sigma n).operator ≤
        OPT.binaryExponentProbability ((n : ℝ) * (D + delta)) :=
    hbeta.trans P.typeII_le
  have hlower :
      (((n : ℝ) * (D + delta) : ℝ) : EReal) ≤
        hypothesisTestingDiv epsilon (densityTensorPow rho n)
          (densityTensorPow sigma n).operator := by
    calc
      (((n : ℝ) * (D + delta) : ℝ) : EReal) =
          OPT.binaryNegLog2
            (OPT.binaryExponentProbability ((n : ℝ) * (D + delta))) :=
        (OPT.binaryNegLog2_binaryExponentProbability _).symm
      _ ≤ OPT.binaryNegLog2
          (betaEpsilon epsilon (densityTensorPow rho n)
            (densityTensorPow sigma n).operator) :=
        binaryNegLog2_antitone hbetaExponent
      _ = hypothesisTestingDiv epsilon (densityTensorPow rho n)
          (densityTensorPow sigma n).operator := rfl
  have hnSub : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have htensor :
      sandwichedRenyiDivBits alpha (densityTensorPow rho n)
          (densityTensorPow sigma n).operator =
        ((((n : ℕ) : ℝ) *
          (sandwichedRenyiDivBits alpha rho sigma.operator).toReal : ℝ) :
            EReal) := by
    calc
      sandwichedRenyiDivBits alpha (densityTensorPow rho n)
          (densityTensorPow sigma n).operator =
          ((((n : ℕ) : ℝ) : EReal) *
            sandwichedRenyiDivBits alpha rho sigma.operator) := by
        have ht := sandwichedRenyiDivBits_densityTensorPow
          alpha halpha rho sigma (n - 1)
        rw [hnSub] at ht
        exact ht
      _ = ((((n : ℕ) : ℝ) *
          (sandwichedRenyiDivBits alpha rho sigma.operator).toReal : ℝ) :
            EReal) := by
        rw [← EReal.coe_toReal hAlphaTop hAlphaBot]
        exact (EReal.coe_mul (n : ℝ)
          (sandwichedRenyiDivBits alpha rho sigma.operator).toReal).symm
  have hupper0 := hypothesisTestingDiv_le_sandwichedRenyi
    alpha halpha epsilon hepsilon (densityTensorPow rho n)
    (densityTensorPow sigma n).operator (densityTensorPow sigma n).nonneg
  have hupper :
      hypothesisTestingDiv epsilon (densityTensorPow rho n)
          (densityTensorPow sigma n).operator ≤
        ((((n : ℕ) : ℝ) *
          (sandwichedRenyiDivBits alpha rho sigma.operator).toReal + c : ℝ) :
            EReal) := by
    rw [htensor] at hupper0
    simpa only [c, ← EReal.coe_add] using hupper0
  have hnRealPos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlinear :
      (n : ℝ) *
          (sandwichedRenyiDivBits alpha rho sigma.operator).toReal + c <
        (n : ℝ) * (D + delta) := by
    nlinarith
  have hstrict :
      ((((n : ℕ) : ℝ) *
          (sandwichedRenyiDivBits alpha rho sigma.operator).toReal + c : ℝ) :
            EReal) <
        (((n : ℝ) * (D + delta) : ℝ) : EReal) :=
    EReal.coe_lt_coe_iff.mpr hlinear
  exact (not_lt_of_ge hlower) (hupper.trans_lt hstrict)

end NativeStein
end QuantumModel

namespace QuantumModel
namespace NativeStein

open NativeHypothesisTesting

end NativeStein
end QuantumModel
