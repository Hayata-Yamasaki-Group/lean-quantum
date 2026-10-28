/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.SandwichedRenyiLMCompat.GSLCore
import Quantum.QuantumModel.KW.Distances.HypothesisTestingBounds.RelativeEntropy.GSLCore
import Quantum.TraceInequality.AudenaertChernoff.GSLCore
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-! # Hypothesis-testing bounds

The Audenaert--Chernoff lower-bound argument.
-/

noncomputable section

open QuantumState
open QuantumChannel HaarUnitary TensorProduct MeasureTheory
open GeneralizedPerspectiveFunction
open scoped ENNReal NNReal ComplexOrder MatrixOrder Topology MeasureTheory
open Filter

namespace QuantumModel
namespace NativeHypothesisTesting

attribute [local instance]
  operatorSelfAdjointCFCBounds operatorSelfAdjointUnitalCFCBounds
  operatorNonnegSpectrumBounds classicalSpaceSelfAdjointUnitalCFCBounds
  classicalSpaceNonnegSpectrumBounds

/-! ## Audenaert--Chernoff lower bound for the Petz divergence -/


private def audenaertSupportProjectionBounds {A : Sys}
    (X : Operator A) : Operator A :=
  (LinearMap.range X).starProjection

private theorem audenaertSupportProjection_isSymmetricProjectionBounds
    {A : Sys} (X : Operator A) :
    (audenaertSupportProjectionBounds X).IsSymmetricProjection :=
  Submodule.isSymmetricProjection_starProjection (LinearMap.range X)

private theorem audenaertSupportProjection_povmElementBounds
    {A : Sys} (X : Operator A) :
    NativeNoCloning.POVMElement (audenaertSupportProjectionBounds X) := by
  constructor
  · exact (LinearMap.nonneg_iff_isPositive _).mpr
      (audenaertSupportProjection_isSymmetricProjectionBounds X).isPositive
  · let hP := audenaertSupportProjection_isSymmetricProjectionBounds X
    let hI : (LinearMap.id : Operator A).IsSymmetricProjection := by
      constructor
      · rw [IsIdempotentElem]
        ext x
        rfl
      · intro x y
        rfl
    exact (hP.le_iff_range_le_range hI).mpr fun x _ => ⟨x, rfl⟩

private theorem audenaertSupportProjection_comp_selfBounds
    {A : Sys} (X : Operator A) :
    (audenaertSupportProjectionBounds X).comp X = X := by
  apply LinearMap.ext
  intro x
  exact Submodule.starProjection_eq_self_iff.mpr ⟨x, rfl⟩

private theorem audenaertSupportProjection_comp_eq_zeroBounds
    {A : Sys} (P Q : Operator A)
    (hP : P.IsSymmetric) (hPQ : P.comp Q = 0) :
    (audenaertSupportProjectionBounds P).comp Q = 0 := by
  apply LinearMap.ext
  intro x
  apply (Submodule.starProjection_apply_eq_zero_iff
    (K := LinearMap.range P)).mpr
  intro y hy
  rcases hy with ⟨z, rfl⟩
  rw [hP]
  have hzero : P (Q x) = 0 := LinearMap.congr_fun hPQ x
  rw [hzero, inner_zero_right]

private theorem audenaertPositiveSupport_pairingBounds
    {A : Sys} (X : Operator A) (hX : IsSelfAdjoint X) :
    (audenaertSupportProjectionBounds X⁺).comp X = X⁺ := by
  let P : Operator A := X⁺
  let N : Operator A := X⁻
  have hPpos : 0 ≤ P := by simpa only [P] using CFC.posPart_nonneg X
  have hPsymm : P.IsSymmetric :=
    ((LinearMap.nonneg_iff_isPositive P).mp hPpos).isSymmetric
  have hPN : P.comp N = 0 := by
    change X⁺ * X⁻ = 0
    exact CFC.posPart_mul_negPart X
  have hself : (audenaertSupportProjectionBounds P).comp P = P :=
    audenaertSupportProjection_comp_selfBounds P
  have hzero : (audenaertSupportProjectionBounds P).comp N = 0 :=
    audenaertSupportProjection_comp_eq_zeroBounds P N hPsymm hPN
  calc
    (audenaertSupportProjectionBounds X⁺).comp X =
        (audenaertSupportProjectionBounds P).comp (P - N) := by
      rw [CFC.posPart_sub_negPart X hX]
    _ = P := by rw [LinearMap.comp_sub, hself, hzero, sub_zero]
    _ = X⁺ := rfl

private noncomputable def audenaertEffectBounds {A : Sys}
    (X : Operator A) : Effect A := by
  let P := audenaertSupportProjectionBounds X⁺
  have hP := audenaertSupportProjection_povmElementBounds X⁺
  refine ⟨operatorEquivMatrix A P, ?_⟩
  constructor
  · exact Matrix.nonneg_iff_posSemidef.mp
      ((QuantumChannel.starAlgEquiv_nonneg_iff
        (operatorEquivMatrix A)).mpr hP.1)
  · have hcomp : 0 ≤ (1 : Operator A) - P := sub_nonneg.mpr hP.2
    have hmapped := (QuantumChannel.starAlgEquiv_nonneg_iff
      (operatorEquivMatrix A)).mpr hcomp
    simpa only [map_sub, map_one] using
      (Matrix.nonneg_iff_posSemidef.mp hmapped)

private theorem testValue_audenaertEffectBounds {A : Sys}
    (H X : Operator A) :
    testValue (audenaertEffectBounds H) X =
      (Tr ((audenaertSupportProjectionBounds H⁺).comp X)).re := by
  unfold testValue MatrixHockeyStick.pairing audenaertEffectBounds
  change
    (Matrix.trace
      (operatorEquivMatrix A (audenaertSupportProjectionBounds H⁺) *
        operatorEquivMatrix A X)).re = _
  rw [← map_mul]
  have htrace :
      Matrix.trace (operatorEquivMatrix A
        ((audenaertSupportProjectionBounds H⁺).comp X)) =
        Tr ((audenaertSupportProjectionBounds H⁺).comp X) := by
    rw [LinearMap.trace_eq_matrix_trace (R := ℂ) (b := spaceBasis A)]
    rfl
  rw [Module.End.mul_eq_comp, htrace]

private theorem exists_weightedError_le_scaledPetzBounds
    {A : Sys} (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (rho : DensityMatrix A) (sigma : Operator A) (hsigma : 0 ≤ sigma) :
    ∃ Q : Effect A,
      p * (1 - testValue Q rho.operator) +
          (1 - p) * testValue Q sigma ≤
        (Tr (CFC.rpow ((p : ℂ) • rho.operator) alpha *
          CFC.rpow (((1 - p : ℝ) : ℂ) • sigma) (1 - alpha))).re := by
  let X : Operator A := (p : ℂ) • rho.operator
  let Y : Operator A := ((1 - p : ℝ) : ℂ) • sigma
  let H : Operator A := X - Y
  let Q : Effect A := audenaertEffectBounds H
  have hX : 0 ≤ X := by
    apply (LinearMap.nonneg_iff_isPositive _).mpr
    exact ((LinearMap.nonneg_iff_isPositive _).mp rho.nonneg).smul_of_nonneg
      (Complex.zero_le_real.mpr hp0.le)
  have hY : 0 ≤ Y := by
    apply (LinearMap.nonneg_iff_isPositive _).mpr
    exact ((LinearMap.nonneg_iff_isPositive _).mp hsigma).smul_of_nonneg
      (Complex.zero_le_real.mpr (sub_nonneg.mpr hp1.le))
  have hH : IsSelfAdjoint H :=
    (IsSelfAdjoint.of_nonneg hX).sub (IsSelfAdjoint.of_nonneg hY)
  have htraceX : (Tr X).re = p := by
    dsimp only [X]
    rw [map_smul, rho.trace_one]
    simp
  have herror :
      p * (1 - testValue Q rho.operator) +
          (1 - p) * testValue Q sigma =
        (Tr X).re - (Tr H⁺).re := by
    rw [show Q = audenaertEffectBounds H by rfl,
      testValue_audenaertEffectBounds,
      testValue_audenaertEffectBounds]
    have hpair := audenaertPositiveSupport_pairingBounds H hH
    have htracePair := congrArg (fun Z : Operator A => (Tr Z).re) hpair
    have hcombine :
        p * (Tr ((audenaertSupportProjectionBounds H⁺).comp rho.operator)).re -
            (1 - p) *
              (Tr ((audenaertSupportProjectionBounds H⁺).comp sigma)).re =
          (Tr ((audenaertSupportProjectionBounds H⁺).comp H)).re := by
      dsimp only [H, X, Y]
      simp only [LinearMap.comp_sub, LinearMap.comp_smul, map_sub, map_smul,
        Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
    rw [htraceX]
    linarith
  have hGamma : 0 ≤ H⁻ := CFC.negPart_nonneg H
  have hdecomp : H⁺ - H⁻ = H := CFC.posPart_sub_negPart H hH
  have htraceDecomp :
      (Tr H⁺).re - (Tr H⁻).re = (Tr X).re - (Tr Y).re := by
    have := congrArg (fun Z : Operator A => (Tr Z).re) hdecomp
    dsimp only [H] at this
    simpa only [map_sub, Complex.sub_re] using this
  have habs : CFC.abs H = H⁺ + H⁻ :=
    (CFC.posPart_add_negPart H hH).symm
  have htraceAbs :
      (Tr (CFC.abs H)).re = (Tr H⁺).re + (Tr H⁻).re := by
    rw [habs, map_add, Complex.add_re]
  have hleft :
      (1 / 2 : ℝ) *
          ((Tr (X + Y)).re - (Tr (CFC.abs (X - Y))).re) =
        (Tr X).re - (Tr H⁺).re := by
    change (1 / 2 : ℝ) *
        ((Tr (X + Y)).re - (Tr (CFC.abs H)).re) = _
    rw [map_add, Complex.add_re, htraceAbs]
    linarith
  have hspectral := AudenaertChernoff.spectral_inequality
    X Y hX hY alpha halpha0 halpha1
  refine ⟨Q, ?_⟩
  rw [herror, ← hleft]
  simpa only [X, Y] using hspectral

private theorem rpow_smul_posBounds {A : Sys}
    (X : Operator A) (hX : 0 ≤ X)
    (c y : ℝ) (hc : 0 < c) (hy : 0 ≤ y) :
    CFC.rpow ((c : ℂ) • X) y =
      ((c ^ y : ℝ) : ℂ) • CFC.rpow X y := by
  have hscaled : 0 ≤ (c : ℂ) • X := by
    apply (LinearMap.nonneg_iff_isPositive _).mpr
    exact ((LinearMap.nonneg_iff_isPositive _).mp hX).smul_of_nonneg
      (Complex.zero_le_real.mpr hc.le)
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_pow]
  rw [CFC.rpow_eq_cfc_real (ha := hscaled),
    CFC.rpow_eq_cfc_real (ha := hX)]
  change cfc (fun x : ℝ => x ^ y) (c • X) =
    (c ^ y) • cfc (fun x : ℝ => x ^ y) X
  rw [← cfc_comp_smul (R := ℝ) c (fun x : ℝ => x ^ y) X
      (hf := (Real.continuous_rpow_const hy).continuousOn),
    ← cfc_smul (R := ℝ) (c ^ y) (fun x : ℝ => x ^ y) X
      (hf := (Real.continuous_rpow_const hy).continuousOn)]
  apply cfc_congr
  intro x hx
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hX hx
  exact Real.mul_rpow hc.le hx0

private theorem scaledPetzQuasiBounds {A : Sys}
    (alpha : ℝ) (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (rho : DensityMatrix A) (sigma : Operator A) (hsigma : 0 ≤ sigma) :
    (Tr (CFC.rpow ((p : ℂ) • rho.operator) alpha *
      CFC.rpow (((1 - p : ℝ) : ℂ) • sigma) (1 - alpha))).re =
      p ^ alpha * (1 - p) ^ (1 - alpha) *
        petzQuasi alpha rho sigma := by
  rw [rpow_smul_posBounds rho.operator rho.nonneg p alpha hp0 halpha0.le,
    rpow_smul_posBounds sigma hsigma (1 - p) (1 - alpha)
      (sub_pos.mpr hp1) (sub_nonneg.mpr halpha1.le)]
  unfold petzQuasi
  simp only [smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul,
    Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

private theorem audenaertBalanceBounds
    (alpha epsilon q : ℝ) (halpha1 : alpha < 1)
    (hepsilon : 0 < epsilon) (hq : 0 < q) :
    let t := (epsilon / q) ^ (1 / (1 - alpha) : ℝ)
    let p := 1 / (t + 1)
    0 < t ∧ 0 < p ∧ p < 1 ∧
      p ^ alpha * (1 - p) ^ (1 - alpha) * q = p * epsilon ∧
      epsilon / t =
        (q / epsilon ^ alpha) ^ (1 / (1 - alpha) : ℝ) := by
  dsimp only
  let t : ℝ := (epsilon / q) ^ (1 / (1 - alpha) : ℝ)
  have hx : 0 < epsilon / q := div_pos hepsilon hq
  have ht : 0 < t := Real.rpow_pos_of_pos hx _
  have hp : 0 < 1 / (t + 1) := one_div_pos.mpr (by linarith)
  have hp1 : 1 / (t + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have h1mp : 1 - 1 / (t + 1) = t * (1 / (t + 1)) := by
    field_simp
    ring
  have htPower : t ^ (1 - alpha) = epsilon / q := by
    dsimp only [t]
    rw [← Real.rpow_mul hx.le]
    have hne : 1 - alpha ≠ 0 := ne_of_gt (sub_pos.mpr halpha1)
    rw [one_div, inv_mul_cancel₀ hne, Real.rpow_one]
  have hscale :
      (1 / (t + 1)) ^ alpha *
          (1 - 1 / (t + 1)) ^ (1 - alpha) * q =
        (1 / (t + 1)) * epsilon := by
    rw [h1mp, Real.mul_rpow ht.le hp.le]
    calc
      (1 / (t + 1)) ^ alpha *
            (t ^ (1 - alpha) *
              (1 / (t + 1)) ^ (1 - alpha)) * q =
          ((1 / (t + 1)) ^ alpha *
            (1 / (t + 1)) ^ (1 - alpha)) *
              (t ^ (1 - alpha) * q) := by ring
      _ = (1 / (t + 1)) ^ (alpha + (1 - alpha)) *
              (t ^ (1 - alpha) * q) := by rw [Real.rpow_add hp]
      _ = (1 / (t + 1)) * epsilon := by
        rw [show alpha + (1 - alpha) = 1 by ring,
          Real.rpow_one, htPower]
        field_simp
  have hradius :
      epsilon / t =
        (q / epsilon ^ alpha) ^ (1 / (1 - alpha) : ℝ) := by
    have hepspow : 0 < epsilon ^ alpha :=
      Real.rpow_pos_of_pos hepsilon _
    have hrbase : 0 <
        (q / epsilon ^ alpha) ^ (1 / (1 - alpha) : ℝ) :=
      Real.rpow_pos_of_pos (div_pos hq hepspow) _
    apply (Real.rpow_left_inj (div_pos hepsilon ht).le hrbase.le
      (ne_of_gt (sub_pos.mpr halpha1))).mp
    rw [Real.div_rpow hepsilon.le ht.le,
      ← Real.rpow_mul (div_pos hq hepspow).le]
    rw [one_div,
      inv_mul_cancel₀ (ne_of_gt (sub_pos.mpr halpha1)),
      Real.rpow_one, htPower]
    field_simp [hepsilon.ne', hq.ne', hepspow.ne']
    rw [← Real.rpow_add hepsilon]
    convert Real.rpow_one epsilon using 1
    all_goals ring
  exact ⟨ht, hp, hp1, hscale, hradius⟩

private theorem petzLogRadiusBounds
    (alpha epsilon q b : ℝ)
    (halpha1 : alpha < 1) (hepsilon : 0 < epsilon)
    (hq : 0 < q) (hb : 0 < b)
    (hbc : b ≤
      (q / epsilon ^ alpha) ^ (1 / (1 - alpha) : ℝ)) :
    Real.logb 2 q / (alpha - 1) +
        (alpha / (alpha - 1)) * Real.logb 2 (1 / epsilon) ≤
      -Real.logb 2 b := by
  have hepspow : 0 < epsilon ^ alpha :=
    Real.rpow_pos_of_pos hepsilon _
  have hlog := Real.log_le_log hb hbc
  rw [Real.log_rpow (div_pos hq hepspow) _] at hlog
  rw [Real.log_div hq.ne' hepspow.ne',
    Real.log_rpow hepsilon alpha] at hlog
  have hlogInv : Real.log (1 / epsilon) = -Real.log epsilon := by
    rw [one_div, Real.log_inv]
  have hden0 : 1 - alpha ≠ 0 :=
    ne_of_gt (sub_pos.mpr halpha1)
  have haden0 : alpha - 1 ≠ 0 := by linarith
  have hnatural :
      Real.log q / (alpha - 1) +
          (alpha / (alpha - 1)) * Real.log (1 / epsilon) ≤
        -Real.log b := by
    rw [hlogInv]
    convert neg_le_neg hlog using 1
    all_goals field_simp [hden0, haden0]
    all_goals ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [Real.logb]
  calc
    Real.log q / Real.log 2 / (alpha - 1) +
          alpha / (alpha - 1) *
            (Real.log (1 / epsilon) / Real.log 2) =
        (Real.log q / (alpha - 1) +
          alpha / (alpha - 1) * Real.log (1 / epsilon)) /
            Real.log 2 := by ring
    _ ≤ (-Real.log b) / Real.log 2 :=
      (div_le_div_iff_of_pos_right hlog2).mpr hnatural
    _ = -(Real.log b / Real.log 2) := by ring

private theorem betaEpsilon_le_objectivePetzBounds {A : Sys}
    (epsilon : OPT.ProbabilityLevel) (rho : DensityMatrix A)
    (sigma : Operator A) (Q : FeasibleTest epsilon rho) :
    betaEpsilon epsilon rho sigma ≤
      Real.toNNReal (testValue Q.1 sigma) := by
  unfold betaEpsilon
  apply csInf_le
  · exact ⟨0, fun _ _ => bot_le⟩
  · exact ⟨Q, rfl⟩

private theorem binaryNegLog2_antitonePetzBounds :
    Antitone OPT.binaryNegLog2 := by
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
    (by exact_mod_cast (pos_iff_ne_zero.mpr hp))
    (NNReal.coe_le_coe.mpr hpq)

private theorem exists_feasibleTest_petzRadiusBounds {A : Sys}
    (alpha : ℝ) (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (epsilon : OPT.ProbabilityLevel) (hepsilon0 : 0 < epsilon.1)
    (rho : DensityMatrix A) (sigma : Operator A) (hsigma : 0 ≤ sigma)
    (hq : 0 < petzQuasi alpha rho sigma) :
    ∃ Q : Effect A,
      1 - epsilon.1 ≤ testValue Q rho.operator ∧
      testValue Q sigma ≤
        (petzQuasi alpha rho sigma / epsilon.1 ^ alpha) ^
          (1 / (1 - alpha) : ℝ) := by
  let q : ℝ := petzQuasi alpha rho sigma
  let t : ℝ := (epsilon.1 / q) ^ (1 / (1 - alpha) : ℝ)
  let p : ℝ := 1 / (t + 1)
  have hbalance := audenaertBalanceBounds
    alpha epsilon.1 q halpha1 hepsilon0 hq
  change 0 < t ∧ 0 < p ∧ p < 1 ∧
      p ^ alpha * (1 - p) ^ (1 - alpha) * q = p * epsilon.1 ∧
      epsilon.1 / t =
        (q / epsilon.1 ^ alpha) ^ (1 / (1 - alpha) : ℝ) at hbalance
  rcases hbalance with ⟨ht, hp, hp1, hscale, hradius⟩
  obtain ⟨Q, hweighted⟩ := exists_weightedError_le_scaledPetzBounds
    alpha halpha0 halpha1 p hp hp1 rho sigma hsigma
  rw [scaledPetzQuasiBounds alpha halpha0 halpha1
    p hp hp1 rho sigma hsigma] at hweighted
  change p * (1 - testValue Q rho.operator) +
      (1 - p) * testValue Q sigma ≤
        p ^ alpha * (1 - p) ^ (1 - alpha) * q at hweighted
  rw [hscale] at hweighted
  have htypeI : 0 ≤ 1 - testValue Q rho.operator := by
    have hQle := Internal.testValue_le_traceComparisonBounds
      Q rho.operator rho.nonneg
    rw [rho.trace_one] at hQle
    norm_num at hQle
    linarith
  have htypeII : 0 ≤ testValue Q sigma :=
    Internal.testValue_nonnegComparisonBounds Q sigma hsigma
  have hfirst : 0 ≤ p * (1 - testValue Q rho.operator) :=
    mul_nonneg hp.le htypeI
  have hsecond : 0 ≤ (1 - p) * testValue Q sigma :=
    mul_nonneg (sub_nonneg.mpr hp1.le) htypeII
  have hfirst_le :
      p * (1 - testValue Q rho.operator) ≤ p * epsilon.1 := by
    linarith
  have htypeI_le : 1 - testValue Q rho.operator ≤ epsilon.1 :=
    by nlinarith
  have hfeasible : 1 - epsilon.1 ≤ testValue Q rho.operator := by
    linarith
  have hsecond_le :
      (1 - p) * testValue Q sigma ≤ p * epsilon.1 := by
    linarith
  have h1mp : 1 - p = t * p := by
    dsimp only [p]
    field_simp
    ring
  have hcancel :
      p * (t * testValue Q sigma) ≤ p * epsilon.1 := by
    calc
      p * (t * testValue Q sigma) =
          (1 - p) * testValue Q sigma := by rw [h1mp]; ring
      _ ≤ p * epsilon.1 := hsecond_le
  have htb : t * testValue Q sigma ≤ epsilon.1 := by
    nlinarith
  have htypeII_le : testValue Q sigma ≤ epsilon.1 / t := by
    apply (le_div_iff₀ ht).mpr
    nlinarith
  refine ⟨Q, hfeasible, ?_⟩
  change testValue Q sigma ≤
    (q / epsilon.1 ^ alpha) ^ (1 / (1 - alpha) : ℝ)
  rw [← hradius]
  exact htypeII_le

private theorem hypothesisTestingDiv_eq_top_of_petzQuasi_eq_zeroBounds
    {A : Sys} (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (epsilon : OPT.ProbabilityLevel)
    (rho : DensityMatrix A) (sigma : Operator A) (hsigma : 0 ≤ sigma)
    (hq : petzQuasi alpha rho sigma = 0) :
    hypothesisTestingDiv epsilon rho sigma = ⊤ := by
  obtain ⟨Q, hweighted⟩ := exists_weightedError_le_scaledPetzBounds
    alpha halpha0 halpha1 (1 / 2 : ℝ) (by norm_num) (by norm_num)
      rho sigma hsigma
  rw [scaledPetzQuasiBounds alpha halpha0 halpha1
    (1 / 2 : ℝ) (by norm_num) (by norm_num) rho sigma hsigma] at hweighted
  simp only [hq, mul_zero] at hweighted
  have htypeI : 0 ≤ 1 - testValue Q rho.operator := by
    have hQle := Internal.testValue_le_traceComparisonBounds
      Q rho.operator rho.nonneg
    rw [rho.trace_one] at hQle
    norm_num at hQle
    linarith
  have htypeII : 0 ≤ testValue Q sigma :=
    Internal.testValue_nonnegComparisonBounds Q sigma hsigma
  have hfirst :
      0 ≤ (1 / 2 : ℝ) * (1 - testValue Q rho.operator) :=
    mul_nonneg (by norm_num) htypeI
  have hsecond :
      0 ≤ (1 - (1 / 2 : ℝ)) * testValue Q sigma :=
    mul_nonneg (by norm_num) htypeII
  have htypeIzero : 1 - testValue Q rho.operator = 0 := by
    nlinarith
  have htypeIIzero : testValue Q sigma = 0 := by
    nlinarith
  have hfeasible : 1 - epsilon.1 ≤ testValue Q rho.operator := by
    have hepsilon_nonneg := epsilon.2.1
    nlinarith
  have hbeta_le := betaEpsilon_le_objectivePetzBounds
    epsilon rho sigma (⟨Q, hfeasible⟩ : FeasibleTest epsilon rho)
  rw [htypeIIzero] at hbeta_le
  have hbeta : betaEpsilon epsilon rho sigma = 0 :=
    le_antisymm (by simpa using hbeta_le) bot_le
  unfold hypothesisTestingDiv
  rw [hbeta, OPT.binaryNegLog2_zero]

/-- The totalized Petz trace-power quasi-entropy is nonnegative. -/
theorem petzQuasi_nonneg_totalized {A : Sys} (alpha : ℝ)
    (rho : DensityMatrix A) (sigma : Operator A) :
    0 ≤ petzQuasi alpha rho sigma := by
  have htrace := NativeMeasuredRelativeEntropy.trace_comp_nonneg
    (CFC.rpow rho.operator alpha) (CFC.rpow sigma (1 - alpha))
    CFC.rpow_nonneg CFC.rpow_nonneg
  unfold petzQuasi
  simpa only [Module.End.mul_eq_comp] using htrace.1

/-- The Petz trace-power quasi-entropy is nonnegative for orders in `(0,1)`
and an arbitrary positive semidefinite right-hand operator.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:7037--7052` (`prop:ineq-hypo-renyi`), for the nonnegative
trace-power term used in the hypothesis-testing comparison.

Source-facing version keeping the domain \(0<\alpha<1\), \(\sigma\geq0\) of the source in the
statement. The unconditional version is `petzQuasi_nonneg_totalized`. -/
theorem petzQuasi_nonneg {A : Sys} (alpha : ℝ)
    (_halpha0 : 0 < alpha) (_halpha1 : alpha < 1)
    (rho : DensityMatrix A) (sigma : Operator A)
    (_hsigma : 0 ≤ sigma) :
    0 ≤ petzQuasi alpha rho sigma := by
  exact petzQuasi_nonneg_totalized alpha rho sigma

/-- The Petz Rényi divergence at order `alpha ∈ (0,1)`, with the standard
hypothesis-testing penalty, is bounded by the hypothesis-testing divergence.

The proof applies the Audenaert--Chernoff spectral inequality directly to a
weighted binary test.  It does not pass through a Petz data-processing
theorem.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:7037--7101` (`prop:ineq-hypo-renyi`,
`eq-hypo_testing_lower`). -/
theorem petzRenyiDivBits_le_hypothesisTestingDiv
    {A : Sys} (alpha : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (epsilon : OPT.ProbabilityLevel)
    (hepsilon0 : 0 < epsilon.1)
    (rho : DensityMatrix A) (sigma : Operator A)
    (hsigma : 0 ≤ sigma) :
    petzRenyiDivBits alpha rho sigma +
        (((alpha / (alpha - 1)) *
          Real.logb 2 (1 / epsilon.1) : ℝ) : EReal) ≤
      hypothesisTestingDiv epsilon rho sigma := by
  have hqnonneg := petzQuasi_nonneg
    alpha halpha0 halpha1 rho sigma hsigma
  by_cases hqzero : petzQuasi alpha rho sigma = 0
  · have htop :=
      hypothesisTestingDiv_eq_top_of_petzQuasi_eq_zeroBounds
        alpha halpha0 halpha1 epsilon rho sigma hsigma hqzero
    rw [petzRenyiDivBits, if_pos hqzero, EReal.top_add_coe, htop]
  · have hqpos : 0 < petzQuasi alpha rho sigma :=
      lt_of_le_of_ne hqnonneg (Ne.symm hqzero)
    obtain ⟨Q, hQfeasible, hQradius⟩ :=
      exists_feasibleTest_petzRadiusBounds
        alpha halpha0 halpha1 epsilon hepsilon0
          rho sigma hsigma hqpos
    let b : ℝ := testValue Q sigma
    have hbnonneg : 0 ≤ b :=
      Internal.testValue_nonnegComparisonBounds Q sigma hsigma
    have hbeta_le := betaEpsilon_le_objectivePetzBounds
      epsilon rho sigma
        (⟨Q, hQfeasible⟩ : FeasibleTest epsilon rho)
    change betaEpsilon epsilon rho sigma ≤ Real.toNNReal b at hbeta_le
    by_cases hbzero : b = 0
    · rw [hbzero] at hbeta_le
      have hbeta : betaEpsilon epsilon rho sigma = 0 :=
        le_antisymm (by simpa using hbeta_le) bot_le
      have htop : hypothesisTestingDiv epsilon rho sigma = ⊤ := by
        unfold hypothesisTestingDiv
        rw [hbeta, OPT.binaryNegLog2_zero]
      rw [htop]
      exact le_top
    · have hbpos : 0 < b :=
        lt_of_le_of_ne hbnonneg (Ne.symm hbzero)
      have hscalar := petzLogRadiusBounds
        alpha epsilon.1 (petzQuasi alpha rho sigma) b
          halpha1 hepsilon0 hqpos hbpos (by simpa only [b] using hQradius)
      have hanti := binaryNegLog2_antitonePetzBounds hbeta_le
      have hbNNzero : Real.toNNReal b ≠ 0 := by
        rw [ne_eq, Real.toNNReal_eq_zero]
        exact not_le.mpr hbpos
      have hbBinary :
          OPT.binaryNegLog2 (Real.toNNReal b) =
            ((-Real.logb 2 b : ℝ) : EReal) := by
        unfold OPT.binaryNegLog2
        rw [if_neg hbNNzero, Real.coe_toNNReal b hbpos.le]
      have hhyp :
          ((-Real.logb 2 b : ℝ) : EReal) ≤
            hypothesisTestingDiv epsilon rho sigma := by
        rw [← hbBinary]
        simpa only [hypothesisTestingDiv] using hanti
      rw [petzRenyiDivBits, if_neg hqzero, ← EReal.coe_add]
      exact (EReal.coe_le_coe_iff.mpr hscalar).trans hhyp


end NativeHypothesisTesting
end QuantumModel
