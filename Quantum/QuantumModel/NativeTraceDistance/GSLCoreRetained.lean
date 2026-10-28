/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.NativeTraceNormCore.GSLCore
import Quantum.QuantumModel.NativeFacade.GSLCore
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Quantum.OperationalProbabilistic.Framework.EffectNorms.GSLCore
import Quantum.OperationalProbabilistic.Framework.ExactCompression.GSLCore
import Quantum.OperationalProbabilistic.Framework.TransformationNorms.GSLCore
import Quantum.QuantumModel.NativeTraceDistance.GSLCore

/-!
# Native trace distance and the operational-norm dictionary

This file identifies the operational norm of the difference of two canonical
quantum preparations with the trace norm of the density-operator difference.
It also proves the contraction of trace distance under native CPTP superoperators
and the trace-norm estimates used for the Powers--Størmer inequality.
-/

noncomputable section

namespace QuantumModel

open CategoryTheory
open QuantumState

namespace NativeTraceDistance

/-- The trace distance `D(rho,sigma) = (1/2) * ‖rho-sigma‖₁`. -/
def traceDistance {A : Sys} (rho sigma : DensityMatrix A) : ℝ :=
  (2 : ℝ)⁻¹ * traceNorm (rho.operator - sigma.operator)

private theorem re_trace_comp_nonneg {A : Sys} (P Q : Operator A)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    0 ≤ (Tr (P.comp Q)).re := by
  let S : Operator A := CFC.sqrt P
  have hSadj : LinearMap.adjoint S = S := by
    rw [← LinearMap.star_eq_adjoint]
    exact (CFC.sqrt_nonneg P).isSelfAdjoint
  have hSsq : S.comp S = P := by
    exact CFC.sqrt_mul_sqrt_self P hP
  have hQpos : Q.IsPositive :=
    (LinearMap.nonneg_iff_isPositive Q).mp hQ
  have hconj :
      ((LinearMap.adjoint S).comp (Q.comp S)).IsPositive :=
    hQpos.adjoint_conj S
  have htrace :
      Tr (P.comp Q) =
        Tr ((LinearMap.adjoint S).comp (Q.comp S)) := by
    calc
      Tr (P.comp Q) = Tr (Q.comp P) :=
        (LinearMap.trace_comp_comm' P Q).symm
      _ = Tr (Q.comp (S.comp S)) := by rw [hSsq]
      _ = Tr ((Q.comp S).comp S) := by rw [LinearMap.comp_assoc]
      _ = Tr (S.comp (Q.comp S)) :=
        LinearMap.trace_comp_comm' S (Q.comp S)
      _ = Tr ((LinearMap.adjoint S).comp (Q.comp S)) := by rw [hSadj]
  rw [htrace]
  exact (Complex.nonneg_iff.mp hconj.trace_nonneg).1

private def supportProjection {A : Sys} (P : Operator A) : Operator A :=
  (LinearMap.range P).starProjection

private theorem supportProjection_isSymmetricProjection {A : Sys}
    (P : Operator A) :
    (supportProjection P).IsSymmetricProjection := by
  exact Submodule.isSymmetricProjection_starProjection (LinearMap.range P)

private theorem id_isSymmetricProjection {A : Sys} :
    (LinearMap.id : Operator A).IsSymmetricProjection := by
  constructor
  · rw [IsIdempotentElem]
    ext x
    rfl
  · intro x y
    rfl

private theorem supportProjection_povmElement {A : Sys} (P : Operator A) :
    NativeNoCloning.POVMElement (supportProjection P) := by
  constructor
  · exact (LinearMap.nonneg_iff_isPositive _).mpr
      (supportProjection_isSymmetricProjection P).isPositive
  · exact ((supportProjection_isSymmetricProjection P).le_iff_range_le_range
      id_isSymmetricProjection).mpr fun x _ => ⟨x, rfl⟩

private theorem supportProjection_comp_self {A : Sys} (P : Operator A) :
    (supportProjection P).comp P = P := by
  apply LinearMap.ext
  intro x
  exact Submodule.starProjection_eq_self_iff.mpr ⟨x, rfl⟩

private theorem supportProjection_comp_eq_zero {A : Sys}
    (P Q : Operator A) (hP : P.IsSymmetric) (hPQ : P.comp Q = 0) :
    (supportProjection P).comp Q = 0 := by
  apply LinearMap.ext
  intro x
  apply (Submodule.starProjection_apply_eq_zero_iff
    (K := LinearMap.range P)).mpr
  intro y hy
  rcases hy with ⟨z, rfl⟩
  rw [hP]
  have hzero : P (Q x) = 0 := LinearMap.congr_fun hPQ x
  rw [hzero, inner_zero_right]

private theorem positiveSupport_pairing {A : Sys} (X : Operator A)
    (hX : IsSelfAdjoint X) :
    (supportProjection X⁺).comp X = X⁺ := by
  let P : Operator A := X⁺
  let N : Operator A := X⁻
  have hPpos : 0 ≤ P := CFC.posPart_nonneg X
  have hPsymm : P.IsSymmetric :=
    ((LinearMap.nonneg_iff_isPositive P).mp hPpos).isSymmetric
  have hPN : P.comp N = 0 := by
    change X⁺ * X⁻ = 0
    exact CFC.posPart_mul_negPart X
  have hself : (supportProjection P).comp P = P :=
    supportProjection_comp_self P
  have hzero : (supportProjection P).comp N = 0 :=
    supportProjection_comp_eq_zero P N hPsymm hPN
  calc
    (supportProjection X⁺).comp X =
        (supportProjection P).comp (P - N) := by
      rw [CFC.posPart_sub_negPart X hX]
    _ = P := by rw [LinearMap.comp_sub, hself, hzero, sub_zero]
    _ = X⁺ := rfl

private theorem negativeSupport_pairing {A : Sys} (X : Operator A)
    (hX : IsSelfAdjoint X) :
    (supportProjection X⁻).comp X = -X⁻ := by
  let P : Operator A := X⁺
  let N : Operator A := X⁻
  have hNpos : 0 ≤ N := CFC.negPart_nonneg X
  have hNsymm : N.IsSymmetric :=
    ((LinearMap.nonneg_iff_isPositive N).mp hNpos).isSymmetric
  have hNP : N.comp P = 0 := by
    change X⁻ * X⁺ = 0
    exact CFC.negPart_mul_posPart X
  have hself : (supportProjection N).comp N = N :=
    supportProjection_comp_self N
  have hzero : (supportProjection N).comp P = 0 :=
    supportProjection_comp_eq_zero N P hNsymm hNP
  calc
    (supportProjection X⁻).comp X =
        (supportProjection N).comp (P - N) := by
      rw [CFC.posPart_sub_negPart X hX]
    _ = -N := by rw [LinearMap.comp_sub, hzero, hself, zero_sub]
    _ = -X⁻ := rfl

private theorem traceNorm_eq_posPart_add_negPart {A : Sys}
    (X : Operator A) (hX : IsSelfAdjoint X) :
    traceNorm X = (Tr X⁺).re + (Tr X⁻).re := by
  rw [traceNorm, ← CFC.posPart_add_negPart X hX, map_add]
  rfl

private theorem density_sub_isSelfAdjoint {A : Sys}
    (rho sigma : DensityMatrix A) :
    IsSelfAdjoint (rho.operator - sigma.operator) := by
  exact ((LinearMap.nonneg_iff_isPositive _).mp rho.nonneg).isSelfAdjoint.sub
    ((LinearMap.nonneg_iff_isPositive _).mp sigma.nonneg).isSelfAdjoint

private theorem povm_pairing_bounds {A : Sys} (E X : Operator A)
    (hE : NativeNoCloning.POVMElement E) (hX : IsSelfAdjoint X) :
    -(Tr X⁻).re ≤ (Tr (E.comp X)).re ∧
      (Tr (E.comp X)).re ≤ (Tr X⁺).re := by
  let P : Operator A := X⁺
  let N : Operator A := X⁻
  have hP : 0 ≤ P := CFC.posPart_nonneg X
  have hN : 0 ≤ N := CFC.negPart_nonneg X
  have hEc : 0 ≤ (LinearMap.id : Operator A) - E :=
    sub_nonneg.mpr hE.2
  have hEP : 0 ≤ (Tr (E.comp P)).re :=
    re_trace_comp_nonneg E P hE.1 hP
  have hEN : 0 ≤ (Tr (E.comp N)).re :=
    re_trace_comp_nonneg E N hE.1 hN
  have hEcP : 0 ≤
      (Tr (((LinearMap.id : Operator A) - E).comp P)).re :=
    re_trace_comp_nonneg ((LinearMap.id : Operator A) - E) P hEc hP
  have hEcN : 0 ≤
      (Tr (((LinearMap.id : Operator A) - E).comp N)).re :=
    re_trace_comp_nonneg ((LinearMap.id : Operator A) - E) N hEc hN
  have hEPle : (Tr (E.comp P)).re ≤ (Tr P).re := by
    rw [LinearMap.sub_comp, LinearMap.id_comp, map_sub, Complex.sub_re] at hEcP
    linarith
  have hENle : (Tr (E.comp N)).re ≤ (Tr N).re := by
    rw [LinearMap.sub_comp, LinearMap.id_comp, map_sub, Complex.sub_re] at hEcN
    linarith
  have hpair :
      (Tr (E.comp X)).re =
        (Tr (E.comp P)).re - (Tr (E.comp N)).re := by
    have hdecomp : P - N = X := CFC.posPart_sub_negPart X hX
    rw [← hdecomp, LinearMap.comp_sub, map_sub, Complex.sub_re]
  constructor <;> rw [hpair]
  · change -(Tr N).re ≤ _
    linarith
  · change _ ≤ (Tr P).re
    linarith

private theorem positiveSupport_pairing_re {A : Sys} (X : Operator A)
    (hX : IsSelfAdjoint X) :
    (Tr ((supportProjection X⁺).comp X)).re = (Tr X⁺).re := by
  rw [positiveSupport_pairing X hX]

private theorem negativeSupport_pairing_re {A : Sys} (X : Operator A)
    (hX : IsSelfAdjoint X) :
    (Tr ((supportProjection X⁻).comp X)).re = -(Tr X⁻).re := by
  rw [negativeSupport_pairing X hX, map_neg]
  rfl

private theorem bornProbability_sub_eq_trace {A : Sys} (E : Operator A)
    (rho sigma : DensityMatrix A) :
    NativeNoCloning.bornProbability E rho -
        NativeNoCloning.bornProbability E sigma =
      (Tr (E.comp (rho.operator - sigma.operator))).re := by
  simp only [NativeNoCloning.bornProbability, LinearMap.comp_sub, map_sub,
    Complex.sub_re]

private theorem operational_sub_eval_eq_prob_sub {A : Sys}
    (rho sigma : DensityMatrix A) (a : OPT.Effect (Sys := Sys) A)
    (ha : OPT.IsEffect (Sys := Sys) a) :
    OPT.stateOperationalQuotientEval (Sys := Sys) a ha
        ((OPT.operationalStateClass (Sys := Sys) rho.toState
            rho.toState_isNormalizedState.1 -
          OPT.operationalStateClass (Sys := Sys) sigma.toState
            sigma.toState_isNormalizedState.1 :
          OPT.OperationalStateSpaceReal (Sys := Sys) A) :
          OPT.StateOperationalQuotient (Sys := Sys) A) =
      OPT.prob (Sys := Sys) a rho.toState -
        OPT.prob (Sys := Sys) a sigma.toState := by
  change OPT.stateOperationalQuotientEval (Sys := Sys) a ha
      (OPT.stateOperationalClass (Sys := Sys) A rho.toState -
        OPT.stateOperationalClass (Sys := Sys) A sigma.toState) = _
  rw [map_sub, OPT.stateOperationalQuotientEval_mk,
    OPT.stateOperationalQuotientEval_mk]

/-- The evaluation of the canonical difference class on an effect with Born-rule
representative `E` is the real trace pairing of `E` with the density difference. -/
private theorem operational_sub_eval_eq_trace {A : Sys}
    (rho sigma : DensityMatrix A) (a : OPT.Effect (Sys := Sys) A)
    (ha : OPT.IsEffect (Sys := Sys) a) (E : Operator A)
    (hborn : ∀ rho : DensityMatrix A,
      OPT.prob (Sys := Sys) a rho.toState =
        NativeNoCloning.bornProbability E rho) :
    OPT.stateOperationalQuotientEval (Sys := Sys) a ha
        ((OPT.operationalStateClass (Sys := Sys) rho.toState
            rho.toState_isNormalizedState.1 -
          OPT.operationalStateClass (Sys := Sys) sigma.toState
            sigma.toState_isNormalizedState.1 :
          OPT.OperationalStateSpaceReal (Sys := Sys) A) :
          OPT.StateOperationalQuotient (Sys := Sys) A) =
      (Tr (E.comp (rho.operator - sigma.operator))).re := by
  rw [operational_sub_eval_eq_prob_sub rho sigma a ha, hborn rho, hborn sigma]
  exact bornProbability_sub_eq_trace E rho sigma

/-- The operational norm of the difference of two canonical quantum
preparations is exactly the trace norm of their density-operator difference.
There is no factor `1/2` in this dictionary. -/
theorem operationalStateNorm_sub_eq_traceNorm {A : Sys}
    (rho sigma : DensityMatrix A) :
    OPT.operationalStateNorm (Sys := Sys)
      (OPT.operationalStateClass (Sys := Sys) rho.toState
          rho.toState_isNormalizedState.1 -
        OPT.operationalStateClass (Sys := Sys) sigma.toState
          sigma.toState_isNormalizedState.1) =
      traceNorm (rho.operator - sigma.operator) := by
  -- Local instances short-cut the repeated real-algebra searches on `Operator A`.
  letI : Algebra ℝ (Operator A) := inferInstance
  letI : Module ℝ (Operator A) := inferInstance
  let delta : OPT.OperationalStateSpaceReal (Sys := Sys) A :=
    OPT.operationalStateClass (Sys := Sys) rho.toState
        rho.toState_isNormalizedState.1 -
      OPT.operationalStateClass (Sys := Sys) sigma.toState
        sigma.toState_isNormalizedState.1
  let X : Operator A := rho.operator - sigma.operator
  let S : Set ℝ := OPT.operationalStateNormEvalRange (Sys := Sys)
    (delta : OPT.StateOperationalQuotient (Sys := Sys) A)
  have hX : IsSelfAdjoint X := density_sub_isSelfAdjoint rho sigma
  have hsup_le : sSup S ≤ (Tr X⁺).re := by
    refine csSup_le (OPT.operationalStateNorm_evalRange_nonempty
      (Sys := Sys) delta) ?_
    rintro y ⟨a, _ha_univ, rfl⟩
    rcases exists_povmElement_of_effect a.1 a.2.1 with ⟨E, hE, hborn⟩
    exact (operational_sub_eval_eq_trace rho sigma a.1 a.2.1 E hborn).le.trans
      (povm_pairing_bounds E X hE hX).2
  have hpos_mem : (Tr X⁺).re ∈ S := by
    rcases exists_effect_of_povmElement (supportProjection X⁺)
      (supportProjection_povmElement X⁺) with ⟨a, ha, hborn⟩
    exact ⟨⟨a, OPT.boundedEffect_of_isEffect (Sys := Sys) ha⟩, Set.mem_univ _,
      (operational_sub_eval_eq_trace rho sigma a ha _ hborn).trans
        (positiveSupport_pairing_re X hX)⟩
  have hinf_ge : -(Tr X⁻).re ≤ sInf S := by
    refine le_csInf (OPT.operationalStateNorm_evalRange_nonempty
      (Sys := Sys) delta) ?_
    rintro y ⟨a, _ha_univ, rfl⟩
    rcases exists_povmElement_of_effect a.1 a.2.1 with ⟨E, hE, hborn⟩
    exact (povm_pairing_bounds E X hE hX).1.trans
      (operational_sub_eval_eq_trace rho sigma a.1 a.2.1 E hborn).ge
  have hneg_mem : -(Tr X⁻).re ∈ S := by
    rcases exists_effect_of_povmElement (supportProjection X⁻)
      (supportProjection_povmElement X⁻) with ⟨a, ha, hborn⟩
    exact ⟨⟨a, OPT.boundedEffect_of_isEffect (Sys := Sys) ha⟩, Set.mem_univ _,
      (operational_sub_eval_eq_trace rho sigma a ha _ hborn).trans
        (negativeSupport_pairing_re X hX)⟩
  have hsup : sSup S = (Tr X⁺).re :=
    le_antisymm hsup_le (le_csSup (OPT.operationalStateNorm_evalRange_bddAbove
      (Sys := Sys) delta) hpos_mem)
  have hinf : sInf S = -(Tr X⁻).re :=
    le_antisymm (csInf_le (OPT.operationalStateNorm_evalRange_bddBelow
      (Sys := Sys) delta) hneg_mem) hinf_ge
  change sSup S - sInf S = traceNorm X
  rw [hsup, hinf, traceNorm_eq_posPart_add_negPart X hX]
  ring

/-- On a positive operator, the trace norm is its ordinary trace. -/
theorem traceNorm_of_nonneg {A : Sys} (X : Operator A) (hX : 0 ≤ X) :
    traceNorm X = (Tr X).re := by
  unfold traceNorm
  rw [CFC.abs_of_nonneg X hX]

/-- Trace distance between channel outputs is no larger than the input trace
distance.  The public statement uses only native density matrices and a
native CPTP superoperator; the proof transfers the existing operational-norm
contraction to the trace norm. -/
theorem traceDistance_channelApply_le {A B : Sys}
    (rho sigma : DensityMatrix A)
    (Phi : NativeNoCloning.Superoperator A B) (hPhi : IsChannel Phi) :
    traceDistance (rho.channelApply Phi hPhi)
        (sigma.channelApply Phi hPhi) ≤
      traceDistance rho sigma := by
  let delta : OPT.OperationalStateSpaceReal (Sys := Sys) A :=
    OPT.operationalStateClass (Sys := Sys) rho.toState
        rho.toState_isNormalizedState.1 -
      OPT.operationalStateClass (Sys := Sys) sigma.toState
        sigma.toState_isNormalizedState.1
  have hmono := OPT.operationalStateNorm_channel_apply_le
    (Sys := Sys) hPhi delta
  rw [OPT.operationalTransformationStateMap_mk] at hmono
  rw [map_sub] at hmono
  rw [OPT.transformationStateMap_mk, OPT.transformationStateMap_mk] at hmono
  unfold traceDistance
  rw [← operationalStateNorm_sub_eq_traceNorm
      (rho.channelApply Phi hPhi) (sigma.channelApply Phi hPhi),
    ← operationalStateNorm_sub_eq_traceNorm rho sigma]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  simpa only [DensityMatrix.channelApply_toState] using hmono

/-- Raw-operator form of native trace-distance contraction under a CPTP
superoperator. -/
theorem traceDistance_contracts {A B : Sys}
    (rho sigma : DensityMatrix A)
    (Phi : NativeNoCloning.Superoperator A B) (hPhi : IsChannel Phi) :
    (2 : ℝ)⁻¹ * traceNorm (Phi rho.operator - Phi sigma.operator) ≤
      (2 : ℝ)⁻¹ * traceNorm (rho.operator - sigma.operator) := by
  simpa [traceDistance] using
    traceDistance_channelApply_le rho sigma Phi hPhi

private theorem abs_apply_norm {A : Sys} (X : Operator A)
    (x : Space A) : ‖CFC.abs X x‖ = ‖X x‖ := by
  let H : Operator A := CFC.abs X
  have hH : H.IsPositive :=
    (LinearMap.nonneg_iff_isPositive _).mp (CFC.abs_nonneg X)
  have hsq : H.comp H = (LinearMap.adjoint X).comp X := by
    simpa [H, LinearMap.star_eq_adjoint] using CFC.abs_mul_abs X
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    @InnerProductSpace.norm_sq_eq_re_inner ℂ (Space A) _ _ _ (H x),
    @InnerProductSpace.norm_sq_eq_re_inner ℂ (Space A) _ _ _ (X x)]
  congr 1
  calc
    inner ℂ (H x) (H x) = inner ℂ x (H (H x)) :=
      hH.isSymmetric x (H x)
    _ = inner ℂ x ((LinearMap.adjoint X) (X x)) := by
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, hsq]
    _ = inner ℂ (X x) (X x) := LinearMap.adjoint_inner_right X x (X x)

/-- Finite-dimensional polar decomposition with a unitary polar factor. -/
private theorem exists_polar_unitary {A : Sys} (X : Operator A) :
    ∃ U : Space A ≃ₗᵢ[ℂ] Space A,
      X = U.toLinearIsometry.toLinearMap.comp (CFC.abs X) := by
  let H : Operator A := CFC.abs X
  obtain ⟨R, hR⟩ := H.rangeRestrict.exists_rightInverse_of_surjective
    H.range_rangeRestrict
  let L : LinearMap.range H →ₗ[ℂ] Space A := X.comp R
  have hLnorm : ∀ s : LinearMap.range H, ‖L s‖ = ‖s‖ := by
    intro s
    have hs : H (R s) = s := by
      have hs' : H.rangeRestrict (R s) = s := by
        simpa using LinearMap.congr_fun hR s
      exact congrArg Subtype.val hs'
    change ‖X (R s)‖ = ‖(s : Space A)‖
    rw [← abs_apply_norm X (R s), show CFC.abs X = H by rfl, hs]
  let LI : LinearMap.range H →ₗᵢ[ℂ] Space A :=
    { toLinearMap := L
      norm_map' := hLnorm }
  let Uiso : Space A →ₗᵢ[ℂ] Space A := LI.extend
  let U : Space A ≃ₗᵢ[ℂ] Space A :=
    LinearIsometryEquiv.ofSurjective Uiso
      (LinearMap.surjective_of_injective Uiso.injective)
  refine ⟨U, ?_⟩
  apply LinearMap.ext
  intro x
  let s : LinearMap.range H := H.rangeRestrict x
  have hUs : U s = LI s := by
    change Uiso s = LI s
    exact LinearIsometry.extend_apply LI s
  have hHR : H (R s) = H x := by
    have hs' : H.rangeRestrict (R s) = s := by
      simpa using LinearMap.congr_fun hR s
    exact (congrArg Subtype.val hs').trans rfl
  have hXR : X (R s) = X x := by
    have hzH : H (R s - x) = 0 := by
      rw [map_sub, hHR, sub_self]
    have hnormzero : ‖X (R s - x)‖ = 0 := by
      rw [← abs_apply_norm X (R s - x), show CFC.abs X = H by rfl,
        hzH, norm_zero]
    have hzX : X (R s - x) = 0 := norm_eq_zero.mp hnormzero
    rw [map_sub, sub_eq_zero] at hzX
    exact hzX
  change X x = U (H x)
  symm
  calc
    U (H x) = U (s : Space A) := rfl
    _ = LI s := hUs
    _ = L s := rfl
    _ = X (R s) := rfl
    _ = X x := hXR

private theorem re_trace_comp_le {A : Sys} (K X : Operator A) :
    (Tr (K.comp X)).re ≤ ‖K.toContinuousLinearMap‖ * traceNorm X := by
  obtain ⟨U, hX⟩ := exists_polar_unitary X
  let H : Operator A := CFC.abs X
  have hHpos : H.IsPositive :=
    (LinearMap.nonneg_iff_isPositive _).mp (CFC.abs_nonneg X)
  have hHsym : H.IsSymmetric := hHpos.isSymmetric
  let b := hHsym.eigenvectorBasis
    (show Module.finrank ℂ (Space A) = Module.finrank ℂ (Space A) by rfl)
  let s := hHsym.eigenvalues
    (show Module.finrank ℂ (Space A) = Module.finrank ℂ (Space A) by rfl)
  have hs_nonneg : ∀ i, 0 ≤ s i := by
    intro i
    exact hHpos.nonneg_eigenvalues rfl i
  have htrace : traceNorm X = ∑ i, s i := by
    unfold traceNorm
    change (Tr H).re = ∑ i, s i
    exact hHsym.re_trace_eq_sum_eigenvalues rfl
  have hterm : ∀ i, (inner ℂ (b i) (K (U (H (b i))))).re ≤
      ‖K.toContinuousLinearMap‖ * s i := by
    intro i
    have hHb : H (b i) = (s i : ℂ) • b i := by
      exact hHsym.apply_eigenvectorBasis rfl i
    calc
      (inner ℂ (b i) (K (U (H (b i))))).re ≤
          ‖inner ℂ (b i) (K (U (H (b i))))‖ := Complex.re_le_norm _
      _ ≤ ‖b i‖ * ‖K (U (H (b i)))‖ := norm_inner_le_norm _ _
      _ = ‖K (U (H (b i)))‖ := by rw [b.norm_eq_one, one_mul]
      _ ≤ ‖K.toContinuousLinearMap‖ * ‖U (H (b i))‖ :=
        K.toContinuousLinearMap.le_opNorm _
      _ = ‖K.toContinuousLinearMap‖ * s i := by
        rw [U.norm_map, hHb, norm_smul, b.norm_eq_one, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hs_nonneg i)]
  calc
    (Tr (K.comp X)).re =
        (Tr (K.comp
          (U.toLinearIsometry.toLinearMap.comp (CFC.abs X)))).re := by rw [← hX]
    _ = ∑ i, (inner ℂ (b i) (K (U (H (b i))))).re := by
      rw [LinearMap.trace_eq_sum_inner _ b]
      simp [LinearMap.comp_apply, H]
    _ ≤ ∑ i, ‖K.toContinuousLinearMap‖ * s i :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = ‖K.toContinuousLinearMap‖ * traceNorm X := by
      rw [htrace, Finset.mul_sum]

private theorem exists_traceNorm_eq_re_trace_polar {A : Sys} (X : Operator A) :
    ∃ U : Space A ≃ₗᵢ[ℂ] Space A,
      traceNorm X = (Tr ((LinearMap.adjoint U.toLinearMap).comp X)).re := by
  obtain ⟨U, hX⟩ := exists_polar_unitary X
  refine ⟨U, ?_⟩
  have hunit : U.symm.toLinearMap.comp U.toLinearIsometry.toLinearMap =
      LinearMap.id := by
    apply LinearMap.ext
    intro x
    simp
  have hcomp : (LinearMap.adjoint U.toLinearMap).comp X = CFC.abs X := by
    conv_lhs => rw [hX]
    rw [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm,
      ← LinearMap.comp_assoc, hunit, LinearMap.id_comp]
  unfold traceNorm
  rw [hcomp]

/-- Polar attainment and the trace-duality upper bound for the finite trace
norm. -/
theorem traceNorm_unitary_duality {A : Sys} (X : Operator A) :
    (∃ U : EnvironmentUnitary A,
      traceNorm X =
        (Tr ((LinearMap.adjoint U.toLinearMap).comp X)).re) ∧
    ∀ K : Operator A, ‖K.toContinuousLinearMap‖ ≤ 1 →
      (Tr (K.comp X)).re ≤ traceNorm X := by
  refine ⟨exists_traceNorm_eq_re_trace_polar X, ?_⟩
  intro K hK
  calc
    (Tr (K.comp X)).re ≤
        ‖K.toContinuousLinearMap‖ * traceNorm X :=
      re_trace_comp_le K X
    _ ≤ 1 * traceNorm X :=
      mul_le_mul_of_nonneg_right hK (traceNorm_nonneg X)
    _ = traceNorm X := one_mul _

/-! ## Powers--Størmer square-root estimate -/

/-- Rectangular operator/trace-norm Hölder inequality.  The middle factor is
square, while the two outer maps may connect different finite QI spaces. -/
theorem traceNorm_comp_comp_le {A B : Sys}
    (L : Space A →ₗ[ℂ] Space B) (X : Operator A)
    (R : Space B →ₗ[ℂ] Space A) :
    traceNorm ((L.comp X).comp R) ≤
      ‖L.toContinuousLinearMap‖ * traceNorm X *
        ‖R.toContinuousLinearMap‖ := by
  letI : Nontrivial (Space B) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by simpa using B.dim_pos)
  let Y : Operator B := (L.comp X).comp R
  obtain ⟨U, hpolar⟩ := exists_traceNorm_eq_re_trace_polar Y
  let Uadj : Operator B := LinearMap.adjoint U.toLinearMap
  let K : Operator A := R.comp (Uadj.comp L)
  have hUnorm : ‖Uadj.toContinuousLinearMap‖ = 1 := by
    rw [show Uadj = U.symm.toLinearMap by
      exact LinearIsometryEquiv.adjoint_toLinearMap_eq_symm U]
    exact U.symm.toLinearIsometry.norm_toContinuousLinearMap
  have hKnorm : ‖K.toContinuousLinearMap‖ ≤
      ‖R.toContinuousLinearMap‖ * ‖L.toContinuousLinearMap‖ := by
    have h2 := ContinuousLinearMap.opNorm_comp_le Uadj.toContinuousLinearMap
      L.toContinuousLinearMap
    rw [hUnorm, one_mul] at h2
    exact (ContinuousLinearMap.opNorm_comp_le R.toContinuousLinearMap
      (Uadj.toContinuousLinearMap.comp L.toContinuousLinearMap)).trans
      (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
  have htracecycle : Tr (Uadj.comp Y) = Tr (K.comp X) := by
    calc
      Tr (Uadj.comp Y) = Tr ((Uadj.comp (L.comp X)).comp R) := rfl
      _ = Tr (R.comp (Uadj.comp (L.comp X))) :=
        LinearMap.trace_comp_comm' R (Uadj.comp (L.comp X))
      _ = Tr (K.comp X) := rfl
  calc
    traceNorm Y = (Tr (Uadj.comp Y)).re := hpolar
    _ = (Tr (K.comp X)).re := congrArg Complex.re htracecycle
    _ ≤ ‖K.toContinuousLinearMap‖ * traceNorm X := re_trace_comp_le K X
    _ ≤ (‖R.toContinuousLinearMap‖ * ‖L.toContinuousLinearMap‖) *
        traceNorm X :=
      mul_le_mul_of_nonneg_right hKnorm (traceNorm_nonneg X)
    _ = ‖L.toContinuousLinearMap‖ * traceNorm X *
        ‖R.toContinuousLinearMap‖ := by ring

private theorem outer_product_opNorm {A : Sys} (u v : Space A) :
    ‖(QuantumChannel.outer_product u v).toContinuousLinearMap‖ =
      ‖u‖ * ‖v‖ := by
  have h := congrArg LinearMap.toContinuousLinearMap
    (QuantumChannel.outer_product_eq_rankOne u v)
  change (QuantumChannel.outer_product u v).toContinuousLinearMap =
    InnerProductSpace.rankOne ℂ v u at h
  rw [h, InnerProductSpace.norm_rankOne, mul_comm]

private def traceNormUnitVector (A : Sys) : Space A :=
  spaceONB A ⟨0, A.dim_pos⟩

private theorem norm_traceNormUnitVector (A : Sys) :
    ‖traceNormUnitVector A‖ = 1 := by
  exact (spaceONB A).norm_eq_one ⟨0, A.dim_pos⟩

/-- Rank-one trace norm is bounded by the product of the vector norms. -/
theorem traceNorm_outer_product_le {A : Sys} (u v : Space A) :
    traceNorm (QuantumChannel.outer_product u v) ≤ ‖u‖ * ‖v‖ := by
  let e : Space A := traceNormUnitVector A
  let L : Operator A := QuantumChannel.outer_product e v
  let P : Operator A := QuantumChannel.outer_product e e
  let R : Operator A := QuantumChannel.outer_product u e
  have he : ‖e‖ = 1 := norm_traceNormUnitVector A
  have hfactor : (L.comp P).comp R = QuantumChannel.outer_product u v := by
    apply LinearMap.ext
    intro x
    simp [L, P, R, QuantumChannel.outer_product_eq_rankOne,
      InnerProductSpace.rankOne_apply, he]
  have hPnonneg : 0 ≤ P := QuantumChannel.outer_product_self_nonneg e
  have hPtrace : traceNorm P = 1 := by
    rw [traceNorm_of_nonneg P hPnonneg]
    change (Tr (QuantumChannel.outer_product e e)).re = 1
    rw [QuantumChannel.trace_outer_product, inner_self_eq_norm_sq_to_K, he]
    norm_num
  rw [← hfactor]
  calc
    traceNorm ((L.comp P).comp R) ≤
        ‖L.toContinuousLinearMap‖ * traceNorm P *
          ‖R.toContinuousLinearMap‖ := traceNorm_comp_comp_le L P R
    _ = ‖u‖ * ‖v‖ := by
      rw [hPtrace, outer_product_opNorm, outer_product_opNorm, he]
      ring

end NativeTraceDistance
end QuantumModel
