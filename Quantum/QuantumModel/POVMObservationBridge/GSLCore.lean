/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.ClassicalFDivConcrete.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiOrder.GSLCore
import Quantum.QuantumModel.FixedOutcomePOVM.GSLCore
import Quantum.QuantumModel.NativeMeasuredRelativeEntropy.GSLCore
import Mathlib.Order.Filter.AtTopBot.Map
import Mathlib.Topology.Order.AtTopBotIxx
import Quantum.QuantumModel.NativeTraceDistance.GSLCore
import Quantum.OperationalProbabilistic.Decomposition.ConditionedStates.GSLCore
import Quantum.OperationalProbabilistic.DistinguishableStates.Core.GSLCore
import Quantum.OperationalProbabilistic.Framework.MeasuredLift.GSLCore
import Quantum.OperationalProbabilistic.Framework.MeasurementStatistics.GSLCore
import Quantum.QuantumModel.HighInterfaces.GSLCoreRetained

/-!
# Native POVMs and allowed observation tests

Correspondence between finite POVMs and allowed observations for the finite-dimensional
quantum model.  It converts finite native POVMs to allowed observation tests and
allowed observation tests back to fixed-outcome native POVMs, preserving the
entire Born PMF in both directions.

References:
the quantum-measurement discussion in Nakahira Section 5.3.3, pp. 91--92, and
Proposition 7.7 in Section 7.3.1, pp. 148--149: a finite effect family is a
measurement exactly when its sum is deterministic.
-/

noncomputable section

namespace QuantumModel

open CategoryTheory
open QuantumState
open OPT.DistinguishableStates
open NativeFidelity
open scoped MonoidalCategory

private theorem toRawSuperoperator_sum {A B : Sys} {ι : Type*} [Fintype ι]
    (f : ι → (A ⟶ B)) :
    HPHom.toRawSuperoperator (∑ i, f i) =
      ∑ i, HPHom.toRawSuperoperator (f i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [HPHom.toRawSuperoperator_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        HPHom.toRawSuperoperator_add, ih]

/-! ## Native POVMs to allowed observation tests -/

/-- From finite POVMs to allowed observation tests.

Every finite native POVM determines an allowed observation test with the same
outcome type and the same Born PMF on every density matrix.  The coherence
step proves that the whole converted categorical effect family sums to the
deterministic effect; it is not merely a pointwise effect conversion.

The source correspondence is Nakahira Section 5.3.3, pp. 91--92, together
with Proposition 7.7 in Section 7.3.1, pp. 148--149. -/
theorem exists_observationTest_of_povm
    {A : Sys} (M : NativeFidelity.POVM A) :
    ∃ T : OPT.ObservationTest (Sys := Sys) A M.ι,
      ∀ rho : DensityMatrix A,
        OPT.observationPMF (OPT.Test.ofIndexed T)
            (DensityMatrix.normalizedStateEquiv rho) =
          M.bornPMF rho := by
  classical
  have hM_le (i : M.ι) :
      M.effect i ≤ (LinearMap.id : Operator A) := by
    rw [← M.sum_eq_id]
    exact Finset.single_le_sum (fun j _hj => M.nonneg j)
      (Finset.mem_univ i)
  choose c hc hborn using fun i =>
    NativeTraceDistance.exists_effect_of_povmElement (M.effect i)
      ⟨M.nonneg i, hM_le i⟩
  have hsumc : ∑ i, c i = OPT.detEffect (Sys := Sys) A := by
    let xi : OPT.OperationalEffectSpaceReal (Sys := Sys) A :=
      ∑ i, OPT.Decomposition.operationalEffectClass
        (Sys := Sys) (c i) (hc i)
    let eta : OPT.OperationalEffectSpaceReal (Sys := Sys) A :=
      OPT.Decomposition.operationalEffectClass (Sys := Sys)
        (OPT.detEffect (Sys := Sys) A)
        (OPT.detEffect_isEffect (Sys := Sys) A)
    have hxieta : xi = eta := by
      apply OPT.normalizedStates_ext_operationalEffects (Sys := Sys)
      intro rho hrho
      let dm : DensityMatrix A := DensityMatrix.ofNormalizedState rho hrho
      have hdm : dm.toState = rho :=
        DensityMatrix.toState_ofNormalizedState rho hrho
      have htraceSum :
          ∑ i, (Tr ((M.effect i).comp dm.operator)).re =
            (Tr ((∑ i, M.effect i).comp dm.operator)).re := by
        have hcomp :
            (∑ i, M.effect i).comp dm.operator =
              ∑ i, (M.effect i).comp dm.operator := by
          apply LinearMap.ext
          intro x
          simp [LinearMap.sum_apply]
        rw [hcomp, map_sum]
        simp
      calc
        OPT.effectOperationalQuotientEval (Sys := Sys) rho hrho.1
            (xi : OPT.EffectOperationalQuotient (Sys := Sys) A) =
            ∑ i, OPT.prob (Sys := Sys) (c i) rho := by
          simp [xi, OPT.Decomposition.operationalEffectClass,
            OPT.effectOperationalQuotientEval_mk]
        _ = ∑ i, NativeNoCloning.bornProbability (M.effect i) dm := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [← hdm]
          exact hborn i dm
        _ = ∑ i, (Tr ((M.effect i).comp dm.operator)).re := rfl
        _ = (Tr ((∑ i, M.effect i).comp dm.operator)).re := htraceSum
        _ = 1 := by
          rw [M.sum_eq_id, LinearMap.id_comp, dm.trace_one]
          norm_num
        _ = OPT.prob (Sys := Sys) (OPT.detEffect (Sys := Sys) A) rho :=
          hrho.2.symm
        _ = OPT.effectOperationalQuotientEval (Sys := Sys) rho hrho.1
            (eta : OPT.EffectOperationalQuotient (Sys := Sys) A) := by
          simp [eta, OPT.Decomposition.operationalEffectClass,
            OPT.effectOperationalQuotientEval_mk]
    apply OPT.effect_eq_of_operationalClass_eq (Sys := Sys)
    have hval := congrArg Subtype.val hxieta
    simpa [xi, eta, OPT.Decomposition.operationalEffectClass, map_sum] using hval
  letI : EffectFamilyObservationTestTheory Sys :=
    effectFamilyObservationTestTheory_of_finiteDeterministicFamilyCompletion
      (Sys := Sys)
  rcases observationTest_of_effects_sum_detEffect
      (Sys := Sys) c hc hsumc with ⟨T, hTc⟩
  refine ⟨T, ?_⟩
  intro rho
  ext i
  change ENNReal.ofReal
      (OPT.prob (Sys := Sys) (T.outcome i) rho.toState) =
    ENNReal.ofReal
      (NativeNoCloning.bornProbability (M.effect i) rho)
  rw [hTc i]
  exact congrArg ENNReal.ofReal (hborn i rho)

/-! ## Allowed observation tests to fixed-outcome native POVMs -/

/-- From allowed observation tests to finite POVMs.

Every allowed bundled observation test determines a native POVM on its exact
bundled outcome type, with the same Born PMF on every density matrix.  The
coherence step uses trace preservation of the total test to prove that the
sum of all Kraus-normalization effects is exactly the identity operator.

The source correspondence is Nakahira Section 5.3.3, pp. 91--92, together
with Proposition 7.7 in Section 7.3.1, pp. 148--149. -/
theorem exists_fixedOutcomePOVM_of_observationTest
    {A : Sys} (T : OPT.Test (Sys := Sys) A (𝟙_ Sys)) :
    ∃ M : FixedOutcomePOVM A T.ι,
      ∀ rho : DensityMatrix A,
        M.bornPMF rho =
          OPT.observationPMF T
            (DensityMatrix.normalizedStateEquiv rho) := by
  classical
  have htrans (i : T.ι) : IsTransformation (T.outcome i) := by
    exact OPT.OperationalProbabilisticTheory.test_transformation
      (Sys := Sys) T.isTest i
  choose K hKmap hKle using fun i => (htrans i).2
  let E : T.ι → Operator A := fun i => (K i).normalization
  have hE_povmElement (i : T.ι) :
      NativeNoCloning.POVMElement (E i) :=
    ⟨krausFamily_normalization_nonneg (K i), hKle i⟩
  have hE_nonneg (i : T.ι) : 0 ≤ E i :=
    (hE_povmElement i).1
  have hsumE : ∑ i, E i = (LinearMap.id : Operator A) := by
    apply operator_eq_of_trace_comp_eq
    intro X
    have htotal : IsChannel (∑ i, T.outcome i) :=
      OPT.CausalOperationalProbabilisticTheory.test_total_channel
        (Sys := Sys) T.outcome T.isTest
    rcases htotal.2 with ⟨Ktotal, hKtotalMap, hKtotalNorm⟩
    have hcomp :
        (∑ i, E i).comp X = ∑ i, (E i).comp X := by
      apply LinearMap.ext
      intro x
      simp [LinearMap.sum_apply]
    calc
      Tr ((∑ i, E i).comp X) = ∑ i, Tr ((E i).comp X) := by
        rw [hcomp, map_sum]
      _ = ∑ i, Tr (HPHom.toRawSuperoperator (T.outcome i) X) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [← hKmap i, trace_krausFamily_map]
      _ = Tr ((∑ i, HPHom.toRawSuperoperator (T.outcome i)) X) := by
        rw [LinearMap.sum_apply, map_sum]
      _ = Tr (HPHom.toRawSuperoperator (∑ i, T.outcome i) X) := by
        rw [toRawSuperoperator_sum]
      _ = Tr (HPHom.toRawSuperoperator Ktotal.map X) := by
        rw [hKtotalMap]
      _ = Tr (Ktotal.normalization.comp X) :=
        trace_krausFamily_map Ktotal X
      _ = Tr ((LinearMap.id : Operator A).comp X) := by
        rw [hKtotalNorm]
  have hborn (i : T.ι) (rho : DensityMatrix A) :
      OPT.prob (Sys := Sys) (T.outcome i) rho.toState =
        NativeNoCloning.bornProbability (E i) rho := by
    have hprob : ∀ (e : OPT.Effect (Sys := Sys) A) (s : OPT.State (Sys := Sys) A),
        OPT.prob (Sys := Sys) e s =
          (Tr (HPHom.toRawSuperoperator (s ≫ e) LinearMap.id)).re := fun _ _ => rfl
    have hcompS : ∀ (s : OPT.State (Sys := Sys) A) (e : OPT.Effect (Sys := Sys) A),
        HPHom.toRawSuperoperator (s ≫ e) LinearMap.id =
          HPHom.toRawSuperoperator e (HPHom.toRawSuperoperator s LinearMap.id) :=
      fun _ _ => rfl
    rw [hprob, hcompS]
    change (Tr (HPHom.toRawSuperoperator (T.outcome i)
        (HPHom.toRawSuperoperator rho.toState LinearMap.id))).re =
      (Tr ((E i).comp rho.operator)).re
    rw [rho.toState_apply_id, ← hKmap i, trace_krausFamily_map]
  let M : FixedOutcomePOVM A T.ι :=
    ⟨E, hE_nonneg, hsumE⟩
  refine ⟨M, ?_⟩
  intro rho
  ext i
  rw [FixedOutcomePOVM.bornPMF_apply, OPT.observationPMF_apply]
  change ENNReal.ofReal
      (NativeNoCloning.bornProbability (E i) rho) =
    ENNReal.ofReal (OPT.prob (Sys := Sys) (T.outcome i) rho.toState)
  exact congrArg ENNReal.ofReal (hborn i rho).symm

/-! ## Cofinality equalities -/

/-- Observation/POVM cofinality equality for the finite-dimensional quantum model.

The left supremum ranges over allowed finite observation tests, while the
right supremum ranges over every bundled finite native POVM.  The first
inequality sends each allowed test through the reverse bridge; the second
sends each native POVM through the forward bridge.  Both comparisons preserve
the two Born PMFs exactly, so no epsilon approximation or attainment
assumption is used. -/
theorem measuredSup_quantumModel_eq_iSup_povm
    {V : Type*} [CompleteLattice V]
    (score : OPT.ClassicalPMFScore V)
    {A : Sys} (rho sigma : DensityMatrix A) :
    OPT.measuredSup score
        (DensityMatrix.normalizedStateEquiv rho)
        (DensityMatrix.normalizedStateEquiv sigma) =
      ⨆ M : NativeFidelity.POVM A,
        score (M.bornPMF rho) (M.bornPMF sigma) := by
  apply le_antisymm
  · unfold OPT.measuredSup
    apply iSup_le
    intro T
    obtain ⟨M, hM⟩ := exists_fixedOutcomePOVM_of_observationTest T
    calc
      score
          (OPT.observationPMF T
            (DensityMatrix.normalizedStateEquiv rho))
          (OPT.observationPMF T
            (DensityMatrix.normalizedStateEquiv sigma)) =
          score (M.bornPMF rho) (M.bornPMF sigma) := by
            rw [hM rho, hM sigma]
      _ ≤ ⨆ N : NativeFidelity.POVM A,
          score (N.bornPMF rho) (N.bornPMF sigma) := by
            exact le_iSup
              (fun N : NativeFidelity.POVM A ↦
                score (N.bornPMF rho) (N.bornPMF sigma))
              M.toPOVM
  · apply iSup_le
    intro M
    obtain ⟨T, hT⟩ := exists_observationTest_of_povm M
    calc
      score (M.bornPMF rho) (M.bornPMF sigma) =
          score
            (OPT.observationPMF (OPT.Test.ofIndexed T)
              (DensityMatrix.normalizedStateEquiv rho))
            (OPT.observationPMF (OPT.Test.ofIndexed T)
              (DensityMatrix.normalizedStateEquiv sigma)) := by
            exact congrArg₂ (@score M.ι M.fintype_ι)
              (hT rho).symm (hT sigma).symm
      _ ≤ OPT.measuredSup score
          (DensityMatrix.normalizedStateEquiv rho)
          (DensityMatrix.normalizedStateEquiv sigma) := by
            exact le_iSup
              (fun N : OPT.Test (Sys := Sys) A (𝟙_ Sys) ↦
                score
                  (OPT.observationPMF N
                    (DensityMatrix.normalizedStateEquiv rho))
                  (OPT.observationPMF N
                    (DensityMatrix.normalizedStateEquiv sigma)))
              (OPT.Test.ofIndexed T)

end QuantumModel
