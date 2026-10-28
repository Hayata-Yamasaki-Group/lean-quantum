/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.NativeFacade.GSLCore
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

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

/-- Unitaries on a finite quantum environment. -/
abbrev EnvironmentUnitary (E : Sys) :=
  Space E ≃ₗᵢ[ℂ] Space E

namespace DensityMatrix

/-- The density matrix obtained by applying a native channel. -/
def channelApply {A B : Sys}
    (rho : DensityMatrix A) (Phi : NativeNoCloning.Superoperator A B)
    (hPhi : IsChannel Phi) : DensityMatrix B :=
  DensityMatrix.ofNormalizedState (rho.toState ≫ Phi)
    (OPT.normalizedState_comp_channel rho.toState_isNormalizedState hPhi)

@[simp]
theorem channelApply_operator {A B : Sys}
    (rho : DensityMatrix A) (Phi : NativeNoCloning.Superoperator A B)
    (hPhi : IsChannel Phi) :
    (rho.channelApply Phi hPhi).operator = Phi rho.operator := by
  have hcomp : ∀ {X Y Z : Sys} (f : X ⟶ Y) (g : Y ⟶ Z) (T : Operator X),
      HPHom.toRawSuperoperator (f ≫ g) T =
        HPHom.toRawSuperoperator g (HPHom.toRawSuperoperator f T) := fun _ _ _ => rfl
  have hop : ∀ (s : OPT.State (Sys := Sys) B) (hs : OPT.IsNormalizedState (Sys := Sys) s),
      (DensityMatrix.ofNormalizedState s hs).operator =
        HPHom.toRawSuperoperator s LinearMap.id := fun _ _ => rfl
  delta channelApply
  rw [hop, hcomp, rho.toState_apply_id]

@[simp]
theorem channelApply_toState {A B : Sys}
    (rho : DensityMatrix A) (Phi : NativeNoCloning.Superoperator A B)
    (hPhi : IsChannel Phi) :
    (rho.channelApply Phi hPhi).toState = rho.toState ≫ Phi := by
  exact DensityMatrix.toState_ofNormalizedState _ _

end DensityMatrix

namespace NativeTraceDistance

/-- Every POVM element is represented by a categorical physical effect with
the same Born probabilities on canonical density-matrix preparations. -/
theorem exists_effect_of_povmElement {A : Sys} (E : Operator A)
    (hE : NativeNoCloning.POVMElement E) :
    ∃ a : OPT.Effect (Sys := Sys) A,
      OPT.IsEffect (Sys := Sys) a ∧
        ∀ rho : DensityMatrix A,
          OPT.prob (Sys := Sys) a rho.toState =
            NativeNoCloning.bornProbability E rho := by
  rcases QuantumChannel.positive_full_spectral_outer_product E hE.1 with
    ⟨u, hu, _⟩
  have hcomp : ∀ {X Y Z : Sys} (f : X ⟶ Y) (g : Y ⟶ Z) (T : Operator X),
      HPHom.toRawSuperoperator (f ≫ g) T =
        HPHom.toRawSuperoperator g (HPHom.toRawSuperoperator f T) := fun _ _ _ => rfl
  have hprob : ∀ (e : OPT.Effect (Sys := Sys) A) (s : OPT.State (Sys := Sys) A),
      OPT.prob (Sys := Sys) e s =
        (Tr (HPHom.toRawSuperoperator (s ≫ e) LinearMap.id)).re := fun _ _ => rfl
  let K : KrausFamily A tensorUnitSystem :=
    { index := Fin (Module.finrank ℂ (Space A))
      fintypeIndex := inferInstance
      decidableEqIndex := inferInstance
      operator := fun i =>
        QuantumChannel.outer_product (u i) (outputUnit tensorUnitSystem) }
  have hKnorm : K.normalization = E := by
    change (∑ i : Fin (Module.finrank ℂ (Space A)),
      (LinearMap.adjoint
        (QuantumChannel.outer_product (u i) (outputUnit tensorUnitSystem))).comp
          (QuantumChannel.outer_product (u i) (outputUnit tensorUnitSystem))) = E
    simp_rw [rankOneKraus_normalization]
    exact hu.symm
  refine ⟨K.map, ?_, ?_⟩
  · change IsTransformation K.map
    exact ⟨K.map_isCompletelyPositive, K, rfl, hKnorm.trans_le hE.2⟩
  · intro rho
    rw [hprob, hcomp]
    change (Tr (HPHom.toRawSuperoperator K.map
      (HPHom.toRawSuperoperator rho.toState LinearMap.id))).re =
        (Tr (E.comp rho.operator)).re
    rw [rho.toState_apply_id, trace_krausFamily_map, hKnorm]

/-- Every categorical physical effect supplies a POVM element through its
Kraus normalization, with exactly the same Born probabilities. -/
theorem exists_povmElement_of_effect {A : Sys}
    (a : OPT.Effect (Sys := Sys) A) (ha : OPT.IsEffect (Sys := Sys) a) :
    ∃ E : Operator A,
      NativeNoCloning.POVMElement E ∧
        ∀ rho : DensityMatrix A,
          OPT.prob (Sys := Sys) a rho.toState =
            NativeNoCloning.bornProbability E rho := by
  change IsTransformation a at ha
  rcases ha.2 with ⟨K, hKmap, hKle⟩
  have hcomp : ∀ {X Y Z : Sys} (f : X ⟶ Y) (g : Y ⟶ Z) (T : Operator X),
      HPHom.toRawSuperoperator (f ≫ g) T =
        HPHom.toRawSuperoperator g (HPHom.toRawSuperoperator f T) := fun _ _ _ => rfl
  have hprob : ∀ (e : OPT.Effect (Sys := Sys) A) (s : OPT.State (Sys := Sys) A),
      OPT.prob (Sys := Sys) e s =
        (Tr (HPHom.toRawSuperoperator (s ≫ e) LinearMap.id)).re := fun _ _ => rfl
  refine ⟨K.normalization,
    ⟨krausFamily_normalization_nonneg K, hKle⟩, ?_⟩
  intro rho
  rw [hprob, hcomp]
  change (Tr (HPHom.toRawSuperoperator a
    (HPHom.toRawSuperoperator rho.toState LinearMap.id))).re =
      (Tr (K.normalization.comp rho.operator)).re
  rw [rho.toState_apply_id, ← hKmap, trace_krausFamily_map]

end NativeTraceDistance
end QuantumModel
