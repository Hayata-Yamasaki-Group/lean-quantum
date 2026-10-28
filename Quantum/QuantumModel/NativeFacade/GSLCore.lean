/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.NativeNoCloning.GSLCore

/-! # Matrix and categorical quantum channels

Equivalences between complete positivity with preservation of the operator trace
and the categorical quantum-channel predicate.
-/

noncomputable section

namespace QuantumModel

open CategoryTheory
open QuantumState
open scoped Kronecker

namespace DensityMatrix

/-- Density matrices are equivalent to normalized categorical preparations.
The proof component expressing normalization is propositionally irrelevant. -/
def normalizedStateEquiv {A : Sys} :
    DensityMatrix A ≃
      {rho : OPT.State (Sys := Sys) A //
        OPT.IsNormalizedState (Sys := Sys) rho} where
  toFun rho := ⟨rho.toState, rho.toState_isNormalizedState⟩
  invFun rho := ofNormalizedState rho.1 rho.2
  left_inv rho := by
    apply DensityMatrix.ext
    exact rho.toState_apply_id
  right_inv rho := by
    apply Subtype.ext
    exact toState_ofNormalizedState rho.1 rho.2

end DensityMatrix

/-- A superoperator preserves trace in the direct, representation-independent
sense when it preserves the ordinary operator trace on every input. -/
def PreservesTrace {A B : Sys} (Phi : A ⟶ B) : Prop :=
  ∀ X : Operator A,
    Tr (HPHom.toRawSuperoperator Phi X) = Tr X

/-- Complete positivity together with trace preservation. -/
def IsCPTP {A B : Sys} (Phi : A ⟶ B) : Prop :=
  QuantumChannel.IsCompletelyPositive (HPHom.toRawSuperoperator Phi) ∧
    PreservesTrace Phi

/-- Equivalence of categorical quantum channels and completely positive trace-preserving maps. -/
theorem isChannel_iff_isCPTP {A B : Sys} (Phi : A ⟶ B) :
    IsChannel Phi ↔ IsCPTP Phi := by
  constructor
  · rintro ⟨hCP, K, hKmap, hKnorm⟩
    refine ⟨hCP, ?_⟩
    intro X
    rw [← hKmap, trace_krausFamily_map, hKnorm]
    simp
  · rintro ⟨hCP, htrace⟩
    obtain ⟨K, hKmap⟩ := exists_krausFamily_of_isEvent hCP
    refine ⟨hCP, K, hKmap, ?_⟩
    apply operator_eq_of_trace_comp_eq
    intro X
    rw [← trace_krausFamily_map K, hKmap, htrace]
    simp

/-- Equivalence of complete positivity and trace preservation with the finite Kraus description. -/
theorem isCPTP_iff_exists_normalizedKraus {A B : Sys} (Phi : A ⟶ B) :
    IsCPTP Phi ↔
      ∃ K : KrausFamily A B,
        K.map = Phi ∧ K.normalization = LinearMap.id := by
  constructor
  · intro hPhi
    exact ((isChannel_iff_isCPTP Phi).mpr hPhi).2
  · rintro ⟨K, hKmap, hKnorm⟩
    apply (isChannel_iff_isCPTP Phi).mp
    refine ⟨?_, K, hKmap, hKnorm⟩
    rw [← hKmap]
    exact K.map_isCompletelyPositive

end QuantumModel
