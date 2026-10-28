/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.StateEffectMaps.GSLCore
import Quantum.OperationalProbabilistic.Framework.EffectNorms.GSLCore
import Quantum.OperationalProbabilistic.Framework.StateNorms.GSLCore

open CategoryTheory
open scoped MonoidalCategory

/-!
# Operational framework: transformation state maps and channel contraction

The action of a transformation on operational state classes is assembled as
`operationalTransformationStateMap`, with its evaluation identity
`stateOperationalQuotientEval_transformationStateMap`.  Channels do not increase the
operational state norm (`operationalStateNorm_channel_apply_le`).
-/

namespace OPT

universe u v w

section CausalOperationalProbabilisticTheory

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]

variable [Preadditive Sys]

variable [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]

variable [CausalOperationalProbabilisticTheory Sys]

/-- The action of an operational transformation on a physical state class,
using a chosen physical representative. -/
private noncomputable def operationalTransformationApplyToPhysicalStateClass {A B : Sys}
    (Δ : OperationalTransformationSpaceReal (Sys := Sys) A B)
    (x : PhysicalStateClassSet (Sys := Sys) A) :
    OperationalStateSpaceReal (Sys := Sys) B :=
  operationalTransformationApplyToStateClass (Sys := Sys) Δ
    (physicalStateClassRepresentative (Sys := Sys) x)
    (physicalStateClassRepresentative_isState (Sys := Sys) x)

/-- For a fixed operational transformation, the free linear-combination map
on physical state classes obtained by acting on each generator. -/
noncomputable def operationalTransformationApplyToStateFinsuppMap {A B : Sys}
    (Δ : OperationalTransformationSpaceReal (Sys := Sys) A B) :
    (PhysicalStateClassSet (Sys := Sys) A →₀ ℝ) →ₗ[ℝ]
      OperationalStateSpaceReal (Sys := Sys) B :=
  Finsupp.linearCombination ℝ
    (operationalTransformationApplyToPhysicalStateClass (Sys := Sys) Δ)

/-- On physical transformation representatives, the chosen physical-state-class
action agrees with the previously constructed physical-transformation state map. -/
private theorem operationalTransformationApplyToPhysicalStateClass_mk {A B : Sys}
    {f : A ⟶ B} (hf : IsTransformation f)
    (x : PhysicalStateClassSet (Sys := Sys) A) :
    operationalTransformationApplyToPhysicalStateClass (Sys := Sys)
        (operationalTransformationClass (Sys := Sys) f hf) x =
      transformationStateMap (Sys := Sys) f hf
        (⟨(x : StateOperationalQuotient (Sys := Sys) A),
          Submodule.subset_span x.2⟩ :
          OperationalStateSpaceReal (Sys := Sys) A) := by
  unfold operationalTransformationApplyToPhysicalStateClass
  rw [operationalTransformationApplyToStateClass_mk (Sys := Sys) hf
    (physicalStateClassRepresentative_isState (Sys := Sys) x)]
  apply congrArg (transformationStateMap (Sys := Sys) f hf)
  apply Subtype.ext
  exact physicalStateClassRepresentative_class_eq (Sys := Sys) x

/-- For a physical transformation representative, the free action on physical
state classes is the already constructed state-space map applied after forming
the input linear combination. -/
private theorem operationalTransformationApplyToStateFinsuppMap_mk_eq_transformationStateMap
    {A B : Sys} {f : A ⟶ B} (hf : IsTransformation f)
    (l : PhysicalStateClassSet (Sys := Sys) A →₀ ℝ) :
    operationalTransformationApplyToStateFinsuppMap (Sys := Sys)
        (operationalTransformationClass (Sys := Sys) f hf) l =
      transformationStateMap (Sys := Sys) f hf
        (operationalStatePhysicalClassCombination (Sys := Sys) A l) := by
  let L₁ :
      (PhysicalStateClassSet (Sys := Sys) A →₀ ℝ) →ₗ[ℝ]
        OperationalStateSpaceReal (Sys := Sys) B :=
    operationalTransformationApplyToStateFinsuppMap (Sys := Sys)
      (operationalTransformationClass (Sys := Sys) f hf)
  let L₂ :
      (PhysicalStateClassSet (Sys := Sys) A →₀ ℝ) →ₗ[ℝ]
        OperationalStateSpaceReal (Sys := Sys) B :=
    (transformationStateMap (Sys := Sys) f hf).comp
      (operationalStatePhysicalClassCombination (Sys := Sys) A)
  have hL : L₁ = L₂ := by
    apply Finsupp.lhom_ext
    intro x r
    calc
      L₁ (Finsupp.single x r) =
          r • operationalTransformationApplyToPhysicalStateClass (Sys := Sys)
            (operationalTransformationClass (Sys := Sys) f hf) x := by
            simp [L₁, operationalTransformationApplyToStateFinsuppMap]
      _ = r • transformationStateMap (Sys := Sys) f hf
          (⟨(x : StateOperationalQuotient (Sys := Sys) A),
            Submodule.subset_span x.2⟩ :
            OperationalStateSpaceReal (Sys := Sys) A) := by
            rw [operationalTransformationApplyToPhysicalStateClass_mk (Sys := Sys) hf x]
      _ = transformationStateMap (Sys := Sys) f hf
          (r • (⟨(x : StateOperationalQuotient (Sys := Sys) A),
            Submodule.subset_span x.2⟩ :
            OperationalStateSpaceReal (Sys := Sys) A)) := by
            rw [map_smul]
      _ = L₂ (Finsupp.single x r) := by
            have hcomb :
                operationalStatePhysicalClassCombination (Sys := Sys) A (Finsupp.single x r) =
                  r • (⟨(x : StateOperationalQuotient (Sys := Sys) A),
                    Submodule.subset_span x.2⟩ :
                    OperationalStateSpaceReal (Sys := Sys) A) := by
              apply Subtype.ext
              change
                (Finsupp.linearCombination ℝ
                  (fun x : PhysicalStateClassSet (Sys := Sys) A =>
                    (x : StateOperationalQuotient (Sys := Sys) A))) (Finsupp.single x r) =
                  r • (x : StateOperationalQuotient (Sys := Sys) A)
              rw [Finsupp.linearCombination_single]
            simp [L₂, hcomb]
  exact LinearMap.congr_fun hL l

/-- The chosen physical-state-class action is additive in the operational
transformation. -/
private theorem operationalTransformationApplyToPhysicalStateClass_add {A B : Sys}
    (Δ Γ : OperationalTransformationSpaceReal (Sys := Sys) A B)
    (x : PhysicalStateClassSet (Sys := Sys) A) :
    operationalTransformationApplyToPhysicalStateClass (Sys := Sys) (Δ + Γ) x =
      operationalTransformationApplyToPhysicalStateClass (Sys := Sys) Δ x +
        operationalTransformationApplyToPhysicalStateClass (Sys := Sys) Γ x := by
  unfold operationalTransformationApplyToPhysicalStateClass
  exact operationalTransformationApplyToStateClass_add (Sys := Sys) Δ Γ
    (physicalStateClassRepresentative_isState (Sys := Sys) x)

/-- The chosen physical-state-class action is homogeneous in the operational
transformation. -/
private theorem operationalTransformationApplyToPhysicalStateClass_smul {A B : Sys}
    (r : ℝ) (Δ : OperationalTransformationSpaceReal (Sys := Sys) A B)
    (x : PhysicalStateClassSet (Sys := Sys) A) :
    operationalTransformationApplyToPhysicalStateClass (Sys := Sys) (r • Δ) x =
      r • operationalTransformationApplyToPhysicalStateClass (Sys := Sys) Δ x := by
  unfold operationalTransformationApplyToPhysicalStateClass
  exact operationalTransformationApplyToStateClass_smul (Sys := Sys) r Δ
    (physicalStateClassRepresentative_isState (Sys := Sys) x)

/-- The free action is additive in the operational transformation. -/
private theorem operationalTransformationApplyToStateFinsuppMap_add {A B : Sys}
    (Δ Γ : OperationalTransformationSpaceReal (Sys := Sys) A B) :
    operationalTransformationApplyToStateFinsuppMap (Sys := Sys) (Δ + Γ) =
      operationalTransformationApplyToStateFinsuppMap (Sys := Sys) Δ +
        operationalTransformationApplyToStateFinsuppMap (Sys := Sys) Γ := by
  apply Finsupp.lhom_ext
  intro x r
  simp [operationalTransformationApplyToStateFinsuppMap,
    operationalTransformationApplyToPhysicalStateClass_add, smul_add]

/-- The free action is homogeneous in the operational transformation. -/
private theorem operationalTransformationApplyToStateFinsuppMap_smul {A B : Sys}
    (r : ℝ) (Δ : OperationalTransformationSpaceReal (Sys := Sys) A B) :
  operationalTransformationApplyToStateFinsuppMap (Sys := Sys) (r • Δ) =
      r • operationalTransformationApplyToStateFinsuppMap (Sys := Sys) Δ := by
  apply Finsupp.lhom_ext
  intro x s
  change
    (Finsupp.linearCombination ℝ
      (operationalTransformationApplyToPhysicalStateClass (Sys := Sys) (r • Δ)))
        (Finsupp.single x s) =
      (r • Finsupp.linearCombination ℝ
        (operationalTransformationApplyToPhysicalStateClass (Sys := Sys) Δ))
        (Finsupp.single x s)
  rw [Finsupp.linearCombination_single, LinearMap.smul_apply,
    Finsupp.linearCombination_single,
    operationalTransformationApplyToPhysicalStateClass_smul]
  exact smul_comm s r (operationalTransformationApplyToPhysicalStateClass (Sys := Sys) Δ x)

/-- For a fixed free input combination, the free action is linear in the
operational transformation class. -/
private noncomputable def operationalTransformationApplyToStateFinsuppMapLinearMap {A B : Sys}
    (l : PhysicalStateClassSet (Sys := Sys) A →₀ ℝ) :
    OperationalTransformationSpaceReal (Sys := Sys) A B →ₗ[ℝ]
      OperationalStateSpaceReal (Sys := Sys) B where
  toFun := fun Δ => operationalTransformationApplyToStateFinsuppMap (Sys := Sys) Δ l
  map_add' := by
    intro Δ Γ
    exact LinearMap.congr_fun
      (operationalTransformationApplyToStateFinsuppMap_add (Sys := Sys) Δ Γ) l
  map_smul' := by
    intro r Δ
    exact LinearMap.congr_fun
      (operationalTransformationApplyToStateFinsuppMap_smul (Sys := Sys) r Δ) l

/-- If a free linear combination of physical input state classes represents
zero, then applying any fixed operational transformation sends it to zero. -/
private theorem operationalTransformationApplyToStateFinsuppMap_eq_zero_of_combination_eq_zero
    {A B : Sys} (Δ : OperationalTransformationSpaceReal (Sys := Sys) A B)
    {l : PhysicalStateClassSet (Sys := Sys) A →₀ ℝ}
    (hl : operationalStatePhysicalClassCombination (Sys := Sys) A l = 0) :
    operationalTransformationApplyToStateFinsuppMap (Sys := Sys) Δ l = 0 := by
  let L := operationalTransformationApplyToStateFinsuppMapLinearMap (Sys := Sys)
    (A := A) (B := B) l
  have hspan :
      ∀ x hx,
        L (⟨x, hx⟩ : OperationalTransformationSpaceReal (Sys := Sys) A B) = 0 := by
    intro x hx
    exact Submodule.span_induction
      (p := fun x hx =>
        L (⟨x, hx⟩ : OperationalTransformationSpaceReal (Sys := Sys) A B) = 0)
      (fun x hx => by
        rcases hx with ⟨f, hf, rfl⟩
        change L (operationalTransformationClass (Sys := Sys) f hf) = 0
        unfold L operationalTransformationApplyToStateFinsuppMapLinearMap
        change operationalTransformationApplyToStateFinsuppMap (Sys := Sys)
          (operationalTransformationClass (Sys := Sys) f hf) l = 0
        rw [operationalTransformationApplyToStateFinsuppMap_mk_eq_transformationStateMap
          (Sys := Sys) hf l, hl]
        exact map_zero (transformationStateMap (Sys := Sys) f hf))
      (by
        change L (0 : OperationalTransformationSpaceReal (Sys := Sys) A B) = 0
        exact map_zero L)
      (fun x y hx hy hx_zero hy_zero => by
        change L ((⟨x, hx⟩ : OperationalTransformationSpaceReal (Sys := Sys) A B) +
              ⟨y, hy⟩) = 0
        rw [map_add, hx_zero, hy_zero, add_zero])
      (fun r x hx hx_zero => by
        change L (r • (⟨x, hx⟩ : OperationalTransformationSpaceReal (Sys := Sys) A B)) = 0
        rw [map_smul, hx_zero, smul_zero])
      hx
  change L Δ = 0
  simpa using hspan (Δ : TransformationOperationalQuotient (Sys := Sys) A B) Δ.2

/-- The free action kills the kernel of the quotient map from formal physical
state combinations to the operational real state space. -/
theorem operationalTransformationApplyToStateFinsuppMap_ker {A B : Sys}
    (Δ : OperationalTransformationSpaceReal (Sys := Sys) A B) :
    LinearMap.ker (operationalStatePhysicalClassCombination (Sys := Sys) A) ≤
      LinearMap.ker (operationalTransformationApplyToStateFinsuppMap (Sys := Sys) Δ) := by
  intro l hl
  change operationalTransformationApplyToStateFinsuppMap (Sys := Sys) Δ l = 0
  exact operationalTransformationApplyToStateFinsuppMap_eq_zero_of_combination_eq_zero
    (Sys := Sys) Δ hl

/-- An operational transformation class induces a real-linear map on the
operational real state spaces. -/
noncomputable def operationalTransformationStateMap {A B : Sys}
    (Δ : OperationalTransformationSpaceReal (Sys := Sys) A B) :
    OperationalStateSpaceReal (Sys := Sys) A →ₗ[ℝ]
      OperationalStateSpaceReal (Sys := Sys) B :=
  (LinearMap.ker (operationalStatePhysicalClassCombination (Sys := Sys) A)).liftQ
    (operationalTransformationApplyToStateFinsuppMap (Sys := Sys) Δ)
    (operationalTransformationApplyToStateFinsuppMap_ker (Sys := Sys) Δ) ∘ₗ
      ((operationalStatePhysicalClassCombination (Sys := Sys) A).quotKerEquivOfSurjective
        (operationalStatePhysicalClassCombination_surjective (Sys := Sys) A)).symm.toLinearMap

/-- On physical transformation representatives, the induced operational
state-space map is the physical transformation state map. -/
theorem operationalTransformationStateMap_mk {A B : Sys}
    {f : A ⟶ B} (hf : IsTransformation f) :
    operationalTransformationStateMap (Sys := Sys)
        (operationalTransformationClass (Sys := Sys) f hf) =
      transformationStateMap (Sys := Sys) f hf := by
  apply LinearMap.ext
  intro δ
  rcases operationalStatePhysicalClassCombination_surjective (Sys := Sys) A δ with ⟨l, hl⟩
  rw [← hl]
  unfold operationalTransformationStateMap
  rw [LinearMap.comp_apply]
  let q := operationalStatePhysicalClassCombination (Sys := Sys) A
  have hsurj : Function.Surjective q :=
    operationalStatePhysicalClassCombination_surjective (Sys := Sys) A
  have hsymm :
      (((q.quotKerEquivOfSurjective hsurj).symm.toLinearMap) (q l)) =
        (Submodule.Quotient.mk l :
          (PhysicalStateClassSet (Sys := Sys) A →₀ ℝ) ⧸ LinearMap.ker q) := by
    exact LinearMap.quotKerEquivOfSurjective_symm_apply (f := q) hsurj l
  change ((LinearMap.ker q).liftQ
      (operationalTransformationApplyToStateFinsuppMap (Sys := Sys)
        (operationalTransformationClass (Sys := Sys) f hf))
      (operationalTransformationApplyToStateFinsuppMap_ker (Sys := Sys)
        (operationalTransformationClass (Sys := Sys) f hf)))
        (((q.quotKerEquivOfSurjective hsurj).symm.toLinearMap) (q l)) =
    transformationStateMap (Sys := Sys) f hf (q l)
  rw [hsymm]
  rw [Submodule.liftQ_apply]
  exact operationalTransformationApplyToStateFinsuppMap_mk_eq_transformationStateMap
    (Sys := Sys) hf l

/-- Evaluation after applying a physical transformation is evaluation by the
pulled-back effect on the input state class. -/
theorem stateOperationalQuotientEval_transformationStateMap {A B : Sys}
    {f : A ⟶ B} (hf : IsTransformation f)
    (b : Effect B) (hb : IsEffect b)
    (δ : OperationalStateSpaceReal (Sys := Sys) A) :
    stateOperationalQuotientEval (Sys := Sys) b hb
        ((transformationStateMap (Sys := Sys) f hf δ :
          OperationalStateSpaceReal (Sys := Sys) B) :
          StateOperationalQuotient (Sys := Sys) B) =
      stateOperationalQuotientEval (Sys := Sys) (f ≫ b)
        (OperationalProbabilisticTheory.transformation_comp (Sys := Sys) hf hb)
        (δ : StateOperationalQuotient (Sys := Sys) A) := by
  change stateOperationalQuotientEval (Sys := Sys) b hb
      (transformationStateMapQuotient (Sys := Sys) f hf
        (δ : StateOperationalQuotient (Sys := Sys) A)) =
    stateOperationalQuotientEval (Sys := Sys) (f ≫ b)
      (OperationalProbabilisticTheory.transformation_comp (Sys := Sys) hf hb)
      (δ : StateOperationalQuotient (Sys := Sys) A)
  refine Submodule.Quotient.induction_on
    (StateOperationalNullSubmodule (Sys := Sys) A)
    (δ : StateOperationalQuotient (Sys := Sys) A) ?_
  intro ρ
  change stateOperationalQuotientEval (Sys := Sys) b hb
      (transformationStateMapQuotient (Sys := Sys) f hf
        (stateOperationalClass (Sys := Sys) A ρ)) =
    stateOperationalQuotientEval (Sys := Sys) (f ≫ b)
      (OperationalProbabilisticTheory.transformation_comp (Sys := Sys) hf hb)
      (stateOperationalClass (Sys := Sys) A ρ)
  rw [transformationStateMapQuotient_mk,
    stateOperationalQuotientEval_mk, stateOperationalQuotientEval_mk]
  simp [prob, transformationStateMapRaw, Category.assoc]

/-- Pulling an effect back along a channel gives a physical effect. -/
theorem channel_effect_isEffect {A B : Sys} {C : A ⟶ B}
    (hC : IsChannel C) {b : Effect B} (hb : IsEffect b) :
    IsEffect (C ≫ b) :=
  OperationalProbabilisticTheory.transformation_comp (Sys := Sys)
    (OperationalProbabilisticTheory.channel_transformation (Sys := Sys) hC) hb

/-- Pulling a bounded effect back along a channel gives a bounded effect. -/
theorem channel_boundedEffect_precomp {A B : Sys} {C : A ⟶ B}
    (hC : IsChannel C) {b : Effect B} (hb : IsBoundedEffect b) :
    IsBoundedEffect (C ≫ b) :=
  boundedEffect_of_isEffect (Sys := Sys)
    (channel_effect_isEffect (Sys := Sys) hC hb.1)

/-- Evaluation after applying the operational state map induced by a channel
is evaluation by the pulled-back effect. -/
theorem stateOperationalQuotientEval_operationalTransformationStateMap_channel
    {A B : Sys} {C : A ⟶ B} (hC : IsChannel C)
    (b : Effect B) (hb : IsEffect b)
    (δ : OperationalStateSpaceReal (Sys := Sys) A) :
    stateOperationalQuotientEval (Sys := Sys) b hb
        ((operationalTransformationStateMap (Sys := Sys)
          (operationalTransformationClass (Sys := Sys) C
            (OperationalProbabilisticTheory.channel_transformation (Sys := Sys) hC)) δ :
          OperationalStateSpaceReal (Sys := Sys) B) :
          StateOperationalQuotient (Sys := Sys) B) =
      stateOperationalQuotientEval (Sys := Sys) (C ≫ b)
        (channel_effect_isEffect (Sys := Sys) hC hb)
        (δ : StateOperationalQuotient (Sys := Sys) A) := by
  rw [operationalTransformationStateMap_mk (Sys := Sys)
    (OperationalProbabilisticTheory.channel_transformation (Sys := Sys) hC)]
  exact stateOperationalQuotientEval_transformationStateMap (Sys := Sys)
    (OperationalProbabilisticTheory.channel_transformation (Sys := Sys) hC) b hb δ

/-- Channels do not increase the state-side operational norm. -/
theorem operationalStateNorm_channel_apply_le
    {A B : Sys} {C : A ⟶ B} (hC : IsChannel C)
    (δ : OperationalStateSpaceReal (Sys := Sys) A) :
    operationalStateNorm (Sys := Sys)
        (operationalTransformationStateMap (Sys := Sys)
          (operationalTransformationClass (Sys := Sys) C
            (OperationalProbabilisticTheory.channel_transformation (Sys := Sys) hC)) δ)
      ≤ operationalStateNorm (Sys := Sys) δ := by
  let δC : OperationalStateSpaceReal (Sys := Sys) B :=
    operationalTransformationStateMap (Sys := Sys)
      (operationalTransformationClass (Sys := Sys) C
        (OperationalProbabilisticTheory.channel_transformation (Sys := Sys) hC)) δ
  let Sδ : Set ℝ := operationalStateNormEvalRange (Sys := Sys)
    (δ : StateOperationalQuotient (Sys := Sys) A)
  let SδC : Set ℝ := operationalStateNormEvalRange (Sys := Sys)
    (δC : StateOperationalQuotient (Sys := Sys) B)
  have hsup : sSup SδC ≤ sSup Sδ := by
    refine csSup_le (operationalStateNorm_evalRange_nonempty (Sys := Sys) δC) ?_
    intro y hy
    rcases hy with ⟨b, _hb_univ, rfl⟩
    have hmem : stateOperationalQuotientEval (Sys := Sys) (C ≫ b.1)
        (channel_effect_isEffect (Sys := Sys) hC b.2.1)
        (δ : StateOperationalQuotient (Sys := Sys) A) ∈ Sδ := by
      exact ⟨⟨C ≫ b.1, channel_boundedEffect_precomp (Sys := Sys) hC b.2⟩,
        trivial, rfl⟩
    dsimp [δC]
    rw [stateOperationalQuotientEval_operationalTransformationStateMap_channel
        (Sys := Sys) hC b.1 b.2.1 δ]
    exact le_csSup (operationalStateNorm_evalRange_bddAbove (Sys := Sys) δ) hmem
  have hinf : sInf Sδ ≤ sInf SδC := by
    refine le_csInf (operationalStateNorm_evalRange_nonempty (Sys := Sys) δC) ?_
    intro y hy
    rcases hy with ⟨b, _hb_univ, rfl⟩
    have hmem : stateOperationalQuotientEval (Sys := Sys) (C ≫ b.1)
        (channel_effect_isEffect (Sys := Sys) hC b.2.1)
        (δ : StateOperationalQuotient (Sys := Sys) A) ∈ Sδ := by
      exact ⟨⟨C ≫ b.1, channel_boundedEffect_precomp (Sys := Sys) hC b.2⟩,
        trivial, rfl⟩
    dsimp [δC]
    rw [stateOperationalQuotientEval_operationalTransformationStateMap_channel
        (Sys := Sys) hC b.1 b.2.1 δ]
    exact csInf_le (operationalStateNorm_evalRange_bddBelow (Sys := Sys) δ) hmem
  unfold operationalStateNorm
  change sSup SδC - sInf SδC ≤ sSup Sδ - sInf Sδ
  exact sub_le_sub hsup hinf

end CausalOperationalProbabilisticTheory
end OPT
