/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.EffectNorms.GSLCore

open CategoryTheory
open scoped MonoidalCategory

/-!
# Operational framework: transformation application with ancilla and operational norms

Applying a transformation to one wing of an ancilla-extended state,
`applyTransformationWithAncilla`, is shown to descend to operational state classes as
`operationalTransformationApplyWithAncilla` (additive, homogeneous, and vanishing on the
zero class). The operational state norm vanishes exactly at zero
(`operationalStateNorm_zero`, `operationalStateNorm_eq_zero_iff`).
-/

namespace OPT

universe u v w

section CausalOperationalProbabilisticTheory

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]

variable [Preadditive Sys]

variable [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]

variable [CausalOperationalProbabilisticTheory Sys]

/-- Promoted from a private helper during the OR3 split (used across slices). -/
lemma sSup_range_eq_zero_of_forall_zero {ι : Type*} (f : ι → ℝ)
    (hf : ∀ i, f i = 0) :
    sSup (Set.range f) = 0 := by
  by_cases hι : Nonempty ι
  · have hrange : Set.range f = {0} := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact hf i
      · intro hy
        rcases hι with ⟨i⟩
        have hy0 : y = 0 := by simpa using hy
        exact ⟨i, by rw [hf i, hy0]⟩
    rw [hrange, csSup_singleton]
  · have hrange : Set.range f = (∅ : Set ℝ) := by
      ext y
      constructor
      · rintro ⟨i, _⟩
        exact False.elim (hι ⟨i⟩)
      · intro hy
        exact False.elim hy
    rw [hrange, Real.sSup_empty]

/-- The infimum of the range of an identically-zero function is zero. -/
private lemma sInf_range_eq_zero_of_forall_zero {ι : Type*} (f : ι → ℝ)
    (hf : ∀ i, f i = 0) :
    sInf (Set.range f) = 0 := by
  by_cases hι : Nonempty ι
  · have hrange : Set.range f = {0} := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact hf i
      · intro hy
        rcases hι with ⟨i⟩
        have hy0 : y = 0 := by simpa using hy
        exact ⟨i, by rw [hf i, hy0]⟩
    rw [hrange, csInf_singleton]
  · have hrange : Set.range f = (∅ : Set ℝ) := by
      ext y
      constructor
      · rintro ⟨i, _⟩
        exact False.elim (hι ⟨i⟩)
      · intro hy
        exact False.elim hy
    rw [hrange, Real.sInf_empty]

/-- The operational state norm formula vanishes at zero. -/
theorem operationalStateNorm_zero (A : Sys) :
    operationalStateNorm (Sys := Sys) (A := A) 0 = 0 := by
  unfold operationalStateNorm
  have hsup :
      sSup (operationalStateNormEvalRange (Sys := Sys)
        ((0 : OperationalStateSpaceReal A) : StateOperationalQuotient (Sys := Sys) A)) = 0 := by
    unfold operationalStateNormEvalRange
    rw [Set.image_univ]
    exact sSup_range_eq_zero_of_forall_zero _ (by
      intro a
      exact map_zero (stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1))
  have hinf :
      sInf (operationalStateNormEvalRange (Sys := Sys)
        ((0 : OperationalStateSpaceReal A) : StateOperationalQuotient (Sys := Sys) A)) = 0 := by
    unfold operationalStateNormEvalRange
    rw [Set.image_univ]
    exact sInf_range_eq_zero_of_forall_zero _ (by
      intro a
      exact map_zero (stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1))
  rw [hsup, hinf, sub_self]

/-- The state-side operational norm formula is positive definite on the operational quotient. -/
theorem operationalStateNorm_eq_zero_iff {A : Sys} (δ : OperationalStateSpaceReal A) :
    operationalStateNorm (Sys := Sys) δ = 0 ↔ δ = 0 := by
  constructor
  · intro hnorm
    let S : Set ℝ := operationalStateNormEvalRange (Sys := Sys)
      (δ : StateOperationalQuotient (Sys := Sys) A)
    have hSabove : BddAbove S := by
      simpa [S] using operationalStateNorm_evalRange_bddAbove (Sys := Sys) δ
    have hSbelow : BddBelow S := by
      simpa [S] using operationalStateNorm_evalRange_bddBelow (Sys := Sys) δ
    have hsupinf : sSup S = sInf S := by
      exact sub_eq_zero.mp (by simpa [S, operationalStateNorm] using hnorm)
    have hzero_mem : (0 : ℝ) ∈ S := by
      dsimp [S, operationalStateNormEvalRange]
      refine ⟨⟨(0 : Effect A), zero_boundedEffect (Sys := Sys) A⟩, trivial, ?_⟩
      exact stateOperationalQuotientEval_zero_effect (Sys := Sys)
        (zero_boundedEffect (Sys := Sys) A).1
        (δ : StateOperationalQuotient (Sys := Sys) A)
    have hsup_zero : sSup S = 0 := by
      have hle : sSup S ≤ 0 := by
        rw [hsupinf]
        exact csInf_le hSbelow hzero_mem
      have hge : 0 ≤ sSup S := le_csSup hSabove hzero_mem
      exact le_antisymm hle hge
    have hinf_zero : sInf S = 0 := by
      rw [← hsupinf, hsup_zero]
    have hbounded_eval :
        ∀ a : {a : Effect A // IsBoundedEffect a},
          stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1
            (δ : StateOperationalQuotient (Sys := Sys) A) = 0 := by
      intro a
      have hy :
          stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1
            (δ : StateOperationalQuotient (Sys := Sys) A) ∈ S := by
        dsimp [S, operationalStateNormEvalRange]
        exact ⟨a, trivial, rfl⟩
      have hle :
          stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1
            (δ : StateOperationalQuotient (Sys := Sys) A) ≤ 0 := by
        simpa [hsup_zero] using le_csSup hSabove hy
      have hge :
          0 ≤ stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1
            (δ : StateOperationalQuotient (Sys := Sys) A) := by
        simpa [hinf_zero] using csInf_le hSbelow hy
      exact le_antisymm hle hge
    have hforall :
        ∀ a : Effect A, (ha : IsEffect a) →
          stateOperationalQuotientEval (Sys := Sys) a ha
            (δ : StateOperationalQuotient (Sys := Sys) A) = 0 := by
      intro a ha
      exact hbounded_eval ⟨a, boundedEffect_of_isEffect (Sys := Sys) ha⟩
    have hquot :
        (δ : StateOperationalQuotient (Sys := Sys) A) = 0 :=
      stateOperationalQuotient_eq_zero_of_forall_eval_zero (Sys := Sys) hforall
    exact Subtype.ext hquot
  · intro hδ
    rw [hδ]
    exact operationalStateNorm_zero (Sys := Sys) A

/-- Apply a transformation to the left component of a state with an explicit
ancillary system. -/
def applyTransformationWithAncilla {A B C : Sys}
    (f : A ⟶ B) (σ : State (A ⊗ C)) : State (B ⊗ C) :=
  σ ≫ (f ⊗ₘ 𝟙 C)

/-- Applying a physical transformation with an ancillary identity to a
physical state gives a physical output state. -/
theorem applyTransformationWithAncilla_isState {A B C : Sys}
    {f : A ⟶ B} (hf : IsTransformation f)
    {σ : State (A ⊗ C)} (hσ : IsState σ) :
    IsState (applyTransformationWithAncilla (Sys := Sys) f σ) :=
  CausalOperationalProbabilisticTheory.transformation_comp (Sys := Sys) hσ
    (CausalOperationalProbabilisticTheory.transformation_tensor (Sys := Sys) hf
      (CausalOperationalProbabilisticTheory.channel_transformation (Sys := Sys)
        (CausalOperationalProbabilisticTheory.channel_id (Sys := Sys) C)))

omit [Linear ℝ Sys] [MonoidalLinear ℝ Sys] [CausalOperationalProbabilisticTheory Sys] in
/-- Applying a transformation with an ancilla is additive in the transformation. -/
private theorem applyTransformationWithAncilla_add {A B C : Sys}
    (f g : A ⟶ B) (σ : State (A ⊗ C)) :
    applyTransformationWithAncilla (Sys := Sys) (f + g) σ =
      applyTransformationWithAncilla (Sys := Sys) f σ +
        applyTransformationWithAncilla (Sys := Sys) g σ := by
  unfold applyTransformationWithAncilla
  calc
    σ ≫ ((f + g) ⊗ₘ 𝟙 C) =
        σ ≫ (f ⊗ₘ 𝟙 C + g ⊗ₘ 𝟙 C) := by
          rw [OperationalProbabilisticTheory.tensor_add_left]
    _ = σ ≫ (f ⊗ₘ 𝟙 C) + σ ≫ (g ⊗ₘ 𝟙 C) := by
          exact OperationalProbabilisticTheory.comp_add (Sys := Sys) σ
            (f ⊗ₘ 𝟙 C) (g ⊗ₘ 𝟙 C)

omit [CausalOperationalProbabilisticTheory Sys] in
/-- Applying a transformation with an ancilla commutes with scalar multiplication of the
transformation.
-/
private theorem applyTransformationWithAncilla_smul {A B C : Sys}
    (r : ℝ) (f : A ⟶ B) (σ : State (A ⊗ C)) :
    applyTransformationWithAncilla (Sys := Sys) (r • f) σ =
      r • applyTransformationWithAncilla (Sys := Sys) f σ := by
  unfold applyTransformationWithAncilla
  calc
    σ ≫ ((r • f) ⊗ₘ 𝟙 C) =
        σ ≫ (r • (f ⊗ₘ 𝟙 C)) := by
          rw [OperationalProbabilisticTheory.tensor_smul_left]
    _ = r • (σ ≫ (f ⊗ₘ 𝟙 C)) := by
          exact OperationalProbabilisticTheory.comp_smul (Sys := Sys) r σ
            (f ⊗ₘ 𝟙 C)

/-- The quotient-linear ancillary action of an operational transformation on
the left component of a fixed input state, before restricting to physical real
spans. -/
noncomputable def transformationApplyWithAncillaQuotientLinearMap {A B C : Sys}
    (σ : State (A ⊗ C)) (hσ : IsState σ) :
    TransformationOperationalQuotient (Sys := Sys) A B →ₗ[ℝ]
      StateOperationalQuotient (Sys := Sys) (B ⊗ C) :=
  (TransformationOperationalNullSubmodule (Sys := Sys) A B).liftQ
    {
      toFun := fun f =>
        stateOperationalClass (Sys := Sys) (B ⊗ C)
          (applyTransformationWithAncilla (Sys := Sys) f σ)
      map_add' := by
        intro f g
        rw [← map_add (stateOperationalClass (Sys := Sys) (B ⊗ C))]
        congr 1
        exact applyTransformationWithAncilla_add (Sys := Sys) f g σ
      map_smul' := by
        intro r f
        calc
          stateOperationalClass (Sys := Sys) (B ⊗ C)
              (applyTransformationWithAncilla (Sys := Sys) (r • f) σ) =
              stateOperationalClass (Sys := Sys) (B ⊗ C)
                (r • applyTransformationWithAncilla (Sys := Sys) f σ) := by
                congr 1
                exact applyTransformationWithAncilla_smul (Sys := Sys) r f σ
          _ = r • stateOperationalClass (Sys := Sys) (B ⊗ C)
                (applyTransformationWithAncilla (Sys := Sys) f σ) := by
                exact map_smul (stateOperationalClass (Sys := Sys) (B ⊗ C)) r
                  (applyTransformationWithAncilla (Sys := Sys) f σ)
    }
    (by
      intro f hf
      apply stateOperationalQuotient_eq_zero_of_forall_eval_zero (Sys := Sys)
      intro e he
      change stateOperationalQuotientEval (Sys := Sys) e he
        (stateOperationalClass (Sys := Sys) (B ⊗ C)
          (applyTransformationWithAncilla (Sys := Sys) f σ)) = 0
      rw [stateOperationalQuotientEval_mk]
      exact hf C σ e hσ he)

/-- On representatives, the quotient-linear ancillary action is applying that
representative transformation with the ancillary identity. -/
@[simp]
theorem transformationApplyWithAncillaQuotientLinearMap_mk {A B C : Sys}
    (σ : State (A ⊗ C)) (hσ : IsState σ) (f : A ⟶ B) :
    transformationApplyWithAncillaQuotientLinearMap (Sys := Sys) σ hσ
        (transformationOperationalClass (Sys := Sys) A B f) =
      stateOperationalClass (Sys := Sys) (B ⊗ C)
        (applyTransformationWithAncilla (Sys := Sys) f σ) := by
  rfl

/-- The ancillary action maps operational real transformations to operational
real states on the output plus auxiliary system. -/
noncomputable def operationalTransformationApplyWithAncilla {A B C : Sys}
    (Δ : OperationalTransformationSpaceReal (Sys := Sys) A B)
    (σ : State (A ⊗ C)) (hσ : IsState σ) :
    OperationalStateSpaceReal (Sys := Sys) (B ⊗ C) :=
  ⟨transformationApplyWithAncillaQuotientLinearMap (Sys := Sys) σ hσ
      (Δ : TransformationOperationalQuotient (Sys := Sys) A B),
    by
      exact Submodule.span_induction
        (p := fun x _ =>
          transformationApplyWithAncillaQuotientLinearMap (Sys := Sys) σ hσ x ∈
            OperationalStateSpaceRealSubmodule (Sys := Sys) (B ⊗ C))
        (fun x hx => by
          rcases hx with ⟨f, hf, rfl⟩
          rw [transformationApplyWithAncillaQuotientLinearMap_mk]
          exact stateClass_mem_OperationalStateSpaceRealSubmodule (Sys := Sys)
            (applyTransformationWithAncilla_isState (Sys := Sys) hf hσ))
        (by
          change transformationApplyWithAncillaQuotientLinearMap (Sys := Sys) σ hσ 0 ∈
            OperationalStateSpaceRealSubmodule (Sys := Sys) (B ⊗ C)
          rw [map_zero]
          exact Submodule.zero_mem _)
        (fun x y _hx _hy hx_mem hy_mem => by
          change transformationApplyWithAncillaQuotientLinearMap (Sys := Sys) σ hσ (x + y) ∈
            OperationalStateSpaceRealSubmodule (Sys := Sys) (B ⊗ C)
          rw [map_add]
          exact Submodule.add_mem _ hx_mem hy_mem)
        (fun r x _hx hx_mem => by
          change transformationApplyWithAncillaQuotientLinearMap (Sys := Sys) σ hσ (r • x) ∈
            OperationalStateSpaceRealSubmodule (Sys := Sys) (B ⊗ C)
          rw [map_smul]
          exact Submodule.smul_mem _ r hx_mem)
        Δ.2⟩

/-- On physical transformation representatives, the ancillary action is the
operational state class of the corresponding output state. -/
theorem operationalTransformationApplyWithAncilla_mk {A B C : Sys}
    {f : A ⟶ B} (hf : IsTransformation f)
    {σ : State (A ⊗ C)} (hσ : IsState σ) :
    operationalTransformationApplyWithAncilla (Sys := Sys)
        (⟨transformationOperationalClass (Sys := Sys) A B f,
          transformationClass_mem_OperationalTransformationSpaceRealSubmodule
            (Sys := Sys) hf⟩ :
          OperationalTransformationSpaceReal (Sys := Sys) A B) σ hσ =
      operationalStateClass (Sys := Sys)
        (applyTransformationWithAncilla (Sys := Sys) f σ)
        (applyTransformationWithAncilla_isState (Sys := Sys) hf hσ) := by
  ext
  exact transformationApplyWithAncillaQuotientLinearMap_mk (Sys := Sys) σ hσ f

/-- The ancillary action is additive in the operational transformation. -/
theorem operationalTransformationApplyWithAncilla_add {A B C : Sys}
    (Δ Γ : OperationalTransformationSpaceReal (Sys := Sys) A B)
    {σ : State (A ⊗ C)} (hσ : IsState σ) :
    operationalTransformationApplyWithAncilla (Sys := Sys) (Δ + Γ) σ hσ =
      operationalTransformationApplyWithAncilla (Sys := Sys) Δ σ hσ +
        operationalTransformationApplyWithAncilla (Sys := Sys) Γ σ hσ := by
  ext
  change transformationApplyWithAncillaQuotientLinearMap (Sys := Sys) σ hσ
      ((Δ : TransformationOperationalQuotient (Sys := Sys) A B) +
        (Γ : TransformationOperationalQuotient (Sys := Sys) A B)) =
    transformationApplyWithAncillaQuotientLinearMap (Sys := Sys) σ hσ
      (Δ : TransformationOperationalQuotient (Sys := Sys) A B) +
    transformationApplyWithAncillaQuotientLinearMap (Sys := Sys) σ hσ
      (Γ : TransformationOperationalQuotient (Sys := Sys) A B)
  exact map_add (transformationApplyWithAncillaQuotientLinearMap (Sys := Sys) σ hσ)
    (Δ : TransformationOperationalQuotient (Sys := Sys) A B)
    (Γ : TransformationOperationalQuotient (Sys := Sys) A B)

/-- The ancillary action is homogeneous in the operational transformation. -/
theorem operationalTransformationApplyWithAncilla_smul {A B C : Sys}
    (r : ℝ) (Δ : OperationalTransformationSpaceReal (Sys := Sys) A B)
    {σ : State (A ⊗ C)} (hσ : IsState σ) :
    operationalTransformationApplyWithAncilla (Sys := Sys) (r • Δ) σ hσ =
      r • operationalTransformationApplyWithAncilla (Sys := Sys) Δ σ hσ := by
  ext
  change transformationApplyWithAncillaQuotientLinearMap (Sys := Sys) σ hσ
      (r • (Δ : TransformationOperationalQuotient (Sys := Sys) A B)) =
    r • transformationApplyWithAncillaQuotientLinearMap (Sys := Sys) σ hσ
      (Δ : TransformationOperationalQuotient (Sys := Sys) A B)
  exact map_smul (transformationApplyWithAncillaQuotientLinearMap (Sys := Sys) σ hσ) r
    (Δ : TransformationOperationalQuotient (Sys := Sys) A B)

end CausalOperationalProbabilisticTheory
end OPT
