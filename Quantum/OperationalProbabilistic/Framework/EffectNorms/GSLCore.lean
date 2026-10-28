/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.StateNorms.GSLCore

open CategoryTheory
open scoped MonoidalCategory

/-!
# Operational framework: the operational state norm

The operational state norm `operationalStateNorm` is built from the suprema and infima of
evaluation ranges over bounded effects; boundedness of those ranges
(`operationalStateNorm_evalRange_bdd`) makes it well defined.  Nonnegativity, homogeneity
(`operationalStateNorm_smul`) and subadditivity (`operationalStateNorm_add_le`) are proved,
together with a bound by binary-observation differences.
-/

namespace OPT

universe u v w

section CausalOperationalProbabilisticTheory

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]

variable [Preadditive Sys]

variable [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]

variable [CausalOperationalProbabilisticTheory Sys]

/-- The state-norm evaluation range of the zero class is bounded above and below. -/
private theorem operationalStateNormEvalRange_bdd_zero (A : Sys) :
    BddAbove (operationalStateNormEvalRange (Sys := Sys)
      (0 : StateOperationalQuotient (Sys := Sys) A)) ∧
    BddBelow (operationalStateNormEvalRange (Sys := Sys)
      (0 : StateOperationalQuotient (Sys := Sys) A)) := by
  constructor
  · refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨a, _ha_univ, rfl⟩
    simp
  · refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨a, _ha_univ, rfl⟩
    simp

/-- Boundedness above and below of the state-norm evaluation range is preserved under addition. -/
private theorem operationalStateNormEvalRange_bdd_add {A : Sys}
    {δ ε : StateOperationalQuotient (Sys := Sys) A}
    (hδ : BddAbove (operationalStateNormEvalRange (Sys := Sys) δ) ∧
      BddBelow (operationalStateNormEvalRange (Sys := Sys) δ))
    (hε : BddAbove (operationalStateNormEvalRange (Sys := Sys) ε) ∧
      BddBelow (operationalStateNormEvalRange (Sys := Sys) ε)) :
    BddAbove (operationalStateNormEvalRange (Sys := Sys) (δ + ε)) ∧
    BddBelow (operationalStateNormEvalRange (Sys := Sys) (δ + ε)) := by
  rcases hδ with ⟨⟨uδ, huδ⟩, ⟨lδ, hlδ⟩⟩
  rcases hε with ⟨⟨uε, huε⟩, ⟨lε, hlε⟩⟩
  constructor
  · refine ⟨uδ + uε, ?_⟩
    intro y hy
    rcases hy with ⟨a, _ha_univ, rfl⟩
    simpa [stateOperationalQuotientEval_add] using add_le_add
      (huδ ⟨a, trivial, rfl⟩)
      (huε ⟨a, trivial, rfl⟩)
  · refine ⟨lδ + lε, ?_⟩
    intro y hy
    rcases hy with ⟨a, _ha_univ, rfl⟩
    simpa [stateOperationalQuotientEval_add] using add_le_add
      (hlδ ⟨a, trivial, rfl⟩)
      (hlε ⟨a, trivial, rfl⟩)

/-- Boundedness above and below of the state-norm evaluation range is preserved under scalar
multiplication.
-/
private theorem operationalStateNormEvalRange_bdd_smul {A : Sys}
    (r : ℝ) {δ : StateOperationalQuotient (Sys := Sys) A}
    (hδ : BddAbove (operationalStateNormEvalRange (Sys := Sys) δ) ∧
      BddBelow (operationalStateNormEvalRange (Sys := Sys) δ)) :
    BddAbove (operationalStateNormEvalRange (Sys := Sys) (r • δ)) ∧
    BddBelow (operationalStateNormEvalRange (Sys := Sys) (r • δ)) := by
  rcases hδ with ⟨⟨u, hu⟩, ⟨l, hl⟩⟩
  by_cases hr : 0 ≤ r
  · constructor
    · refine ⟨r * u, ?_⟩
      intro y hy
      rcases hy with ⟨a, _ha_univ, rfl⟩
      simpa [stateOperationalQuotientEval_smul] using mul_le_mul_of_nonneg_left
        (hu ⟨a, trivial, rfl⟩) hr
    · refine ⟨r * l, ?_⟩
      intro y hy
      rcases hy with ⟨a, _ha_univ, rfl⟩
      simpa [stateOperationalQuotientEval_smul] using mul_le_mul_of_nonneg_left
        (hl ⟨a, trivial, rfl⟩) hr
  · have hrle : r ≤ 0 := le_of_not_ge hr
    constructor
    · refine ⟨r * l, ?_⟩
      intro y hy
      rcases hy with ⟨a, _ha_univ, rfl⟩
      simpa [stateOperationalQuotientEval_smul] using mul_le_mul_of_nonpos_left
        (hl ⟨a, trivial, rfl⟩) hrle
    · refine ⟨r * u, ?_⟩
      intro y hy
      rcases hy with ⟨a, _ha_univ, rfl⟩
      simpa [stateOperationalQuotientEval_smul] using mul_le_mul_of_nonpos_left
        (hu ⟨a, trivial, rfl⟩) hrle

/-- The state-side operational-norm evaluation range is bounded on every
operational real state class. -/
theorem operationalStateNorm_evalRange_bdd {A : Sys}
    (δ : OperationalStateSpaceReal (Sys := Sys) A) :
    BddAbove (operationalStateNormEvalRange (Sys := Sys)
      (δ : StateOperationalQuotient (Sys := Sys) A)) ∧
    BddBelow (operationalStateNormEvalRange (Sys := Sys)
      (δ : StateOperationalQuotient (Sys := Sys) A)) := by
  exact Submodule.span_induction
    (p := fun x _ =>
      BddAbove (operationalStateNormEvalRange (Sys := Sys) x) ∧
      BddBelow (operationalStateNormEvalRange (Sys := Sys) x))
    (fun x hx => by
      rcases hx with ⟨ρ, hρ, rfl⟩
      constructor
      · simpa [operationalStateNormEvalRange] using
          operationalStateNorm_evalRange_bddAbove_of_isState (Sys := Sys) hρ
      · simpa [operationalStateNormEvalRange] using
          operationalStateNorm_evalRange_bddBelow_of_isState (Sys := Sys) hρ)
    (operationalStateNormEvalRange_bdd_zero (Sys := Sys) A)
    (fun _ _ _ _ hδ hε => operationalStateNormEvalRange_bdd_add (Sys := Sys) hδ hε)
    (fun r _ _ hδ => operationalStateNormEvalRange_bdd_smul (Sys := Sys) r hδ)
    δ.2

/-- The state-side operational-norm evaluation range is bounded above on every
operational real state class. -/
theorem operationalStateNorm_evalRange_bddAbove {A : Sys}
    (δ : OperationalStateSpaceReal (Sys := Sys) A) :
    BddAbove (operationalStateNormEvalRange (Sys := Sys)
      (δ : StateOperationalQuotient (Sys := Sys) A)) :=
  (operationalStateNorm_evalRange_bdd (Sys := Sys) δ).1

/-- The state-side operational-norm evaluation range is bounded below on every
operational real state class. -/
theorem operationalStateNorm_evalRange_bddBelow {A : Sys}
    (δ : OperationalStateSpaceReal (Sys := Sys) A) :
    BddBelow (operationalStateNormEvalRange (Sys := Sys)
      (δ : StateOperationalQuotient (Sys := Sys) A)) :=
  (operationalStateNorm_evalRange_bdd (Sys := Sys) δ).2

/-- CDP operational norm formula on the quotient-generated real state space. -/
noncomputable def operationalStateNorm {A : Sys} (δ : OperationalStateSpaceReal A) : ℝ :=
  sSup (operationalStateNormEvalRange (Sys := Sys)
      (δ : StateOperationalQuotient (Sys := Sys) A)) -
    sInf (operationalStateNormEvalRange (Sys := Sys)
      (δ : StateOperationalQuotient (Sys := Sys) A))

/-- The state-side operational norm formula is nonnegative. -/
theorem operationalStateNorm_nonneg {A : Sys} (δ : OperationalStateSpaceReal A) :
    0 ≤ operationalStateNorm (Sys := Sys) δ := by
  unfold operationalStateNorm
  exact sub_nonneg.mpr
    (Real.sInf_le_sSup _
      (operationalStateNorm_evalRange_bddBelow (Sys := Sys) δ)
      (operationalStateNorm_evalRange_bddAbove (Sys := Sys) δ))

/-- For a nonnegative scalar, the supremum of the state-norm evaluation range scales by that
scalar.
-/
private theorem operationalStateNorm_sSup_smul_of_nonneg {A : Sys} (r : ℝ) (hr : 0 ≤ r)
    (δ : OperationalStateSpaceReal A) :
    sSup (operationalStateNormEvalRange (Sys := Sys)
      ((r • δ : OperationalStateSpaceReal A) : StateOperationalQuotient (Sys := Sys) A)) =
    r * sSup (operationalStateNormEvalRange (Sys := Sys)
      (δ : StateOperationalQuotient (Sys := Sys) A)) := by
  unfold operationalStateNormEvalRange
  rw [Set.image_univ, Set.image_univ]
  change sSup (Set.range (fun a : {a : Effect A // IsBoundedEffect a} =>
      stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1
        (r • (δ : StateOperationalQuotient (Sys := Sys) A)))) =
    r * sSup (Set.range (fun a : {a : Effect A // IsBoundedEffect a} =>
      stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1
        (δ : StateOperationalQuotient (Sys := Sys) A)))
  simp_rw [stateOperationalQuotientEval_smul]
  rw [sSup_range, sSup_range]
  exact (Real.mul_iSup_of_nonneg hr _).symm

/-- For a nonnegative scalar, the infimum of the state-norm evaluation range scales by that scalar.
-/
private theorem operationalStateNorm_sInf_smul_of_nonneg {A : Sys} (r : ℝ) (hr : 0 ≤ r)
    (δ : OperationalStateSpaceReal A) :
    sInf (operationalStateNormEvalRange (Sys := Sys)
      ((r • δ : OperationalStateSpaceReal A) : StateOperationalQuotient (Sys := Sys) A)) =
    r * sInf (operationalStateNormEvalRange (Sys := Sys)
      (δ : StateOperationalQuotient (Sys := Sys) A)) := by
  unfold operationalStateNormEvalRange
  rw [Set.image_univ, Set.image_univ]
  change sInf (Set.range (fun a : {a : Effect A // IsBoundedEffect a} =>
      stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1
        (r • (δ : StateOperationalQuotient (Sys := Sys) A)))) =
    r * sInf (Set.range (fun a : {a : Effect A // IsBoundedEffect a} =>
      stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1
        (δ : StateOperationalQuotient (Sys := Sys) A)))
  simp_rw [stateOperationalQuotientEval_smul]
  rw [sInf_range, sInf_range]
  exact (Real.mul_iInf_of_nonneg hr _).symm

/-- For a nonpositive scalar, the supremum of the scaled state-norm evaluation range equals the
scalar times the infimum of the original range.
-/
private theorem operationalStateNorm_sSup_smul_of_nonpos {A : Sys} (r : ℝ) (hr : r ≤ 0)
    (δ : OperationalStateSpaceReal A) :
    sSup (operationalStateNormEvalRange (Sys := Sys)
      ((r • δ : OperationalStateSpaceReal A) : StateOperationalQuotient (Sys := Sys) A)) =
    r * sInf (operationalStateNormEvalRange (Sys := Sys)
      (δ : StateOperationalQuotient (Sys := Sys) A)) := by
  unfold operationalStateNormEvalRange
  rw [Set.image_univ, Set.image_univ]
  change sSup (Set.range (fun a : {a : Effect A // IsBoundedEffect a} =>
      stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1
        (r • (δ : StateOperationalQuotient (Sys := Sys) A)))) =
    r * sInf (Set.range (fun a : {a : Effect A // IsBoundedEffect a} =>
      stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1
        (δ : StateOperationalQuotient (Sys := Sys) A)))
  simp_rw [stateOperationalQuotientEval_smul]
  rw [sSup_range, sInf_range]
  exact (Real.mul_iInf_of_nonpos hr _).symm

/-- For a nonpositive scalar, the infimum of the scaled state-norm evaluation range equals the
scalar times the supremum of the original range.
-/
private theorem operationalStateNorm_sInf_smul_of_nonpos {A : Sys} (r : ℝ) (hr : r ≤ 0)
    (δ : OperationalStateSpaceReal A) :
    sInf (operationalStateNormEvalRange (Sys := Sys)
      ((r • δ : OperationalStateSpaceReal A) : StateOperationalQuotient (Sys := Sys) A)) =
    r * sSup (operationalStateNormEvalRange (Sys := Sys)
      (δ : StateOperationalQuotient (Sys := Sys) A)) := by
  unfold operationalStateNormEvalRange
  rw [Set.image_univ, Set.image_univ]
  change sInf (Set.range (fun a : {a : Effect A // IsBoundedEffect a} =>
      stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1
        (r • (δ : StateOperationalQuotient (Sys := Sys) A)))) =
    r * sSup (Set.range (fun a : {a : Effect A // IsBoundedEffect a} =>
      stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1
        (δ : StateOperationalQuotient (Sys := Sys) A)))
  simp_rw [stateOperationalQuotientEval_smul]
  rw [sInf_range, sSup_range]
  exact (Real.mul_iSup_of_nonpos hr _).symm

/-- The state-side operational norm formula is homogeneous. -/
theorem operationalStateNorm_smul {A : Sys} (r : ℝ) (δ : OperationalStateSpaceReal A) :
    operationalStateNorm (Sys := Sys) (r • δ) =
      |r| * operationalStateNorm (Sys := Sys) δ := by
  by_cases hr : 0 ≤ r
  · unfold operationalStateNorm
    rw [operationalStateNorm_sSup_smul_of_nonneg (Sys := Sys) r hr δ,
      operationalStateNorm_sInf_smul_of_nonneg (Sys := Sys) r hr δ,
      abs_of_nonneg hr]
    ring
  · have hrle : r ≤ 0 := le_of_not_ge hr
    unfold operationalStateNorm
    rw [operationalStateNorm_sSup_smul_of_nonpos (Sys := Sys) r hrle δ,
      operationalStateNorm_sInf_smul_of_nonpos (Sys := Sys) r hrle δ,
      abs_of_nonpos hrle]
    ring

/-- The state-side operational norm formula satisfies the triangle inequality. -/
theorem operationalStateNorm_add_le {A : Sys}
    (δ ε : OperationalStateSpaceReal A) :
    operationalStateNorm (Sys := Sys) (δ + ε) ≤
      operationalStateNorm (Sys := Sys) δ + operationalStateNorm (Sys := Sys) ε := by
  let Sδ := operationalStateNormEvalRange (Sys := Sys)
    (δ : StateOperationalQuotient (Sys := Sys) A)
  let Sε := operationalStateNormEvalRange (Sys := Sys)
    (ε : StateOperationalQuotient (Sys := Sys) A)
  let Ssum := operationalStateNormEvalRange (Sys := Sys)
    ((δ + ε : OperationalStateSpaceReal A) : StateOperationalQuotient (Sys := Sys) A)
  have hsup : sSup Ssum ≤ sSup Sδ + sSup Sε := by
    refine csSup_le (operationalStateNorm_evalRange_nonempty (Sys := Sys) (δ + ε)) ?_
    intro y hy
    rcases hy with ⟨a, _ha_univ, rfl⟩
    have hδ : stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1
        (δ : StateOperationalQuotient (Sys := Sys) A) ≤ sSup Sδ := by
      exact le_csSup (operationalStateNorm_evalRange_bddAbove (Sys := Sys) δ)
        ⟨a, trivial, rfl⟩
    have hε : stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1
        (ε : StateOperationalQuotient (Sys := Sys) A) ≤ sSup Sε := by
      exact le_csSup (operationalStateNorm_evalRange_bddAbove (Sys := Sys) ε)
        ⟨a, trivial, rfl⟩
    simpa [Sδ, Sε, Ssum, stateOperationalQuotientEval_add] using add_le_add hδ hε
  have hinf : sInf Sδ + sInf Sε ≤ sInf Ssum := by
    refine le_csInf (operationalStateNorm_evalRange_nonempty (Sys := Sys) (δ + ε)) ?_
    intro y hy
    rcases hy with ⟨a, _ha_univ, rfl⟩
    have hδ : sInf Sδ ≤ stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1
        (δ : StateOperationalQuotient (Sys := Sys) A) := by
      exact csInf_le (operationalStateNorm_evalRange_bddBelow (Sys := Sys) δ)
        ⟨a, trivial, rfl⟩
    have hε : sInf Sε ≤ stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1
        (ε : StateOperationalQuotient (Sys := Sys) A) := by
      exact csInf_le (operationalStateNorm_evalRange_bddBelow (Sys := Sys) ε)
        ⟨a, trivial, rfl⟩
    simpa [Sδ, Sε, Ssum, stateOperationalQuotientEval_add] using add_le_add hδ hε
  unfold operationalStateNorm
  change sSup Ssum - sInf Ssum ≤ (sSup Sδ - sInf Sδ) + (sSup Sε - sInf Sε)
  calc
    sSup Ssum - sInf Ssum ≤ (sSup Sδ + sSup Sε) - (sInf Sδ + sInf Sε) :=
      sub_le_sub hsup hinf
    _ = (sSup Sδ - sInf Sδ) + (sSup Sε - sInf Sε) := by ring

/-- If every signed binary observation-test evaluation is bounded by `K`, then
the state-side operational norm is bounded by `K`. -/
theorem operationalStateNorm_le_of_forall_binaryObservationDiff_le {A : Sys}
    (η : OperationalStateSpaceReal (Sys := Sys) A) (K : ℝ)
    (hK : ∀ M : BinaryObservationTest (Sys := Sys) A,
      binaryObservationDiffEval (Sys := Sys) M η ≤ K) :
    operationalStateNorm (Sys := Sys) η ≤ K := by
  let S : Set ℝ := operationalStateNormEvalRange (Sys := Sys)
    (η : StateOperationalQuotient (Sys := Sys) A)
  let eη : ℝ := stateOperationalQuotientEval (Sys := Sys) (detEffect A)
    (detEffect_isEffect (Sys := Sys) A) η
  have hupper_each : ∀ a : {a : Effect A // IsBoundedEffect a},
      stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1
        (η : StateOperationalQuotient (Sys := Sys) A) ≤ (eη + K) / 2 := by
    intro a
    rcases binaryObservationTest_of_effect_as_one (Sys := Sys) a.1 a.2.1 with ⟨M, hM⟩
    let b : Effect A := M.outcome BinaryObservationIndex.zero
    have hb : IsEffect b :=
      binaryObservation_outcome_isEffect (Sys := Sys) M BinaryObservationIndex.zero
    have hone : IsEffect (M.outcome BinaryObservationIndex.one) :=
      binaryObservation_outcome_isEffect (Sys := Sys) M BinaryObservationIndex.one
    have hsum : b + M.outcome BinaryObservationIndex.one = detEffect A := by
      simpa [b] using binaryObservation_total_eq_detEffect (Sys := Sys) M
    have hsumEff : IsEffect (b + M.outcome BinaryObservationIndex.one) := by
      simpa [hsum] using detEffect_isEffect (Sys := Sys) A
    have heval_sum : eη =
        stateOperationalQuotientEval (Sys := Sys) b hb η +
          stateOperationalQuotientEval (Sys := Sys)
            (M.outcome BinaryObservationIndex.one) hone η := by
      dsimp [eη]
      calc
        stateOperationalQuotientEval (Sys := Sys) (detEffect A)
            (detEffect_isEffect (Sys := Sys) A) η =
          stateOperationalQuotientEval (Sys := Sys)
            (b + M.outcome BinaryObservationIndex.one) hsumEff η :=
            stateOperationalQuotientEval_congr_effect (Sys := Sys) hsum.symm
              (detEffect_isEffect (Sys := Sys) A) hsumEff η
        _ = stateOperationalQuotientEval (Sys := Sys) b hb η +
              stateOperationalQuotientEval (Sys := Sys)
                (M.outcome BinaryObservationIndex.one) hone η :=
            stateOperationalQuotientEval_add_effect (Sys := Sys) b
              (M.outcome BinaryObservationIndex.one) hb hone hsumEff η
    have hdiff :
        stateOperationalQuotientEval (Sys := Sys)
            (M.outcome BinaryObservationIndex.one) hone η -
          stateOperationalQuotientEval (Sys := Sys) b hb η ≤ K := by
      simpa [binaryObservationDiffEval, b] using hK M
    have hone_eval_eq :
        stateOperationalQuotientEval (Sys := Sys)
            (M.outcome BinaryObservationIndex.one) hone η =
          stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1 η :=
      stateOperationalQuotientEval_congr_effect (Sys := Sys) hM hone a.2.1 η
    rw [← hone_eval_eq]
    linarith
  have hlower_each : ∀ a : {a : Effect A // IsBoundedEffect a},
      (eη - K) / 2 ≤ stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1
        (η : StateOperationalQuotient (Sys := Sys) A) := by
    intro a
    rcases binaryObservationTest_of_effect_as_zero (Sys := Sys) a.1 a.2.1 with ⟨M, hM⟩
    let b : Effect A := M.outcome BinaryObservationIndex.one
    have hzero : IsEffect (M.outcome BinaryObservationIndex.zero) :=
      binaryObservation_outcome_isEffect (Sys := Sys) M BinaryObservationIndex.zero
    have hb : IsEffect b :=
      binaryObservation_outcome_isEffect (Sys := Sys) M BinaryObservationIndex.one
    have hsum : M.outcome BinaryObservationIndex.zero + b = detEffect A := by
      simpa [b] using binaryObservation_total_eq_detEffect (Sys := Sys) M
    have hsumEff : IsEffect (M.outcome BinaryObservationIndex.zero + b) := by
      simpa [hsum] using detEffect_isEffect (Sys := Sys) A
    have heval_sum : eη =
        stateOperationalQuotientEval (Sys := Sys)
            (M.outcome BinaryObservationIndex.zero) hzero η +
          stateOperationalQuotientEval (Sys := Sys) b hb η := by
      dsimp [eη]
      calc
        stateOperationalQuotientEval (Sys := Sys) (detEffect A)
            (detEffect_isEffect (Sys := Sys) A) η =
          stateOperationalQuotientEval (Sys := Sys)
            (M.outcome BinaryObservationIndex.zero + b) hsumEff η :=
            stateOperationalQuotientEval_congr_effect (Sys := Sys) hsum.symm
              (detEffect_isEffect (Sys := Sys) A) hsumEff η
        _ = stateOperationalQuotientEval (Sys := Sys)
              (M.outcome BinaryObservationIndex.zero) hzero η +
              stateOperationalQuotientEval (Sys := Sys) b hb η :=
            stateOperationalQuotientEval_add_effect (Sys := Sys)
              (M.outcome BinaryObservationIndex.zero) b hzero hb hsumEff η
    have hdiff :
        stateOperationalQuotientEval (Sys := Sys) b hb η -
          stateOperationalQuotientEval (Sys := Sys)
            (M.outcome BinaryObservationIndex.zero) hzero η ≤ K := by
      simpa [binaryObservationDiffEval, b] using hK M
    have hzero_eval_eq :
        stateOperationalQuotientEval (Sys := Sys)
            (M.outcome BinaryObservationIndex.zero) hzero η =
          stateOperationalQuotientEval (Sys := Sys) a.1 a.2.1 η :=
      stateOperationalQuotientEval_congr_effect (Sys := Sys) hM hzero a.2.1 η
    rw [← hzero_eval_eq]
    linarith
  have hsup : sSup S ≤ (eη + K) / 2 := by
    refine csSup_le (operationalStateNorm_evalRange_nonempty (Sys := Sys) η) ?_
    intro y hy
    rcases hy with ⟨a, _ha_univ, rfl⟩
    exact hupper_each a
  have hinf : (eη - K) / 2 ≤ sInf S := by
    refine le_csInf (operationalStateNorm_evalRange_nonempty (Sys := Sys) η) ?_
    intro y hy
    rcases hy with ⟨a, _ha_univ, rfl⟩
    exact hlower_each a
  unfold operationalStateNorm
  change sSup S - sInf S ≤ K
  calc
    sSup S - sInf S ≤ (eη + K) / 2 - (eη - K) / 2 :=
      sub_le_sub hsup hinf
    _ = K := by ring

end CausalOperationalProbabilisticTheory
end OPT
