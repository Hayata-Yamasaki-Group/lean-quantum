/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.Channel.ChoiKraus

/-!
Stinespring implications and complete-positivity equivalence closure.
-/

namespace QuantumChannel

open QuantumState
open TensorProduct

universe u v w

section RepresentationsOfChannels

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-! ### Stinespring representations and forward implications -/
/--
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press, 2018), Eq.
(2.71) / Theorem 2.22 / Corollary 2.27. The diagonal specialization A=B of Eq. (2.71) is adopted as
the definition. It packages the diagonal condition of Theorem 2.22, without including the TP
property, isometry, or minimality.
-/
def StinespringRep (Φ : T ℋ₁ ℋ₂) (ℋ₃ : Type u) [Qudit ℋ₃] : Prop :=
  ∃ A : ℋ₁ →ₗ[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃),
    ∀ X : L ℋ₁,
      Φ X =
        (@traceOutRight ℋ₂ inferInstance ℋ₃ inferInstance
          (((A.comp X).comp
            (LinearMap.adjoint A : (ℋ₂ ⊗[ℂ] ℋ₃) →ₗ[ℂ] ℋ₁)) : L (ℋ₂ ⊗[ℂ] ℋ₃)) : L ℋ₂)

/--
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press,
2018), Theorem 2.22. Packaging of the Stinespring condition in Lean. The environment is restricted
to the same universe as the input; the zero map and zero dimensions are also allowed.
-/
def HasStinespring (Φ : T ℋ₁ ℋ₂) : Prop :=
  ∃ (ℋ₃ : Type u) (_ : Qudit ℋ₃), @StinespringRep ℋ₁ ℋ₂ _ _ Φ ℋ₃ _

def HasRankStinespring (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) : Prop :=
  ∃ (ℋ₃ : Type u) (inst : Qudit ℋ₃),
    Module.finrank ℂ ℋ₃ = choiRank b Φ ∧
      @StinespringRep ℋ₁ ℋ₂ _ _ Φ ℋ₃ inst

theorem hasStinespring_of_hasRankStinespring
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankStinespring b Φ → HasStinespring Φ := by
  rintro ⟨ℋ₃, inst, _, hstinespring⟩
  exact ⟨ℋ₃, inst, hstinespring⟩

/--
Source: arXiv:2607.05492v1, the implication from positivity of the amplification to Choi positivity
in §2.B, p.12. Displayed theorem `tensor_to_choi` (no separate number).
-/
theorem choiPositive_of_amplificationPositive
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    AmplificationPositive Φ → ChoiPositive b Φ := by
  intro hΦ
  exact hΦ (outer_product (vec b (I ℋ₁)) (vec b (I ℋ₁)))
    (outer_product_self_nonneg (vec b (I ℋ₁)))

-- (1) → (2)
/--
Source: arXiv:2607.05492v1, the implication from complete positivity to positivity of the
amplification in §2.B, p.12. Displayed theorem
`cp_to_tensor` (no separate number).
-/
theorem amplificationPositive_of_cp
    (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → AmplificationPositive Φ := by
  exact cp_amplify Φ

-- (3) → (5)
/--
Source: arXiv:2607.05492v1, the implication from Choi positivity to a Kraus representation with a
rank condition in §2.B, p.12. Displayed theorem
`choi_to_rank_kraus` (no separate number).
-/
theorem hasRankKraus_of_choiPositive
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    ChoiPositive b Φ → HasRankKraus b Φ := by
  intro hΦ
  obtain ⟨κ, hκ, hκ', hcard, u, hu⟩ :=
    positive_to_rank_outer_product (choi b Φ) hΦ
  letI : DecidableEq κ := hκ
  letI : Fintype κ := hκ'
  refine ⟨κ, hκ, hκ', ?_, ?_⟩
  · exact hcard
  · exact choi_outer_product_to_kraus b Φ u hu

theorem isPositiveMap_of_choiPositive
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    ChoiPositive b Φ → IsPositiveMap Φ :=
  isPositiveMap_of_hasRankKraus b Φ ∘
    hasRankKraus_of_choiPositive b Φ

theorem hasKraus_of_choiPositive
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    ChoiPositive b Φ → HasKraus Φ :=
  hasKraus_of_hasRankKraus b Φ ∘
    hasRankKraus_of_choiPositive b Φ

theorem conjugate_kraus_expansion
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) (X : L ℋ₁) :
    conjugateEnd (TensorProduct.comm ℂ ℋ₂ (EuclideanSpace ℂ κ))
      (((krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A).comp X).comp
        (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A))) =
      ∑ a : κ, ∑ b : κ,
        (endomorphismTensorEquiv (ℋ₁ := EuclideanSpace ℂ κ) (ℋ₂ := ℋ₂)).symm
          ((outer_product (EuclideanSpace.basisFun κ ℂ b) (EuclideanSpace.basisFun κ ℂ a)) ⊗ₜ[ℂ]
            ((A a).comp (X.comp (LinearMap.adjoint (A b))))) := by
  classical
  apply TensorProduct.ext'
  intro z y
  rw [← (EuclideanSpace.basisFun κ ℂ).sum_repr' z]
  simp_rw [TensorProduct.sum_tmul]
  simp_rw [← TensorProduct.smul_tmul']
  simp [map_sum, map_smul,
    conjugateEnd_krausToStinespringOperator_apply_single_tmul,
    endomorphismTensorEquiv_symm_outer_product_apply, EuclideanSpace.basisFun_apply]
  simp [outer_product_eq_rankOne, EuclideanSpace.inner_single_left, ite_tmul_zero_left]

/--
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press,
2018), Proposition 2.20. Partial correspondence to a corollary obtained from the diagonal
specialization A=B=V. Uses a standard finite environment and does not assert cross terms between two
families, isometry, the TP condition, or minimality.
-/
theorem traceOutRight_kraus
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) (X : L ℋ₁) :
    traceOutRight ((((krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A).comp X).comp
      (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A)))) =
      ∑ a : κ, (A a).comp (X.comp (LinearMap.adjoint (A a))) := by
  classical
  dsimp [traceOutRight]
  rw [conjugate_kraus_expansion (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A X]
  simp [traceOutLeft_tmul, trace_outer_product_single, EuclideanSpace.basisFun_apply]

/-- The superoperator induced by the Kraus/Stinespring right-trace construction. -/
noncomputable def krausSuperoperator
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) : T ℋ₁ ℋ₂ where
  toFun X :=
    traceOutRight ((((krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A).comp X).comp
      (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A))))
  map_add' X Y := by
    ext y
    simp [LinearMap.comp_add, LinearMap.add_comp]
  map_smul' c X := by
    ext y
    simp [LinearMap.comp_smul, LinearMap.smul_comp]

lemma isPositiveMap_traceOutRightKraus
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) :
    IsPositiveMap (krausSuperoperator A) := by
  intro X hX
  change 0 ≤ traceOutRight ((((krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A).comp X).comp
    (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A))))
  rw [traceOutRight_kraus (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A X]
  exact Finset.sum_nonneg fun a _ =>
    isPositiveMap_conjugate (ℋ₁ := ℋ₁) (ℋ₃ := ℋ₂) (A a) X hX

/-- The bundled Kraus/Stinespring right-trace map is monotone for the operator order. -/
@[gcongr]
lemma traceOutRightKraus_mono
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) {X Y : L ℋ₁} (hXY : X ≤ Y) :
    krausSuperoperator A X ≤ krausSuperoperator A Y := by
  apply traceOutRight_le_traceOutRight
  exact conjugate_map_le_map
    (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A) hXY

theorem stinespringRep_of_krausRep
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (Φ : T ℋ₁ ℋ₂) :
    KrausRep Φ κ → StinespringRep Φ (EuclideanSpace ℂ κ) := by
  rintro ⟨A, hA⟩
  refine ⟨krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A, ?_⟩
  intro X
  rw [hA X]
  simpa using (traceOutRight_kraus (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A X).symm

-- (4) → (6)
theorem hasStinespring_of_hasKraus
    (Φ : T ℋ₁ ℋ₂) :
    HasKraus Φ → HasStinespring Φ := by
  rintro ⟨κ, hκ, hκ', hΦ⟩
  letI : DecidableEq κ := hκ
  letI : Fintype κ := hκ'
  exact ⟨EuclideanSpace ℂ κ, inferInstance,
    stinespringRep_of_krausRep (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) Φ hΦ⟩

-- (5) → (7)
/--
Source: arXiv:2607.05492v1, the implication from a Kraus representation with a rank condition to a
Stinespring representation in §2.B, p.12. Displayed theorem
`rank_kraus_to_rank_stinespring` (no separate number).
-/
theorem hasRankStinespring_of_hasRankKraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankKraus b Φ → HasRankStinespring b Φ := by
  rintro ⟨κ, hκ, hκ', hcard, hΦ⟩
  letI : DecidableEq κ := hκ
  letI : Fintype κ := hκ'
  refine ⟨EuclideanSpace ℂ κ, inferInstance, ?_, ?_⟩
  · rw [finrank_kraus_environment]
    exact hcard
  · exact stinespringRep_of_krausRep (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) Φ hΦ

theorem hasStinespring_of_choiPositive
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    ChoiPositive b Φ → HasStinespring Φ :=
  hasStinespring_of_hasKraus Φ ∘
    hasKraus_of_choiPositive b Φ

theorem hasRankStinespring_of_choiPositive
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    ChoiPositive b Φ → HasRankStinespring b Φ :=
  hasRankStinespring_of_hasRankKraus b Φ ∘
    hasRankKraus_of_choiPositive b Φ

theorem hasRankKraus_of_amplificationPositive
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    AmplificationPositive Φ → HasRankKraus b Φ :=
  hasRankKraus_of_choiPositive b Φ ∘
    choiPositive_of_amplificationPositive b Φ

theorem hasKraus_of_amplificationPositive
    (Φ : T ℋ₁ ℋ₂) :
    AmplificationPositive Φ → HasKraus Φ := by
  classical
  let b := Module.Free.chooseBasis ℂ ℋ₁
  exact hasKraus_of_choiPositive b Φ ∘
    choiPositive_of_amplificationPositive b Φ

theorem hasStinespring_of_amplificationPositive
    (Φ : T ℋ₁ ℋ₂) :
    AmplificationPositive Φ → HasStinespring Φ :=
  hasStinespring_of_hasKraus Φ ∘
    hasKraus_of_amplificationPositive Φ

theorem hasRankStinespring_of_amplificationPositive
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    AmplificationPositive Φ → HasRankStinespring b Φ :=
  hasRankStinespring_of_choiPositive b Φ ∘
    choiPositive_of_amplificationPositive b Φ

theorem isPositiveMap_of_amplificationPositive
    (Φ : T ℋ₁ ℋ₂) :
    AmplificationPositive Φ → IsPositiveMap Φ :=
  isPositiveMap_of_hasKraus Φ ∘
    hasKraus_of_amplificationPositive Φ

theorem choiPositive_of_cp
    (b : Module.Basis ι ℂ ℋ₁) (Φ : (L ℋ₁) →ₗ[ℂ] (L ℋ₂)) :
    IsCompletelyPositive Φ → ChoiPositive b Φ :=
  choiPositive_of_amplificationPositive b Φ ∘
    amplificationPositive_of_cp Φ

theorem hasRankKraus_of_cp
    (b : Module.Basis ι ℂ ℋ₁) (Φ : (L ℋ₁) →ₗ[ℂ] (L ℋ₂)) :
    IsCompletelyPositive Φ → HasRankKraus b Φ :=
  hasRankKraus_of_choiPositive b Φ ∘
    choiPositive_of_cp b Φ

omit [DecidableEq ι] [Fintype ι] in
theorem hasKraus_of_cp [Finite ι]
    (b : Module.Basis ι ℂ ℋ₁) (Φ : (L ℋ₁) →ₗ[ℂ] (L ℋ₂)) :
    IsCompletelyPositive Φ → HasKraus Φ := by
  classical
  have := Fintype.ofFinite ι
  exact hasKraus_of_hasRankKraus b Φ ∘
    hasRankKraus_of_cp b Φ

omit [DecidableEq ι] [Fintype ι] in
theorem hasStinespring_of_cp [Finite ι]
    (b : Module.Basis ι ℂ ℋ₁) (Φ : (L ℋ₁) →ₗ[ℂ] (L ℋ₂)) :
    IsCompletelyPositive Φ → HasStinespring Φ := by
  classical
  have := Fintype.ofFinite ι
  exact hasStinespring_of_hasKraus Φ ∘
    hasKraus_of_cp b Φ

theorem hasRankStinespring_of_cp
    (b : Module.Basis ι ℂ ℋ₁) (Φ : (L ℋ₁) →ₗ[ℂ] (L ℋ₂)) :
    IsCompletelyPositive Φ → HasRankStinespring b Φ :=
  hasRankStinespring_of_hasRankKraus b Φ ∘
    hasRankKraus_of_cp b Φ

theorem cp_of_hasKraus
    (Φ : (L ℋ₁) →ₗ[ℂ] (L ℋ₂)) :
    HasKraus Φ → IsCompletelyPositive Φ := by
  rintro ⟨κ, hκ, hκ', hΦ⟩
  letI : DecidableEq κ := hκ
  letI : Fintype κ := hκ'
  exact cp_of_krausRep Φ hΦ

theorem cp_of_hasRankKraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : (L ℋ₁) →ₗ[ℂ] (L ℋ₂)) :
    HasRankKraus b Φ → IsCompletelyPositive Φ := by
  intro hΦ
  exact cp_of_hasKraus Φ (hasKraus_of_hasRankKraus b Φ hΦ)

/--
Source: arXiv:2607.05492v1, §2.
-/
theorem cp_iff_tensor
    (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ ↔ AmplificationPositive Φ := by
  refine ⟨amplificationPositive_of_cp Φ, ?_⟩
  intro hTensor
  exact cp_of_hasKraus Φ (hasKraus_of_amplificationPositive Φ hTensor)

/--
Source: arXiv:2607.05492v1, §2.
-/
theorem cp_iff_kraus
    (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ ↔ HasKraus Φ := by
  exact ⟨hasKraus_of_amplificationPositive Φ ∘ amplificationPositive_of_cp Φ,
    cp_of_hasKraus Φ⟩

/--
Source: arXiv:2607.05492v1, §2.
-/
theorem cp_iff_rank_kraus
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis κ ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ ↔ HasRankKraus b Φ := by
  exact ⟨hasRankKraus_of_cp b Φ,
    cp_of_hasRankKraus b Φ⟩

/-! ### Trace-preserving channel representation notes -/
-- Theorem 2.26 https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudits ℋ₁, ℋ₂, and any Φ ∈ T(ℋ₁,ℋ₂), the following statements are equivalent:
-- 1: Φ is a trace-preserving ContinuosLinearMap;
-- 2: traceOutLeft[J(Φ)] = I(ℋ₁);
-- 3: ∃qudit ℋ₃, ∃A,B∈(ℋ₁→L[ℂ]ℋ₂⊗ℋ₃), Φ(X)=Tr₃[A X B†] ∧ A† B = I(ℋ₁)

-- Corollary 2.27 https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudits ℋ₁, ℋ₂, and any Φ ∈ T(ℋ₁,ℋ₂), the following statements are equivalent:
-- 1: Φ ∈ C(ℋ₁,ℋ₂);
-- 2: J(Φ)∈ Pos(ℋ₂⊗ℋ₁) ∧ traceOutLeft[J(Φ)] = I(ℋ₁);
-- 3: ∃qudit ℋ₃, ∃A∈(ℋ₁→L[ℂ]ℋ₂⊗ℋ₃), Φ(X)=Tr₃[A X A†] ∧ A† A = I(ℋ₁)

end RepresentationsOfChannels

end QuantumChannel
