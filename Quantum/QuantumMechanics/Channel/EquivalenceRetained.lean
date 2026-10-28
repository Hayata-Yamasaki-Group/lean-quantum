/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.Channel.ChoiKrausStrongSubadditivity
import Quantum.QuantumMechanics.Channel.ChoiKraus
import Quantum.QuantumMechanics.Channel.Equivalence

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

lemma stinespring_cstarMatrix_nonneg
    {ℋ₃ : Type u} [Qudit ℋ₃]
    (Φ : (L ℋ₁) →ₗ[ℂ] (L ℋ₂)) (hΦ : StinespringRep Φ ℋ₃) :
    ∀ (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) (L ℋ₁)),
      0 ≤ M → 0 ≤ M.map Φ := by
  obtain ⟨A, hA⟩ := hΦ
  let K : T ℋ₁ (ℋ₂ ⊗[ℂ] ℋ₃) := krausTerm A
  have hΦeq : Φ = (traceOutRight (ℋ₂ := ℋ₂) (ℋ₃ := ℋ₃)).comp K := by
    apply LinearMap.ext
    intro X
    rw [hA X]
    simp [K, krausTerm, LinearMap.comp_assoc]
  have hCP : IsCompletelyPositive
      Φ := by
    rw [hΦeq]
    exact isCompletelyPositive_comp K (traceOutRight (ℋ₂ := ℋ₂) (ℋ₃ := ℋ₃))
      (isCompletelyPositive_krausTerm A)
      (cp_traceOutRight (stdOrthonormalBasis ℂ ℋ₃))
  exact (isCompletelyPositive_iff_cstarMatrix_nonneg Φ).mp hCP

theorem choi_iff_rank_kraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    ChoiPositive b Φ ↔ HasRankKraus b Φ := by
  exact ⟨hasRankKraus_of_choiPositive b Φ, choiPositive_of_hasRankKraus b Φ⟩

/--
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press,
2018), Theorem 2.22. Partial correspondence to the equivalence between the Choi and Kraus
conditions. Generalized to an arbitrary algebraic basis, agreeing at the standard basis. The zero
map and zero dimensions are also allowed.
-/
theorem choi_iff_kraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    ChoiPositive b Φ ↔ HasKraus Φ := by
  exact ⟨hasKraus_of_choiPositive b Φ, choiPositive_of_hasKraus b Φ⟩

/-! ### Complete positivity equivalence closure -/
-- (6) → (1)
theorem cp_of_hasStinespring
    (Φ : T ℋ₁ ℋ₂) :
    HasStinespring Φ → IsCompletelyPositive Φ := by
  rintro ⟨ℋ₃, inst, hΦ⟩
  letI : Qudit ℋ₃ := inst
  exact (isCompletelyPositive_iff_cstarMatrix_nonneg Φ).mpr
    (stinespring_cstarMatrix_nonneg Φ hΦ)

omit [DecidableEq ι] [Fintype ι] in
theorem cp_of_amplificationPositive [Finite ι]
    (b : Module.Basis ι ℂ ℋ₁) (Φ : (L ℋ₁) →ₗ[ℂ] (L ℋ₂)) :
    AmplificationPositive Φ → IsCompletelyPositive Φ := by
  classical
  have := Fintype.ofFinite ι
  exact cp_of_hasStinespring Φ ∘
    hasStinespring_of_choiPositive b Φ ∘
    choiPositive_of_amplificationPositive b Φ

theorem cp_of_choiPositive
    (b : Module.Basis ι ℂ ℋ₁) (Φ : (L ℋ₁) →ₗ[ℂ] (L ℋ₂)) :
    ChoiPositive b Φ → IsCompletelyPositive Φ :=
  cp_of_hasStinespring Φ ∘
    hasStinespring_of_hasRankStinespring b Φ ∘
    hasRankStinespring_of_hasRankKraus b Φ ∘
    hasRankKraus_of_choiPositive b Φ

theorem cp_of_hasRankStinespring
    (b : Module.Basis ι ℂ ℋ₁) (Φ : (L ℋ₁) →ₗ[ℂ] (L ℋ₂)) :
    HasRankStinespring b Φ → IsCompletelyPositive Φ :=
  cp_of_hasStinespring Φ ∘
    hasStinespring_of_hasRankStinespring b Φ

/--
Source: arXiv:2607.05492v1, §2.
-/
theorem cp_iff_choi
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis κ ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ ↔ ChoiPositive b Φ := by
  exact ⟨choiPositive_of_cp b Φ, cp_of_choiPositive b Φ⟩

/--
Source: arXiv:2607.05492v1, §2.
-/
theorem cp_iff_stinespring
    (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ ↔ HasStinespring Φ := by
  exact ⟨hasStinespring_of_amplificationPositive Φ ∘ amplificationPositive_of_cp Φ,
    cp_of_hasStinespring Φ⟩

/--
Source: arXiv:2607.05492v1, §2.
-/
theorem cp_iff_rank_stinespring
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis κ ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ ↔ HasRankStinespring b Φ := by
  exact ⟨hasRankStinespring_of_cp b Φ,
    cp_of_hasRankStinespring b Φ⟩

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
