/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.Channel.Representations
import Mathlib.Analysis.InnerProductSpace.Trace
import Quantum.QuantumMechanics.Channel.ChoiKraus

/-!
Choi expansion, injectivity, Kraus recovery, and the right partial trace as a Kraus map.
-/

namespace QuantumChannel

open QuantumState
open TensorProduct

universe u v w

section RepresentationsOfChannels

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

theorem choiPositive_of_krausRep
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    KrausRep Φ κ → ChoiPositive b Φ := by
  rintro ⟨A, hA⟩
  have hΦ :
      Φ = ∑ a : κ, krausTerm (A a) := by
    apply LinearMap.ext
    intro X
    simpa [krausTerm] using hA X
  rw [hΦ]
  rw [ChoiPositive, choi_kraus_expansion]
  exact Finset.sum_nonneg fun a _ =>
    outer_product_self_nonneg (vec b (A a))

theorem choiPositive_of_hasKraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasKraus Φ → ChoiPositive b Φ := by
  rintro ⟨κ, hκ, hκ', hΦ⟩
  letI : DecidableEq κ := hκ
  letI : Fintype κ := hκ'
  exact choiPositive_of_krausRep b Φ hΦ

theorem choiPositive_of_hasRankKraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankKraus b Φ → ChoiPositive b Φ :=
  choiPositive_of_hasKraus b Φ ∘
    hasKraus_of_hasRankKraus b Φ

theorem isCompletelyPositive_comp
    {ℋ₃ : Type w} [Qudit ℋ₃]
    (Φ : (L ℋ₁) →ₗ[ℂ] (L ℋ₂)) (Ψ : (L ℋ₂) →ₗ[ℂ] (L ℋ₃))
    (hΦ : IsCompletelyPositive Φ)
    (hΨ : IsCompletelyPositive Ψ) :
    IsCompletelyPositive (Ψ.comp Φ) := by
  refine (isCompletelyPositive_iff_cstarMatrix_nonneg (Ψ.comp Φ)).mpr ?_
  intro k M hM
  rw [← show (M.map Φ).map Ψ = M.map (Ψ.comp Φ) by
    ext i j X
    simp [CStarMatrix.map_apply]]
  exact (isCompletelyPositive_iff_cstarMatrix_nonneg Ψ).mp hΨ k _
    ((isCompletelyPositive_iff_cstarMatrix_nonneg Φ).mp hΦ k M hM)

end RepresentationsOfChannels

end QuantumChannel
