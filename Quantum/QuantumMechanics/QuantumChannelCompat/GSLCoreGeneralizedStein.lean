/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumMechanics.Channel.Stinespring
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCore

/-!
# Quantum channels as linear maps

Linear-map representations of channels and their spectral and norm identities.
-/

namespace QuantumChannel

open QuantumState TensorProduct
universe u v w
variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

lemma Tr₂_l_tensor_equiv_symm_tmul
    (X : L ℋ₁) (Y : L ℋ₂) :
    Tr₂ ((l_tensor_equiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).symm (X ⊗ₜ[ℂ] Y)) = (Tr X) • Y := by
  simp [Tr₂, l_tensor_equiv, endomorphismTensorEquiv]

theorem completelyPositive_to_positiveMap
    (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → IsPositiveMap Φ := by
  rintro ⟨Ψ, rfl⟩ X hX
  exact map_nonneg Ψ hX

lemma krausTerm_isPositiveMap
    (V : ℋ₁ →ₗ[ℂ] ℋ₂) :
    IsPositiveMap (krausTerm V) := by
  intro A hA
  have hAclm : A.toContinuousLinearMap.IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).1 (by simpa using hA)
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).2 <| by
    simpa [krausTerm, LinearMap.comp_assoc, LinearMap.star_eq_adjoint,
      ContinuousLinearMap.coe_comp] using hAclm.conj_adjoint V.toContinuousLinearMap

lemma krausTerm_isCompletelyPositive
    (V : ℋ₁ →ₗ[ℂ] ℋ₂) :
    IsCompletelyPositive (krausTerm V) := by
  refine (isCompletelyPositive_iff_cstarMatrix_nonneg (krausTerm V)).mpr ?_
  intro k M hM
  have hK : IsKPositive k (krausTerm V) := by
    exact (isKPositive_iff_isPositiveMap_ampSuper (k := k) (Φ := krausTerm V)).mpr <| by
      simpa [ampSuper_krausTerm_eq] using
        krausTerm_isPositiveMap (V := ampKrausFactor k V)
  exact hK M hM

lemma sum_krausTerm_isCompletelyPositive
    {σ : Type*} [Fintype σ]
    (V : σ → (ℋ₁ →ₗ[ℂ] ℋ₂)) :
    IsCompletelyPositive (∑ r, krausTerm (V r)) := by
  classical
  refine (isCompletelyPositive_iff_cstarMatrix_nonneg (∑ r, krausTerm (V r))).mpr ?_
  intro k M hM
  have hmap : M.map (∑ r, (krausTerm (V r) : T ℋ₁ ℋ₂)) = ∑ r, M.map (krausTerm (V r)) := by
    have hmapFin (s : Finset σ) :
        M.map (Finset.sum s fun r => (krausTerm (V r) : T ℋ₁ ℋ₂)) =
          Finset.sum s fun r => M.map (krausTerm (V r)) := by
      ext i j x
      induction s using Finset.induction_on with
      | empty =>
          simp [CStarMatrix.map_apply]
      | @insert a s ha ih =>
          simp [Finset.sum_insert, ha, CStarMatrix.map_apply, LinearMap.sum_apply]
          simpa [CStarMatrix.map_apply, LinearMap.sum_apply] using ih
    simpa using hmapFin Finset.univ
  simpa [hmap] using
    (Finset.sum_nonneg fun r _ =>
      (isCompletelyPositive_iff_cstarMatrix_nonneg (krausTerm (V r))).mp
        (krausTerm_isCompletelyPositive (V r)) k M hM)

theorem fixed_kraus_to_cp
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (Φ : T ℋ₁ ℋ₂) :
    KrausRep Φ κ → IsCompletelyPositive Φ := by
  rintro ⟨A, hA⟩
  have hΦ : Φ = ∑ a : κ, krausTerm (A a) := by
    apply LinearMap.ext
    intro X
    simpa [krausTerm] using hA X
  rw [hΦ]
  exact sum_krausTerm_isCompletelyPositive A

theorem hasRankKraus_to_hasKraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankKraus b Φ → HasKraus Φ := by
  rintro ⟨κ, dec, inst, _, hkraus⟩
  exact ⟨κ, dec, inst, hkraus⟩

theorem rankKraus_to_kraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankKraus b Φ → HasKraus Φ :=
  hasRankKraus_to_hasKraus b Φ

theorem comp_isCompletelyPositive
    {ℋ₃ : Type w} [Qudit ℋ₃]
    (Φ : T ℋ₁ ℋ₂) (Ψ : T ℋ₂ ℋ₃)
    (hΦ : IsCompletelyPositive Φ) (hΨ : IsCompletelyPositive Ψ) :
    IsCompletelyPositive (Ψ.comp Φ) := by
  refine (isCompletelyPositive_iff_cstarMatrix_nonneg (Ψ.comp Φ)).mpr ?_
  intro k M hM
  have hΦM :
      0 ≤ M.map Φ :=
    (isCompletelyPositive_iff_cstarMatrix_nonneg Φ).mp hΦ k M hM
  have hΨM :
      0 ≤ (M.map Φ).map Ψ :=
    (isCompletelyPositive_iff_cstarMatrix_nonneg Ψ).mp hΨ k (M.map Φ) hΦM
  have hmap : (M.map Φ).map Ψ = M.map (Ψ.comp Φ) := by
    ext i j X
    simp [CStarMatrix.map_apply]
  simpa [hmap] using hΨM

theorem tensor_to_choi
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    AmplificationPositive Φ → ChoiPositive b Φ := by
  intro hΦ
  exact hΦ (outer_product (vec b (I ℋ₁)) (vec b (I ℋ₁)))
    (outer_product_self_nonneg (vec b (I ℋ₁)))

theorem cp_to_tensor
    (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → AmplificationPositive Φ := by
  exact cp_amplify Φ

theorem choi_to_rank_kraus
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

theorem cp_to_choi
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → ChoiPositive b Φ :=
  tensor_to_choi b Φ ∘
    cp_to_tensor Φ

theorem cp_to_rank_kraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → HasRankKraus b Φ :=
  choi_to_rank_kraus b Φ ∘
    cp_to_choi b Φ

omit [DecidableEq ι] [Fintype ι] in
theorem cp_to_kraus [Finite ι]
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    IsCompletelyPositive Φ → HasKraus Φ := by
  classical
  have := Fintype.ofFinite ι
  exact rankKraus_to_kraus b Φ ∘
    cp_to_rank_kraus b Φ

end QuantumChannel
