/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.Channel.Representations
import Mathlib.Analysis.InnerProductSpace.Trace

-- Choi--Kraus lemmas retain the finite-index binders used by `KrausRep`.
-- Suppress type-only unused-binder checks for these explicit instances.
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

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

/-! ### Choi expansion, injectivity, and Kraus recovery -/
lemma endomorphismTensorEquiv_symm_outer_product
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (u v : E) (x y : F) :
    (endomorphismTensorEquiv (ℋ₁ := E) (ℋ₂ := F)).symm
      ((outer_product u v) ⊗ₜ[ℂ] (outer_product x y)) =
        outer_product (u ⊗ₜ[ℂ] x) (v ⊗ₜ[ℂ] y) := by
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro a b
    simp [endomorphismTensorEquiv, outer_product, TensorProduct.inner_tmul, smul_tmul']
  · intro z₁ z₂ hz₁ hz₂
    simp [hz₁, hz₂]

@[deprecated endomorphismTensorEquiv_symm_outer_product (since := "2026-09-26")]
alias l_tensor_equiv_symm_outer_product := endomorphismTensorEquiv_symm_outer_product

lemma endomorphismTensorEquiv_outer_product_tmul
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (u v : E) (x y : F) :
    (endomorphismTensorEquiv (ℋ₁ := E) (ℋ₂ := F))
      (outer_product (u ⊗ₜ[ℂ] x) (v ⊗ₜ[ℂ] y)) =
        (outer_product u v) ⊗ₜ[ℂ] (outer_product x y) := by
  apply (endomorphismTensorEquiv (ℋ₁ := E) (ℋ₂ := F)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (endomorphismTensorEquiv_symm_outer_product (E := E) (F := F) u v x y).symm

@[deprecated endomorphismTensorEquiv_outer_product_tmul (since := "2026-09-26")]
alias l_tensor_equiv_outer_product_tmul := endomorphismTensorEquiv_outer_product_tmul

/--
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press, 2018), Eq.
(2.65). Generalization to an arbitrary algebraic basis, agreeing upon specialization to the standard
basis.
-/
lemma choi_basis_expansion
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    choi b Φ =
      ∑ i : ι, ∑ j : ι,
        (endomorphismTensorEquiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
          ((Φ (outer_product (b i) (b j))) ⊗ₜ[ℂ] outer_product (b i) (b j)) := by
  rw [choi, vec_apply]
  simp only [I, LinearMap.id_coe, id_eq]
  change (endomorphismTensorEquiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
      ((TensorProduct.map Φ LinearMap.id)
        ((endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
          (outer_product (∑ i : ι, b i ⊗ₜ[ℂ] b i) (∑ i : ι, b i ⊗ₜ[ℂ] b i)))) =
    ∑ i : ι, ∑ j : ι,
      (endomorphismTensorEquiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
        ((Φ (outer_product (b i) (b j))) ⊗ₜ[ℂ] outer_product (b i) (b j))
  rw [show outer_product (∑ i : ι, b i ⊗ₜ[ℂ] b i) (∑ i : ι, b i ⊗ₜ[ℂ] b i) =
      ∑ i : ι, ∑ j : ι, outer_product (b i ⊗ₜ[ℂ] b i) (b j ⊗ₜ[ℂ] b j) by
    exact outer_product_sum (fun i : ι => b i ⊗ₜ[ℂ] b i) (fun i : ι => b i ⊗ₜ[ℂ] b i)]
  simp only [map_sum]
  simp_rw [endomorphismTensorEquiv_outer_product_tmul]
  simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq]

lemma tensor_basis_sum_coeff
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b : Module.Basis ι ℂ E) (p q : ι) (S : ι → ι → L F) :
    (TensorProduct.rid ℂ (L F) : (L F ⊗[ℂ] ℂ) →ₗ[ℂ] L F)
      ((TensorProduct.map LinearMap.id
        { toFun := fun X : L E =>
            b.coord q (X ((InnerProductSpace.toDual ℂ E).symm ((b.coord p).toContinuousLinearMap)))
          map_add' := by intro X Y; simp
          map_smul' := by intro c X; simp })
        (∑ i : ι, ∑ j : ι, S i j ⊗ₜ[ℂ] outer_product (b i) (b j))) =
      S p q := by
  classical
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · have hcoeff :
          (b.repr ((outer_product (b p) (b q))
            ((InnerProductSpace.toDual ℂ E).symm
              (LinearMap.toContinuousLinearMap (b.coord p))))) q = 1 := by
          simpa using (basis_outer_coeff b p q p q)
      simp [Module.Basis.coord_apply, hcoeff]
    · intro j _ hjq
      have hcoeff :
          (b.repr ((outer_product (b p) (b j))
            ((InnerProductSpace.toDual ℂ E).symm
              (LinearMap.toContinuousLinearMap (b.coord p))))) q = 0 := by
          simpa [hjq] using (basis_outer_coeff b p q p j)
      simp [Module.Basis.coord_apply, hcoeff]
    · intro hq
      simp at hq
  · intro i _ hip
    apply Finset.sum_eq_zero
    intro j _
    have hcoeff :
        (b.repr ((outer_product (b i) (b j))
          ((InnerProductSpace.toDual ℂ E).symm
            (LinearMap.toContinuousLinearMap (b.coord p))))) q = 0 := by
        simpa [hip] using (basis_outer_coeff b p q i j)
    simp [Module.Basis.coord_apply, hcoeff]
  · intro hp
    simp at hp

lemma choi_basis_apply_eq_of_choi_eq
    (b : Module.Basis ι ℂ ℋ₁) {Φ Ψ : T ℋ₁ ℋ₂}
    (h : choi b Φ = choi b Ψ) (i j : ι) :
    Φ (outer_product (b i) (b j)) = Ψ (outer_product (b i) (b j)) := by
  have htensor :
      (∑ p : ι, ∑ q : ι,
        Φ (outer_product (b p) (b q)) ⊗ₜ[ℂ] outer_product (b p) (b q)) =
      (∑ p : ι, ∑ q : ι,
        Ψ (outer_product (b p) (b q)) ⊗ₜ[ℂ] outer_product (b p) (b q)) := by
    have h' := congrArg (endomorphismTensorEquiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)) h
    simpa [choi_basis_expansion] using h'
  calc
    Φ (outer_product (b i) (b j)) =
        (TensorProduct.rid ℂ (L ℋ₂) : (L ℋ₂ ⊗[ℂ] ℂ) →ₗ[ℂ] L ℋ₂)
          ((TensorProduct.map LinearMap.id
            { toFun := fun X : L ℋ₁ =>
                b.coord j
                  (X ((InnerProductSpace.toDual ℂ ℋ₁).symm ((b.coord i).toContinuousLinearMap)))
              map_add' := by intro X Y; simp
              map_smul' := by intro c X; simp })
            (∑ p : ι, ∑ q : ι,
              Φ (outer_product (b p) (b q)) ⊗ₜ[ℂ] outer_product (b p) (b q))) := by
          exact (tensor_basis_sum_coeff b i j
            (fun p q => Φ (outer_product (b p) (b q)))).symm
    _ =
        (TensorProduct.rid ℂ (L ℋ₂) : (L ℋ₂ ⊗[ℂ] ℂ) →ₗ[ℂ] L ℋ₂)
          ((TensorProduct.map LinearMap.id
            { toFun := fun X : L ℋ₁ =>
                b.coord j
                  (X ((InnerProductSpace.toDual ℂ ℋ₁).symm ((b.coord i).toContinuousLinearMap)))
              map_add' := by intro X Y; simp
              map_smul' := by intro c X; simp })
            (∑ p : ι, ∑ q : ι,
              Ψ (outer_product (b p) (b q)) ⊗ₜ[ℂ] outer_product (b p) (b q))) := by
          rw [htensor]
    _ = Ψ (outer_product (b i) (b j)) := by
          exact tensor_basis_sum_coeff b i j
            (fun p q => Ψ (outer_product (b p) (b q)))

lemma choi_injective
    (b : Module.Basis ι ℂ ℋ₁) :
    Function.Injective (choi b : T ℋ₁ ℋ₂ → L (ℋ₂ ⊗[ℂ] ℋ₁)) := by
  intro Φ Ψ h
  apply LinearMap.ext
  intro X
  conv_lhs => rw [linearMap_eq_sum_basis_outer_product b X]
  conv_rhs => rw [linearMap_eq_sum_basis_outer_product b X]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [choi_basis_apply_eq_of_choi_eq b h i j]

lemma outer_product_vec_expansion
    (b : Module.Basis ι ℂ ℋ₁) (A : ℋ₁ →ₗ[ℂ] ℋ₂) :
    outer_product (vec b A) (vec b A) =
      ∑ i : ι, ∑ j : ι,
        (endomorphismTensorEquiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
          ((outer_product (A (b i)) (A (b j))) ⊗ₜ[ℂ] outer_product (b i) (b j)) := by
  rw [vec_apply]
  rw [show outer_product (∑ i : ι, A (b i) ⊗ₜ[ℂ] b i)
      (∑ i : ι, A (b i) ⊗ₜ[ℂ] b i) =
      ∑ i : ι, ∑ j : ι,
        outer_product (A (b i) ⊗ₜ[ℂ] b i) (A (b j) ⊗ₜ[ℂ] b j) by
    exact outer_product_sum
      (fun i : ι => A (b i) ⊗ₜ[ℂ] b i)
      (fun i : ι => A (b i) ⊗ₜ[ℂ] b i)]
  simp_rw [← endomorphismTensorEquiv_symm_outer_product]

-- The triple finite-sum expansion and reindexing need the enlarged heartbeat budget.
lemma choi_kraus_expansion
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis ι ℂ ℋ₁) (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) :
    choi b (∑ a : κ, krausTerm (A a)) =
      ∑ a : κ, outer_product (vec b (A a)) (vec b (A a)) := by
  classical
  rw [choi_basis_expansion]
  simp only [LinearMap.sum_apply, krausTerm]
  change
    ∑ i : ι, ∑ j : ι,
      (endomorphismTensorEquiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
        (((∑ a : κ, (A a).comp ((outer_product (b i) (b j)).comp
          (LinearMap.adjoint (A a)))) ⊗ₜ[ℂ] outer_product (b i) (b j))) =
      ∑ a : κ, outer_product (vec b (A a)) (vec b (A a))
  simp_rw [comp_outer_product_adjoint]
  simp_rw [TensorProduct.sum_tmul]
  simp only [map_sum]
  simp_rw [outer_product_vec_expansion]
  let F : ι → ι → κ → L (ℋ₂ ⊗[ℂ] ℋ₁) :=
    fun i j a =>
      (endomorphismTensorEquiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
        ((outer_product (A a (b i)) (A a (b j))) ⊗ₜ[ℂ] outer_product (b i) (b j))
  change ∑ i : ι, ∑ j : ι, ∑ a : κ, F i j a =
    ∑ a : κ, ∑ i : ι, ∑ j : ι, F i j a
  calc
    ∑ i : ι, ∑ j : ι, ∑ a : κ, F i j a
        = ∑ i : ι, ∑ a : κ, ∑ j : ι, F i j a := by
          refine Finset.sum_congr rfl ?_
          intro i _
          exact Finset.sum_comm
    _ = ∑ a : κ, ∑ i : ι, ∑ j : ι, F i j a := by
          exact Finset.sum_comm

lemma choi_outer_product_kraus_apply
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂)
    (u : κ → ℋ₂ ⊗[ℂ] ℋ₁)
    (hΦ : choi b Φ = ∑ a : κ, outer_product (u a) (u a))
    (X : L ℋ₁) :
    let A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂) :=
      fun a => (vecLinearEquiv (ℋ₁ := ℋ₂) b).symm (u a)
    Φ X = ∑ a : κ, (A a).comp (X.comp (LinearMap.adjoint (A a))) := by
  classical
  let A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂) :=
    fun a => (vecLinearEquiv (ℋ₁ := ℋ₂) b).symm (u a)
  let Ψ : T ℋ₁ ℋ₂ := ∑ a : κ, krausTerm (A a)
  have hvec : ∀ a : κ, vec b (A a) = u a := by
    intro a
    rw [← vecLinearEquiv_toLinearMap (ℋ₁ := ℋ₂) b]
    exact LinearEquiv.apply_symm_apply (vecLinearEquiv (ℋ₁ := ℋ₂) b) (u a)
  have hΨ : choi b Ψ = choi b Φ := by
    calc
      choi b Ψ = ∑ a : κ, outer_product (vec b (A a)) (vec b (A a)) := by
        simpa [Ψ] using choi_kraus_expansion b A
      _ = ∑ a : κ, outer_product (u a) (u a) := by simp_rw [hvec]
      _ = choi b Φ := hΦ.symm
  have hmap : Ψ = Φ := choi_injective b hΨ
  simpa [Ψ, krausTerm] using (LinearMap.congr_fun hmap X).symm

lemma choi_outer_product_to_kraus
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂)
    (u : κ → ℋ₂ ⊗[ℂ] ℋ₁)
    (hΦ : choi b Φ = ∑ a : κ, outer_product (u a) (u a)) :
    KrausRep Φ κ := by
  refine ⟨fun a => (vecLinearEquiv (ℋ₁ := ℋ₂) b).symm (u a), ?_⟩
  intro X
  exact choi_outer_product_kraus_apply b Φ u hΦ X

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

/-! ### Right partial trace as a Kraus map -/
-- The `rw` steps use the normal forms produced by the preceding `simp` calls.
set_option linter.flexible false in
lemma endomorphismTensorEquiv_symm_outer_product_apply
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (u v x : E) (T : L F) (y : F) :
    ((endomorphismTensorEquiv (ℋ₁ := E) (ℋ₂ := F)).symm
      ((outer_product u v) ⊗ₜ[ℂ] T)) (x ⊗ₜ[ℂ] y) =
        (outer_product u v x) ⊗ₜ[ℂ] T y := by
  let b := stdOrthonormalBasis ℂ F
  rw [linearMap_eq_sum_outer_product b T]
  rw [TensorProduct.tmul_sum]
  rw [map_sum]
  simp only [LinearMap.sum_apply, endomorphismTensorEquiv_symm_outer_product]
  simp [outer_product_eq_rankOne, TensorProduct.inner_tmul]
  rw [TensorProduct.tmul_sum]
  simp [smul_tmul', smul_smul, mul_comm]

@[deprecated endomorphismTensorEquiv_symm_outer_product_apply (since := "2026-09-26")]
alias l_tensor_equiv_symm_outer_product_apply := endomorphismTensorEquiv_symm_outer_product_apply

lemma ite_tmul_zero_left
    {E : Type u} {F : Type v}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (p : Prop) [Decidable p] (x : E) (y : F) :
    (if p then x else 0) ⊗ₜ[ℂ] y = if p then x ⊗ₜ[ℂ] y else 0 := by
  by_cases hp : p <;> simp [hp]

lemma trace_outer_product_basisFun
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (a b : κ) :
    Tr (outer_product (EuclideanSpace.basisFun κ ℂ a) (EuclideanSpace.basisFun κ ℂ b)) =
      if a = b then 1 else 0 := by
  rw [outer_product_eq_rankOne, InnerProductSpace.trace_rankOne]
  by_cases hab : a = b
  · subst hab
    simp [EuclideanSpace.basisFun_apply]
  · simpa [hab] using (EuclideanSpace.basisFun κ ℂ).inner_eq_ite a b

lemma trace_outer_product_single
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (a b : κ) :
    Tr (outer_product (EuclideanSpace.single a (1 : ℂ)) (EuclideanSpace.single b (1 : ℂ))) =
      if a = b then 1 else 0 := by
  simpa [EuclideanSpace.basisFun_apply] using
    (trace_outer_product_basisFun (κ := κ) a b)

lemma trace_outer_product
    {E : Type u} [Qudit E] (u v : E) :
    Tr (outer_product u v) = inner ℂ u v := by
  rw [outer_product_eq_rankOne]
  simpa using InnerProductSpace.trace_rankOne (𝕜 := ℂ) (E := E) v u

noncomputable def tensorRightSlice
    {κ : Type*} [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (i : κ) :
    E ⊗[ℂ] F →ₗ[ℂ] E :=
  (TensorProduct.rid ℂ E : (E ⊗[ℂ] ℂ) →ₗ[ℂ] E) ∘ₗ
    TensorProduct.map LinearMap.id (b.toBasis.coord i)

lemma tensorRightSlice_tmul
    {κ : Type*} [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (i : κ) (x : E) (y : F) :
    tensorRightSlice (E := E) (F := F) b i (x ⊗ₜ[ℂ] y) =
      b.toBasis.coord i y • x := by
  simp [tensorRightSlice]

lemma tensorRightSlice_expand
    {κ : Type*} [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (z : E ⊗[ℂ] F) :
    z = ∑ i : κ, tensorRightSlice (E := E) (F := F) b i z ⊗ₜ[ℂ] b i := by
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro x y
    calc
      x ⊗ₜ[ℂ] y = x ⊗ₜ[ℂ] (∑ i : κ, b.repr y i • b i) := by
        rw [b.sum_repr]
      _ = ∑ i : κ, x ⊗ₜ[ℂ] (b.repr y i • b i) := by
        rw [TensorProduct.tmul_sum]
      _ = ∑ i : κ, (b.toBasis.coord i y • x) ⊗ₜ[ℂ] b i := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        simp [OrthonormalBasis.repr_apply_apply]
  · intro x y hx hy
    calc
      x + y =
          ∑ i, (tensorRightSlice (E := E) (F := F) b i) x ⊗ₜ[ℂ] b i +
            ∑ i, (tensorRightSlice (E := E) (F := F) b i) y ⊗ₜ[ℂ] b i := by
            exact congrArg₂ (fun a b => a + b) hx hy
      _ =
          ∑ i,
            ((tensorRightSlice (E := E) (F := F) b i) x ⊗ₜ[ℂ] b i +
              (tensorRightSlice (E := E) (F := F) b i) y ⊗ₜ[ℂ] b i) := by
            rw [Finset.sum_add_distrib]
      _ =
          ∑ i,
            ((tensorRightSlice (E := E) (F := F) b i) x +
              (tensorRightSlice (E := E) (F := F) b i) y) ⊗ₜ[ℂ] b i := by
            simp [TensorProduct.add_tmul]
      _ =
          ∑ i, (tensorRightSlice (E := E) (F := F) b i) (x + y) ⊗ₜ[ℂ] b i := by
            simp [map_add]

lemma TrRight_outer_product_tmul_basis
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (i j : κ) (x y : E) :
    traceOutRight (ℋ₂ := E) (ℋ₃ := F)
      (outer_product (x ⊗ₜ[ℂ] b i) (y ⊗ₜ[ℂ] b j)) =
        if i = j then outer_product x y else 0 := by
  dsimp [traceOutRight]
  have hconj :
      conjugateEnd (TensorProduct.comm ℂ E F)
        (outer_product (x ⊗ₜ[ℂ] b i) (y ⊗ₜ[ℂ] b j)) =
        outer_product (b i ⊗ₜ[ℂ] x) (b j ⊗ₜ[ℂ] y) := by
    apply LinearMap.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [conjugateEnd, outer_product]
    · intro a c
      simp [conjugateEnd, outer_product_eq_rankOne, TensorProduct.inner_tmul, mul_comm]
    · intro z w hz hw
      simp [hz, hw]
  rw [hconj]
  rw [← endomorphismTensorEquiv_symm_outer_product (E := F) (F := E) (b i) (b j) x y]
  rw [traceOutLeft_tmul]
  rw [trace_outer_product]
  by_cases hij : i = j
  · subst j
    simp
  · simp [b.inner_eq_ite, hij]

/--
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press, 2018), Eq.
(1.121). Partial correspondence to a corollary obtained from the definition of the right partial
trace. Expand rank-one operators in a finite orthonormal basis of the factor being traced out.
-/
lemma TrRight_outer_product
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (u v : E ⊗[ℂ] F) :
    traceOutRight (ℋ₂ := E) (ℋ₃ := F) (outer_product u v) =
      ∑ i : κ,
        outer_product
          (tensorRightSlice (E := E) (F := F) b i u)
          (tensorRightSlice (E := E) (F := F) b i v) := by
  classical
  conv_lhs =>
    rw [tensorRightSlice_expand (E := E) (F := F) b u,
      tensorRightSlice_expand (E := E) (F := F) b v]
    rw [outer_product_sum]
  simp only [map_sum]
  simp_rw [TrRight_outer_product_tmul_basis]
  simp

lemma tensorRightSlice_comp_outer_product
    {κ : Type*} [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (i : κ) (u v : E ⊗[ℂ] F) :
    (tensorRightSlice (E := E) (F := F) b i).comp
        ((outer_product u v).comp
          (LinearMap.adjoint (tensorRightSlice (E := E) (F := F) b i))) =
      outer_product
        (tensorRightSlice (E := E) (F := F) b i u)
        (tensorRightSlice (E := E) (F := F) b i v) := by
  exact @comp_outer_product_adjoint (E ⊗[ℂ] F) inferInstance E inferInstance
    (tensorRightSlice (E := E) (F := F) b i) u v

lemma traceOutRight_eq_kraus_sum
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) (X : L (E ⊗[ℂ] F)) :
    traceOutRight (ℋ₂ := E) (ℋ₃ := F) X =
      (∑ i : κ,
        (tensorRightSlice (E := E) (F := F) b i).comp
          (X.comp (LinearMap.adjoint (tensorRightSlice (E := E) (F := F) b i))) : L E) := by
  let c : OrthonormalBasis (Fin (Module.finrank ℂ (E ⊗[ℂ] F))) ℂ (E ⊗[ℂ] F) :=
    stdOrthonormalBasis ℂ (E ⊗[ℂ] F)
  rw [linearMap_eq_sum_outer_product c X]
  rw [map_sum]
  simp_rw [TrRight_outer_product (E := E) (F := F) b]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext z
  simp [LinearMap.comp_apply, ← tensorRightSlice_comp_outer_product]

theorem krausRep_traceOutRight
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) :
    KrausRep (ℋ₁ := E ⊗[ℂ] F) (ℋ₂ := E)
      (traceOutRight (ℋ₂ := E) (ℋ₃ := F)) κ := by
  refine ⟨fun i => tensorRightSlice (E := E) (F := F) b i, ?_⟩
  intro X
  exact traceOutRight_eq_kraus_sum b X

theorem cp_traceOutRight
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (b : OrthonormalBasis κ ℂ F) :
    IsCompletelyPositive (traceOutRight (ℋ₂ := E) (ℋ₃ := F)) := by
  exact cp_of_krausRep
    (ℋ₁ := E ⊗[ℂ] F) (ℋ₂ := E)
    (traceOutRight (ℋ₂ := E) (ℋ₃ := F))
    (krausRep_traceOutRight b)

/-- The right partial trace is monotone for the operator order. -/
@[gcongr]
theorem traceOutRight_le_traceOutRight
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    {X Y : L (E ⊗[ℂ] F)} (hXY : X ≤ Y) :
    traceOutRight (ℋ₂ := E) (ℋ₃ := F) X ≤ traceOutRight (ℋ₂ := E) (ℋ₃ := F) Y := by
  have hpos : 0 ≤ traceOutRight (ℋ₂ := E) (ℋ₃ := F) (Y - X) :=
    isPositiveMap_of_cp (traceOutRight (ℋ₂ := E) (ℋ₃ := F))
      (cp_traceOutRight (stdOrthonormalBasis ℂ F))
      (Y - X) (sub_nonneg.mpr hXY)
  rw [map_sub] at hpos
  exact sub_nonneg.mp hpos

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
