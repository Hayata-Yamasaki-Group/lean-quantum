/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.QuantumState
import Quantum.QuantumMechanics.OperatorInstances
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Quantum.QuantumMechanics.Channel.Basic

/-!
Basic quantum-channel types, partial traces, vectorization, transposes, outer products,
and Choi operators.
-/

namespace QuantumChannel

open QuantumState
open TensorProduct

universe u v w

section Definition

/-! ### Partial trace tools -/

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

lemma endomorphismTensorEquiv_map_tmul
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (B : L E) (C : L F) :
    (endomorphismTensorEquiv (ℋ₁ := E) (ℋ₂ := F)) (TensorProduct.map B C) =
      B ⊗ₜ[ℂ] C := by
  apply (endomorphismTensorEquiv (ℋ₁ := E) (ℋ₂ := F)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (endomorphismTensorEquiv_symm_tmul (E := E) (F := F) B C).symm

lemma traceOutLeft_tmul_nonneg
    (X : L ℋ₁) (Y : L ℋ₂) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ traceOutLeft ((endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).symm (X ⊗ₜ[ℂ] Y)) := by
  rw [traceOutLeft_tmul]
  exact (LinearMap.nonneg_iff_isPositive _).mpr <|
    ((LinearMap.nonneg_iff_isPositive Y).mp hY).smul_of_nonneg
      ((LinearMap.nonneg_iff_isPositive X).mp hX).trace_nonneg

lemma traceOutLeft_sum_tmul_nonneg
    {κ : Type u} [Fintype κ]
    (X : κ → L ℋ₁) (Y : κ → L ℋ₂)
    (hX : ∀ a, 0 ≤ X a) (hY : ∀ a, 0 ≤ Y a) :
    0 ≤ traceOutLeft
      (∑ a : κ,
        (endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).symm ((X a) ⊗ₜ[ℂ] (Y a))) := by
  rw [map_sum]
  exact Finset.sum_nonneg fun a _ =>
    traceOutLeft_tmul_nonneg (X a) (Y a) (hX a) (hY a)

-- (1.131) (1.132) https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
-- Lemma 5.12 http://www.ueltschi.org/AZschool/notes/EricCarlen.pdf
-- For any qudit ℋ, any A,B ∈ L(ℋ), and any K ∈ L(ℋ),
-- ⟨ vec[K] ∣ (A ⊗ B) vec[K] ⟩ = Tr[K† A K B.transpose]
noncomputable def l_transpose (b : Module.Basis ι ℂ ℋ₁)
  (A : L ℋ₁) : L ℋ₁ :=
  b.toDualEquiv.symm.toLinearMap ∘ₗ A.dualMap ∘ₗ b.toDualEquiv.toLinearMap

lemma dualTensorHom_map
    {R : Type*} [CommSemiring R]
    {M M' N N' : Type*}
    [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N] [AddCommMonoid N']
    [Module R M] [Module R M'] [Module R N] [Module R N']
    (f : M' →ₗ[R] M) (g : N →ₗ[R] N')
    (x : (Module.Dual R M) ⊗[R] N) :
    (dualTensorHom R M' N') (TensorProduct.map f.dualMap g x)
      = g ∘ₗ (dualTensorHom R M N x) ∘ₗ f := by
  refine TensorProduct.induction_on x ?h0 ?htmul ?hadd
  · simp
  · intro φ n
    -- both sides are linear maps, so compare them pointwise via ext
    ext m'
    -- fold `map_tmul`, `dualTensorHom_apply`, `dualMap_apply` with simp
    simp [dualTensorHom_apply]
  · intro x y hx hy
    simp only [map_add, hx, hy]
    ext _
    simp

lemma dualTensorHomEquiv_symm_map
    {R : Type*} [CommSemiring R]
    {M M' N N' : Type*}
    [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N] [AddCommMonoid N']
    [Module R M] [Module R M'] [Module R N] [Module R N']
    [Module.Free R M] [Module.Finite R M]
    [Module.Free R M'] [Module.Finite R M']
    (f : M' →ₗ[R] M) (g : N →ₗ[R] N')
    (K : M →ₗ[R] N) :
    TensorProduct.map f.dualMap g ((dualTensorHomEquiv R M N).symm K)
      = (dualTensorHomEquiv R M' N').symm (g ∘ₗ K ∘ₗ f) := by
  -- `dualTensorHomEquiv` is a linear equivalence, so reduce to the Hom side by injectivity
  apply (dualTensorHomEquiv R M' N').injective
  -- the forward map of `dualTensorHomEquiv` is `dualTensorHom`, so the lemma above finishes the
  -- proof
  simpa [dualTensorHomEquiv] using
    (dualTensorHom_map (R := R) (M := M) (M' := M') (N := N) (N' := N') f g
      ((dualTensorHomEquiv R M N).symm K))

omit [Fintype ι] in
lemma dual_comm [Finite ι] {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] [Module.Free R M]
    (b : Module.Basis ι R M) (x y : M) :
  (b.toDual x) y = (b.toDual y) x := by
  have := Fintype.ofFinite ι
  rw [←(Module.Basis.sum_equivFun b x)]
  rw [map_sum, map_sum, LinearMap.sum_apply]
  congr
  ext i
  rw [map_smul, map_smul, LinearMap.smul_apply]
  congr 1
  rw [←(Module.Basis.sum_equivFun b y)]
  rw [map_sum, map_sum, LinearMap.sum_apply]
  congr
  ext j
  rw [map_smul, map_smul, LinearMap.smul_apply]
  congr 1
  rw [b.toDual_apply, b.toDual_apply]
  congr 1
  exact Eq.propIntro (fun a ↦ id (Eq.symm a)) fun a ↦ id (Eq.symm a)

omit [Fintype ι] in
lemma dual_symm_comm [Finite ι] {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] [Module.Free R M]
    (b : Module.Basis ι R M) (x y : Module.Dual R M) :
  x (b.toDualEquiv.symm y) = y (b.toDualEquiv.symm x) := by
  nth_rw 1 [(by simp : x = b.toDualEquiv (b.toDualEquiv.symm x))]
  nth_rw 2 [(by simp : y = b.toDualEquiv (b.toDualEquiv.symm y))]
  rw [b.toDualEquiv_apply]
  apply dual_comm

lemma comp_dual_equiv_symm_eq (b : Module.Basis ι ℂ ℋ₂)
  (B : L ℋ₂) : B ∘ₗ
      (b.toDualEquiv.symm : Module.Dual ℂ ℋ₂ →ₗ[ℂ] ℋ₂)
    = ((Module.evalEquiv ℂ ℋ₂).symm :
        Module.Dual ℂ (Module.Dual ℂ ℋ₂) →ₗ[ℂ] ℋ₂) ∘ₗ
      ((l_transpose b B) ∘ₗ
        (b.toDualEquiv.symm : Module.Dual ℂ ℋ₂ →ₗ[ℂ] ℋ₂)).dualMap := by
  ext x
  dsimp only [l_transpose]
  apply (Module.evalEquiv ℂ ℋ₂).injective
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Module.evalEquiv_apply,
    LinearEquiv.apply_symm_apply]
  ext y
  simp only [Module.Dual.eval_apply, LinearMap.dualMap_apply',
    LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearEquiv.apply_symm_apply]
  have hxy := dual_symm_comm b (y ∘ₗ B) x
  simpa using hxy

omit [Fintype ι] in
lemma dual_equiv_symm_eq [Finite ι] (b : Module.Basis ι ℂ ℋ₂)
  : (b.toDualEquiv.symm : Module.Dual ℂ ℋ₂ →ₗ[ℂ] ℋ₂)
    = ((Module.evalEquiv ℂ ℋ₂).symm :
        Module.Dual ℂ (Module.Dual ℂ ℋ₂) →ₗ[ℂ] ℋ₂) ∘ₗ
      (b.toDualEquiv.symm : Module.Dual ℂ ℋ₂ →ₗ[ℂ] ℋ₂).dualMap := by
  have := Fintype.ofFinite ι
  let := comp_dual_equiv_symm_eq b (I ℋ₂)
  simp only [LinearMap.id_comp, l_transpose, LinearMap.dualMap_id, LinearEquiv.comp_coe,
    LinearEquiv.self_trans_symm,
    LinearEquiv.refl_toLinearMap] at this
  exact this

lemma map_vec_eq_vec (b : Module.Basis ι ℂ ℋ₂)
  (A : L ℋ₁) (B : L ℋ₂) (K : ℋ₂ →ₗ[ℂ] ℋ₁) :
  (TensorProduct.map A B) (vec b K) = vec b (A ∘ₗ K ∘ₗ (l_transpose b B)) := by
  simp only [vec, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [map_comm]
  congr 1
  rw [map_map]
  simp only [LinearMap.comp_id]
  nth_rw 2 [dual_equiv_symm_eq]
  rw [(by simp : LinearMap.id = LinearMap.id ∘ₗ LinearMap.id), map_comp]
  rw [comp_dual_equiv_symm_eq]
  rw [(by simp : A = LinearMap.id ∘ₗ A), map_comp]
  simp only [LinearMap.coe_comp, Function.comp_apply]
  congr 1
  rw [dualTensorHomEquiv_symm_map, dualTensorHomEquiv_symm_map]
  rfl

/--
Source: arXiv:2607.05492v1, the identity between the vectorization inner product and the trace in
§2.B, p.10. Displayed lemma `inner_vec_eq_trace` (no separate number).
-/
lemma inner_vec_eq_trace
  (b : OrthonormalBasis ι ℂ ℋ₂)
  (A B : ℋ₂ →ₗ[ℂ] ℋ₁) :
  inner ℂ (vec b.toBasis A) (vec b.toBasis B) = Tr (A† ∘ₗ B) := by
  calc
    inner ℂ (vec b.toBasis A) (vec b.toBasis B)
        = ∑ i : ι, inner ℂ (A (b i)) (B (b i)) := by
      simp [vec_apply, inner_sum, sum_inner, b.inner_eq_ite]
    _ = ∑ i : ι, inner ℂ (b i) ((A† ∘ₗ B) (b i)) := by
      simp [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
    _ = ∑ i : ι, b.toBasis.coord i ((A† ∘ₗ B) (b i)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hcoord : b.toBasis.coord i = (innerSL ℂ (b i)).toLinearMap := by
        ext j
        simp [b.repr_apply_apply]
      simp [hcoord]
    _ = Tr (A† ∘ₗ B) := by
      simp [Tr, LinearMap.trace_eq_matrix_trace (b := b.toBasis) (f := A† ∘ₗ B),
        Matrix.trace, LinearMap.toMatrix_apply]

/--
Source: arXiv:2607.05492v1, Ando's identity for vectorization in §2.B, p.10. Displayed lemma
`ando_identity` (no separate number).
-/
lemma ando_identity (b : OrthonormalBasis ι ℂ ℋ₂)
  (A : L ℋ₁) (B : L ℋ₂) (K : ℋ₂ →ₗ[ℂ] ℋ₁) :
  inner ℂ (vec b.toBasis K) ((TensorProduct.map A B) (vec b.toBasis K))
    = Tr (K† ∘ₗ A ∘ₗ K ∘ₗ (l_transpose b.toBasis B)) := by
  rw [map_vec_eq_vec]
  apply inner_vec_eq_trace

lemma traceOutLeft_simple_outer_product_sum_nonneg
    {κ : Type u} [Fintype κ]
    (x : κ → ℋ₁) (y : κ → ℋ₂) :
    0 ≤ traceOutLeft
      (∑ a : κ,
        (endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).symm
          ((outer_product (x a) (x a)) ⊗ₜ[ℂ] (outer_product (y a) (y a)))) := by
  exact traceOutLeft_sum_tmul_nonneg
    (fun a => outer_product (x a) (x a))
    (fun a => outer_product (y a) (y a))
    (fun a => outer_product_self_nonneg (x a))
    (fun a => outer_product_self_nonneg (y a))

end Definition

end QuantumChannel
