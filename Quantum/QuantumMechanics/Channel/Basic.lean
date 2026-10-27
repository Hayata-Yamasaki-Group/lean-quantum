/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.QuantumState
import Quantum.QuantumMechanics.OperatorInstances
import Mathlib.Analysis.InnerProductSpace.TensorProduct

-- The basis APIs (`vec`, `choi`) retain explicit finite-index instances.
-- Suppress type-only unused-binder checks for `DecidableEq` and `Fintype`.
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
Basic quantum-channel types, partial traces, vectorization, transposes, outer products,
and Choi operators.
-/

namespace QuantumChannel

open QuantumState
open TensorProduct

universe u v w

section Definition
/-! ### Basic channel type -/
-- The set of linear maps
abbrev T (ℋ₁ : Type u) (ℋ₂ : Type v)
  [AddCommGroup ℋ₁] [Module ℂ ℋ₁] [AddCommGroup ℋ₂] [Module ℂ ℋ₂] : Type (max u v) :=
  (L ℋ₁) →ₗ[ℂ] (L ℋ₂)

/--
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press,
2018), Definition 2.13. Complete positivity and trace preservation on all operators are packaged in
a structure, also allowing zero dimensions.
-/
structure CPTP (ℋ₁ : Type u) (ℋ₂ : Type v) [Qudit ℋ₁] [Qudit ℋ₂]
    extends CompletelyPositiveMap (L ℋ₁) (L ℋ₂) where
  trace_map (ρ : L ℋ₁) : Tr ρ = Tr (toFun ρ)

/-! ### Partial trace tools -/

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

-- Def: Left partial trace (1.119), with simple-tensor evaluation (1.120)
-- https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
-- traceOutLeft(X) for X ∈ L(ℋ₁⊗ℋ₂)

noncomputable instance : Qudit (ℋ₁ ⊗[ℂ] ℋ₂) := by
  letI : Module.Finite ℂ (ℋ₁ ⊗[ℂ] ℋ₂) := inferInstance
  exact
    { toNormedAddCommGroup := inferInstance
      toInnerProductSpace := inferInstance
      toCompleteSpace := inferInstance
      fg_top := Module.Finite.fg_top }

noncomputable instance {κ : Type u} [Fintype κ] [DecidableEq κ] :
    Qudit (EuclideanSpace ℂ κ) := by
  letI : Module.Finite ℂ (EuclideanSpace ℂ κ) :=
    Module.Finite.of_basis (EuclideanSpace.basisFun κ ℂ).toBasis
  exact
    { toNormedAddCommGroup := inferInstance
      toInnerProductSpace := inferInstance
      toCompleteSpace := inferInstance
      fg_top := Module.Finite.fg_top }

noncomputable def endomorphismTensorEquiv {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂] :
  (L (ℋ₁ ⊗[ℂ] ℋ₂)) ≃ₗ[ℂ] (L ℋ₁ ⊗[ℂ] L ℋ₂) :=
  ((dualTensorHomEquiv ℂ (ℋ₁ ⊗[ℂ] ℋ₂) (ℋ₁ ⊗[ℂ] ℋ₂)).symm : LinearEquiv (RingHom.id ℂ) _ _).trans <|
  ((dualDistribEquiv ℂ ℋ₁ ℋ₂).symm.rTensor (ℋ₁ ⊗[ℂ] ℋ₂)).trans <|
  (TensorProduct.assoc ℂ (Module.Dual ℂ ℋ₁ ⊗[ℂ] Module.Dual ℂ ℋ₂) ℋ₁ ℋ₂).symm.trans <|
  ((TensorProduct.assoc ℂ (Module.Dual ℂ ℋ₁) (Module.Dual ℂ ℋ₂) ℋ₁).rTensor ℋ₂).trans <|
  (((TensorProduct.comm ℂ (Module.Dual ℂ ℋ₂) ℋ₁).lTensor (Module.Dual ℂ ℋ₁)).rTensor ℋ₂).trans <|
  ((TensorProduct.assoc ℂ (Module.Dual ℂ ℋ₁) ℋ₁ (Module.Dual ℂ ℋ₂)).symm.rTensor ℋ₂).trans <|
  (TensorProduct.assoc ℂ (Module.Dual ℂ ℋ₁ ⊗[ℂ] ℋ₁) (Module.Dual ℂ ℋ₂) ℋ₂).trans <|
  (TensorProduct.congr (dualTensorHomEquiv ℂ ℋ₁ ℋ₁) (dualTensorHomEquiv ℂ ℋ₂ ℋ₂))

-- It may be neccesary to add some lemmas to use endomorphismTensorEquiv effectively

/--
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press, 2018), Eq.
(1.119) / Eq. (1.120). Corresponds to the definition in Eq. (1.119); the evaluation in Eq. (1.120)
is a separate declaration.
-/
noncomputable def traceOutLeft : T (ℋ₁ ⊗[ℂ] ℋ₂) ℋ₂ :=
  (TensorProduct.lid ℂ (L ℋ₂)).toLinearMap
  ∘ₗ (TensorProduct.map Tr LinearMap.id)
  ∘ₗ endomorphismTensorEquiv.toLinearMap

/--
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press, 2018), Eq.
(1.120). Partial correspondence to the evaluation of the left partial trace on simple tensors.
-/
lemma traceOutLeft_tmul
    (X : L ℋ₁) (Y : L ℋ₂) :
    traceOutLeft (endomorphismTensorEquiv.symm (X ⊗ₜ[ℂ] Y)) =
      (Tr X) • Y := by
  simp [traceOutLeft, endomorphismTensorEquiv]

lemma endomorphismTensorEquiv_symm_tmul_aux
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (u : Module.Dual ℂ E ⊗[ℂ] E)
    (v : Module.Dual ℂ F ⊗[ℂ] F) :
    (endomorphismTensorEquiv (ℋ₁ := E) (ℋ₂ := F)).symm
        ((dualTensorHom ℂ E E u) ⊗ₜ[ℂ] (dualTensorHom ℂ F F v)) =
      TensorProduct.map (dualTensorHom ℂ E E u) (dualTensorHom ℂ F F v) := by
  induction u using TensorProduct.induction_on with
  | zero =>
      simp [TensorProduct.map_zero_left]
  | tmul f p =>
      induction v using TensorProduct.induction_on with
      | zero =>
          simp [TensorProduct.map_zero_right]
      | tmul g q =>
          ext x y
          simp [endomorphismTensorEquiv, TensorProduct.map, smul_smul]
      | add v₁ v₂ hv₁ hv₂ =>
          simp [TensorProduct.tmul_add, map_add, TensorProduct.map_add_right, hv₁, hv₂]
  | add u₁ u₂ hu₁ hu₂ =>
      simp [TensorProduct.add_tmul, map_add, TensorProduct.map_add_left, hu₁, hu₂]

@[deprecated endomorphismTensorEquiv_symm_tmul_aux (since := "2026-09-26")]
alias l_tensor_equiv_symm_tmul_aux := endomorphismTensorEquiv_symm_tmul_aux

lemma endomorphismTensorEquiv_symm_tmul
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (B : L E) (C : L F) :
    endomorphismTensorEquiv.symm (B ⊗ₜ[ℂ] C) =
      TensorProduct.map B C := by
  let bE := Module.Free.chooseBasis ℂ E
  let bF := Module.Free.chooseBasis ℂ F
  let u : Module.Dual ℂ E ⊗[ℂ] E := (dualTensorHomEquivOfBasis bE).symm B
  let v : Module.Dual ℂ F ⊗[ℂ] F := (dualTensorHomEquivOfBasis bF).symm C
  have hu : dualTensorHom ℂ E E u = B := by
    simp [u]
  have hv : dualTensorHom ℂ F F v = C := by
    simp [v]
  rw [← hu, ← hv]
  exact endomorphismTensorEquiv_symm_tmul_aux (E := E) (F := F) u v

@[deprecated endomorphismTensorEquiv_symm_tmul (since := "2026-09-26")]
alias l_tensor_equiv_symm_tmul := endomorphismTensorEquiv_symm_tmul

lemma endomorphismTensorEquiv_map_tmul
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    (B : L E) (C : L F) :
    endomorphismTensorEquiv (TensorProduct.map B C) =
      B ⊗ₜ[ℂ] C := by
  apply (endomorphismTensorEquiv (ℋ₁ := E) (ℋ₂ := F)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (endomorphismTensorEquiv_symm_tmul (E := E) (F := F) B C).symm

@[deprecated endomorphismTensorEquiv_map_tmul (since := "2026-09-26")]
alias l_tensor_equiv_map_tmul := endomorphismTensorEquiv_map_tmul

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

-- def: vec(A) (1.127) https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
-- vec[|u⟩⟨v|] := |u⟩⊗|v⟩ : (ℋ₁ →L[ℂ] ℋ₂) → ℋ₂⊗ℋ₁
/-! ### Vectorization and transpose identities -/
noncomputable def vec (b : Module.Basis ι ℂ ℋ₂) :
  (ℋ₂ →ₗ[ℂ] ℋ₁) →ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂) :=
  (TensorProduct.comm ℂ ℋ₂ ℋ₁)
  ∘ₗ (TensorProduct.map b.toDualEquiv.symm.toLinearMap LinearMap.id)
  ∘ₗ (dualTensorHomEquiv ℂ ℋ₂ ℋ₁).symm.toLinearMap

noncomputable def vecLinearEquiv (b : Module.Basis ι ℂ ℋ₂) :
    (ℋ₂ →ₗ[ℂ] ℋ₁) ≃ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂) :=
  (dualTensorHomEquiv ℂ ℋ₂ ℋ₁).symm.trans <|
    (TensorProduct.congr b.toDualEquiv.symm (LinearEquiv.refl ℂ ℋ₁)).trans <|
      TensorProduct.comm ℂ ℋ₂ ℋ₁

lemma vecLinearEquiv_toLinearMap (b : Module.Basis ι ℂ ℋ₂) :
    (vecLinearEquiv (ℋ₁ := ℋ₁) b :
      (ℋ₂ →ₗ[ℂ] ℋ₁) →ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂)) = vec b := by
  ext A
  simp [vecLinearEquiv, vec, TensorProduct.congr]

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
    -- Both sides are linear maps, so use ext to compare them pointwise.
    ext m'
    -- Simplify `map_tmul`, `dualTensorHom_apply`, and `dualMap_apply` with simp.
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
  -- Since `dualTensorHomEquiv` is a linear equivalence, use injective to reduce to the Hom side.
  apply (dualTensorHomEquiv R M' N').injective
  -- The forward map of `dualTensorHomEquiv` is `dualTensorHom`, so the lemma above finishes the
  -- proof.
  simpa [dualTensorHomEquiv] using
    (dualTensorHom_map (R := R) (M := M) (M' := M') (N := N) (N' := N') f g
      ((dualTensorHomEquiv R M N).symm K))

lemma dual_comm {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] [Module.Free R M]
    (b : Module.Basis ι R M) (x y : M) :
  (b.toDual x) y = (b.toDual y) x := by
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

lemma dual_symm_comm {R : Type*} [CommSemiring R]
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

lemma dual_equiv_symm_eq (b : Module.Basis ι ℂ ℋ₂)
  : (b.toDualEquiv.symm : Module.Dual ℂ ℋ₂ →ₗ[ℂ] ℋ₂)
    = ((Module.evalEquiv ℂ ℋ₂).symm :
        Module.Dual ℂ (Module.Dual ℂ ℋ₂) →ₗ[ℂ] ℋ₂) ∘ₗ
      (b.toDualEquiv.symm : Module.Dual ℂ ℋ₂ →ₗ[ℂ] ℋ₂).dualMap := by
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
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press, 2018), Eq.
(1.127). Generalization to an arbitrary finite algebraic basis. Partial correspondence that agrees
upon specialization to the standard basis of the source.
-/
lemma vec_apply (b : Module.Basis ι ℂ ℋ₂)
  (C : ℋ₂ →ₗ[ℂ] ℋ₁) :
  vec b C = ∑ i : ι, (C (b i)) ⊗ₜ[ℂ] (b i) := by
  have h : dualTensorHomEquivOfBasis b = dualTensorHomEquiv ℂ ℋ₂ ℋ₁ := by
    exact LinearEquiv.toLinearMap_inj.mp rfl
  rw [vec, ←h]
  simp only [dualTensorHomEquivOfBasis, LinearEquiv.ofLinear, Module.Basis.coe_dualBasis,
    LinearMap.coe_sum, LinearMap.coe_comp, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_symm_mk', Finset.sum_apply,
    Function.comp_apply, LinearMap.applyₗ_apply_apply, mk_apply, map_sum,
    map_tmul, LinearMap.id_coe, id_eq, comm_tmul]
  congr
  ext i
  congr
  have h : b.toDualEquiv (b i) = b.coord i := by
    simpa [Module.Basis.toDualEquiv_apply] using (Module.Basis.coe_toDual_self (b := b) i)
  rw [←h]
  exact LinearEquiv.symm_apply_apply b.toDualEquiv (b i)

/--
Source: this paper, arXiv:2607.05492v1, the identity between the vectorization inner product and the
trace in §2.B, p.10. The displayed lemma
`inner_vec_eq_trace` (no separate number).
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
Source: this paper, arXiv:2607.05492v1, Ando's identity for vectorization in §2.B, p.10. The
displayed lemma
`ando_identity` (no separate number).
-/
lemma ando_identity (b : OrthonormalBasis ι ℂ ℋ₂)
  (A : L ℋ₁) (B : L ℋ₂) (K : ℋ₂ →ₗ[ℂ] ℋ₁) :
  inner ℂ (vec b.toBasis K) ((TensorProduct.map A B) (vec b.toBasis K))
    = Tr (K† ∘ₗ A ∘ₗ K ∘ₗ (l_transpose b.toBasis B)) := by
  rw [map_vec_eq_vec]
  apply inner_vec_eq_trace

-- def: Choi operator (2.64) https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- J(Φ) := (Φ⊗id)(vec[I(ℋ₂⊗ℋ₁)] vec[I(ℋ₂⊗ℋ₁)]†) for Φ ∈ T(ℋ₁,ℋ₂)

-- (1.57) in https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf
/-! ### Outer products and the Choi operator -/
noncomputable def outer_product
  (u : ℋ₁) (v : ℋ₂) : ℋ₁ →ₗ[ℂ] ℋ₂ :=
  (dualTensorHomEquiv ℂ ℋ₁ ℋ₂).toLinearMap <|
    ((InnerProductSpace.toDualMap ℂ ℋ₁ u) ⊗ₜ[ℂ] v)

lemma outer_product_eq_rankOne
    (u : ℋ₁) (v : ℋ₂) :
    outer_product u v =
      (InnerProductSpace.rankOne ℂ v u : ℋ₁ →ₗ[ℂ] ℋ₂) := by
  ext x
  simp [outer_product, dualTensorHom_apply]

lemma outer_product_self_nonneg
    (u : ℋ₁) :
    0 ≤ outer_product u u := by
  rw [outer_product_eq_rankOne]
  have hcont : (InnerProductSpace.rankOne ℂ u u).IsPositive :=
    InnerProductSpace.isPositive_rankOne_self (𝕜 := ℂ) u
  exact (LinearMap.nonneg_iff_isPositive _).mpr <|
    (LinearMap.isPositive_toContinuousLinearMap_iff _).mp hcont

lemma outer_product_sum
    {κ : Type*} [Fintype κ]
    (x y : κ → ℋ₁) :
    outer_product (∑ a : κ, x a) (∑ a : κ, y a) =
      ∑ a : κ, ∑ b : κ, outer_product (x a) (y b) := by
  ext z
  simp [outer_product_eq_rankOne]

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

@[deprecated traceOutLeft_simple_outer_product_sum_nonneg (since := "2026-09-26")]
alias Tr₂_simple_outer_product_sum_nonneg := traceOutLeft_simple_outer_product_sum_nonneg

/--
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press, 2018), Eq.
(2.64). Generalization to an arbitrary algebraic basis, agreeing upon specialization to the standard
basis. For a non-orthonormal basis it differs from the Choi operator in the source; zero dimensions
are also allowed.
-/
noncomputable def choi (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) : L (ℋ₂ ⊗[ℂ] ℋ₁) :=
  (endomorphismTensorEquiv.symm.toLinearMap
  ∘ₗ (TensorProduct.map Φ LinearMap.id)
  ∘ₗ endomorphismTensorEquiv.toLinearMap) (outer_product (vec b (I ℋ₁)) (vec b (I ℋ₁)))

end Definition

end QuantumChannel

namespace QuantumChannel

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u

/-- Application of an outer product: `(|v⟩⟨u|) x = ⟪u, x⟫ • v`. -/
lemma outer_product_apply {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂]
    (u : ℋ₁) (v : ℋ₂) (x : ℋ₁) :
    outer_product u v x = (inner ℂ u x : ℂ) • v := by
  rw [outer_product_eq_rankOne]
  simp [InnerProductSpace.rankOne_apply]

end

end QuantumChannel

namespace QuantumChannel

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u

/-- `v ↦ outer_product u v` as a bundled (continuous) linear map. -/
private noncomputable def outerL {ℋ : Type u} [Qudit ℋ] (u : ℋ) : ℋ →ₗ[ℂ] B ℋ where
  toFun v := (outer_product u v).toContinuousLinearMap
  map_add' v w := by
    ext x
    change outer_product u (v + w) x = outer_product u v x + outer_product u w x
    simp [QuantumChannel.outer_product_apply, smul_add]
  map_smul' c v := by
    ext x
    change outer_product u (c • v) x = c • outer_product u v x
    simp [QuantumChannel.outer_product_apply, smul_smul, mul_comm]

end

end QuantumChannel

namespace QuantumChannel

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u

lemma continuous_outerL {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (u : ℋ) :
    Continuous (fun v : ℋ => (outer_product u v).toContinuousLinearMap) :=
  (outerL u).continuous_of_finiteDimensional

end

end QuantumChannel

namespace QuantumChannel

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u

/-- Reconstruction of a continuous endomorphism from an orthonormal basis. -/
lemma continuousLinearMap_eq_sum_outer_product
    {ℋ : Type u} [Qudit ℋ] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ ℋ) (T : B ℋ) :
    T = ∑ i : ι, (outer_product (b i) (T (b i))).toContinuousLinearMap := by
  ext x
  have hsum : T x = ∑ i : ι, inner ℂ (b i) x • T (b i) := by
    simpa using congrArg T (b.sum_repr' x).symm
  calc
    T x = ∑ i : ι, inner ℂ (b i) x • T (b i) := hsum
    _ = (∑ i : ι, (outer_product (b i) (T (b i))).toContinuousLinearMap) x := by
      simp [ContinuousLinearMap.sum_apply, outer_product_eq_rankOne]

end

end QuantumChannel
