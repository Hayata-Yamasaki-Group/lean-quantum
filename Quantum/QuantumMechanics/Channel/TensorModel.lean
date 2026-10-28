/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.Channel.Amplification

/-!
Tensor-model descriptions of full matrix amplifications.
-/

namespace QuantumChannel

open QuantumState
open TensorProduct

universe u v w

section RepresentationsOfChannels

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-! ### Tensor model for the full amplification -/

noncomputable def basisPiTensorLinearEquiv
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) :
    DS n ℋ₂ ≃ₗ[ℂ] ℋ₂ ⊗[ℂ] ℋ₁ :=
  (dsEquiv n ℋ₂).toLinearEquiv.trans <|
    ((Finsupp.linearEquivFunOnFinite ℂ ℋ₂ (Fin n)).symm.trans
      (TensorProduct.equivFinsuppOfBasisRight b.toBasis).symm)

lemma basisPiTensorLinearEquiv_apply
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) (x : DS n ℋ₂) :
    basisPiTensorLinearEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b x =
      ∑ i, dsProj n ℋ₂ i x ⊗ₜ[ℂ] b i := by
  rw [basisPiTensorLinearEquiv]
  change
    (TensorProduct.equivFinsuppOfBasisRight b.toBasis).symm
        ((Finsupp.linearEquivFunOnFinite ℂ ℋ₂ (Fin n)).symm ((dsEquiv n ℋ₂) x)) =
      ∑ i, dsProj n ℋ₂ i x ⊗ₜ[ℂ] b i
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply]
  simp [Finsupp.sum_fintype, dsProj, dsEquiv]

lemma basisPiTensorLinearEquiv_dsIncl
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) (i : Fin n) (x : ℋ₂) :
    basisPiTensorLinearEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b (dsIncl n ℋ₂ i x) =
      x ⊗ₜ[ℂ] b i := by
  rw [basisPiTensorLinearEquiv_apply]
  classical
  rw [Finset.sum_eq_single i]
  · simp [dsProj_dsIncl_apply]
  · intro j _ hji
    simp [dsProj_dsIncl_apply, hji]
  · simp

lemma basisPiTensorLinearEquiv_inner
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) (x y : DS n ℋ₂) :
    inner ℂ
        (basisPiTensorLinearEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b x)
        (basisPiTensorLinearEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b y) =
      inner ℂ x y := by
  rw [basisPiTensorLinearEquiv_apply, basisPiTensorLinearEquiv_apply]
  classical
  simp only [inner_sum, sum_inner, TensorProduct.inner_tmul]
  simpa [PiLp.inner_apply] using
    (b.orthonormal.inner_left_right_finset
      (s := Finset.univ)
      (a := fun i j => inner ℂ (dsProj n ℋ₂ j x) (dsProj n ℋ₂ i y)))

noncomputable def basisPiTensorLinearIsometryEquiv
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) :
    DS n ℋ₂ ≃ₗᵢ[ℂ] ℋ₂ ⊗[ℂ] ℋ₁ :=
  (basisPiTensorLinearEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b).isometryOfInner
    (basisPiTensorLinearEquiv_inner (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b)

noncomputable def basisPiTensorEndAlgEquiv
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) :
    L (DS n ℋ₂) ≃⋆ₐ[ℂ] L (ℋ₂ ⊗[ℂ] ℋ₁) :=
  (linearToContinuousEndStarAlgEquiv (ℋ := DS n ℋ₂)).trans <|
    ((basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b).conjStarAlgEquiv.trans
      (linearToContinuousEndStarAlgEquiv (ℋ := ℋ₂ ⊗[ℂ] ℋ₁)).symm)

lemma basisPiTensorLinearIsometryEquiv_apply
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) (x : DS n ℋ₂) :
    basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b x =
      ∑ i, dsProj n ℋ₂ i x ⊗ₜ[ℂ] b i := by
  simpa using basisPiTensorLinearEquiv_apply (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b x

lemma basisPiTensorLinearIsometryEquiv_dsIncl
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) (i : Fin n) (x : ℋ₂) :
    basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b (dsIncl n ℋ₂ i x) =
      x ⊗ₜ[ℂ] b i := by
  exact basisPiTensorLinearEquiv_dsIncl (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b i x

lemma basisPiTensorLinearIsometryEquiv_symm_tmul
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁) (i : Fin n) (x : ℋ₂) :
    (basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b).symm (x ⊗ₜ[ℂ] b i) =
      dsIncl n ℋ₂ i x := by
  apply (basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b).injective
  simpa using
    (basisPiTensorLinearIsometryEquiv_dsIncl (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b i x).symm

lemma basisPiTensorEndAlgEquiv_apply_apply
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁)
    (A : L (DS n ℋ₂)) (z : ℋ₂ ⊗[ℂ] ℋ₁) :
    basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b A z =
      basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b
        (A ((basisPiTensorLinearIsometryEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b).symm z)) := by
  rfl

lemma basisPiTensorEndAlgEquiv_apply_tmul_basis
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁)
    (A : L (DS n ℋ₂)) (x : ℋ₂) (j : Fin n) :
    basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b A (x ⊗ₜ[ℂ] b j) =
      ∑ i : Fin n, ((ampCStarEquiv n ℋ₂ A) i j) x ⊗ₜ[ℂ] b i := by
  rw [basisPiTensorEndAlgEquiv_apply_apply]
  rw [basisPiTensorLinearIsometryEquiv_symm_tmul]
  rw [basisPiTensorLinearIsometryEquiv_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  have hcoord :
      dsProj n ℋ₂ i (A (dsIncl n ℋ₂ j x)) =
        ampPlainEquiv n ℋ₂ A i j x := by
    symm
    exact ampPlainEquiv_apply_apply_ds
      (k := n) (ℋ := ℋ₂) (f := A) (i := i) (j := j) (x := x)
  rw [hcoord]
  rfl

lemma matrixUnit_apply_basis
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁)
    (i j k : Fin n) :
    outer_product (b j) (b i) (b k) = if j = k then b i else 0 := by
  by_cases h : j = k
  · subst h
    simp [outer_product, dualTensorHom_apply]
  · simp [outer_product, dualTensorHom_apply, h]

lemma basisPiTensorEndAlgEquiv_expansion
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁)
    (A : L (DS n ℋ₂)) :
    basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b A =
      ∑ i : Fin n, ∑ j : Fin n,
        (endomorphismTensorEquiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
          (((ampCStarEquiv n ℋ₂ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i)) := by
  apply TensorProduct.ext'
  intro x v
  conv_lhs => rw [← b.sum_repr v]
  rw [TensorProduct.tmul_sum, map_sum]
  simp_rw [TensorProduct.tmul_smul, map_smul,
    basisPiTensorEndAlgEquiv_apply_tmul_basis]
  rw [Finset.sum_comm]
  simp [Finset.smul_sum, endomorphismTensorEquiv_symm_tmul, outer_product, dualTensorHom_apply,
    TensorProduct.tmul_smul, OrthonormalBasis.repr_apply_apply]

lemma basisPiTensorEndAlgEquiv_ampSuper
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ ℋ₁)
    (Φ : T ℋ₁ ℋ₂) (A : L (DS n ℋ₁)) :
    basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b (ampSuper n Φ A) =
      amplifyWithId Φ (basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁) n b A) := by
  rw [basisPiTensorEndAlgEquiv_expansion (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b (ampSuper n Φ A)]
  rw [basisPiTensorEndAlgEquiv_expansion (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁) n b A]
  simp only [amplifyWithId, LinearMap.comp_apply, map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  have hentry :
      (ampCStarEquiv n ℋ₂ (ampSuper n Φ A)) i j =
        Φ ((ampCStarEquiv n ℋ₁ A) i j) := by
    have h := congrFun (congrFun (ampCStarEquiv_ampSuper_apply (k := n) (Φ := Φ) (A := A)) i) j
    simpa [CStarMatrix.map_apply] using h
  have hterm :
      ((ampCStarEquiv n ℋ₂ (ampSuper n Φ A)) i j) ⊗ₜ[ℂ] outer_product (b j) (b i) =
        Φ ((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i) := by
    exact congrArg (fun B : L ℋ₂ => B ⊗ₜ[ℂ] outer_product (b j) (b i)) hentry
  have hcancel :
      (endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
          ((endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁)).symm
            (((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i))) =
        ((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i) := by
    exact LinearEquiv.apply_symm_apply (endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
      (((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i))
  apply (endomorphismTensorEquiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).injective
  rw [LinearEquiv.apply_symm_apply]
  have houter :
      (endomorphismTensorEquiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁))
          ((endomorphismTensorEquiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
            ((TensorProduct.map Φ LinearMap.id)
              ((endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
                ((endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁)).symm
                  (((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i)))))) =
        (TensorProduct.map Φ LinearMap.id)
          ((endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
            ((endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁)).symm
              (((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i)))) := by
    exact LinearEquiv.apply_symm_apply (endomorphismTensorEquiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁))
      ((TensorProduct.map Φ LinearMap.id)
        ((endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
          ((endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁)).symm
            (((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i)))))
  change
      ((ampCStarEquiv n ℋ₂ (ampSuper n Φ A)) i j) ⊗ₜ[ℂ] outer_product (b j) (b i) =
        (endomorphismTensorEquiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁))
          ((endomorphismTensorEquiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm
            ((TensorProduct.map Φ LinearMap.id)
              ((endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁))
                ((endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁)).symm
                  (((ampCStarEquiv n ℋ₁ A) i j) ⊗ₜ[ℂ] outer_product (b j) (b i))))))
  rw [houter]
  rw [hcancel]
  rw [TensorProduct.map_tmul]
  exact hterm

lemma ampSuper_krausTerm_eq
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) :
    ampSuper k (krausTerm V) = krausTerm (ampKrausFactor k V) := by
  apply LinearMap.ext
  intro A
  apply (ampCStarEquiv k ℋ₂).injective
  trans (ampCStarEquiv k ℋ₁ A).map (krausTerm V)
  · simpa using ampCStarEquiv_ampSuper_apply (k := k) (Φ := krausTerm V) (A := A)
  ext i j x
  change (((ampCStarEquiv k ℋ₁ A).map (krausTerm V)) i j) x =
    ampPlainEquiv k ℋ₂ ((krausTerm (ampKrausFactor k V)) A) i j x
  rw [ampPlainEquiv_apply_apply_ds]
  have hentry :
      (ampCStarEquiv k ℋ₁ A i j) (V.adjoint x) =
        dsProj k ℋ₁ i (A (dsIncl k ℋ₁ j (V.adjoint x))) := by
    simpa using
      (ampPlainEquiv_apply_apply_ds (k := k) (ℋ := ℋ₁) (f := A) (i := i) (j := j)
        (x := V.adjoint x)).symm
  simp [CStarMatrix.map_apply, krausTerm, dsProj_ampKrausFactor,
    ampKrausFactor_adjoint_dsIncl, hentry]

lemma isCompletelyPositive_krausTerm
    (V : ℋ₁ →ₗ[ℂ] ℋ₂) :
    IsCompletelyPositive (krausTerm V) := by
  refine (isCompletelyPositive_iff_cstarMatrix_nonneg (krausTerm V)).mpr ?_
  intro k M hM
  have hK : IsKPositive k (krausTerm V) := by
    exact (isKPositive_iff_isPositiveMap_ampSuper (k := k) (Φ := krausTerm V)).mpr <| by
      simpa [ampSuper_krausTerm_eq] using
        isPositiveMap_krausTerm (V := ampKrausFactor k V)
  exact hK M hM

lemma isCompletelyPositive_sum_krausTerm
    {σ : Type*} [Fintype σ]
    (V : σ → (ℋ₁ →ₗ[ℂ] ℋ₂)) :
    IsCompletelyPositive (∑ r, krausTerm (V r)) := by
  letI : Ring (L ℋ₁) := Module.End.instRing
  letI : Ring (L ℋ₂) := Module.End.instRing
  letI : AddCommGroup (L ℋ₁) := Module.End.instRing.toAddCommGroup
  letI : AddCommGroup (L ℋ₂) := Module.End.instRing.toAddCommGroup
  letI : Module ℂ (L ℋ₁) := LinearMap.module
  letI : Module ℂ (L ℋ₂) := LinearMap.module
  classical
  refine (isCompletelyPositive_iff_cstarMatrix_nonneg (∑ r, krausTerm (V r))).mpr ?_
  intro k M hM
  let mapped : ((L ℋ₁) →ₗ[ℂ] (L ℋ₂)) →+
      CStarMatrix (Fin k) (Fin k) (L ℋ₂) := {
    toFun := fun Ψ => M.map Ψ
    map_zero' := by
      ext i j x
      simp [CStarMatrix.map_apply]
    map_add' := by
      intro Ψ Θ
      ext i j x
      simp [CStarMatrix.map_apply] }
  change 0 ≤ mapped (∑ r, krausTerm (V r))
  rw [map_sum]
  exact Finset.sum_nonneg fun r _ =>
    (isCompletelyPositive_iff_cstarMatrix_nonneg (krausTerm (V r))).mp
      (isCompletelyPositive_krausTerm (V r)) k M hM

/--
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press,
2018), Theorem 2.22. Packaging in Lean of the finite-dimensional amplification condition in
Theorem 2.22.
-/
def AmplificationPositive (Φ : T ℋ₁ ℋ₂) : Prop :=
  IsPositiveMap (amplifyWithId Φ)

lemma cp_amplify
    (Φ : (L ℋ₁) →ₗ[ℂ] (L ℋ₂)) :
    IsCompletelyPositive Φ → AmplificationPositive Φ := by
  intro hΦ X hX
  let n := Module.finrank ℂ ℋ₁
  let b : OrthonormalBasis (Fin n) ℂ ℋ₁ := stdOrthonormalBasis ℂ ℋ₁
  let e₁ := basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁) n b
  let e₂ := basisPiTensorEndAlgEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b
  let A : L (DS n ℋ₁) := e₁.symm X
  have hA : 0 ≤ A := by
    have hX' : 0 ≤ e₁ A := by
      simpa [A, e₁] using hX
    exact (starAlgEquiv_nonneg_iff e₁).1 hX'
  have hK : IsKPositive n Φ :=
    (isCompletelyPositive_iff_cstarMatrix_nonneg Φ).mp hΦ n
  have hAmp : 0 ≤ ampSuper n Φ A :=
    (isKPositive_iff_isPositiveMap_ampSuper (k := n) (Φ := Φ)).mp hK A hA
  have hTensor : 0 ≤ e₂ (ampSuper n Φ A) :=
    starAlgEquiv_nonneg e₂ hAmp
  have hEq : e₂ (ampSuper n Φ A) = amplifyWithId Φ X := by
    simpa [A, e₁, e₂] using
      basisPiTensorEndAlgEquiv_ampSuper (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) n b Φ A
  simpa [hEq] using hTensor

end RepresentationsOfChannels

end QuantumChannel
