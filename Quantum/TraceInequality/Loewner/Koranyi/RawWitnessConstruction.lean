import Quantum.TraceInequality.Loewner.Statement
import Quantum.TraceInequality.Loewner.Koranyi.FiniteConstruction
import Quantum.TraceInequality.Loewner.Koranyi.QuadraticEstimate

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set

open scoped ComplexOrder
open scoped MatrixOrder

noncomputable section

/-- Finite-dimensional raw witness extracted from `koranyi_finite_construct`. -/
structure RawFiniteWitness {n : ℕ} (f : ℝ → ℝ) (y : Fin (n + 1) → ℝ) where
  hy : Quantum.TraceInequality.pointsHyp (n := n) y
  H : Type
  instNormedAddCommGroup : NormedAddCommGroup H
  instInnerProductSpace : InnerProductSpace ℂ H
  instFiniteDimensional : FiniteDimensional ℂ H
  v : Fin (n + 1) → H
  φ : H
  A : H →ₗ[ℂ] H
  hGram :
    ∀ i j : Fin (n + 1),
      inner (𝕜 := ℂ) (v i) (v j) = (loewnerKernel f (y i) (y j) : ℂ)
  hφ : φ = v 0
  hSpanTop : Submodule.span ℂ (Set.range v) = ⊤
  hA : IsSelfAdjoint A
  hA_apply :
    ∀ i, i ≠ 0 → A (v i) = (1 / (y i : ℂ)) • (v i - φ)
  hWitness :
    ∀ i, i ≠ 0 → v i - (y i : ℂ) • A (v i) = φ
  hNormSq :
    ∀ i, ‖v i‖ ^ 2 = loewnerKernel f (y i) (y i)
  hLinearIndependent : LinearIndependent ℂ v

attribute [instance] RawFiniteWitness.instNormedAddCommGroup
attribute [instance] RawFiniteWitness.instInnerProductSpace
attribute [instance] RawFiniteWitness.instFiniteDimensional

private theorem exists_rawFiniteWitness_of_posDef {n : ℕ} {f : ℝ → ℝ} {y : Fin (n + 1) → ℝ}
    (hy : Quantum.TraceInequality.pointsHyp (n := n) y)
    (hL : (Quantum.TraceInequality.loewnerMatrix (n := n) f y).PosDef) :
    ∃ _ : RawFiniteWitness f y, True := by
  classical
  rcases
      Quantum.TraceInequality.Loewner.exists_gram_vectors
        (n := n) (f := f) (y := y) hL.posSemidef with
    ⟨H, instN, instI, instFD, v, hGram, hSpanTop⟩
  letI : NormedAddCommGroup H := instN
  letI : InnerProductSpace ℂ H := instI
  letI : FiniteDimensional ℂ H := instFD
  let φ : H := v 0
  have hgram :
      Matrix.gram ℂ v = Quantum.TraceInequality.loewnerMatrix (n := n) f y := by
    ext i j
    simpa [Matrix.gram_apply, Quantum.TraceInequality.loewnerMatrix] using hGram i j
  have hpos : (Matrix.gram ℂ v).PosDef := by
    simpa [hgram] using hL
  have hLinearIndependent : LinearIndependent ℂ v :=
    Matrix.linearIndependent_of_posDef_gram (𝕜 := ℂ) (v := v) hpos
  have hNormSq : ∀ i, ‖v i‖ ^ 2 = loewnerKernel f (y i) (y i) := by
    intro i
    have hdiag : inner (𝕜 := ℂ) (v i) (v i) = (loewnerKernel f (y i) (y i) : ℂ) := hGram i i
    have hre := congrArg Complex.re hdiag
    simpa using ((inner_self_eq_norm_sq (𝕜 := ℂ) (x := v i)).symm.trans hre)
  have hA :
      ∃ A : H →ₗ[ℂ] H,
        IsSelfAdjoint A ∧
          (∀ i, i ≠ 0 → A (v i) = (1 / (y i : ℂ)) • (v i - φ)) := by
    have hv_sp' : (⊤ : Submodule ℂ H) ≤ Submodule.span ℂ (Set.range v) := by
      simp [hSpanTop]
    let b : Module.Basis (Fin (n + 1)) ℂ H := Module.Basis.mk hLinearIndependent hv_sp'
    have hb : ∀ i : Fin (n + 1), b i = v i := by
      intro i
      exact Module.Basis.mk_apply (hli := hLinearIndependent) (hsp := hv_sp') (v := v) i
    have inner_prescribed_symm :
        ∀ {i j : Fin (n + 1)}, i ≠ 0 → j ≠ 0 →
          inner (𝕜 := ℂ) ((1 / (y i : ℂ)) • (v i - φ)) (v j) =
            inner (𝕜 := ℂ) (v i) ((1 / (y j : ℂ)) • (v j - φ)) := by
      intro i j hi hj
      rcases hy with ⟨hy0, hyinj, _, hyne0⟩
      have hyi0 : y i ≠ 0 := hyne0 i hi
      have hyj0 : y j ≠ 0 := hyne0 j hj
      have hyi0C : (y i : ℂ) ≠ 0 := by exact_mod_cast hyi0
      have hyj0C : (y j : ℂ) ≠ 0 := by exact_mod_cast hyj0
      have hLij : inner (𝕜 := ℂ) (v i) (v j) = (loewnerKernel f (y i) (y j) : ℂ) := hGram i j
      have hL0j : inner (𝕜 := ℂ) φ (v j) = (loewnerKernel f (y 0) (y j) : ℂ) := by
        simpa [φ] using hGram 0 j
      have hLi0 : inner (𝕜 := ℂ) (v i) φ = (loewnerKernel f (y i) (y 0) : ℂ) := by
        simpa [φ] using hGram i 0
      have hy0' : y 0 = 0 := hy0
      have hKoranyi :
          (loewnerKernel f (y i) (y j) - loewnerKernel f 0 (y j)) / (y i) =
            (loewnerKernel f (y i) (y j) - loewnerKernel f (y i) 0) / (y j) := by
        by_cases hij : i = j
        · subst hij
          have hs : loewnerKernel f 0 (y i) = loewnerKernel f (y i) 0 := by
            simpa using (loewnerKernel_swap (f := f) 0 (y i))
          simp [hs, div_eq_mul_inv, sub_eq_add_neg]
        · have hyij : y i ≠ y j := by
            intro h
            exact hij (hyinj h)
          simpa [hy0'] using
            (koranyi_identity (f := f) (x := y i) (y := y j) hyi0 hyj0 hyij)
      have hKoranyiC :
          ((loewnerKernel f (y i) (y j) - loewnerKernel f 0 (y j)) / (y i) : ℂ) =
            ((loewnerKernel f (y i) (y j) - loewnerKernel f (y i) 0) / (y j) : ℂ) := by
        exact_mod_cast hKoranyi
      calc
        inner (𝕜 := ℂ) ((1 / (y i : ℂ)) • (v i - φ)) (v j)
            = (1 / (y i : ℂ)) * (inner (𝕜 := ℂ) (v i - φ) (v j)) := by
                simp [inner_smul_left]
        _ = (1 / (y i : ℂ)) * (inner (𝕜 := ℂ) (v i) (v j) - inner (𝕜 := ℂ) φ (v j)) := by
              simp [sub_eq_add_neg, inner_add_left, inner_neg_left]
        _ =
            (1 / (y i : ℂ)) *
              ((loewnerKernel f (y i) (y j) : ℂ) -
                (loewnerKernel f 0 (y j) : ℂ)) := by
              simp [hLij, hL0j, hy0', sub_eq_add_neg]
        _ = ((loewnerKernel f (y i) (y j) - loewnerKernel f 0 (y j)) / (y i) : ℂ) := by
              simp [div_eq_mul_inv, mul_comm, sub_eq_add_neg]
        _ = ((loewnerKernel f (y i) (y j) - loewnerKernel f (y i) 0) / (y j) : ℂ) := by
              simpa using hKoranyiC
        _ =
            (1 / (y j : ℂ)) *
              ((loewnerKernel f (y i) (y j) : ℂ) -
                (loewnerKernel f (y i) 0 : ℂ)) := by
              simp [div_eq_mul_inv, mul_comm, sub_eq_add_neg]
        _ = (1 / (y j : ℂ)) * (inner (𝕜 := ℂ) (v i) (v j) - inner (𝕜 := ℂ) (v i) φ) := by
              simp [hLij, hLi0, hy0', φ, sub_eq_add_neg]
        _ = (1 / (y j : ℂ)) * inner (𝕜 := ℂ) (v i) (v j - φ) := by
              simp [inner_sub_right]
        _ = inner (𝕜 := ℂ) (v i) ((1 / (y j : ℂ)) • (v j - φ)) := by
              simp [inner_smul_right]
    let ι₁ : Type := { i : Fin (n + 1) // i ≠ 0 }
    let v₁ : ι₁ → H := fun i => v i.1
    let K : Submodule ℂ H := Submodule.span ℂ (Set.range v₁)
    letI : IsUniformAddGroup K := K.toAddSubgroup.isUniformAddGroup
    letI : @CompleteSpace K (@PseudoMetricSpace.toUniformSpace K
        (@SeminormedAddCommGroup.toPseudoMetricSpace K
          (@NormedAddCommGroup.toSeminormedAddCommGroup K inferInstance))) :=
      FiniteDimensional.complete ℂ K
    have hv₁_mem : ∀ i : ι₁, v₁ i ∈ K := fun i => Submodule.subset_span ⟨i, rfl⟩
    have hv₁_li : LinearIndependent ℂ v₁ :=
      hLinearIndependent.comp (fun i : ι₁ => (i : Fin (n + 1))) Subtype.coe_injective
    let vK : ι₁ → K := fun i => ⟨v₁ i, hv₁_mem i⟩
    have hvK_li : LinearIndependent ℂ vK := by
      have hcomp : LinearIndependent ℂ (K.subtype ∘ vK) := by
        simpa [vK, v₁] using hv₁_li
      exact LinearIndependent.of_comp K.subtype hcomp
    have hvK_span : Submodule.span ℂ (Set.range vK) = ⊤ := by
      simpa [vK, K, v₁] using
        (Submodule.span_range_subtype_eq_top_iff (R := ℂ) (p := K) (s := v₁) hv₁_mem).2 rfl
    have hvK_sp' : (⊤ : Submodule ℂ K) ≤ Submodule.span ℂ (Set.range vK) := by
      simp [hvK_span]
    let bK : Module.Basis ι₁ ℂ K := Module.Basis.mk hvK_li hvK_sp'
    let Agen₁ : ι₁ → H := fun i => (1 / (y i.1 : ℂ)) • (v i.1 - φ)
    let ℓ : K →ₗ[ℂ] ℂ := (bK.constr ℂ fun i => inner (𝕜 := ℂ) (v 0) (Agen₁ i))
    let ℓc : StrongDual ℂ K :=
      (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := K) (F' := ℂ)) ℓ
    let wK : K := (InnerProductSpace.toDual ℂ K).symm ℓc
    let w0_base : H := (wK : H)
    haveI : K.HasOrthogonalProjection := by infer_instance
    let u : H := (v 0) - K.starProjection (v 0)
    have huK : ∀ x ∈ K, inner (𝕜 := ℂ) u x = 0 := by
      intro x hx
      simpa [u] using (K.starProjection_inner_eq_zero (v := v 0) x hx)
    have hu0 : u ≠ 0 := by
      intro hu
      have hv0_mem : v 0 ∈ K := by
        have : K.starProjection (v 0) = v 0 := by
          have : (v 0) - K.starProjection (v 0) = 0 := by simpa [u] using hu
          exact (sub_eq_zero.mp this).symm
        simpa [K.starProjection_eq_self_iff] using this
      have hrange : Set.range v₁ = v '' ({0}ᶜ : Set (Fin (n + 1))) := by
        ext x
        constructor
        · rintro ⟨i, rfl⟩
          refine ⟨i.1, ?_, rfl⟩
          exact i.2
        · rintro ⟨i, hi, rfl⟩
          refine ⟨⟨i, ?_⟩, rfl⟩
          simpa using hi
      have hv0_not :
          v 0 ∉ Submodule.span ℂ (v '' ({0}ᶜ : Set (Fin (n + 1)))) := by
        simpa using (hLinearIndependent.notMem_span 0)
      have : v 0 ∈ Submodule.span ℂ (v '' ({0}ᶜ : Set (Fin (n + 1)))) := by
        simpa [K, hrange] using hv0_mem
      exact hv0_not this
    have hu_inner : inner (𝕜 := ℂ) u (v 0) = inner (𝕜 := ℂ) u u := by
      have hproj_mem : K.starProjection (v 0) ∈ K := K.starProjection_apply_mem (x := v 0)
      calc
        inner (𝕜 := ℂ) u (v 0)
            = inner (𝕜 := ℂ) u (u + K.starProjection (v 0)) := by
                simp [u, sub_add_cancel]
        _ = inner (𝕜 := ℂ) u u + inner (𝕜 := ℂ) u (K.starProjection (v 0)) := by
              simp [inner_add_right]
        _ = inner (𝕜 := ℂ) u u := by
              have : inner (𝕜 := ℂ) u (K.starProjection (v 0)) = 0 := by
                simpa using (huK (K.starProjection (v 0)) hproj_mem)
              simp [this]
    have hu_inner_ne0 : inner (𝕜 := ℂ) u (v 0) ≠ 0 := by
      have huu_ne0 : inner (𝕜 := ℂ) u u ≠ 0 :=
        (inner_self_ne_zero (𝕜 := ℂ) (x := u)).2 hu0
      simpa [hu_inner] using huu_ne0
    let u' : H := (1 / star (inner (𝕜 := ℂ) u (v 0))) • u
    have hu'_inner : inner (𝕜 := ℂ) u' (v 0) = (1 : ℂ) := by
      calc
        inner (𝕜 := ℂ) u' (v 0)
            = star (1 / star (inner (𝕜 := ℂ) u (v 0))) * inner (𝕜 := ℂ) u (v 0) := by
                simp [u', inner_smul_left]
        _ = (1 / inner (𝕜 := ℂ) u (v 0)) * inner (𝕜 := ℂ) u (v 0) := by
              simp
        _ = (1 : ℂ) := by
              field_simp [hu_inner_ne0]
    let a : ℂ := inner (𝕜 := ℂ) w0_base (v 0)
    let α : ℂ := (Complex.im a) * Complex.I
    let w0 : H := w0_base + α • u'
    let w : Fin (n + 1) → H :=
      fun i => if h : i = 0 then w0 else (1 / (y i : ℂ)) • (v i - φ)
    let A : H →ₗ[ℂ] H := b.constr ℂ w
    have hA_apply' : ∀ i, i ≠ 0 → A (v i) = (1 / (y i : ℂ)) • (v i - φ) := by
      intro i hi
      have : (A (b i)) = w i := by
        change (b.constr ℂ w) (b i) = w i
        exact b.constr_basis (S := ℂ) (f := w) i
      have hbvi : b i = v i := hb i
      simp [hbvi, w, hi] at this
      simpa [hbvi] using this
    have hb0 : b 0 = v 0 := hb 0
    have hAv0 : A (v 0) = w0 := by
      have : A (b 0) = w 0 := by
        change (b.constr ℂ w) (b 0) = w 0
        exact b.constr_basis (S := ℂ) (f := w) 0
      have : A (b 0) = w0 := by simpa [w] using this
      simpa [hb0] using this
    have h00 : inner (𝕜 := ℂ) (A (v 0)) (v 0) = inner (𝕜 := ℂ) (v 0) (A (v 0)) := by
      have him : (inner (𝕜 := ℂ) w0 (v 0)).im = 0 := by
        simp [w0, a, α, inner_add_left, inner_smul_left, hu'_inner]
      have hstar : star (inner (𝕜 := ℂ) w0 (v 0)) = inner (𝕜 := ℂ) w0 (v 0) := by
        simpa [Complex.star_def] using (Complex.conj_eq_iff_im).2 him
      have hz : star (inner (𝕜 := ℂ) w0 (v 0)) = inner (𝕜 := ℂ) (v 0) w0 := by
        exact inner_conj_symm (v 0) w0
      calc
        inner (𝕜 := ℂ) (A (v 0)) (v 0) = inner (𝕜 := ℂ) w0 (v 0) := by
          simp [hAv0]
        _ = star (inner (𝕜 := ℂ) w0 (v 0)) := by simpa using hstar.symm
        _ = inner (𝕜 := ℂ) (v 0) w0 := hz
        _ = inner (𝕜 := ℂ) (v 0) (A (v 0)) := by simp [hAv0]
    have h0j : ∀ j : Fin (n + 1), j ≠ 0 →
        inner (𝕜 := ℂ) (A (v 0)) (v j) = inner (𝕜 := ℂ) (v 0) (A (v j)) := by
      intro j hj0
      have hvj_mem : v j ∈ K := by
        refine Submodule.subset_span ?_
        exact ⟨⟨j, hj0⟩, rfl⟩
      let xK : K := ⟨v j, hvj_mem⟩
      have hu'K : inner (𝕜 := ℂ) u' (v j) = 0 := by
        have : inner (𝕜 := ℂ) u (v j) = 0 := huK (v j) hvj_mem
        simp [u', inner_smul_left, this]
      have hw_toDual : inner (𝕜 := ℂ) wK xK = ℓc xK := by
        dsimp [wK]
        exact InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := K) (x := xK) (y := ℓc)
      have hbKj : bK ⟨j, hj0⟩ = vK ⟨j, hj0⟩ := by
        exact
          Module.Basis.mk_apply (hli := hvK_li) (hsp := hvK_sp') (v := vK) ⟨j, hj0⟩
      have hℓx : ℓ xK = inner (𝕜 := ℂ) (v 0) (Agen₁ ⟨j, hj0⟩) := by
        have : ℓ (bK ⟨j, hj0⟩) = inner (𝕜 := ℂ) (v 0) (Agen₁ ⟨j, hj0⟩) := by
          simpa [ℓ] using
            (bK.constr_basis (S := ℂ) (f := fun i => inner (𝕜 := ℂ) (v 0) (Agen₁ i)) ⟨j, hj0⟩)
        simpa [xK, vK, hbKj] using this
      have hw0_base :
          inner (𝕜 := ℂ) w0_base (v j) = inner (𝕜 := ℂ) (v 0) (Agen₁ ⟨j, hj0⟩) := by
        have : inner (𝕜 := ℂ) wK xK = ℓ xK := by
          simpa [ℓc] using hw_toDual
        have : inner (𝕜 := ℂ) w0_base (v j) = ℓ xK := by
          simpa [w0_base, xK] using (Submodule.coe_inner K wK xK).symm.trans this
        simp [this, hℓx]
      have hAvj : A (v j) = Agen₁ ⟨j, hj0⟩ := by
        simpa [Agen₁] using hA_apply' j hj0
      calc
        inner (𝕜 := ℂ) (A (v 0)) (v j) = inner (𝕜 := ℂ) w0 (v j) := by
          simp [hAv0]
        _ = inner (𝕜 := ℂ) w0_base (v j) + inner (𝕜 := ℂ) (α • u') (v j) := by
              simp [w0, inner_add_left]
        _ = inner (𝕜 := ℂ) w0_base (v j) := by
              simp [inner_smul_left, hu'K]
        _ = inner (𝕜 := ℂ) (v 0) (A (v j)) := by
              simpa [hAvj] using hw0_base
    have hsymm_on_v :
        ∀ i j : Fin (n + 1),
          inner (𝕜 := ℂ) (A (v i)) (v j) = inner (𝕜 := ℂ) (v i) (A (v j)) := by
      intro i j
      by_cases hi : i = 0
      · subst hi
        by_cases hj : j = 0
        · subst hj
          exact h00
        · exact h0j j hj
      · by_cases hj : j = 0
        · subst hj
          have h := h0j i hi
          have h' :
              star (inner (𝕜 := ℂ) (A (v 0)) (v i)) =
                star (inner (𝕜 := ℂ) (v 0) (A (v i))) := congrArg star h
          simpa [inner_conj_symm] using h'.symm
        · have hAi : A (v i) = (1 / (y i : ℂ)) • (v i - φ) := hA_apply' i hi
          have hAj : A (v j) = (1 / (y j : ℂ)) • (v j - φ) := hA_apply' j hj
          simpa [hAi, hAj] using inner_prescribed_symm (i := i) (j := j) hi hj
    have hsymm_basis :
        ∀ i j : Fin (n + 1),
          inner (𝕜 := ℂ) (A (b i)) (b j) = inner (𝕜 := ℂ) (b i) (A (b j)) := by
      intro i j
      simpa [hb i, hb j] using hsymm_on_v i j
    have hsymm : A.IsSymmetric := by
      intro x y
      set sx : Finset (Fin (n + 1)) := Finset.univ
      set sy : Finset (Fin (n + 1)) := Finset.univ
      set fx : Fin (n + 1) → H := fun i => (b.repr x i) • b i
      set fy : Fin (n + 1) → H := fun j => (b.repr y j) • b j
      have hx : x = ∑ i ∈ sx, fx i := by
        exact (b.sum_repr x).symm
      have hy : y = ∑ j ∈ sy, fy j := by
        exact (b.sum_repr y).symm
      rw [hx, hy]
      rw [map_sum (g := A) (f := fx) (s := sx)]
      rw [map_sum (g := A) (f := fy) (s := sy)]
      rw [sum_inner sx (fun i => A (fx i)) (∑ j ∈ sy, fy j)]
      rw [sum_inner sx fx (∑ j ∈ sy, A (fy j))]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [inner_sum sy fy (A (fx i))]
      rw [inner_sum sy (fun j => A (fy j)) (fx i)]
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hL :
          inner (𝕜 := ℂ) (A (fx i)) (fy j)
            =
              (starRingEnd ℂ) (b.repr x i) * (b.repr y j) *
                inner (𝕜 := ℂ) (A (b i)) (b j) := by
        dsimp [fx, fy]
        calc
          inner (𝕜 := ℂ) (A ((b.repr x i) • b i)) ((b.repr y j) • b j)
              = inner (𝕜 := ℂ) ((b.repr x i) • A (b i)) ((b.repr y j) • b j) := by
                  simp
          _ = (starRingEnd ℂ) (b.repr x i) * inner (𝕜 := ℂ) (A (b i)) ((b.repr y j) • b j) := by
                simp [inner_smul_left]
          _ =
              (starRingEnd ℂ) (b.repr x i) *
                ((b.repr y j) * inner (𝕜 := ℂ) (A (b i)) (b j)) := by
                simp [inner_smul_right]
          _ =
              (starRingEnd ℂ) (b.repr x i) * (b.repr y j) *
                inner (𝕜 := ℂ) (A (b i)) (b j) := by
                simp [mul_assoc]
      have hR :
          inner (𝕜 := ℂ) (fx i) (A (fy j))
            =
              (starRingEnd ℂ) (b.repr x i) * (b.repr y j) *
                inner (𝕜 := ℂ) (b i) (A (b j)) := by
        dsimp [fx, fy]
        calc
          inner (𝕜 := ℂ) ((b.repr x i) • b i) (A ((b.repr y j) • b j))
              = inner (𝕜 := ℂ) ((b.repr x i) • b i) ((b.repr y j) • A (b j)) := by
                  simp
          _ =
              (starRingEnd ℂ) (b.repr x i) *
                inner (𝕜 := ℂ) (b i) ((b.repr y j) • A (b j)) := by
                simp [inner_smul_left]
          _ =
              (starRingEnd ℂ) (b.repr x i) *
                ((b.repr y j) * inner (𝕜 := ℂ) (b i) (A (b j))) := by
                simp [inner_smul_right]
          _ =
              (starRingEnd ℂ) (b.repr x i) * (b.repr y j) *
                inner (𝕜 := ℂ) (b i) (A (b j)) := by
                simp [mul_assoc]
      simp [hL, hR, hsymm_basis, mul_assoc]
    refine ⟨A, ?_, hA_apply'⟩
    exact (LinearMap.isSymmetric_iff_isSelfAdjoint (A := A)).1 hsymm
  rcases hA with ⟨A, hA_sa, hA_apply⟩
  refine ⟨{ H := H
            hy := hy
            instNormedAddCommGroup := instN
            instInnerProductSpace := instI
            instFiniteDimensional := instFD
            v := v
            φ := φ
            A := A
            hGram := hGram
            hφ := rfl
            hSpanTop := hSpanTop
            hA := hA_sa
            hA_apply := hA_apply
            hWitness := ?_
            hNormSq := hNormSq
            hLinearIndependent := hLinearIndependent }, trivial⟩
  intro i hi
  rcases hy with ⟨_, _, _, hyne0⟩
  have hyi0 : (y i : ℂ) ≠ 0 := by
    exact_mod_cast (hyne0 i hi)
  calc
    v i - (y i : ℂ) • A (v i)
        = v i - (y i : ℂ) • ((1 / (y i : ℂ)) • (v i - φ)) := by
            simp [hA_apply i hi]
    _ = v i - ((y i : ℂ) * (1 / (y i : ℂ))) • (v i - φ) := by
          simp [smul_smul]
    _ = v i - (1 : ℂ) • (v i - φ) := by
          simp [div_eq_mul_inv, hyi0]
    _ = v i - (v i - φ) := by simp
    _ = φ := by
          simp [sub_eq_add_neg, add_comm]

/-- Noncomputable extraction of the raw finite witness from Step 2. -/
noncomputable def rawFiniteWitness_of_posDef {n : ℕ} {f : ℝ → ℝ} {y : Fin (n + 1) → ℝ}
    (hy : Quantum.TraceInequality.pointsHyp (n := n) y)
    (hL : (Quantum.TraceInequality.loewnerMatrix (n := n) f y).PosDef) :
    RawFiniteWitness f y :=
  Classical.choose (exists_rawFiniteWitness_of_posDef (f := f) (y := y) hy hL)

end

end Loewner
end TraceInequality
end Quantum
