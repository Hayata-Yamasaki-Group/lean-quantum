/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.Channel.Basic
import Quantum.QuantumMechanics.OperatorBridge

/-!
Complete positivity, matrix amplification predicates, and Kraus-term amplification tools.
-/

namespace QuantumChannel

open QuantumState
open TensorProduct

universe u v w

section RepresentationsOfChannels

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]

/-! ### Complete positivity and matrix amplification predicates -/
-- Proposition 2.17 https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudit ℋ, and any P ∈ Pos(ℋ),
-- the map Φ(α):=αP ∈ T(ℂ,ℋ) is a completely positive ContinuourLinearMap.

-- Proposition 2.18 and its remark https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudits ℋ₁, ℋ₂, and any Φ ∈ T(ℋ₁,ℋ₂),
-- if Φ is a completely positive ContinuourLinearMap,
-- the adjoint map of Φ is a completely positive ContinuourLinearMap.

-- Corollary 2.19 https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudit ℋ, Tr ∈ T(ℋ,ℂ) is a completely positive ContinuourLinearMap.

-- Proposition 2.20 https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudits ℋ₁, ℋ₂, and any Φ ∈ T(ℋ₁,ℋ₂),
-- J(Φ)=∑_{a∈Σ} vec(Aₐ) vec(Bₐ)†
-- if and only if
-- for ℋ₃=ℂ^Σ, A,B∈(ℋ₁→L[ℂ]ℋ₂⊗ℋ₃) defined as
-- A=∑_{a∈Σ}Aₐ⊗eₐ,
-- B=∑_{a∈Σ}Aₐ⊗eₐ,
-- it holds for all X∈L(X) that
-- Φ(X)=Tr₃[Aₐ X Bₐ†]

-- Theorem 2.22 https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf
-- For any qudits ℋ₁, ℋ₂, and any Φ ∈ T(ℋ₁,ℋ₂), the following statements are equivalent:
-- 1: Φ is a completely positive ContinuosLinearMap;
-- 2: J(Φ) ∈ Pos(ℋ₂⊗ℋ₁);
-- 3: ∃qudit ℋ₃, ∃A∈(ℋ₁→L[ℂ]ℋ₂⊗ℋ₃), Φ(X)=Tr₃[A X A†]

theorem card_nonzero_eigenvalues_eq_finrank_range
    {E : Type u} [Qudit E] (T : L E) (hT : 0 ≤ T) :
    let n := Module.finrank ℂ E
    let hSym : T.IsSymmetric := (LinearMap.nonneg_iff_isPositive T).mp hT |>.isSymmetric
    Fintype.card { i : Fin n // hSym.eigenvalues rfl i ≠ 0 } =
      Module.finrank ℂ (LinearMap.range T) := by
  classical
  dsimp
  let n := Module.finrank ℂ E
  let hSym : T.IsSymmetric := (LinearMap.nonneg_iff_isPositive T).mp hT |>.isSymmetric
  have hzero :
      Fintype.card { i : Fin n // hSym.eigenvalues rfl i = 0 } =
        Module.finrank ℂ (LinearMap.ker T) := by
    have hzero' := hSym.card_filter_eigenvalues_eq (hn := rfl) (μ := (0 : ℝ))
    have hker :
        Module.finrank ℂ (Module.End.eigenspace T 0) = Module.finrank ℂ (LinearMap.ker T) := by
      simpa using congrArg (fun S : Submodule ℂ E => Module.finrank ℂ S)
        (Module.End.eigenspace_zero (R := ℂ) T)
    simpa [Fintype.card_subtype] using hzero'.trans hker
  have hcard :
      Fintype.card { i : Fin n // hSym.eigenvalues rfl i ≠ 0 } =
        n - Module.finrank ℂ (LinearMap.ker T) := by
    rw [Fintype.card_subtype_compl]
    simp [n, hzero]
  rw [hcard]
  exact by
    simp [n, (Nat.eq_sub_of_add_eq (LinearMap.finrank_range_add_finrank_ker T)).symm]

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/--
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press, 2018), Eq.
(1.123). Correspondence with the domain extended to zero-dimensional Hilbert spaces as well.
-/
def IsPositiveMap (Φ : T ℋ₁ ℋ₂) : Prop :=
  ∀ X : L ℋ₁, 0 ≤ X → 0 ≤ Φ X

def IsKPositive (k : ℕ) (Φ : (L ℋ₁) →ₗ[ℂ] (L ℋ₂)) : Prop :=
  ∀ M : CStarMatrix (Fin k) (Fin k) (L ℋ₁), 0 ≤ M → 0 ≤ M.map Φ

/--
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press, 2018)
chapter-level reference (no numbered correspondence).
-/
noncomputable def amplifyWithId (Φ : T ℋ₁ ℋ₂) : T (ℋ₁ ⊗[ℂ] ℋ₁) (ℋ₂ ⊗[ℂ] ℋ₁) :=
  ((endomorphismTensorEquiv (ℋ₁ := ℋ₂) (ℋ₂ := ℋ₁)).symm :
      (L ℋ₂ ⊗[ℂ] L ℋ₁) →ₗ[ℂ] L (ℋ₂ ⊗[ℂ] ℋ₁))
    ∘ₗ (TensorProduct.map Φ LinearMap.id)
    ∘ₗ (endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₁) :
      L (ℋ₁ ⊗[ℂ] ℋ₁) →ₗ[ℂ] (L ℋ₁ ⊗[ℂ] L ℋ₁))

/--
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press, 2018), Eq.
(1.124) / Theorem 2.22. The definition in Eq. (1.124) is packaged as a Lean existential predicate,
also allowing zero dimensions. This definition does not assert
the whole group of equivalences of Theorem 2.22.
-/
def IsCompletelyPositive (Φ : T ℋ₁ ℋ₂) : Prop :=
  ∃ Ψ : CompletelyPositiveMap (L ℋ₁) (L ℋ₂), Ψ.toLinearMap = Φ

/--
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press, 2018)
chapter-level reference (no numbered correspondence).
-/
theorem isCompletelyPositive_iff_cstarMatrix_nonneg
    (Φ : (L ℋ₁) →ₗ[ℂ] (L ℋ₂)) :
    IsCompletelyPositive Φ ↔
      ∀ (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) (L ℋ₁)),
        0 ≤ M → 0 ≤ M.map Φ := by
  constructor
  · rintro ⟨Ψ, hΨ⟩ k M hM
    rw [← hΨ]
    exact Ψ.map_cstarMatrix_nonneg' k M hM
  · intro hΦ
    exact ⟨{ Φ with map_cstarMatrix_nonneg' := hΦ }, rfl⟩

abbrev DS (k : ℕ) (ℋ : Type u) := PiLp 2 (fun _ : Fin k => ℋ)

noncomputable instance dsFiniteDimensional (k : ℕ) (ℋ : Type u) [Qudit ℋ] :
    FiniteDimensional ℂ (DS k ℋ) :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm.toLinearEquiv).finiteDimensional

noncomputable instance dsQudit (k : ℕ) (ℋ : Type u) [Qudit ℋ] : Qudit (DS k ℋ) where
  toNormedAddCommGroup := inferInstance
  toInnerProductSpace := inferInstance
  toCompleteSpace := inferInstance
  fg_top := by
    letI : Module.Finite ℂ (DS k ℋ) := dsFiniteDimensional k ℋ
    simpa using (Module.Finite.fg_top (R := ℂ) (M := DS k ℋ))

noncomputable def ampPlainEquiv (k : ℕ) (ℋ : Type u) [Qudit ℋ] :
    L (DS k ℋ) ≃ₐ[ℂ] Matrix (Fin k) (Fin k) (L ℋ) :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).toLinearEquiv.conjAlgEquiv ℂ).trans
    (endVecAlgEquivMatrixEnd (ι := Fin k) (R := ℂ) (A := ℂ) (M := ℋ))

lemma ampPlainEquiv_apply_apply
    (k : ℕ) (ℋ : Type u) [Qudit ℋ]
    (f : L (DS k ℋ)) (i j : Fin k) (x : ℋ) :
    ampPlainEquiv k ℋ f i j x =
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ))
        (f (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm) (Pi.single j x))) i := by
  rfl

lemma inner_symm_single
    (k : ℕ) (ℋ : Type u) [Qudit ℋ]
    (v : DS k ℋ) (i : Fin k) (x : ℋ) :
    inner ℂ v (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm) (Pi.single i x)) =
      inner ℂ (v i) x := by
  rw [PiLp.inner_apply]
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro hi
    simp at hi

lemma inner_single_symm
    (k : ℕ) (ℋ : Type u) [Qudit ℋ]
    (i : Fin k) (x : ℋ) (v : DS k ℋ) :
    inner ℂ (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm) (Pi.single i x)) v =
      inner ℂ x (v i) := by
  rw [PiLp.inner_apply]
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro hi
    simp at hi

lemma inner_coord_right
    (k : ℕ) (ℋ : Type u) [Qudit ℋ]
    (z : DS k ℋ) (i : Fin k) (y : ℋ) :
    inner ℂ ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)) z i) y =
      inner ℂ z (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm) (Pi.single i y)) := by
  simpa using (inner_symm_single (k := k) (ℋ := ℋ) (v := z) (i := i) (x := y)).symm

lemma inner_coord_left
    (k : ℕ) (ℋ : Type u) [Qudit ℋ]
    (i : Fin k) (x : ℋ) (z : DS k ℋ) :
    inner ℂ x ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)) z i) =
      inner ℂ (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm) (Pi.single i x)) z := by
  simpa using (inner_single_symm (k := k) (ℋ := ℋ) (i := i) (x := x) (v := z)).symm

lemma ampPlainEquiv_map_star
    (k : ℕ) (ℋ : Type u) [Qudit ℋ]
    (f : L (DS k ℋ)) :
    ampPlainEquiv k ℋ (star f) = star (ampPlainEquiv k ℋ f) := by
  ext i j x
  apply ext_inner_right ℂ
  intro y
  rw [ampPlainEquiv_apply_apply, Matrix.star_apply]
  have hstar :
      inner ℂ ((star ((ampPlainEquiv k ℋ) f j i)) x) y =
        inner ℂ x ((ampPlainEquiv k ℋ f j i) y) := by
    change inner ℂ (((ampPlainEquiv k ℋ f j i)†) x) y =
      inner ℂ x ((ampPlainEquiv k ℋ f j i) y)
    simpa using
      (LinearMap.adjoint_inner_left (A := ampPlainEquiv k ℋ f j i) (x := y) (y := x))
  rw [hstar, ampPlainEquiv_apply_apply, inner_coord_right, inner_coord_left]
  simpa using
    (LinearMap.adjoint_inner_left
      (A := f)
      (x := ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm (Pi.single i y)))
      (y := ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℋ)).symm (Pi.single j x))))

noncomputable def ampMatrixStarAlgEquiv (k : ℕ) (ℋ : Type u) [Qudit ℋ] :
    L (DS k ℋ) ≃⋆ₐ[ℂ] Matrix (Fin k) (Fin k) (L ℋ) :=
  StarAlgEquiv.ofAlgEquiv (ampPlainEquiv k ℋ) (ampPlainEquiv_map_star (k := k) (ℋ := ℋ))

noncomputable def ampCStarEquiv (k : ℕ) (ℋ : Type u) [Qudit ℋ] :
    L (DS k ℋ) ≃⋆ₐ[ℂ] CStarMatrix (Fin k) (Fin k) (L ℋ) :=
  (ampMatrixStarAlgEquiv k ℋ).trans CStarMatrix.ofMatrixStarAlgEquiv

noncomputable def ampSuper
    (k : ℕ) (Φ : T ℋ₁ ℋ₂) : T (DS k ℋ₁) (DS k ℋ₂) :=
  (ampCStarEquiv k ℋ₂).symm.toAlgEquiv.toLinearMap ∘ₗ
    (CStarMatrix.mapₗ Φ) ∘ₗ
      (ampCStarEquiv k ℋ₁).toAlgEquiv.toLinearMap

lemma ampCStarEquiv_ampSuper_apply
    (k : ℕ) (Φ : T ℋ₁ ℋ₂) (A : L (DS k ℋ₁)) :
    ampCStarEquiv k ℋ₂ (ampSuper k Φ A) = (ampCStarEquiv k ℋ₁ A).map Φ := by
  change
    ampCStarEquiv k ℋ₂
      ((ampCStarEquiv k ℋ₂).symm (((ampCStarEquiv k ℋ₁) A).map Φ)) =
        ((ampCStarEquiv k ℋ₁) A).map Φ
  exact (ampCStarEquiv k ℋ₂).apply_symm_apply _

lemma starAlgEquiv_mem_nonnegClosure
    {A B : Type*}
    [Semiring A] [StarRing A] [Algebra ℂ A] [PartialOrder A] [StarOrderedRing A]
    [Semiring B] [StarRing B] [Algebra ℂ B] [PartialOrder B] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B) {x : A}
    (hx : x ∈ AddSubmonoid.closure (Set.range fun s : A => star s * s)) :
    e x ∈ AddSubmonoid.closure (Set.range fun t : B => star t * t) := by
  induction hx using AddSubmonoid.closure_induction with
  | mem y hy =>
      obtain ⟨s, rfl⟩ := hy
      refine AddSubmonoid.subset_closure ⟨e s, ?_⟩
      simpa using congrArg (fun z => z * e s) (map_star e s).symm
  | zero =>
      rw [map_zero]
      exact AddSubmonoid.zero_mem (AddSubmonoid.closure (Set.range fun t : B => star t * t))
  | add y z _ _ ihy ihz =>
      rw [map_add]
      exact AddSubmonoid.add_mem (AddSubmonoid.closure (Set.range fun t : B => star t * t)) ihy ihz

lemma starAlgEquiv_nonneg
    {A B : Type*}
    [Semiring A] [StarRing A] [Algebra ℂ A] [PartialOrder A] [StarOrderedRing A]
    [Semiring B] [StarRing B] [Algebra ℂ B] [PartialOrder B] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B) {x : A} (hx : 0 ≤ x) :
    0 ≤ e x := by
  refine StarOrderedRing.nonneg_iff.mpr ?_
  exact starAlgEquiv_mem_nonnegClosure e (StarOrderedRing.nonneg_iff.mp hx)

/-- A star algebra equivalence is monotone for the positive-cone order. -/
@[gcongr]
lemma starAlgEquiv_le_starAlgEquiv
    {A B : Type*}
    [Semiring A] [StarRing A] [Algebra ℂ A] [PartialOrder A] [StarOrderedRing A]
    [Semiring B] [StarRing B] [Algebra ℂ B] [PartialOrder B] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B) {x y : A} (hxy : x ≤ y) :
    e x ≤ e y := by
  exact OrderHomClass.monotone e hxy

lemma starAlgEquiv_nonneg_iff
    {A B : Type*}
    [Semiring A] [StarRing A] [Algebra ℂ A] [PartialOrder A] [StarOrderedRing A]
    [Semiring B] [StarRing B] [Algebra ℂ B] [PartialOrder B] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B) {x : A} :
    0 ≤ e x ↔ 0 ≤ x := by
  constructor
  · intro hx
    simpa using starAlgEquiv_nonneg e.symm hx
  · intro hx
    exact starAlgEquiv_nonneg e hx

lemma isKPositive_iff_isPositiveMap_ampSuper
    (k : ℕ) (Φ : (L ℋ₁) →ₗ[ℂ] (L ℋ₂)) :
    IsKPositive k Φ ↔ IsPositiveMap (ampSuper k Φ) := by
  constructor
  · intro hΦ A hA
    have hAmap : 0 ≤ ampCStarEquiv k ℋ₁ A :=
      starAlgEquiv_nonneg (ampCStarEquiv k ℋ₁) hA
    have hMapped : 0 ≤ (ampCStarEquiv k ℋ₁ A).map Φ := hΦ _ hAmap
    have hMap : 0 ≤ ampCStarEquiv k ℋ₂ (ampSuper k Φ A) := by
      rw [ampCStarEquiv_ampSuper_apply]
      exact hMapped
    exact (starAlgEquiv_nonneg_iff (ampCStarEquiv k ℋ₂)).1 hMap
  · intro hΦ M hM
    let A : L (DS k ℋ₁) := (ampCStarEquiv k ℋ₁).symm M
    have hMA : ampCStarEquiv k ℋ₁ A = M := by simp [A]
    have hA : 0 ≤ A := by
      apply (starAlgEquiv_nonneg_iff (ampCStarEquiv k ℋ₁)).1
      exact hMA.symm ▸ hM
    have hAmp : 0 ≤ ampSuper k Φ A := hΦ A hA
    have hMap : 0 ≤ ampCStarEquiv k ℋ₂ (ampSuper k Φ A) :=
      starAlgEquiv_nonneg (ampCStarEquiv k ℋ₂) hAmp
    have hMapped : 0 ≤ M.map Φ := by
      rw [← hMA, ← ampCStarEquiv_ampSuper_apply]
      exact hMap
    exact hMapped

theorem isPositiveMap_of_cp
    (Φ : (L ℋ₁) →ₗ[ℂ] (L ℋ₂)) :
    IsCompletelyPositive Φ → IsPositiveMap Φ := by
  rintro ⟨Ψ, hΨ⟩ X hX
  rw [← hΨ]
  exact map_nonneg Ψ hX

/-! ### Kraus terms and diagonal amplifications -/
lemma isPositiveMap_conjugate
    {ℋ₃ : Type w} [Qudit ℋ₃]
    (A : ℋ₁ →ₗ[ℂ] ℋ₃) :
    IsPositiveMap
      { toFun := fun X => A.comp (X.comp (LinearMap.adjoint A))
        map_add' := by
          intro X Y
          ext x
          simp
        map_smul' := by
          intro c X
          ext x
          simp } := by
  intro X hX
  exact (LinearMap.nonneg_iff_isPositive _).mpr <|
    (LinearMap.nonneg_iff_isPositive X).mp hX |>.conj_adjoint A

/-- The bundled conjugation map associated to a linear map is monotone for the operator order. -/
@[gcongr]
lemma conjugate_map_le_map
    {ℋ₃ : Type w} [Qudit ℋ₃]
    (A : ℋ₁ →ₗ[ℂ] ℋ₃) {X Y : L ℋ₁} (hXY : X ≤ Y) :
    ({ toFun := fun X => A.comp (X.comp (LinearMap.adjoint A))
       map_add' := by
         intro X Y
         ext x
         simp
       map_smul' := by
         intro c X
         ext x
         simp } : T ℋ₁ ℋ₃) X ≤
    ({ toFun := fun X => A.comp (X.comp (LinearMap.adjoint A))
       map_add' := by
         intro X Y
         ext x
         simp
       map_smul' := by
         intro c X
         ext x
         simp } : T ℋ₁ ℋ₃) Y := by
  let Φ : T ℋ₁ ℋ₃ :=
    { toFun := fun X => A.comp (X.comp (LinearMap.adjoint A))
      map_add' := by
        intro X Y
        ext x
        simp
      map_smul' := by
        intro c X
        ext x
        simp }
  change Φ X ≤ Φ Y
  have hpos : 0 ≤ Φ (Y - X) :=
    isPositiveMap_conjugate A (Y - X) (sub_nonneg.mpr hXY)
  rw [map_sub] at hpos
  exact sub_nonneg.mp hpos

lemma comp_outer_product_adjoint
    {ℋ₃ : Type w} [Qudit ℋ₃]
    (A : ℋ₁ →ₗ[ℂ] ℋ₃) (u v : ℋ₁) :
    A.comp ((outer_product u v).comp (LinearMap.adjoint A)) =
      outer_product (A u) (A v) := by
  ext y
  simp [outer_product_eq_rankOne, LinearMap.adjoint_inner_right]

noncomputable def krausTerm
    (V : ℋ₁ →ₗ[ℂ] ℋ₂) : T ℋ₁ ℋ₂ where
  toFun := fun A => V ∘ₗ A ∘ₗ V†
  map_add' := by
    intro A B
    ext x
    simp [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' := by
    intro c A
    ext x
    simp [LinearMap.smul_comp, LinearMap.comp_smul]

lemma isPositiveMap_krausTerm
    (V : ℋ₁ →ₗ[ℂ] ℋ₂) :
    IsPositiveMap (krausTerm V) := by
  intro A hA
  exact (LinearMap.nonneg_iff_isPositive _).2 <| by
    simpa [krausTerm, LinearMap.star_eq_adjoint] using
      ((LinearMap.nonneg_iff_isPositive A).1 hA).conj_adjoint V

noncomputable def dsEquiv (k : ℕ) (ℋ : Type*) [Qudit ℋ] :
    DS k ℋ ≃L[ℂ] (Fin k → ℋ) :=
  PiLp.continuousLinearEquiv (p := (2 : ENNReal)) (𝕜 := ℂ) (β := fun _ : Fin k => ℋ)

noncomputable def dsProj (k : ℕ) (ℋ : Type*) [Qudit ℋ] (i : Fin k) :
    DS k ℋ →L[ℂ] ℋ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℋ) i) ∘L
    (dsEquiv k ℋ).toContinuousLinearMap

noncomputable def dsIncl (k : ℕ) (ℋ : Type*) [Qudit ℋ] (i : Fin k) :
    ℋ →L[ℂ] DS k ℋ :=
  (dsEquiv k ℋ).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.single ℂ (fun _ : Fin k => ℋ) i)

lemma dsProj_dsIncl_apply
    (k : ℕ) (ℋ : Type*) [Qudit ℋ] (i j : Fin k) (x : ℋ) :
    dsProj k ℋ i (dsIncl k ℋ j x) = if i = j then x else 0 := by
  by_cases h : i = j
  · subst h
    simp [dsProj, dsIncl, dsEquiv]
  · simp [dsProj, dsIncl, dsEquiv, h]

lemma dsIncl_adjoint
    (k : ℕ) (ℋ : Type*) [Qudit ℋ] (i : Fin k) :
    (dsIncl k ℋ i).adjoint = dsProj k ℋ i := by
  apply ContinuousLinearMap.ext
  intro x
  refine ext_inner_right ℂ fun y => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  simpa [dsProj, dsIncl, dsEquiv] using
    (inner_symm_single (k := k) (ℋ := ℋ) (v := x) (i := i) (x := y))

lemma dsProj_adjoint
    (k : ℕ) (ℋ : Type*) [Qudit ℋ] (i : Fin k) :
    (dsProj k ℋ i).adjoint = dsIncl k ℋ i := by
  calc
    (dsProj k ℋ i).adjoint = ((dsIncl k ℋ i).adjoint).adjoint := by rw [dsIncl_adjoint]
    _ = dsIncl k ℋ i := ContinuousLinearMap.adjoint_adjoint _

noncomputable def ampKrausFactorCLM
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) : DS k ℋ₁ →L[ℂ] DS k ℋ₂ :=
  ∑ i : Fin k, ((dsIncl k ℋ₂ i).comp V.toContinuousLinearMap).comp (dsProj k ℋ₁ i)

noncomputable def ampKrausFactor
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) : DS k ℋ₁ →ₗ[ℂ] DS k ℋ₂ :=
  (ampKrausFactorCLM k V : DS k ℋ₁ →ₗ[ℂ] DS k ℋ₂)

lemma dsProj_ampKrausFactorCLM
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) (i : Fin k) (x : DS k ℋ₁) :
    dsProj k ℋ₂ i (ampKrausFactorCLM k V x) = V (dsProj k ℋ₁ i x) := by
  classical
  simp [ampKrausFactorCLM, Finset.sum_apply, dsProj_dsIncl_apply]

lemma ampKrausFactorCLM_dsIncl
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) (i : Fin k) (x : ℋ₁) :
    ampKrausFactorCLM k V (dsIncl k ℋ₁ i x) = dsIncl k ℋ₂ i (V x) := by
  apply (dsEquiv k ℋ₂).injective
  ext j
  have h :=
    dsProj_ampKrausFactorCLM (k := k) (V := V) (i := j) (x := dsIncl k ℋ₁ i x)
  by_cases hji : j = i
  · subst hji
    simpa [dsProj, dsIncl, dsEquiv] using h
  · simpa [dsProj, dsIncl, dsEquiv, hji] using h

lemma ampKrausFactorCLM_adjoint_dsIncl
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) (i : Fin k) (x : ℋ₂) :
    (ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x) = dsIncl k ℋ₁ i (V.adjoint x) := by
  classical
  apply (dsEquiv k ℋ₁).injective
  ext j
  apply ext_inner_right ℂ
  intro y
  rw [show
      inner ℂ
          ((dsEquiv k ℋ₁) ((ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x)) j) y =
        inner ℂ
          (dsProj k ℋ₁ j ((ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x))) y by
      rfl]
  rw [show
      inner ℂ ((dsEquiv k ℋ₁) (dsIncl k ℋ₁ i (V.adjoint x)) j) y =
        inner ℂ (dsProj k ℋ₁ j (dsIncl k ℋ₁ i (V.adjoint x))) y by
      rfl]
  by_cases hji : j = i
  · subst j
    calc
      inner ℂ
          (dsProj k ℋ₁ i ((ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x))) y =
        inner ℂ ((ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x))
          (dsIncl k ℋ₁ i y) := by
          simpa [dsIncl_adjoint] using
            (ContinuousLinearMap.adjoint_inner_left
              (A := dsIncl k ℋ₁ i)
              (x := y)
              (y := (ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x)))
      _ = inner ℂ (dsIncl k ℋ₂ i x)
          (ampKrausFactorCLM k V (dsIncl k ℋ₁ i y)) := by
          exact ContinuousLinearMap.adjoint_inner_left
            (A := ampKrausFactorCLM k V)
            (x := dsIncl k ℋ₁ i y)
            (y := dsIncl k ℋ₂ i x)
      _ = inner ℂ (dsIncl k ℋ₂ i x) (dsIncl k ℋ₂ i (V y)) := by
          rw [ampKrausFactorCLM_dsIncl]
      _ = inner ℂ (V.adjoint x) y := by
          rw [← ContinuousLinearMap.adjoint_inner_right
            (A := dsIncl k ℋ₂ i)
            (x := x)
            (y := dsIncl k ℋ₂ i (V y))]
          simp [dsIncl_adjoint, dsProj_dsIncl_apply,
            LinearMap.adjoint_inner_left]
      _ = inner ℂ (dsProj k ℋ₁ i (dsIncl k ℋ₁ i (V.adjoint x))) y := by
          simp [dsProj_dsIncl_apply]
  · calc
      inner ℂ
          (dsProj k ℋ₁ j ((ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x))) y =
        inner ℂ ((ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x))
          (dsIncl k ℋ₁ j y) := by
          simpa [dsIncl_adjoint] using
            (ContinuousLinearMap.adjoint_inner_left
              (A := dsIncl k ℋ₁ j)
              (x := y)
              (y := (ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x)))
      _ = inner ℂ (dsIncl k ℋ₂ i x)
          (ampKrausFactorCLM k V (dsIncl k ℋ₁ j y)) := by
          exact ContinuousLinearMap.adjoint_inner_left
            (A := ampKrausFactorCLM k V)
            (x := dsIncl k ℋ₁ j y)
            (y := dsIncl k ℋ₂ i x)
      _ = inner ℂ (dsIncl k ℋ₂ i x) (dsIncl k ℋ₂ j (V y)) := by
          rw [ampKrausFactorCLM_dsIncl]
      _ = 0 := by
          rw [← ContinuousLinearMap.adjoint_inner_right
            (A := dsIncl k ℋ₂ i)
            (x := x)
            (y := dsIncl k ℋ₂ j (V y))]
          have hij : i ≠ j := fun hij => hji hij.symm
          simp [dsIncl_adjoint, dsProj_dsIncl_apply, hij]
      _ = inner ℂ (dsProj k ℋ₁ j (dsIncl k ℋ₁ i (V.adjoint x))) y := by
          simp [dsProj_dsIncl_apply, hji]

lemma ampKrausFactor_adjoint_dsIncl
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) (i : Fin k) (x : ℋ₂) :
    ((ampKrausFactor k V)†) (dsIncl k ℋ₂ i x) = dsIncl k ℋ₁ i (V.adjoint x) := by
  change (ampKrausFactorCLM k V).adjoint (dsIncl k ℋ₂ i x) = dsIncl k ℋ₁ i (V.adjoint x)
  exact ampKrausFactorCLM_adjoint_dsIncl (k := k) (V := V) (i := i) (x := x)

lemma dsProj_ampKrausFactor
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) (i : Fin k) (x : DS k ℋ₁) :
    dsProj k ℋ₂ i (ampKrausFactor k V x) = V (dsProj k ℋ₁ i x) := by
  exact dsProj_ampKrausFactorCLM (k := k) (V := V) (i := i) (x := x)

lemma ampKrausFactor_dsIncl
    (k : ℕ) (V : ℋ₁ →ₗ[ℂ] ℋ₂) (i : Fin k) (x : ℋ₁) :
    ampKrausFactor k V (dsIncl k ℋ₁ i x) = dsIncl k ℋ₂ i (V x) := by
  exact ampKrausFactorCLM_dsIncl (k := k) (V := V) (i := i) (x := x)

lemma ampPlainEquiv_apply_apply_ds
    (k : ℕ) (ℋ : Type*) [Qudit ℋ]
    (f : L (DS k ℋ)) (i j : Fin k) (x : ℋ) :
    ampPlainEquiv k ℋ f i j x = dsProj k ℋ i (f (dsIncl k ℋ j x)) := by
  simpa [dsProj, dsIncl, dsEquiv] using
    (ampPlainEquiv_apply_apply (k := k) (ℋ := ℋ) (f := f) (i := i) (j := j) (x := x))

lemma ampPlainEquiv_symm_apply_apply
    (k : ℕ) (ℋ : Type*) [Qudit ℋ]
    (N : CStarMatrix (Fin k) (Fin k) (L ℋ))
    (i j : Fin k) (x : ℋ) :
    ampPlainEquiv k ℋ ((ampCStarEquiv k ℋ).symm N) i j x = N i j x := by
  simp [ampCStarEquiv, ampMatrixStarAlgEquiv, ampPlainEquiv]
  rfl

end RepresentationsOfChannels

end QuantumChannel
