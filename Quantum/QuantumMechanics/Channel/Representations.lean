/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.Channel.TensorModel

/-!
Choi and Kraus representation predicates, rank packages, and Stinespring setup.
-/

namespace QuantumChannel

open QuantumState
open TensorProduct

universe u v w

section RepresentationsOfChannels

variable {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-! ### Choi and Kraus representation predicates -/
/--
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press,
2018), Theorem 2.22. Generalization to an arbitrary algebraic basis, agreeing with the condition of
the source at the standard basis. The zero map and zero dimensions are also allowed.
-/
def ChoiPositive (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) : Prop :=
  0 ≤ choi b Φ

/--
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press,
2018), Theorem 2.22. The Kraus condition is packaged with a fixed finite index type. The zero map,
the empty index type and zero dimensions are also allowed.
-/
def KrausRep (Φ : T ℋ₁ ℋ₂) (κ : Type*) [DecidableEq κ] [Fintype κ] : Prop :=
  ∃ A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂),
    ∀ X : L ℋ₁, Φ X = ∑ a : κ, (A a).comp (X.comp (LinearMap.adjoint (A a)))

theorem cp_of_krausRep
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (Φ : (L ℋ₁) →ₗ[ℂ] (L ℋ₂)) :
    KrausRep Φ κ → IsCompletelyPositive Φ := by
  rintro ⟨A, hA⟩
  have hΦ : Φ = ∑ a : κ, krausTerm (A a) := by
    apply LinearMap.ext
    intro X
    simpa [krausTerm] using hA X
  rw [hΦ]
  exact isCompletelyPositive_sum_krausTerm A

noncomputable def choiRank (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) : ℕ :=
  Module.finrank ℂ (LinearMap.range (choi b Φ))

/--
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press,
2018), Theorem 2.22. The Kraus condition is packaged by an existential quantification over finite
index types. The zero map, the empty index type and zero dimensions are also allowed.
-/
def HasKraus (Φ : T ℋ₁ ℋ₂) : Prop :=
  ∃ (κ : Type u) (_ : DecidableEq κ) (_ : Fintype κ),
    @KrausRep ℋ₁ ℋ₂ _ _ Φ κ _ _

def HasRankKraus (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) : Prop :=
  ∃ (κ : Type u) (dec : DecidableEq κ) (inst : Fintype κ),
    Fintype.card κ = choiRank b Φ ∧
      @KrausRep ℋ₁ ℋ₂ _ _ Φ κ dec inst

lemma positive_full_spectral_outer_product
    {E : Type*} [Qudit E] (T : L E) (hT : 0 ≤ T) :
    let n := Module.finrank ℂ E
    let hTpos : T.IsPositive := (LinearMap.nonneg_iff_isPositive T).mp hT
    let hSym : T.IsSymmetric := hTpos.isSymmetric
    ∃ u : Fin n → E,
      T = ∑ i : Fin n, outer_product (u i) (u i) ∧
        ∀ i : Fin n, hSym.eigenvalues rfl i = 0 → u i = 0 := by
  classical
  dsimp
  let n := Module.finrank ℂ E
  let hTpos : T.IsPositive := (LinearMap.nonneg_iff_isPositive T).mp hT
  let hSym : T.IsSymmetric := hTpos.isSymmetric
  let u : Fin n → E :=
    fun i => ((hSym.eigenvalues rfl i).sqrt : ℂ) • hSym.eigenvectorBasis rfl i
  refine ⟨u, ?_, ?_⟩
  · ext x
    rw [show (∑ i : Fin n, outer_product (u i) (u i)) x =
        ∑ i : Fin n, inner ℂ (u i) x • u i by
      simp [outer_product_eq_rankOne]]
    have happly (i : Fin n) : (hSym.eigenvalues rfl i : ℂ) •
        hSym.eigenvectorBasis rfl i = T (hSym.eigenvectorBasis rfl i) :=
      (hSym.apply_eigenvectorBasis rfl i).symm
    simp_rw [u, inner_smul_left, smul_smul, mul_assoc, Complex.conj_ofReal,
      mul_comm (inner ℂ _ _), ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.sqrt_mul (hTpos.nonneg_eigenvalues rfl _),
      Real.sqrt_mul_self (hTpos.nonneg_eigenvalues rfl _), mul_comm _ (inner ℂ _ _),
      ← smul_eq_mul, smul_assoc, happly, ← map_smul, ← map_sum,
      ← OrthonormalBasis.repr_apply_apply, OrthonormalBasis.sum_repr]
  · intro i hi
    simp [u, hi]

lemma positive_spectral_outer_product
    {E : Type*} [Qudit E] (T : L E) (hT : 0 ≤ T) :
    let n := Module.finrank ℂ E
    let hTpos : T.IsPositive := (LinearMap.nonneg_iff_isPositive T).mp hT
    let hSym : T.IsSymmetric := hTpos.isSymmetric
    ∃ u : { i : Fin n // hSym.eigenvalues rfl i ≠ 0 } → E,
      T = ∑ a, outer_product (u a) (u a) := by
  dsimp
  let n := Module.finrank ℂ E
  let hTpos : T.IsPositive := (LinearMap.nonneg_iff_isPositive T).mp hT
  let hSym : T.IsSymmetric := hTpos.isSymmetric
  let p : Fin n → Prop := fun i => hSym.eigenvalues rfl i ≠ 0
  obtain ⟨u, hsum, hzero⟩ :=
    positive_full_spectral_outer_product (T := T) (hT := hT)
  refine ⟨fun a => u a, ?_⟩
  have hzero_sum :
      (∑ a : { i : Fin n // ¬ p i }, outer_product (u a) (u a)) = 0 := by
    apply Fintype.sum_eq_zero
    intro a
    have ha : hSym.eigenvalues rfl a = 0 := not_not.mp a.property
    simp [hzero a ha, outer_product]
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype p
      (fun i : Fin n => outer_product (u i) (u i))
  calc
    T = ∑ i : Fin n, outer_product (u i) (u i) := hsum
    _ = ∑ a : { i : Fin n // p i }, outer_product (u a) (u a) := by
      rw [← hsplit, hzero_sum, add_zero]

lemma positive_to_rank_outer_product
    {E : Type*} [Qudit E] (T : L E) (hT : 0 ≤ T) :
    ∃ (κ : Type u) (_ : DecidableEq κ) (_ : Fintype κ),
      Fintype.card κ = Module.finrank ℂ (LinearMap.range T) ∧
        ∃ u : κ → E, T = ∑ a : κ, outer_product (u a) (u a) := by
  let n := Module.finrank ℂ E
  let hTpos : T.IsPositive := (LinearMap.nonneg_iff_isPositive T).mp hT
  let hSym : T.IsSymmetric := hTpos.isSymmetric
  let κ₀ := { i : Fin n // hSym.eigenvalues rfl i ≠ 0 }
  let κ := ULift κ₀
  have hcard₀ : Fintype.card κ₀ = Module.finrank ℂ (LinearMap.range T) := by
    exact card_nonzero_eigenvalues_eq_finrank_range T hT
  have hcard : Fintype.card κ = Module.finrank ℂ (LinearMap.range T) := by
    simpa [κ, Fintype.card_ulift] using hcard₀
  obtain ⟨u₀, hu₀⟩ :=
    positive_spectral_outer_product (T := T) (hT := hT)
  refine ⟨κ, inferInstance, inferInstance, hcard, ?_⟩
  refine ⟨fun a : κ => u₀ a.down, ?_⟩
  have hsum :
      (∑ a : κ, outer_product (u₀ a.down) (u₀ a.down)) =
        ∑ a : κ₀, outer_product (u₀ a) (u₀ a) := by
    symm
    refine Fintype.sum_equiv (Equiv.ulift.symm : κ₀ ≃ κ) _ _ ?_
    intro a
    rfl
  exact hu₀.trans hsum.symm

theorem hasKraus_of_hasRankKraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankKraus b Φ → HasKraus Φ := by
  rintro ⟨κ, dec, inst, _, hkraus⟩
  exact ⟨κ, dec, inst, hkraus⟩

theorem isPositiveMap_of_hasKraus
    (Φ : T ℋ₁ ℋ₂) :
    HasKraus Φ → IsPositiveMap Φ := by
  rintro ⟨κ, hκ, hκ', A, hA⟩ X hX
  letI : DecidableEq κ := hκ
  letI : Fintype κ := hκ'
  rw [hA X]
  exact Finset.sum_nonneg fun a _ =>
    isPositiveMap_conjugate (ℋ₁ := ℋ₁) (ℋ₃ := ℋ₂) (A a) X hX

theorem isPositiveMap_of_hasRankKraus
    (b : Module.Basis ι ℂ ℋ₁) (Φ : T ℋ₁ ℋ₂) :
    HasRankKraus b Φ → IsPositiveMap Φ :=
  isPositiveMap_of_hasKraus Φ ∘
    hasKraus_of_hasRankKraus b Φ

/-! ### Stinespring operator setup and basis decompositions -/
noncomputable def conjugateEnd {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (e : E ≃ₗ[ℂ] F) :
    L E →ₗ[ℂ] L F where
  toFun X := (e : E →ₗ[ℂ] F).comp (X.comp (e.symm : F →ₗ[ℂ] E))
  map_add' X Y := by
    ext x
    simp
  map_smul' c X := by
    ext x
    simp

lemma isPositiveMap_conjugateEnd_comm
    {E : Type u} {F : Type v} [Qudit E] [Qudit F] :
    IsPositiveMap (conjugateEnd (TensorProduct.comm ℂ E F)) := by
  intro X hX
  have hXpos : X.IsPositive := (LinearMap.nonneg_iff_isPositive X).mp hX
  have hcomm :
      LinearMap.adjoint
          (TensorProduct.comm ℂ E F : (E ⊗[ℂ] F) →ₗ[ℂ] (F ⊗[ℂ] E)) =
        ((TensorProduct.comm ℂ E F).symm : (F ⊗[ℂ] E) →ₗ[ℂ] (E ⊗[ℂ] F)) := by
    simpa [TensorProduct.toLinearEquiv_commIsometry] using
      (LinearIsometryEquiv.adjoint_toLinearMap_eq_symm
        (TensorProduct.commIsometry ℂ E F))
  exact (LinearMap.nonneg_iff_isPositive _).mpr <| by
    simpa [conjugateEnd, hcomm] using
      hXpos.conj_adjoint
        (TensorProduct.comm ℂ E F : (E ⊗[ℂ] F) →ₗ[ℂ] (F ⊗[ℂ] E))

/-- Swapping tensor factors by `TensorProduct.comm` is monotone on endomorphisms. -/
@[gcongr]
lemma conjugateEnd_comm_le_conjugateEnd_comm
    {E : Type u} {F : Type v} [Qudit E] [Qudit F]
    {X Y : L (E ⊗[ℂ] F)} (hXY : X ≤ Y) :
    conjugateEnd (TensorProduct.comm ℂ E F) X ≤
      conjugateEnd (TensorProduct.comm ℂ E F) Y := by
  have hpos : 0 ≤ conjugateEnd (TensorProduct.comm ℂ E F) (Y - X) :=
    isPositiveMap_conjugateEnd_comm (E := E) (F := F) (Y - X) (sub_nonneg.mpr hXY)
  rw [map_sub] at hpos
  exact sub_nonneg.mp hpos

/--
Source: John Watrous, "The Theory of Quantum Information" (Cambridge University Press, 2018), Eq.
(1.121). Corresponds to the definition of the right partial trace.
-/
noncomputable def traceOutRight {ℋ₃ : Type u} [Qudit ℋ₃] : T (ℋ₂ ⊗[ℂ] ℋ₃) ℋ₂ :=
  (traceOutLeft (ℋ₁ := ℋ₃) (ℋ₂ := ℋ₂)).comp
    (conjugateEnd (TensorProduct.comm ℂ ℋ₂ ℋ₃))

noncomputable def krausToStinespringOperator
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) :
    ℋ₁ →ₗ[ℂ] (ℋ₂ ⊗[ℂ] EuclideanSpace ℂ κ) where
  toFun x := ∑ a : κ, (A a x) ⊗ₜ[ℂ] (EuclideanSpace.basisFun κ ℂ a)
  map_add' x y := by
    simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp [TensorProduct.smul_tmul', Finset.smul_sum]

lemma krausToStinespringOperator_apply
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) (x : ℋ₁) :
    krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A x
      = ∑ a : κ, (A a x) ⊗ₜ[ℂ] (EuclideanSpace.basisFun κ ℂ a) :=
  rfl

lemma adjoint_krausToStinespringOperator_tmul_basisFun
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) (y : ℋ₂) (b : κ) :
    (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A))
        (y ⊗ₜ[ℂ] EuclideanSpace.basisFun κ ℂ b) =
      (LinearMap.adjoint (A b)) y := by
  apply ext_inner_right ℂ
  intro x
  rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
  simp [krausToStinespringOperator_apply, inner_sum, TensorProduct.inner_tmul,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

lemma conjugateEnd_krausToStinespringOperator_apply_basisFun_tmul
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) (X : L ℋ₁) (b : κ) (y : ℋ₂) :
    (conjugateEnd (TensorProduct.comm ℂ ℋ₂ (EuclideanSpace ℂ κ))
        (((krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A).comp X).comp
          (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A))))
      ((EuclideanSpace.basisFun κ ℂ b) ⊗ₜ[ℂ] y) =
        ∑ a : κ, (EuclideanSpace.basisFun κ ℂ a) ⊗ₜ[ℂ]
          ((A a).comp (X.comp (LinearMap.adjoint (A b))) y) := by
  have hadj :
      (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A))
          (y ⊗ₜ[ℂ] EuclideanSpace.single b (1 : ℂ)) =
        (LinearMap.adjoint (A b)) y := by
    simpa [EuclideanSpace.basisFun_apply] using
      (adjoint_krausToStinespringOperator_tmul_basisFun
        (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) (κ := κ) A y b)
  simp [conjugateEnd, krausToStinespringOperator_apply, LinearMap.comp_apply,
    EuclideanSpace.basisFun_apply, hadj]

lemma conjugateEnd_krausToStinespringOperator_apply_single_tmul
    {κ : Type u} [DecidableEq κ] [Fintype κ]
    (A : κ → (ℋ₁ →ₗ[ℂ] ℋ₂)) (X : L ℋ₁) (b : κ) (y : ℋ₂) :
    (conjugateEnd (TensorProduct.comm ℂ ℋ₂ (EuclideanSpace ℂ κ))
        (((krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A).comp X).comp
          (LinearMap.adjoint (krausToStinespringOperator (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A))))
      ((EuclideanSpace.single b (1 : ℂ)) ⊗ₜ[ℂ] y) =
        ∑ a : κ, (EuclideanSpace.single a (1 : ℂ)) ⊗ₜ[ℂ]
          ((A a).comp (X.comp (LinearMap.adjoint (A b))) y) := by
  simpa [EuclideanSpace.basisFun_apply] using
    (conjugateEnd_krausToStinespringOperator_apply_basisFun_tmul
      (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) A X b y)

lemma finrank_kraus_environment
    {κ : Type u} [Fintype κ] :
    Module.finrank ℂ (EuclideanSpace ℂ κ) = Fintype.card κ := by
  simp [finrank_euclideanSpace (𝕜 := ℂ) (ι := κ)]

lemma linearMap_eq_sum_outer_product
    {E : Type u} [Qudit E] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (T : L E) :
    T = ∑ i : ι, outer_product (b i) (T (b i)) := by
  ext x
  have hsum : T x = ∑ i : ι, inner ℂ (b i) x • T (b i) := by
    simpa using congrArg T (b.sum_repr' x).symm
  calc
    T x = ∑ i : ι, inner ℂ (b i) x • T (b i) := hsum
    _ = (∑ i : ι, outer_product (b i) (T (b i))) x := by
      simp [LinearMap.sum_apply, outer_product_eq_rankOne]

lemma basis_dual_inner
    {E : Type u} [Qudit E] {ι : Type*} [DecidableEq ι] [Finite ι]
    (b : Module.Basis ι ℂ E) (i j : ι) :
    inner ℂ (b i)
      ((InnerProductSpace.toDual ℂ E).symm ((b.coord j).toContinuousLinearMap)) =
        if i = j then 1 else 0 := by
  rw [← inner_conj_symm]
  have h :
      inner ℂ
        ((InnerProductSpace.toDual ℂ E).symm ((b.coord j).toContinuousLinearMap))
        (b i) = if i = j then 1 else 0 := by
    simpa using (Module.Basis.dualBasis_apply_self b j i)
  rw [h]
  by_cases hij : i = j <;> simp [hij]

lemma basis_sum_dual
    {E : Type u} [Qudit E] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ E) (x : E) :
    x =
      ∑ i : ι, inner ℂ (b i) x •
        ((InnerProductSpace.toDual ℂ E).symm ((b.coord i).toContinuousLinearMap)) := by
  classical
  apply InnerProductSpace.ext_inner_left_basis b
  intro j
  rw [inner_sum]
  simp [inner_smul_right, basis_dual_inner]

lemma linearMap_eq_sum_basis_outer_product
    {E : Type u} [Qudit E] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ E) (T : L E) :
    T =
      ∑ i : ι, ∑ j : ι,
        (b.coord j
          (T ((InnerProductSpace.toDual ℂ E).symm ((b.coord i).toContinuousLinearMap)))) •
          outer_product (b i) (b j) := by
  classical
  ext x
  have hx := basis_sum_dual b x
  calc
    T x =
        T (∑ i : ι, inner ℂ (b i) x •
          ((InnerProductSpace.toDual ℂ E).symm ((b.coord i).toContinuousLinearMap))) := by
          rw [← hx]
    _ = ∑ i : ι, inner ℂ (b i) x •
          T ((InnerProductSpace.toDual ℂ E).symm ((b.coord i).toContinuousLinearMap)) := by
          simp [map_sum]
    _ = ∑ i : ι, inner ℂ (b i) x •
          (∑ j : ι,
            (b.coord j
              (T ((InnerProductSpace.toDual ℂ E).symm ((b.coord i).toContinuousLinearMap)))) •
              b j) := by
          simp [b.sum_repr]
    _ = (∑ i : ι, ∑ j : ι,
        (b.coord j
          (T ((InnerProductSpace.toDual ℂ E).symm ((b.coord i).toContinuousLinearMap)))) •
          outer_product (b i) (b j)) x := by
          simp only [LinearMap.sum_apply]
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          simp [outer_product, dualTensorHom_apply, smul_smul, mul_comm]

lemma basis_outer_coeff
    {E : Type u} [Qudit E] {ι : Type*} [DecidableEq ι] [Finite ι]
    (b : Module.Basis ι ℂ E) (p q i j : ι) :
    b.coord q ((outer_product (b i) (b j))
      ((InnerProductSpace.toDual ℂ E).symm ((b.coord p).toContinuousLinearMap))) =
        if i = p then if j = q then 1 else 0 else 0 := by
  have hinner := basis_dual_inner b i p
  by_cases hip : i = p
  · subst hip
    by_cases hjq : j = q <;> simp [outer_product, dualTensorHom_apply, hinner, hjq]
  · simp [outer_product, dualTensorHom_apply, hinner, hip]

end RepresentationsOfChannels

end QuantumChannel
