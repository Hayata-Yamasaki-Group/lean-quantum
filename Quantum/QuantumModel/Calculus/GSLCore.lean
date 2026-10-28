/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.CategoryInstances.GSLCore
import Quantum.QuantumModel.InstrumentCompletion.GSLCore
import Quantum.OperationalProbabilistic.Framework.Core.GSLCore

/-!
# Kraus calculus for the finite-dimensional quantum model

This file supplies the elementary closure and normalization results needed to
interpret the quantum-system skeleton as an operational probabilistic theory.
-/

noncomputable section

namespace QuantumModel

open CategoryTheory
open CategoryTheory.MonoidalCategory
open QuantumState

variable {A B C D : Sys}

/-! ## Choosing Kraus families -/

theorem exists_krausFamily_of_isEvent {f : A ⟶ B} (hf : IsEvent f) :
    ∃ K : KrausFamily A B, K.map = f := by
  let b := (EuclideanSpace.basisFun (Fin A.dim) ℂ).toBasis
  obtain ⟨ι, hdec, hfin, V, hV⟩ :=
    QuantumChannel.cp_to_kraus b (HPHom.toRawSuperoperator f) hf
  let K : KrausFamily A B :=
    { index := ι
      fintypeIndex := hfin
      decidableEqIndex := hdec
      operator := V }
  refine ⟨K, ?_⟩
  letI : DecidableEq ι := hdec
  letI : Fintype ι := hfin
  apply HPHom.ext
  intro X
  change K.rawMap X = HPHom.toRawSuperoperator f X
  simpa [KrausFamily.rawMap, K, QuantumChannel.krausTerm] using (hV X).symm

/-! ## Completely positive maps -/

theorem isEvent_zero : IsEvent (0 : A ⟶ B) := by
  let K : KrausFamily A B :=
    { index := Empty
      fintypeIndex := inferInstance
      decidableEqIndex := inferInstance
      operator := Empty.elim }
  change QuantumChannel.IsCompletelyPositive (0 : RawSuperoperator A B)
  simpa [KrausFamily.rawMap, K] using K.map_isCompletelyPositive

theorem isEvent_add {f g : A ⟶ B}
    (hf : IsEvent f) (hg : IsEvent g) : IsEvent (f + g) := by
  obtain ⟨K, hK⟩ := exists_krausFamily_of_isEvent hf
  obtain ⟨L, hL⟩ := exists_krausFamily_of_isEvent hg
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  letI := L.fintypeIndex
  letI := L.decidableEqIndex
  let M : KrausFamily A B :=
    { index := Sum K.index L.index
      fintypeIndex := inferInstance
      decidableEqIndex := inferInstance
      operator := Sum.elim K.operator L.operator }
  have hM : M.map = f + g := by
    calc
      M.map = K.map + L.map := by
        apply HPHom.ext
        intro X
        change M.rawMap X = K.rawMap X + L.rawMap X
        simp [KrausFamily.rawMap, M, Fintype.sum_sum_type]
      _ = f + g := congrArg₂ (· + ·) hK hL
  rw [← hM]
  exact M.map_isCompletelyPositive

theorem isEvent_sum {ι : Type*} [Fintype ι]
    (f : ι → (A ⟶ B)) (hf : ∀ i, IsEvent (f i)) :
    IsEvent (∑ i, f i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using (isEvent_zero (A := A) (B := B))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact isEvent_add (hf i) ih

theorem isEvent_nonneg_smul {r : ℝ} {f : A ⟶ B}
    (hr : 0 ≤ r) (hf : IsEvent f) : IsEvent (r • f) := by
  obtain ⟨K, hK⟩ := exists_krausFamily_of_isEvent hf
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  let L : KrausFamily A B :=
    { index := K.index
      fintypeIndex := inferInstance
      decidableEqIndex := inferInstance
      operator := fun i => (Real.sqrt r : ℂ) • K.operator i }
  have hL : L.map = r • f := by
    rw [← hK]
    apply HPHom.ext
    intro X
    change L.rawMap X = (r : ℂ) • K.rawMap X
    simp only [KrausFamily.rawMap, L, LinearMap.sum_apply,
      QuantumChannel.krausTerm]
    have hadj (i : K.index) :
        LinearMap.adjoint ((Real.sqrt r : ℂ) • K.operator i) =
          (Real.sqrt r : ℂ) • LinearMap.adjoint (K.operator i) := by
      simpa using
        (map_smulₛₗ
          (LinearMap.adjoint (𝕜 := ℂ) :
            (Space A →ₗ[ℂ] Space B) ≃ₗ⋆[ℂ] (Space B →ₗ[ℂ] Space A))
          (Real.sqrt r : ℂ) (K.operator i))
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change ((Real.sqrt r : ℂ) • K.operator i).comp
        (X.comp (LinearMap.adjoint ((Real.sqrt r : ℂ) • K.operator i))) =
      (r : ℂ) • (K.operator i).comp
        (X.comp (LinearMap.adjoint (K.operator i)))
    rw [hadj]
    simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
    congr 1
    norm_cast
    exact Real.mul_self_sqrt hr
  rw [← hL]
  exact L.map_isCompletelyPositive

theorem isEvent_id : IsEvent (𝟙 A) := by
  let K : KrausFamily A A :=
    { index := PUnit
      fintypeIndex := inferInstance
      decidableEqIndex := inferInstance
      operator := fun _ => LinearMap.id }
  have hK : K.map = 𝟙 A := by
    apply HPHom.ext
    intro X
    change K.rawMap X = X
    simp [KrausFamily.rawMap, K, QuantumChannel.krausTerm]
  rw [← hK]
  exact K.map_isCompletelyPositive

/-! ## Comparing Kraus families -/

theorem krausFamily_normalization_nonneg (K : KrausFamily A B) :
    0 ≤ K.normalization := by
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  rw [KrausFamily.normalization]
  apply Finset.sum_nonneg
  intro i _
  exact (LinearMap.nonneg_iff_isPositive _).mpr <| by
    simpa only [LinearMap.id_comp] using
      (LinearMap.isPositive_one.adjoint_conj (K.operator i))

theorem trace_krausFamily_map (K : KrausFamily A B) (X : Operator A) :
    QuantumState.Tr (HPHom.toRawSuperoperator K.map X) =
      QuantumState.Tr (K.normalization.comp X) := by
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  rw [KrausFamily.map_toRawSuperoperator, KrausFamily.rawMap,
    KrausFamily.normalization]
  simp only [LinearMap.sum_apply, map_sum, QuantumChannel.krausTerm]
  have hcomp :
      (∑ i, (LinearMap.adjoint (K.operator i)).comp (K.operator i)).comp X =
        ∑ i, ((LinearMap.adjoint (K.operator i)).comp (K.operator i)).comp X := by
    ext v
    simp
  rw [hcomp, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    QuantumState.Tr
        ((K.operator i).comp (X.comp (LinearMap.adjoint (K.operator i)))) =
        QuantumState.Tr
          ((X.comp (LinearMap.adjoint (K.operator i))).comp (K.operator i)) :=
      (LinearMap.trace_comp_comm' (K.operator i)
        (X.comp (LinearMap.adjoint (K.operator i)))).symm
    _ = QuantumState.Tr
          (((LinearMap.adjoint (K.operator i)).comp (K.operator i)).comp X) := by
      rw [LinearMap.comp_assoc]
      exact (LinearMap.trace_comp_comm'
        X ((LinearMap.adjoint (K.operator i)).comp (K.operator i))).symm

theorem operator_eq_of_trace_comp_eq {X Y : Operator A}
    (h : ∀ Z : Operator A,
      QuantumState.Tr (X.comp Z) = QuantumState.Tr (Y.comp Z)) : X = Y := by
  apply LinearMap.ext
  intro v
  apply ext_inner_right ℂ
  intro u
  let w := X v - Y v
  have huv := h (QuantumChannel.outer_product w v)
  have hcompX :
      X.comp (QuantumChannel.outer_product w v) =
        QuantumChannel.outer_product w (X v) := by
    ext z
    simp [QuantumChannel.outer_product_eq_rankOne]
  have hcompY :
      Y.comp (QuantumChannel.outer_product w v) =
        QuantumChannel.outer_product w (Y v) := by
    ext z
    simp [QuantumChannel.outer_product_eq_rankOne]
  rw [hcompX, hcompY, QuantumChannel.trace_outer_product,
    QuantumChannel.trace_outer_product] at huv
  have hw : inner ℂ w w = 0 := by
    rw [show w = X v - Y v by rfl, inner_sub_right, huv, sub_self]
  have hwzero : w = 0 := inner_self_eq_zero.mp hw
  have hv : X v = Y v := sub_eq_zero.mp hwzero
  simp [hv]

theorem krausFamily_normalization_eq_of_map_eq
    (K L : KrausFamily A B) (hmap : K.map = L.map) :
    K.normalization = L.normalization := by
  apply operator_eq_of_trace_comp_eq
  intro X
  rw [← trace_krausFamily_map K, ← trace_krausFamily_map L, hmap]

/-! ## Basic normalized maps -/

theorem isTransformation_zero : IsTransformation (0 : A ⟶ B) := by
  refine ⟨isEvent_zero, ?_⟩
  let K : KrausFamily A B :=
    { index := Empty
      fintypeIndex := inferInstance
      decidableEqIndex := inferInstance
      operator := Empty.elim }
  refine ⟨K, ?_, ?_⟩
  · apply HPHom.ext
    intro X
    simp [KrausFamily.rawMap, K]
  · rw [KrausFamily.normalization]
    simp only [K, Finset.univ_eq_empty, Finset.sum_empty]
    exact (LinearMap.nonneg_iff_isPositive _).mpr LinearMap.isPositive_one

theorem isChannel_id : IsChannel (𝟙 A) := by
  refine ⟨isEvent_id, ?_⟩
  let K : KrausFamily A A :=
    { index := PUnit
      fintypeIndex := inferInstance
      decidableEqIndex := inferInstance
      operator := fun _ => LinearMap.id }
  refine ⟨K, ?_, ?_⟩
  · apply HPHom.ext
    intro X
    change K.rawMap X = X
    simp [KrausFamily.rawMap, K, QuantumChannel.krausTerm]
  · simp [KrausFamily.normalization, K]

theorem isChannel_isTransformation {f : A ⟶ B}
    (hf : IsChannel f) : IsTransformation f := by
  refine ⟨hf.1, ?_⟩
  obtain ⟨K, hK, hnorm⟩ := hf.2
  exact ⟨K, hK, le_of_eq hnorm⟩

/-! ## Sequential composition -/

namespace KrausFamily

/-- Product Kraus family for sequential composition. -/
def comp (L : KrausFamily B C) (K : KrausFamily A B) : KrausFamily A C :=
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  letI := L.fintypeIndex
  letI := L.decidableEqIndex
  { index := K.index × L.index
    fintypeIndex := inferInstance
    decidableEqIndex := inferInstance
    operator := fun p => (L.operator p.2).comp (K.operator p.1) }

theorem comp_map (L : KrausFamily B C) (K : KrausFamily A B) :
    (L.comp K).map = K.map ≫ L.map := by
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  letI := L.fintypeIndex
  letI := L.decidableEqIndex
  have hterm (i : K.index) (j : L.index) :
      QuantumChannel.krausTerm ((L.operator j).comp (K.operator i)) =
        (QuantumChannel.krausTerm (L.operator j)).comp
          (QuantumChannel.krausTerm (K.operator i)) := by
    apply LinearMap.ext
    intro X
    apply LinearMap.ext
    intro v
    simp [QuantumChannel.krausTerm, LinearMap.adjoint_comp,
      LinearMap.comp_apply, LinearMap.comp_assoc]
  apply HPHom.ext
  intro X
  change (L.comp K).rawMap X = L.rawMap (K.rawMap X)
  simp only [rawMap, comp, hterm,
    LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  exact Fintype.sum_prod_type _

/-- The input effect obtained after sequentially applying `K` and `L`. -/
def compNormalization (L : KrausFamily B C) (K : KrausFamily A B) : Operator A := by
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  exact ∑ i, (LinearMap.adjoint (K.operator i)).comp
    (L.normalization.comp (K.operator i))

theorem comp_normalization (L : KrausFamily B C) (K : KrausFamily A B) :
    (L.comp K).normalization = L.compNormalization K := by
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  letI := L.fintypeIndex
  letI := L.decidableEqIndex
  apply LinearMap.ext
  intro v
  simp only [normalization, comp, compNormalization,
    LinearMap.adjoint_comp, LinearMap.comp_apply,
    LinearMap.sum_apply, map_sum]
  exact Fintype.sum_prod_type _

/-- Scale every Kraus operator by the square root of a real coefficient. -/
def scale (r : ℝ) (K : KrausFamily A B) : KrausFamily A B :=
  { index := K.index
    fintypeIndex := K.fintypeIndex
    decidableEqIndex := K.decidableEqIndex
    operator := fun i => (Real.sqrt r : ℂ) • K.operator i }

theorem scale_map (K : KrausFamily A B) {r : ℝ} (hr : 0 ≤ r) :
    (K.scale r).map = r • K.map := by
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  apply HPHom.ext
  intro X
  change (K.scale r).rawMap X = (r : ℂ) • K.rawMap X
  simp only [rawMap, scale, LinearMap.sum_apply, QuantumChannel.krausTerm]
  have hadj (i : K.index) :
      LinearMap.adjoint ((Real.sqrt r : ℂ) • K.operator i) =
        (Real.sqrt r : ℂ) • LinearMap.adjoint (K.operator i) := by
    simpa using
      (map_smulₛₗ
        (LinearMap.adjoint (𝕜 := ℂ) :
          (Space A →ₗ[ℂ] Space B) ≃ₗ⋆[ℂ] (Space B →ₗ[ℂ] Space A))
        (Real.sqrt r : ℂ) (K.operator i))
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change ((Real.sqrt r : ℂ) • K.operator i).comp
      (X.comp (LinearMap.adjoint ((Real.sqrt r : ℂ) • K.operator i))) =
    (r : ℂ) • (K.operator i).comp
      (X.comp (LinearMap.adjoint (K.operator i)))
  rw [hadj]
  simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  congr 1
  norm_cast
  exact Real.mul_self_sqrt hr

theorem scale_normalization (K : KrausFamily A B) {r : ℝ} (hr : 0 ≤ r) :
    (K.scale r).normalization = r • K.normalization := by
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  change (K.scale r).normalization = (r : ℂ) • K.normalization
  simp only [normalization, scale]
  have hadj (i : K.index) :
      LinearMap.adjoint ((Real.sqrt r : ℂ) • K.operator i) =
        (Real.sqrt r : ℂ) • LinearMap.adjoint (K.operator i) := by
    simpa using
      (map_smulₛₗ
        (LinearMap.adjoint (𝕜 := ℂ) :
          (Space A →ₗ[ℂ] Space B) ≃ₗ⋆[ℂ] (Space B →ₗ[ℂ] Space A))
        (Real.sqrt r : ℂ) (K.operator i))
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hadj]
  simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  congr 1
  norm_cast
  exact Real.mul_self_sqrt hr

end KrausFamily

theorem adjoint_sandwich_mono (V : Space A →ₗ[ℂ] Space B)
    {X Y : Operator B} (hXY : X ≤ Y) :
    (LinearMap.adjoint V).comp (X.comp V) ≤
      (LinearMap.adjoint V).comp (Y.comp V) := by
  rw [← sub_nonneg]
  have hpos : (Y - X).IsPositive :=
    (LinearMap.nonneg_iff_isPositive _).mp (sub_nonneg.mpr hXY)
  apply (LinearMap.nonneg_iff_isPositive _).mpr
  convert hpos.adjoint_conj V using 1
  simp [LinearMap.comp_sub, LinearMap.sub_comp]

theorem isTransformation_comp {f : A ⟶ B} {g : B ⟶ C}
    (hf : IsTransformation f) (hg : IsTransformation g) :
    IsTransformation (f ≫ g) := by
  rcases hf with ⟨hfCP, K, hK, hKle⟩
  rcases hg with ⟨hgCP, L, hL, hLle⟩
  let M := L.comp K
  have hMmap : M.map = f ≫ g := by
    rw [KrausFamily.comp_map, hK, hL]
  refine ⟨QuantumChannel.comp_isCompletelyPositive
    (HPHom.toRawSuperoperator f) (HPHom.toRawSuperoperator g) hfCP hgCP,
    M, hMmap, ?_⟩
  rw [KrausFamily.comp_normalization]
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  change (∑ i, (LinearMap.adjoint (K.operator i)).comp
      (L.normalization.comp (K.operator i))) ≤ LinearMap.id
  calc
    (∑ i, (LinearMap.adjoint (K.operator i)).comp
        (L.normalization.comp (K.operator i))) ≤
        ∑ i, (LinearMap.adjoint (K.operator i)).comp
          (LinearMap.id.comp (K.operator i)) := by
      apply Finset.sum_le_sum
      intro i _
      exact adjoint_sandwich_mono (K.operator i) hLle
    _ = K.normalization := by
      letI := K.fintypeIndex
      letI := K.decidableEqIndex
      simp [KrausFamily.normalization]
    _ ≤ LinearMap.id := hKle

theorem isChannel_comp {f : A ⟶ B} {g : B ⟶ C}
    (hf : IsChannel f) (hg : IsChannel g) : IsChannel (f ≫ g) := by
  rcases hf with ⟨hfCP, K, hK, hKnorm⟩
  rcases hg with ⟨hgCP, L, hL, hLnorm⟩
  let M := L.comp K
  have hMmap : M.map = f ≫ g := by
    rw [KrausFamily.comp_map, hK, hL]
  refine ⟨QuantumChannel.comp_isCompletelyPositive
    (HPHom.toRawSuperoperator f) (HPHom.toRawSuperoperator g) hfCP hgCP,
    M, hMmap, ?_⟩
  rw [KrausFamily.comp_normalization]
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  unfold KrausFamily.compNormalization
  rw [hLnorm]
  change (∑ i, (LinearMap.adjoint (K.operator i)).comp
      (LinearMap.id.comp (K.operator i))) = LinearMap.id
  simpa [KrausFamily.normalization] using hKnorm

/-- A convex combination of two elements below `z` is below `z` (stated abstractly so that the
order and scalar instances on operators are synthesized once, at the use site). -/
private theorem convex_combination_le {E : Type*} [AddCommGroup E] [PartialOrder E]
    [IsOrderedAddMonoid E] [Module ℝ E] [PosSMulMono ℝ E] {x y z : E} {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) (hx : x ≤ z) (hy : y ≤ z) :
    p • x + q • y ≤ z :=
  calc
    p • x + q • y ≤ p • z + q • z :=
      add_le_add (smul_le_smul_of_nonneg_left hx hp) (smul_le_smul_of_nonneg_left hy hq)
    _ = z := by rw [← add_smul, hpq, one_smul]

theorem isTransformation_convex {f g : A ⟶ B} {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1)
    (hf : IsTransformation f) (hg : IsTransformation g) :
    IsTransformation (p • f + q • g) := by
  rcases hf with ⟨hfCP, K, hK, hKle⟩
  rcases hg with ⟨hgCP, L, hL, hLle⟩
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  letI := L.fintypeIndex
  letI := L.decidableEqIndex
  let M : KrausFamily A B :=
    { index := Sum K.index L.index
      fintypeIndex := inferInstance
      decidableEqIndex := inferInstance
      operator := Sum.elim (K.scale p).operator (L.scale q).operator }
  have hMmap : M.map = p • f + q • g := by
    calc
      M.map = (K.scale p).map + (L.scale q).map := by
        apply HPHom.ext
        intro X
        change M.rawMap X = (K.scale p).rawMap X + (L.scale q).rawMap X
        simp [KrausFamily.rawMap, M, Fintype.sum_sum_type]
        rfl
      _ = p • K.map + q • L.map := by
        rw [KrausFamily.scale_map K hp, KrausFamily.scale_map L hq]
      _ = p • f + q • g := congrArg₂ (· + ·)
        (congrArg (p • ·) hK) (congrArg (q • ·) hL)
  have hMnorm :
      M.normalization = p • K.normalization + q • L.normalization := by
    calc
      M.normalization =
          (K.scale p).normalization + (L.scale q).normalization := by
        simp only [KrausFamily.normalization, M, Fintype.sum_sum_type]
        congr
      _ = p • K.normalization + q • L.normalization := by
        rw [KrausFamily.scale_normalization K hp,
          KrausFamily.scale_normalization L hq]
  have hMle : M.normalization ≤ LinearMap.id := by
    rw [hMnorm]
    exact convex_combination_le hp hq hpq hKle hLle
  exact ⟨isEvent_add (isEvent_nonneg_smul hp hfCP)
    (isEvent_nonneg_smul hq hgCP), M, hMmap, hMle⟩

/-! ## Partial sums of tests -/

theorem partialSum_isTransformation
    {ι : Type*} [Fintype ι] {T : ι → (A ⟶ B)}
    (hcp : ∀ i, IsEvent (T i))
    (htotal : IsChannel (Finset.univ.sum T))
    (s : Finset ι) :
    IsTransformation (s.sum T) := by
  classical
  have hsEvent : IsEvent (s.sum T) := by
    induction s using Finset.induction_on with
    | empty => simpa using (isEvent_zero (A := A) (B := B))
    | @insert i t hi iht =>
        rw [Finset.sum_insert hi]
        exact isEvent_add (hcp i) iht
  let t : Finset ι := Finset.univ \ s
  have htEvent : IsEvent (t.sum T) := by
    induction t using Finset.induction_on with
    | empty => simpa using (isEvent_zero (A := A) (B := B))
    | @insert i u hi ihu =>
        rw [Finset.sum_insert hi]
        exact isEvent_add (hcp i) ihu
  obtain ⟨K, hK⟩ := exists_krausFamily_of_isEvent hsEvent
  obtain ⟨L, hL⟩ := exists_krausFamily_of_isEvent htEvent
  obtain ⟨J, hJ, hJnorm⟩ := htotal.2
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  letI := L.fintypeIndex
  letI := L.decidableEqIndex
  let M : KrausFamily A B :=
    { index := Sum K.index L.index
      fintypeIndex := inferInstance
      decidableEqIndex := inferInstance
      operator := Sum.elim K.operator L.operator }
  have hMmap : M.map = Finset.univ.sum T := by
    calc
      M.map = K.map + L.map := by
        apply HPHom.ext
        intro X
        change M.rawMap X = K.rawMap X + L.rawMap X
        simp [KrausFamily.rawMap, M, Fintype.sum_sum_type]
      _ = s.sum T + t.sum T := congrArg₂ (· + ·) hK hL
      _ = Finset.univ.sum T := by
        simp [t]
  have hMnorm : M.normalization = K.normalization + L.normalization := by
    simp [KrausFamily.normalization, M, Fintype.sum_sum_type]
  have hnormEq : M.normalization = LinearMap.id :=
    (krausFamily_normalization_eq_of_map_eq M J (hMmap.trans hJ.symm)).trans hJnorm
  have hKle : K.normalization ≤ LinearMap.id := by
    rw [← hnormEq, hMnorm]
    exact le_add_of_nonneg_right (krausFamily_normalization_nonneg L)
  exact ⟨hsEvent, K, hK, hKle⟩

end QuantumModel
