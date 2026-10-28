/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.NativeFidelity.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiUmegakiKWExtra.GSLCore
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# KL divergence of POVM statistics

`povmKLDivergence` is the classical Kullback--Leibler divergence of the Born distributions of a
finite POVM.  POVM effects are pulled back through a normalized Kraus representation, and the
measurement channel of a POVM gives the bound of `povmKLDivergence` by the Umegaki relative
entropy (`povmKLDivergence_coe_le_umegakiRelEntropyNN`).  No equality with the Umegaki relative
entropy is asserted.
-/

noncomputable section

namespace QuantumModel
namespace NativeMeasuredRelativeEntropy

open QuantumState
open NativeFidelity
open scoped ENNReal

/-! ## Classical KL and the native measured divergence -/

/-- Classical Kullback--Leibler divergence of two finite probability mass
functions, using natural logarithms and Mathlib's extended nonnegative value. -/
noncomputable def classicalKL {ι : Type} [Fintype ι]
    (p q : PMF ι) : ℝ≥0∞ :=
  letI : MeasurableSpace ι := ⊤
  InformationTheory.klDiv p.toMeasure q.toMeasure

/-- Classical KL divergence between the two Born distributions produced by a
fixed finite POVM. -/
noncomputable def povmKLDivergence {A : Sys} (M : POVM A)
    (rho sigma : DensityMatrix A) : ℝ≥0∞ :=
  classicalKL (M.bornPMF rho) (M.bornPMF sigma)

/-! ## Heisenberg pullback of a POVM -/

/-- A chosen normalized Kraus family for a native CPTP superoperator. -/
noncomputable def channelKrausFamily {A B : Sys}
    (Phi : NativeNoCloning.Superoperator A B) (hPhi : IsCPTP Phi) :
    KrausFamily A B :=
  Classical.choose ((isCPTP_iff_exists_normalizedKraus Phi).mp hPhi)

/-- The chosen Kraus family represents the native CPTP superoperator. -/
theorem channelKrausFamily_map {A B : Sys}
    (Phi : NativeNoCloning.Superoperator A B) (hPhi : IsCPTP Phi) :
    (channelKrausFamily Phi hPhi).map = Phi :=
  (Classical.choose_spec
    ((isCPTP_iff_exists_normalizedKraus Phi).mp hPhi)).1

/-- The chosen Kraus family is normalized. -/
theorem channelKrausFamily_normalization {A B : Sys}
    (Phi : NativeNoCloning.Superoperator A B) (hPhi : IsCPTP Phi) :
    (channelKrausFamily Phi hPhi).normalization = LinearMap.id :=
  (Classical.choose_spec
    ((isCPTP_iff_exists_normalizedKraus Phi).mp hPhi)).2

/-- Heisenberg pullback of one effect through a Kraus family. -/
noncomputable def pullbackEffect {A B : Sys}
    (K : KrausFamily A B) (E : Operator B) : Operator A := by
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  exact ∑ j, (LinearMap.adjoint (K.operator j)).comp
    (E.comp (K.operator j))

/-- A positive effect remains positive under Kraus pullback. -/
theorem KrausFamily.pullbackEffect_nonneg {A B : Sys}
    (K : KrausFamily A B) {E : Operator B} (hE : 0 ≤ E) :
    0 ≤ pullbackEffect K E := by
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  rw [pullbackEffect]
  apply Finset.sum_nonneg
  intro j _hj
  exact (LinearMap.nonneg_iff_isPositive _).mpr
    (((LinearMap.nonneg_iff_isPositive E).mp hE).adjoint_conj
      (K.operator j))

/-- Pullback of the identity effect is the Kraus normalization operator. -/
theorem KrausFamily.pullbackEffect_id {A B : Sys}
    (K : KrausFamily A B) :
    pullbackEffect K (LinearMap.id : Operator B) = K.normalization := by
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  simp [pullbackEffect, KrausFamily.normalization]

/-! ## Trace of the pulled-back effect -/

/-- Trace duality between Schrödinger Kraus action and Heisenberg effect
pullback. -/
theorem trace_pullbackEffect {A B : Sys} (K : KrausFamily A B)
    (E : Operator B) (X : Operator A) :
    Tr ((pullbackEffect K E).comp X) =
      Tr (E.comp (HPHom.toRawSuperoperator K.map X)) := by
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  have hleft :
      (∑ j, (LinearMap.adjoint (K.operator j)).comp
          (E.comp (K.operator j))).comp X =
        ∑ j, ((LinearMap.adjoint (K.operator j)).comp
          (E.comp (K.operator j))).comp X := by
    ext x
    simp
  rw [pullbackEffect, hleft, map_sum, KrausFamily.map_toRawSuperoperator,
    KrausFamily.rawMap]
  simp only [LinearMap.sum_apply]
  have hright :
      E.comp (∑ j, QuantumChannel.krausTerm (K.operator j) X) =
        ∑ j, E.comp (QuantumChannel.krausTerm (K.operator j) X) := by
    ext x
    simp
  rw [hright, map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [QuantumChannel.krausTerm]
  calc
    Tr (((LinearMap.adjoint (K.operator j)).comp
        (E.comp (K.operator j))).comp X) =
        Tr ((LinearMap.adjoint (K.operator j)).comp
          ((E.comp (K.operator j)).comp X)) := by
      rw [LinearMap.comp_assoc]
    _ = Tr (((E.comp (K.operator j)).comp X).comp
          (LinearMap.adjoint (K.operator j))) :=
      LinearMap.trace_comp_comm' _ _
    _ = Tr (E.comp ((K.operator j).comp
          (X.comp (LinearMap.adjoint (K.operator j))))) := by
      rfl

/-! ## Measurement-channel bridge to Umegaki relative entropy -/

open QuantumChannel
open SandwichedRenyiRelativeEntropy
open scoped ComplexOrder MeasureTheory

/-- A model system has a nonzero Hilbert space because its dimension is positive. -/
instance instNontrivialSpace (A : Sys) : Nontrivial (Space A) :=
  Module.nontrivial_of_finrank_pos (R := ℂ) (by simpa using A.dim_pos)

/-- Canonical Hilbert space for a finite classical register, indexed through
`Fin (card ι)` so that no `DecidableEq ι` is required by the public API. -/
abbrev ClassicalSpace (ι : Type) [Fintype ι] :=
  EuclideanSpace ℂ (Fin (Fintype.card ι))

noncomputable instance instFiniteClassicalSpace (ι : Type) [Fintype ι] :
    Module.Finite ℂ (ClassicalSpace ι) :=
  Module.Finite.of_basis
    (EuclideanSpace.basisFun (Fin (Fintype.card ι)) ℂ).toBasis

instance instNontrivialClassicalSpace (ι : Type) [Fintype ι] [Nonempty ι] :
    Nontrivial (ClassicalSpace ι) :=
  Module.nontrivial_of_finrank_pos (R := ℂ) (by
    simp only [ClassicalSpace, finrank_euclideanSpace]
    exact Fintype.card_pos)

def classicalBasis {ι : Type} [Fintype ι] (i : ι) : ClassicalSpace ι :=
  EuclideanSpace.basisFun (Fin (Fintype.card ι)) ℂ (Fintype.equivFin ι i)

noncomputable def classicalOrthonormalBasis (ι : Type) [Fintype ι] :
    OrthonormalBasis ι ℂ (ClassicalSpace ι) :=
  (EuclideanSpace.basisFun (Fin (Fintype.card ι)) ℂ).reindex
    (Fintype.equivFin ι).symm

@[simp] theorem classicalOrthonormalBasis_apply {ι : Type} [Fintype ι]
    (i : ι) : classicalOrthonormalBasis ι i = classicalBasis i := by
  simp [classicalOrthonormalBasis, classicalBasis,
    OrthonormalBasis.reindex_apply]

/-- Operator diagonal in the canonical basis labelled by a finite type. -/
noncomputable def diagonalOperator {ι : Type} [Fintype ι]
    (z : ι → ℂ) : L (ClassicalSpace ι) :=
  ∑ i, z i • outer_product (classicalBasis i) (classicalBasis i)

@[simp] theorem inner_classicalBasis {ι : Type} [Fintype ι] [DecidableEq ι]
    (i j : ι) :
    inner ℂ (classicalBasis i) (classicalBasis j) = if i = j then 1 else 0 := by
  classical
  simpa [classicalBasis] using
    (EuclideanSpace.basisFun (Fin (Fintype.card ι)) ℂ).inner_eq_ite
      (Fintype.equivFin ι i) (Fintype.equivFin ι j)

@[simp] theorem outer_product_classicalBasis_apply {ι : Type} [Fintype ι]
    [DecidableEq ι]
    (i j : ι) :
    outer_product (classicalBasis i) (classicalBasis i) (classicalBasis j) =
      if i = j then classicalBasis j else 0 := by
  classical
  rw [outer_product_eq_rankOne]
  change inner ℂ (classicalBasis i) (classicalBasis j) • classicalBasis i = _
  rw [inner_classicalBasis]
  by_cases h : i = j <;> simp [h]

@[simp] theorem diagonalOperator_apply_basis {ι : Type} [Fintype ι]
    (z : ι → ℂ) (i : ι) :
    diagonalOperator z (classicalBasis i) = z i • classicalBasis i := by
  classical
  rw [diagonalOperator]
  simp only [LinearMap.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp only [LinearMap.smul_apply, outer_product_classicalBasis_apply, if_pos]
  · intro j _hj hji
    simp only [LinearMap.smul_apply, outer_product_classicalBasis_apply,
      if_neg hji, smul_zero]
  · simp

@[simp] theorem norm_classicalBasis {ι : Type} [Fintype ι] (i : ι) :
    ‖classicalBasis i‖ = 1 := by
  simp [classicalBasis]

/-- Density operator whose canonical diagonal is the finite PMF `p`. -/
noncomputable def diagonalPMF {ι : Type} [Fintype ι] (p : PMF ι) :
    L (ClassicalSpace ι) :=
  diagonalOperator (fun i ↦ ((p i).toReal : ℂ))

@[simp] theorem diagonalPMF_apply_basis {ι : Type} [Fintype ι]
    (p : PMF ι) (i : ι) :
    diagonalPMF p (classicalBasis i) =
      ((p i).toReal : ℂ) • classicalBasis i :=
  diagonalOperator_apply_basis _ i

theorem trace_diagonalOperator {ι : Type} [Fintype ι] (z : ι → ℂ) :
    Tr (diagonalOperator z) = ∑ i, z i := by
  classical
  simp [diagonalOperator, map_sum, trace_outer_product]

theorem diagonalOperator_nonneg {ι : Type} [Fintype ι]
    (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) :
    0 ≤ diagonalOperator (fun i ↦ (r i : ℂ)) := by
  classical
  rw [diagonalOperator]
  apply Finset.sum_nonneg
  intro i _hi
  apply (LinearMap.nonneg_iff_isPositive _).mpr
  exact ((LinearMap.nonneg_iff_isPositive _).mp (outer_product_self_nonneg _)).smul_of_nonneg
    (Complex.zero_le_real.mpr (hr i))

theorem diagonalPMF_nonneg {ι : Type} [Fintype ι] (p : PMF ι) :
    0 ≤ diagonalPMF p := by
  exact diagonalOperator_nonneg _ (fun i ↦ ENNReal.toReal_nonneg)

theorem trace_diagonalPMF {ι : Type} [Fintype ι] (p : PMF ι) :
    Tr (diagonalPMF p) = 1 := by
  rw [diagonalPMF, trace_diagonalOperator]
  norm_cast
  rw [← ENNReal.toReal_sum]
  · have hp : ∑ i, p i = 1 := by simpa using p.tsum_coe
    rw [hp]
    simp
  · exact fun i _hi ↦ p.apply_ne_top i

/-! Measurement channel. -/

noncomputable def povmSpectralVectors {A : Sys} (M : POVM A) (i : M.ι) :
    Fin (Module.finrank ℂ (Space A)) → Space A :=
  Classical.choose
    (positive_full_spectral_outer_product (M.effect i) (M.nonneg i))

theorem povmSpectralVectors_sum {A : Sys} (M : POVM A) (i : M.ι) :
    M.effect i = ∑ a, outer_product (povmSpectralVectors M i a)
      (povmSpectralVectors M i a) :=
  (Classical.choose_spec
    (positive_full_spectral_outer_product (M.effect i) (M.nonneg i))).1

noncomputable def measurementKrausOperator {A : Sys} (M : POVM A)
    (p : M.ι × Fin (Module.finrank ℂ (Space A))) :
    Space A →ₗ[ℂ] ClassicalSpace M.ι :=
  outer_product (povmSpectralVectors M p.1 p.2) (classicalBasis p.1)

theorem trace_outer_product_comp {A : Sys} (u : Space A) (X : Operator A) :
    Tr ((outer_product u u).comp X) = inner ℂ u (X u) := by
  calc
    Tr ((outer_product u u).comp X) = Tr (X.comp (outer_product u u)) :=
      LinearMap.trace_comp_comm' _ _
    _ = Tr (outer_product u (X u)) := by
      congr 1
      ext x
      simp [outer_product_eq_rankOne]
    _ = inner ℂ u (X u) := trace_outer_product _ _

theorem measurementKrausTerm_apply {A : Sys} (M : POVM A)
    (p : M.ι × Fin (Module.finrank ℂ (Space A))) (X : Operator A) :
    krausTerm (measurementKrausOperator M p) X =
      (inner ℂ (povmSpectralVectors M p.1 p.2)
          (X (povmSpectralVectors M p.1 p.2))) •
        outer_product (classicalBasis p.1) (classicalBasis p.1) := by
  let u := povmSpectralVectors M p.1 p.2
  let e := classicalBasis p.1
  let W : Space A →ₗ[ℂ] ClassicalSpace M.ι := outer_product u e
  change W.comp (X.comp (LinearMap.adjoint W)) =
    (inner ℂ u (X u)) • outer_product e e
  have hadj (y : ClassicalSpace M.ι) :
      LinearMap.adjoint W y = inner ℂ e y • u := by
    apply ext_inner_right ℂ
    intro x
    rw [LinearMap.adjoint_inner_left]
    rw [show W x = inner ℂ u x • e by
      simp [W, outer_product_eq_rankOne]]
    simp
  ext y
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hadj, map_smul]
  simp [W, outer_product_eq_rankOne]
  ring

noncomputable def measurementRaw {A : Sys} (M : POVM A) :
    T (Space A) (ClassicalSpace M.ι) :=
  ∑ p : M.ι × Fin (Module.finrank ℂ (Space A)),
    krausTerm (measurementKrausOperator M p)

theorem sum_inner_povmSpectralVectors {A : Sys} (M : POVM A)
    (i : M.ι) (X : Operator A) :
    (∑ a, inner ℂ (povmSpectralVectors M i a)
      (X (povmSpectralVectors M i a))) = Tr ((M.effect i).comp X) := by
  rw [povmSpectralVectors_sum]
  have hcomp :
      (∑ a, outer_product (povmSpectralVectors M i a)
        (povmSpectralVectors M i a)).comp X =
      ∑ a, (outer_product (povmSpectralVectors M i a)
        (povmSpectralVectors M i a)).comp X := by
    ext x
    simp
  rw [hcomp, map_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  exact (trace_outer_product_comp (povmSpectralVectors M i a) X).symm

theorem measurementRaw_apply {A : Sys} (M : POVM A) (X : Operator A) :
    measurementRaw M X =
      diagonalOperator (fun i ↦ Tr ((M.effect i).comp X)) := by
  classical
  rw [measurementRaw]
  simp only [LinearMap.sum_apply, Fintype.sum_prod_type]
  simp_rw [measurementKrausTerm_apply]
  rw [diagonalOperator]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← sum_inner_povmSpectralVectors M i X, Finset.sum_smul]

theorem measurementRaw_isCompletelyPositive {A : Sys} (M : POVM A) :
    IsCompletelyPositive (measurementRaw M) := by
  classical
  exact sum_krausTerm_isCompletelyPositive (measurementKrausOperator M)

noncomputable def measurementCPMap {A : Sys} (M : POVM A) :
    CompletelyPositiveMap (Operator A) (L (ClassicalSpace M.ι)) :=
  Classical.choose (measurementRaw_isCompletelyPositive M)

theorem measurementCPMap_toLinearMap {A : Sys} (M : POVM A) :
    (measurementCPMap M).toLinearMap = measurementRaw M :=
  Classical.choose_spec (measurementRaw_isCompletelyPositive M)

theorem trace_measurementRaw {A : Sys} (M : POVM A) (X : Operator A) :
    Tr (measurementRaw M X) = Tr X := by
  rw [measurementRaw_apply, trace_diagonalOperator]
  calc
    (∑ i, Tr ((M.effect i).comp X)) =
        Tr ((∑ i, M.effect i).comp X) := by
      have hcomp : (∑ i, M.effect i).comp X =
          ∑ i, (M.effect i).comp X := by
        ext x
        simp
      rw [hcomp, map_sum]
    _ = Tr X := by rw [M.sum_eq_id, LinearMap.id_comp]

/-- CPTP measurement channel associated with a finite POVM.  Its classical
output is `∑ i, p i |i⟩⟨i|`, with `p` the Born PMF. -/
noncomputable def measurementChannel {A : Sys} (M : POVM A) :
    CPTP (Space A) (ClassicalSpace M.ι) where
  toCompletelyPositiveMap := measurementCPMap M
  trace_map X := by
    rw [measurementCPMap_toLinearMap]
    exact (trace_measurementRaw M X).symm

theorem trace_comp_nonneg {A : Sys} (P Q : Operator A)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    (0 : ℂ) ≤ Tr (P.comp Q) := by
  let S : Operator A := CFC.sqrt P
  have hSadj : LinearMap.adjoint S = S := by
    rw [← LinearMap.star_eq_adjoint]
    exact (CFC.sqrt_nonneg P).isSelfAdjoint
  have hSsq : S.comp S = P := CFC.sqrt_mul_sqrt_self P hP
  have hQpos : Q.IsPositive := (LinearMap.nonneg_iff_isPositive Q).mp hQ
  have hconj : ((LinearMap.adjoint S).comp (Q.comp S)).IsPositive :=
    hQpos.adjoint_conj S
  have htrace : Tr (P.comp Q) =
      Tr ((LinearMap.adjoint S).comp (Q.comp S)) := by
    calc
      Tr (P.comp Q) = Tr (Q.comp P) :=
        (LinearMap.trace_comp_comm' P Q).symm
      _ = Tr (Q.comp (S.comp S)) := by rw [hSsq]
      _ = Tr ((Q.comp S).comp S) := by rw [LinearMap.comp_assoc]
      _ = Tr (S.comp (Q.comp S)) := LinearMap.trace_comp_comm' S (Q.comp S)
      _ = Tr ((LinearMap.adjoint S).comp (Q.comp S)) := by rw [hSadj]
  rw [htrace]
  exact hconj.trace_nonneg

/-- A measurement channel outputs the Born PMF as a diagonal operator. -/
theorem measurementChannel_apply {A : Sys} (M : POVM A)
    (rho : DensityMatrix A) :
    (measurementChannel M).toFun rho.operator =
      diagonalPMF (M.bornPMF rho) := by
  change (measurementCPMap M).toLinearMap rho.operator = _
  rw [measurementCPMap_toLinearMap, measurementRaw_apply, diagonalPMF]
  congr 1
  funext i
  rw [POVM.bornPMF_apply]
  rw [ENNReal.toReal_ofReal (M.bornProbability_nonneg rho i)]
  unfold NativeNoCloning.bornProbability
  have htr := trace_comp_nonneg (M.effect i) rho.operator (M.nonneg i) rho.nonneg
  exact Complex.ext rfl (Complex.nonneg_iff.mp htr).2.symm

theorem diagonalOperator_apply {ι : Type} [Fintype ι] (z : ι → ℂ)
    (x : ClassicalSpace ι) :
    diagonalOperator z x =
      ∑ i, (z i * inner ℂ (classicalBasis i) x) • classicalBasis i := by
  have hexpand :
      (∑ i, inner ℂ (classicalBasis i) x • classicalBasis i) = x := by
    simpa using (classicalOrthonormalBasis ι).sum_repr' x
  calc
    diagonalOperator z x = diagonalOperator z
        (∑ i, inner ℂ (classicalBasis i) x • classicalBasis i) := by
      rw [hexpand]
    _ = ∑ i, diagonalOperator z
        (inner ℂ (classicalBasis i) x • classicalBasis i) := by
      rw [map_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [map_smul, diagonalOperator_apply_basis, smul_smul]
      rw [mul_comm]

theorem inner_diagonalOperator {ι : Type} [Fintype ι]
    (z : ι → ℂ) (x : ClassicalSpace ι) (i : ι) :
    inner ℂ (classicalBasis i) (diagonalOperator z x) =
      z i * inner ℂ (classicalBasis i) x := by
  classical
  rw [diagonalOperator_apply, inner_sum]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [hji.symm]
  · simp

theorem suppLE_diagonalPMF_iff {ι : Type} [Fintype ι] [Nonempty ι]
    (p q : PMF ι) :
    suppLE (diagonalPMF p) (diagonalPMF q) ↔
      ∀ i, q i = 0 → p i = 0 := by
  classical
  constructor
  · intro hsupp i hqi
    have hqker : classicalBasis i ∈ LinearMap.ker (diagonalPMF q) := by
      rw [LinearMap.mem_ker, diagonalPMF, diagonalOperator_apply_basis]
      simp [hqi]
    have hpker := hsupp hqker
    rw [LinearMap.mem_ker, diagonalPMF, diagonalOperator_apply_basis] at hpker
    have hbasis : classicalBasis i ≠ 0 := by
      intro hzero
      have := norm_classicalBasis i
      rw [hzero, norm_zero] at this
      norm_num at this
    have hpReal : (p i).toReal = 0 := by
      have hcomplex : ((p i).toReal : ℂ) = 0 :=
        (smul_eq_zero.mp hpker).resolve_right hbasis
      exact_mod_cast hcomplex
    exact (ENNReal.toReal_eq_zero_iff (p i)).mp hpReal |>.resolve_right
      (p.apply_ne_top i)
  · intro hpq x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [diagonalPMF, diagonalOperator_apply]
    apply Finset.sum_eq_zero
    intro i _hi
    have hcoef : ((q i).toReal : ℂ) *
        inner ℂ (classicalBasis i) x = 0 := by
      have := congrArg (fun y ↦ inner ℂ (classicalBasis i) y) hx
      change inner ℂ (classicalBasis i)
          (diagonalOperator (fun i ↦ ((q i).toReal : ℂ)) x) =
        inner ℂ (classicalBasis i) 0 at this
      rw [inner_diagonalOperator] at this
      simpa using this
    by_cases hqi : q i = 0
    · simp [hpq i hqi]
    · have hqReal : ((q i).toReal : ℂ) ≠ 0 := by
        exact_mod_cast (ENNReal.toReal_ne_zero.mpr ⟨hqi, q.apply_ne_top i⟩)
      have hinner : inner ℂ (classicalBasis i) x = 0 :=
        (mul_eq_zero.mp hcoef).resolve_left hqReal
      simp [hinner]

theorem log_diagonalPMF_apply {ι : Type} [Fintype ι] [Nonempty ι]
    (p : PMF ι) (i : ι) :
    CFC.log (diagonalPMF p) (classicalBasis i) =
      ((Real.log (p i).toReal : ℝ) : ℂ) • classicalBasis i := by
  have hbasis : classicalBasis (ι := ι) i ≠ 0 := by
    intro hzero
    have hnorm : ‖classicalBasis (ι := ι) i‖ = 1 := norm_classicalBasis i
    rw [hzero, norm_zero] at hnorm
    exact zero_ne_one hnorm
  refine cfc_real_apply_eigenvector_lm
    (IsSelfAdjoint.of_nonneg (diagonalPMF_nonneg p)) Real.log
    (diagonalOperator_apply_basis _ i) ?_
  exact mem_spectrum_real_of_eigenvector_lm
    (A := diagonalPMF p) (v := classicalBasis i) hbasis
    (diagonalOperator_apply_basis _ i)

theorem umegakiNorm_diagonalPMF {ι : Type} [Fintype ι] [Nonempty ι]
    (p q : PMF ι) :
    umegakiNorm (diagonalPMF p) (diagonalPMF q) =
      ∑ i, (p i).toReal * (Real.log (p i).toReal - Real.log (q i).toReal) := by
  unfold umegakiNorm
  rw [trace_diagonalPMF]
  simp only [Complex.one_re, div_one]
  rw [LinearMap.trace_eq_sum_inner
    (diagonalPMF p * (CFC.log (diagonalPMF p) - CFC.log (diagonalPMF q)))
    (classicalOrthonormalBasis ι), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [classicalOrthonormalBasis_apply, Module.End.mul_apply,
    LinearMap.sub_apply, log_diagonalPMF_apply p i,
    log_diagonalPMF_apply q i]
  have hinner : inner ℂ (classicalBasis i) (classicalBasis i) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, norm_classicalBasis]
    norm_num
  simp only [map_sub, map_smul, diagonalPMF_apply_basis,
    inner_sub_right, inner_smul_right, hinner,
    mul_one, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem pmf_toMeasure_ac_iff {ι : Type} (p q : PMF ι) :
    @MeasureTheory.Measure.AbsolutelyContinuous ι ⊤
      (@PMF.toMeasure ι ⊤ p) (@PMF.toMeasure ι ⊤ q) ↔
      ∀ i, q i = 0 → p i = 0 := by
  letI : MeasurableSpace ι := ⊤
  constructor
  · intro hac i hqi
    have hzero : q.toMeasure ({i} : Set ι) = 0 := by
      rw [PMF.toMeasure_apply_singleton q i (MeasurableSet.singleton i), hqi]
    have := hac hzero
    simpa [PMF.toMeasure_apply_singleton p i (MeasurableSet.singleton i)] using this
  · intro hpq
    refine MeasureTheory.Measure.AbsolutelyContinuous.mk fun s hs hqs ↦ ?_
    rw [p.toMeasure_apply_eq_zero_iff hs]
    rw [q.toMeasure_apply_eq_zero_iff hs] at hqs
    rw [Set.disjoint_left] at hqs ⊢
    intro i hip his
    exact hqs ((q.mem_support_iff i).2 fun hqi ↦
      (p.mem_support_iff i).1 hip (hpq i hqi)) his

theorem classicalKL_toReal_eq_sum {ι : Type} [Fintype ι] (p q : PMF ι)
    (hpq : ∀ i, q i = 0 → p i = 0) :
    (classicalKL p q).toReal =
      ∑ i, (p i).toReal *
        (Real.log (p i).toReal - Real.log (q i).toReal) := by
  letI : MeasurableSpace ι := ⊤
  have hac : p.toMeasure ≪ q.toMeasure := (pmf_toMeasure_ac_iff p q).2 hpq
  rw [classicalKL]
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac (by simp)]
  rw [PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hpi : p i = 0
  · simp [hpi]
  have hqi : q i ≠ 0 := fun h ↦ hpi (hpq i h)
  have hrn_mul :
      p.toMeasure.rnDeriv q.toMeasure i * q i = p i := by
    have hrn := MeasureTheory.Measure.setLIntegral_rnDeriv'
      hac (MeasurableSet.singleton i)
    rw [MeasureTheory.lintegral_singleton,
      PMF.toMeasure_apply_singleton q i (MeasurableSet.singleton i),
      PMF.toMeasure_apply_singleton p i (MeasurableSet.singleton i)] at hrn
    exact hrn
  have hpReal : (p i).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hpi, p.apply_ne_top i⟩
  have hqReal : (q i).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hqi, q.apply_ne_top i⟩
  have hrnReal : (p.toMeasure.rnDeriv q.toMeasure i).toReal =
      (p i).toReal / (q i).toReal := by
    rw [eq_div_iff hqReal]
    simpa only [ENNReal.toReal_mul] using congrArg ENNReal.toReal hrn_mul
  change (p i).toReal *
      Real.log (p.toMeasure.rnDeriv q.toMeasure i).toReal = _
  rw [hrnReal, Real.log_div hpReal hqReal]

theorem classicalKL_ne_top_of_support {ι : Type} [Fintype ι] (p q : PMF ι)
    (hpq : ∀ i, q i = 0 → p i = 0) : classicalKL p q ≠ ⊤ := by
  letI : MeasurableSpace ι := ⊤
  have hac : p.toMeasure ≪ q.toMeasure := (pmf_toMeasure_ac_iff p q).2 hpq
  rw [classicalKL]
  exact InformationTheory.klDiv_ne_top hac MeasureTheory.Integrable.of_finite

/-- Umegaki relative entropy of diagonal finite PMFs is Mathlib's classical KL,
including the infinite value caused by a support mismatch. -/
theorem umegakiRelEntropyNN_diagonalPMF
    {ι : Type} [Fintype ι] [Nonempty ι] (p q : PMF ι) :
    umegakiRelEntropyNN (diagonalPMF p) (diagonalPMF q) =
      (classicalKL p q : EReal) := by
  by_cases hpq : ∀ i, q i = 0 → p i = 0
  · rw [umegakiRelEntropyNN,
      if_pos ((suppLE_diagonalPMF_iff p q).2 hpq),
      umegakiNorm_diagonalPMF]
    have hne := classicalKL_ne_top_of_support p q hpq
    rw [← EReal.coe_ennreal_toReal hne, classicalKL_toReal_eq_sum p q hpq]
  · have hsupp : ¬ suppLE (diagonalPMF p) (diagonalPMF q) := by
      simpa only [suppLE_diagonalPMF_iff] using hpq
    rw [umegakiRelEntropyNN, if_neg hsupp]
    letI : MeasurableSpace ι := ⊤
    have hac : ¬p.toMeasure ≪ q.toMeasure := by
      simpa only [pmf_toMeasure_ac_iff] using hpq
    rw [classicalKL, InformationTheory.klDiv_of_not_ac hac,
      EReal.coe_ennreal_top]

theorem povmKLDivergence_coe_le_umegakiRelEntropyNN {A : Sys}
    (M : POVM A) (rho sigma : DensityMatrix A) :
    (povmKLDivergence M rho sigma : EReal) ≤
      umegakiRelEntropyNN rho.operator sigma.operator := by
  letI : Nonempty M.ι :=
    ⟨Classical.choose (M.bornPMF rho).support_nonempty⟩
  have hdpi := UmegakiDPI.monotoneOnNonNeg
    (measurementChannel M) rho.nonneg sigma.nonneg
  rw [measurementChannel_apply M rho, measurementChannel_apply M sigma,
    umegakiRelEntropyNN_diagonalPMF] at hdpi
  exact hdpi

theorem umegakiRelEntropyNN_density_nonneg {A : Sys}
    (rho sigma : DensityMatrix A) :
    0 ≤ umegakiRelEntropyNN rho.operator sigma.operator := by
  exact (EReal.coe_ennreal_nonneg
      (povmKLDivergence (POVM.trivial A) rho sigma)).trans
    (povmKLDivergence_coe_le_umegakiRelEntropyNN
      (POVM.trivial A) rho sigma)

end NativeMeasuredRelativeEntropy
end QuantumModel
