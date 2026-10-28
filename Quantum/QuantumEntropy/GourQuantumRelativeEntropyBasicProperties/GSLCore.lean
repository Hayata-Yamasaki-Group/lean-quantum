import Quantum.QuantumMechanics.OuterProduct.GSLCore
import Quantum.QuantumEntropy.GourQuantumMaxRelativeEntropy.GSLCore
import Quantum.QuantumEntropy.PetzRenyiEndpointIdentities.GSLCore
import Quantum.OperationalProbabilistic.Framework.QuantumRelativeEntropyLaws.GSLCore

import Quantum.QuantumMechanics.Channel.ChoiKraus
import Quantum.QuantumMechanics.Channel.Representations
/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

open scoped ComplexOrder ENNReal NNReal TensorProduct

/-!
# Bounds for Gour quantum relative entropies

Gour's Theorem 6.10 bounds an arbitrary finite-dimensional matrix divergence satisfying data
processing, tensor additivity, and binary normalization
(`gourQuantumRelativeEntropy_min_max_bounds`).  The measurement, preparation and calibration
channels used in the proof are constructed as concrete CPTP maps.
-/

namespace OPT

noncomputable section

universe u v

open QuantumState QuantumChannel
open SandwichedRenyiRelativeEntropy

/-! ## Concrete finite-dimensional channels -/

/-- The measure-and-prepare summand `X ↦ Tr(A X) B`. -/
private noncomputable def gourMeasurePrepareTerm
    {H : Type u} {K : Type v} [Qudit H] [Qudit K] (A : L H) (B : L K) :
    T H K where
  toFun X := Tr (A * X) • B
  map_add' X Y := by
    rw [mul_add, map_add, add_smul]
  map_smul' c X := by
    rw [mul_smul_comm, map_smul, RingHom.id_apply]
    simp [smul_eq_mul, smul_smul]

/-- The adjoint of an outer product exchanges its two vectors. -/
private lemma gourAdjoint_outerProduct
    {H : Type u} {K : Type v} [Qudit H] [Qudit K] (x : H) (y : K) :
    LinearMap.adjoint (outer_product x y) = outer_product y x := by
  apply LinearMap.ext
  intro z
  apply ext_inner_right ℂ
  intro w
  rw [LinearMap.adjoint_inner_left, QuantumChannel.outer_product_apply_univ,
    QuantumChannel.outer_product_apply_univ, inner_smul_right, inner_smul_left,
    inner_conj_symm]
  ring

/-- A rank-one Kraus term evaluates to a scalar multiple of a rank-one output. -/
private lemma gourKrausTerm_outerProduct
    {H : Type u} {K : Type v} [Qudit H] [Qudit K]
    (x : H) (y : K) (X : L H) :
    (krausTerm (outer_product x y) : T H K) X =
      inner ℂ x (X x) • outer_product y y := by
  apply LinearMap.ext
  intro z
  change outer_product x y (X (LinearMap.adjoint (outer_product x y) z)) =
    (inner ℂ x (X x) • outer_product y y) z
  rw [gourAdjoint_outerProduct]
  simp only [QuantumChannel.outer_product_apply_univ, map_smul, smul_smul,
    LinearMap.smul_apply]
  rw [mul_comm]

/-- Trace evaluation used in the measure-and-prepare Kraus decomposition. -/
private lemma gourTrace_outerProduct_mul
    {H : Type u} [Qudit H] (x : H) (X : L H) :
    Tr (outer_product x x * X) = inner ℂ x (X x) := by
  rw [LinearMap.trace_mul_comm ℂ (outer_product x x) X]
  have hcomp : X * outer_product x x = outer_product x (X x) := by
    ext z
    simp only [Module.End.mul_apply, QuantumChannel.outer_product_apply, map_smul]
  rw [hcomp, trace_outer_product]

/-- A positive measure-and-prepare summand is completely positive. -/
private lemma gourMeasurePrepareTerm_isCompletelyPositive
    {H : Type u} {K : Type v} [Qudit H] [Qudit K]
    (A : L H) (B : L K) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    IsCompletelyPositive (gourMeasurePrepareTerm A B) := by
  classical
  obtain ⟨x, hx, _⟩ := positive_full_spectral_outer_product A hA
  obtain ⟨y, hy, _⟩ := positive_full_spectral_outer_product B hB
  apply fixed_kraus_to_cp (gourMeasurePrepareTerm A B)
    (κ := Fin (Module.finrank ℂ H) × Fin (Module.finrank ℂ K))
  refine ⟨fun p : Fin (Module.finrank ℂ H) × Fin (Module.finrank ℂ K) =>
    outer_product (x p.1) (y p.2), ?_⟩
  intro X
  change gourMeasurePrepareTerm A B X =
    ∑ p : Fin (Module.finrank ℂ H) × Fin (Module.finrank ℂ K),
      (krausTerm (outer_product (x p.1) (y p.2)) : T H K) X
  simp_rw [gourKrausTerm_outerProduct]
  rw [Fintype.sum_prod_type]
  have hinner : (∑ i, inner ℂ (x i) (X (x i))) = Tr (A * X) := by
    rw [hx, Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (gourTrace_outerProduct_mul (x i) X).symm
  have hy' : (∑ j, outer_product (y j) (y j)) = B := hy.symm
  simp_rw [← Finset.smul_sum, hy']
  rw [← Finset.sum_smul, hinner]
  rfl

/-- The linear map underlying a binary measure-and-prepare channel. -/
private noncomputable def gourMeasurePrepareMap
    {H : Type u} {K : Type v} [Qudit H] [Qudit K]
    (effect : Fin 2 → L H) (state : Fin 2 → L K) : T H K :=
  gourMeasurePrepareTerm (effect 0) (state 0) +
    gourMeasurePrepareTerm (effect 1) (state 1)

/-- A finite POVM followed by preparation of density operators is CPTP. -/
private noncomputable def gourMeasurePrepareChannel
    {H : Type u} {K : Type v} [Qudit H] [Qudit K]
    (effect : Fin 2 → L H) (state : Fin 2 → L K)
    (heffect : ∀ i, 0 ≤ effect i)
    (hsum : ∑ i, effect i = 1)
    (hstate : ∀ i, IsDensity (state i)) : CPTP H K where
  toFun := gourMeasurePrepareMap effect state
  map_add' := (gourMeasurePrepareMap effect state).map_add
  map_smul' := (gourMeasurePrepareMap effect state).map_smul
  map_cstarMatrix_nonneg' k M hM := by
    have hcp0 := gourMeasurePrepareTerm_isCompletelyPositive
      (effect 0) (state 0) (heffect 0)
      ((LinearMap.nonneg_iff_isPositive _).mpr (hstate 0).1)
    have hcp1 := gourMeasurePrepareTerm_isCompletelyPositive
      (effect 1) (state 1) (heffect 1)
      ((LinearMap.nonneg_iff_isPositive _).mpr (hstate 1).1)
    have h0 := (isCompletelyPositive_iff_cstarMatrix_nonneg _).mp hcp0 k M hM
    have h1 := (isCompletelyPositive_iff_cstarMatrix_nonneg _).mp hcp1 k M hM
    simpa only [gourMeasurePrepareMap, CStarMatrix.map_apply,
      LinearMap.add_apply] using add_nonneg h0 h1
  trace_map X := by
    rw [show gourMeasurePrepareMap effect state X =
        ∑ i, Tr (effect i * X) • state i by
      simp [gourMeasurePrepareMap, gourMeasurePrepareTerm, Fin.sum_univ_two]]
    rw [map_sum]
    simp_rw [map_smul, smul_eq_mul, (hstate _).2, mul_one]
    rw [← map_sum, ← Finset.sum_mul, hsum, one_mul]

@[simp]
private lemma gourMeasurePrepareChannel_apply
    {H : Type u} {K : Type v} [Qudit H] [Qudit K]
    (effect : Fin 2 → L H) (state : Fin 2 → L K)
    (heffect : ∀ i, 0 ≤ effect i)
    (hsum : ∑ i, effect i = 1)
    (hstate : ∀ i, IsDensity (state i)) (X : L H) :
    (gourMeasurePrepareChannel effect state heffect hsum hstate).toFun X =
      ∑ i, Tr (effect i * X) • state i := by
  change (gourMeasurePrepareMap effect state) X = _
  simp [gourMeasurePrepareMap, gourMeasurePrepareTerm, Fin.sum_univ_two]

/-! ## A concrete binary calibration system -/

private abbrev GourBit := EuclideanSpace ℂ (ULift.{u} (Fin 2))

private noncomputable def gourBitBasis :
    OrthonormalBasis (ULift.{u} (Fin 2)) ℂ GourBit.{u} :=
  EuclideanSpace.basisFun (ULift.{u} (Fin 2)) ℂ

private noncomputable def gourBitPure (i : Fin 2) : L GourBit.{u} :=
  outer_product (gourBitBasis (ULift.up i)) (gourBitBasis (ULift.up i))

private lemma gourBitPure_density (i : Fin 2) :
    IsDensity (gourBitPure.{u} i) := by
  constructor
  · exact (LinearMap.nonneg_iff_isPositive _).mp
      (outer_product_self_nonneg (gourBitBasis (ULift.up i)))
  · rw [gourBitPure, trace_outer_product]
    simp

private lemma gourBitPure_idempotent (i : Fin 2) :
    IsIdempotentElem (gourBitPure.{u} i) := by
  change gourBitPure i * gourBitPure i = gourBitPure i
  ext x
  simp only [Module.End.mul_apply, gourBitPure, QuantumChannel.outer_product_apply,
    map_smul, smul_smul]
  have hii : inner ℂ (gourBitBasis (ULift.up i))
      (gourBitBasis (ULift.up i)) = 1 := by
    simp
  rw [hii]
  simp

private lemma gourBitPure_orthogonal :
    gourBitPure.{u} 0 * gourBitPure 1 = 0 := by
  ext x
  simp only [Module.End.mul_apply, gourBitPure, QuantumChannel.outer_product_apply,
    map_smul, smul_smul, LinearMap.zero_apply]
  have h01 : inner ℂ (gourBitBasis (ULift.up (0 : Fin 2)))
      (gourBitBasis (ULift.up (1 : Fin 2))) = 0 := by
    simp
  rw [h01]
  simp

private lemma gourBitPure_resolution :
    gourBitPure.{u} 0 + gourBitPure 1 = 1 := by
  have h := linearMap_eq_sum_outer_product gourBitBasis (1 : L GourBit.{u})
  simp only [Module.End.one_apply] at h
  have hsumAll :
      (∑ j : ULift.{u} (Fin 2),
        outer_product (gourBitBasis j) (gourBitBasis j)) = 1 := h.symm
  have hsum : (∑ i : Fin 2, gourBitPure i) = 1 := by
    calc
      (∑ i : Fin 2, gourBitPure i) =
          ∑ j : ULift.{u} (Fin 2),
            outer_product (gourBitBasis j) (gourBitBasis j) := by
        refine Fintype.sum_equiv
          (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2)) _ _ ?_
        intro i
        rfl
      _ = 1 := hsumAll
  simpa [Fin.sum_univ_two] using hsum

private noncomputable def gourBinaryPair : PetzBinaryPurePair GourBit.{u} where
  pure₀ := gourBitPure 0
  pure₁ := gourBitPure 1
  pure₀_density := gourBitPure_density 0
  pure₁_density := gourBitPure_density 1
  pure₀_idempotent := gourBitPure_idempotent 0
  pure₁_idempotent := gourBitPure_idempotent 1
  orthogonal := gourBitPure_orthogonal
  resolution := gourBitPure_resolution

/-- The classical binary density with distinguished probability `p`. -/
private noncomputable def gourBinaryState (p : ℝ≥0) : L GourBit.{u} :=
  ((p : ℝ) : ℂ) • gourBinaryPair.pure₀ +
    (((1 - p : ℝ≥0) : ℝ) : ℂ) • gourBinaryPair.pure₁

private lemma gourBinaryState_density (p : ℝ≥0) (hp : p ≤ 1) :
    IsDensity (gourBinaryState.{u} p) := by
  have hpComplex : (0 : ℂ) ≤ ((p : ℝ) : ℂ) :=
    Complex.zero_le_real.mpr p.property
  have hcompComplex : (0 : ℂ) ≤ (((1 - p : ℝ≥0) : ℝ) : ℂ) :=
    Complex.zero_le_real.mpr (NNReal.coe_nonneg _)
  constructor
  · rw [gourBinaryState]
    exact (gourBinaryPair.pure₀_density.1.smul_of_nonneg hpComplex).add
      (gourBinaryPair.pure₁_density.1.smul_of_nonneg hcompComplex)
  · rw [gourBinaryState, map_add, map_smul, map_smul,
      gourBinaryPair.pure₀_density.2, gourBinaryPair.pure₁_density.2,
      smul_eq_mul, smul_eq_mul]
    push_cast [NNReal.coe_sub hp]
    ring

@[simp]
private lemma gourBinaryState_one :
    gourBinaryState.{u} 1 = gourBinaryPair.pure₀ := by
  simp [gourBinaryState]

private lemma gourBinaryState_half :
    gourBinaryState.{u} ((2 : ℝ≥0)⁻¹) = gourBinaryPair.uniform := by
  rw [gourBinaryState, PetzBinaryPurePair.uniform, ← gourBinaryPair.resolution]
  norm_num

/-! ## The three laws and binary calibration -/

/-- A system-polymorphic extended-real divergence on finite-dimensional
density operators. -/
abbrev GourMatrixStateDivergence :=
  {H : Type u} → [Qudit H] → [Nontrivial H] →
    (rho sigma : L H) → IsDensity rho → IsDensity sigma → EReal

/-- The matrix form of Gour's three defining laws for a quantum relative
entropy: data processing, tensor additivity, and binary normalization. -/
structure GourMatrixRelativeEntropyLaws
    (D : GourMatrixStateDivergence.{u}) : Prop where
  dataProcessing :
    ∀ {H K : Type u} [Qudit H] [Nontrivial H] [Qudit K] [Nontrivial K]
      (E : CPTP H K)
      (rho sigma : L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma),
      D (E.toFun rho) (E.toFun sigma)
          (quantumFMapDensity E rho hrho) (quantumFMapDensity E sigma hsigma) ≤
        D rho sigma hrho hsigma
  tensorAdditivity :
    ∀ {H K : Type u} [Qudit H] [Nontrivial H] [Qudit K] [Nontrivial K]
      [Nontrivial (H ⊗[ℂ] K)]
      (rho₁ sigma₁ : L H) (rho₂ sigma₂ : L K)
      (hrho₁ : IsDensity rho₁) (hsigma₁ : IsDensity sigma₁)
      (hrho₂ : IsDensity rho₂) (hsigma₂ : IsDensity sigma₂),
      D (TensorProduct.map rho₁ rho₂ : L (H ⊗[ℂ] K))
          (TensorProduct.map sigma₁ sigma₂)
          (isDensity_tensorProduct rho₁ rho₂ hrho₁ hrho₂)
          (isDensity_tensorProduct sigma₁ sigma₂ hsigma₁ hsigma₂) =
        D rho₁ sigma₁ hrho₁ hsigma₁ + D rho₂ sigma₂ hrho₂ hsigma₂
  binaryNormalization :
    ∀ {H : Type u} [Qudit H] [Nontrivial H] (pair : PetzBinaryPurePair H),
      D pair.pure₀ pair.uniform pair.pure₀_density pair.uniform_density = 1

private lemma gourBinaryPure_one_mul_zero :
    gourBinaryPair.{u}.pure₁ * gourBinaryPair.pure₀ = 0 := by
  change gourBitPure 1 * gourBitPure 0 = 0
  ext x
  simp only [Module.End.mul_apply, gourBitPure, QuantumChannel.outer_product_apply,
    map_smul, smul_smul, LinearMap.zero_apply]
  have h10 : inner ℂ (gourBitBasis (ULift.up (1 : Fin 2)))
      (gourBitBasis (ULift.up (0 : Fin 2))) = 0 := by
    simp
  rw [h10]
  simp

private lemma gourTrace_binaryPure_mul (i j : Fin 2) :
    Tr (gourBitPure.{u} i * gourBitPure j) = if i = j then 1 else 0 := by
  simp only [gourBitPure]
  rw [gourTrace_outerProduct_mul, QuantumChannel.outer_product_apply, inner_smul_right]
  by_cases hij : i = j
  · subst j
    have hii : inner ℂ (gourBitBasis.{u} (ULift.up i))
        (gourBitBasis (ULift.up i)) = 1 := by
      simp
    simp
  · have hij0 : inner ℂ (gourBitBasis.{u} (ULift.up i))
        (gourBitBasis (ULift.up j)) = 0 := by
      simp [hij]
    simp [hij, hij0]

private lemma gourTrace_pureZero_mul_binaryState (p : ℝ≥0) :
    Tr (gourBinaryPair.{u}.pure₀ * gourBinaryState p) = (p : ℂ) := by
  rw [gourBinaryState, mul_add, mul_smul_comm, mul_smul_comm,
    map_add, map_smul, map_smul, gourBinaryPair.pure₀_idempotent,
    gourBinaryPair.orthogonal, gourBinaryPair.pure₀_density.2, map_zero]
  simp

private lemma gourTrace_pureOne_mul_binaryState (p : ℝ≥0) :
    Tr (gourBinaryPair.{u}.pure₁ * gourBinaryState p) =
      (((1 - p : ℝ≥0) : ℝ) : ℂ) := by
  rw [gourBinaryState, mul_add, mul_smul_comm, mul_smul_comm,
    map_add, map_smul, map_smul, gourBinaryPure_one_mul_zero,
    gourBinaryPair.pure₁_idempotent, map_zero,
    gourBinaryPair.pure₁_density.2]
  simp

private lemma gourBinaryEffects_nonneg (i : Fin 2) :
    0 ≤ ![gourBinaryPair.{u}.pure₀, gourBinaryPair.pure₁] i := by
  fin_cases i
  · exact (LinearMap.nonneg_iff_isPositive _).mpr
      gourBinaryPair.pure₀_density.1
  · exact (LinearMap.nonneg_iff_isPositive _).mpr
      gourBinaryPair.pure₁_density.1

private lemma gourBinaryEffects_sum :
    ∑ i, ![gourBinaryPair.{u}.pure₀, gourBinaryPair.pure₁] i = 1 := by
  simpa [Fin.sum_univ_two] using gourBinaryPair.resolution

/-- Prepare one of two density operators after measuring the standard bit. -/
private noncomputable def gourBinaryPreparationChannel
    {H : Type u} [Qudit H]
    (tau₀ tau₁ : L H) (htau₀ : IsDensity tau₀) (htau₁ : IsDensity tau₁) :
    CPTP GourBit.{u} H :=
  gourMeasurePrepareChannel
    ![gourBinaryPair.pure₀, gourBinaryPair.pure₁] ![tau₀, tau₁]
    gourBinaryEffects_nonneg gourBinaryEffects_sum (by
      intro i
      fin_cases i
      · exact htau₀
      · exact htau₁)

private lemma gourBinaryPreparationChannel_apply_pureZero
    {H : Type u} [Qudit H]
    (tau₀ tau₁ : L H) (htau₀ : IsDensity tau₀) (htau₁ : IsDensity tau₁) :
    (gourBinaryPreparationChannel tau₀ tau₁ htau₀ htau₁).toFun
        gourBinaryPair.pure₀ = tau₀ := by
  rw [gourBinaryPreparationChannel, gourMeasurePrepareChannel_apply]
  simp only [Fin.sum_univ_two]
  change Tr (gourBitPure 0 * gourBitPure 0) • tau₀ +
    Tr (gourBitPure 1 * gourBitPure 0) • tau₁ = tau₀
  rw [gourTrace_binaryPure_mul, gourTrace_binaryPure_mul]
  simp

private lemma gourBinaryPreparationChannel_apply_binaryState
    {H : Type u} [Qudit H]
    (tau₀ tau₁ : L H) (htau₀ : IsDensity tau₀) (htau₁ : IsDensity tau₁)
    (p : ℝ≥0) :
    (gourBinaryPreparationChannel tau₀ tau₁ htau₀ htau₁).toFun
        (gourBinaryState p) =
      ((p : ℝ) : ℂ) • tau₀ +
        (((1 - p : ℝ≥0) : ℝ) : ℂ) • tau₁ := by
  rw [gourBinaryPreparationChannel, gourMeasurePrepareChannel_apply]
  simp [Fin.sum_univ_two, gourTrace_pureZero_mul_binaryState,
    gourTrace_pureOne_mul_binaryState]

private noncomputable def gourBitTensorPure (i j : Fin 2) :
    L (GourBit.{u} ⊗[ℂ] GourBit.{u}) :=
  TensorProduct.map (gourBitPure i) (gourBitPure j)

private lemma gourBitTensorPure_density (i j : Fin 2) :
    IsDensity (gourBitTensorPure.{u} i j) :=
  isDensity_tensorProduct (gourBitPure i) (gourBitPure j)
    (gourBitPure_density i) (gourBitPure_density j)

private lemma gourBinaryTensor_expand
    (p q : ℝ≥0) (hp : p ≤ 1) (hq : q ≤ 1) :
    (TensorProduct.map (gourBinaryState p) (gourBinaryState q) :
      L (GourBit.{u} ⊗[ℂ] GourBit.{u})) =
      ((((p : ℝ) * (q : ℝ) : ℝ) : ℂ) • gourBitTensorPure 0 0) +
      ((((p : ℝ) * (1 - (q : ℝ)) : ℝ) : ℂ) • gourBitTensorPure 0 1) +
      ((((1 - (p : ℝ)) * (q : ℝ) : ℝ) : ℂ) • gourBitTensorPure 1 0) +
      ((((1 - (p : ℝ)) * (1 - (q : ℝ)) : ℝ) : ℂ) •
        gourBitTensorPure 1 1) := by
  have hpSub : ((((1 - p : ℝ≥0) : ℝ) : ℂ)) =
      ((1 - (p : ℝ) : ℝ) : ℂ) := by
    push_cast [NNReal.coe_sub hp]
    rfl
  have hqSub : ((((1 - q : ℝ≥0) : ℝ) : ℂ)) =
      ((1 - (q : ℝ) : ℝ) : ℂ) := by
    push_cast [NNReal.coe_sub hq]
    rfl
  rw [gourBinaryState, gourBinaryState, hpSub, hqSub]
  simp only [TensorProduct.map_add_left, TensorProduct.map_add_right,
    TensorProduct.map_smul_left, TensorProduct.map_smul_right,
    gourBinaryPair, gourBitTensorPure]
  push_cast
  module

private noncomputable def gourSplitResidual (p q : ℝ≥0) :
    L (GourBit.{u} ⊗[ℂ] GourBit.{u}) :=
  let d : ℝ := 1 - (p : ℝ) * (q : ℝ)
  ((((p : ℝ) * (1 - (q : ℝ)) / d : ℝ) : ℂ) • gourBitTensorPure 0 1) +
  ((((1 - (p : ℝ)) * (q : ℝ) / d : ℝ) : ℂ) • gourBitTensorPure 1 0) +
  ((((1 - (p : ℝ)) * (1 - (q : ℝ)) / d : ℝ) : ℂ) •
    gourBitTensorPure 1 1)

private lemma gourSplitResidual_density
    (p q : ℝ≥0) (hp : p ≤ 1) (hq : q ≤ 1) (hpq : p * q ≠ 1) :
    IsDensity (gourSplitResidual.{u} p q) := by
  have hpR : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hqR : (q : ℝ) ≤ 1 := by exact_mod_cast hq
  have hpqLe : p * q ≤ 1 := by
    exact mul_le_one₀ hp q.property hq
  have hpqLt : p * q < 1 := lt_of_le_of_ne hpqLe hpq
  have hd : 0 < 1 - (p : ℝ) * (q : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hpqLt)
  have ha : 0 ≤ (p : ℝ) * (1 - (q : ℝ)) /
      (1 - (p : ℝ) * (q : ℝ)) :=
    div_nonneg (mul_nonneg p.property (sub_nonneg.mpr hqR)) hd.le
  have hb : 0 ≤ (1 - (p : ℝ)) * (q : ℝ) /
      (1 - (p : ℝ) * (q : ℝ)) :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hpR) q.property) hd.le
  have hc : 0 ≤ (1 - (p : ℝ)) * (1 - (q : ℝ)) /
      (1 - (p : ℝ) * (q : ℝ)) :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hpR) (sub_nonneg.mpr hqR)) hd.le
  constructor
  · unfold gourSplitResidual
    exact (((gourBitTensorPure_density 0 1).1.smul_of_nonneg
      (Complex.zero_le_real.mpr ha)).add
      ((gourBitTensorPure_density 1 0).1.smul_of_nonneg
        (Complex.zero_le_real.mpr hb))).add
      ((gourBitTensorPure_density 1 1).1.smul_of_nonneg
        (Complex.zero_le_real.mpr hc))
  · unfold gourSplitResidual
    rw [map_add, map_add, map_smul, map_smul, map_smul,
      (gourBitTensorPure_density 0 1).2,
      (gourBitTensorPure_density 1 0).2,
      (gourBitTensorPure_density 1 1).2]
    simp only [smul_eq_mul, mul_one]
    norm_cast
    field_simp [ne_of_gt hd]
    ring
    push_cast
    rfl

private lemma gourSplitResidual_mixture
    (p q : ℝ≥0) (hp : p ≤ 1) (hq : q ≤ 1) (hpq : p * q ≠ 1) :
    ((((p : ℝ) * (q : ℝ) : ℝ) : ℂ) • gourBitTensorPure.{u} 0 0) +
      (((1 - (p : ℝ) * (q : ℝ) : ℝ) : ℂ) • gourSplitResidual p q) =
    TensorProduct.map (gourBinaryState p) (gourBinaryState q) := by
  rw [gourBinaryTensor_expand p q hp hq]
  unfold gourSplitResidual
  have hpR : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hqR : (q : ℝ) ≤ 1 := by exact_mod_cast hq
  have hpqLe : p * q ≤ 1 := mul_le_one₀ hp q.property hq
  have hpqLt : p * q < 1 := lt_of_le_of_ne hpqLe hpq
  have hd : 1 - (p : ℝ) * (q : ℝ) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (by exact_mod_cast hpqLt))
  have ha :
      (((1 - (p : ℝ) * (q : ℝ) : ℝ) : ℂ) *
        (((p : ℝ) * (1 - (q : ℝ)) /
          (1 - (p : ℝ) * (q : ℝ)) : ℝ) : ℂ)) =
        (((p : ℝ) * (1 - (q : ℝ)) : ℝ) : ℂ) := by
    norm_cast
    field_simp [hd]
  have hb :
      (((1 - (p : ℝ) * (q : ℝ) : ℝ) : ℂ) *
        (((1 - (p : ℝ)) * (q : ℝ) /
          (1 - (p : ℝ) * (q : ℝ)) : ℝ) : ℂ)) =
        ((((1 - (p : ℝ)) * (q : ℝ)) : ℝ) : ℂ) := by
    norm_cast
    field_simp [hd]
  have hc :
      (((1 - (p : ℝ) * (q : ℝ) : ℝ) : ℂ) *
        (((1 - (p : ℝ)) * (1 - (q : ℝ)) /
          (1 - (p : ℝ) * (q : ℝ)) : ℝ) : ℂ)) =
        ((((1 - (p : ℝ)) * (1 - (q : ℝ))) : ℝ) : ℂ) := by
    norm_cast
    field_simp [hd]
  simp only [smul_add, smul_smul]
  rw [ha, hb, hc]
  module

private lemma gourBitTensorPure_zeroZero_starProjection :
    IsStarProjection (gourBitTensorPure.{u} 0 0) := by
  apply isStarProjection_iff'.2
  constructor
  · unfold gourBitTensorPure
    rw [← TensorProduct.map_mul]
    rw [gourBitPure_idempotent]
  · unfold gourBitTensorPure
    exact (gourBitTensorPure_density 0 0).1.isSelfAdjoint.star_eq

private lemma gourMultiplyEffects_nonneg (i : Fin 2) :
    0 ≤ ![gourBitTensorPure.{u} 0 0, 1 - gourBitTensorPure 0 0] i := by
  fin_cases i
  · exact gourBitTensorPure_zeroZero_starProjection.{u}.nonneg
  · exact gourBitTensorPure_zeroZero_starProjection.{u}.one_sub_nonneg

private lemma gourMultiplyEffects_sum :
    ∑ i, ![gourBitTensorPure.{u} 0 0, 1 - gourBitTensorPure 0 0] i = 1 := by
  simp [Fin.sum_univ_two]

private noncomputable def gourBinaryMultiplyChannel :
    CPTP (GourBit.{u} ⊗[ℂ] GourBit.{u}) GourBit.{u} :=
  gourMeasurePrepareChannel
    ![gourBitTensorPure 0 0, 1 - gourBitTensorPure 0 0]
    ![gourBinaryPair.pure₀, gourBinaryPair.pure₁]
    gourMultiplyEffects_nonneg gourMultiplyEffects_sum (by
      intro i
      fin_cases i
      · exact gourBinaryPair.pure₀_density
      · exact gourBinaryPair.pure₁_density)

private lemma gourBinaryMultiplyChannel_apply_pure :
    gourBinaryMultiplyChannel.{u}.toFun (gourBitTensorPure 0 0) =
      gourBinaryPair.pure₀ := by
  rw [gourBinaryMultiplyChannel, gourMeasurePrepareChannel_apply]
  simp only [Fin.sum_univ_two]
  have h00 := gourBitTensorPure_zeroZero_starProjection.{u}
  change Tr (gourBitTensorPure 0 0 * gourBitTensorPure 0 0) •
      gourBinaryPair.pure₀ +
    Tr ((1 - gourBitTensorPure 0 0) * gourBitTensorPure 0 0) •
      gourBinaryPair.pure₁ = gourBinaryPair.pure₀
  rw [h00.isIdempotentElem, h00.one_sub_mul_self, map_zero,
    (gourBitTensorPure_density.{u} 0 0).2]
  simp

private lemma gourTrace_zeroZero_mul_binaryTensor
    (p q : ℝ≥0) :
    Tr (gourBitTensorPure.{u} 0 0 *
      TensorProduct.map (gourBinaryState p) (gourBinaryState q)) =
      (((p : ℝ) * (q : ℝ) : ℝ) : ℂ) := by
  letI : Module.Finite ℂ GourBit.{u} :=
    Module.Finite.of_basis gourBitBasis.toBasis
  unfold gourBitTensorPure
  rw [← TensorProduct.map_mul (gourBitPure 0) (gourBinaryState p)
      (gourBitPure 0) (gourBinaryState q),
    LinearMap.trace_tensorProduct'
      (gourBitPure 0 * gourBinaryState p)
      (gourBitPure 0 * gourBinaryState q)]
  have hpTrace : Tr (gourBitPure 0 * gourBinaryState p) = (p : ℂ) := by
    change Tr (gourBinaryPair.pure₀ * gourBinaryState p) = (p : ℂ)
    exact gourTrace_pureZero_mul_binaryState p
  have hqTrace : Tr (gourBitPure 0 * gourBinaryState q) = (q : ℂ) := by
    change Tr (gourBinaryPair.pure₀ * gourBinaryState q) = (q : ℂ)
    exact gourTrace_pureZero_mul_binaryState q
  rw [hpTrace, hqTrace]
  push_cast
  rfl

private lemma gourBinaryMultiplyChannel_apply_binaryTensor
    (p q : ℝ≥0) (hp : p ≤ 1) (hq : q ≤ 1) :
    gourBinaryMultiplyChannel.{u}.toFun
        (TensorProduct.map (gourBinaryState p) (gourBinaryState q)) =
      gourBinaryState (p * q) := by
  rw [gourBinaryMultiplyChannel, gourMeasurePrepareChannel_apply]
  simp only [Fin.sum_univ_two]
  let X : L (GourBit.{u} ⊗[ℂ] GourBit.{u}) :=
    TensorProduct.map (gourBinaryState p) (gourBinaryState q)
  have hXtrace : Tr X = 1 :=
    (isDensity_tensorProduct (gourBinaryState p) (gourBinaryState q)
      (gourBinaryState_density p hp) (gourBinaryState_density q hq)).2
  have hfirst : Tr (gourBitTensorPure 0 0 * X) =
      (((p : ℝ) * (q : ℝ) : ℝ) : ℂ) :=
    gourTrace_zeroZero_mul_binaryTensor p q
  have hsecond : Tr ((1 - gourBitTensorPure 0 0) * X) =
      ((1 - (p : ℝ) * (q : ℝ) : ℝ) : ℂ) := by
    rw [sub_mul, one_mul, map_sub, hXtrace, hfirst]
    push_cast
    rfl
  change Tr (gourBitTensorPure 0 0 * X) • gourBinaryPair.pure₀ +
      Tr ((1 - gourBitTensorPure 0 0) * X) • gourBinaryPair.pure₁ =
    gourBinaryState (p * q)
  rw [hfirst, hsecond, gourBinaryState]
  have hpqLe : p * q ≤ 1 := mul_le_one₀ hp q.property hq
  push_cast [NNReal.coe_sub hpqLe]
  rfl

private noncomputable def gourBinarySplitChannel
    (p q : ℝ≥0) (hp : p ≤ 1) (hq : q ≤ 1) :
    CPTP GourBit.{u} (GourBit.{u} ⊗[ℂ] GourBit.{u}) :=
  if hpq : p * q = 1 then
    gourBinaryPreparationChannel
      (gourBitTensorPure 0 0) (gourBitTensorPure 0 0)
      (gourBitTensorPure_density 0 0) (gourBitTensorPure_density 0 0)
  else
    gourBinaryPreparationChannel
      (gourBitTensorPure 0 0) (gourSplitResidual p q)
      (gourBitTensorPure_density 0 0)
      (gourSplitResidual_density p q hp hq hpq)

private lemma gourBinarySplitChannel_apply_pure
    (p q : ℝ≥0) (hp : p ≤ 1) (hq : q ≤ 1) :
    (gourBinarySplitChannel.{u} p q hp hq).toFun gourBinaryPair.pure₀ =
      gourBitTensorPure 0 0 := by
  rw [gourBinarySplitChannel]
  split_ifs with hpq
  · exact gourBinaryPreparationChannel_apply_pureZero _ _ _ _
  · exact gourBinaryPreparationChannel_apply_pureZero _ _ _ _

private lemma gourEq_one_of_mul_eq_one
    (p q : ℝ≥0) (hp : p ≤ 1) (hq : q ≤ 1) (hpq : p * q = 1) :
    p = 1 ∧ q = 1 := by
  have hpR : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hqR : (q : ℝ) ≤ 1 := by exact_mod_cast hq
  have hpqR : (p : ℝ) * (q : ℝ) = 1 := by exact_mod_cast hpq
  constructor
  · apply le_antisymm hp
    apply le_of_not_gt
    intro hpLt
    have hlt : p * q < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left (show (0 : ℝ≥0) ≤ p from bot_le)
        hpLt hq
    rw [hpq] at hlt
    exact lt_irrefl 1 hlt
  · apply le_antisymm hq
    apply le_of_not_gt
    intro hqLt
    have hlt : p * q < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_right hp
        (show (0 : ℝ≥0) ≤ q from bot_le) hqLt
    rw [hpq] at hlt
    exact lt_irrefl 1 hlt

private lemma gourBinarySplitChannel_apply_binaryState
    (p q : ℝ≥0) (hp : p ≤ 1) (hq : q ≤ 1) :
    (gourBinarySplitChannel.{u} p q hp hq).toFun (gourBinaryState (p * q)) =
      TensorProduct.map (gourBinaryState p) (gourBinaryState q) := by
  rw [gourBinarySplitChannel]
  split_ifs with hpq
  · obtain ⟨rfl, rfl⟩ := gourEq_one_of_mul_eq_one p q hp hq hpq
    rw [gourBinaryPreparationChannel_apply_binaryState]
    simp [gourBitTensorPure, gourBinaryPair]
  · rw [gourBinaryPreparationChannel_apply_binaryState]
    have hpqLe : p * q ≤ 1 := mul_le_one₀ hp q.property hq
    rw [show (((p * q : ℝ≥0) : ℝ) : ℂ) =
        (((p : ℝ) * (q : ℝ) : ℝ) : ℂ) by push_cast; rfl]
    rw [show ((((1 - p * q : ℝ≥0) : ℝ) : ℂ)) =
        ((1 - (p : ℝ) * (q : ℝ) : ℝ) : ℂ) by
      push_cast [NNReal.coe_sub hpqLe]; rfl]
    exact gourSplitResidual_mixture p q hp hq hpq

private noncomputable def gourWidenProbability (p q : ℝ≥0) : ℝ≥0 :=
  (q - p) / (1 - p)

private lemma gourWidenProbability_le_one
    (p q : ℝ≥0) (hp : p ≤ q) (hq : q ≤ 1) (hp1 : p ≠ 1) :
    gourWidenProbability p q ≤ 1 := by
  unfold gourWidenProbability
  have hpLt : p < 1 := lt_of_le_of_ne (hp.trans hq) hp1
  apply NNReal.coe_le_coe.mp
  rw [NNReal.coe_div, NNReal.coe_one, NNReal.coe_sub hp,
    NNReal.coe_sub (hp.trans hq)]
  exact (div_le_one (sub_pos.mpr (by exact_mod_cast hpLt))).2
    (sub_le_sub_right (by exact_mod_cast hq) (p : ℝ))

private noncomputable def gourBinaryWidenChannel
    (p q : ℝ≥0) (hp : p ≤ q) (hq : q ≤ 1) :
    CPTP GourBit.{u} GourBit.{u} :=
  if hp1 : p = 1 then
    gourBinaryPreparationChannel gourBinaryPair.pure₀ gourBinaryPair.pure₀
      gourBinaryPair.pure₀_density gourBinaryPair.pure₀_density
  else
    gourBinaryPreparationChannel gourBinaryPair.pure₀
      (gourBinaryState (gourWidenProbability p q))
      gourBinaryPair.pure₀_density
      (gourBinaryState_density _
        (gourWidenProbability_le_one p q hp hq hp1))

private lemma gourBinaryWidenChannel_apply_pure
    (p q : ℝ≥0) (hp : p ≤ q) (hq : q ≤ 1) :
    (gourBinaryWidenChannel.{u} p q hp hq).toFun gourBinaryPair.pure₀ =
      gourBinaryPair.pure₀ := by
  rw [gourBinaryWidenChannel]
  split_ifs
  · exact gourBinaryPreparationChannel_apply_pureZero _ _ _ _
  · exact gourBinaryPreparationChannel_apply_pureZero _ _ _ _

private lemma gourBinaryWidenChannel_apply_binaryState
    (p q : ℝ≥0) (hp : p ≤ q) (hq : q ≤ 1) :
    (gourBinaryWidenChannel.{u} p q hp hq).toFun (gourBinaryState p) =
      gourBinaryState q := by
  rw [gourBinaryWidenChannel]
  split_ifs with hp1
  · have hq1 : q = 1 := le_antisymm hq (hp1 ▸ hp)
    subst p
    subst q
    rw [gourBinaryPreparationChannel_apply_binaryState]
    simp
  · rw [gourBinaryPreparationChannel_apply_binaryState]
    have hpLt : p < 1 := lt_of_le_of_ne (hp.trans hq) hp1
    have hden : (1 : ℝ) - (p : ℝ) ≠ 0 := by
      exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hpLt))
    have hrLe : gourWidenProbability p q ≤ 1 :=
      gourWidenProbability_le_one p q hp hq hp1
    have hrLe' : (q - p) / (1 - p) ≤ 1 := by
      simpa [gourWidenProbability] using hrLe
    rw [gourBinaryState, gourBinaryState, gourWidenProbability]
    simp only [smul_add, smul_smul]
    push_cast [NNReal.coe_sub hp, NNReal.coe_sub hq,
      NNReal.coe_sub (hp.trans hq), NNReal.coe_sub hrLe', NNReal.coe_div]
    have hdenC : (1 : ℂ) - (((p : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast hden
    have hzero :
        (((p : ℝ) : ℂ) +
          (1 - (((p : ℝ) : ℂ))) *
            ((((q : ℝ) : ℂ) - ((p : ℝ) : ℂ)) /
              (1 - ((p : ℝ) : ℂ)))) =
          ((q : ℝ) : ℂ) := by
      field_simp [hdenC]
      ring
    have hone :
        (1 - (((p : ℝ) : ℂ))) *
          (1 - ((((q : ℝ) : ℂ) - ((p : ℝ) : ℂ)) /
            (1 - ((p : ℝ) : ℂ)))) =
          (1 - ((q : ℝ) : ℂ)) := by
      field_simp [hdenC]
      ring
    rw [← add_assoc, ← add_smul, hzero, hone]

private lemma gourBinary_value
    {D : GourMatrixStateDivergence.{u}}
    (laws : GourMatrixRelativeEntropyLaws.{u} D)
    (p : ℝ≥0) (hp : p ≤ 1) :
    D gourBinaryPair.pure₀ (gourBinaryState p)
        gourBinaryPair.pure₀_density (gourBinaryState_density p hp) =
      binaryNegLog2 p := by
  let f : ℝ≥0 → EReal := fun q =>
    if hq : q ≤ 1 then
      D gourBinaryPair.pure₀ (gourBinaryState q)
        gourBinaryPair.pure₀_density (gourBinaryState_density q hq)
    else 0
  have hf (q : ℝ≥0) (hq : q ≤ 1) :
      f q = D gourBinaryPair.pure₀ (gourBinaryState q)
        gourBinaryPair.pure₀_density (gourBinaryState_density q hq) := by
    simp only [f, dif_pos hq]
  rw [← hf p hp]
  apply binaryCalibration_eq_negLog2 f
  · intro q r hq hr
    rw [hf (q * r) (mul_le_one₀ hq r.property hr), hf q hq, hf r hr]
    have hforward := laws.dataProcessing gourBinaryMultiplyChannel
      (gourBitTensorPure 0 0)
      (TensorProduct.map (gourBinaryState q) (gourBinaryState r))
      (gourBitTensorPure_density 0 0)
      (isDensity_tensorProduct (gourBinaryState q) (gourBinaryState r)
        (gourBinaryState_density q hq) (gourBinaryState_density r hr))
    have hforward' :
        D gourBinaryPair.pure₀ (gourBinaryState (q * r))
            gourBinaryPair.pure₀_density
            (gourBinaryState_density (q * r)
              (mul_le_one₀ hq r.property hr)) ≤
          D (gourBitTensorPure 0 0)
            (TensorProduct.map (gourBinaryState q) (gourBinaryState r))
            (gourBitTensorPure_density 0 0)
            (isDensity_tensorProduct (gourBinaryState q) (gourBinaryState r)
              (gourBinaryState_density q hq) (gourBinaryState_density r hr)) := by
      simpa only [gourBinaryMultiplyChannel_apply_pure,
        gourBinaryMultiplyChannel_apply_binaryTensor q r hq hr] using hforward
    have hbackward := laws.dataProcessing (gourBinarySplitChannel q r hq hr)
      gourBinaryPair.pure₀ (gourBinaryState (q * r))
      gourBinaryPair.pure₀_density
      (gourBinaryState_density (q * r) (mul_le_one₀ hq r.property hr))
    have hbackward' :
        D (gourBitTensorPure 0 0)
            (TensorProduct.map (gourBinaryState q) (gourBinaryState r))
            (gourBitTensorPure_density 0 0)
            (isDensity_tensorProduct (gourBinaryState q) (gourBinaryState r)
              (gourBinaryState_density q hq) (gourBinaryState_density r hr)) ≤
          D gourBinaryPair.pure₀ (gourBinaryState (q * r))
            gourBinaryPair.pure₀_density
            (gourBinaryState_density (q * r)
              (mul_le_one₀ hq r.property hr)) := by
      simpa only [gourBinarySplitChannel_apply_pure,
        gourBinarySplitChannel_apply_binaryState] using hbackward
    calc
      D gourBinaryPair.pure₀ (gourBinaryState (q * r))
          gourBinaryPair.pure₀_density
          (gourBinaryState_density (q * r) (mul_le_one₀ hq r.property hr)) =
        D (gourBitTensorPure 0 0)
          (TensorProduct.map (gourBinaryState q) (gourBinaryState r))
          (gourBitTensorPure_density 0 0)
          (isDensity_tensorProduct (gourBinaryState q) (gourBinaryState r)
            (gourBinaryState_density q hq) (gourBinaryState_density r hr)) :=
        le_antisymm hforward' hbackward'
      _ = D gourBinaryPair.pure₀ (gourBinaryState q)
            gourBinaryPair.pure₀_density (gourBinaryState_density q hq) +
          D gourBinaryPair.pure₀ (gourBinaryState r)
            gourBinaryPair.pure₀_density (gourBinaryState_density r hr) := by
        exact laws.tensorAdditivity gourBinaryPair.pure₀ (gourBinaryState q)
          gourBinaryPair.pure₀ (gourBinaryState r)
          gourBinaryPair.pure₀_density (gourBinaryState_density q hq)
          gourBinaryPair.pure₀_density (gourBinaryState_density r hr)
  · intro q hq r hr hqr
    rw [hf q hq.2, hf r hr.2]
    have h := laws.dataProcessing (gourBinaryWidenChannel q r hqr hr.2)
      gourBinaryPair.pure₀ (gourBinaryState q)
      gourBinaryPair.pure₀_density (gourBinaryState_density q hq.2)
    simpa only [gourBinaryWidenChannel_apply_pure,
      gourBinaryWidenChannel_apply_binaryState] using h
  · rw [hf ((2 : ℝ≥0)⁻¹) (by norm_num)]
    simpa only [gourBinaryState_half] using
      laws.binaryNormalization gourBinaryPair
  · exact hp

/-! ## Support measurement and domination preparation -/

private lemma gourTraceMul_im_eq_zero_of_nonneg
    {H : Type u} [Qudit H] {X Y : L H} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    (Tr (X * Y)).im = 0 := by
  have hsx : IsSelfAdjoint (CFC.sqrt X) :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg X)
  have hsy : IsSelfAdjoint (CFC.sqrt Y) :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg Y)
  have htrace : Tr (star (CFC.sqrt X * CFC.sqrt Y) *
      (CFC.sqrt X * CFC.sqrt Y)) = Tr (X * Y) := by
    calc
      Tr (star (CFC.sqrt X * CFC.sqrt Y) *
          (CFC.sqrt X * CFC.sqrt Y)) =
          Tr ((CFC.sqrt Y * CFC.sqrt X) *
            (CFC.sqrt X * CFC.sqrt Y)) := by
        rw [star_mul, hsx.star_eq, hsy.star_eq]
      _ = Tr (CFC.sqrt Y *
          ((CFC.sqrt X * CFC.sqrt X) * CFC.sqrt Y)) := by
        simp only [mul_assoc]
      _ = Tr (CFC.sqrt Y * (X * CFC.sqrt Y)) := by
        rw [CFC.sqrt_mul_sqrt_self X hX]
      _ = Tr ((X * CFC.sqrt Y) * CFC.sqrt Y) :=
        LinearMap.trace_mul_comm ℂ (CFC.sqrt Y) (X * CFC.sqrt Y)
      _ = Tr (X * (CFC.sqrt Y * CFC.sqrt Y)) := by rw [mul_assoc]
      _ = Tr (X * Y) := by rw [CFC.sqrt_mul_sqrt_self Y hY]
  have hnonneg :
      0 ≤ Tr (star (CFC.sqrt X * CFC.sqrt Y) *
        (CFC.sqrt X * CFC.sqrt Y)) :=
    ((LinearMap.nonneg_iff_isPositive _).mp
      (star_mul_self_nonneg (CFC.sqrt X * CFC.sqrt Y))).trace_nonneg
  have him : (Tr (star (CFC.sqrt X * CFC.sqrt Y) *
      (CFC.sqrt X * CFC.sqrt Y))).im = 0 :=
    (Complex.nonneg_iff.mp hnonneg).2.symm
  rwa [htrace] at him

private theorem gourClassicalSupportOverlap_ne_top
    {ι : Type} [Fintype ι] (p q : PMF ι) :
    classicalSupportOverlapPMF p q ≠ ⊤ := by
  classical
  unfold classicalSupportOverlapPMF
  rw [ENNReal.sum_ne_top]
  intro i _
  split_ifs <;> simp [q.apply_ne_top]

private theorem gourClassicalSupportOverlap_le_one
    {ι : Type} [Fintype ι] (p q : PMF ι) :
    classicalSupportOverlapPMF p q ≤ 1 := by
  classical
  have hsum : ∑ i, q i = 1 := by
    simpa only [tsum_fintype] using q.tsum_coe
  unfold classicalSupportOverlapPMF
  calc
    (∑ i, if i ∈ p.support then q i else 0) ≤ ∑ i, q i := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> simp
    _ = 1 := hsum

private lemma gourDominationExponent_nonneg
    {H : Type u} [Qudit H] [Nontrivial H]
    {rho sigma : L H} (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    {lam : ℝ} (hdom : rho ≤ (((2 : ℝ) ^ lam : ℝ) : ℂ) • sigma) :
    0 ≤ lam := by
  have hdiff : 0 ≤
      (((2 : ℝ) ^ lam : ℝ) : ℂ) • sigma - rho :=
    sub_nonneg.mpr hdom
  have htrace := ((LinearMap.nonneg_iff_isPositive _).mp hdiff).trace_nonneg
  have hre := (Complex.nonneg_iff.mp htrace).1
  rw [map_sub, map_smul, hsigma.2, hrho.2, smul_eq_mul, mul_one,
    Complex.sub_re, Complex.ofReal_re, Complex.one_re] at hre
  by_contra hlam
  have hlamNeg : lam < 0 := lt_of_not_ge hlam
  have hpowLt : (2 : ℝ) ^ lam < 1 := by
    simpa only [Real.rpow_zero] using
      ((Real.strictMono_rpow_of_base_gt_one (b := 2) (by norm_num)).lt_iff_lt.mpr
        hlamNeg)
  linarith

private noncomputable def gourSupportProbability
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma) : ℝ≥0 :=
  ⟨(classicalSupportOverlapPMF
      (petzSpectralP rho sigma hrho hsigma)
      (petzSpectralQ rho sigma hrho hsigma)).toReal,
    ENNReal.toReal_nonneg⟩

private lemma gourSupportProbability_le_one
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    gourSupportProbability rho sigma hrho hsigma ≤ 1 := by
  apply NNReal.coe_le_coe.mp
  change (classicalSupportOverlapPMF
      (petzSpectralP rho sigma hrho hsigma)
      (petzSpectralQ rho sigma hrho hsigma)).toReal ≤ 1
  rw [← ENNReal.toReal_one]
  exact (ENNReal.toReal_le_toReal
    (gourClassicalSupportOverlap_ne_top _ _) ENNReal.one_ne_top).2
      (gourClassicalSupportOverlap_le_one _ _)

private lemma gourSupportProbability_eq_tracePower
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    (gourSupportProbability rho sigma hrho hsigma : ℝ) =
      petzSupportTracePower 0 rho sigma := by
  exact classicalSupportOverlapPMF_petzSpectral_toReal_eq
    rho sigma hrho hsigma

private noncomputable def gourSupportMeasurementChannel
    {H : Type u} [Qudit H]
    (rho : L H) : CPTP H GourBit.{u} :=
  let P : L H := (LinearMap.range rho).starProjection.toLinearMap
  gourMeasurePrepareChannel ![P, 1 - P]
    ![gourBinaryPair.pure₀, gourBinaryPair.pure₁]
    (by
      intro i
      fin_cases i
      · change 0 ≤ P
        exact (LinearMap.nonneg_iff_isPositive _).mpr
          (Submodule.isSymmetricProjection_starProjection
            (LinearMap.range rho)).isPositive
      · change 0 ≤ 1 - P
        have hP := Submodule.isSymmetricProjection_starProjection
          (LinearMap.range rho)
        have hOne : (1 : L H).IsSymmetric := by
          exact LinearMap.IsSymmetric.id
        exact (LinearMap.nonneg_iff_isPositive _).mpr
          (⟨hP.isIdempotentElem.one_sub,
            hOne.sub hP.isSymmetric⟩ :
              (1 - P).IsSymmetricProjection).isPositive)
    (by simp [Fin.sum_univ_two])
    (by
      intro i
      fin_cases i
      · exact gourBinaryPair.pure₀_density
      · exact gourBinaryPair.pure₁_density)

private lemma gourSupportProjection_mul_self
    {H : Type u} [Qudit H] (rho : L H) :
    (LinearMap.range rho).starProjection.toLinearMap * rho = rho := by
  ext x
  change (LinearMap.range rho).starProjection (rho x) = rho x
  exact Submodule.starProjection_eq_self_iff.mpr ⟨x, rfl⟩

private lemma gourSupportMeasurementChannel_apply_left
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho : L H) (hrho : IsDensity rho) :
    (gourSupportMeasurementChannel rho).toFun rho =
      gourBinaryPair.pure₀ := by
  rw [gourSupportMeasurementChannel, gourMeasurePrepareChannel_apply]
  simp only [Fin.sum_univ_two]
  let P : L H := (LinearMap.range rho).starProjection.toLinearMap
  have hPrho : P * rho = rho := gourSupportProjection_mul_self rho
  have hcomp : (1 - P) * rho = 0 := by
    rw [sub_mul, one_mul, hPrho, sub_self]
  change Tr (P * rho) • gourBinaryPair.pure₀ +
      Tr ((1 - P) * rho) • gourBinaryPair.pure₁ = _
  rw [hPrho, hcomp, hrho.2, map_zero]
  simp

private lemma gourSupportMeasurementChannel_apply_right
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    (gourSupportMeasurementChannel rho).toFun sigma =
      gourBinaryState (gourSupportProbability rho sigma hrho hsigma) := by
  rw [gourSupportMeasurementChannel, gourMeasurePrepareChannel_apply]
  simp only [Fin.sum_univ_two]
  let P : L H := (LinearMap.range rho).starProjection.toLinearMap
  let p := gourSupportProbability rho sigma hrho hsigma
  have hPnonneg : 0 ≤ P :=
    (LinearMap.nonneg_iff_isPositive _).mpr
      (Submodule.isSymmetricProjection_starProjection
        (LinearMap.range rho)).isPositive
  have hsigmaNonneg : 0 ≤ sigma :=
    (LinearMap.nonneg_iff_isPositive _).mpr hsigma.1
  have hreal : (Tr (P * sigma)).re = (p : ℝ) := by
    rw [gourSupportProbability_eq_tracePower]
    unfold petzSupportTracePower
    rw [petzSupportRpow_zero, show 1 - (0 : ℝ) = 1 by norm_num,
      petzSupportRpow_of_ne_zero sigma one_ne_zero]
    have hsigmaRpow : CFC.rpow sigma 1 = sigma :=
      CFC.rpow_one sigma hsigmaNonneg
    rw [hsigmaRpow]
  have him : (Tr (P * sigma)).im = 0 :=
    gourTraceMul_im_eq_zero_of_nonneg hPnonneg hsigmaNonneg
  have hfirst : Tr (P * sigma) = ((p : ℝ) : ℂ) := by
    apply Complex.ext
    · simpa using hreal
    · simpa using him
  have hsecond : Tr ((1 - P) * sigma) =
      (((1 - p : ℝ≥0) : ℝ) : ℂ) := by
    rw [sub_mul, one_mul, map_sub, hsigma.2, hfirst]
    have hpLe : p ≤ 1 := gourSupportProbability_le_one
      rho sigma hrho hsigma
    norm_cast
    exact (NNReal.coe_sub hpLe).symm
  change Tr (P * sigma) • gourBinaryPair.pure₀ +
      Tr ((1 - P) * sigma) • gourBinaryPair.pure₁ = _
  rw [hfirst, hsecond]
  rfl

private lemma gourQuantumMin_eq_binaryValue
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    quantumMinRelativeEntropy rho sigma hrho hsigma =
      binaryNegLog2 (gourSupportProbability rho sigma hrho hsigma) := by
  unfold quantumMinRelativeEntropy binaryNegLog2
  by_cases hmul : rho * sigma = 0
  · have htrace : petzSupportTracePower 0 rho sigma = 0 :=
      (petzSupportTracePower_zero_eq_zero_iff_mul_eq_zero
        rho sigma hrho hsigma).2 hmul
    have hp : gourSupportProbability rho sigma hrho hsigma = 0 := by
      apply NNReal.eq
      rw [gourSupportProbability_eq_tracePower, htrace]
      rfl
    simp [hmul, hp]
  · have htrace : petzSupportTracePower 0 rho sigma ≠ 0 := fun hzero =>
      hmul ((petzSupportTracePower_zero_eq_zero_iff_mul_eq_zero
        rho sigma hrho hsigma).1 hzero)
    have hp : gourSupportProbability rho sigma hrho hsigma ≠ 0 := by
      intro hp
      apply htrace
      rw [← gourSupportProbability_eq_tracePower rho sigma hrho hsigma, hp]
      rfl
    simp only [if_neg hmul, if_neg hp]
    rw [← gourSupportProbability_eq_tracePower rho sigma hrho hsigma]

private noncomputable def gourDominationResidual
    {H : Type u} [Qudit H] (rho sigma : L H) (t : ℝ) : L H :=
  (((t - 1)⁻¹ : ℝ) : ℂ) • ((((t : ℝ) : ℂ) • sigma) - rho)

private lemma gourDominationResidual_density
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (t : ℝ) (ht : 1 < t)
    (hdom : rho ≤ (((t : ℝ) : ℂ) • sigma)) :
    IsDensity (gourDominationResidual rho sigma t) := by
  have hdiff : 0 ≤ (((t : ℝ) : ℂ) • sigma) - rho :=
    sub_nonneg.mpr hdom
  constructor
  · exact ((LinearMap.nonneg_iff_isPositive _).mp hdiff).smul_of_nonneg
      (Complex.zero_le_real.mpr (inv_nonneg.mpr (sub_nonneg.mpr ht.le)))
  · unfold gourDominationResidual
    rw [map_smul, map_sub, map_smul, hsigma.2, hrho.2,
      smul_eq_mul, smul_eq_mul, mul_one]
    norm_cast
    field_simp [ne_of_gt (sub_pos.mpr ht)]

private lemma gourDominationResidual_mixture
    {H : Type u} [Qudit H]
    (rho sigma : L H) (t : ℝ) (ht : 1 < t) :
    (((t⁻¹ : ℝ) : ℂ) • rho) +
        (((1 - t⁻¹ : ℝ) : ℂ) • gourDominationResidual rho sigma t) =
      sigma := by
  unfold gourDominationResidual
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have ht1 : t - 1 ≠ 0 := ne_of_gt (sub_pos.mpr ht)
  have hminus : -1 + t ≠ 0 := by linarith
  have hcoef : t⁻¹ + (t⁻¹ * (-1 + t)⁻¹ - (-1 + t)⁻¹) = 0 := by
    field_simp [ht0, ht1, hminus]
    ring
  have hcoefC := congrArg (fun x : ℝ => (x : ℂ)) hcoef
  push_cast at hcoefC
  have hsigmaCoef : (1 - t⁻¹) * ((t - 1)⁻¹ * t) = 1 := by
    field_simp [ht0, ht1]
  have hsigmaCoefC := congrArg (fun x : ℝ => (x : ℂ)) hsigmaCoef
  push_cast at hsigmaCoefC
  match_scalars
  · rw [show (t : ℂ) - 1 = -1 + (t : ℂ) by ring]
    ring_nf at hcoefC ⊢
    exact hcoefC
  · ring_nf at hsigmaCoefC ⊢
    exact hsigmaCoefC

private lemma gourUpperBound_of_domination
    {D : GourMatrixStateDivergence.{u}}
    (laws : GourMatrixRelativeEntropyLaws.{u} D)
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma)
    (lam : ℝ) (hdom : rho ≤ (((2 : ℝ) ^ lam : ℝ) : ℂ) • sigma) :
    D rho sigma hrho hsigma ≤ (lam : EReal) := by
  let t : ℝ := (2 : ℝ) ^ lam
  have hlam : 0 ≤ lam := gourDominationExponent_nonneg hrho hsigma hdom
  have htOne : 1 ≤ t := by
    simpa only [t, Real.rpow_zero] using
      (Real.strictMono_rpow_of_base_gt_one (b := 2) (by norm_num)).monotone
        hlam
  by_cases ht : t = 1
  · have hlamZero : lam = 0 := by
      apply (Real.strictMono_rpow_of_base_gt_one (b := 2) (by norm_num)).injective
      simpa [t] using ht
    have hrs : rho = sigma := IsDensity.eq_of_le hrho hsigma (by
      simpa [t, ht] using hdom)
    subst sigma
    have hdpi := laws.dataProcessing
      (gourBinaryPreparationChannel rho rho hrho hrho)
      gourBinaryPair.pure₀ (gourBinaryState 1)
      gourBinaryPair.pure₀_density (gourBinaryState_density 1 le_rfl)
    have hmapLeft :
        (gourBinaryPreparationChannel rho rho hrho hrho).toFun
          gourBinaryPair.pure₀ = rho :=
      gourBinaryPreparationChannel_apply_pureZero _ _ _ _
    have hmapRight :
        (gourBinaryPreparationChannel rho rho hrho hrho).toFun
          (gourBinaryState 1) = rho := by
      rw [gourBinaryState_one]
      exact hmapLeft
    have hle : D rho rho hrho hrho ≤
        D gourBinaryPair.pure₀ (gourBinaryState 1)
          gourBinaryPair.pure₀_density (gourBinaryState_density 1 le_rfl) := by
      simpa only [hmapLeft, hmapRight] using hdpi
    rw [gourBinary_value laws 1 le_rfl] at hle
    simpa [hlamZero, binaryNegLog2] using hle
  · have htLt : 1 < t := lt_of_le_of_ne htOne (Ne.symm ht)
    let tau := gourDominationResidual rho sigma t
    have htau : IsDensity tau :=
      gourDominationResidual_density rho sigma hrho hsigma t htLt (by
        simpa only [t] using hdom)
    let p := binaryExponentProbability lam
    have hpLe : p ≤ 1 := binaryExponentProbability_le_one hlam
    have hpEq : (p : ℝ) = t⁻¹ := by
      simp [p, t, binaryExponentProbability, NNReal.coe_rpow, Real.rpow_neg]
    have hdpi := laws.dataProcessing
      (gourBinaryPreparationChannel rho tau hrho htau)
      gourBinaryPair.pure₀ (gourBinaryState p)
      gourBinaryPair.pure₀_density (gourBinaryState_density p hpLe)
    have hmapRight :
        (gourBinaryPreparationChannel rho tau hrho htau).toFun
            (gourBinaryState p) = sigma := by
      rw [gourBinaryPreparationChannel_apply_binaryState]
      rw [show (((p : ℝ) : ℂ)) = ((t⁻¹ : ℝ) : ℂ) by rw [hpEq]]
      rw [show ((((1 - p : ℝ≥0) : ℝ) : ℂ)) =
          ((1 - t⁻¹ : ℝ) : ℂ) by
        norm_cast
        rw [NNReal.coe_sub hpLe, hpEq]
        norm_num]
      exact gourDominationResidual_mixture rho sigma t htLt
    have hmapLeft :
        (gourBinaryPreparationChannel rho tau hrho htau).toFun
          gourBinaryPair.pure₀ = rho :=
      gourBinaryPreparationChannel_apply_pureZero _ _ _ _
    have hle : D rho sigma hrho hsigma ≤
        D gourBinaryPair.pure₀ (gourBinaryState p)
          gourBinaryPair.pure₀_density (gourBinaryState_density p hpLe) := by
      simpa only [hmapLeft, hmapRight] using hdpi
    rw [gourBinary_value laws p hpLe,
      binaryNegLog2_binaryExponentProbability] at hle
    exact hle

theorem gourQuantumRelativeEntropy_min_max_bounds
    {D : GourMatrixStateDivergence.{u}}
    (laws : GourMatrixRelativeEntropyLaws.{u} D)
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : QuantumDensityMatrix H) :
    quantumMinRelativeEntropy rho.1 sigma.1 rho.2 sigma.2 ≤
        D rho.1 sigma.1 rho.2 sigma.2 ∧
      D rho.1 sigma.1 rho.2 sigma.2 ≤
        quantumMaxRelativeEntropyBits rho sigma := by
  rcases rho with ⟨rho, hrho⟩
  rcases sigma with ⟨sigma, hsigma⟩
  constructor
  · have hdpi := laws.dataProcessing
      (gourSupportMeasurementChannel rho) rho sigma hrho hsigma
    have hmapLeft := gourSupportMeasurementChannel_apply_left rho hrho
    have hmapRight :=
      gourSupportMeasurementChannel_apply_right rho sigma hrho hsigma
    have hle :
        D gourBinaryPair.pure₀
            (gourBinaryState (gourSupportProbability rho sigma hrho hsigma))
            gourBinaryPair.pure₀_density
            (gourBinaryState_density _
              (gourSupportProbability_le_one rho sigma hrho hsigma)) ≤
          D rho sigma hrho hsigma := by
      simpa only [hmapLeft, hmapRight] using hdpi
    rw [gourBinary_value laws _
      (gourSupportProbability_le_one rho sigma hrho hsigma)] at hle
    rwa [gourQuantumMin_eq_binaryValue rho sigma hrho hsigma]
  · unfold quantumMaxRelativeEntropyBits OrderedCone.maxRelEntropy
    apply le_sInf
    rintro z ⟨lam, rfl, hdom⟩
    exact gourUpperBound_of_domination laws rho sigma hrho hsigma lam (by
      simpa only [Complex.coe_smul] using hdom)

end

end OPT
