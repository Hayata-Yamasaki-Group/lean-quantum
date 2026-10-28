/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.StructuralCalculus.GSLCore
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Unit coordinates and the trace effect

This file identifies operators on the one-dimensional tensor unit with complex
scalars and supplies the trace bridges needed by the quantum OPT instances.
-/

noncomputable section

namespace QuantumModel

open CategoryTheory
open CategoryTheory.MonoidalCategory
open QuantumState
open scoped ComplexOrder

/-- The unique canonical coordinate of the tensor-unit Hilbert space. -/
def unitIndex : Fin tensorUnitSystem.dim :=
  ⟨0, tensorUnitSystem.dim_pos⟩

/-- The canonical unit vector of the tensor-unit Hilbert space. -/
def unitVector : Space tensorUnitSystem :=
  EuclideanSpace.basisFun (Fin tensorUnitSystem.dim) ℂ unitIndex

@[simp]
theorem norm_unitVector : ‖unitVector‖ = 1 := by
  simp [unitVector]

/-- The scalar coordinate of a unit operator is its sole matrix coefficient. -/
theorem operatorUnitEquiv_symm_eq_inner (X : Operator tensorUnitSystem) :
    operatorUnitEquiv.symm X = inner ℂ unitVector (X unitVector) := by
  change operatorEquivMatrix tensorUnitSystem X unitIndex unitIndex = _
  unfold operatorEquivMatrix
  rw [LinearMap.toMatrixOrthonormal_apply_apply]
  rfl

/-- Trace is exactly the scalar coordinate on the one-dimensional tensor unit. -/
theorem trace_unitOperator (X : Operator tensorUnitSystem) :
    Tr X = operatorUnitEquiv.symm X := by
  rw [LinearMap.trace_eq_sum_inner X
    (EuclideanSpace.basisFun (Fin tensorUnitSystem.dim) ℂ)]
  rw [operatorUnitEquiv_symm_eq_inner]
  change (∑ _i : Fin 1,
      inner ℂ ((EuclideanSpace.basisFun (Fin 1) ℂ) 0)
        (X ((EuclideanSpace.basisFun (Fin 1) ℂ) 0))) = _
  rw [Fin.sum_univ_one]
  rfl

@[simp]
theorem trace_operatorUnitEquiv (z : ℂ) :
    Tr (operatorUnitEquiv z) = z := by
  rw [trace_unitOperator]
  exact operatorUnitEquiv.symm_apply_apply z

/-- Every unit operator is its trace times the canonical unit operator. -/
theorem operatorUnitEquiv_trace (X : Operator tensorUnitSystem) :
    operatorUnitEquiv (Tr X) = X := by
  rw [trace_unitOperator]
  exact operatorUnitEquiv.apply_symm_apply X

@[simp]
theorem operatorUnitEquiv_one :
    operatorUnitEquiv 1 = (LinearMap.id : Operator tensorUnitSystem) := by
  apply operatorUnitEquiv.symm.injective
  rw [operatorUnitEquiv.symm_apply_apply]
  rw [operatorUnitEquiv_symm_eq_inner]
  simp [unitVector]

/-- Scalar coordinates act by scalar multiplication of the unit operator. -/
theorem operatorUnitEquiv_eq_smul_id (z : ℂ) :
    operatorUnitEquiv z = z • (LinearMap.id : Operator tensorUnitSystem) := by
  calc
    operatorUnitEquiv z = operatorUnitEquiv (z • 1) := by rw [smul_eq_mul, mul_one]
    _ = z • operatorUnitEquiv 1 := map_smul operatorUnitEquiv z 1
    _ = z • (LinearMap.id : Operator tensorUnitSystem) := by
      rw [operatorUnitEquiv_one]

/-- Real evaluation of a closed quantum scalar. -/
def quantumScalarEval :
    (tensorUnitSystem ⟶ tensorUnitSystem) →ₗ[ℝ] ℝ where
  toFun s := (Tr (HPHom.toRawSuperoperator s LinearMap.id)).re
  map_add' s t := by
    change (Tr ((HPHom.toRawSuperoperator s + HPHom.toRawSuperoperator t)
      LinearMap.id)).re =
      (Tr (HPHom.toRawSuperoperator s LinearMap.id)).re +
        (Tr (HPHom.toRawSuperoperator t LinearMap.id)).re
    rw [LinearMap.add_apply, map_add]
    rfl
  map_smul' r s := by
    change (Tr (((r : ℂ) • HPHom.toRawSuperoperator s) LinearMap.id)).re =
      r • (Tr (HPHom.toRawSuperoperator s LinearMap.id)).re
    rw [LinearMap.smul_apply, map_smul]
    simp

@[simp]
theorem quantumScalarEval_id :
    quantumScalarEval (𝟙 tensorUnitSystem) = 1 := by
  change (Tr (LinearMap.id : Operator tensorUnitSystem)).re = 1
  rw [trace_unitOperator, operatorUnitEquiv_symm_eq_inner]
  simp [unitVector]

/-- Complete positivity makes the real scalar evaluation nonnegative. -/
theorem quantumScalarEval_nonneg
    {s : tensorUnitSystem ⟶ tensorUnitSystem} (hs : IsEvent s) :
    0 ≤ quantumScalarEval s := by
  have hid : (0 : Operator tensorUnitSystem) ≤ LinearMap.id :=
    (LinearMap.nonneg_iff_isPositive _).mpr LinearMap.isPositive_id
  have hout : (0 : Operator tensorUnitSystem) ≤
      HPHom.toRawSuperoperator s LinearMap.id :=
    QuantumChannel.completelyPositive_to_positiveMap
      (HPHom.toRawSuperoperator s) hs LinearMap.id hid
  have htrace := ((LinearMap.nonneg_iff_isPositive _).mp hout).trace_nonneg
  exact (Complex.nonneg_iff.mp htrace).1

/-- The trace of a CP scalar applied to the unit operator is a nonnegative
complex number (and hence has zero imaginary part). -/
theorem trace_scalar_apply_id_nonneg
    {s : tensorUnitSystem ⟶ tensorUnitSystem} (hs : IsEvent s) :
    (0 : ℂ) ≤ Tr (HPHom.toRawSuperoperator s LinearMap.id) := by
  have hid : (0 : Operator tensorUnitSystem) ≤ LinearMap.id :=
    (LinearMap.nonneg_iff_isPositive _).mpr LinearMap.isPositive_id
  have hout : (0 : Operator tensorUnitSystem) ≤
      HPHom.toRawSuperoperator s LinearMap.id :=
    QuantumChannel.completelyPositive_to_positiveMap
      (HPHom.toRawSuperoperator s) hs LinearMap.id hid
  exact ((LinearMap.nonneg_iff_isPositive _).mp hout).trace_nonneg

/-- Evaluation of CP scalars is multiplicative under sequential composition. -/
theorem quantumScalarEval_comp
    {s t : tensorUnitSystem ⟶ tensorUnitSystem}
    (hs : IsEvent s) (ht : IsEvent t) :
    quantumScalarEval (s ≫ t) = quantumScalarEval s * quantumScalarEval t := by
  let zs : ℂ := Tr (HPHom.toRawSuperoperator s LinearMap.id)
  let zt : ℂ := Tr (HPHom.toRawSuperoperator t LinearMap.id)
  have hscoord : HPHom.toRawSuperoperator s LinearMap.id = operatorUnitEquiv zs :=
    (operatorUnitEquiv_trace (HPHom.toRawSuperoperator s LinearMap.id)).symm
  have hsim : zs.im = 0 :=
    (trace_scalar_apply_id_nonneg hs).2.symm
  have htim : zt.im = 0 :=
    (trace_scalar_apply_id_nonneg ht).2.symm
  change (Tr (HPHom.toRawSuperoperator t
    (HPHom.toRawSuperoperator s LinearMap.id))).re =
    zs.re * zt.re
  calc
    (Tr (HPHom.toRawSuperoperator t
        (HPHom.toRawSuperoperator s LinearMap.id))).re =
        (Tr (HPHom.toRawSuperoperator t (operatorUnitEquiv zs))).re := by
      rw [hscoord]
    _ = (Tr (HPHom.toRawSuperoperator t (zs •
        (LinearMap.id : Operator tensorUnitSystem)))).re := by
      rw [operatorUnitEquiv_eq_smul_id]
    _ = (Tr (zs • HPHom.toRawSuperoperator t LinearMap.id)).re := by
      rw [map_smul]
    _ = (zs * zt).re := by simp [zt, smul_eq_mul]
    _ = zs.re * zt.re := by
      simp [Complex.mul_re, hsim, htim]

/-- Evaluation is multiplicative for the categorical tensor of CP scalars. -/
theorem quantumScalarEval_tensor
    {s t : tensorUnitSystem ⟶ tensorUnitSystem}
    (hs : IsEvent s) (ht : IsEvent t) :
    quantumScalarEval (OPT.tensorScalar (Sys := QuantumModel.Sys) s t) =
      quantumScalarEval s * quantumScalarEval t := by
  have htensor_comp : OPT.tensorScalar (Sys := QuantumModel.Sys) s t = s ≫ t := by
    simp [OPT.tensorScalar, MonoidalCategory.tensorHom_def, Category.assoc,
      MonoidalCategory.unitors_equal, MonoidalCategory.unitors_inv_equal]
  rw [htensor_comp]
  exact quantumScalarEval_comp hs ht

/-! ## The deterministic trace effect -/

variable {A B : Sys}

/-- The orthonormal-basis bra family representing the trace effect. -/
def traceKrausFamily (A : Sys) : KrausFamily A tensorUnitSystem :=
  { index := Fin A.dim
    fintypeIndex := inferInstance
    decidableEqIndex := inferInstance
    operator := fun i => QuantumChannel.outer_product
      ((EuclideanSpace.basisFun (Fin A.dim) ℂ) i) unitVector }

/-- The trace functional, bundled as the basis-bra Kraus HP morphism. -/
noncomputable def traceEffect (A : Sys) : A ⟶ tensorUnitSystem :=
  (traceKrausFamily A).map

/-- The basis bras resolve the identity on the input Hilbert space. -/
theorem traceKrausFamily_normalization (A : Sys) :
    (traceKrausFamily A).normalization = LinearMap.id := by
  rw [KrausFamily.normalization]
  change (∑ i : Fin A.dim,
      (LinearMap.adjoint
        (QuantumChannel.outer_product
          ((EuclideanSpace.basisFun (Fin A.dim) ℂ) i) unitVector)).comp
        (QuantumChannel.outer_product
          ((EuclideanSpace.basisFun (Fin A.dim) ℂ) i) unitVector)) = LinearMap.id
  have hunit : unitVector = outputUnit tensorUnitSystem := by
    simp [unitVector, unitIndex, outputUnit]
  simp_rw [hunit, rankOneKraus_normalization]
  simpa [QuantumChannel.outer_product_eq_rankOne] using
    congrArg ContinuousLinearMap.toLinearMap
      (EuclideanSpace.basisFun (Fin A.dim) ℂ).sum_rankOne_eq_id

/-- Applying the trace effect produces the trace in the tensor-unit coordinate. -/
@[simp]
theorem traceEffect_apply (A : Sys) (X : Operator A) :
    HPHom.toRawSuperoperator (traceEffect A) X =
      operatorUnitEquiv (Tr X) := by
  change (traceKrausFamily A).rawMap X = operatorUnitEquiv (Tr X)
  calc
    (traceKrausFamily A).rawMap X =
        operatorUnitEquiv (Tr ((traceKrausFamily A).rawMap X)) :=
      (operatorUnitEquiv_trace _).symm
    _ = operatorUnitEquiv
        (Tr ((traceKrausFamily A).normalization.comp X)) := by
      change operatorUnitEquiv
          (Tr (HPHom.toRawSuperoperator (traceKrausFamily A).map X)) = _
      rw [trace_krausFamily_map]
    _ = operatorUnitEquiv (Tr X) := by
      rw [traceKrausFamily_normalization]
      simp

/-- The basis-bra Kraus map is the trace effect. -/
theorem traceKrausFamily_map (A : Sys) :
    (traceKrausFamily A).map = traceEffect A :=
  rfl

/-- The trace effect is completely positive and trace preserving. -/
theorem traceEffect_isChannel (A : Sys) : IsChannel (traceEffect A) := by
  let K := traceKrausFamily A
  refine ⟨?_, K, traceKrausFamily_map A, traceKrausFamily_normalization A⟩
  rw [← traceKrausFamily_map A]
  exact K.map_isCompletelyPositive

/-- A channel with tensor-unit output is uniquely the trace effect. -/
theorem traceEffect_unique {A : Sys}
    {e : A ⟶ tensorUnitSystem} (he : IsChannel e) :
    e = traceEffect A := by
  rcases he.2 with ⟨K, hKmap, hKnorm⟩
  apply HPHom.ext
  intro X
  rw [traceEffect_apply]
  calc
    HPHom.toRawSuperoperator e X = K.rawMap X := by
      rw [← hKmap, KrausFamily.map_toRawSuperoperator]
    _ = operatorUnitEquiv (Tr (K.rawMap X)) := (operatorUnitEquiv_trace _).symm
    _ = operatorUnitEquiv (Tr (K.normalization.comp X)) := by
      change operatorUnitEquiv
          (Tr (HPHom.toRawSuperoperator K.map X)) = _
      rw [trace_krausFamily_map]
    _ = operatorUnitEquiv (Tr X) := by rw [hKnorm]; simp

/-- A trace-nonincreasing CP map that preserves the trace effect is a channel. -/
theorem isChannel_of_isTransformation_comp_traceEffect
    {f : A ⟶ B} (hf : IsTransformation f)
    (hpres : f ≫ traceEffect B = traceEffect A) :
    IsChannel f := by
  rcases hf with ⟨hfCP, K, hKmap, hKle⟩
  refine ⟨hfCP, K, hKmap, ?_⟩
  apply operator_eq_of_trace_comp_eq
  intro X
  rw [← trace_krausFamily_map K, hKmap]
  have hpresX := congrArg
    (fun h : A ⟶ tensorUnitSystem ↦ HPHom.toRawSuperoperator h X) hpres
  change HPHom.toRawSuperoperator (traceEffect B)
      (HPHom.toRawSuperoperator f X) =
    HPHom.toRawSuperoperator (traceEffect A) X at hpresX
  rw [traceEffect_apply, traceEffect_apply] at hpresX
  simpa using operatorUnitEquiv.injective hpresX

/-- The missing trace effect of a trace-nonincreasing transformation is CP. -/
theorem traceEffect_sub_comp_isEvent
    {f : A ⟶ B} (hf : IsTransformation f) :
    IsEvent (traceEffect A - (f ≫ traceEffect B)) := by
  obtain ⟨g, hg, hfg⟩ := exists_cp_complement_of_isTransformation f hf
  have hdiscardChannel :
      IsChannel ((f + g) ≫ traceEffect B) :=
    isChannel_comp hfg (traceEffect_isChannel B)
  have hunique :
      (f + g) ≫ traceEffect B = traceEffect A :=
    traceEffect_unique hdiscardChannel
  have heq : traceEffect A - (f ≫ traceEffect B) =
      g ≫ traceEffect B := by
    rw [← hunique, Preadditive.add_comp]
    abel
  rw [heq]
  exact QuantumChannel.comp_isCompletelyPositive
    (HPHom.toRawSuperoperator g)
    (HPHom.toRawSuperoperator (traceEffect B))
    hg (traceEffect_isChannel B).1

end QuantumModel
