/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
-- Projections identify normal idempotents with self-adjoint idempotents in C*-algebras.
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Algebra.Order.Star.Pi
-- Matrix-block algebra automorphisms are inner after identifying matrices with endomorphisms.
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Artinian.Ring
-- Complete orthogonal idempotent families package the coordinate block projections.
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Topology.Order.Basic
import Quantum.TraceInequality.HiaiPetz.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheorem
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Primitives
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Transport
import Quantum.Analysis.CStar.CayleySpectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.InnerProductSpace.Trace

-- Part of the finite-dimensional infrastructure for the AH1 matrix-order bridge.

/-!
# Positive-ray AH1 endpoint order

Carlen 2022 Theorem 1.45 (AH1): CFC twist, endpoint linear control,
inverse-square order, endpoint quotient comparison, and Cayley normalization.
-/

namespace Quantum.TraceInequality.Loewner

open scoped MatrixOrder ComplexOrder CStarAlgebra FinMatrixCStar
open scoped Topology
open Filter
open Matrix

/-!
### Local instance caches for heavy real-scalar searches

The endpoint CFC comparison repeatedly elaborates real scalar actions on
complex operator algebras.  These local instances register the same winner
terms as the D1 cache fix, avoiding repeated restricted-scalar searches after
local instance changes.
-/

/-- Local cache: real scalar multiplication on operators over an ambient space. -/
private noncomputable local instance instRealSMulCLMEndCache
    {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℂ T] :
    SMul ℝ (T →L[ℂ] T) :=
  Algebra.complexToReal.toSMul

/-- Local cache: real module structure on operators over an ambient space. -/
private noncomputable local instance instRealModuleCLMEndCache
    {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℂ T] :
    Module ℝ (T →L[ℂ] T) :=
  Module.complexToReal (T →L[ℂ] T)

/-- Local cache: real algebra structure on operators over an ambient space. -/
private noncomputable local instance instRealAlgebraCLMEndCache
    {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℂ T] :
    Algebra ℝ (T →L[ℂ] T) :=
  Algebra.complexToReal

/-- Local cache: real multiplicative action on operators over an ambient space. -/
private noncomputable local instance instRealMulActionCLMEndCache
    {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℂ T] :
    MulAction ℝ (T →L[ℂ] T) :=
  (Module.complexToReal (T →L[ℂ] T)).toMulAction

/-- Local cache: real distributive action on operators over an ambient space. -/
private noncomputable local instance instRealDistribSMulCLMEndCache
    {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℂ T] :
    DistribSMul ℝ (T →L[ℂ] T) :=
  (Module.complexToReal (T →L[ℂ] T)).toDistribMulAction.toDistribSMul

/-- Local cache: the real action commutes with the algebra self-action. -/
private noncomputable local instance instRealSMulCommClassCLMEndCache
    {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℂ T] :
    SMulCommClass ℝ (T →L[ℂ] T) (T →L[ℂ] T) :=
  SMulCommClass.complexToReal

/-! ### Concrete CFC twist and endpoint linear control -/
/-- Concrete finite-dimensional CFC twist `X ↦ X^* g(X) X`. -/
noncomputable def positiveRayMatrixCfcTwist (g : ℝ → ℝ) (n : ℕ)
    (X : HansenPedersen.Mₙ n) : HansenPedersen.Mₙ n :=
  Xᴴ * positiveRayMatrixCfc g n X * X

/-- On positive inputs, the CFC twist `X^* g(X) X` is Hermitian. -/
lemma positiveRayMatrixCfcTwist_isHermitian_of_posDef {g : ℝ → ℝ} {n : ℕ}
    (X : HansenPedersen.Mₙ n) (hX : X.PosDef) :
    (positiveRayMatrixCfcTwist g n X).IsHermitian := by
  dsimp [positiveRayMatrixCfcTwist]
  exact Matrix.isHermitian_conjTranspose_mul_mul X
    (positiveRayMatrixCfc_isHermitian_of_posDef (g := g) X hX)

/-- The CFC twist has the expected vector quadratic-form identity. -/
lemma positiveRayMatrixCfcTwist_qform {g : ℝ → ℝ} {n : ℕ}
    (X : HansenPedersen.Mₙ n) (v : Fin n → ℂ) :
    positiveRayQForm (positiveRayMatrixCfcTwist g n X) v =
      positiveRayQForm (positiveRayMatrixCfc g n X) (X.mulVec v) := by
  unfold positiveRayMatrixCfcTwist positiveRayQForm
  simp only [star_mulVec, dotProduct_mulVec, vecMul_vecMul]

/-- The concrete CFC twist satisfies the positive-input twist predicate. -/
theorem positiveRayMatrixCfcTwistOnPositive (g : ℝ → ℝ) :
    PositiveRayMatrixQFormTwistOnPositive
      (positiveRayMatrixCfc g) (positiveRayMatrixCfcTwist g) := by
  intro n X _hX v
  exact positiveRayMatrixCfcTwist_qform (g := g) X v

/--
Endpoint linear control for a positive-ray scalar function.

This packages the estimate `0 ≤ h x ≤ C * x`, eventually as `x` tends to
`0` from the right.
-/
def PositiveRayEndpointLinearControl (h : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 ≤ h x ∧ h x ≤ C * x

/--
Endpoint linear control can be unpacked as a concrete right-neighborhood
estimate on an interval `(0, δ)`.
-/
lemma PositiveRayEndpointLinearControl.exists_pos_interval_bound
    {h : ℝ → ℝ} (hlin : PositiveRayEndpointLinearControl h) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (0 : ℝ) δ → 0 ≤ h x ∧ h x ≤ C * x := by
  rcases hlin with ⟨C, hC, hbound⟩
  have hmem : {x : ℝ | 0 ≤ h x ∧ h x ≤ C * x} ∈ 𝓝[>] (0 : ℝ) := hbound
  rcases Metric.mem_nhdsWithin_iff.mp hmem with ⟨ε, hε, hsubset⟩
  refine ⟨C, min ε 1, hC, lt_min hε zero_lt_one, ?_⟩
  intro x hx
  have hxball : x ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [abs_of_pos hx.1] using lt_of_lt_of_le hx.2 (min_le_left ε 1)
  exact hsubset ⟨hxball, hx.1⟩

/--
Closed positive-ray matrix CFC convexity plus endpoint linear control implies
continuity of the scalar function on the closed positive ray.
-/
theorem continuousOn_Ici_of_closedMatrixConvex_endpointControl
    {h : ℝ → ℝ}
    (hclosed : PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0)) :
    ContinuousOn h (Set.Ici (0 : ℝ)) := by
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) h :=
    positiveRayScalarConvexOn_Ici_of_closedMatrixOperatorConvex hclosed
  have hcontIoi : ContinuousOn h (Set.Ioi (0 : ℝ)) := by
    simpa [interior_Ici] using hconv.continuousOn_interior
  rcases PositiveRayEndpointLinearControl.exists_pos_interval_bound hlin with
    ⟨C, δ, _hC, hδ, hbound⟩
  intro x hx
  by_cases hxzero : x = 0
  · subst x
    have hupper :
        ∀ᶠ y in 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ), h y - h 0 ≤ C * y := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with y hy0 hyδ
      by_cases hyzero : y = 0
      · simp [hyzero]
      · have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hyzero)
        exact (hbound ⟨hypos, hyδ⟩).2
    have hlower :
        ∀ᶠ y in 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ), 0 ≤ h y - h 0 := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with y hy0 hyδ
      by_cases hyzero : y = 0
      · simp [hyzero]
      · have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hyzero)
        exact (hbound ⟨hypos, hyδ⟩).1
    have hCx :
        Tendsto (fun y : ℝ => C * y)
          (𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)) (𝓝 0) := by
      have hid : ContinuousWithinAt (fun y : ℝ => y)
          (Set.Ici (0 : ℝ)) (0 : ℝ) := continuousWithinAt_id
      simpa using (hid.const_mul C).tendsto
    have hdiff :
        Tendsto (fun y : ℝ => h y - h 0)
          (𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)) (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hCx hlower hupper
    have hsum :
        Tendsto (fun y : ℝ => (h y - h 0) + h 0)
          (𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)) (𝓝 (0 + h 0)) :=
      hdiff.add tendsto_const_nhds
    simpa [sub_add_cancel] using hsum
  · have hxpos : x ∈ Set.Ioi (0 : ℝ) := lt_of_le_of_ne hx (Ne.symm hxzero)
    exact (hcontIoi x hxpos).mono_of_mem_nhdsWithin
      (nhdsWithin_le_nhds (Ioi_mem_nhds hxpos))

/-! ### Inverse-square endpoint shift order -/
section PositiveRayEndpointShiftOrder

/-- The bounded-operator algebra on `EuclideanSpace ℂ (Fin n)` has a real continuous functional
calculus for self-adjoint elements. -/
noncomputable local instance positiveRayEndpointShiftOrderCFC
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))] :
    ContinuousFunctionalCalculus ℝ
      ((EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- Nonnegative bounded operators on `EuclideanSpace ℂ (Fin n)` have nonnegative real spectrum. -/
noncomputable local instance positiveRayEndpointShiftOrderNonnegSpectrumClass
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))] :
    NonnegSpectrumClass ℝ
      ((EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) := inferInstance

end PositiveRayEndpointShiftOrder

/-! ### Endpoint quotient and inverse-square CFC comparison -/
/-- The endpoint quotient with prescribed endpoint value `d`. -/
noncomputable def positiveRayEndpointQuotient (h : ℝ → ℝ) (d : ℝ) : ℝ → ℝ :=
  fun x => if x = 0 then d else (h x - h 0) / x

section PositiveRayEndpointQuotientCFC

/-- The bounded-operator algebra on `EuclideanSpace ℂ (Fin n)` has a real continuous functional
calculus for self-adjoint elements. -/
noncomputable local instance positiveRayEndpointQuotientCFCCFC
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))] :
    ContinuousFunctionalCalculus ℝ
      ((EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- Nonnegative bounded operators on `EuclideanSpace ℂ (Fin n)` have nonnegative real spectrum. -/
noncomputable local instance positiveRayEndpointQuotientCFCNonnegSpectrumClass
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))] :
    NonnegSpectrumClass ℝ
      ((EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) := inferInstance

/-! ### Cayley pullback and finite spectral normalization -/
/-- A finite-dimensional complex algebra has finite real spectrum. -/
theorem positiveRayEndpointQuotientCFC_spectrum_real_finite_of_finiteDimensional_complex
    {B : Type*} [Ring B] [Algebra ℂ B] [IsScalarTower ℝ ℂ B]
    [FiniteDimensional ℂ B] (b : B) :
    (spectrum ℝ b).Finite := by
  exact spectrum_real_finite_of_finiteDimensional_complex b

/-- A finite-dimensional non-unital C*-algebra has finite real quasispectrum. -/
theorem positiveRayEndpointQuotientCFC_quasispectrum_real_finite_of_finiteDimensional_complex
    {A : Type*} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A] (a : A) :
    (quasispectrum ℝ a).Finite := by
  rw [Unitization.quasispectrum_eq_spectrum_inr' ℝ ℂ a]
  exact positiveRayEndpointQuotientCFC_spectrum_real_finite_of_finiteDimensional_complex
    (B := Unitization ℂ A) (a : Unitization ℂ A)

end PositiveRayEndpointQuotientCFC

end Quantum.TraceInequality.Loewner
