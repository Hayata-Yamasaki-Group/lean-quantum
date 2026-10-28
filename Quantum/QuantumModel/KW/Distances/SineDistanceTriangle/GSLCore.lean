/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.SupportCompression.GSLCore
import Quantum.QuantumModel.NativeTraceNormCore.GSLCore
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Quantum.QuantumModel.NativeFidelity.GSLCoreRetained
import Quantum.QuantumModel.FuchsCavesFvGUpper.GSLCore
import Quantum.QuantumModel.NativeTraceDistance.GSLCore
import Quantum.QuantumModel.NativeTraceDistance.GSLCoreRetained
import Quantum.QuantumModel.HighInterfaces.GSLCore
import Quantum.QuantumModel.HighInterfaces.GSLCoreRetained
import Quantum.OperationalProbabilistic.Framework.ExactCompression.GSLCore
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Quantum.OperationalProbabilistic.Framework.NormalizedEffects.GSLCore
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformConvergence
import Quantum.OperationalProbabilistic.Framework.TestingRegionHockeyStick.GSLCore
import Quantum.OperationalProbabilistic.Framework.OrderedConeMaxRelativeEntropy.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestOutcomes.GSLCore
import Quantum.OperationalProbabilistic.Framework.TransformationNorms.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiOrder.GSLCore
import Quantum.OperationalProbabilistic.Framework.MeasurementEntropy.GSLCore
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Tactic
import Quantum.OperationalProbabilistic.OperationalFidelity.GSLCore
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Probability.Distributions.Uniform
import Quantum.OperationalProbabilistic.Framework.QuantumRelativeEntropyLaws.GSLCore
import Quantum.OperationalProbabilistic.Framework.QuantumRelativeEntropyLaws.GSLCoreRetained
import Mathlib.Geometry.Convex.Cone.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Topology
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Quantum.OperationalProbabilistic.Framework.StateEffectMaps.GSLCore
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.IsLUB
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Instances.Matrix
import Quantum.OperationalProbabilistic.Decomposition.ConditionedStates.GSLCore
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Quantum.OperationalProbabilistic.Framework.LosslessConditioning.GSLCore
import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Analysis.Convex.Integral
import Quantum.OperationalProbabilistic.Framework.EffectsAndPreparations.GSLCore
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Quantum.OperationalProbabilistic.Framework.FiniteIIDPMF.GSLCore
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.Convex.Independent
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Quantum.OperationalProbabilistic.DistinguishableStates.Core.GSLCore
import Quantum.OperationalProbabilistic.Framework.StateNorms.GSLCore
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Matrix.ToLin
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivConcrete.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivergence.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiDivergence.GSLCore
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import Quantum.OperationalProbabilistic.Framework.TransformationApplication.GSLCore
import Quantum.OperationalProbabilistic.Framework.Core.GSLCore
import Quantum.OperationalProbabilistic.Framework.EffectNorms.GSLCore
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Quantum.OperationalProbabilistic.Framework.MeasuredLift.GSLCore
import Quantum.OperationalProbabilistic.Framework.MeasurementStatistics.GSLCore
import Quantum.OperationalProbabilistic.Framework.OperationalStateDistance.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestingRegion.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestingRegionDecisionDefinitions.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestsCore.GSLCore
import Quantum.OperationalProbabilistic.Framework.TransformationQuotients.GSLCore
import Quantum.OperationalProbabilistic.MeasuredRelativeEntropy.GSLCore
import Mathlib.Analysis.Convex.Strict
import Quantum.QuantumModel.NativeNoCloning.GSLCore
import Quantum.QuantumModel.NativeMeasuredRelativeEntropy.GSLCore
import Quantum.QuantumModel.SupportFaceDictionary.GSLCore
import Mathlib.Analysis.InnerProductSpace.PiL2
import Quantum.TraceInequality.HilbertSchmidtOperatorSpace
import Quantum.QuantumModel.NativePureTargetFidelity.GSLCore

/-!
# Trace distance between pure states

The exact trace distance between two normalized pure states
(`NativeTraceDistance.traceDistance_pureOfUnitVector_eq`).
-/

noncomputable section

namespace QuantumModel

open CategoryTheory
open QuantumState
open scoped ComplexOrder MonoidalCategory TensorProduct

-- The cubic identity for the difference of two unit rank-one projections (the original proof
-- of `hcube` below, stated directly on outer products so that no costly `change` is needed).
private theorem outer_product_sub_cube {A : Sys} (u v : Space A) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (x : Space A) :
    (QuantumChannel.outer_product u u - QuantumChannel.outer_product v v)
        ((QuantumChannel.outer_product u u - QuantumChannel.outer_product v v)
          ((QuantumChannel.outer_product u u -
            QuantumChannel.outer_product v v) x)) =
      (1 - ‖(inner ℂ u v : ℂ)‖ ^ 2 : ℝ) •
        ((QuantumChannel.outer_product u u -
          QuantumChannel.outer_product v v) x) := by
  simp only [QuantumChannel.outer_product_eq_rankOne,
    LinearMap.sub_apply, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, inner_sub_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hu, Complex.coe_algebraMap,
    Complex.ofReal_one, one_pow, mul_one, hv, smul_sub]
  rw [(inner_conj_symm v u).symm]
  rw [← algebraMap_smul ℂ (1 - ‖(inner ℂ u v : ℂ)‖ ^ 2)
      ((inner ℂ u x) • u),
    ← algebraMap_smul ℂ (1 - ‖(inner ℂ u v : ℂ)‖ ^ 2)
      ((inner ℂ v x) • v)]
  simp only [map_sub, map_one, smul_smul]
  push_cast
  have hnorm : (‖(inner ℂ u v : ℂ)‖ : ℂ) ^ 2 =
      starRingEnd ℂ (inner ℂ u v) * inner ℂ u v := by
    rw [← Complex.ofReal_pow, Complex.sq_norm]
    simpa [starRingEnd_apply] using
      (Complex.normSq_eq_conj_mul_self (z := inner ℂ u v))
  congr 1
  · congr 1
    simp only [RCLike.algebraMap_eq_ofReal] at hnorm ⊢
    linear_combination (norm := ring_nf) (inner ℂ u x) * hnorm
    rw [sub_eq_zero]
    congr 1
  · congr 1
    simp only [RCLike.algebraMap_eq_ofReal] at hnorm ⊢
    linear_combination (norm := ring_nf) (inner ℂ v x) * hnorm
    rw [sub_eq_zero]
    congr 1

-- A symmetric operator with `X ∘ X ∘ X = t • X` (`0 < t`) has `‖t^{-1/2} • X‖ ≤ 1`: its
-- eigenvalues satisfy `λ ^ 2 ≤ t` (the original proof of `hK` below).
private theorem opNorm_inv_sqrt_smul_le_one {A : Sys} (X : Operator A) (hXsymm : X.IsSymmetric)
    (t : ℝ) (htpos : 0 < t) (ht_nonneg : 0 ≤ t) (hcube : X.comp (X.comp X) = (t : ℂ) • X) :
    ‖((((Real.sqrt t : ℂ)⁻¹) • X : Operator A)).toContinuousLinearMap‖ ≤ 1 := by
  let b := hXsymm.eigenvectorBasis
    (show Module.finrank ℂ (Space A) = Module.finrank ℂ (Space A) by rfl)
  let eig := hXsymm.eigenvalues
    (show Module.finrank ℂ (Space A) = Module.finrank ℂ (Space A) by rfl)
  have heig_sq (i : Fin (Module.finrank ℂ (Space A))) :
      eig i ^ 2 ≤ t := by
    have happ := LinearMap.congr_fun hcube (b i)
    have heig : X (b i) = (eig i : ℂ) • b i := by
      exact hXsymm.apply_eigenvectorBasis rfl i
    simp only [LinearMap.comp_apply, heig, map_smul, smul_smul,
      LinearMap.smul_apply] at happ
    have hb_ne : b i ≠ 0 := b.toBasis.ne_zero i
    have hscalar : ((eig i : ℂ) ^ 3) = (t : ℂ) * eig i := by
      exact smul_left_injective ℂ hb_ne (by
        simpa [pow_succ, mul_assoc] using happ)
    have hscalar_re : eig i ^ 3 = t * eig i := by
      exact_mod_cast hscalar
    by_cases hzero : eig i = 0
    · simp [hzero, le_of_lt htpos]
    · have heq : eig i ^ 2 = t := by
        have hmul : eig i * (eig i ^ 2 - t) = 0 := by
          nlinarith [hscalar_re]
        exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hzero)
      exact heq.le
  have hcoord (i : Fin (Module.finrank ℂ (Space A))) (x : Space A) :
      b.repr (((Real.sqrt t : ℂ)⁻¹) • X x) i =
        ((Real.sqrt t : ℂ)⁻¹ * (eig i : ℂ)) * b.repr x i := by
    rw [map_smul]
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [hXsymm.eigenvectorBasis_apply_self_apply rfl]
    simp [b, eig, mul_assoc]
  have hcoeff (i : Fin (Module.finrank ℂ (Space A))) :
      ‖((Real.sqrt t : ℂ)⁻¹ * (eig i : ℂ))‖ ≤ 1 := by
    have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.2 htpos
    have hsqrt_sq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht_nonneg
    have habs_sq : |eig i| ^ 2 = eig i ^ 2 := sq_abs (eig i)
    have habs_le : |eig i| ≤ Real.sqrt t := by
      apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).1
      rw [habs_sq, hsqrt_sq]
      exact heig_sq i
    rw [norm_mul, norm_inv, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hsqrt_pos]
    exact (inv_mul_le_one₀ hsqrt_pos).2 habs_le
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  suffices hbound : ‖(Real.sqrt t : ℂ)⁻¹ • X x‖ ≤ ‖x‖ by
    rw [LinearMap.coe_toContinuousLinearMap', LinearMap.smul_apply, one_mul]
    exact hbound
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  calc
    ‖(Real.sqrt t : ℂ)⁻¹ • X x‖ ^ 2 =
        ‖b.repr ((Real.sqrt t : ℂ)⁻¹ • X x)‖ ^ 2 := by
      rw [b.repr.norm_map]
    _ = ∑ i, ‖b.repr ((Real.sqrt t : ℂ)⁻¹ • X x) i‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
    _ ≤ ∑ i, ‖b.repr x i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [hcoord]
      have hc := hcoeff i
      rw [norm_mul, mul_pow]
      have hcsq :
          ‖((Real.sqrt t : ℂ)⁻¹ * (eig i : ℂ))‖ ^ 2 ≤ 1 := by
        nlinarith [norm_nonneg
          ((Real.sqrt t : ℂ)⁻¹ * (eig i : ℂ))]
      calc
        ‖((Real.sqrt t : ℂ)⁻¹ * (eig i : ℂ))‖ ^ 2 *
            ‖b.repr x i‖ ^ 2 ≤ 1 * ‖b.repr x i‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcsq (sq_nonneg _)
        _ = ‖b.repr x i‖ ^ 2 := one_mul _
    _ = ‖b.repr x‖ ^ 2 := by rw [EuclideanSpace.norm_sq_eq]
    _ = ‖x‖ ^ 2 := by rw [b.repr.norm_map]

/-- The trace distance of two normalized pure states is the sine of their angle.

Source: Khatri--Wilde, arXiv:2011.04672v2, Chapter 6,
`eq-trace_dist_pure_states` (TeX lines 14--15).
The only difference from this formalization is the argument representation: pure states are
constructed from unit vectors rather than from density matrices. Finite dimensionality and the
square convention for the fidelity agree with the source.
There are no other differences. -/
theorem NativeTraceDistance.traceDistance_pureOfUnitVector_eq
    {A : Sys} (u v : Space A) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    NativeTraceDistance.traceDistance
        (DensityMatrix.pureOfUnitVector u hu)
        (DensityMatrix.pureOfUnitVector v hv) =
      Real.sqrt (1 - ‖(inner ℂ u v : ℂ)‖ ^ 2) := by
  let rho : DensityMatrix A := DensityMatrix.pureOfUnitVector u hu
  let sigma : DensityMatrix A := DensityMatrix.pureOfUnitVector v hv
  let X : Operator A := rho.operator - sigma.operator
  let t : ℝ := 1 - ‖(inner ℂ u v : ℂ)‖ ^ 2
  change NativeTraceDistance.traceDistance rho sigma = Real.sqrt t
  have hoverlap_le : ‖(inner ℂ u v : ℂ)‖ ≤ 1 := by
    calc
      ‖(inner ℂ u v : ℂ)‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
      _ = 1 := by rw [hu, hv, one_mul]
  have ht_nonneg : 0 ≤ t := by
    dsimp [t]
    nlinarith [sq_nonneg ‖(inner ℂ u v : ℂ)‖,
      norm_nonneg (inner ℂ u v : ℂ)]
  have hfidSq : NativeFidelity.operatorRootFidelity rho sigma ^ 2 =
      ‖(inner ℂ u v : ℂ)‖ ^ 2 := by
    rw [NativeFidelity.operatorRootFidelity_sq_pureOfUnitVector]
    change (Tr ((QuantumChannel.outer_product v v).comp
      (QuantumChannel.outer_product u u))).re = _
    rw [NativeMeasuredRelativeEntropy.trace_outer_product_comp]
    simp only [QuantumChannel.outer_product_eq_rankOne,
      ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
      CStarModule.inner_op_smul_right, Complex.mul_re]
    rw [(inner_conj_symm v u).symm]
    change (inner ℂ u v * starRingEnd ℂ (inner ℂ u v)).re =
      ‖(inner ℂ u v : ℂ)‖ ^ 2
    have hnorm : (‖(inner ℂ u v : ℂ)‖ : ℂ) ^ 2 =
        starRingEnd ℂ (inner ℂ u v) * inner ℂ u v := by
      rw [← Complex.ofReal_pow, Complex.sq_norm]
      simpa [starRingEnd_apply] using
        (Complex.normSq_eq_conj_mul_self (z := inner ℂ u v))
    calc
      (inner ℂ u v * starRingEnd ℂ (inner ℂ u v)).re =
          (starRingEnd ℂ (inner ℂ u v) * inner ℂ u v).re := by
        rw [mul_comm]
      _ = (((‖(inner ℂ u v : ℂ)‖ : ℝ) : ℂ) ^ 2).re :=
        congrArg Complex.re hnorm.symm
      _ = ‖(inner ℂ u v : ℂ)‖ ^ 2 := by
        norm_num [pow_two, Complex.mul_re]
  have hupper : NativeTraceDistance.traceDistance rho sigma ≤ Real.sqrt t := by
    have h := NativeFidelity.fuchsVanDeGraaf_upper rho sigma
    rw [hfidSq] at h
    exact h
  have hdist_nonneg : 0 ≤ NativeTraceDistance.traceDistance rho sigma := by
    unfold NativeTraceDistance.traceDistance
    exact mul_nonneg (by positivity) (NativeTraceDistance.traceNorm_nonneg _)
  by_cases htzero : t = 0
  · rw [htzero, Real.sqrt_zero] at hupper ⊢
    exact le_antisymm hupper hdist_nonneg
  · have htpos : 0 < t := lt_of_le_of_ne ht_nonneg (Ne.symm htzero)
    have hcube : X.comp (X.comp X) = (t : ℂ) • X := by
      apply LinearMap.ext
      intro x
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.smul_apply]
      have h := outer_product_sub_cube u v hu hv x
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)] at h
      exact h
    let K : Operator A := ((Real.sqrt t : ℂ)⁻¹) • X
    have hK : ‖K.toContinuousLinearMap‖ ≤ 1 := by
      have hXsymm : X.IsSymmetric :=
        (((LinearMap.nonneg_iff_isPositive _).mp
          (QuantumChannel.outer_product_self_nonneg u)).isSymmetric).sub
            (((LinearMap.nonneg_iff_isPositive _).mp
              (QuantumChannel.outer_product_self_nonneg v)).isSymmetric)
      exact opNorm_inv_sqrt_smul_le_one X hXsymm t htpos ht_nonneg hcube
    have htrace : (Tr (X.comp X)).re = 2 * t := by
      rw [show X.comp X =
          (QuantumChannel.outer_product u u).comp X -
            (QuantumChannel.outer_product v v).comp X by
        simp [X, rho, sigma, DensityMatrix.pureOfUnitVector,
          LinearMap.sub_comp]]
      rw [map_sub, Complex.sub_re,
        NativeMeasuredRelativeEntropy.trace_outer_product_comp,
        NativeMeasuredRelativeEntropy.trace_outer_product_comp]
      simp only [DensityMatrix.pureOfUnitVector,
        QuantumChannel.outer_product_eq_rankOne, LinearMap.sub_apply,
        ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
        inner_self_eq_norm_sq_to_K, hu, Complex.coe_algebraMap,
        Complex.ofReal_one, one_pow, one_smul, CStarModule.inner_sub_right,
        CStarModule.inner_op_smul_right, Complex.sub_re, Complex.one_re,
        Complex.mul_re, hv, X, rho, sigma]
      rw [(inner_conj_symm v u).symm]
      change
        1 - (starRingEnd ℂ (inner ℂ u v) * inner ℂ u v).re -
            ((inner ℂ u v * starRingEnd ℂ (inner ℂ u v)).re - 1) =
          2 * t
      have hnorm : (‖(inner ℂ u v : ℂ)‖ : ℂ) ^ 2 =
          starRingEnd ℂ (inner ℂ u v) * inner ℂ u v := by
        rw [← Complex.ofReal_pow, Complex.sq_norm]
        simpa [starRingEnd_apply] using
          (Complex.normSq_eq_conj_mul_self (z := inner ℂ u v))
      have hprod1 :
          (starRingEnd ℂ (inner ℂ u v) * inner ℂ u v).re =
            ‖(inner ℂ u v : ℂ)‖ ^ 2 := by
        calc
          (starRingEnd ℂ (inner ℂ u v) * inner ℂ u v).re =
              ((‖(inner ℂ u v : ℂ)‖ : ℂ) ^ 2).re :=
            congrArg Complex.re hnorm.symm
          _ = ‖(inner ℂ u v : ℂ)‖ ^ 2 := by
            norm_num [pow_two, Complex.mul_re]
      have hprod2 :
          (inner ℂ u v * starRingEnd ℂ (inner ℂ u v)).re =
            ‖(inner ℂ u v : ℂ)‖ ^ 2 := by
        rw [mul_comm]
        exact hprod1
      rw [hprod1, hprod2]
      dsimp [t]
      ring
    have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.2 htpos
    have hsqrt_ne : Real.sqrt t ≠ 0 := ne_of_gt hsqrt_pos
    have hsqrt_sq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht_nonneg
    have hpair : (Tr (K.comp X)).re = 2 * Real.sqrt t := by
      rw [show K.comp X = ((Real.sqrt t : ℂ)⁻¹ • X.comp X) by
        simp [K, LinearMap.smul_comp]]
      rw [map_smul]
      change (((Real.sqrt t : ℂ)⁻¹ * Tr (X.comp X)).re) = _
      have hcinv : (Real.sqrt t : ℂ)⁻¹ = ((Real.sqrt t)⁻¹ : ℝ) := by
        push_cast
        rfl
      rw [hcinv, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, htrace]
      have htwice : 2 * t = 2 * Real.sqrt t * Real.sqrt t := by
        nlinarith [hsqrt_sq]
      calc
        (Real.sqrt t)⁻¹ * (2 * t) =
            (Real.sqrt t)⁻¹ * (2 * Real.sqrt t * Real.sqrt t) := by
          rw [htwice]
        _ = 2 * ((Real.sqrt t)⁻¹ * Real.sqrt t) * Real.sqrt t := by ring
        _ = 2 * Real.sqrt t := by rw [inv_mul_cancel₀ hsqrt_ne]; ring
    have hdual := (NativeTraceDistance.traceNorm_unitary_duality X).2 K hK
    rw [hpair] at hdual
    have hlower : Real.sqrt t ≤ NativeTraceDistance.traceDistance rho sigma := by
      change Real.sqrt t ≤ (2 : ℝ)⁻¹ * NativeTraceDistance.traceNorm X
      nlinarith
    exact le_antisymm hupper hlower

end QuantumModel
