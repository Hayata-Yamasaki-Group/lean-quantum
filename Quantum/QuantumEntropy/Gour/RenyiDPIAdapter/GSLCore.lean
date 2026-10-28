/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.Gour.Sandwiched.EndpointClassification.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiNonNegExtra.GSLCore
import Quantum.QuantumMechanics.DiagonalDensity.GSLCore
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.Provider
import Quantum.QuantumMechanics.DensityOperator.GSLCore
import Mathlib.Topology.Order.AtTopBotIxx
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Analysis.Convex.Function
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivDPI.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivConcrete.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiOrder.GSLCore
import Quantum.OperationalProbabilistic.Framework.MeasurementEntropy.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiDivergence.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiRelativeEntropyLimits.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiPowerFDivBridge.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiRelativeEntropy.GSLCore
import Quantum.OperationalProbabilistic.Framework.OrderedConeMaxRelativeEntropy.GSLCore
import Quantum.QuantumEntropy.GourQuantumRelativeEntropyBasicProperties.GSLCore
import Quantum.QuantumEntropy.PetzTraceClassification.GSLCore
import Quantum.QuantumEntropy.RenyiDPI.Interface
import Quantum.QuantumEntropy.SandwichedRenyiBase.Defs
import Quantum.QuantumEntropy.SandwichedRenyiBase.NonNeg.Defs

/-! # Gour bits laws for sandwiched Rényi divergence

For orders strictly greater than one, the Gour quantity is the natural-log
quantity multiplied by `1 / Real.log 2`. Data processing and tensor
additivity are expressed for this fixed quantity.
-/

namespace RenyiDPI

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy OPT
open scoped TensorProduct

universe u v

/-- The existing Gour quantity in bits, at an order strictly greater than one. -/
theorem gourSandwichedBits_eq_scaled_nn_gt_one
    {H : Type u} [Qudit H] [Nontrivial H]
    {α : ℝ} (hα : 1 < α) (ρ σ : L H) (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    gourSandwichedRenyiBits (ENNReal.ofReal α) ρ σ hρ hσ =
      ((1 / Real.log 2 : ℝ) : EReal) * sandwichedRenyiDivNN α ρ σ := by
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  have hone : ENNReal.ofReal α ≠ 1 := by
    intro h
    have := congrArg ENNReal.toReal h
    exact hα.ne' (by simpa only [ENNReal.toReal_ofReal hα0.le,
      ENNReal.toReal_one] using this)
  rw [gourSandwichedRenyiBits_standard_order
    (ENNReal.ofReal_ne_zero_iff.mpr hα0) hone ENNReal.ofReal_ne_top
    (by rw [ENNReal.toReal_ofReal hα0.le]; linarith),
    ENNReal.toReal_ofReal hα0.le]
  unfold standardSandwichedRenyiBitsFinite sandwichedRenyiDivNN
  rw [if_neg hα.ne']
  split_ifs
  · exact (EReal.coe_mul_top_of_pos
      (one_div_pos.mpr (Real.log_pos (by norm_num)))).symm
  · rw [← EReal.coe_mul]
    congr 1
    unfold sandwichedRenyiDiv
    rw [Real.logb]
    ring

private theorem bits_dataProcessing
    (dpi : SandwichedMonotoneOnNonNeg.{u})
    {H K : Type u} [Qudit H] [Nontrivial H] [Qudit K] [Nontrivial K]
    (E : CPTP H K) {α : ℝ} (hα : 1 < α)
    (ρ σ : L H) (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    gourSandwichedRenyiBits (ENNReal.ofReal α) (E.toFun ρ) (E.toFun σ)
        (quantumFMapDensity E ρ hρ) (quantumFMapDensity E σ hσ) ≤
      gourSandwichedRenyiBits (ENNReal.ofReal α) ρ σ hρ hσ := by
  rw [gourSandwichedBits_eq_scaled_nn_gt_one hα,
    gourSandwichedBits_eq_scaled_nn_gt_one hα]
  exact mul_le_mul_of_nonneg_left
    (dpi E hα ((LinearMap.nonneg_iff_isPositive ρ).mpr hρ.1)
      ((LinearMap.nonneg_iff_isPositive σ).mpr hσ.1))
    (EReal.coe_nonneg.mpr (one_div_nonneg.mpr (Real.log_pos (by norm_num)).le))

private theorem bits_tensor
    (tensor : SandwichedTensorAdditiveOnDensity.{u, v})
    {H : Type u} {K : Type v} [Qudit H] [Qudit K]
    [Nontrivial H] [Nontrivial K] [Nontrivial (H ⊗[ℂ] K)]
    {α : ℝ} (hα : 1 < α) (ρ₁ σ₁ : L H) (ρ₂ σ₂ : L K)
    (hρ₁ : IsDensity ρ₁) (hσ₁ : IsDensity σ₁)
    (hρ₂ : IsDensity ρ₂) (hσ₂ : IsDensity σ₂) :
    gourSandwichedRenyiBits (ENNReal.ofReal α)
        (TensorProduct.map ρ₁ ρ₂) (TensorProduct.map σ₁ σ₂)
        (isDensity_tensorProduct ρ₁ ρ₂ hρ₁ hρ₂)
        (isDensity_tensorProduct σ₁ σ₂ hσ₁ hσ₂) =
      gourSandwichedRenyiBits (ENNReal.ofReal α) ρ₁ σ₁ hρ₁ hσ₁ +
        gourSandwichedRenyiBits (ENNReal.ofReal α) ρ₂ σ₂ hρ₂ hσ₂ := by
  rw [gourSandwichedBits_eq_scaled_nn_gt_one hα,
    gourSandwichedBits_eq_scaled_nn_gt_one hα,
    gourSandwichedBits_eq_scaled_nn_gt_one hα,
    tensor ρ₁ σ₁ ρ₂ σ₂ hα hρ₁ hσ₁ hρ₂ hσ₂]
  exact EReal.left_distrib_of_nonneg_of_ne_top
    (EReal.coe_nonneg.mpr (one_div_nonneg.mpr (Real.log_pos (by norm_num)).le))
    (EReal.coe_ne_top _) _ _

/-- Data processing for Gour sandwiched Rényi divergence in bits. -/
theorem gourSandwichedBits_dataProcessing_gt_one
    {H K : Type u} [Qudit H] [Nontrivial H] [Qudit K] [Nontrivial K]
    (E : CPTP H K) {α : ℝ} (hα : 1 < α)
    (ρ σ : L H) (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    gourSandwichedRenyiBits (ENNReal.ofReal α) (E.toFun ρ) (E.toFun σ)
        (quantumFMapDensity E ρ hρ) (quantumFMapDensity E σ hσ) ≤
      gourSandwichedRenyiBits (ENNReal.ofReal α) ρ σ hρ hσ :=
  bits_dataProcessing sandwichedMonotoneOnNonNeg E hα ρ σ hρ hσ

/-- Gour bits tensor additivity supplied by the selected sandwiched side. -/
theorem gourSandwichedBits_tensor_gt_one
    {H : Type u} {K : Type v} [Qudit H] [Qudit K]
    [Nontrivial H] [Nontrivial K] [Nontrivial (H ⊗[ℂ] K)]
    {α : ℝ} (hα : 1 < α) (ρ₁ σ₁ : L H) (ρ₂ σ₂ : L K)
    (hρ₁ : IsDensity ρ₁) (hσ₁ : IsDensity σ₁)
    (hρ₂ : IsDensity ρ₂) (hσ₂ : IsDensity σ₂) :
    gourSandwichedRenyiBits (ENNReal.ofReal α)
        (TensorProduct.map ρ₁ ρ₂) (TensorProduct.map σ₁ σ₂)
        (isDensity_tensorProduct ρ₁ ρ₂ hρ₁ hρ₂)
        (isDensity_tensorProduct σ₁ σ₂ hσ₁ hσ₂) =
      gourSandwichedRenyiBits (ENNReal.ofReal α) ρ₁ σ₁ hρ₁ hσ₁ +
        gourSandwichedRenyiBits (ENNReal.ofReal α) ρ₂ σ₂ hρ₂ hσ₂ :=
  bits_tensor sandwichedTensorAdditivity hα ρ₁ σ₁ ρ₂ σ₂ hρ₁ hσ₁ hρ₂ hσ₂

end RenyiDPI
