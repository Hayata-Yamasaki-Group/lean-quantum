/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.GourQuantumRelativeEntropyBasicProperties.GSLCore
import Quantum.QuantumMechanics.DensityOperator.GSLCore
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Quantum.OperationalProbabilistic.Decomposition.ConditionedStates.GSLCore
import Mathlib.LinearAlgebra.Matrix.Trace
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
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Instances.Matrix
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Logic.Equiv.Bool
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Topology.Algebra.Star.Unitary
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCoreGeneralizedStein
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCore
import Mathlib.Analysis.Complex.Isometry
import Quantum.OperationalProbabilistic.Framework.OrderedConeMaxRelativeEntropyDensity.GSLCore
import Mathlib.Topology.MetricSpace.Basic

open scoped ENNReal

/-!
# Directed max-relative entropy facts

The domination exponent and the quantum max-relative entropy in bits between density operators
are nonnegative (`thompsonDominationExponent_nonneg`,
`quantumMaxRelativeEntropyBits_nonnegative`); cf. the quantum Thompson distance, Gour
eq. (6.122).
-/

namespace OPT

noncomputable section

universe u v

open QuantumState QuantumChannel
open SandwichedRenyiRelativeEntropy

/-! ## Directed max-relative entropy facts -/

/-- A domination exponent between normalized density operators is
nonnegative. -/
private lemma thompsonDominationExponent_nonneg
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

/-- Bit-valued quantum max-relative entropy is nonnegative on density
operators, including the support-mismatch branch. -/
theorem quantumMaxRelativeEntropyBits_nonnegative
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : L H) (hrho : IsDensity rho) (hsigma : IsDensity sigma) :
    0 ≤ quantumMaxRelativeEntropyBits ⟨rho, hrho⟩ ⟨sigma, hsigma⟩ := by
  change 0 ≤ OrderedCone.maxRelEntropy rho sigma
  unfold OrderedCone.maxRelEntropy
  apply le_sInf
  rintro z ⟨lam, rfl, hdom⟩
  exact EReal.coe_nonneg.mpr
    (thompsonDominationExponent_nonneg hrho hsigma (by
      simpa only [Complex.coe_smul] using hdom))

end

end OPT
