/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.FuchsCavesCFCBridge.GSLCore
import Quantum.OperationalProbabilistic.OperationalFidelity.GSLCore
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCoreGeneralizedStein
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCore
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
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Quantum.OperationalProbabilistic.DistinguishableStates.Core.GSLCore
import Quantum.OperationalProbabilistic.Framework.StateNorms.GSLCore
import Quantum.QuantumModel.MatrixHockeyStick.GSLCore
import Quantum.OperationalProbabilistic.Framework.MeasurementStatistics.GSLCore
import Quantum.OperationalProbabilistic.Framework.TestingRegionHockeyStick.GSLCore
import Quantum.QuantumModel.NativeTraceDistance.GSLCore
import Quantum.QuantumModel.NativeTraceDistance.GSLCoreRetained
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.Provider
import Quantum.QuantumEntropy.SandwichedRenyiBase.Umegaki.Reduction
import Quantum.QuantumEntropy.SandwichedRenyiBase.Tensor.GSLCore
import Quantum.QuantumEntropy.UmegakiDPI.NonNegLift
import Quantum.QuantumModel.RegularizationUmegaki.GSLCore
import Quantum.QuantumModel.NativeFacade.GSLCore
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Quantum.QuantumModel.NativeMeasuredRelativeEntropy.GSLCore
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Quantum.TraceInequality.HilbertSchmidtOperatorSpace

/-!
# Measurement lower bound for the root fidelity and upper Fuchs--van de Graaf

This module proves the upper Fuchs--van de Graaf inequality at the classical,
operational and quantum-model levels, and bounds the operator root fidelity by
the root overlap of the Born distributions of any POVM
(`operatorRootFidelity_le_rootOverlap`).

The Fuchs--Caves optimal-measurement statement is documented via KNI,
arXiv:0910.0994, § Fidelity in GPT (source TeX lines 246--263,
not equation numbers).  Its primary sources are Fuchs's thesis,
quant-ph/9601020, and Fuchs--Caves, quant-ph/9604001, Eq. (7).  The
Fuchs--van de Graaf bounds are likewise summarized in KNI, arXiv:0910.0994, at
source TeX lines 308--317 (not equation numbers), referring to Fuchs--van de Graaf (1999).
-/

noncomputable section

open CategoryTheory
open QuantumState
open scoped ENNReal MonoidalCategory

namespace OPT

universe u v

private theorem pmf_toReal_sum_eq_one {iota : Type} [Fintype iota]
    (p : PMF iota) :
    ∑ i, (p i).toReal = 1 := by
  calc
    ∑ i, (p i).toReal = (∑ i, p i).toReal := by
      rw [ENNReal.toReal_sum]
      intro i _hi
      exact PMF.apply_ne_top p i
    _ = 1 := by rw [show ∑ i, p i = (1 : ℝ≥0∞) by simpa using p.tsum_coe]; simp

private theorem classicalRootFidelity_toReal_eq_sum_sqrt
    {iota : Type} [Fintype iota] (p q : PMF iota) :
    (classicalRootFidelity p q).toReal =
      ∑ i, Real.sqrt ((p i).toReal * (q i).toReal) := by
  unfold classicalRootFidelity
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i _hi
    change ((p i * q i) ^ (1 / 2 : ℝ)).toReal = _
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_mul, ← Real.sqrt_eq_rpow]
  · intro i _hi
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (PMF.apply_ne_top p i) (PMF.apply_ne_top q i))

private theorem classicalRootFidelity_toReal_eq_sum_sqrt_mul_sqrt
    {iota : Type} [Fintype iota] (p q : PMF iota) :
    (classicalRootFidelity p q).toReal =
      ∑ i, Real.sqrt (p i).toReal * Real.sqrt (q i).toReal := by
  rw [classicalRootFidelity_toReal_eq_sum_sqrt]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Real.sqrt_mul (ENNReal.toReal_nonneg : 0 ≤ (p i).toReal)]

/-- Classical upper Fuchs--van de Graaf inequality, in total-variation form:
`D_TV(p,q) ≤ sqrt (1 - F_c(p,q)^2)`.

This is the upper inequality in Fuchs--van de Graaf (1999), as summarized at
KNI source TeX lines 308--317, with the root Bhattacharyya convention. -/
theorem classicalFuchsVanDeGraaf_upper
    {iota : Type} [Fintype iota] (p q : PMF iota) :
    (2 : ℝ)⁻¹ * ∑ i, |(p i).toReal - (q i).toReal| ≤
      Real.sqrt (1 - (classicalRootFidelity p q).toReal ^ 2) := by
  let a : iota → ℝ := fun i => Real.sqrt (p i).toReal
  let b : iota → ℝ := fun i => Real.sqrt (q i).toReal
  let F : ℝ := (classicalRootFidelity p q).toReal
  let D : ℝ := (2 : ℝ)⁻¹ * ∑ i, |(p i).toReal - (q i).toReal|
  have ha_nonneg (i : iota) : 0 ≤ a i := Real.sqrt_nonneg _
  have hb_nonneg (i : iota) : 0 ≤ b i := Real.sqrt_nonneg _
  have ha_sq (i : iota) : a i ^ 2 = (p i).toReal := by
    exact Real.sq_sqrt ENNReal.toReal_nonneg
  have hb_sq (i : iota) : b i ^ 2 = (q i).toReal := by
    exact Real.sq_sqrt ENNReal.toReal_nonneg
  have hFsum : F = ∑ i, a i * b i := by
    exact classicalRootFidelity_toReal_eq_sum_sqrt_mul_sqrt p q
  have hp : ∑ i, a i ^ 2 = 1 := by
    simp_rw [ha_sq]
    exact pmf_toReal_sum_eq_one p
  have hq : ∑ i, b i ^ 2 = 1 := by
    simp_rw [hb_sq]
    exact pmf_toReal_sum_eq_one q
  have habs (i : iota) :
      |(p i).toReal - (q i).toReal| =
        |a i - b i| * (a i + b i) := by
    rw [← ha_sq, ← hb_sq]
    have hfactor : a i ^ 2 - b i ^ 2 = (a i - b i) * (a i + b i) := by ring
    rw [hfactor, abs_mul, abs_of_nonneg (add_nonneg (ha_nonneg i) (hb_nonneg i))]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset iota)
    (fun i => |a i - b i|) (fun i => a i + b i)
  have hminus : ∑ i, |a i - b i| ^ 2 = 2 - 2 * F := by
    simp_rw [sq_abs]
    calc
      ∑ i, (a i - b i) ^ 2 =
          ∑ i, (a i ^ 2 + b i ^ 2 - 2 * (a i * b i)) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = (∑ i, a i ^ 2) + (∑ i, b i ^ 2) -
          2 * ∑ i, a i * b i := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.mul_sum]
      _ = 2 - 2 * F := by rw [hp, hq, ← hFsum]; ring
  have hplus : ∑ i, (a i + b i) ^ 2 = 2 + 2 * F := by
    calc
      ∑ i, (a i + b i) ^ 2 =
          ∑ i, (a i ^ 2 + b i ^ 2 + 2 * (a i * b i)) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = (∑ i, a i ^ 2) + (∑ i, b i ^ 2) +
          2 * ∑ i, a i * b i := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.mul_sum]
      _ = 2 + 2 * F := by rw [hp, hq, ← hFsum]; ring
  have hDsq : D ^ 2 ≤ 1 - F ^ 2 := by
    dsimp only [D]
    simp_rw [habs]
    calc
      ((2 : ℝ)⁻¹ * ∑ i, |a i - b i| * (a i + b i)) ^ 2 ≤
          ((2 : ℝ)⁻¹) ^ 2 *
            ((∑ i, |a i - b i| ^ 2) * ∑ i, (a i + b i) ^ 2) := by
        nlinarith
      _ = 1 - F ^ 2 := by rw [hminus, hplus]; ring
  have hF_nonneg : 0 ≤ F := ENNReal.toReal_nonneg
  have hF_le_one : F ≤ 1 := by
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      (classicalRootFidelity_le_one p q)
  have hrad : 0 ≤ 1 - F ^ 2 := by nlinarith
  have hD_nonneg : 0 ≤ D := by
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  dsimp only [D, F] at hDsq hrad hD_nonneg ⊢
  exact (Real.le_sqrt hD_nonneg hrad).2 hDsq

private theorem binaryGap_le_totalVariation
    (p q : PMF BinaryObservationIndex) :
    (p BinaryObservationIndex.one).toReal -
        (q BinaryObservationIndex.one).toReal ≤
      (2 : ℝ)⁻¹ * ∑ i, |(p i).toReal - (q i).toReal| := by
  let d : BinaryObservationIndex → ℝ := fun i =>
    (p i).toReal - (q i).toReal
  have hp := pmf_toReal_sum_eq_one p
  have hq := pmf_toReal_sum_eq_one q
  rw [sum_binaryObservationIndex] at hp hq
  have hzero : d BinaryObservationIndex.zero =
      -d BinaryObservationIndex.one := by
    dsimp only [d]
    linarith
  rw [sum_binaryObservationIndex]
  change d BinaryObservationIndex.one ≤
    (2 : ℝ)⁻¹ *
      (|d BinaryObservationIndex.zero| + |d BinaryObservationIndex.one|)
  rw [hzero, abs_neg]
  convert le_abs_self (d BinaryObservationIndex.one) using 1
  ring

private theorem binaryFuchsVanDeGraaf_upper
    (p q : PMF BinaryObservationIndex) :
    (p BinaryObservationIndex.one).toReal -
        (q BinaryObservationIndex.one).toReal ≤
      Real.sqrt (1 - (classicalRootFidelity p q).toReal ^ 2) :=
  (binaryGap_le_totalVariation p q).trans
    (classicalFuchsVanDeGraaf_upper p q)

section Operational

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]
  [Preadditive Sys] [CategoryTheory.Linear ℝ Sys]
  [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
  [CausalOperationalProbabilisticTheory Sys]

/-- Operational upper Fuchs--van de Graaf inequality for the allowed finite
measurement root fidelity:
`D_op(rho,sigma) ≤ sqrt (1 - F_allowed(rho,sigma)^2)`.

The proof applies the classical upper inequality to every binary observation
and then uses the defining infimum over all allowed finite observations.  This
is the upper inequality of Fuchs--van de Graaf (1999), as summarized at KNI
source TeX lines 308--317. -/
theorem fuchsVanDeGraaf_upper {A : Sys}
    (rho sigma : NormalizedState (Sys := Sys) A) :
    operationalStateDistance (Sys := Sys)
        (operationalStateClass (Sys := Sys) rho.1 rho.2.1)
        (operationalStateClass (Sys := Sys) sigma.1 sigma.2.1) ≤
      Real.sqrt (1 - allowedOperationalRootFidelity rho sigma ^ 2) := by
  let D := operationalStateDistance (Sys := Sys)
    (operationalStateClass (Sys := Sys) rho.1 rho.2.1)
    (operationalStateClass (Sys := Sys) sigma.1 sigma.2.1)
  let F := allowedOperationalRootFidelity rho sigma
  let R := Real.sqrt (1 - F ^ 2)
  have hF_nonneg : 0 ≤ F := by
    dsimp only [F]
    exact allowedOperationalRootFidelity_nonneg rho sigma
  have hF_le_one : F ≤ 1 := by
    dsimp only [F]
    exact allowedOperationalRootFidelity_le_one rho sigma
  have hR_nonneg : 0 ≤ R := Real.sqrt_nonneg _
  have hpoint (M : BinaryObservationTest (Sys := Sys) A) :
      prob (Sys := Sys) (M.outcome BinaryObservationIndex.one) rho.1 -
          prob (Sys := Sys) (M.outcome BinaryObservationIndex.one) sigma.1 ≤ R := by
    let T : Test (Sys := Sys) A (𝟙_ Sys) := Test.ofIndexed M
    let p : PMF BinaryObservationIndex := observationPMF T rho
    let q : PMF BinaryObservationIndex := observationPMF T sigma
    let FM : ℝ := (classicalRootFidelity p q).toReal
    have hrhoProb : 0 ≤
        prob (Sys := Sys) (M.outcome BinaryObservationIndex.one) rho.1 :=
      prob_nonneg_of_isState_isEffect (Sys := Sys) rho.2.1
        (binaryObservation_outcome_isEffect (Sys := Sys) M
          BinaryObservationIndex.one)
    have hsigmaProb : 0 ≤
        prob (Sys := Sys) (M.outcome BinaryObservationIndex.one) sigma.1 :=
      prob_nonneg_of_isState_isEffect (Sys := Sys) sigma.2.1
        (binaryObservation_outcome_isEffect (Sys := Sys) M
          BinaryObservationIndex.one)
    have hpone : (p BinaryObservationIndex.one).toReal =
        prob (Sys := Sys) (M.outcome BinaryObservationIndex.one) rho.1 := by
      rw [show p BinaryObservationIndex.one = ENNReal.ofReal
          (prob (Sys := Sys) (M.outcome BinaryObservationIndex.one) rho.1) by
        exact observationPMF_apply T rho BinaryObservationIndex.one]
      exact ENNReal.toReal_ofReal hrhoProb
    have hqone : (q BinaryObservationIndex.one).toReal =
        prob (Sys := Sys) (M.outcome BinaryObservationIndex.one) sigma.1 := by
      rw [show q BinaryObservationIndex.one = ENNReal.ofReal
          (prob (Sys := Sys) (M.outcome BinaryObservationIndex.one) sigma.1) by
        exact observationPMF_apply T sigma BinaryObservationIndex.one]
      exact ENNReal.toReal_ofReal hsigmaProb
    have hclassical := binaryFuchsVanDeGraaf_upper p q
    rw [hpone, hqone] at hclassical
    have hinf : allowedOperationalRootFidelityENNReal rho sigma ≤
        classicalRootFidelity p q := by
      unfold allowedOperationalRootFidelityENNReal
      exact iInf_le _ T
    have hF_le_FM : F ≤ FM := by
      dsimp only [F, FM, allowedOperationalRootFidelity]
      exact ENNReal.toReal_mono (classicalRootFidelity_ne_top p q) hinf
    have hFM_nonneg : 0 ≤ FM := ENNReal.toReal_nonneg
    have hsquares : 1 - FM ^ 2 ≤ 1 - F ^ 2 := by
      nlinarith
    exact hclassical.trans (Real.sqrt_le_sqrt hsquares)
  have hH : hockeyStick (Sys := Sys) HockeyStickOrder.one rho sigma ≤
      ENNReal.ofReal R := by
    unfold hockeyStick regionSupENNReal
    apply iSup_le
    rintro ⟨z, hz⟩
    rcases hz with ⟨M, rfl⟩
    apply ENNReal.ofReal_le_ofReal
    simpa [testingPoint, HockeyStickOrder.one] using hpoint M
  rw [hockeyStick_one_eq_operationalStateDistance (Sys := Sys)] at hH
  have hreal : D ≤ R := by
    exact (ENNReal.ofReal_le_ofReal_iff hR_nonneg).mp hH
  exact hreal

end Operational

end OPT

namespace QuantumModel

open NativeFidelity

/-- The operational state distance of the canonical quantum-model states is
the native trace distance.  This is the distance side of the OPT/native
dictionary used by the upper Fuchs--van de Graaf inequality. -/
theorem operationalStateDistance_quantumModel {A : Sys}
    (rho sigma : DensityMatrix A) :
    OPT.operationalStateDistance (Sys := Sys)
        (OPT.operationalStateClass (Sys := Sys)
          (DensityMatrix.normalizedStateEquiv rho).1
          (DensityMatrix.normalizedStateEquiv rho).2.1)
        (OPT.operationalStateClass (Sys := Sys)
          (DensityMatrix.normalizedStateEquiv sigma).1
          (DensityMatrix.normalizedStateEquiv sigma).2.1) =
      NativeTraceDistance.traceDistance rho sigma := by
  change (2 : ℝ)⁻¹ *
      OPT.operationalStateNorm (Sys := Sys)
        (OPT.operationalStateClass (Sys := Sys) rho.toState
            rho.toState_isNormalizedState.1 -
          OPT.operationalStateClass (Sys := Sys) sigma.toState
            sigma.toState_isNormalizedState.1) =
    (2 : ℝ)⁻¹ * NativeTraceDistance.traceNorm
      (rho.operator - sigma.operator)
  rw [NativeTraceDistance.operationalStateNorm_sub_eq_traceNorm]

/-- Fidelity cofinality: on the finite-dimensional quantum model, the
OPT-owned infimum over allowed finite observations is exactly the infimum over
all finite native POVMs. -/
theorem allowedOperationalRootFidelityENNReal_quantumModel {A : Sys}
    (rho sigma : DensityMatrix A) :
    OPT.allowedOperationalRootFidelityENNReal
        (DensityMatrix.normalizedStateEquiv rho)
        (DensityMatrix.normalizedStateEquiv sigma) =
      measuredPOVMRootFidelityENNReal rho sigma := by
  let score : OPT.ClassicalPMFScore (OrderDual ℝ≥0∞) :=
    fun p q => OrderDual.toDual (OPT.classicalRootFidelity p q)
  have h := measuredSup_quantumModel_eq_iSup_povm score rho sigma
  simpa [score, OPT.measuredSup, OPT.allowedOperationalRootFidelityENNReal,
    measuredPOVMRootFidelityENNReal, OPT.classicalRootFidelity,
    NativeFidelity.classicalRootFidelity, POVM.rootOverlap] using h

namespace NativeFidelity

open HilbertSchmidtOperatorSpace

open FuchsCavesInternal

private theorem hsInner_eq_trace_operator {A : Sys} (X Y : Operator A) :
    inner ℂ
        (ofOp X.toContinuousLinearMap : HSOp (Space A))
        (ofOp Y.toContinuousLinearMap : HSOp (Space A)) =
      Tr (star X * Y) := by
  rw [hsInner_eq_trace]
  congr 1

private theorem rootOverlap_toReal_eq_sum_sqrt {A : Sys} (M : POVM A)
    (rho sigma : DensityMatrix A) :
    (M.rootOverlap rho sigma).toReal =
      ∑ i, Real.sqrt
        (NativeNoCloning.bornProbability (M.effect i) rho *
          NativeNoCloning.bornProbability (M.effect i) sigma) := by
  unfold POVM.rootOverlap classicalRootFidelity
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i _hi
    change ((ENNReal.ofReal
        (NativeNoCloning.bornProbability (M.effect i) rho) *
      ENNReal.ofReal
        (NativeNoCloning.bornProbability (M.effect i) sigma)) ^
          (1 / 2 : ℝ)).toReal = _
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (M.bornProbability_nonneg rho i),
      ENNReal.toReal_ofReal (M.bornProbability_nonneg sigma i),
      ← Real.sqrt_eq_rpow]
  · intro i _hi
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top
        (ENNReal.ofReal_ne_top) (ENNReal.ofReal_ne_top))

private theorem polarTerm_le_bornGeometricMean {A : Sys}
    (M : POVM A) (rho sigma : DensityMatrix A)
    (U : EnvironmentUnitary A) (i : M.ι) :
    let K : Operator A := LinearMap.adjoint U.toLinearMap
    let R : Operator A := positiveSqrt rho.operator
    let S : Operator A := positiveSqrt sigma.operator
    (Tr (K * R * M.effect i * S)).re ≤
      Real.sqrt
        (NativeNoCloning.bornProbability (M.effect i) rho *
          NativeNoCloning.bornProbability (M.effect i) sigma) := by
  let K : Operator A := LinearMap.adjoint U.toLinearMap
  let R : Operator A := positiveSqrt rho.operator
  let S : Operator A := positiveSqrt sigma.operator
  let C : Operator A := positiveSqrt (M.effect i)
  let X : Operator A := C * R * U.toLinearMap
  let Y : Operator A := C * S
  -- Name the two Hilbert--Schmidt vectors once: each spelled-out `ofOp _.toContinuousLinearMap`
  -- repeats the costly coercion (`CoeFun`) search.
  let x : HSOp (Space A) := ofOp X.toContinuousLinearMap
  let y : HSOp (Space A) := ofOp Y.toContinuousLinearMap
  have hC_nonneg : 0 ≤ C := positiveSqrt_nonneg (M.effect i)
  have hR_nonneg : 0 ≤ R := positiveSqrt_nonneg rho.operator
  have hS_nonneg : 0 ≤ S := positiveSqrt_nonneg sigma.operator
  have hCstar : star C = C := hC_nonneg.isSelfAdjoint
  have hRstar : star R = R := hR_nonneg.isSelfAdjoint
  have hSstar : star S = S := hS_nonneg.isSelfAdjoint
  have hCsq : C * C = M.effect i :=
    positiveSqrt_mul_self (M.effect i) (M.nonneg i)
  have hRsq : R * R = rho.operator :=
    positiveSqrt_mul_self rho.operator rho.nonneg
  have hSsq : S * S = sigma.operator :=
    positiveSqrt_mul_self sigma.operator sigma.nonneg
  have hUK : U.toLinearMap * K = (1 : Operator A) := by
    rw [show K = U.symm.toLinearMap by
      exact LinearIsometryEquiv.adjoint_toLinearMap_eq_symm U]
    ext x
    simp
  have hXstar : star X = K * R * C := by
    simp only [X, K, star_mul, hCstar, hRstar,
      LinearMap.star_eq_adjoint]
    exact (mul_assoc K R C).symm
  have hYstar : star Y = S * C := by
    simp only [Y, star_mul, hCstar, hSstar]
  have hXsq : ‖x‖ ^ 2 =
      NativeNoCloning.bornProbability (M.effect i) rho := by
    calc
      ‖x‖ ^ 2 =
          (inner ℂ x
            x).re :=
        @InnerProductSpace.norm_sq_eq_re_inner ℂ (HSOp (Space A)) _ _ _ _
      _ = (Tr (star X * X)).re := by
        exact congrArg Complex.re (hsInner_eq_trace_operator X X)
      _ = (Tr ((K * R * M.effect i * R) * U.toLinearMap)).re := by
        congr 2
        rw [hXstar, show X = C * R * U.toLinearMap by rfl]
        calc
          (K * R * C) * (C * R * U.toLinearMap) =
              (K * R * (C * C) * R) * U.toLinearMap := by noncomm_ring
          _ = (K * R * M.effect i * R) * U.toLinearMap := by rw [hCsq]
      _ = (Tr (U.toLinearMap * (K * R * M.effect i * R))).re := by
        exact congrArg Complex.re
          (LinearMap.trace_comp_comm' U.toLinearMap
            (K * R * M.effect i * R))
      _ = (Tr (R * M.effect i * R)).re := by
        congr 2
        rw [show U.toLinearMap * (K * R * M.effect i * R) =
          (U.toLinearMap * K) * R * M.effect i * R by noncomm_ring,
          hUK, one_mul]
      _ = (Tr (M.effect i * rho.operator)).re := by
        rw [show R * M.effect i * R = R * (M.effect i * R) by noncomm_ring]
        calc
          (Tr (R * (M.effect i * R))).re =
              (Tr ((M.effect i * R) * R)).re :=
            congrArg Complex.re
              (LinearMap.trace_comp_comm' (M.effect i * R) R)
          _ = (Tr (M.effect i * rho.operator)).re := by
            congr 2
            rw [mul_assoc, hRsq]
      _ = NativeNoCloning.bornProbability (M.effect i) rho := rfl
  have hYsq : ‖y‖ ^ 2 =
      NativeNoCloning.bornProbability (M.effect i) sigma := by
    calc
      ‖y‖ ^ 2 =
          (inner ℂ y
            y).re :=
        @InnerProductSpace.norm_sq_eq_re_inner ℂ (HSOp (Space A)) _ _ _ _
      _ = (Tr (star Y * Y)).re := by
        exact congrArg Complex.re (hsInner_eq_trace_operator Y Y)
      _ = (Tr (S * M.effect i * S)).re := by
        congr 2
        rw [hYstar, show Y = C * S by rfl]
        rw [show S * C * (C * S) = S * (C * C) * S by noncomm_ring,
          hCsq]
      _ = (Tr (M.effect i * sigma.operator)).re := by
        rw [show S * M.effect i * S = S * (M.effect i * S) by noncomm_ring]
        calc
          (Tr (S * (M.effect i * S))).re =
              (Tr ((M.effect i * S) * S)).re :=
            congrArg Complex.re
              (LinearMap.trace_comp_comm' (M.effect i * S) S)
          _ = (Tr (M.effect i * sigma.operator)).re := by
            congr 2
            rw [mul_assoc, hSsq]
      _ = NativeNoCloning.bornProbability (M.effect i) sigma := rfl
  have hXnorm : ‖x‖ =
      Real.sqrt (NativeNoCloning.bornProbability (M.effect i) rho) := by
    rw [← Real.sqrt_sq
      (norm_nonneg x), hXsq]
  have hYnorm : ‖y‖ =
      Real.sqrt (NativeNoCloning.bornProbability (M.effect i) sigma) := by
    rw [← Real.sqrt_sq
      (norm_nonneg y), hYsq]
  have htrace : Tr (K * R * M.effect i * S) = Tr (star X * Y) := by
    congr 1
    rw [hXstar, show Y = C * S by rfl, ← hCsq]
    noncomm_ring
  calc
    (Tr (K * R * M.effect i * S)).re =
        (inner ℂ x
          y).re := by
      rw [htrace, hsInner_eq_trace_operator]
    _ ≤ ‖inner ℂ x
        y‖ :=
      Complex.re_le_norm _
    _ ≤ ‖x‖ *
        ‖y‖ :=
      norm_inner_le_norm _ _
    _ = Real.sqrt
        (NativeNoCloning.bornProbability (M.effect i) rho *
          NativeNoCloning.bornProbability (M.effect i) sigma) := by
      rw [hXnorm, hYnorm,
        Real.sqrt_mul (M.bornProbability_nonneg rho i)]

/-- Every finite POVM has classical root overlap at least the operator root
fidelity.  This is the measurement-monotonicity half of the Fuchs--Caves
dictionary at KNI source TeX lines 246--263 and requires no faithfulness
assumption. -/
theorem operatorRootFidelity_le_rootOverlap {A : Sys} (M : POVM A)
    (rho sigma : DensityMatrix A) :
    ENNReal.ofReal (operatorRootFidelity rho sigma) ≤
      M.rootOverlap rho sigma := by
  let R : Operator A := positiveSqrt rho.operator
  let S : Operator A := positiveSqrt sigma.operator
  obtain ⟨U, hU⟩ :=
    (NativeTraceDistance.traceNorm_unitary_duality (R * S)).1
  let K : Operator A := LinearMap.adjoint U.toLinearMap
  have hsumTrace :
      (Tr (K * R * S)).re =
        ∑ i, (Tr (K * R * M.effect i * S)).re := by
    calc
      (Tr (K * R * S)).re =
          (Tr (K * R * (∑ i, M.effect i) * S)).re := by
        apply congrArg Complex.re
        apply congrArg Tr
        ext x
        simp [M.sum_eq_id]
      _ = ∑ i, (Tr (K * R * M.effect i * S)).re := by
        simp only [Finset.mul_sum, Finset.sum_mul, map_sum, Complex.re_sum]
  have hpolarTrace :
      (Tr (LinearMap.adjoint U.toLinearMap ∘ₗ (R * S))).re =
        (Tr (K * R * S)).re := by
    congr 2
  have hreal : operatorRootFidelity rho sigma ≤
      (M.rootOverlap rho sigma).toReal := by
    rw [operatorRootFidelity_eq_traceNorm_positiveSqrt,
      show positiveSqrt rho.operator * positiveSqrt sigma.operator = R * S by rfl,
      hU, hpolarTrace, hsumTrace, rootOverlap_toReal_eq_sum_sqrt]
    exact Finset.sum_le_sum fun i _hi =>
      polarTerm_le_bornGeometricMean M rho sigma U i
  exact ENNReal.ofReal_le_of_le_toReal hreal

/-- Native upper Fuchs--van de Graaf inequality
`D(rho,sigma) ≤ sqrt (1 - F_R(rho,sigma)^2)`.

The operational inequality is Fuchs--van de Graaf (1999), as summarized at
KNI source TeX lines 308--317.
The comparison between its measured fidelity and the operator expression uses
the POVM lower half of the Fuchs--Caves dictionary and therefore requires no
faithfulness hypothesis. -/
theorem fuchsVanDeGraaf_upper {A : Sys} (rho sigma : DensityMatrix A) :
    NativeTraceDistance.traceDistance rho sigma ≤
      Real.sqrt (1 - operatorRootFidelity rho sigma ^ 2) := by
  let rho' := DensityMatrix.normalizedStateEquiv rho
  let sigma' := DensityMatrix.normalizedStateEquiv sigma
  let Fm : ℝ := OPT.allowedOperationalRootFidelity rho' sigma'
  let Fo : ℝ := operatorRootFidelity rho sigma
  have hgeneric := OPT.fuchsVanDeGraaf_upper rho' sigma'
  rw [operationalStateDistance_quantumModel rho sigma] at hgeneric
  have hmeasuredLower : ENNReal.ofReal Fo ≤
      measuredPOVMRootFidelityENNReal rho sigma := by
    unfold measuredPOVMRootFidelityENNReal
    apply le_iInf
    intro M
    exact operatorRootFidelity_le_rootOverlap M rho sigma
  have hownerLower : ENNReal.ofReal Fo ≤
      OPT.allowedOperationalRootFidelityENNReal rho' sigma' := by
    rw [allowedOperationalRootFidelityENNReal_quantumModel rho sigma]
    exact hmeasuredLower
  have hFo_nonneg : 0 ≤ Fo := operatorRootFidelity_nonneg rho sigma
  have hFm_nonneg : 0 ≤ Fm := by
    exact OPT.allowedOperationalRootFidelity_nonneg rho' sigma'
  have hFm_le_one : Fm ≤ 1 := by
    exact OPT.allowedOperationalRootFidelity_le_one rho' sigma'
  have hFo_le_Fm : Fo ≤ Fm := by
    calc
      Fo = (ENNReal.ofReal Fo).toReal := by rw [ENNReal.toReal_ofReal hFo_nonneg]
      _ ≤ (OPT.allowedOperationalRootFidelityENNReal rho' sigma').toReal :=
        ENNReal.toReal_mono
          (OPT.allowedOperationalRootFidelityENNReal_ne_top rho' sigma')
          hownerLower
      _ = Fm := rfl
  have hsquares : 1 - Fm ^ 2 ≤ 1 - Fo ^ 2 := by
    nlinarith
  exact hgeneric.trans (Real.sqrt_le_sqrt hsquares)

end NativeFidelity
end QuantumModel
