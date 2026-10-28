/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.MatrixHockeyStick.GSLCore
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
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
import Mathlib.Analysis.Complex.Isometry
import Quantum.QuantumModel.NativeTraceDistance.GSLCore
import Quantum.QuantumModel.NativeEffectStateDefinitions.GSLCore
import Quantum.QuantumModel.Calculus.GSLCore
import Quantum.QuantumModel.RegularizationCarrier.GSLCore
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Quantum.OperationalProbabilistic.Framework.EffectsAndPreparations.GSLCore
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Topology.Sequences
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Quantum.OperationalProbabilistic.Framework.FiniteIIDPMF.GSLCore
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Quantum.OperationalProbabilistic.Framework.OrderedConeMaxRelativeEntropy.GSLCore
import Quantum.QuantumModel.NativeNoCloning.GSLCore
import Quantum.QuantumModel.NativeMeasuredRelativeEntropy.GSLCore
import Quantum.QuantumModel.NativeFidelity.GSLCore
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Quantum.QuantumMechanics.BridgeCertificates
import Quantum.QuantumEntropy.HaarUnitaryLM.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiUmegakiKWExtra.GSLCore
import Quantum.QuantumEntropy.VonNeumann.Basic
import Quantum.QuantumMechanics.QuantumChannelKWCompat.GSLCore
import Quantum.QuantumModel.HighInterfaces.GSLCore
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Quantum.OperationalProbabilistic.Framework.TestingRegionDecisionDefinitions.GSLCore
import Quantum.OperationalProbabilistic.Framework.QuantumRelativeEntropyLaws.GSLCore
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup


/-!
# Khatri--Wilde hypothesis-testing relative entropy

This file formalizes the finite-dimensional core and basic properties of the
hypothesis-testing relative entropy from Khatri--Wilde,
arXiv:2011.04672v2, `entropies.tex:6589--6951`.  The source's Hilbert-space
operators are represented by `Sys`, `Operator`, and `DensityMatrix`; the
public definitions are totalized to an arbitrary native operator in the
second argument.  Results carrying an operational or divergence
interpretation impose positive semidefiniteness explicitly; outside that
domain, only the declared algebraic extension is intended.  Base two and
finite negative values are retained through `OPT.binaryNegLog2` and `EReal`.

Nonnegative conversion uses `Real.toNNReal`.
-/

noncomputable section

open QuantumState
open scoped ENNReal NNReal ComplexOrder MatrixOrder Topology
open Filter

namespace QuantumModel
namespace NativeHypothesisTesting

/-- A native binary test effect in finite matrix coordinates.

Source: Khatri--Wilde, arXiv:2011.04672v2, `entropies.tex:6589--6608`.
The operator interval `0 <= Q <= 1` is represented by the existing finite
matrix effect carrier. -/
abbrev Effect (A : Sys) :=
  MatrixHockeyStick.Effect (Fin A.dim)

/-- The real trace pairing of a test effect with a native operator.

Source: Khatri--Wilde, arXiv:2011.04672v2, `entropies.tex:6589--6608`.
-/
def testValue {A : Sys} (Q : Effect A) (X : Operator A) : ℝ :=
  MatrixHockeyStick.pairing Q.1 (operatorEquivMatrix A X)

/-- Tests whose acceptance probability on `rho` is at least `1 - epsilon`.

Source: Khatri--Wilde, arXiv:2011.04672v2, `entropies.tex:6589--6608`.
-/
def FeasibleTest {A : Sys}
    (epsilon : OPT.ProbabilityLevel) (rho : DensityMatrix A) :=
  {Q : Effect A // 1 - epsilon.1 ≤ testValue Q rho.operator}

/-- Minimum type-II acceptance over native feasible effects.

Source: Khatri--Wilde, arXiv:2011.04672v2, Definition at
`entropies.tex:6589--6608`.  Nonnegative conversion uses `Real.toNNReal`. -/
noncomputable def betaEpsilon {A : Sys}
    (epsilon : OPT.ProbabilityLevel) (rho : DensityMatrix A)
    (sigma : Operator A) : ℝ≥0 :=
  sInf (Set.range fun Q : FeasibleTest epsilon rho =>
    Real.toNNReal (testValue Q.1 sigma))

/-- Base-two hypothesis-testing relative entropy.

Source: Khatri--Wilde, arXiv:2011.04672v2, Definition at
`entropies.tex:6589--6608`. -/
noncomputable def hypothesisTestingDiv {A : Sys}
    (epsilon : OPT.ProbabilityLevel) (rho : DensityMatrix A)
    (sigma : Operator A) : EReal :=
  OPT.binaryNegLog2 (betaEpsilon epsilon rho sigma)

/-- Predicate saying that a native effect attains the constrained minimum.

Source: Khatri--Wilde, arXiv:2011.04672v2, `entropies.tex:6675--6764`.
Nonnegative conversion uses `Real.toNNReal`. -/
def IsBetaOptimal {A : Sys}
    (epsilon : OPT.ProbabilityLevel) (rho : DensityMatrix A)
    (sigma : Operator A) (Q : Effect A) : Prop :=
  1 - epsilon.1 ≤ testValue Q rho.operator ∧
    Real.toNNReal (testValue Q sigma) = betaEpsilon epsilon rho sigma

theorem Internal.matrixEffect_to_povmElement {A : Sys} (Q : Effect A) :
    NativeNoCloning.POVMElement ((operatorEquivMatrix A).symm Q.1) := by
  constructor
  · apply (QuantumChannel.starAlgEquiv_nonneg_iff
      (operatorEquivMatrix A)).mp
    rw [(operatorEquivMatrix A).apply_symm_apply]
    exact Matrix.nonneg_iff_posSemidef.mpr Q.2.1
  · rw [← sub_nonneg]
    have hmat : 0 ≤ (1 : Matrix (Fin A.dim) (Fin A.dim) ℂ) - Q.1 :=
      Matrix.nonneg_iff_posSemidef.mpr Q.2.2
    have hop := (QuantumChannel.starAlgEquiv_nonneg_iff
      (operatorEquivMatrix A).symm).mpr hmat
    simpa using hop

private def identityEffect (A : Sys) : Effect A := by
  refine ⟨1, ?_⟩
  exact ⟨Matrix.PosSemidef.one, by simpa using
    (Matrix.PosSemidef.zero :
      (0 : Matrix (Fin A.dim) (Fin A.dim) ℂ).PosSemidef)⟩

private def zeroEffect (A : Sys) : Effect A := by
  refine ⟨0, ?_⟩
  exact ⟨Matrix.PosSemidef.zero, by simpa using
    (Matrix.PosSemidef.one :
      (1 : Matrix (Fin A.dim) (Fin A.dim) ℂ).PosSemidef)⟩

@[simp] private theorem testValue_identity {A : Sys} (X : Operator A) :
    testValue (identityEffect A) X = (Tr X).re := by
  unfold testValue MatrixHockeyStick.pairing identityEffect
  rw [one_mul]
  have htrace : Matrix.trace (operatorEquivMatrix A X) = Tr X := by
    rw [LinearMap.trace_eq_matrix_trace (R := ℂ) (b := spaceBasis A)]
    rfl
  exact congrArg Complex.re htrace

@[simp] private theorem testValue_zero {A : Sys} (X : Operator A) :
    testValue (zeroEffect A) X = 0 := by
  simp [testValue, MatrixHockeyStick.pairing, zeroEffect]

/-- The constrained native test carrier is nonempty.

Source: Khatri--Wilde, arXiv:2011.04672v2, `entropies.tex:6589--6608`.
The identity effect is feasible at every public error level. -/
theorem feasibleTest_nonempty {A : Sys}
    (epsilon : OPT.ProbabilityLevel) (rho : DensityMatrix A) :
    Nonempty (FeasibleTest epsilon rho) := by
  refine ⟨⟨identityEffect A, ?_⟩⟩
  rw [testValue_identity, rho.trace_one]
  norm_num
  exact epsilon.2.1

private def matrixEffectCarrier (A : Sys) :
    Set (Matrix (Fin A.dim) (Fin A.dim) ℂ) :=
  {Q | MatrixHockeyStick.IsEffect Q}

private def operatorEffectCarrier (A : Sys) : Set (Operator A) :=
  {E | 0 ≤ E ∧ E ≤ LinearMap.id}

private theorem operatorEffectCarrier_isClosed (A : Sys) :
    IsClosed (operatorEffectCarrier A) := by
  change IsClosed
    ({E : Operator A | 0 ≤ E} ∩
      {E : Operator A | E ≤ LinearMap.id})
  exact (isClosed_le continuous_const continuous_id).inter
    (isClosed_le continuous_id continuous_const)

private theorem operatorEffectCarrier_isBounded (A : Sys) :
    Bornology.IsBounded (operatorEffectCarrier A) := by
  apply Bornology.IsBounded.subset
    (Metric.isBounded_closedBall : Bornology.IsBounded
      (Metric.closedBall
        (0 : Operator A) 1))
  intro E hE
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg E hE.1).2 hE.2

private theorem operatorEffectCarrier_isCompact (A : Sys) :
    IsCompact (operatorEffectCarrier A) := by
  letI : FiniteDimensional ℂ (Operator A) := by infer_instance
  letI : ProperSpace (Operator A) := FiniteDimensional.proper ℂ _
  exact Metric.isCompact_of_isClosed_isBounded
    (operatorEffectCarrier_isClosed A) (operatorEffectCarrier_isBounded A)

private theorem matrixEffectCarrier_isCompact (A : Sys) :
    IsCompact (matrixEffectCarrier A) := by
  have heq : matrixEffectCarrier A =
      operatorEquivMatrix A '' operatorEffectCarrier A := by
    ext Q
    constructor
    · intro hQ
      let Qe : Effect A := ⟨Q, hQ⟩
      refine ⟨(operatorEquivMatrix A).symm Q, ?_, ?_⟩
      · exact Internal.matrixEffect_to_povmElement Qe
      · exact (operatorEquivMatrix A).apply_symm_apply Q
    · rintro ⟨E, hE, rfl⟩
      constructor
      · exact Matrix.nonneg_iff_posSemidef.mp
          ((QuantumChannel.starAlgEquiv_nonneg_iff
            (operatorEquivMatrix A)).mpr hE.1)
      · apply Matrix.nonneg_iff_posSemidef.mp
        change 0 ≤ (1 : Matrix (Fin A.dim) (Fin A.dim) ℂ) -
          operatorEquivMatrix A E
        rw [← map_one (operatorEquivMatrix A), ← map_sub]
        exact (QuantumChannel.starAlgEquiv_nonneg_iff
          (operatorEquivMatrix A)).mpr (sub_nonneg.mpr hE.2)
  rw [heq]
  have hcontinuous : Continuous (operatorEquivMatrix A) :=
    (operatorEquivMatrix A).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
  exact (operatorEffectCarrier_isCompact A).image hcontinuous

private noncomputable instance effectCompactSpace (A : Sys) :
    CompactSpace (Effect A) := by
  change CompactSpace (matrixEffectCarrier A)
  exact isCompact_iff_compactSpace.mp (matrixEffectCarrier_isCompact A)

theorem Internal.testValue_continuous {A : Sys} (X : Operator A) :
    Continuous (fun Q : Effect A => testValue Q X) := by
  unfold testValue MatrixHockeyStick.pairing
  fun_prop

private instance feasibleTestTopologicalSpace {A : Sys}
    (epsilon : OPT.ProbabilityLevel) (rho : DensityMatrix A) :
    TopologicalSpace (FeasibleTest epsilon rho) :=
  TopologicalSpace.induced
    (fun Q : FeasibleTest epsilon rho => Q.1)
    (inferInstance : TopologicalSpace (Effect A))

private noncomputable instance feasibleTestCompactSpace {A : Sys}
    (epsilon : OPT.ProbabilityLevel) (rho : DensityMatrix A) :
    CompactSpace (FeasibleTest epsilon rho) := by
  have hclosed : IsClosed
      {Q : Effect A | 1 - epsilon.1 ≤ testValue Q rho.operator} :=
    isClosed_le continuous_const (Internal.testValue_continuous rho.operator)
  have hcompact : IsCompact
      {Q : Effect A | 1 - epsilon.1 ≤ testValue Q rho.operator} :=
    isCompact_univ.of_isClosed_subset hclosed (Set.subset_univ _)
  change CompactSpace
    {Q : Effect A | 1 - epsilon.1 ≤ testValue Q rho.operator}
  exact isCompact_iff_compactSpace.mp hcompact

private theorem betaEpsilon_range_bddBelow {A : Sys}
    (epsilon : OPT.ProbabilityLevel) (rho : DensityMatrix A)
    (sigma : Operator A) :
    BddBelow (Set.range fun Q : FeasibleTest epsilon rho =>
      Real.toNNReal (testValue Q.1 sigma)) :=
  ⟨0, fun _ _ => bot_le⟩

theorem Internal.betaEpsilon_le_objective {A : Sys}
    (epsilon : OPT.ProbabilityLevel) (rho : DensityMatrix A)
    (sigma : Operator A) (Q : FeasibleTest epsilon rho) :
    betaEpsilon epsilon rho sigma ≤
      Real.toNNReal (testValue Q.1 sigma) := by
  unfold betaEpsilon
  exact csInf_le (betaEpsilon_range_bddBelow epsilon rho sigma) ⟨Q, rfl⟩

/-- A positive right-hand operator admits a native test attaining
`betaEpsilon`.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:6675--6764`.  Attainment is proved from the closed bounded
finite-dimensional effect interval and continuity of the trace objective;
it is not assumed as an axiom or producer field. -/
theorem exists_betaOptimal {A : Sys}
    (epsilon : OPT.ProbabilityLevel) (rho : DensityMatrix A)
    (sigma : Operator A) (hsigma : 0 ≤ sigma) :
    ∃ Q : Effect A, IsBetaOptimal epsilon rho sigma Q := by
  have _hsigmaWitness : 0 ≤ sigma := hsigma
  letI : Nonempty (FeasibleTest epsilon rho) :=
    feasibleTest_nonempty epsilon rho
  let f : FeasibleTest epsilon rho → ℝ≥0 := fun Q =>
    Real.toNNReal (testValue Q.1 sigma)
  have hf : Continuous f :=
    continuous_real_toNNReal.comp
      ((Internal.testValue_continuous sigma).comp continuous_subtype_val)
  rcases isCompact_univ.exists_isMinOn
      (Set.univ_nonempty : (Set.univ : Set (FeasibleTest epsilon rho)).Nonempty)
      hf.continuousOn with ⟨Q, _hQuniv, hQmin⟩
  have hQeq : f Q = sInf (Set.range f) := by
    apply le_antisymm
    · apply le_csInf (Set.range_nonempty f)
      intro y hy
      rcases hy with ⟨R, rfl⟩
      exact hQmin (Set.mem_univ R)
    · exact csInf_le (betaEpsilon_range_bddBelow epsilon rho sigma) ⟨Q, rfl⟩
  refine ⟨Q.1, Q.2, ?_⟩
  exact hQeq

private def scaledEffect {A : Sys} (t : ℝ) (Q : Effect A)
    (ht : 0 ≤ t) (ht_one : t ≤ 1) : Effect A := by
  refine ⟨(t : ℂ) • Q.1, ?_⟩
  constructor
  · exact Matrix.PosSemidef.smul (α := ℝ) Q.2.1 ht
  · have hsum :=
      (Matrix.PosSemidef.smul (α := ℝ) Q.2.1
        (sub_nonneg.mpr ht_one)).add Q.2.2
    convert hsum using 1
    ext i j
    change
      (1 : Matrix (Fin A.dim) (Fin A.dim) ℂ) i j -
          (t : ℂ) * Q.1 i j =
        ((1 - t : ℝ) : ℂ) * Q.1 i j +
          ((1 : Matrix (Fin A.dim) (Fin A.dim) ℂ) i j - Q.1 i j)
    push_cast
    ring

private theorem testValue_scaledEffect {A : Sys} (t : ℝ) (Q : Effect A)
    (ht : 0 ≤ t) (ht_one : t ≤ 1) (X : Operator A) :
    testValue (scaledEffect t Q ht ht_one) X = t * testValue Q X := by
  unfold testValue MatrixHockeyStick.pairing scaledEffect
  rw [Matrix.smul_mul, Matrix.trace_smul]
  simp [Complex.mul_re]

theorem Internal.testValue_nonneg {A : Sys} (Q : Effect A)
    (X : Operator A) (hX : 0 ≤ X) :
    0 ≤ testValue Q X := by
  apply MatrixHockeyStick.trace_mul_re_nonneg_of_posSemidef Q.2.1
  exact Matrix.nonneg_iff_posSemidef.mp
    ((QuantumChannel.starAlgEquiv_nonneg_iff
      (operatorEquivMatrix A)).mpr hX)

/-- An optimal native test can be chosen with exact acceptance
`1 - epsilon`.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:6675--6764`.  Starting from a compactness optimizer, scalar
shrinkage makes the acceptance constraint exact while positivity of `sigma`
prevents the type-II objective from increasing. -/
theorem exists_betaOptimal_acceptance_eq {A : Sys}
    (epsilon : OPT.ProbabilityLevel) (rho : DensityMatrix A)
    (sigma : Operator A) (hsigma : 0 ≤ sigma) :
    ∃ Q : Effect A,
      IsBetaOptimal epsilon rho sigma Q ∧
      testValue Q rho.operator = 1 - epsilon.1 := by
  have hbase : 0 ≤ 1 - epsilon.1 := sub_nonneg.mpr epsilon.2.2
  by_cases hbase_zero : 1 - epsilon.1 = 0
  · let Q : Effect A := zeroEffect A
    have hQfeasible : 1 - epsilon.1 ≤ testValue Q rho.operator := by
      rw [hbase_zero, testValue_zero]
    have hbeta_zero : betaEpsilon epsilon rho sigma = 0 := by
      apply le_antisymm
      · have hle := Internal.betaEpsilon_le_objective epsilon rho sigma
            (⟨Q, hQfeasible⟩ : FeasibleTest epsilon rho)
        simpa [Q] using hle
      · exact bot_le
    refine ⟨Q, ⟨hQfeasible, ?_⟩, ?_⟩
    · simp [Q, hbeta_zero]
    · simp [Q, hbase_zero]
  · obtain ⟨Q, hQoptimal⟩ :=
      exists_betaOptimal epsilon rho sigma hsigma
    let a : ℝ := testValue Q rho.operator
    have hbase_pos : 0 < 1 - epsilon.1 :=
      lt_of_le_of_ne hbase (Ne.symm hbase_zero)
    have ha_pos : 0 < a := hbase_pos.trans_le hQoptimal.1
    let t : ℝ := (1 - epsilon.1) / a
    have ht : 0 ≤ t := div_nonneg hbase ha_pos.le
    have ht_one : t ≤ 1 := (div_le_one ha_pos).mpr hQoptimal.1
    let R : Effect A := scaledEffect t Q ht ht_one
    have hRaccept : testValue R rho.operator = 1 - epsilon.1 := by
      rw [show R = scaledEffect t Q ht ht_one by rfl,
        testValue_scaledEffect]
      dsimp only [t, a]
      exact div_mul_cancel₀ (1 - epsilon.1) ha_pos.ne'
    have hRfeasible : 1 - epsilon.1 ≤ testValue R rho.operator :=
      hRaccept.ge
    have hRobj_le :
        Real.toNNReal (testValue R sigma) ≤ betaEpsilon epsilon rho sigma := by
      rw [show R = scaledEffect t Q ht ht_one by rfl,
        testValue_scaledEffect]
      have hQsigma : 0 ≤ testValue Q sigma := Internal.testValue_nonneg Q sigma hsigma
      calc
        Real.toNNReal (t * testValue Q sigma) ≤
            Real.toNNReal (testValue Q sigma) :=
          Real.toNNReal_monotone (by nlinarith)
        _ = betaEpsilon epsilon rho sigma := hQoptimal.2
    have hbeta_le_Robj :
        betaEpsilon epsilon rho sigma ≤
          Real.toNNReal (testValue R sigma) :=
      Internal.betaEpsilon_le_objective epsilon rho sigma
        (⟨R, hRfeasible⟩ : FeasibleTest epsilon rho)
    refine ⟨R, ⟨hRfeasible, le_antisymm hRobj_le hbeta_le_Robj⟩,
      hRaccept⟩

def Internal.matrixEffectOfPOVMElement {A : Sys} (E : Operator A)
    (hE : NativeNoCloning.POVMElement E) : Effect A := by
  refine ⟨operatorEquivMatrix A E, ?_⟩
  constructor
  · exact Matrix.nonneg_iff_posSemidef.mp
      ((QuantumChannel.starAlgEquiv_nonneg_iff
        (operatorEquivMatrix A)).mpr hE.1)
  · apply Matrix.nonneg_iff_posSemidef.mp
    change 0 ≤ (1 : Matrix (Fin A.dim) (Fin A.dim) ℂ) -
      operatorEquivMatrix A E
    rw [← map_one (operatorEquivMatrix A), ← map_sub]
    exact (QuantumChannel.starAlgEquiv_nonneg_iff
      (operatorEquivMatrix A)).mpr (sub_nonneg.mpr hE.2)

/-- Testing a density matrix against itself has minimum acceptance exactly
`1 - epsilon`.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:6807--6838`.  Nonnegative conversion uses `Real.toNNReal`. -/
theorem betaEpsilon_self {A : Sys}
    (epsilon : OPT.ProbabilityLevel) (rho : DensityMatrix A) :
    betaEpsilon epsilon rho rho.operator =
      Real.toNNReal (1 - epsilon.1) := by
  obtain ⟨Q, hQoptimal, hQaccept⟩ :=
    exists_betaOptimal_acceptance_eq epsilon rho rho.operator rho.nonneg
  rw [← hQoptimal.2, hQaccept]

/-- Self hypothesis-testing divergence is the calibrated binary base-two
negative logarithm of `1 - epsilon`.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:6807--6838`.  Nonnegative conversion uses `Real.toNNReal`. -/
theorem hypothesisTestingDiv_self {A : Sys}
    (epsilon : OPT.ProbabilityLevel) (rho : DensityMatrix A) :
    hypothesisTestingDiv epsilon rho rho.operator =
      OPT.binaryNegLog2 (Real.toNNReal (1 - epsilon.1)) := by
  rw [hypothesisTestingDiv, betaEpsilon_self]

/-- Increasing the permitted type-I error can only decrease the minimum
type-II acceptance.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:6807--6861`. -/
theorem betaEpsilon_antitone_epsilon {A : Sys}
    {epsilon epsilon' : OPT.ProbabilityLevel}
    (h : epsilon.1 ≤ epsilon'.1)
    (rho : DensityMatrix A) (sigma : Operator A) :
    betaEpsilon epsilon' rho sigma ≤ betaEpsilon epsilon rho sigma := by
  letI : Nonempty (FeasibleTest epsilon rho) :=
    feasibleTest_nonempty epsilon rho
  change
    sInf (Set.range fun Q : FeasibleTest epsilon' rho =>
      Real.toNNReal (testValue Q.1 sigma)) ≤
    sInf (Set.range fun Q : FeasibleTest epsilon rho =>
      Real.toNNReal (testValue Q.1 sigma))
  apply le_csInf (Set.range_nonempty _)
  intro y hy
  rcases hy with ⟨Q, rfl⟩
  exact csInf_le (betaEpsilon_range_bddBelow epsilon' rho sigma)
    ⟨⟨Q.1, le_trans (by linarith) Q.2⟩, rfl⟩

theorem Internal.binaryNegLog2_antitone : Antitone OPT.binaryNegLog2 := by
  intro p q hpq
  by_cases hp : p = 0
  · rw [hp, OPT.binaryNegLog2_zero]
    exact le_top
  by_cases hq : q = 0
  · have : p = 0 := nonpos_iff_eq_zero.mp (hq ▸ hpq)
    exact (hp this).elim
  simp only [OPT.binaryNegLog2, if_neg hp, if_neg hq,
    EReal.coe_le_coe_iff]
  apply neg_le_neg
  exact Real.logb_le_logb_of_le (b := 2) (by norm_num)
    (by exact_mod_cast (pos_iff_ne_zero.mpr hp))
    (NNReal.coe_le_coe.mpr hpq)

/-- Increasing the permitted type-I error can only increase the
hypothesis-testing divergence.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:6807--6861`. -/
theorem hypothesisTestingDiv_mono_epsilon {A : Sys}
    {epsilon epsilon' : OPT.ProbabilityLevel}
    (h : epsilon.1 ≤ epsilon'.1)
    (rho : DensityMatrix A) (sigma : Operator A) :
    hypothesisTestingDiv epsilon rho sigma ≤
      hypothesisTestingDiv epsilon' rho sigma := by
  apply Internal.binaryNegLog2_antitone
  exact betaEpsilon_antitone_epsilon h rho sigma

private theorem pullbackEffect_add {A B : Sys}
    (K : KrausFamily A B) (E F : Operator B) :
    NativeMeasuredRelativeEntropy.pullbackEffect K (E + F) =
      NativeMeasuredRelativeEntropy.pullbackEffect K E +
        NativeMeasuredRelativeEntropy.pullbackEffect K F := by
  letI := K.fintypeIndex
  letI := K.decidableEqIndex
  unfold NativeMeasuredRelativeEntropy.pullbackEffect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  ext x
  simp [LinearMap.comp_apply]

private noncomputable def pullbackMatrixEffect {A B : Sys}
    (Q : Effect B) (Phi : NativeNoCloning.Superoperator A B)
    (hPhi : IsCPTP Phi) : Effect A := by
  let K := NativeMeasuredRelativeEntropy.channelKrausFamily Phi hPhi
  let E : Operator B := (operatorEquivMatrix B).symm Q.1
  have hE : NativeNoCloning.POVMElement E := Internal.matrixEffect_to_povmElement Q
  let Ein : Operator A :=
    NativeMeasuredRelativeEntropy.pullbackEffect K E
  have hEin_nonneg : 0 ≤ Ein :=
    NativeMeasuredRelativeEntropy.KrausFamily.pullbackEffect_nonneg K hE.1
  have hcomplement_nonneg : 0 ≤
      NativeMeasuredRelativeEntropy.pullbackEffect K
        ((LinearMap.id : Operator B) - E) :=
    NativeMeasuredRelativeEntropy.KrausFamily.pullbackEffect_nonneg K
      (sub_nonneg.mpr hE.2)
  have hsum : Ein +
      NativeMeasuredRelativeEntropy.pullbackEffect K
        ((LinearMap.id : Operator B) - E) = LinearMap.id := by
    calc
      Ein + NativeMeasuredRelativeEntropy.pullbackEffect K
          ((LinearMap.id : Operator B) - E) =
          NativeMeasuredRelativeEntropy.pullbackEffect K
            (E + ((LinearMap.id : Operator B) - E)) := by
        exact (pullbackEffect_add K E ((LinearMap.id : Operator B) - E)).symm
      _ = NativeMeasuredRelativeEntropy.pullbackEffect K LinearMap.id := by
        congr 1
        abel
      _ = K.normalization :=
        NativeMeasuredRelativeEntropy.KrausFamily.pullbackEffect_id K
      _ = LinearMap.id :=
        NativeMeasuredRelativeEntropy.channelKrausFamily_normalization Phi hPhi
  have hEin_le : Ein ≤ LinearMap.id := by
    rw [← hsum]
    exact le_add_of_nonneg_right hcomplement_nonneg
  exact Internal.matrixEffectOfPOVMElement Ein ⟨hEin_nonneg, hEin_le⟩

theorem Internal.testValue_matrixEffectOfPOVMElement_operator {A : Sys}
    (E : Operator A) (hE : NativeNoCloning.POVMElement E)
    (X : Operator A) :
    testValue (Internal.matrixEffectOfPOVMElement E hE) X =
      (Tr (E.comp X)).re := by
  unfold testValue MatrixHockeyStick.pairing Internal.matrixEffectOfPOVMElement
  rw [LinearMap.trace_eq_matrix_trace (R := ℂ) (b := spaceBasis A),
    LinearMap.toMatrix_comp (spaceBasis A) (spaceBasis A) (spaceBasis A)]
  rfl

theorem Internal.testValue_eq_trace_effectOperator {A : Sys}
    (Q : Effect A) (X : Operator A) :
    testValue Q X =
      (Tr (((operatorEquivMatrix A).symm Q.1).comp X)).re := by
  unfold testValue MatrixHockeyStick.pairing
  rw [LinearMap.trace_eq_matrix_trace (R := ℂ) (b := spaceBasis A),
    LinearMap.toMatrix_comp (spaceBasis A) (spaceBasis A) (spaceBasis A)]
  change
    (Matrix.trace (Q.1 * operatorEquivMatrix A X)).re =
      (Matrix.trace
        (operatorEquivMatrix A ((operatorEquivMatrix A).symm Q.1) *
          operatorEquivMatrix A X)).re
  rw [(operatorEquivMatrix A).apply_symm_apply]

private theorem testValue_pullbackMatrixEffect {A B : Sys}
    (Q : Effect B) (Phi : NativeNoCloning.Superoperator A B)
    (hPhi : IsCPTP Phi) (X : Operator A) :
    testValue (pullbackMatrixEffect Q Phi hPhi) X =
      testValue Q (HPHom.toRawSuperoperator Phi X) := by
  let K := NativeMeasuredRelativeEntropy.channelKrausFamily Phi hPhi
  let E : Operator B := (operatorEquivMatrix B).symm Q.1
  let Ein : Operator A :=
    NativeMeasuredRelativeEntropy.pullbackEffect K E
  have htrace := NativeMeasuredRelativeEntropy.trace_pullbackEffect K E X
  have hmap : HPHom.toRawSuperoperator K.map X =
      HPHom.toRawSuperoperator Phi X := by
    rw [NativeMeasuredRelativeEntropy.channelKrausFamily_map]
  unfold pullbackMatrixEffect
  rw [Internal.testValue_matrixEffectOfPOVMElement_operator,
    Internal.testValue_eq_trace_effectOperator]
  change (Tr (Ein.comp X)).re =
    (Tr (E.comp (HPHom.toRawSuperoperator Phi X))).re
  rw [htrace, hmap]

/-- Native constrained type-II error is monotone under a CPTP channel.

Source: Khatri--Wilde, arXiv:2011.04672v2, data processing theorem at
`entropies.tex:6765--6806`.  The proof pulls an output effect back through a
normalized Kraus family and uses trace duality. -/
theorem betaEpsilon_mono_of_isCPTP
    {A B : Sys} (epsilon : OPT.ProbabilityLevel)
    (rho : DensityMatrix A) (sigma : Operator A) (hsigma : 0 ≤ sigma)
    (Phi : NativeNoCloning.Superoperator A B) (hPhi : IsCPTP Phi) :
    betaEpsilon epsilon rho sigma ≤
      betaEpsilon epsilon
        (NativeFidelity.channelApply rho Phi hPhi)
        (HPHom.toRawSuperoperator Phi sigma) := by
  have hposPhi :
      QuantumChannel.IsPositiveMap (HPHom.toRawSuperoperator Phi) :=
    QuantumChannel.completelyPositive_to_positiveMap _ hPhi.1
  have hsigmaOut : 0 ≤ HPHom.toRawSuperoperator Phi sigma :=
    hposPhi sigma hsigma
  obtain ⟨Q, hQ⟩ := exists_betaOptimal epsilon
    (NativeFidelity.channelApply rho Phi hPhi)
    (HPHom.toRawSuperoperator Phi sigma) hsigmaOut
  let R : Effect A := pullbackMatrixEffect Q Phi hPhi
  have hRfeasible : 1 - epsilon.1 ≤ testValue R rho.operator := by
    rw [show R = pullbackMatrixEffect Q Phi hPhi by rfl,
      testValue_pullbackMatrixEffect,
      ← NativeFidelity.channelApply_operator rho Phi hPhi]
    exact hQ.1
  calc
    betaEpsilon epsilon rho sigma ≤ Real.toNNReal (testValue R sigma) :=
      Internal.betaEpsilon_le_objective epsilon rho sigma ⟨R, hRfeasible⟩
    _ = Real.toNNReal
        (testValue Q (HPHom.toRawSuperoperator Phi sigma)) := by
      rw [show R = pullbackMatrixEffect Q Phi hPhi by rfl,
        testValue_pullbackMatrixEffect]
    _ = betaEpsilon epsilon
        (NativeFidelity.channelApply rho Phi hPhi)
        (HPHom.toRawSuperoperator Phi sigma) := hQ.2

/-- Hypothesis-testing divergence satisfies CPTP data processing.

Source: Khatri--Wilde, arXiv:2011.04672v2, data processing theorem at
`entropies.tex:6765--6806`. -/
theorem hypothesisTestingDiv_mono_of_isCPTP
    {A B : Sys} (epsilon : OPT.ProbabilityLevel)
    (rho : DensityMatrix A) (sigma : Operator A) (hsigma : 0 ≤ sigma)
    (Phi : NativeNoCloning.Superoperator A B) (hPhi : IsCPTP Phi) :
    hypothesisTestingDiv epsilon
        (NativeFidelity.channelApply rho Phi hPhi)
        (HPHom.toRawSuperoperator Phi sigma) ≤
      hypothesisTestingDiv epsilon rho sigma := by
  apply Internal.binaryNegLog2_antitone
  exact betaEpsilon_mono_of_isCPTP epsilon rho sigma hsigma Phi hPhi


end NativeHypothesisTesting
end QuantumModel
