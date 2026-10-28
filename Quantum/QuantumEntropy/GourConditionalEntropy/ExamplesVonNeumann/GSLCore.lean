import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesDefinitions.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.Definitions.GSLCore
import Quantum.QuantumEntropy.GourQuantumRelativeEntropyBasicProperties.GSLCore
import Quantum.QuantumMechanics.DiagonalDensity.GSLCore
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
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
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
import Quantum.QuantumEntropy.GourSemiCausalMemory.GSLCore
import Quantum.OperationalProbabilistic.Framework.QuantumRelativeEntropyLaws.GSLCore
import Mathlib.Topology.Order.AtTopBotIxx
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiOrder.GSLCore
import Quantum.OperationalProbabilistic.Framework.MeasurementEntropy.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiDivergence.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiRelativeEntropyLimits.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiPowerFDivBridge.GSLCore
import Quantum.QuantumEntropy.GourQuantumMaxRelativeEntropy.GSLCore
import Quantum.QuantumMechanics.SpectralPinching.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.FromRelativePreparation.GSLCore
import Quantum.QuantumEntropy.CFCDeriv
import Quantum.QuantumEntropy.Gour.UmegakiDPIAdapter.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivergence.GSLCore
import Quantum.QuantumEntropy.PetzRenyiSpectralReduction.GSLCore
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.Provider
import Quantum.QuantumEntropy.Gour.PetzQuantumRenyiDivergence.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiBase.Umegaki.Reduction
import Quantum.QuantumEntropy.UmegakiDPI.NonNegLift
import Quantum.TraceInequality.LownerHeinzTheorem
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
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
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.Subadditive
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.PNat.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Quantum.OperationalProbabilistic.Framework.EffectsAndPreparations.GSLCore
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Quantum.OperationalProbabilistic.Framework.StateNorms.GSLCore
import Quantum.QuantumEntropy.PinchingTensorSpectrum.GSLCore
import Quantum.QuantumMechanics.DensityOperator.GSLCore
import Quantum.QuantumEntropy.GourShortedOperator.GSLCore
import Quantum.QuantumEntropy.PetzSupportRpowContinuity.GSLCore
import Quantum.QuantumEntropy.QuantumFDivergence.GSLCore
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiRelativeEntropy.GSLCore
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Quantum.QuantumEntropy.PetzRenyiEndpointIdentities.GSLCore
import Quantum.QuantumMechanics.OuterProduct.GSLCore
import Mathlib.Data.Sum.Interval

open QuantumState QuantumChannel GourConditionalEntropy GourChoi GourSemiCausal
open scoped TensorProduct ComplexOrder BigOperators ENNReal Topology

universe u

namespace GourConditionalEntropy

section

private theorem w38c01_spectral_entropy {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : {X : L A // IsDensity X}) :
    vonNeumannEntropy ρ.1 = -∑ i, OPT.petzRenyiSpectralEigenvalue ρ.1 ρ.2 i *
      Real.logb 2 (OPT.petzRenyiSpectralEigenvalue ρ.1 ρ.2 i) := by
  rw [vonNeumannEntropy, OPT.petzRenyiTraceMulLogSelf_eq_spectralSum ρ.1 ρ.2]
  simp only [Real.logb, ← mul_div_assoc, ← Finset.sum_div, neg_div]

private theorem w38c01_bits_laws : OPT.GourMatrixRelativeEntropyLaws.{u} umegakiBits := by
  have laws := OPT.petzOrderOneLaws_from_umegakiDPI.{u, u}
  refine ⟨?_, ?_, ?_⟩
  · intro H K _ _ _ _ E ρ σ hρ hσ
    simpa only [OPT.petzQuantumRenyiDivergence_one_eq_umegakiRelEntropyNN,
      umegakiBits] using laws.dataProcessing E ρ σ hρ hσ
  · intro H K _ _ _ _ _ ρ₁ σ₁ ρ₂ σ₂ hρ₁ hσ₁ hρ₂ hσ₂
    simpa only [OPT.petzQuantumRenyiDivergence_one_eq_umegakiRelEntropyNN,
      umegakiBits] using laws.tensorAdditivity ρ₁ σ₁ ρ₂ σ₂ hρ₁ hσ₁ hρ₂ hσ₂
  · intro H _ _ pair
    simpa only [OPT.petzQuantumRenyiDivergence_one_eq_umegakiRelEntropyNN,
      umegakiBits] using laws.binaryNormalization pair

private theorem w38c01_bits_trace {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : L A) (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hsupp : SandwichedRenyiRelativeEntropy.suppLE ρ σ) :
    umegakiBits ρ σ hρ hσ =
      (((Tr (ρ * (CFC.log ρ - CFC.log σ))).re / Real.log 2 : ℝ) : EReal) := by
  simp only [umegakiBits, SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN,
    if_pos hsupp, SandwichedRenyiRelativeEntropy.umegakiNorm, hρ.2,
    Complex.one_re, div_one, ← EReal.coe_mul]
  congr 1
  ring

theorem w38_vn_spectral_dictionary :
  (∀ {A : Type u} [Qudit A]
    [Nontrivial A]
    (ρ : {X : L (A) // IsDensity X}),
    vonNeumannEntropy ρ.1 = -∑ i, OPT.petzRenyiSpectralEigenvalue ρ.1 ρ.2 i *
      Real.logb 2 (OPT.petzRenyiSpectralEigenvalue ρ.1 ρ.2 i)) ∧
  (∀ x : ℝ, (0 : ℝ) * Real.logb 2 x = 0) ∧
  OPT.GourMatrixRelativeEntropyLaws.{u} umegakiBits ∧
  (∀ {A : Type u} [Qudit A]
    [Nontrivial A] (ρ σ : L A) (hρ : IsDensity ρ) (hσ : IsDensity σ),
    SandwichedRenyiRelativeEntropy.suppLE ρ σ →
    umegakiBits ρ σ hρ hσ =
      (((Tr (ρ * (CFC.log ρ - CFC.log σ))).re / Real.log 2 : ℝ) : EReal)) := by
  refine ⟨fun ρ => w38c01_spectral_entropy ρ, fun x => zero_mul _, w38c01_bits_laws, ?_⟩
  intro A _ _ ρ σ hρ hσ hsupp
  exact w38c01_bits_trace ρ σ hρ hσ hsupp

end

section

end

section

end

section

end

section

end

section

end

section

end

section

end

section


end

section

end

section

end

section

end

section

end

end GourConditionalEntropy
