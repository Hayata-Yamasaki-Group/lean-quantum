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
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Sum.Interval
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Logic.Equiv.Bool

open QuantumState QuantumChannel GourConditionalEntropy
open scoped TensorProduct ComplexOrder BigOperators ENNReal Topology

universe u

namespace GourConditionalEntropy

private lemma w37c01_support_trace_bounds
    {H : Type u} [Qudit H] [Nontrivial H]
    (ρ σ : {X : L H // IsDensity X}) :
    0 ≤ OPT.petzSupportTracePower 0 ρ.1 σ.1 ∧
      OPT.petzSupportTracePower 0 ρ.1 σ.1 ≤ 1 := by
  classical
  rw [← OPT.classicalSupportOverlapPMF_petzSpectral_toReal_eq ρ.1 σ.1 ρ.2 σ.2]
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have hle : OPT.classicalSupportOverlapPMF
      (OPT.petzSpectralP ρ.1 σ.1 ρ.2 σ.2) (OPT.petzSpectralQ ρ.1 σ.1 ρ.2 σ.2) ≤ 1 := by
    unfold OPT.classicalSupportOverlapPMF
    calc
      _ ≤ ∑ i, OPT.petzSpectralQ ρ.1 σ.1 ρ.2 σ.2 i := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs <;> simp
      _ = 1 := by
        simpa only [tsum_fintype] using (OPT.petzSpectralQ ρ.1 σ.1 ρ.2 σ.2).tsum_coe
  simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hle

private lemma w37c01_divergence_nonnegative
    (D : OPT.GourMatrixStateDivergence.{u}) (laws : OPT.GourMatrixRelativeEntropyLaws D)
    {H : Type u} [Qudit H] [Nontrivial H]
    (ρ σ : {X : L H // IsDensity X}) : 0 ≤ D ρ.1 σ.1 ρ.2 σ.2 := by
  apply le_trans _ (OPT.gourQuantumRelativeEntropy_min_max_bounds laws ρ σ).1
  unfold OPT.quantumMinRelativeEntropy
  split_ifs
  · exact le_top
  · apply EReal.coe_nonneg.mpr
    exact neg_nonneg.mpr (Real.logb_nonpos (by norm_num)
      (w37c01_support_trace_bounds ρ σ).1 (w37c01_support_trace_bounds ρ σ).2)

private lemma w37c01_eigenstate_reverse_product
    {H : Type u} [Qudit H] [Nontrivial H]
    (ψ σ : {X : L H // IsDensity X}) (p : ℝ)
    (heigen : σ.1 * ψ.1 = (p : ℂ) • ψ.1) :
    ψ.1 * σ.1 = (p : ℂ) • ψ.1 := by
  have hψ := (IsSelfAdjoint.of_nonneg
    ((LinearMap.nonneg_iff_isPositive _).mpr ψ.2.1)).star_eq
  have hσ := (IsSelfAdjoint.of_nonneg
    ((LinearMap.nonneg_iff_isPositive _).mpr σ.2.1)).star_eq
  have h := congrArg star heigen
  simpa only [star_mul, star_smul, hψ, hσ, Complex.star_def, Complex.conj_ofReal] using h

private lemma w37c01_eigenstate_trace
    {H : Type u} [Qudit H] [Nontrivial H]
    (ψ σ : {X : L H // IsDensity X}) (hidem : IsIdempotentElem ψ.1)
    (p : ℝ) (heigen : σ.1 * ψ.1 = (p : ℂ) • ψ.1) :
    OPT.petzSupportTracePower 0 ψ.1 σ.1 = p := by
  have hprojection : ψ.1.IsSymmetricProjection := ⟨hidem, ψ.2.1.isSymmetric⟩
  obtain ⟨_, hstar⟩ :=
    LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hprojection
  have hpow : CFC.rpow σ.1 1 = σ.1 :=
    CFC.rpow_one σ.1 ((LinearMap.nonneg_iff_isPositive _).mpr σ.2.1)
  unfold OPT.petzSupportTracePower
  rw [OPT.petzSupportRpow_zero, ← hstar, show 1 - (0 : ℝ) = 1 by norm_num,
    OPT.petzSupportRpow_of_ne_zero σ.1 one_ne_zero,
    hpow,
    w37c01_eigenstate_reverse_product ψ σ p heigen, map_smul, ψ.2.2, smul_eq_mul,
    mul_one, Complex.ofReal_re]

private lemma w37c01_eigenstate_domination
    {H : Type u} [Qudit H] [Nontrivial H]
    (ψ σ : {X : L H // IsDensity X}) (hidem : IsIdempotentElem ψ.1)
    (p : ℝ) (hp : 0 < p) (heigen : σ.1 * ψ.1 = (p : ℂ) • ψ.1) :
    ψ.1 ≤ ((2 : ℝ) ^ (-Real.logb 2 p)) • σ.1 := by
  have hψ : IsSelfAdjoint ψ.1 := IsSelfAdjoint.of_nonneg
    ((LinearMap.nonneg_iff_isPositive _).mpr ψ.2.1)
  have hone : IsSelfAdjoint (1 : L H) := IsSelfAdjoint.one (L H)
  have hpos := (hone.sub hψ).conjugate_nonneg
    ((LinearMap.nonneg_iff_isPositive _).mpr σ.2.1)
  have hreverse := w37c01_eigenstate_reverse_product ψ σ p heigen
  have hres : (1 - ψ.1) * σ.1 * (1 - ψ.1) = σ.1 - (p : ℂ) • ψ.1 := by
    rw [sub_mul, one_mul, hreverse, mul_sub, mul_one, sub_mul,
      heigen, smul_mul_assoc, hidem.eq]
    abel
  rw [hres] at hpos
  have hscaled := smul_le_smul_of_nonneg_left (sub_nonneg.mp hpos)
    (inv_nonneg.mpr hp.le)
  have hdom : ψ.1 ≤ p⁻¹ • σ.1 := by
    simpa only [Complex.coe_smul, smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
      using hscaled
  have hpow : (2 : ℝ) ^ (-Real.logb 2 p) = p⁻¹ := by
    rw [Real.rpow_neg (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hp]
  rwa [hpow]

theorem w37_relative_diagonal_calibration :
  ∀ (D : OPT.GourMatrixStateDivergence.{u}),
    OPT.GourMatrixRelativeEntropyLaws D →
    (∀ {H : Type u} [Qudit H] [Nontrivial H]
      (ρ σ : {X : L H // IsDensity X}), 0 ≤ D ρ.1 σ.1 ρ.2 σ.2) ∧
    (∀ {H : Type u} [Qudit H] [Nontrivial H]
      (ρ : {X : L H // IsDensity X}), D ρ.1 ρ.1 ρ.2 ρ.2 = 0) ∧
    (∀ {H : Type u} [Qudit H] [Nontrivial H]
      (ψ σ : {X : L H // IsDensity X}), IsIdempotentElem ψ.1 →
      ∀ p : ℝ, σ.1 * ψ.1 = (p : ℂ) • ψ.1 →
        D ψ.1 σ.1 ψ.2 σ.2 =
          if p = 0 then ⊤ else ((-Real.logb 2 p : ℝ) : EReal)) := by
  intro D laws
  refine ⟨w37c01_divergence_nonnegative D laws, ?_, ?_⟩
  · intro H _ _ ρ
    apply le_antisymm _ (w37c01_divergence_nonnegative D laws ρ ρ)
    apply le_trans (OPT.gourQuantumRelativeEntropy_min_max_bounds laws ρ ρ).2
    have hdom : ρ.1 ≤ ((2 : ℝ) ^ (0 : ℝ)) • ρ.1 := by simp
    simpa only [EReal.coe_zero] using OPT.OrderedCone.maxRelEntropy_le_of_domination hdom
  · intro H _ _ ψ σ hidem p heigen
    have htrace := w37c01_eigenstate_trace ψ σ hidem p heigen
    have hzero : ψ.1 * σ.1 = 0 ↔ p = 0 := by
      rw [← OPT.petzSupportTracePower_zero_eq_zero_iff_mul_eq_zero
        ψ.1 σ.1 ψ.2 σ.2, htrace]
    have hmin : OPT.quantumMinRelativeEntropy ψ.1 σ.1 ψ.2 σ.2 =
        if p = 0 then ⊤ else ((-Real.logb 2 p : ℝ) : EReal) := by
      simp only [OPT.quantumMinRelativeEntropy, hzero, htrace]
    have hlower := (OPT.gourQuantumRelativeEntropy_min_max_bounds laws ψ σ).1
    rw [hmin] at hlower
    apply le_antisymm _ hlower
    by_cases hp : p = 0
    · simp only [if_pos hp]
      exact le_top
    · rw [if_neg hp]
      have hpnonneg : 0 ≤ p := htrace ▸ (w37c01_support_trace_bounds ψ σ).1
      apply le_trans (OPT.gourQuantumRelativeEntropy_min_max_bounds laws ψ σ).2
      exact OPT.OrderedCone.maxRelEntropy_le_of_domination
        (w37c01_eigenstate_domination ψ σ hidem p (lt_of_le_of_ne hpnonneg (Ne.symm hp)) heigen)

end GourConditionalEntropy
