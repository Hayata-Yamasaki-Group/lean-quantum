/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.KW.Distances.HypothesisTestingCore.Basic
import Quantum.QuantumModel.MatrixHockeyStick.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiLMCompat.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiNonNegKWExtra.GSLCore
import Quantum.QuantumModel.NativeMeasuredRelativeEntropy.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiOrder.GSLCore
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.Provider
import Quantum.QuantumEntropy.SandwichedRenyiBase.Umegaki.Reduction
import Quantum.QuantumEntropy.UmegakiDPI.NonNegLift
import Quantum.QuantumModel.NativeFacade.GSLCore
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Quantum.QuantumEntropy.SandwichedRenyiUmegakiKWExtra.GSLCore
import Mathlib.Topology.Bases
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Khatri--Wilde hypothesis-testing comparison bounds

The base-two entropy quantities (Umegaki, sandwiched and Petz Rényi relative entropies, binary
entropy) and the one-shot comparison of the hypothesis-testing relative entropy with the
Umegaki and sandwiched Rényi relative entropies, from Khatri--Wilde, arXiv:2011.04672v2.  The
definitions are totalized to an arbitrary native operator in the second argument; results with
an operational or divergence interpretation impose positive semidefiniteness explicitly.
Logarithms have base two, and extended values are kept in `EReal`.
-/

noncomputable section

open QuantumState
open QuantumChannel HaarUnitary TensorProduct MeasureTheory
open GeneralizedPerspectiveFunction
open scoped ENNReal NNReal ComplexOrder MatrixOrder Topology MeasureTheory
open Filter

namespace QuantumModel
namespace NativeHypothesisTesting

local instance operatorSelfAdjointCFCBounds (A : Sys) :
    NonUnitalContinuousFunctionalCalculus ℝ (Operator A) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance operatorSelfAdjointUnitalCFCBounds (A : Sys) :
    ContinuousFunctionalCalculus ℝ (Operator A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

local instance operatorNonnegSpectrumBounds (A : Sys) :
    NonnegSpectrumClass ℝ (Operator A) :=
  CStarAlgebra.instNonnegSpectrumClass

/-! ## Entropy quantities -/

/-- Umegaki relative entropy in bits for a density operator against an
arbitrary native operator.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:70--75`. -/
noncomputable def umegakiRelEntropyBits {A : Sys}
    (rho : DensityMatrix A) (sigma : Operator A) : EReal :=
  SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN
      rho.operator sigma /
    ((Real.log 2 : ℝ) : EReal)

/-- Sandwiched Rényi divergence in bits, retaining the extended-value
support-mismatch branch.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:2039--2050`. -/
noncomputable def sandwichedRenyiDivBits {A : Sys}
    (alpha : ℝ) (rho : DensityMatrix A) (sigma : Operator A) : EReal :=
  SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN
      alpha rho.operator sigma /
    ((Real.log 2 : ℝ) : EReal)

/-- The Petz trace-power quasi-entropy.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:6855--6905`. -/
noncomputable def petzQuasi {A : Sys}
    (alpha : ℝ) (rho : DensityMatrix A) (sigma : Operator A) : ℝ :=
  (Tr (CFC.rpow rho.operator alpha *
    CFC.rpow sigma (1 - alpha))).re

/-- Petz Rényi divergence in bits.  Orthogonal support is represented by
`top`, rather than being erased through a real logarithm at zero.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:1447--1456`. -/
noncomputable def petzRenyiDivBits {A : Sys}
    (alpha : ℝ) (rho : DensityMatrix A) (sigma : Operator A) : EReal :=
  if petzQuasi alpha rho sigma = 0 then ⊤
  else
    ((Real.logb 2 (petzQuasi alpha rho sigma) /
      (alpha - 1) : ℝ) : EReal)

/-- Binary entropy in bits, with both endpoint values defined as zero.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:6777--6814`. -/
noncomputable def binaryEntropyBits (p : OPT.ProbabilityLevel) : ℝ :=
  if p.1 = 0 ∨ p.1 = 1 then 0
  else
    -p.1 * Real.logb 2 p.1 -
      (1 - p.1) * Real.logb 2 (1 - p.1)

/-! ## One-shot comparison bounds -/

private theorem matrixEffect_to_povmElementBounds {A : Sys} (Q : Effect A) :
    NativeNoCloning.POVMElement ((operatorEquivMatrix A).symm Q.1) := by
  constructor
  · apply (QuantumChannel.starAlgEquiv_nonneg_iff
      (operatorEquivMatrix A)).mp
    rw [(operatorEquivMatrix A).apply_symm_apply]
    exact Matrix.nonneg_iff_posSemidef.mpr Q.2.1
  · rw [← sub_nonneg]
    change 0 ≤ (1 : Operator A) - (operatorEquivMatrix A).symm Q.1
    apply (QuantumChannel.starAlgEquiv_nonneg_iff
      (operatorEquivMatrix A)).mp
    rw [map_sub, map_one, (operatorEquivMatrix A).apply_symm_apply]
    exact Matrix.nonneg_iff_posSemidef.mpr Q.2.2

private theorem testValue_eq_trace_effectOperatorBounds {A : Sys}
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

private noncomputable abbrev binaryPOVMBounds {A : Sys} (Q : Effect A) :
    NativeFidelity.POVM A where
  ι := Fin 2
  effect i := if i = 0 then (operatorEquivMatrix A).symm Q.1
    else LinearMap.id - (operatorEquivMatrix A).symm Q.1
  nonneg i := by
    split
    · exact (matrixEffect_to_povmElementBounds Q).1
    · exact sub_nonneg.mpr (matrixEffect_to_povmElementBounds Q).2
  sum_eq_id := by
    rw [Fin.sum_univ_two]
    simp

private noncomputable def binaryWeightBounds {A : Sys}
    (Q : Effect A) (X : Operator A) (i : Fin 2) : ℝ :=
  if i = 0 then testValue Q X else (Tr X).re - testValue Q X

@[simp] private theorem binaryWeightBounds_zero {A : Sys}
    (Q : Effect A) (X : Operator A) :
    binaryWeightBounds Q X 0 = testValue Q X := by
  simp [binaryWeightBounds]

@[simp] private theorem binaryWeightBounds_one {A : Sys}
    (Q : Effect A) (X : Operator A) :
    binaryWeightBounds Q X 1 = (Tr X).re - testValue Q X := by
  simp [binaryWeightBounds]

theorem Internal.testValue_nonnegComparisonBounds {A : Sys} (Q : Effect A)
    (X : Operator A) (hX : 0 ≤ X) :
    0 ≤ testValue Q X := by
  unfold testValue
  apply MatrixHockeyStick.trace_mul_re_nonneg_of_posSemidef Q.2.1
  exact Matrix.nonneg_iff_posSemidef.mp
    ((QuantumChannel.starAlgEquiv_nonneg_iff
      (operatorEquivMatrix A)).mpr hX)

theorem Internal.testValue_le_traceComparisonBounds {A : Sys} (Q : Effect A)
    (X : Operator A) (hX : 0 ≤ X) :
    testValue Q X ≤ (Tr X).re := by
  have hnonneg := Internal.testValue_nonnegComparisonBounds
    (⟨1 - Q.1, Q.2.2, by simpa using Q.2.1⟩ : Effect A) X hX
  unfold testValue MatrixHockeyStick.pairing at hnonneg ⊢
  have htrace : Matrix.trace (operatorEquivMatrix A X) = Tr X := by
    rw [LinearMap.trace_eq_matrix_trace (R := ℂ) (b := spaceBasis A)]
    rfl
  rw [Matrix.sub_mul, Matrix.trace_sub, one_mul, Complex.sub_re,
    htrace] at hnonneg
  linarith

private theorem binaryWeightBounds_nonneg {A : Sys}
    (Q : Effect A) (X : Operator A) (hX : 0 ≤ X) (i : Fin 2) :
    0 ≤ binaryWeightBounds Q X i := by
  fin_cases i
  · simpa using Internal.testValue_nonnegComparisonBounds Q X hX
  · simpa using sub_nonneg.mpr
      (Internal.testValue_le_traceComparisonBounds Q X hX)

private theorem measurementChannel_binaryPOVMBounds_apply {A : Sys}
    (Q : Effect A) (X : Operator A) (hX : 0 ≤ X) :
    (NativeMeasuredRelativeEntropy.measurementChannel
      (binaryPOVMBounds Q)).toFun X =
      NativeMeasuredRelativeEntropy.diagonalOperator
        (fun i ↦ (binaryWeightBounds Q X i : ℂ)) := by
  let E : Operator A := (operatorEquivMatrix A).symm Q.1
  have hE : NativeNoCloning.POVMElement E :=
    matrixEffect_to_povmElementBounds Q
  have hEXnonneg : (0 : ℂ) ≤ Tr (E.comp X) :=
    NativeMeasuredRelativeEntropy.trace_comp_nonneg E X hE.1 hX
  have hXtrace_nonneg : (0 : ℂ) ≤ Tr X :=
    ((LinearMap.nonneg_iff_isPositive X).mp hX).trace_nonneg
  change (NativeMeasuredRelativeEntropy.measurementCPMap
      (binaryPOVMBounds Q)).toLinearMap X = _
  rw [NativeMeasuredRelativeEntropy.measurementCPMap_toLinearMap,
    NativeMeasuredRelativeEntropy.measurementRaw_apply]
  congr 1
  funext i
  fin_cases i
  · simp only
    change Tr (E.comp X) = (testValue Q X : ℂ)
    apply Complex.ext
    · simpa [E] using (testValue_eq_trace_effectOperatorBounds Q X).symm
    · simpa using (Complex.nonneg_iff.mp hEXnonneg).2.symm
  · simp only
    change Tr ((LinearMap.id - E).comp X) =
      (((Tr X).re - testValue Q X : ℝ) : ℂ)
    have hcomp : (LinearMap.id - E).comp X = X - E.comp X := by
      ext x
      simp [LinearMap.sub_apply]
    rw [hcomp, map_sub]
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.ofReal_re]
      rw [testValue_eq_trace_effectOperatorBounds]
    · simp only [Complex.sub_im, Complex.ofReal_im]
      rw [← (Complex.nonneg_iff.mp hXtrace_nonneg).2,
        ← (Complex.nonneg_iff.mp hEXnonneg).2]
      norm_num

private theorem classicalBasis_ne_zeroBounds {ι : Type} [Fintype ι]
    (i : ι) : NativeMeasuredRelativeEntropy.classicalBasis i ≠ 0 := by
  intro hzero
  have hnorm := NativeMeasuredRelativeEntropy.norm_classicalBasis i
  rw [hzero, norm_zero] at hnorm
  exact zero_ne_one hnorm

private theorem log_diagonalOperator_applyBounds
    {ι : Type} [Fintype ι] [Nonempty ι]
    (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (i : ι) :
    CFC.log (NativeMeasuredRelativeEntropy.diagonalOperator
        (fun i ↦ (r i : ℂ)))
        (NativeMeasuredRelativeEntropy.classicalBasis i) =
      ((Real.log (r i) : ℝ) : ℂ) •
        NativeMeasuredRelativeEntropy.classicalBasis i := by
  let D := NativeMeasuredRelativeEntropy.diagonalOperator
    (fun i ↦ (r i : ℂ))
  have hD : 0 ≤ D :=
    NativeMeasuredRelativeEntropy.diagonalOperator_nonneg r hr
  refine SandwichedRenyiRelativeEntropy.cfc_real_apply_eigenvector_lm
    (IsSelfAdjoint.of_nonneg hD) Real.log
    (NativeMeasuredRelativeEntropy.diagonalOperator_apply_basis _ i) ?_
  exact SandwichedRenyiRelativeEntropy.mem_spectrum_real_of_eigenvector_lm
    (A := D) (v := NativeMeasuredRelativeEntropy.classicalBasis i)
    (classicalBasis_ne_zeroBounds i)
    (NativeMeasuredRelativeEntropy.diagonalOperator_apply_basis _ i)

private theorem umegakiNorm_diagonalWeightsBounds
    {ι : Type} [Fintype ι] [Nonempty ι]
    (r s : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (hs : ∀ i, 0 ≤ s i)
    (hrsum : ∑ i, r i = 1) :
    SandwichedRenyiRelativeEntropy.umegakiNorm
        (NativeMeasuredRelativeEntropy.diagonalOperator
          (fun i ↦ (r i : ℂ)))
        (NativeMeasuredRelativeEntropy.diagonalOperator
          (fun i ↦ (s i : ℂ))) =
      ∑ i, r i * (Real.log (r i) - Real.log (s i)) := by
  unfold SandwichedRenyiRelativeEntropy.umegakiNorm
  rw [NativeMeasuredRelativeEntropy.trace_diagonalOperator]
  have htrace : (∑ i, (r i : ℂ)) = 1 := by exact_mod_cast hrsum
  rw [htrace]
  simp only [Complex.one_re, div_one]
  rw [LinearMap.trace_eq_sum_inner
    (NativeMeasuredRelativeEntropy.diagonalOperator (fun i ↦ (r i : ℂ)) *
      (CFC.log (NativeMeasuredRelativeEntropy.diagonalOperator
          (fun i ↦ (r i : ℂ))) -
        CFC.log (NativeMeasuredRelativeEntropy.diagonalOperator
          (fun i ↦ (s i : ℂ)))))
    (NativeMeasuredRelativeEntropy.classicalOrthonormalBasis ι), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [NativeMeasuredRelativeEntropy.classicalOrthonormalBasis_apply,
    Module.End.mul_apply, LinearMap.sub_apply,
    log_diagonalOperator_applyBounds r hr i,
    log_diagonalOperator_applyBounds s hs i,
    map_sub, map_smul,
    NativeMeasuredRelativeEntropy.diagonalOperator_apply_basis,
    inner_sub_right, inner_smul_right]
  have hinner : inner ℂ
      (NativeMeasuredRelativeEntropy.classicalBasis i)
      (NativeMeasuredRelativeEntropy.classicalBasis i) = 1 := by
    rw [inner_self_eq_norm_sq_to_K,
      NativeMeasuredRelativeEntropy.norm_classicalBasis]
    norm_num
  rw [map_smul,
    NativeMeasuredRelativeEntropy.diagonalOperator_apply_basis,
    inner_smul_right, inner_smul_right, inner_smul_right]
  simp only [hinner, mul_one, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

local instance classicalSpaceSelfAdjointUnitalCFCBounds
    (ι : Type) [Fintype ι] [Nonempty ι] :
    ContinuousFunctionalCalculus ℝ
      (L (NativeMeasuredRelativeEntropy.ClassicalSpace ι)) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

local instance classicalSpaceNonnegSpectrumBounds
    (ι : Type) [Fintype ι] [Nonempty ι] :
    NonnegSpectrumClass ℝ
      (L (NativeMeasuredRelativeEntropy.ClassicalSpace ι)) :=
  CStarAlgebra.instNonnegSpectrumClass

theorem Internal.rpow_diagonalOperator_applyBounds
    {ι : Type} [Fintype ι] [Nonempty ι]
    (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (y : ℝ) (i : ι) :
    CFC.rpow (NativeMeasuredRelativeEntropy.diagonalOperator
        (fun i ↦ (r i : ℂ))) y
        (NativeMeasuredRelativeEntropy.classicalBasis i) =
      (((r i) ^ y : ℝ) : ℂ) •
        NativeMeasuredRelativeEntropy.classicalBasis i := by
  let D := NativeMeasuredRelativeEntropy.diagonalOperator
    (fun i ↦ (r i : ℂ))
  have hD : 0 ≤ D :=
    NativeMeasuredRelativeEntropy.diagonalOperator_nonneg r hr
  have heq : CFC.rpow D y = cfc (fun x : ℝ ↦ x ^ y) D := by
    rw [CFC.rpow_eq_pow]
    exact CFC.rpow_eq_cfc_real (ha := hD)
  rw [heq]
  exact SandwichedRenyiRelativeEntropy.cfc_real_apply_eigenvector_lm
    (IsSelfAdjoint.of_nonneg hD) (fun x : ℝ ↦ x ^ y)
    (NativeMeasuredRelativeEntropy.diagonalOperator_apply_basis _ i)
    (SandwichedRenyiRelativeEntropy.mem_spectrum_real_of_eigenvector_lm
      (A := D) (v := NativeMeasuredRelativeEntropy.classicalBasis i)
      (classicalBasis_ne_zeroBounds i)
      (NativeMeasuredRelativeEntropy.diagonalOperator_apply_basis _ i))

private theorem sandwichedQuasi_diagonalWeightsBounds
    {ι : Type} [Fintype ι] [Nonempty ι]
    (alpha : ℝ) (r s : ι → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hs : ∀ i, 0 ≤ s i) :
    (SandwichedRenyiRelativeEntropy.sandwichedQuasi alpha
      (NativeMeasuredRelativeEntropy.diagonalOperator
        (fun i ↦ (r i : ℂ)))
      (NativeMeasuredRelativeEntropy.diagonalOperator
        (fun i ↦ (s i : ℂ)))).re =
      ∑ i, (((s i) ^ ((1 - alpha) / (2 * alpha)) * r i *
        (s i) ^ ((1 - alpha) / (2 * alpha))) ^ alpha) := by
  let Dr := NativeMeasuredRelativeEntropy.diagonalOperator
    (fun i ↦ (r i : ℂ))
  let Ds := NativeMeasuredRelativeEntropy.diagonalOperator
    (fun i ↦ (s i : ℂ))
  let gamma : ℝ := (1 - alpha) / (2 * alpha)
  let M := CFC.rpow Ds gamma * Dr * CFC.rpow Ds gamma
  have hDr : 0 ≤ Dr :=
    NativeMeasuredRelativeEntropy.diagonalOperator_nonneg r hr
  have hM : 0 ≤ M := by
    exact conjugate_nonneg_of_nonneg hDr CFC.rpow_nonneg
  have hMapply (i : ι) : M
      (NativeMeasuredRelativeEntropy.classicalBasis i) =
        ((((s i) ^ gamma * r i * (s i) ^ gamma : ℝ) : ℂ)) •
          NativeMeasuredRelativeEntropy.classicalBasis i := by
    dsimp only [M, Dr, Ds]
    rw [Module.End.mul_apply, Module.End.mul_apply,
      Internal.rpow_diagonalOperator_applyBounds s hs gamma i,
      map_smul,
      NativeMeasuredRelativeEntropy.diagonalOperator_apply_basis,
      map_smul, map_smul,
      Internal.rpow_diagonalOperator_applyBounds s hs gamma i]
    simp only [smul_smul]
    congr 1
    push_cast
    ring
  have hMrpow (i : ι) : CFC.rpow M alpha
      (NativeMeasuredRelativeEntropy.classicalBasis i) =
        (((((s i) ^ gamma * r i * (s i) ^ gamma) ^ alpha : ℝ) : ℂ)) •
          NativeMeasuredRelativeEntropy.classicalBasis i := by
    have heq : CFC.rpow M alpha = cfc (fun x : ℝ ↦ x ^ alpha) M := by
      rw [CFC.rpow_eq_pow]
      exact CFC.rpow_eq_cfc_real (ha := hM)
    rw [heq]
    exact SandwichedRenyiRelativeEntropy.cfc_real_apply_eigenvector_lm
      (IsSelfAdjoint.of_nonneg hM) (fun x : ℝ ↦ x ^ alpha)
      (hMapply i)
      (SandwichedRenyiRelativeEntropy.mem_spectrum_real_of_eigenvector_lm
        (A := M) (v := NativeMeasuredRelativeEntropy.classicalBasis i)
        (classicalBasis_ne_zeroBounds i) (hMapply i))
  unfold SandwichedRenyiRelativeEntropy.sandwichedQuasi
  change (Tr (CFC.rpow M alpha)).re = _
  rw [LinearMap.trace_eq_sum_inner (CFC.rpow M alpha)
    (NativeMeasuredRelativeEntropy.classicalOrthonormalBasis ι), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [NativeMeasuredRelativeEntropy.classicalOrthonormalBasis_apply,
    hMrpow, inner_smul_right]
  have hinner : inner ℂ
      (NativeMeasuredRelativeEntropy.classicalBasis i)
      (NativeMeasuredRelativeEntropy.classicalBasis i) = 1 := by
    rw [inner_self_eq_norm_sq_to_K,
      NativeMeasuredRelativeEntropy.norm_classicalBasis]
    norm_num
  simp [gamma]

private theorem suppLE_diagonalWeights_imp {ι : Type} [Fintype ι]
    [Nonempty ι] (r s : ι → ℝ)
    (hsupp : SandwichedRenyiRelativeEntropy.suppLE
      (NativeMeasuredRelativeEntropy.diagonalOperator
        (fun i ↦ (r i : ℂ)))
      (NativeMeasuredRelativeEntropy.diagonalOperator
        (fun i ↦ (s i : ℂ))))
    (i : ι) (hsi : s i = 0) : r i = 0 := by
  have hsker : NativeMeasuredRelativeEntropy.classicalBasis i ∈
      LinearMap.ker (NativeMeasuredRelativeEntropy.diagonalOperator
        (fun i ↦ (s i : ℂ))) := by
    rw [LinearMap.mem_ker,
      NativeMeasuredRelativeEntropy.diagonalOperator_apply_basis]
    simp [hsi]
  have hrker := hsupp hsker
  rw [LinearMap.mem_ker,
    NativeMeasuredRelativeEntropy.diagonalOperator_apply_basis] at hrker
  have hrcomplex : (r i : ℂ) = 0 :=
    (smul_eq_zero.mp hrker).resolve_right (classicalBasis_ne_zeroBounds i)
  exact_mod_cast hrcomplex

private theorem binaryEntropyBits_eq_log_formula
    (epsilon : OPT.ProbabilityLevel) (hepsilon : epsilon.1 < 1) :
    binaryEntropyBits epsilon =
      (-epsilon.1 * Real.log epsilon.1 -
        (1 - epsilon.1) * Real.log (1 - epsilon.1)) / Real.log 2 := by
  by_cases hepsilon0 : epsilon.1 = 0
  · simp [binaryEntropyBits, hepsilon0]
  · have hepsilon1 : epsilon.1 ≠ 1 := ne_of_lt hepsilon
    rw [binaryEntropyBits, if_neg (by simp [hepsilon0, hepsilon1])]
    simp only [Real.logb]
    ring

/-! The next two theorems bound hypothesis-testing divergence using Umegaki
and sandwiched Rényi relative entropies. -/

/-- The hypothesis-testing divergence is controlled by Umegaki relative
entropy, binary entropy, and the trace correction for an unnormalised second
argument.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:6777--6814`. -/
theorem hypothesisTestingDiv_le_umegaki
    {A : Sys} (epsilon : OPT.ProbabilityLevel)
    (hepsilon : epsilon.1 < 1)
    (rho : DensityMatrix A) (sigma : Operator A)
    (hsigma : 0 ≤ sigma) (hsigma0 : sigma ≠ 0) :
    hypothesisTestingDiv epsilon rho sigma ≤
      (((1 / (1 - epsilon.1) : ℝ) : EReal) *
        (umegakiRelEntropyBits rho sigma +
          ((binaryEntropyBits epsilon : ℝ) : EReal) +
          ((epsilon.1 *
            Real.logb 2 (Tr sigma).re : ℝ) : EReal))) := by
  let a : ℝ := 1 - epsilon.1
  let t : ℝ := (Tr sigma).re
  have ha : 0 < a := by dsimp [a]; linarith
  have ht : 0 < t := by
    exact QuantumEntropy.trace_re_pos_of_ne_zero
      hsigma hsigma0
  obtain ⟨Q, hQoptimal, hQaccept⟩ :=
    exists_betaOptimal_acceptance_eq epsilon rho sigma hsigma
  let b : ℝ := testValue Q sigma
  have hb : 0 ≤ b := Internal.testValue_nonnegComparisonBounds Q sigma hsigma
  have hbt : b ≤ t := Internal.testValue_le_traceComparisonBounds Q sigma hsigma
  let r : Fin 2 → ℝ := fun i ↦ binaryWeightBounds Q rho.operator i
  let s : Fin 2 → ℝ := fun i ↦ binaryWeightBounds Q sigma i
  have hr : ∀ i, 0 ≤ r i := fun i ↦
    binaryWeightBounds_nonneg Q rho.operator rho.nonneg i
  have hs : ∀ i, 0 ≤ s i := fun i ↦
    binaryWeightBounds_nonneg Q sigma hsigma i
  have hrsum : ∑ i, r i = 1 := by
    rw [Fin.sum_univ_two]
    simp only [r, binaryWeightBounds_zero, binaryWeightBounds_one,
      rho.trace_one, Complex.one_re]
    ring
  let M := NativeMeasuredRelativeEntropy.measurementChannel
    (binaryPOVMBounds Q)
  have hmeasureRho : M.toFun rho.operator =
      NativeMeasuredRelativeEntropy.diagonalOperator
        (fun i ↦ (r i : ℂ)) := by
    exact measurementChannel_binaryPOVMBounds_apply Q rho.operator rho.nonneg
  have hmeasureSigma : M.toFun sigma =
      NativeMeasuredRelativeEntropy.diagonalOperator
        (fun i ↦ (s i : ℂ)) := by
    exact measurementChannel_binaryPOVMBounds_apply Q sigma hsigma
  have hdpi :=
    UmegakiDPI.monotoneOnNonNeg
      M rho.nonneg hsigma
  by_cases hb0 : b = 0
  · have hs0 : s 0 = 0 := by simp [s, b, hb0]
    have hr0 : r 0 = a := by simp [r, a, hQaccept]
    have hnotSuppOut : ¬ SandwichedRenyiRelativeEntropy.suppLE
        (NativeMeasuredRelativeEntropy.diagonalOperator
          (fun i ↦ (r i : ℂ)))
        (NativeMeasuredRelativeEntropy.diagonalOperator
          (fun i ↦ (s i : ℂ))) := by
      intro hsupp
      have hz := suppLE_diagonalWeights_imp r s hsupp 0 hs0
      rw [hr0] at hz
      exact ha.ne' hz
    rw [hmeasureRho, hmeasureSigma,
      SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN,
      if_neg hnotSuppOut] at hdpi
    have hinputTop :
        SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN
          rho.operator sigma = ⊤ := top_unique hdpi
    have hbitsTop : umegakiRelEntropyBits rho sigma = ⊤ := by
      unfold umegakiRelEntropyBits
      rw [hinputTop]
      exact EReal.top_div_of_pos_ne_top
        (EReal.coe_pos.mpr (Real.log_pos (by norm_num)))
        (EReal.coe_ne_top _)
    have hbeta0 : betaEpsilon epsilon rho sigma = 0 := by
      rw [← hQoptimal.2]
      simp [b, hb0]
    rw [hypothesisTestingDiv, hbeta0, OPT.binaryNegLog2_zero, hbitsTop]
    simp only [EReal.top_add_coe]
    rw [EReal.coe_mul_top_of_pos (one_div_pos.mpr ha)]
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    by_cases hsupp : SandwichedRenyiRelativeEntropy.suppLE
        rho.operator sigma
    · have hsuppOut : SandwichedRenyiRelativeEntropy.suppLE
          (M.toFun rho.operator) (M.toFun sigma) :=
        SandwichedRenyiRelativeEntropy.suppLE_of_CPTP
          M rho.nonneg hsigma hsupp
      have hsuppDiag : SandwichedRenyiRelativeEntropy.suppLE
          (NativeMeasuredRelativeEntropy.diagonalOperator
            (fun i ↦ (r i : ℂ)))
          (NativeMeasuredRelativeEntropy.diagonalOperator
            (fun i ↦ (s i : ℂ))) := by
        simpa only [hmeasureRho, hmeasureSigma] using hsuppOut
      rw [hmeasureRho, hmeasureSigma,
        SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN,
        if_pos hsuppDiag,
        umegakiNorm_diagonalWeightsBounds r s hr hs hrsum,
        SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN,
        if_pos hsupp, EReal.coe_le_coe_iff] at hdpi
      have hdpiReal :
          a * (Real.log a - Real.log b) +
              epsilon.1 *
                (Real.log epsilon.1 - Real.log (t - b)) ≤
            SandwichedRenyiRelativeEntropy.umegakiNorm
              rho.operator sigma := by
        convert hdpi using 1
        all_goals simp only [Fin.sum_univ_two, r, s, binaryWeightBounds_zero,
          binaryWeightBounds_one, hQaccept, rho.trace_one, Complex.one_re,
          a, b, t]
        all_goals ring
      have hlogTerm :
          epsilon.1 * Real.log (t - b) ≤
            epsilon.1 * Real.log t := by
        have htb : 0 ≤ t - b := sub_nonneg.mpr hbt
        by_cases htb0 : t - b = 0
        · have hs1 : s 1 = 0 := by simp [s, t, b, htb0]
          have hr1 := suppLE_diagonalWeights_imp r s hsuppDiag 1 hs1
          have he0 : epsilon.1 = 0 := by
            simpa [r, rho.trace_one, hQaccept] using hr1
          simp [he0]
        · have htbpos : 0 < t - b :=
            lt_of_le_of_ne htb (Ne.symm htb0)
          exact mul_le_mul_of_nonneg_left
            (Real.log_le_log htbpos (by linarith)) epsilon.2.1
      have hscalar :
          -a * Real.log b ≤
            SandwichedRenyiRelativeEntropy.umegakiNorm rho.operator sigma +
              (-epsilon.1 * Real.log epsilon.1 -
                a * Real.log a) + epsilon.1 * Real.log t := by
        linarith [hdpiReal, hlogTerm]
      have hhyp : hypothesisTestingDiv epsilon rho sigma =
          ((-Real.log b / Real.log 2 : ℝ) : EReal) := by
        unfold hypothesisTestingDiv
        rw [← hQoptimal.2]
        have htoNNReal : Real.toNNReal b ≠ 0 := by
          rw [ne_eq, Real.toNNReal_eq_zero]
          exact not_le.mpr hbpos
        unfold OPT.binaryNegLog2
        rw [if_neg htoNNReal, Real.coe_toNNReal b hbpos.le]
        simp only [Real.logb]
        congr 1
        ring
      have humegaki : umegakiRelEntropyBits rho sigma =
          ((SandwichedRenyiRelativeEntropy.umegakiNorm rho.operator sigma /
            Real.log 2 : ℝ) : EReal) := by
        unfold umegakiRelEntropyBits
        rw [SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN,
          if_pos hsupp]
        rfl
      rw [hhyp, humegaki,
        binaryEntropyBits_eq_log_formula epsilon hepsilon]
      simp only [Real.logb, ← EReal.coe_add, ← EReal.coe_mul]
      rw [EReal.coe_le_coe_iff]
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      calc
        -Real.log b / Real.log 2 =
            (-a * Real.log b) / (a * Real.log 2) := by
              field_simp
        _ ≤ (SandwichedRenyiRelativeEntropy.umegakiNorm rho.operator sigma +
              (-epsilon.1 * Real.log epsilon.1 - a * Real.log a) +
                epsilon.1 * Real.log t) / (a * Real.log 2) :=
          div_le_div_of_nonneg_right hscalar (mul_nonneg ha.le hlog2.le)
        _ = (1 / a) *
            (SandwichedRenyiRelativeEntropy.umegakiNorm rho.operator sigma /
              Real.log 2 +
              (-epsilon.1 * Real.log epsilon.1 - a * Real.log a) /
                Real.log 2 +
              epsilon.1 * (Real.log t / Real.log 2)) := by
          field_simp
    · have hinputTop :
          SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN
            rho.operator sigma = ⊤ := by
        unfold SandwichedRenyiRelativeEntropy.umegakiRelEntropyNN
        rw [if_neg hsupp]
      have hbitsTop : umegakiRelEntropyBits rho sigma = ⊤ := by
        unfold umegakiRelEntropyBits
        rw [hinputTop]
        exact EReal.top_div_of_pos_ne_top
          (EReal.coe_pos.mpr (Real.log_pos (by norm_num)))
          (EReal.coe_ne_top _)
      rw [hbitsTop]
      simp only [EReal.top_add_coe]
      rw [EReal.coe_mul_top_of_pos (one_div_pos.mpr ha)]
      exact le_top

/-- The hypothesis-testing divergence is bounded by every sandwiched Rényi
divergence of order strictly larger than one, with the standard testing
penalty.

Source: Khatri--Wilde, arXiv:2011.04672v2,
`entropies.tex:6816--6853`. -/
theorem hypothesisTestingDiv_le_sandwichedRenyi
    {A : Sys} (alpha : ℝ) (halpha : 1 < alpha)
    (epsilon : OPT.ProbabilityLevel) (hepsilon : epsilon.1 < 1)
    (rho : DensityMatrix A) (sigma : Operator A) (hsigma : 0 ≤ sigma) :
    hypothesisTestingDiv epsilon rho sigma ≤
      sandwichedRenyiDivBits alpha rho sigma +
        (((alpha / (alpha - 1)) *
          Real.logb 2 (1 / (1 - epsilon.1)) : ℝ) : EReal) := by
  have halpha0 : 0 < alpha := lt_trans zero_lt_one halpha
  have halphaDen : 0 < alpha - 1 := sub_pos.mpr halpha
  let a : ℝ := 1 - epsilon.1
  have ha : 0 < a := by dsimp [a]; linarith
  by_cases hsupp : SandwichedRenyiRelativeEntropy.suppLE
      rho.operator sigma
  · obtain ⟨Q, hQoptimal, hQaccept⟩ :=
      exists_betaOptimal_acceptance_eq epsilon rho sigma hsigma
    let b : ℝ := testValue Q sigma
    have hb : 0 ≤ b := Internal.testValue_nonnegComparisonBounds Q sigma hsigma
    let r : Fin 2 → ℝ := fun i ↦ binaryWeightBounds Q rho.operator i
    let s : Fin 2 → ℝ := fun i ↦ binaryWeightBounds Q sigma i
    have hr : ∀ i, 0 ≤ r i := fun i ↦
      binaryWeightBounds_nonneg Q rho.operator rho.nonneg i
    have hs : ∀ i, 0 ≤ s i := fun i ↦
      binaryWeightBounds_nonneg Q sigma hsigma i
    have hrsum : ∑ i, r i = 1 := by
      rw [Fin.sum_univ_two]
      simp only [r, binaryWeightBounds_zero, binaryWeightBounds_one,
        rho.trace_one, Complex.one_re]
      ring
    let M := NativeMeasuredRelativeEntropy.measurementChannel
      (binaryPOVMBounds Q)
    have hmeasureRho : M.toFun rho.operator =
        NativeMeasuredRelativeEntropy.diagonalOperator
          (fun i ↦ (r i : ℂ)) := by
      exact measurementChannel_binaryPOVMBounds_apply Q rho.operator rho.nonneg
    have hmeasureSigma : M.toFun sigma =
        NativeMeasuredRelativeEntropy.diagonalOperator
          (fun i ↦ (s i : ℂ)) := by
      exact measurementChannel_binaryPOVMBounds_apply Q sigma hsigma
    have hsuppOut : SandwichedRenyiRelativeEntropy.suppLE
        (M.toFun rho.operator) (M.toFun sigma) :=
      SandwichedRenyiRelativeEntropy.suppLE_of_CPTP
        M rho.nonneg hsigma hsupp
    have hsuppDiag : SandwichedRenyiRelativeEntropy.suppLE
        (NativeMeasuredRelativeEntropy.diagonalOperator
          (fun i ↦ (r i : ℂ)))
        (NativeMeasuredRelativeEntropy.diagonalOperator
          (fun i ↦ (s i : ℂ))) := by
      simpa only [hmeasureRho, hmeasureSigma] using hsuppOut
    have hbpos : 0 < b := by
      by_contra hnot
      have hb0 : b = 0 := le_antisymm (not_lt.mp hnot) hb
      have hs0 : s 0 = 0 := by simp [s, b, hb0]
      have hr0 := suppLE_diagonalWeights_imp r s hsuppDiag 0 hs0
      have : a = 0 := by simpa [r, a, hQaccept] using hr0
      exact ha.ne' this
    have hinCondition : ¬ ((1 < alpha ∧
          ¬ SandwichedRenyiRelativeEntropy.suppLE rho.operator sigma) ∨
        (alpha < 1 ∧ rho.operator ≠ 0 ∧
          (SandwichedRenyiRelativeEntropy.sandwichedQuasi
            alpha rho.operator sigma).re = 0)) := by
      rintro (hbad | hbad)
      · exact hbad.2 hsupp
      · linarith [hbad.1]
    have houtCondition : ¬ ((1 < alpha ∧
          ¬ SandwichedRenyiRelativeEntropy.suppLE
            (M.toFun rho.operator) (M.toFun sigma)) ∨
        (alpha < 1 ∧ M.toFun rho.operator ≠ 0 ∧
          (SandwichedRenyiRelativeEntropy.sandwichedQuasi alpha
            (M.toFun rho.operator) (M.toFun sigma)).re = 0)) := by
      rintro (hbad | hbad)
      · exact hbad.2 hsuppOut
      · linarith [hbad.1]
    have hdpi :=
      RenyiDPI.sandwichedMonotoneOnNonNeg M halpha rho.nonneg hsigma
    rw [SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN,
      if_neg houtCondition,
      SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN,
      if_neg hinCondition, EReal.coe_le_coe_iff] at hdpi
    let q : ℝ :=
      (SandwichedRenyiRelativeEntropy.sandwichedQuasi alpha
        (M.toFun rho.operator) (M.toFun sigma)).re
    let gamma : ℝ := (1 - alpha) / (2 * alpha)
    have hqsum : q = ∑ i,
        (((s i) ^ gamma * r i * (s i) ^ gamma) ^ alpha) := by
      dsimp only [q]
      rw [hmeasureRho, hmeasureSigma]
      simpa only [gamma] using
        sandwichedQuasi_diagonalWeightsBounds alpha r s hr hs
    have htraceOut : (Tr (M.toFun rho.operator)).re = 1 := by
      rw [hmeasureRho,
        NativeMeasuredRelativeEntropy.trace_diagonalOperator]
      have : (∑ i, (r i : ℂ)) = 1 := by exact_mod_cast hrsum
      rw [this]
      rfl
    have hdpiReal : (1 / (alpha - 1)) * Real.log q ≤
        SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv
          alpha rho.operator sigma := by
      unfold SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv at hdpi
      rw [htraceOut, div_one] at hdpi
      exact hdpi
    let selected : ℝ :=
      ((b ^ gamma) * a * (b ^ gamma)) ^ alpha
    have hselectedLower : selected ≤ q := by
      have hterm1 : 0 ≤
          (((s 1) ^ gamma * r 1 * (s 1) ^ gamma) ^ alpha) :=
        Real.rpow_nonneg (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg (hs 1) _) (hr 1))
          (Real.rpow_nonneg (hs 1) _)) _
      calc
        selected =
            (((s 0) ^ gamma * r 0 * (s 0) ^ gamma) ^ alpha) := by
          simp [selected, s, r, b, a, hQaccept]
        _ ≤ (((s 0) ^ gamma * r 0 * (s 0) ^ gamma) ^ alpha) +
            (((s 1) ^ gamma * r 1 * (s 1) ^ gamma) ^ alpha) :=
          le_add_of_nonneg_right hterm1
        _ = q := by rw [hqsum, Fin.sum_univ_two]
    have hbgamma : 0 < b ^ gamma := Real.rpow_pos_of_pos hbpos _
    have hselectedPos : 0 < selected := by
      dsimp only [selected]
      exact Real.rpow_pos_of_pos
        (mul_pos (mul_pos hbgamma ha) hbgamma) _
    have hqpos : 0 < q := hselectedPos.trans_le hselectedLower
    have hlogLower : Real.log selected ≤ Real.log q :=
      Real.log_le_log hselectedPos hselectedLower
    have houtputLower :
        (1 / (alpha - 1)) * Real.log selected ≤
          SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv
            alpha rho.operator sigma := by
      exact (mul_le_mul_of_nonneg_left hlogLower
        (one_div_nonneg.mpr halphaDen.le)).trans hdpiReal
    have hlogSelected : Real.log selected =
        alpha * (gamma * Real.log b + Real.log a +
          gamma * Real.log b) := by
      dsimp only [selected]
      rw [Real.log_rpow (mul_pos (mul_pos hbgamma ha) hbgamma) alpha,
        Real.log_mul (mul_ne_zero hbgamma.ne' ha.ne') hbgamma.ne',
        Real.log_mul hbgamma.ne' ha.ne',
        Real.log_rpow hbpos gamma]
    have hlogInv : Real.log (1 / a) = -Real.log a := by
      rw [one_div, Real.log_inv]
    have hselectedDiv :
        (1 / (alpha - 1)) * Real.log selected =
          -Real.log b -
            (alpha / (alpha - 1)) * Real.log (1 / a) := by
      rw [hlogSelected, hlogInv]
      dsimp only [gamma]
      field_simp
      ring
    have hscalar : -Real.log b ≤
        SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv
            alpha rho.operator sigma +
          (alpha / (alpha - 1)) * Real.log (1 / a) := by
      rw [hselectedDiv] at houtputLower
      linarith
    have hhyp : hypothesisTestingDiv epsilon rho sigma =
        ((-Real.log b / Real.log 2 : ℝ) : EReal) := by
      unfold hypothesisTestingDiv
      rw [← hQoptimal.2]
      have htoNNReal : Real.toNNReal b ≠ 0 := by
        rw [ne_eq, Real.toNNReal_eq_zero]
        exact not_le.mpr hbpos
      unfold OPT.binaryNegLog2
      rw [if_neg htoNNReal, Real.coe_toNNReal b hbpos.le]
      simp only [Real.logb]
      congr 1
      ring
    have hsandwiched : sandwichedRenyiDivBits alpha rho sigma =
        ((SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv
          alpha rho.operator sigma / Real.log 2 : ℝ) : EReal) := by
      unfold sandwichedRenyiDivBits
      rw [SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN,
        if_neg hinCondition]
      rfl
    rw [hhyp, hsandwiched]
    simp only [Real.logb, ← EReal.coe_add,
      EReal.coe_le_coe_iff]
    have hlog2 : 0 ≤ Real.log 2 :=
      (Real.log_pos (by norm_num)).le
    exact (div_le_div_of_nonneg_right hscalar hlog2).trans_eq (by ring)
  · have htop :
        SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN
          alpha rho.operator sigma = ⊤ := by
      unfold SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN
      rw [if_pos (Or.inl ⟨halpha, hsupp⟩)]
    have hbitsTop : sandwichedRenyiDivBits alpha rho sigma = ⊤ := by
      unfold sandwichedRenyiDivBits
      rw [htop]
      exact EReal.top_div_of_pos_ne_top
        (EReal.coe_pos.mpr (Real.log_pos (by norm_num)))
        (EReal.coe_ne_top _)
    rw [hbitsTop, EReal.top_add_coe]
    exact le_top


end NativeHypothesisTesting
end QuantumModel

namespace QuantumModel.KWBridges

open QuantumModel QuantumState QuantumModel.NativeHypothesisTesting

set_option autoImplicit false

end QuantumModel.KWBridges
