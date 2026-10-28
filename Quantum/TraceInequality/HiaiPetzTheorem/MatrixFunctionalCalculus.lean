/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

-- This file is long but is not split: its private declarations are specific to the proof
-- routes of Theorems 6.2 and 6.4, and splitting the file or making them public would add API
-- without benefit. The eigenrow/`vecMulVec`/`matrixCfcR` lemmas shared with `MidpointKernel`
-- are public.

import Quantum.TraceInequality.HiaiPetz.BlockSumBase
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.TracePowerBridge
import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.Surface
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.Transport
import Quantum.TraceInequality.HiaiPetzTheorem.Core.Basic

/-!
# Matrix functional calculus layer for the Hiai–Petz inequalities

Matrix-level functional-calculus machinery connecting the several equivalent
conditions of Hiai–Petz Theorem 6.2 and feeding the trace-power monotonicity and
concavity results.  It packages the operator/matrix monotonicity conditions and
the strictly-positive direct and inverse map inequalities as propositions, and it
identifies the `J`-operator trace-power functionals with the Lieb and inverse
trace-power functionals under the unit and positive-definite regimes.

## Main definitions

* `AllHOperatorMonotoneOnIoi` / `MatrixMonotoneCondition`: the all-Hilbert-space
  and matrix-only forms of Theorem 6.2 condition (i).
* `StrictlyPositiveDirectInequality` / `StrictlyPositiveInverseInequality`: the
  direct and inverse map inequalities in the strictly-positive regime.
* `JointConcavity`: the joint-concavity condition for a scalar function `f`.

## Main results

* `jPowerTrace_unit_eq_liebTracePower` /
  `jInversePowerTrace_unit_eq_inverseTracePower` and their positive-definite
  extensions `..._eq_..._of_posDef`: identification of the `J`-operator
  trace-power functionals with the Lieb / inverse trace-power functionals.
* `matrix_midpoint_concave_Ioi_of_jointConcavity`: joint concavity of `f`
  transfers to matrix midpoint concavity of `matrixCfcR f` in the Loewner order
  on the positive spectrum.

## Implementation notes

The private-declaration dependency graph forms a single indivisible cluster
spanning most of the file (see the NOTE below), so the module is kept unsplit.

## References

* Hiai, Theorem 6.2.
-/

namespace HiaiPetz

open Matrix Unitary
open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

namespace QuasiEntropyDataProcessing.JointConcavity

/-- Midpoint form of joint concavity for the quasi-entropy.
Source: Hiai, Theorem 6.2, condition (iv). -/
theorem midpoint (f : ℝ → ℝ) (hIV : QuasiEntropyDataProcessing.JointConcavity f)
    {n : ℕ} {A₁ A₂ B₁ B₂ X : Mₙ n}
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    (1 / 2 : ℝ) * quasiEntropy f A₁ B₁ X + (1 - (1 / 2 : ℝ)) * quasiEntropy f A₂ B₂ X ≤
      quasiEntropy f ((1 / 2 : ℝ) • A₁ + (1 - (1 / 2 : ℝ)) • A₂)
        ((1 / 2 : ℝ) • B₁ + (1 - (1 / 2 : ℝ)) • B₂) X := by
  refine hIV (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) (X := X) (t := 1 / 2)
    ?_ ?_ hA₁ hA₂ hB₁ hB₂
  · norm_num
  · norm_num

end QuasiEntropyDataProcessing.JointConcavity

private theorem jointConcavity_midpoint_unit (f : ℝ → ℝ)
    (hIV : QuasiEntropyDataProcessing.JointConcavity f)
    {n : ℕ} {A₁ A₂ X : Mₙ n}
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂) :
    (1 / 2 : ℝ) * quasiEntropy f A₁ 1 X + (1 - (1 / 2 : ℝ)) * quasiEntropy f A₂ 1 X ≤
      quasiEntropy f ((1 / 2 : ℝ) • A₁ + (1 - (1 / 2 : ℝ)) • A₂) (1 : Mₙ n) X := by
  have hone :
      ((1 / 2 : ℝ) • (1 : Mₙ n) + (1 - (1 / 2 : ℝ)) • (1 : Mₙ n)) = (1 : Mₙ n) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      norm_num [Matrix.one_apply]
    · simp [hij]
  have h :=
    QuasiEntropyDataProcessing.JointConcavity.midpoint f hIV
      (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := (1 : Mₙ n))
      (B₂ := (1 : Mₙ n)) (X := X) hA₁ hA₂ (Matrix.PosDef.one (R := ℂ) (n := Fin n))
      (Matrix.PosDef.one (R := ℂ) (n := Fin n))
  rw [hone] at h
  simpa using h

noncomputable def matrixToEuclidEquiv (n : ℕ) :
    Mₙ n ≃L[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  LinearEquiv.toContinuousLinearEquiv
    ((Matrix.toEuclideanLin (n := Fin n) (𝕜 := ℂ)).trans
      LinearMap.toContinuousLinearMap)

private lemma leftMul_eigenmatrix_mem_eigenspace
    {n : ℕ} {A : Mₙ n} (hA : IsSelfAdjoint A) (i j : Fin n) :
    Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ)) (Pi.single j (1 : ℂ)) ∈
      Module.End.eigenspace (leftMul A).toLinearMap (hA.isHermitian.eigenvalues i : ℂ) := by
  rw [Module.End.mem_eigenspace_iff]
  ext a b
  change (A * Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
    (Pi.single j (1 : ℂ))) a b = _
  rw [Matrix.mul_vecMulVec]
  have hmul := hA.isHermitian.mulVec_eigenvectorBasis i
  simp [hmul, Matrix.vecMulVec_apply, mul_assoc]

private lemma leftMul_cfcR_apply_eigenmatrix
    {n : ℕ} (f : ℝ → ℝ) {A : Mₙ n} (hA : IsSelfAdjoint A) (i j : Fin n) :
    hsCfcR f (leftMul A)
      (Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ)) (Pi.single j (1 : ℂ))) =
    (f (hA.isHermitian.eigenvalues i) : ℂ) •
      Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ)) (Pi.single j (1 : ℂ)) := by
  simpa [hsCfcR] using
    (@HiaiPetz.cfcR_apply_of_mem_eigenspace_real_transport (Mₙ n)
      (instMatrixNormedAddCommGroup (n := n))
      (instMatrixInnerProductSpace (n := n))
      (instMatrixCompleteSpace (n := n))
      (Matrix.finiteDimensional)
      (IsSelfAdjoint.instContinuousFunctionalCalculus :
        ContinuousFunctionalCalculus ℝ (HSOp n) IsSelfAdjoint)
      f (leftMul A) (leftMul_isSelfAdjoint hA)
      (hA.isHermitian.eigenvalues i)
      (Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ)) (Pi.single j (1 : ℂ)))
      (leftMul_eigenmatrix_mem_eigenspace (hA := hA) i j))

private lemma leftMul_matrixCfcR_apply_eigenmatrix
    {n : ℕ} (f : ℝ → ℝ) {A : Mₙ n} (hA : IsSelfAdjoint A) (i j : Fin n) :
    leftMul (HansenPedersen.matrixCfcR f A)
      (Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ)) (Pi.single j (1 : ℂ))) =
    (f (hA.isHermitian.eigenvalues i) : ℂ) •
      Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ)) (Pi.single j (1 : ℂ)) := by
  rw [leftMul_apply, Matrix.mul_vecMulVec,
    HiaiPetz.matrixCfcR_mulVec_eigenvectorBasis_transport (hA := hA),
    Matrix.smul_vecMulVec]

private lemma cfc_leftMul_eq_leftMul_matrixCfcR_on_eigenmatrix
    {n : ℕ} (f : ℝ → ℝ) {A : Mₙ n} (hA : IsSelfAdjoint A) (i j : Fin n) :
    hsCfcR f (leftMul A)
      (Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ)) (Pi.single j (1 : ℂ))) =
    leftMul (HansenPedersen.matrixCfcR f A)
      (Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
        (Pi.single j (1 : ℂ))) := by
  rw [leftMul_cfcR_apply_eigenmatrix (hA := hA), leftMul_matrixCfcR_apply_eigenmatrix (hA := hA)]

private lemma clm_map_sum_smul
    {ι : Type*} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →L[ℂ] F) (s : Finset ι) (c : ι → ℂ) (x : ι → E) :
    T (Finset.sum s fun i => c i • x i) = Finset.sum s fun i => c i • T (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi hs =>
      simp [hi, hs, map_add, map_smul]

private lemma vecMulVec_sum_smul
    {n : ℕ} (s : Finset (Fin n)) (c : Fin n → ℂ)
    (v : Fin n → Fin n → ℂ) (j : Fin n) :
    Matrix.vecMulVec (Finset.sum s fun i => c i • v i) (Pi.single j (1 : ℂ)) =
      Finset.sum s fun i => c i • Matrix.vecMulVec (v i) (Pi.single j (1 : ℂ)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi hs =>
      simp [hi, hs, Matrix.add_vecMulVec, Matrix.smul_vecMulVec]

private lemma singleCol_eq_sum_eigenbasis
    {n : ℕ} {A : Mₙ n} (hA : IsSelfAdjoint A) (x : Fin n → ℂ) (j : Fin n) :
    Matrix.vecMulVec x (Pi.single j (1 : ℂ)) =
      ∑ i : Fin n,
        (((hA.isHermitian.eigenvectorBasis.toBasis).repr (WithLp.toLp 2 x) i : ℂ)) •
          Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ))
            (Pi.single j (1 : ℂ)) := by
  let c : Fin n → ℂ := fun i =>
    ((hA.isHermitian.eigenvectorBasis.toBasis).repr (WithLp.toLp 2 x) i : ℂ)
  have hsum :=
    congrArg (fun v : EuclideanSpace ℂ (Fin n) => Matrix.vecMulVec v (Pi.single j (1 : ℂ)))
      ((hA.isHermitian.eigenvectorBasis.toBasis).sum_repr (WithLp.toLp 2 x)).symm
  simpa [c, vecMulVec_sum_smul] using hsum

private lemma cfc_leftMul_eq_leftMul_matrixCfcR_on_singleCol
    {n : ℕ} (f : ℝ → ℝ) {A : Mₙ n}
    (hA : IsSelfAdjoint A) (x : Fin n → ℂ) (j : Fin n) :
    hsCfcR f (leftMul A) (Matrix.vecMulVec x (Pi.single j (1 : ℂ))) =
      leftMul (HansenPedersen.matrixCfcR f A) (Matrix.vecMulVec x (Pi.single j (1 : ℂ))) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  let c : Fin n → ℂ := fun i =>
    ((hA.isHermitian.eigenvectorBasis.toBasis).repr (WithLp.toLp 2 x) i : ℂ)
  let Y : Fin n → Mₙ n := fun i =>
    Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ)) (Pi.single j (1 : ℂ))
  have hdecomp : Matrix.vecMulVec x (Pi.single j (1 : ℂ)) = ∑ i : Fin n, c i • Y i := by
    simpa [c, Y] using singleCol_eq_sum_eigenbasis (hA := hA) x j
  rw [hdecomp]
  calc
    hsCfcR f (leftMul A) (∑ i : Fin n, c i • Y i) =
      ∑ i : Fin n, c i • hsCfcR f (leftMul A) (Y i) := by
        simpa using
          (@clm_map_sum_smul (Fin n) (Mₙ n) (Mₙ n)
            (instMatrixNormedAddCommGroup (n := n))
            (instMatrixNormedSpace (n := n))
            (instMatrixNormedAddCommGroup (n := n))
            (instMatrixNormedSpace (n := n))
            (hsCfcR f (leftMul A)) Finset.univ c Y)
    _ =
      ∑ i : Fin n, c i • leftMul (HansenPedersen.matrixCfcR f A) (Y i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact congrArg (fun M : Mₙ n => c i • M)
          (cfc_leftMul_eq_leftMul_matrixCfcR_on_eigenmatrix (f := f) (hA := hA) i j)
    _ = leftMul (HansenPedersen.matrixCfcR f A) (∑ i : Fin n, c i • Y i) := by
      symm
      simpa using
        (@clm_map_sum_smul (Fin n) (Mₙ n) (Mₙ n)
          (instMatrixNormedAddCommGroup (n := n))
          (instMatrixNormedSpace (n := n))
          (instMatrixNormedAddCommGroup (n := n))
          (instMatrixNormedSpace (n := n))
          (leftMul (HansenPedersen.matrixCfcR f A)) Finset.univ c Y)

private lemma matrix_eq_sum_singleCols {n : ℕ} (X : Mₙ n) :
    X = ∑ j : Fin n, Matrix.vecMulVec (X.col j) (Pi.single j (1 : ℂ)) := by
  ext a b
  rw [Matrix.sum_apply]
  simp [Matrix.vecMulVec_apply, Matrix.col, Pi.single_apply]

theorem cfc_leftMul_eq_leftMul_matrixCfcR
    {n : ℕ} (f : ℝ → ℝ) {A : Mₙ n}
    (hA : IsSelfAdjoint A) :
    hsCfcR f (leftMul A) =
      leftMul (HansenPedersen.matrixCfcR f A) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  ext X a b
  rw [matrix_eq_sum_singleCols X]
  calc
    (hsCfcR f (leftMul A) (∑ j : Fin n, Matrix.vecMulVec (X.col j) (Pi.single j (1 : ℂ)))) a b =
      (∑ j : Fin n,
        hsCfcR f (leftMul A) (Matrix.vecMulVec (X.col j) (Pi.single j (1 : ℂ)))) a b := by
        simpa using congrArg (fun M : Mₙ n => M a b)
          (@clm_map_sum_smul (Fin n) (Mₙ n) (Mₙ n)
            (instMatrixNormedAddCommGroup (n := n))
            (instMatrixNormedSpace (n := n))
            (instMatrixNormedAddCommGroup (n := n))
            (instMatrixNormedSpace (n := n))
            (hsCfcR f (leftMul A)) Finset.univ (fun _ => (1 : ℂ))
            (fun j => Matrix.vecMulVec (X.col j) (Pi.single j (1 : ℂ))))
    _ =
      (∑ j : Fin n,
        leftMul (HansenPedersen.matrixCfcR f A)
          (Matrix.vecMulVec (X.col j) (Pi.single j (1 : ℂ)))) a b := by
          exact congrArg (fun M : Mₙ n => M a b) <|
            Finset.sum_congr rfl (fun j _ =>
              cfc_leftMul_eq_leftMul_matrixCfcR_on_singleCol (f := f) (hA := hA) (X.col j) j)
    _ =
      (leftMul (HansenPedersen.matrixCfcR f A)
        (∑ j : Fin n, Matrix.vecMulVec (X.col j) (Pi.single j (1 : ℂ)))) a b := by
          symm
          simpa using congrArg (fun M : Mₙ n => M a b)
            (@clm_map_sum_smul (Fin n) (Mₙ n) (Mₙ n)
              (instMatrixNormedAddCommGroup (n := n))
              (instMatrixNormedSpace (n := n))
              (instMatrixNormedAddCommGroup (n := n))
              (instMatrixNormedSpace (n := n))
              (leftMul (HansenPedersen.matrixCfcR f A)) Finset.univ
              (fun _ => (1 : ℂ)) (fun j => Matrix.vecMulVec (X.col j) (Pi.single j (1 : ℂ))))

theorem jArg_one_eq_leftMul {n : ℕ} (A : Mₙ n) :
    jArg A (1 : Mₙ n) = leftMul A := by
  ext X
  simp [jArg, leftMul]

/-- With right input `1`, `J_f(A,1)` is left multiplication by the matrix
functional calculus `f(A)`.
Sanity lemma: unit-right `J_f(A,1)` calculation; terminology from
Hiai, Definition 6.1. -/
theorem jOperator_one_right
    {n : ℕ} (f : ℝ → ℝ) {A : Mₙ n} (hA : IsSelfAdjoint A) :
    jOperator f A (1 : Mₙ n) = leftMul (HansenPedersen.matrixCfcR f A) := by
  calc
    jOperator f A (1 : Mₙ n)
        = hsCfcR f (leftMul A) * rightMul (1 : Mₙ n) := by
            simp [jOperator, jArg_one_eq_leftMul]
    _ = leftMul (HansenPedersen.matrixCfcR f A) * 1 := by
          rw [cfc_leftMul_eq_leftMul_matrixCfcR f hA, rightMul_one]
    _ = leftMul (HansenPedersen.matrixCfcR f A) := by simp

/-- With right input `1`, quasi-entropy reduces to the ordinary trace form
associated to the matrix functional calculus `f(A)`.
Sanity lemma: unit-right quasi-entropy reduction; terminology from
Hiai, Definition 6.1. -/
theorem quasiEntropy_one_right
    {n : ℕ} (f : ℝ → ℝ) {A X : Mₙ n} (hA : IsSelfAdjoint A) :
    quasiEntropy f A (1 : Mₙ n) X =
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X * (HansenPedersen.matrixCfcR f A * X))) := by
  rw [quasiEntropy, jOperator_one_right f hA]
  rfl

private theorem jointConcavity_midpoint_unit_matrixCfcR
    (f : ℝ → ℝ) (hIV : QuasiEntropyDataProcessing.JointConcavity f)
    {n : ℕ} {A₁ A₂ X : Mₙ n}
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂) :
    (1 / 2 : ℝ) *
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X * (HansenPedersen.matrixCfcR f A₁ * X))) +
      (1 - (1 / 2 : ℝ)) *
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X * (HansenPedersen.matrixCfcR f A₂ * X))) ≤
      Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X *
            (HansenPedersen.matrixCfcR f
              ((1 / 2 : ℝ) • A₁ + (1 - (1 / 2 : ℝ)) • A₂) * X))) := by
  have hmid :=
    jointConcavity_midpoint_unit f hIV (n := n) (A₁ := A₁) (A₂ := A₂) (X := X) hA₁ hA₂
  have hA_mid_sa :
      IsSelfAdjoint ((1 / 2 : ℝ) • A₁ + (1 - (1 / 2 : ℝ)) • A₂) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      ((IsSelfAdjoint.all (1 / 2 : ℝ)).smul hA₁.1).add
        ((IsSelfAdjoint.all (1 - (1 / 2 : ℝ))).smul hA₂.1)
  rw [quasiEntropy_one_right f hA₁.1, quasiEntropy_one_right f hA₂.1,
    quasiEntropy_one_right f hA_mid_sa] at hmid
  exact hmid

private theorem trace_conjTranspose_mul_matrix_mul_singletonCol
    {n : ℕ} (M : Mₙ n) (x : Fin n → ℂ) (j : Fin n) :
    Matrix.trace
        (Matrix.conjTranspose (Matrix.vecMulVec x (Pi.single j (1 : ℂ))) *
          (M * Matrix.vecMulVec x (Pi.single j (1 : ℂ)))) =
      dotProduct (star x) (M.mulVec x) := by
  rw [Matrix.mul_vecMulVec, Matrix.conjTranspose_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.trace_vecMulVec]
  simp

private theorem matrixPosDef_of_isSelfAdjoint_of_spectrum_subset_Ioi
    {n : ℕ} {A : Mₙ n}
    (hA : IsSelfAdjoint A) (hσA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)) :
    Matrix.PosDef A := by
  let hAh : A.IsHermitian := by
    simpa [Matrix.IsHermitian, IsSelfAdjoint] using hA
  have hA_posDef : A.PosDef := by
    rw [hAh.posDef_iff_eigenvalues_pos]
    intro i
    have hi_spec : hAh.eigenvalues i ∈ spectrum ℝ A := hAh.eigenvalues_mem_spectrum_real i
    simpa [Set.mem_Ioi] using hσA hi_spec
  exact hA_posDef

private theorem jointConcavity_midpoint_unit_dotProduct
    (f : ℝ → ℝ) (hIV : QuasiEntropyDataProcessing.JointConcavity f)
    {n : ℕ} {A₁ A₂ : Mₙ n} {x : Fin n → ℂ}
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂) :
    (1 / 2 : ℝ) *
        Complex.re (dotProduct (star x) ((HansenPedersen.matrixCfcR f A₁).mulVec x)) +
      (1 - (1 / 2 : ℝ)) *
        Complex.re (dotProduct (star x) ((HansenPedersen.matrixCfcR f A₂).mulVec x)) ≤
      Complex.re
        (dotProduct (star x)
          ((HansenPedersen.matrixCfcR f
            ((1 / 2 : ℝ) • A₁ + (1 - (1 / 2 : ℝ)) • A₂)).mulVec x)) := by
  cases n with
  | zero =>
      have hx0 : x = 0 := by ext i; exact Fin.elim0 i
      subst hx0
      simp
  | succ k =>
      let X : Mₙ (k + 1) := Matrix.vecMulVec x (Pi.single 0 (1 : ℂ))
      have htrace :=
        jointConcavity_midpoint_unit_matrixCfcR f hIV (n := k + 1) (A₁ := A₁) (A₂ := A₂) (X := X)
          hA₁ hA₂
      have hmid_eq :
          ((1 / 2 : ℝ) • A₁ + (1 - (1 / 2 : ℝ)) • A₂) = ((1 / 2 : ℝ) • (A₁ + A₂)) := by
        have hhalf : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by norm_num
        have hsmul :
            (1 / 2 : ℝ) • (A₁ + A₂) = (1 / 2 : ℝ) • A₁ + (1 / 2 : ℝ) • A₂ := by
          ext i j
          exact smul_add (1 / 2 : ℝ) (A₁ i j) (A₂ i j)
        calc
          ((1 / 2 : ℝ) • A₁ + (1 - (1 / 2 : ℝ)) • A₂)
              = (1 / 2 : ℝ) • A₁ + (1 / 2 : ℝ) • A₂ := by rw [hhalf]
          _ = (1 / 2 : ℝ) • (A₁ + A₂) := hsmul.symm
      rw [trace_conjTranspose_mul_matrix_mul_singletonCol
          (M := HansenPedersen.matrixCfcR f A₁) (x := x) (j := 0),
        trace_conjTranspose_mul_matrix_mul_singletonCol
          (M := HansenPedersen.matrixCfcR f A₂) (x := x) (j := 0),
        trace_conjTranspose_mul_matrix_mul_singletonCol
          (M := HansenPedersen.matrixCfcR f
            ((1 / 2 : ℝ) • A₁ + (1 - (1 / 2 : ℝ)) • A₂)) (x := x) (j := 0)] at htrace
      simpa [hmid_eq] using htrace

/-- If `f` satisfies the joint-concavity condition, then `matrixCfcR f` is
midpoint concave in the Loewner order on self-adjoint matrices with positive
spectrum: `½ (f(A) + f(B)) ≤ f(½ (A + B))`. -/
theorem matrix_midpoint_concave_Ioi_of_jointConcavity
    (f : ℝ → ℝ) :
    QuasiEntropyDataProcessing.JointConcavity f →
      ∀ {n : ℕ} {A B : Mₙ n},
        IsSelfAdjoint A →
        IsSelfAdjoint B →
        spectrum ℝ A ⊆ Set.Ioi (0 : ℝ) →
        spectrum ℝ B ⊆ Set.Ioi (0 : ℝ) →
        (1 / 2 : ℝ) •
            (HansenPedersen.matrixCfcR f A + HansenPedersen.matrixCfcR f B) ≤
          HansenPedersen.matrixCfcR f ((1 / 2 : ℝ) • (A + B)) := by
  intro hIV n A B hA hB hσA hσB
  /- Step 1: Convert spectral positivity into positive-definite matrix data. -/
  have hA_pd : Matrix.PosDef A := matrixPosDef_of_isSelfAdjoint_of_spectrum_subset_Ioi hA hσA
  have hB_pd : Matrix.PosDef B := matrixPosDef_of_isSelfAdjoint_of_spectrum_subset_Ioi hB hσB
  let M :=
    HansenPedersen.matrixCfcR f ((1 / 2 : ℝ) • (A + B)) -
      (1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f A + HansenPedersen.matrixCfcR f B)
  have hmid_sa : IsSelfAdjoint ((1 / 2 : ℝ) • (A + B)) := by
    have hsa :
          IsSelfAdjoint ((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B) :=
        ((IsSelfAdjoint.all (1 / 2 : ℝ)).smul hA).add ((IsSelfAdjoint.all (1 / 2 : ℝ)).smul hB)
    have hsum :
        (1 / 2 : ℝ) • (A + B) = (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B := by
      ext i j
      exact smul_add (1 / 2 : ℝ) (A i j) (B i j)
    rw [hsum]
    exact hsa
  have hM_sa : IsSelfAdjoint M := by
    refine (matrixCfcR_isSelfAdjoint f hmid_sa).sub ?_
    refine ((IsSelfAdjoint.all (1 / 2 : ℝ)).smul ?_)
    exact (matrixCfcR_isSelfAdjoint f hA).add (matrixCfcR_isSelfAdjoint f hB)
  /- Step 2: Reduce Loewner order to nonnegativity of the difference form. -/
  have hM_psd : M.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · simpa [Matrix.IsHermitian, IsSelfAdjoint] using hM_sa
    · intro x
      /- Step 3: Apply midpoint joint concavity to the vector quadratic form. -/
      have hquad :=
        jointConcavity_midpoint_unit_dotProduct f hIV (A₁ := A) (A₂ := B) (x := x) hA_pd hB_pd
      have hmid_eq :
          ((1 / 2 : ℝ) • A + (1 - (1 / 2 : ℝ)) • B) = ((1 / 2 : ℝ) • (A + B)) := by
        have hhalf : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by norm_num
        have hsmul :
            (1 / 2 : ℝ) • (A + B) = (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B := by
          ext i j
          exact smul_add (1 / 2 : ℝ) (A i j) (B i j)
        calc
          ((1 / 2 : ℝ) • A + (1 - (1 / 2 : ℝ)) • B)
              = (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B := by rw [hhalf]
          _ = (1 / 2 : ℝ) • (A + B) := hsmul.symm
      have hhalf : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by norm_num
      let a : ℝ :=
        Complex.re (dotProduct (star x) ((HansenPedersen.matrixCfcR f A).mulVec x))
      let b : ℝ :=
        Complex.re (dotProduct (star x) ((HansenPedersen.matrixCfcR f B).mulVec x))
      let c : ℝ :=
        Complex.re
          (dotProduct (star x)
            ((HansenPedersen.matrixCfcR f ((1 / 2 : ℝ) • (A + B))).mulVec x))
      have hquad' : (1 / 2 : ℝ) * a + (1 - (1 / 2 : ℝ)) * b ≤ c := by
        have hquad0 := hquad
        rw [hmid_eq] at hquad0
        simpa [a, b, c] using hquad0
      let u : ℂ :=
        dotProduct (star x) ((HansenPedersen.matrixCfcR f ((1 / 2 : ℝ) • (A + B))).mulVec x)
      let v : ℂ :=
        dotProduct (star x) ((HansenPedersen.matrixCfcR f A).mulVec x)
      let w : ℂ :=
        dotProduct (star x) ((HansenPedersen.matrixCfcR f B).mulVec x)
      /- Step 4: Express M x as the midpoint CFC term minus endpoint terms. -/
      have hlinVec :
          M.mulVec x =
            (HansenPedersen.matrixCfcR f ((1 / 2 : ℝ) • (A + B))).mulVec x -
              ((1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f A).mulVec x +
                (1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f B).mulVec x) := by
        have hsumVec :
            (((1 / 2 : ℝ) •
                (HansenPedersen.matrixCfcR f A + HansenPedersen.matrixCfcR f B)) *ᵥ x) =
              (1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f A *ᵥ x) +
                (1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f B *ᵥ x) := by
          calc
            (((1 / 2 : ℝ) •
                (HansenPedersen.matrixCfcR f A + HansenPedersen.matrixCfcR f B)) *ᵥ x)
                = (1 / 2 : ℝ) •
                    ((HansenPedersen.matrixCfcR f A + HansenPedersen.matrixCfcR f B) *ᵥ x) := by
                  exact Matrix.smul_mulVec (1 / 2 : ℝ)
                    (HansenPedersen.matrixCfcR f A + HansenPedersen.matrixCfcR f B) x
            _ = (1 / 2 : ℝ) •
                    (HansenPedersen.matrixCfcR f A *ᵥ x +
                      HansenPedersen.matrixCfcR f B *ᵥ x) := by
                  rw [Matrix.add_mulVec]
            _ = (1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f A *ᵥ x) +
                  (1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f B *ᵥ x) := by
                  exact smul_add (1 / 2 : ℝ) (HansenPedersen.matrixCfcR f A *ᵥ x)
                    (HansenPedersen.matrixCfcR f B *ᵥ x)
        dsimp [M]
        rw [Matrix.sub_mulVec, hsumVec]
      have hlin :
          dotProduct (star x) (M.mulVec x) =
            u - ((1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w) := by
        have hdotA :
            dotProduct (star x) ((1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f A).mulVec x) =
              (1 / 2 : ℝ) • v := by
          exact dotProduct_smul (1 / 2 : ℝ) (star x)
            ((HansenPedersen.matrixCfcR f A).mulVec x)
        have hdotB :
            dotProduct (star x) ((1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f B).mulVec x) =
              (1 / 2 : ℝ) • w := by
          exact dotProduct_smul (1 / 2 : ℝ) (star x)
            ((HansenPedersen.matrixCfcR f B).mulVec x)
        calc
          dotProduct (star x) (M.mulVec x)
              = dotProduct (star x)
                  ((HansenPedersen.matrixCfcR f ((1 / 2 : ℝ) • (A + B))).mulVec x -
                    ((1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f A).mulVec x +
                      (1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f B).mulVec x)) := by
                rw [hlinVec]
          _ = u -
                (dotProduct (star x) ((1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f A).mulVec x) +
                  dotProduct (star x)
                    ((1 / 2 : ℝ) • (HansenPedersen.matrixCfcR f B).mulVec x)) := by
                simp [u, dotProduct_sub, dotProduct_add]
          _ = u - ((1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w) := by
                rw [hdotA, hdotB]
      have hcalc :
          Complex.re (dotProduct (star x) (M.mulVec x)) =
            c - ((1 / 2 : ℝ) * a + (1 - (1 / 2 : ℝ)) * b) := by
        have hreal := congrArg Complex.re hlin
        dsimp [u, v, w, a, b, c] at hreal ⊢
        rw [hhalf]
        simpa using hreal
      /- Step 5: Use real nonnegativity and Hermitian symmetry for complex order. -/
      have hre : 0 ≤ Complex.re (dotProduct (star x) (M.mulVec x)) := by
        rw [hcalc]
        exact sub_nonneg.mpr hquad'
      have him : Complex.im (dotProduct (star x) (M.mulVec x)) = 0 := by
        have hHerm : M.IsHermitian := by
          simpa [Matrix.IsHermitian, IsSelfAdjoint] using hM_sa
        exact Matrix.IsHermitian.im_star_dotProduct_mulVec_self (A := M) hHerm x
      rw [Complex.le_def]
      exact ⟨hre, by simpa using him.symm⟩
  /- Step 6: Translate positive semidefiniteness of M back to matrix order. -/
  refine sub_nonneg.mp ?_
  simpa [M, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (hM_psd.nonneg : (0 : Mₙ n) ≤ M)

end HiaiPetz

namespace HiaiPetz.MatrixFunctionalCalculus

noncomputable section

open HiaiPetz Matrix Unitary
open scoped MatrixOrder ComplexOrder CStarAlgebra

/-- Section-local reducible cache for the `CStarAlgebra` instance on the Euclidean
CLM algebra `EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)`; see the
section note above on turning repeated instance searches into head-matches. -/
@[reducible, local instance]
private noncomputable def instCStarAlgebraEuclideanCLMScoped {n : ℕ} :
    CStarAlgebra (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  inferInstance

/-- Section-local reducible cache for the real `ContinuousFunctionalCalculus`
instance (at `IsSelfAdjoint`) on the Euclidean CLM algebra
`EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)`; see the section note
above. -/
@[reducible, local instance]
private noncomputable def instCFCRealEuclideanCLMScoped {n : ℕ} :
    ContinuousFunctionalCalculus ℝ
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) IsSelfAdjoint :=
  inferInstance

/-- Section-local reducible cache for the `Algebra ℝ` instance on the Euclidean
CLM algebra `EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)`; see the
section note above. -/
@[reducible, local instance]
private noncomputable def instAlgebraRealEuclideanCLMScopedCond {n : ℕ} :
    Algebra ℝ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  inferInstance

/-- Section-local reducible cache for the `AddRightMono` instance on the Euclidean
CLM algebra `EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)`; see the
section note above. -/
@[reducible, local instance]
private noncomputable def instAddRightMonoEuclideanCLMScoped {n : ℕ} :
    AddRightMono (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  inferInstance

/-- Section-local reducible cache for the `Algebra ℝ` instance on the matrix
algebra `Mₙ n`; see the section note above. -/
@[reducible, local instance]
private noncomputable def instAlgebraRealMatrixScopedCond {n : ℕ} :
    Algebra ℝ (Mₙ n) :=
  inferInstance

/-- Section-local reducible cache for the `AddRightMono` instance on the matrix
algebra `Mₙ n`; see the section note above. -/
@[reducible, local instance]
private noncomputable def instAddRightMonoMatrixScopedCond {n : ℕ} :
    AddRightMono (Mₙ n) :=
  inferInstance

/-- `Matrix.toEuclideanCLM` preserves self-adjointness. -/
private lemma isSelfAdjoint_toEuclideanCLM {n : ℕ} {A : Mₙ n} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A) := by
  have h1 : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (star A) =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A :=
    congrArg _ hA
  simpa [map_star] using h1

/-- `Matrix.toEuclideanCLM` preserves the real spectrum. -/
private lemma spectrum_toEuclideanCLM {n : ℕ} (A : Mₙ n) :
    spectrum ℝ (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A) = spectrum ℝ A := by
  simpa using
    AlgEquiv.spectrum_eq ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).restrictScalars ℝ) A

/-- `Matrix.toEuclideanCLM` is monotone for the Loewner orders. -/
private lemma toEuclideanCLM_mono {n : ℕ} {A B : Mₙ n} (hAB : A ≤ B) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A ≤
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B := by
  have hBA_psd : (B - A).PosSemidef := by
    exact (Matrix.nonneg_iff_posSemidef).mp (sub_nonneg.mpr hAB)
  have hφBA_pos :
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (B - A) :
          EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).IsPositive := by
    simpa [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
      ((Matrix.isPositive_toEuclideanLin_iff (A := B - A)).2 hBA_psd)
  have hφBA_nonneg : 0 ≤ Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (B - A) := by
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).2 hφBA_pos
  exact sub_nonneg.mp (by simpa [map_sub] using hφBA_nonneg)

/-- The Loewner order on matrices is reflected by `Matrix.toEuclideanCLM`. -/
private lemma le_of_toEuclideanCLM_le {n : ℕ} {X Y : Mₙ n}
    (h : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X ≤
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) Y) :
    X ≤ Y := by
  have hpos :
      ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) (Y - X) :
          EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).IsPositive := by
    rw [map_sub]
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).1 (sub_nonneg.mpr h)
  have hTpos : (Matrix.toEuclideanLin (Y - X)).IsPositive := by
    refine (LinearMap.isPositive_toContinuousLinearMap_iff _).1 ?_
    change ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) (Y - X) :
        EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).IsPositive
    exact hpos
  exact sub_nonneg.mp ((Matrix.nonneg_iff_posSemidef).2
    ((Matrix.isPositive_toEuclideanLin_iff (A := Y - X)).1 hTpos))

/-- `Matrix.toEuclideanCLM` intertwines the matrix real CFC with the operator real CFC. -/
private lemma toEuclideanCLM_matrixCfcR {n : ℕ} (f : ℝ → ℝ) (A : Mₙ n) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (HansenPedersen.matrixCfcR f A) =
      HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A) := by
  change
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm
          (HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f
            (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A))) =
      HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) f
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A)
  simp

theorem matrixMonotoneCondition_of_allHOperatorMonotoneOnIoi
    {f : ℝ → ℝ}
    (hmono : QuasiEntropyDataProcessing.AllHOperatorMonotoneOnIoi f) :
    QuasiEntropyDataProcessing.MatrixMonotoneCondition f := by
  intro n A B hA hB hσA hσB hAB
  cases n with
  | zero =>
      exact le_of_eq (Subsingleton.elim _ _)
  | succ k =>
      have hpush :
          HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin (k + 1))) f
              (Matrix.toEuclideanCLM (n := Fin (k + 1)) (𝕜 := ℂ) A) ≤
            HansenPedersen.cfcR (ℋ := EuclideanSpace ℂ (Fin (k + 1))) f
              (Matrix.toEuclideanCLM (n := Fin (k + 1)) (𝕜 := ℂ) B) :=
        hmono (EuclideanSpace ℂ (Fin (k + 1)))
          (isSelfAdjoint_toEuclideanCLM hA) (isSelfAdjoint_toEuclideanCLM hB)
          (by rw [spectrum_toEuclideanCLM]; exact hσA)
          (by rw [spectrum_toEuclideanCLM]; exact hσB)
          (toEuclideanCLM_mono hAB)
      apply le_of_toEuclideanCLM_le
      rw [toEuclideanCLM_matrixCfcR, toEuclideanCLM_matrixCfcR]
      exact hpush

end

end HiaiPetz.MatrixFunctionalCalculus
