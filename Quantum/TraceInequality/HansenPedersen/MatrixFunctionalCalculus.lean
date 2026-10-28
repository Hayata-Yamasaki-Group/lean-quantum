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
import Quantum.TraceInequality.HansenPedersen.MapVocabulary
import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
import Quantum.TraceInequality.HansenPedersen.FiniteDimensional.Surface
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus
import Quantum.TraceInequality.HiaiPetzTheorem.MatrixFunctionalCalculus

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

private def hsMatrixSpace (n : ℕ) : Type := Mₙ n

private noncomputable instance instHsMatrixSpaceNormedAddCommGroup (n : ℕ) :
    NormedAddCommGroup (hsMatrixSpace n) :=
  instMatrixNormedAddCommGroup (n := n)

private noncomputable instance instHsMatrixSpaceNormedSpace (n : ℕ) :
    NormedSpace ℂ (hsMatrixSpace n) :=
  instMatrixNormedSpace (n := n)

private noncomputable instance instHsMatrixSpaceInnerProductSpace (n : ℕ) :
    InnerProductSpace ℂ (hsMatrixSpace n) :=
  instMatrixInnerProductSpace (n := n)

private noncomputable instance instHsMatrixSpaceCompleteSpace (n : ℕ) :
    CompleteSpace (hsMatrixSpace n) :=
  instMatrixCompleteSpace (n := n)

namespace QuasiEntropyDataProcessing

namespace StrictlyPositiveInverseInequality

/-- Apply the strict-output inverse inequality using the bundled map hypotheses.
Source: Hiai, Theorem 6.2, condition (ii) = (6.3), output-nondegenerate case. -/
theorem map_le {f : ℝ → ℝ} (h : StrictlyPositiveInverseInequality f)
    {n m : ℕ} {Φ : HSMap n m} {A B : Mₙ n}
    (hΦ : StrictlyPositiveSchwarzTracePreservingMap Φ)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    (show HSOp n from
      (hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ)) ≤
      (jOperatorInv f A B) :=
  h Φ hΦ.positiveMap hΦ.tracePreserving hΦ.adjointSchwarz hA hB hΦ.outputPosDef

end StrictlyPositiveInverseInequality

namespace StrictlyPositiveDirectInequality

/-- Apply the strict-output direct inequality using the bundled map hypotheses.
Source: Hiai, Theorem 6.2, condition (iii) = (6.4), output-nondegenerate case. -/
theorem map_le {f : ℝ → ℝ} (h : StrictlyPositiveDirectInequality f)
    {n m : ℕ} {Φ : HSMap n m} {A B : Mₙ n}
    (hΦ : StrictlyPositiveSchwarzTracePreservingMap Φ)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    (show HSOp m from Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))) ≤
      (jOperator f (Φ A) (Φ B)) :=
  h Φ hΦ.positiveMap hΦ.tracePreserving hΦ.adjointSchwarz hA hB hΦ.outputPosDef

end StrictlyPositiveDirectInequality

end QuasiEntropyDataProcessing

private noncomputable def leftMulStarAlgHom {n : ℕ} : Mₙ n →⋆ₐ[ℝ] HSOp n where
  toFun := leftMul
  map_one' := by
    ext X i j
    simp
  map_mul' A B := by
    ext X i j
    simp
  map_zero' := by
    ext X i j
    simp [leftMul_apply]
  map_add' A B := by
    ext X i j
    simp [leftMul_apply]
  commutes' r := by
    ext X i j
    change (((algebraMap ℝ (Mₙ n)) r) * X) i j = (r : ℂ) * X i j
    simp [Algebra.algebraMap_eq_smul_one, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.one_apply]
  map_star' A := by
    simpa [ContinuousLinearMap.star_eq_adjoint, hsAdjoint] using (hsAdjoint_leftMul A).symm

private theorem leftMulTransport_apply {n : ℕ} (A X : Mₙ n)
    (x : EuclideanSpace ℂ (Fin n)) :
    (ContinuousLinearEquiv.conjContinuousAlgEquiv (matrixToEuclidEquiv n) (leftMul A))
        ((matrixToEuclidEquiv n) X) x =
      ((matrixToEuclidEquiv n) (A * X)) x := by
  change
    ((matrixToEuclidEquiv n)
      (A * (matrixToEuclidEquiv n).symm ((matrixToEuclidEquiv n) X))) x =
      ((matrixToEuclidEquiv n) (A * X)) x
  simp

private theorem leftMulEuclid_apply {n : ℕ} (A X : Mₙ n)
    (x : EuclideanSpace ℂ (Fin n)) :
    (ContinuousLinearMap.mulLeftRight ℂ
        (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A)
        (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n))))
      ((matrixToEuclidEquiv n) X) x =
      ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) (A * X)) x := by
  ext i
  change (A *ᵥ ((((matrixToEuclidEquiv n) X) x).ofLp)) i = ((A * X) *ᵥ x.ofLp) i
  rw [show (((matrixToEuclidEquiv n) X) x).ofLp = X *ᵥ x.ofLp by rfl, Matrix.mulVec_mulVec]

private theorem leftMul_transport_eq_mulLeftRight {n : ℕ} (A : Mₙ n) :
    ContinuousLinearEquiv.conjContinuousAlgEquiv (matrixToEuclidEquiv n) (leftMul A) =
      ContinuousLinearMap.mulLeftRight ℂ
        (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
        ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) A)
        (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n))) := by
  ext T x i
  let X : Mₙ n := (matrixToEuclidEquiv n).symm T
  have hTX : T = (matrixToEuclidEquiv n) X := by
    simp [X]
  rw [hTX, leftMulTransport_apply, leftMulEuclid_apply]
  rfl

private theorem hsCfcR_leftMul_eq_normalCfc
    {n : ℕ} (f : ℝ → ℝ) {A : Mₙ n}
    (hA : IsSelfAdjoint A) :
    hsCfcR f (leftMul A) =
      cfc (R := ℂ) (fun z : ℂ => (f z.re : ℂ)) (leftMul A) := by
  let K := hsMatrixSpace n
  letI : CStarAlgebra (K →L[ℂ] K) :=
    @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace K
      (instHsMatrixSpaceNormedAddCommGroup n)
      (instHsMatrixSpaceInnerProductSpace n)
      (instHsMatrixSpaceCompleteSpace n)
  letI : ContinuousFunctionalCalculus ℂ (HSOp n) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  have hleft : IsSelfAdjoint (leftMul A) := leftMul_isSelfAdjoint hA
  simpa [hsCfcR, HansenPedersen.cfcR] using
    (HansenPedersen.Internal.realCfc_eq_normalCfc_of_selfAdjoint
      (K := K) (f := f) (T := leftMul A) hleft)

/-- `vecMulVec` is additive in a summed, scaled left vector. -/
lemma vecMulVec_sum_smul_right
    {n : ℕ} (s : Finset (Fin n)) (c : Fin n → ℂ)
    (v : Fin n → Fin n → ℂ) (r : Fin n → ℂ) :
    Matrix.vecMulVec (Finset.sum s fun i => c i • v i) r =
      Finset.sum s fun i => c i • Matrix.vecMulVec (v i) r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi hs =>
      simp [hi, hs, Matrix.add_vecMulVec, Matrix.smul_vecMulVec]

/-- Expansion of a dyad `vecMulVec x r` along the eigenvector basis of a self-adjoint matrix. -/
lemma vecMulVec_left_eq_sum_eigenbasis
    {n : ℕ} {A : Mₙ n} (hA : IsSelfAdjoint A) (x r : Fin n → ℂ) :
    Matrix.vecMulVec x r =
      ∑ i : Fin n,
        (((hA.isHermitian.eigenvectorBasis.toBasis).repr (WithLp.toLp 2 x) i : ℂ)) •
          Matrix.vecMulVec ((hA.isHermitian.eigenvectorBasis i : Fin n → ℂ)) r := by
  let c : Fin n → ℂ := fun i =>
    ((hA.isHermitian.eigenvectorBasis.toBasis).repr (WithLp.toLp 2 x) i : ℂ)
  have hsum :=
    congrArg (fun v : EuclideanSpace ℂ (Fin n) => Matrix.vecMulVec v r)
      ((hA.isHermitian.eigenvectorBasis.toBasis).sum_repr (WithLp.toLp 2 x)).symm
  simpa [c, vecMulVec_sum_smul_right] using hsum

end HiaiPetz

namespace HiaiPetz.MatrixFunctionalCalculus

noncomputable section

open HiaiPetz Matrix Unitary
open scoped MatrixOrder ComplexOrder CStarAlgebra

private theorem allHOperatorMonotone_Ioi_of_matrixMonotoneCondition
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hI : QuasiEntropyDataProcessing.MatrixMonotoneCondition f) :
    HansenPedersen.AllHOperatorMonotoneOnInterval.{0} (Set.Ioi (0 : ℝ)) f := by
  exact HansenPedersen.matrixMonotoneImpliesAllHOperatorMonotone
    (J := Set.Ioi (0 : ℝ)) (f := f) (convex_Ioi (0 : ℝ)) hf hI

/-- A continuous matrix-monotone function on `(0,∞)` is operator monotone on every
Hilbert space in universe `0`, by the public finite-dimensional approximation theorem. -/
theorem allHOperatorMonotoneOnIoi_of_matrixMonotoneCondition
    {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    QuasiEntropyDataProcessing.MatrixMonotoneCondition f →
      QuasiEntropyDataProcessing.AllHOperatorMonotoneOnIoi f :=
  allHOperatorMonotone_Ioi_of_matrixMonotoneCondition f hf

/-- On continuous functions over `(0,∞)`, all-Hilbert-space operator monotonicity
is equivalent to the matrix-monotone condition. This bridge does not require positivity. -/
theorem allHOperatorMonotoneOnIoi_iff_matrixMonotoneCondition
    {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    QuasiEntropyDataProcessing.AllHOperatorMonotoneOnIoi f ↔
      QuasiEntropyDataProcessing.MatrixMonotoneCondition f :=
  ⟨HiaiPetz.MatrixFunctionalCalculus.matrixMonotoneCondition_of_allHOperatorMonotoneOnIoi,
    HiaiPetz.MatrixFunctionalCalculus.allHOperatorMonotoneOnIoi_of_matrixMonotoneCondition hf⟩

end

end HiaiPetz.MatrixFunctionalCalculus
