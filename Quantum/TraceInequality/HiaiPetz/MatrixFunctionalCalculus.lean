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
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Lagrange

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

namespace QuasiEntropyDataProcessing

/-- Strict-output inverse inequality.
Source: Hiai, Theorem 6.2, condition (ii) = (6.3), restricted by the
output-nondegeneracy assumption `Φ(1) > 0`. The map class is the same as in the
general-output condition. In the source, the primed labels (ii') and (iii') denote the versions
restricted to trace-preserving completely positive maps with `Φ(1) > 0`; this condition is not
restricted to such maps. -/
def StrictlyPositiveInverseInequality (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {A B : Mₙ n},
    IsPositiveMap Φ →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    Matrix.PosDef (Φ (1 : Mₙ n)) →
    (show HSOp n from
      (hsAdjoint Φ).comp ((jOperatorInv f (Φ A) (Φ B)).comp Φ)) ≤
      (jOperatorInv f A B)

/-- Strict-output direct inequality.
Source: Hiai, Theorem 6.2, condition (iii) = (6.4), restricted by the
output-nondegeneracy assumption `Φ(1) > 0`. The map class is the same as in the
general-output condition. -/
def StrictlyPositiveDirectInequality (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {A B : Mₙ n},
    IsPositiveMap Φ →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    Matrix.PosDef (Φ (1 : Mₙ n)) →
    (show HSOp m from Φ.comp ((jOperator f A B).comp (hsAdjoint Φ))) ≤
      (jOperator f (Φ A) (Φ B))

/-- Joint concavity of the quasi-entropy.
Source: Hiai, Theorem 6.2, condition (iv). -/
def JointConcavity (f : ℝ → ℝ) : Prop :=
  ∀ {n : ℕ} {A₁ A₂ B₁ B₂ X : Mₙ n} {t : ℝ},
    0 ≤ t →
    t ≤ 1 →
    Matrix.PosDef A₁ →
    Matrix.PosDef A₂ →
    Matrix.PosDef B₁ →
    Matrix.PosDef B₂ →
    t * quasiEntropy f A₁ B₁ X + (1 - t) * quasiEntropy f A₂ B₂ X ≤
      quasiEntropy f (t • A₁ + (1 - t) • A₂) (t • B₁ + (1 - t) • B₂) X

end QuasiEntropyDataProcessing

end HiaiPetz
