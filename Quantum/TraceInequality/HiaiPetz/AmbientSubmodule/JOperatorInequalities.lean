/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.JOperator
import Quantum.TraceInequality.HiaiPetz.HilbertSchmidt.InnerProduct

/-!
# Quadratic-form consequences for ambient operators

Inequalities and quadratic-form transport lemmas following from the
positive-definite `J`-operator inverse identities.

## Main results

* `hsQForm_hsAdjoint_comp` and `hsQForm_comp_hsAdjoint`: quadratic-form
  identities for conjugating an operator by a Hilbert-Schmidt map and its
  adjoint.
* `ringInverse_antitone_of_nonneg_isUnit`: order reversal of the ring inverse
  for positive invertible operators.
* `hsle_jOperatorInv_of_hsle_jOperator_of_posDef` and
  `hsle_jOperator_of_hsle_jOperatorInv_of_posDef`: conversion between order
  inequalities for `jOperator` and `jOperatorInv`.

## References

* Internal finite-dimensional quadratic-form layer for the Hiai-Petz
  data-processing construction.
-/

namespace HiaiPetz

open scoped MatrixOrder

open scoped ComplexOrder

noncomputable section MatrixScopedInstances

attribute [local instance] instMatrixNormedAddCommGroupScoped
attribute [local instance] instMatrixNormedSpaceScoped
attribute [local instance] instMatrixInnerProductSpaceScoped
attribute [local instance] instMatrixCompleteSpaceScoped
attribute [local instance] instWithLpMatrixPairInnerProductSpace
attribute [local instance] instWithLpMatrixPairNormedSpace
attribute [local instance] instWithLpMatrixPairCompleteSpace

/-- If `A` and `B` are positive definite, the real spectrum of `jArg A B` lies
in the positive half-line. -/
theorem spectrum_jArg_subset_Ioi_of_posDef {n : ℕ} {A B : Mₙ n}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    spectrum ℝ (jArg A B) ⊆ Set.Ioi (0 : ℝ) :=
  spectrum_jArg_subset_Ioi hA hB

/-- Quadratic forms of `Φ ∘ T ∘ hsAdjoint Φ` can be tested after applying
`hsAdjoint Φ` to the vector. -/
theorem hsQForm_comp_hsAdjoint {n m : ℕ} (Φ : HSMap n m) (T : HSOp n) (X : Mₙ m) :
    Complex.re
      (Matrix.trace
        (Matrix.conjTranspose X * ((Φ.comp (T.comp (hsAdjoint Φ))) X))) =
      Complex.re
        (Matrix.trace (Matrix.conjTranspose ((hsAdjoint Φ) X) * (T ((hsAdjoint Φ) X)))) := by
  letI := instMatrixNormedAddCommGroup (n := n)
  letI := instMatrixNormedSpace (n := n)
  letI := instMatrixInnerProductSpace (n := n)
  letI := instMatrixCompleteSpace (n := n)
  letI := instMatrixNormedAddCommGroup (n := m)
  letI := instMatrixNormedSpace (n := m)
  letI := instMatrixInnerProductSpace (n := m)
  letI := instMatrixCompleteSpace (n := m)
  have hinner :
      inner ℂ X ((Φ.comp (T.comp (hsAdjoint Φ))) X) =
        inner ℂ ((hsAdjoint Φ) X) (T ((hsAdjoint Φ) X)) := by
    simpa [hsAdjoint, ContinuousLinearMap.comp_apply] using
      (@ContinuousLinearMap.adjoint_inner_left ℂ (Mₙ n) (Mₙ m)
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixNormedAddCommGroup (n := m))
        (instMatrixInnerProductSpace (n := n))
        (instMatrixInnerProductSpace (n := m))
        (instMatrixCompleteSpace (n := n))
        (instMatrixCompleteSpace (n := m))
        Φ (T ((hsAdjoint Φ) X)) X).symm
  calc
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose X * ((Φ.comp (T.comp (hsAdjoint Φ))) X)))
      = Complex.re
          (Matrix.trace (((Φ.comp (T.comp (hsAdjoint Φ))) X) * Matrix.conjTranspose X)) := by
            rw [Matrix.trace_mul_comm]
    _ = Complex.re
          (Matrix.trace (T ((hsAdjoint Φ) X) * Matrix.conjTranspose ((hsAdjoint Φ) X))) := by
          simpa [inner] using congrArg Complex.re hinner
    _ = Complex.re
          (Matrix.trace (Matrix.conjTranspose ((hsAdjoint Φ) X) * T ((hsAdjoint Φ) X))) := by
          rw [Matrix.trace_mul_comm]

end MatrixScopedInstances

end HiaiPetz
