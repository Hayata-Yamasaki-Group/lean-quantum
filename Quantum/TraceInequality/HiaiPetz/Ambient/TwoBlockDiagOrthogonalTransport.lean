/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.OrthogonalTransport


/-!
Compatibility entry point for orthogonal transport of two-block diagonal CFC.

The proof payload lives in content-named submodules under
`Ambient/TwoBlockDiagOrthogonalTransport/`.
-/

namespace HiaiPetz

open scoped MatrixOrder Matrix.Norms.Frobenius

open scoped ComplexOrder

attribute [local instance]
  instMatrixNormedAddCommGroup
  instMatrixNormedSpace
  instMatrixInnerProductSpace
  instMatrixCompleteSpace

noncomputable section MatrixScopedInstances

/-- Transport identity for the two-block diagonal functional calculus: the ambient CFC image
`ambientTwoBlockDiagJArgCfc f` of the `J`-argument agrees with the orthogonal-decomposition
conjugation image `orthogonalConjDiagCfcOp f`, for self-adjoint `A₁, A₂` and positive-definite
`B₁, B₂`.  It moves the functional calculus through the orthogonal block decomposition by chaining
the ambient-to-transport and transport-to-conjugation equalities. -/
theorem cfcJArg_eq_orthogonalConjDiag {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂)
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂) :
    ambientTwoBlockDiagJArgCfc (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ =
      orthogonalConjDiagCfcOp (n := n) f
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ := by
  rw [ambientTwoBlockDiagJArgCfc_eq_orthogonalTransportCfcImage_core
    n f (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ hA₁ hA₂]
  exact orthogonalTransportCfcImage_eq_orthogonalConjDiagCfcOp_core
    n f (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ hA₁ hA₂


end MatrixScopedInstances

end HiaiPetz
