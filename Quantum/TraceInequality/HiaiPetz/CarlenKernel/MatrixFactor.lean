/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.MatrixHilbert
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Algebra.DirectSum.LinearMap

/-!
# Positive-semidefinite matrix factorization vocabulary
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped Matrix.Norms.Frobenius MatrixOrder CStarAlgebra ComplexOrder

/-- A positive semidefinite complex matrix factors as `Yᴴ * Y`. -/
theorem matrixPosSemidef_eq_conjTranspose_mul_self {ι : Type*} [Fintype ι]
    {C : Matrix ι ι ℂ}
    (hC : C.PosSemidef) :
    ∃ Y : Matrix ι ι ℂ, C = Matrix.conjTranspose Y * Y := by
  classical
  -- Take `Y = √D * Uᴴ` from the spectral decomposition `C = U * D * Uᴴ`.
  refine ⟨Matrix.diagonal (fun i => ((Real.sqrt (hC.1.eigenvalues i) : ℝ) : ℂ)) *
      star (hC.1.eigenvectorUnitary : Matrix ι ι ℂ), ?_⟩
  conv_lhs => rw [hC.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose, star_star,
    Matrix.diagonal_conjTranspose, ← Matrix.mul_assoc,
    Matrix.mul_assoc _ (Matrix.diagonal _) (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  congr 3
  funext i
  simp only [Function.comp_apply, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hC.eigenvalues_nonneg i)]
  rfl

end Quantum.TraceInequality.Loewner.HiaiPetz
