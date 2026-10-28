/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.HilbertSchmidt.QuadraticForm
import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Quantum.TraceInequality.HansenPedersen.HilbertSchmidt.Instances

/-!
# Provider-independent vocabulary used by Hiai--Petz consumers

This module exposes Hilbert--Schmidt trace/order utilities and the generic
restriction from all-Hilbert-space operator monotonicity to the finite matrix
model.  None of these declarations supplies a Hiai--Petz 6.2 implication.
-/

namespace HiaiPetz.AmbientInstances

/-- Scoped shared C-star witness for Hilbert--Schmidt operators. -/
noncomputable scoped instance instSharedHSOpCStarAlgebra {n : ℕ} :
    CStarAlgebra (HiaiPetz.HSOp n) :=
  HiaiPetz.hsOpCStarAlgebra

end HiaiPetz.AmbientInstances

namespace ProofNet

open HiaiPetz Matrix Unitary
open scoped CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section

/-- Hilbert--Schmidt adjointness moves a map across the real trace pairing. -/
theorem re_trace_mul_hsAdjoint_eq {n m : ℕ} (Φ : HSMap n m) {B : Mₙ n} {M : Mₙ m}
    (hB : IsSelfAdjoint B) (hΦB : IsSelfAdjoint (Φ B)) :
    Complex.re (Matrix.trace (B * ((hsAdjoint Φ) M))) =
      Complex.re (Matrix.trace ((Φ B) * M)) := by
  have hinner :
      inner ℂ B ((hsAdjoint Φ) M) = inner ℂ (Φ B) M := by
    simpa [hsAdjoint] using
      @ContinuousLinearMap.adjoint_inner_right ℂ (Mₙ n) (Mₙ m)
        (inferInstance : RCLike ℂ)
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixNormedAddCommGroup (n := m))
        (instMatrixInnerProductSpace (n := n))
        (instMatrixInnerProductSpace (n := m))
        (instMatrixCompleteSpace (n := n))
        (instMatrixCompleteSpace (n := m))
        Φ B M
  have hB_star : Matrix.conjTranspose B = B := by
    simpa using hB.star_eq
  have hΦB_star : Matrix.conjTranspose (Φ B) = Φ B := by
    simpa using hΦB.star_eq
  calc
    Complex.re (Matrix.trace (B * ((hsAdjoint Φ) M)))
        = Complex.re (Matrix.trace (((hsAdjoint Φ) M) * B)) := by
            rw [Matrix.trace_mul_comm]
    _ = Complex.re (inner ℂ B ((hsAdjoint Φ) M)) := by
          simp [inner, hB_star]
    _ = Complex.re (inner ℂ (Φ B) M) := by rw [hinner]
    _ = Complex.re (Matrix.trace (M * Matrix.conjTranspose (Φ B))) := by
          simp [inner]
    _ = Complex.re (Matrix.trace (M * (Φ B))) := by rw [hΦB_star]
    _ = Complex.re (Matrix.trace ((Φ B) * M)) := by
          rw [Matrix.trace_mul_comm]

end

end ProofNet
