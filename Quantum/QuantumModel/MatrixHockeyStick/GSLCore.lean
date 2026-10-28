/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

/-!
# Matrix effects and the trace pairing

Matrix effects `0 ≤ Q ≤ 1` (`IsEffect`, `Effect`), the pairing `Re (trace (Q * H))`, and
nonnegativity of `Re (trace (A * B))` for positive semidefinite matrices.
-/

noncomputable section

open Matrix
open scoped ComplexOrder

namespace MatrixHockeyStick

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A finite matrix effect is a matrix in the positive interval `[0, 1]`. -/
def IsEffect (Q : Matrix n n ℂ) : Prop :=
  Q.PosSemidef ∧ ((1 : Matrix n n ℂ) - Q).PosSemidef

/-- The subtype of finite matrix effects. -/
abbrev Effect (n : Type*) [Fintype n] [DecidableEq n] :=
  {Q : Matrix n n ℂ // IsEffect Q}

/-- Real part of the trace pairing between an effect and a matrix. -/
def pairing (Q H : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (Q * H)).re

omit [DecidableEq n] in
/-- The real trace of a product of two positive semidefinite matrices is
nonnegative. -/
theorem trace_mul_re_nonneg_of_posSemidef
    {P X : Matrix n n ℂ} (hP : P.PosSemidef) (hX : X.PosSemidef) :
    0 ≤ (Matrix.trace (P * X)).re := by
  obtain ⟨S, hS⟩ : ∃ S : Matrix n n ℂ, P = Sᴴ * S := by
    classical
    let U : Matrix n n ℂ := hP.1.eigenvectorUnitary
    let d : n → ℂ := fun i => ((√(hP.1.eigenvalues i) : ℝ) : ℂ)
    refine ⟨diagonal d * star U, ?_⟩
    have hd : (fun i => star d i * d i) = RCLike.ofReal ∘ hP.1.eigenvalues := by
      funext i
      simp only [Function.comp_apply, Pi.star_apply, d, Complex.star_def, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hP.eigenvalues_nonneg i)]
      rfl
    conv_lhs => rw [hP.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rw [conjTranspose_mul, ← star_eq_conjTranspose, star_star, diagonal_conjTranspose]
    symm
    rw [Matrix.mul_assoc U, ← Matrix.mul_assoc (diagonal (star d)), diagonal_mul_diagonal', hd,
      Matrix.mul_assoc]
  have hsandwich : (S * X * Sᴴ).PosSemidef :=
    hX.mul_mul_conjTranspose_same S
  have htrace_nonneg : 0 ≤ Matrix.trace (S * X * Sᴴ) :=
    hsandwich.trace_nonneg
  have htrace_eq : Matrix.trace (P * X) =
      Matrix.trace (S * X * Sᴴ) := by
    calc
      Matrix.trace (P * X) = Matrix.trace ((Sᴴ * S) * X) := by rw [hS]
      _ = Matrix.trace (S * X * Sᴴ) := by
        exact (Matrix.trace_mul_cycle S X Sᴴ).symm
  rw [htrace_eq]
  exact (Complex.nonneg_iff.mp htrace_nonneg).1

end MatrixHockeyStick
