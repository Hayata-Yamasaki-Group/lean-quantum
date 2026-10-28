/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.TransformationNorms.GSLCore
import Quantum.OperationalProbabilistic.Framework.EffectNorms.GSLCore
import Quantum.OperationalProbabilistic.Framework.TransformationApplication.GSLCore

open CategoryTheory
open scoped MonoidalCategory

/-!
# Operational framework: the norm on operational states

The operational state-norm laws (`operationalStateNorm_laws`) give the `Norm` instance
`instNormOperationalStateSpaceReal` and the normed-space core of the real operational state
space.
-/

namespace OPT

universe u v w

section CausalOperationalProbabilisticTheory

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]

variable [Preadditive Sys]

variable [CategoryTheory.Linear ℝ Sys] [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]

variable [CausalOperationalProbabilisticTheory Sys]

/-- The state-side operational norm laws, bundled as a theorem rather than a
Mathlib normed-space instance. -/
theorem operationalStateNorm_laws {A : Sys} :
    (∀ δ : OperationalStateSpaceReal (Sys := Sys) A,
      0 ≤ operationalStateNorm (Sys := Sys) δ) ∧
    (∀ (r : ℝ) (δ : OperationalStateSpaceReal (Sys := Sys) A),
      operationalStateNorm (Sys := Sys) (r • δ) =
        |r| * operationalStateNorm (Sys := Sys) δ) ∧
    (∀ δ ε : OperationalStateSpaceReal (Sys := Sys) A,
      operationalStateNorm (Sys := Sys) (δ + ε) ≤
        operationalStateNorm (Sys := Sys) δ + operationalStateNorm (Sys := Sys) ε) ∧
    (∀ δ : OperationalStateSpaceReal (Sys := Sys) A,
      operationalStateNorm (Sys := Sys) δ = 0 ↔ δ = 0) := by
  constructor
  · intro δ
    exact operationalStateNorm_nonneg (Sys := Sys) δ
  constructor
  · intro r δ
    exact operationalStateNorm_smul (Sys := Sys) r δ
  constructor
  · intro δ ε
    exact operationalStateNorm_add_le (Sys := Sys) δ ε
  · intro δ
    exact operationalStateNorm_eq_zero_iff (Sys := Sys) δ

/-- The canonical Mathlib norm on the operational real state space is the
state-side operational norm. -/
noncomputable instance instNormOperationalStateSpaceReal {A : Sys} :
    Norm (OperationalStateSpaceReal (Sys := Sys) A) where
  norm := operationalStateNorm (Sys := Sys)

/-- The Mathlib norm on the operational real state space is the state-side operational norm. -/
@[simp]
theorem norm_operationalStateSpaceReal {A : Sys}
    (δ : OperationalStateSpaceReal (Sys := Sys) A) :
    ‖δ‖ = operationalStateNorm (Sys := Sys) δ :=
  rfl

/-- The state-side operational norm laws as a Mathlib normed-space core. This
does not create a `NormedAddCommGroup` or `NormedSpace` instance. -/
theorem operationalStateNormedSpaceCore {A : Sys} :
    NormedSpace.Core ℝ (OperationalStateSpaceReal (Sys := Sys) A) where
  norm_nonneg := by
    intro δ
    exact (operationalStateNorm_laws (Sys := Sys) (A := A)).1 δ
  norm_smul := by
    intro r δ
    simpa [norm_operationalStateSpaceReal, Real.norm_eq_abs] using
      (operationalStateNorm_laws (Sys := Sys) (A := A)).2.1 r δ
  norm_triangle := by
    intro δ ε
    exact (operationalStateNorm_laws (Sys := Sys) (A := A)).2.2.1 δ ε
  norm_eq_zero_iff := by
    intro δ
    exact (operationalStateNorm_laws (Sys := Sys) (A := A)).2.2.2 δ

end CausalOperationalProbabilisticTheory
end OPT
