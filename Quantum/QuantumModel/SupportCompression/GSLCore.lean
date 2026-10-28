/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.InstrumentCompletion.GSLCore
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Density matrices and support orders

Density matrices, their support subspaces, the support inclusion relation
`SupportLE`, and the adjoint identity for outer products. This module keeps the
declarations of the original module that the public development uses.
-/

namespace QuantumModel

open CategoryTheory
open QuantumState

structure DensityMatrix (A : Sys) where
  operator : Operator A
  nonneg : 0 ≤ operator
  trace_one : Tr operator = 1

namespace DensityMatrix

variable {A : Sys}

noncomputable def supportSubspace (rho : DensityMatrix A) : Submodule ℂ (Space A) :=
  LinearMap.range rho.operator

theorem adjoint_outer_product {B : Sys} (u : Space A) (v : Space B) :
    LinearMap.adjoint (QuantumChannel.outer_product u v) =
      QuantumChannel.outer_product v u := by
  apply LinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [LinearMap.adjoint_inner_left]
  simp [QuantumChannel.outer_product_eq_rankOne, inner_smul_left,
    inner_smul_right, mul_comm]

/-- Literal support inclusion for density matrices. -/
def SupportLE (sigma rho : DensityMatrix A) : Prop :=
  supportSubspace sigma ≤ supportSubspace rho

end DensityMatrix
end QuantumModel
