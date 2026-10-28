/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetzTheorem.Core
import Quantum.TraceInequality.HiaiPetz.OperatorCore
import Quantum.TraceInequality.HiaiPetz.Core.MatrixType
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Topology.Algebra.Module.LinearMap
import Quantum.TraceInequality.HiaiPetz.Core.Basic

namespace HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder

noncomputable section MatrixScopedInstances

variable {n m : ℕ}

/-- Right multiplication by the identity is the identity operator.
Source: Hiai, Definition 6.1 right multiplication. -/
@[simp] theorem rightMul_one :
    rightMul (1 : Mₙ n) = (1 : HSOp n) := by
  ext X i j
  simp [rightMul_apply]

end MatrixScopedInstances

end HiaiPetz
