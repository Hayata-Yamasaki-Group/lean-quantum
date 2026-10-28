/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.NativeTraceDistance.GSLCore
import Quantum.QuantumModel.NativeTraceDistance.GSLCoreRetained
import Quantum.OperationalProbabilistic.Framework.ExactCompression.GSLCore
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.ENNReal.Inv
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Native quantum fidelity

The operator root fidelity of density matrices, finite POVMs with their Born distributions,
the classical root fidelity and root overlap, the measured POVM root fidelity, and channel
application to density matrices.
-/

noncomputable section

namespace QuantumModel
namespace NativeFidelity

open CategoryTheory
open QuantumState
open scoped ENNReal MonoidalCategory

/-- Textbook operator root-fidelity expression
`F_R(rho,sigma) = Tr |sqrt rho * sqrt sigma|`.

The name `operatorRootFidelity` distinguishes this operator expression from the
measurement-based root overlap.  For every finite POVM `M`, this development proves
`operatorRootFidelity rho sigma ≤ M.rootOverlap rho sigma`
(`operatorRootFidelity_le_rootOverlap`); the Fuchs--Caves equality with the infimum over
measurements is not formalized. -/
def operatorRootFidelity {A : Sys}
    (rho sigma : DensityMatrix A) : ℝ :=
  NativeTraceDistance.traceNorm
    ((CFC.sqrt rho.operator).comp (CFC.sqrt sigma.operator))

/-- The operator root-fidelity expression is nonnegative. -/
theorem operatorRootFidelity_nonneg {A : Sys}
    (rho sigma : DensityMatrix A) :
    0 ≤ operatorRootFidelity rho sigma := by
  let X : Operator A :=
    (CFC.sqrt rho.operator).comp (CFC.sqrt sigma.operator)
  have hpositive : (CFC.abs X).IsPositive :=
    (LinearMap.nonneg_iff_isPositive (CFC.abs X)).mp (CFC.abs_nonneg X)
  exact (Complex.nonneg_iff.mp hpositive.trace_nonneg).1

end NativeFidelity
end QuantumModel
