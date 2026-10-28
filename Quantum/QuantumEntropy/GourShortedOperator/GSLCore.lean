/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumEntropy.PetzTraceClassification.GSLCore
import Quantum.QuantumEntropy.Common.PositiveDefinitePerturbation
import Quantum.QuantumEntropy.Common.PositiveDefiniteTensor
import Quantum.TraceInequality.LiebTrace.Monotonicity
import Quantum.QuantumEntropy.TensorCFCUmegaki
import Quantum.QuantumEntropy.TensorCFC
import Quantum.QuantumEntropy.Common.PositiveDefiniteCertificatesGeneralizedStein
import Quantum.QuantumMechanics.QuantumStateGeneralizedStein

/-!
# Positive definiteness and the positive-definite set

`isPositiveDefinite_iff_mem_pdSetLM`: an operator is positive definite exactly when it lies in
`pdSetLM`.
-/

namespace OPT

open QuantumState
open SandwichedRenyiRelativeEntropy
open scoped ComplexOrder

universe u v

variable {H : Type u} [Qudit H]
variable {A : L H}

/-- The public positive-definite predicate agrees with the analytic `pdSetLM` domain. -/
theorem isPositiveDefinite_iff_mem_pdSetLM [Nontrivial H] (A : L H) :
    IsPositiveDefinite A ↔ A ∈ pdSetLM := by
  constructor
  · rintro ⟨hA, hdet⟩
    apply pdSetLM_of_nonneg_isUnit
    · exact (LinearMap.nonneg_iff_isPositive A).mpr hA
    · exact (LinearMap.isUnit_iff_isUnit_det A).mpr
        (isUnit_iff_ne_zero.mpr hdet)
  · intro hA
    refine ⟨(LinearMap.nonneg_iff_isPositive A).mp (nonneg_of_pdSetLM hA), ?_⟩
    exact isUnit_iff_ne_zero.mp
      ((LinearMap.isUnit_iff_isUnit_det A).mp (isUnit_of_pdSetLM hA))

end OPT
