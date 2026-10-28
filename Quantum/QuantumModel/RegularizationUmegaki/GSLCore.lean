/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCoreGeneralizedStein
import Quantum.QuantumMechanics.QuantumChannelCompat.GSLCore
import Quantum.QuantumMechanics.BridgeCertificates
import Quantum.QuantumEntropy.HaarUnitaryLM.GSLCore
import Quantum.QuantumEntropy.SandwichedRenyiUmegakiKWExtra.GSLCore
import Quantum.QuantumEntropy.VonNeumann.Basic
import Quantum.QuantumEntropy.VonNeumann.StateTensor
import Quantum.QuantumModel.RegularizationCarrier.GSLCore
import Quantum.QuantumModel.RegularizationCarrier.GSLCoreRetained

/-!
# Support inclusion: native and Hilbert-space forms

`supportLE_iff_suppLE` identifies the support order of native density matrices with the support
inclusion of their Hilbert-space operators.
-/

noncomputable section

open QuantumState TensorProduct
open scoped TensorProduct

namespace QuantumModel
namespace DensityMatrix

/-- Native range support equals the entropy layer's reverse-kernel support for density matrices. -/
theorem supportLE_iff_suppLE {A : Sys}
    (rho sigma : DensityMatrix A) :
    SupportLE rho sigma ↔
      SandwichedRenyiRelativeEntropy.suppLE rho.operator sigma.operator := by
  have hrho : rho.operator.IsSymmetric :=
    (LinearMap.nonneg_iff_isPositive rho.operator).mp rho.nonneg |>.isSymmetric
  have hsigma : sigma.operator.IsSymmetric :=
    (LinearMap.nonneg_iff_isPositive sigma.operator).mp sigma.nonneg |>.isSymmetric
  unfold SupportLE supportSubspace SandwichedRenyiRelativeEntropy.suppLE
  exact (ContinuousLinearMap.ker_le_ker_iff_range_le_range
    (T := rho.operator.toContinuousLinearMap)
    (U := sigma.operator.toContinuousLinearMap) hrho hsigma).symm

end DensityMatrix
end QuantumModel

namespace OPT
namespace Decomposition

open SandwichedRenyiRelativeEntropy

end Decomposition
end OPT

namespace QuantumModel

open SandwichedRenyiRelativeEntropy

end QuantumModel
