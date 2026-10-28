/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.OperationalProbabilistic.Framework.OrderedConeMaxRelativeEntropy.GSLCore
import Quantum.QuantumMechanics.DensityOperator.GSLCore
import Quantum.QuantumEntropy.PetzRenyiRelativeEntropyLaws.GSLCore
import Quantum.QuantumEntropy.PetzRenyiSpectralReduction.GSLCore
import Quantum.QuantumEntropy.TensorCFCUmegaki
import Quantum.QuantumEntropy.TensorCFC
import Mathlib.Analysis.SpecialFunctions.Log.Base

open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower ℝ ℂ (L H) :=
  RestrictScalars.isScalarTower ℝ ℂ (L H)


open QuantumState QuantumChannel TensorProduct
open SandwichedRenyiRelativeEntropy

/-!
# Quantum max-relative entropy

The bit-valued, extended-real quantum max-relative entropy (Gour, eq. (6.112)), defined at the
ordered-cone level.
-/

namespace OPT

noncomputable section

universe u v

/-! ## A. The bit-valued ordered-cone definition -/

/-- The quantum max-relative entropy in bits for a pair of density
operators. -/
noncomputable def quantumMaxRelativeEntropyBits
    {H : Type u} [Qudit H] [Nontrivial H]
    (rho sigma : QuantumDensityMatrix H) : EReal :=
  OrderedCone.maxRelEntropy rho.1 sigma.1

end

end OPT
