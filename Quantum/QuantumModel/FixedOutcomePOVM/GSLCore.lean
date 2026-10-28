/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.NativeFidelity.GSLCore
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Fixed-outcome native POVMs

`FixedOutcomePOVM A ι` is the type of native POVMs with the prescribed finite outcome type `ι`,
realized on the carrier `fixedOutcomePOVMCarrier`, with its Born PMF.
-/

noncomputable section

namespace QuantumModel

open QuantumState Set
open NativeFidelity
open scoped ENNReal Topology

/-- Families of effects satisfying positivity and normalization for a fixed
finite outcome type. -/
def fixedOutcomePOVMCarrier (A : Sys) (ι : Type) [Fintype ι] :
    Set (ι → Operator A) :=
  {E | (∀ i, 0 ≤ E i) ∧ Finset.univ.sum E = LinearMap.id}

/-- A native POVM whose finite outcome type is fixed externally.  The
carrier may have outcome type `Fin (A.dim ^ 2)`. -/
def FixedOutcomePOVM (A : Sys) (ι : Type) [Fintype ι] :=
  ↥(fixedOutcomePOVMCarrier A ι)

namespace FixedOutcomePOVM

variable {A : Sys} {ι κ : Type} [Fintype ι] [Fintype κ]

/-- The effect in a fixed outcome slot. -/
def effect (M : FixedOutcomePOVM A ι) (i : ι) : Operator A :=
  M.1 i

/-- Every fixed-outcome effect is nonnegative.  Zero is permitted. -/
theorem nonneg (M : FixedOutcomePOVM A ι) (i : ι) :
    0 ≤ M.effect i :=
  M.2.1 i

/-- The fixed-outcome effects sum to the identity. -/
theorem sum_eq_id (M : FixedOutcomePOVM A ι) :
    Finset.univ.sum M.effect = LinearMap.id :=
  M.2.2

/-- Forget the fixed external outcome type and obtain the bundled native
POVM used by the measured divergence over all finite POVMs. -/
def toPOVM (M : FixedOutcomePOVM A ι) : POVM A where
  ι := ι
  effect := M.effect
  nonneg := M.nonneg
  sum_eq_id := M.sum_eq_id

/-- Born PMF of a fixed-outcome POVM. -/
noncomputable def bornPMF (M : FixedOutcomePOVM A ι)
    (rho : DensityMatrix A) : PMF ι :=
  M.toPOVM.bornPMF rho

@[simp]
theorem bornPMF_apply (M : FixedOutcomePOVM A ι)
    (rho : DensityMatrix A) (i : ι) :
    M.bornPMF rho i = ENNReal.ofReal
      (NativeNoCloning.bornProbability (M.effect i) rho) :=
  rfl

end FixedOutcomePOVM
end QuantumModel
