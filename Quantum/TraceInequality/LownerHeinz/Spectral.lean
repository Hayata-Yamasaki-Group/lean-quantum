/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LownerHeinz.Log

/-!
# Spectral-order reexports

This file is part of the split `LownerHeinzCore` development.
-/

namespace LownerHeinzCore

universe u

open CFC

namespace Spectral

variable {𝓐 : Type u} [CStarAlgebra 𝓐]
variable [Nontrivial 𝓐]

/-! ### Spectral-order reexports -/

section

-- Confine `spectralOrder` to this wrapper namespace.
-- We use local instances so the order change does not leak outside.
noncomputable local instance : PartialOrder 𝓐 := CStarAlgebra.spectralOrder 𝓐
noncomputable local instance : StarOrderedRing 𝓐 := CStarAlgebra.spectralOrderedRing 𝓐

-- Wrappers: expose the main theorems under spectral order without duplicating proofs.

omit [Nontrivial 𝓐] in
/-- Spectral-order version of `LownerHeinzCore.one_div_operatorAntitoneOn_Ioi`. -/
theorem one_div_operatorAntitoneOn_Ioi :
    OperatorAntitoneOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x) := by
  simpa using (LownerHeinzCore.one_div_operatorAntitoneOn_Ioi (𝓐 := 𝓐))

omit [Nontrivial 𝓐] in
/-- Spectral-order antitonicity of the reciprocal functional calculus. -/
@[gcongr]
theorem cfcR_one_div_le_cfcR_one_div_of_le {A B : 𝓐}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hBA : B ≤ A)
    (hspA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hspB : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    cfcR (fun x : ℝ ↦ 1 / x) A ≤ cfcR (fun x : ℝ ↦ 1 / x) B :=
  one_div_operatorAntitoneOn_Ioi hA hB hBA hspA hspB

/-- Spectral-order version of `LownerHeinzCore.operatorConvexOn_one_div_Ioi`. -/
theorem operatorConvexOn_one_div_Ioi :
    OperatorConvexOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x) := by
  simpa using (LownerHeinzCore.operatorConvexOn_one_div_Ioi (𝓐 := 𝓐))

omit [Nontrivial 𝓐] in
/-- Spectral-order version of `LownerHeinzCore.one_div_add_t_operatorAntitoneOn_Ici`. -/
theorem one_div_add_t_operatorAntitoneOn_Ici :
  ∀ t : ℝ, 0 < t →
    OperatorAntitoneOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ 1 / (x + t)) := by
  intro t ht
  simpa using (LownerHeinzCore.one_div_add_t_operatorAntitoneOn_Ici (𝓐 := 𝓐) t ht)

omit [Nontrivial 𝓐] in
/-- Spectral-order antitonicity of the shifted reciprocal functional calculus. -/
@[gcongr]
theorem cfcR_one_div_add_le_cfcR_one_div_add_of_le {t : ℝ} (ht : 0 < t)
    {A B : 𝓐} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hBA : B ≤ A)
    (hspA : spectrum ℝ A ⊆ Set.Ici (0 : ℝ))
    (hspB : spectrum ℝ B ⊆ Set.Ici (0 : ℝ)) :
    cfcR (fun x : ℝ ↦ 1 / (x + t)) A ≤ cfcR (fun x : ℝ ↦ 1 / (x + t)) B :=
  one_div_add_t_operatorAntitoneOn_Ici t ht hA hB hBA hspA hspB

/-- Spectral-order version of `LownerHeinzCore.operatorConvexOn_one_div_add_t_Ici`. -/
theorem operatorConvexOn_one_div_add_t_Ici :
  ∀ t : ℝ, 0 < t →
    OperatorConvexOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ 1 / (x + t)) := by
  intro t ht
  simpa using (LownerHeinzCore.operatorConvexOn_one_div_add_t_Ici (𝓐 := 𝓐) t ht)

omit [Nontrivial 𝓐] in
/-- Spectral-order version of `LownerHeinzCore.ratio_add_t_operatorMonotoneOn_Ici`. -/
theorem ratio_add_t_operatorMonotoneOn_Ici :
  ∀ t : ℝ, 0 < t →
    OperatorMonotoneOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x / (x + t)) := by
  intro t ht
  simpa using (LownerHeinzCore.ratio_add_t_operatorMonotoneOn_Ici (𝓐 := 𝓐) t ht)

omit [Nontrivial 𝓐] in
/-- Spectral-order monotonicity of the ratio functional calculus. -/
@[gcongr]
theorem cfcR_ratio_add_le_cfcR_ratio_add_of_le {t : ℝ} (ht : 0 < t)
    {A B : 𝓐} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hBA : B ≤ A)
    (hspA : spectrum ℝ A ⊆ Set.Ici (0 : ℝ))
    (hspB : spectrum ℝ B ⊆ Set.Ici (0 : ℝ)) :
    cfcR (fun x : ℝ ↦ x / (x + t)) B ≤ cfcR (fun x : ℝ ↦ x / (x + t)) A :=
  ratio_add_t_operatorMonotoneOn_Ici t ht hA hB hBA hspA hspB

/-- Spectral-order version of `LownerHeinzCore.operatorConcaveOn_ratio_add_t_Ici`. -/
theorem operatorConcaveOn_ratio_add_t_Ici :
  ∀ t : ℝ, 0 < t →
    OperatorConcaveOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x / (x + t)) := by
  intro t ht
  simpa using (LownerHeinzCore.operatorConcaveOn_ratio_add_t_Ici (𝓐 := 𝓐) t ht)

omit [Nontrivial 𝓐] in
/-- Spectral-order version of `LownerHeinzCore.power_Icc_zero_one_operatorMonotoneOn_Ici`. -/
theorem power_Icc_zero_one_operatorMonotoneOn_Ici : ∀ p ∈ Set.Icc (0 : ℝ) 1,
    OperatorMonotoneOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  simpa using (LownerHeinzCore.power_Icc_zero_one_operatorMonotoneOn_Ici (𝓐 := 𝓐) p hp)

omit [Nontrivial 𝓐] in
/-- Spectral-order monotonicity of real powers for exponents in `[0, 1]`. -/
@[gcongr]
theorem cfcR_rpow_le_cfcR_rpow_of_le {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    {A B : 𝓐} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hBA : B ≤ A)
    (hspA : spectrum ℝ A ⊆ Set.Ici (0 : ℝ))
    (hspB : spectrum ℝ B ⊆ Set.Ici (0 : ℝ)) :
    cfcR (fun x : ℝ ↦ x ^ p) B ≤ cfcR (fun x : ℝ ↦ x ^ p) A :=
  power_Icc_zero_one_operatorMonotoneOn_Ici p hp hA hB hBA hspA hspB

/-- Spectral-order version of `LownerHeinzCore.operatorConcaveOn_rpow_Ici`. -/
theorem operatorConcaveOn_rpow_Ici : ∀ p ∈ Set.Icc (0 : ℝ) 1,
    OperatorConcaveOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  simpa using (LownerHeinzCore.operatorConcaveOn_rpow_Ici (𝓐 := 𝓐) p hp)

/-- Spectral-order version of `LownerHeinzCore.operatorConvexOn_rpow_Ici`. -/
theorem operatorConvexOn_rpow_Ici : ∀ p ∈ Set.Icc (1 : ℝ) 2,
    OperatorConvexOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  simpa using (LownerHeinzCore.operatorConvexOn_rpow_Ici (𝓐 := 𝓐) p hp)

omit [Nontrivial 𝓐] in
/-- Spectral-order version of
`LownerHeinzCore.power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi`. -/
theorem power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi : ∀ p ∈ Set.Icc (-1 : ℝ) 0,
    OperatorMonotoneOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x ↦ -(x ^ p)) := by
  intro p hp
  simpa using (LownerHeinzCore.power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi (𝓐 := 𝓐) p hp)

omit [Nontrivial 𝓐] in
/-- Spectral-order monotonicity of negative real powers after negation. -/
@[gcongr]
theorem cfcR_neg_rpow_le_cfcR_neg_rpow_of_le {p : ℝ}
    (hp : p ∈ Set.Icc (-1 : ℝ) 0) {A B : 𝓐}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hBA : B ≤ A)
    (hspA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hspB : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    cfcR (fun x : ℝ ↦ -(x ^ p)) B ≤ cfcR (fun x : ℝ ↦ -(x ^ p)) A :=
  power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi p hp hA hB hBA hspA hspB

/-- Spectral-order version of
`LownerHeinzCore.operatorConcaveOn_neg_rpow_Ioi`. -/
theorem operatorConcaveOn_neg_rpow_Ioi : ∀ p ∈ Set.Icc (-1 : ℝ) 0,
    OperatorConcaveOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x ↦ -(x ^ p)) := by
  intro p hp
  simpa using (LownerHeinzCore.operatorConcaveOn_neg_rpow_Ioi (𝓐 := 𝓐) p hp)

omit [Nontrivial 𝓐] in
/-- Spectral-order version of `LownerHeinzCore.power_Icc_neg_one_zero_operatorAntitoneOn_Ioi`. -/
theorem power_Icc_neg_one_zero_operatorAntitoneOn_Ioi (p : ℝ)
    (hp : p ∈ Set.Icc (-1 : ℝ) 0) :
    OperatorAntitoneOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x ↦ x ^ p) := by
  simpa using (LownerHeinzCore.power_Icc_neg_one_zero_operatorAntitoneOn_Ioi (𝓐 := 𝓐) p hp)

end

end Spectral

end LownerHeinzCore
