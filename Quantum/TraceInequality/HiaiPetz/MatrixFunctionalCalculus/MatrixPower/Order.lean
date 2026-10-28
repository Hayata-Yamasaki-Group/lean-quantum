/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.MatrixPower.Basic

/-!
# Order properties of matrix real powers

This file transports Hansen-Pedersen and Loewner-Heinz order results from
continuous linear operators on Euclidean space back to finite complex matrices.
The main outputs are concavity and monotonicity of `matrixPower r` on the
positive semidefinite cone, plus antitonicity for negative powers on positive
definite matrices.

## Main results

* `matrixPower_concave_nonneg`: operator concavity of `A ↦ A ^ r` for
  `0 ≤ r ≤ 1` on nonnegative matrices.
* `matrixPower_monotone_nonneg`: Loewner-Heinz monotonicity for matrix powers
  with exponent in `[0, 1]`.
* `matrixPower_antitone_neg_Icc_posDef`: order reversal for powers
  `-1 ≤ s ≤ 0` on positive-definite matrices.

## References

* Hiai, *Matrix analysis and its applications*,
  SGC Library 200, Saiensu-sha, 2025, Chapter 6 matrix-power calculus.
* Hiai-Yanagi, Section 5.1, Loewner-Heinz and Hansen-Pedersen consequences.
-/

namespace HiaiPetz

open scoped ComplexOrder MatrixOrder

noncomputable section MatrixScopedInstances

variable {n : ℕ}

/- Instance cache: the real scalar action (`Module ℝ`) on Euclidean CLMs used by
`•` in the Hansen-Pedersen transport exceeds the default `synthInstance`
heartbeat budget per search and is re-run at every use site. Caching it as a
section-level reducible instance makes each search a head-match (same pattern
as `Composition.lean` and `JensenOperatorInequality.lean`). -/
/-- Local cached real module structure on Euclidean continuous linear maps,
used by scalar convex combinations after transporting matrix order goals. -/
@[reducible, local instance]
private noncomputable def instModuleRealEuclideanCLMScoped :
    Module ℝ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  inferInstance

/-- Local cached distributive real scalar action on Euclidean continuous linear
maps, used by transported Hansen-Pedersen convexity statements. -/
@[reducible, local instance]
private noncomputable def instDistribSMulRealEuclideanCLMScoped :
    DistribSMul ℝ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  inferInstance

/-- Transport of `matrixPower` through the star-algebra equivalence
`Matrix.toEuclideanCLM`: the matrix-side real power `matrixPower r` is carried
to the CLM-side real functional calculus of `x ^ r`. This is the heavy
normalization step shared by the Hansen-Pedersen transport proofs below,
factored out so it elaborates only once per use instead of inside a large
`simp` call. -/
private lemma toEuclideanCLM_matrixPower (r : ℝ) (A : Mₙ n) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (matrixPower r A) =
      LownerHeinzTheorem.cfcR (fun x : ℝ => x ^ r)
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A) := by
  simp only [matrixPower, HansenPedersen.matrixCfcR, StarAlgEquiv.apply_symm_apply]
  rfl

/-- Hansen-Pedersen concavity of `x ↦ x ^ r` on the Euclidean operator side, written with the
weights in the order used by `matrixPower_concave_nonneg`. -/
private lemma rpow_cfcR_concave_euclidean [Nontrivial (EuclideanSpace ℂ (Fin n))] {r t : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {X Y : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)}
    (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y)
    (hXs : spectrum ℝ X ⊆ Set.Ici (0 : ℝ)) (hYs : spectrum ℝ Y ⊆ Set.Ici (0 : ℝ)) :
    t • LownerHeinzTheorem.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) (fun x : ℝ => x ^ r) X +
        (1 - t) • LownerHeinzTheorem.cfcR (ℋ := EuclideanSpace ℂ (Fin n))
          (fun x : ℝ => x ^ r) Y ≤
      LownerHeinzTheorem.cfcR (ℋ := EuclideanSpace ℂ (Fin n))
        (fun x : ℝ => x ^ r) (t • X + (1 - t) • Y) := by
  have h :=
    HansenPedersen.rpow_operatorConcaveOnInterval_Ici
      (ℋ := EuclideanSpace ℂ (Fin n)) (p := r) hr (A := Y) (B := X) (t := t)
      hY hX ht.1 ht.2 hYs hXs
  dsimp [HansenPedersen.OperatorConcaveOnInterval, LownerHeinzTheorem.OperatorConcaveOn,
    LownerHeinzCore.OperatorConcaveOn, LownerHeinzCore.OperatorConvexOn,
    LownerHeinzCore.cfcR] at h
  have hneg := neg_le_neg h
  simpa [LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR, cfc_neg, smul_add,
    add_comm, add_left_comm, add_assoc] using hneg

-- CLM CFC order instances are deep for matrix-to-operator transport.
-- Hansen-Pedersen concavity transported through `Matrix.toEuclideanCLM`.
/-- Matrix real powers are concave on the nonnegative cone for exponents
`r ∈ [0, 1]`; the scalar `t` is a convex-combination weight in `[0, 1]`.
Local API: Hiai-Yanagi, Hansen-Pedersen concavity consequence of Loewner-Heinz. -/
theorem matrixPower_concave_nonneg {n : ℕ} {r t : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {B1 B2 : Mₙ n} (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) :
    t • matrixPower r B1 + (1 - t) • matrixPower r B2 ≤
      matrixPower r (t • B1 + (1 - t) • B2) := by
  by_cases hn : n = 0
  · subst n
    exact le_of_eq (Subsingleton.elim _ _)
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    euclideanNontrivial_of_fin_ne_zero hn
  let φ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hB1sa : IsSelfAdjoint (φ B1) :=
    IsSelfAdjoint.of_nonneg (toEuclideanCLM_nonneg_of_matrix_nonneg hB1)
  have hB2sa : IsSelfAdjoint (φ B2) :=
    IsSelfAdjoint.of_nonneg (toEuclideanCLM_nonneg_of_matrix_nonneg hB2)
  have hspec1 : spectrum ℝ (φ B1) ⊆ Set.Ici (0 : ℝ) :=
    toEuclideanCLM_spectrum_Ici_of_matrix_nonneg hB1
  have hspec2 : spectrum ℝ (φ B2) ⊆ Set.Ici (0 : ℝ) :=
    toEuclideanCLM_spectrum_Ici_of_matrix_nonneg hB2
  have hraw :=
    rpow_cfcR_concave_euclidean (n := n) hr ht hB1sa hB2sa hspec1 hspec2
  have hpush :
      φ (t • matrixPower r B1 + (1 - t) • matrixPower r B2) ≤
        φ (matrixPower r (t • B1 + (1 - t) • B2)) := by
    simp only [φ, map_add, toEuclideanCLM_real_smul, toEuclideanCLM_matrixPower]
    exact hraw
  exact ((show
      φ (t • matrixPower r B1 + (1 - t) • matrixPower r B2) ≤
        φ (matrixPower r (t • B1 + (1 - t) • B2)) ↔
      t • matrixPower r B1 + (1 - t) • matrixPower r B2 ≤
        matrixPower r (t • B1 + (1 - t) • B2) from map_le_map_iff φ)).1 hpush

-- CLM CFC order instances are deep for matrix-to-operator transport.
-- Hansen-Pedersen monotonicity transported through `Matrix.toEuclideanCLM`.
/-- Loewner-Heinz monotonicity for matrix real powers: if
`0 ≤ B1 ≤ B2` and `r ∈ [0, 1]`, then `B1 ^ r ≤ B2 ^ r`.
Source: Hiai-Yanagi, Theorem 5.1.1. -/
theorem matrixPower_monotone_nonneg {n : ℕ} {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1)
    {B1 B2 : Mₙ n} (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (hle : B1 ≤ B2) :
    matrixPower r B1 ≤ matrixPower r B2 := by
  by_cases hn : n = 0
  · subst n
    simp
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    euclideanNontrivial_of_fin_ne_zero hn
  let φ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hmono :=
    HansenPedersen.rpow_operatorMonotoneOnInterval_Ici
      (ℋ := EuclideanSpace ℂ (Fin n)) (p := r) hr
  have hB1sa : IsSelfAdjoint (φ B1) :=
    IsSelfAdjoint.of_nonneg (toEuclideanCLM_nonneg_of_matrix_nonneg hB1)
  have hB2sa : IsSelfAdjoint (φ B2) :=
    IsSelfAdjoint.of_nonneg (toEuclideanCLM_nonneg_of_matrix_nonneg hB2)
  have hspec1 : spectrum ℝ (φ B1) ⊆ Set.Ici (0 : ℝ) :=
    toEuclideanCLM_spectrum_Ici_of_matrix_nonneg hB1
  have hspec2 : spectrum ℝ (φ B2) ⊆ Set.Ici (0 : ℝ) :=
    toEuclideanCLM_spectrum_Ici_of_matrix_nonneg hB2
  have hleφ : φ B1 ≤ φ B2 :=
    ((show φ B1 ≤ φ B2 ↔ B1 ≤ B2 from map_le_map_iff φ)).2 hle
  have h :=
    hmono (A := φ B1) (B := φ B2) hB1sa hB2sa hspec1 hspec2 hleφ
  have hpush : φ (matrixPower r B1) ≤ φ (matrixPower r B2) := by
    simpa [matrixPower, HansenPedersen.matrixCfcR, φ, powerFn, LownerHeinzTheorem.cfcR] using h
  exact ((show φ (matrixPower r B1) ≤ φ (matrixPower r B2) ↔
      matrixPower r B1 ≤ matrixPower r B2 from map_le_map_iff φ)).1 hpush

attribute [gcongr] matrixPower_monotone_nonneg

-- CLM CFC order instances are deep for negative-power antitonicity.
-- Loewner-Heinz negative-power order transported through `Matrix.toEuclideanCLM`.
/-- Negative real powers are antitone on positive-definite matrices for
exponents `s ∈ [-1, 0]`: from `C ≤ D` one obtains `D ^ s ≤ C ^ s`.
Local API: Hiai-Yanagi, negative-power Loewner-Heinz consequence. -/
theorem matrixPower_antitone_neg_Icc_posDef {n : ℕ} {s : ℝ}
    (hs : s ∈ Set.Icc (-1 : ℝ) 0)
    {C D : Mₙ n} (hC : Matrix.PosDef C) (hD : Matrix.PosDef D) (hle : C ≤ D) :
    matrixPower s D ≤ matrixPower s C := by
  by_cases hn : n = 0
  · subst n
    simp
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    euclideanNontrivial_of_fin_ne_zero hn
  let φ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hmono :=
    LownerHeinzTheorem.power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi
      (ℋ := EuclideanSpace ℂ (Fin n)) s hs
  have hCnonneg : 0 ≤ φ C :=
    toEuclideanCLM_nonneg_of_matrix_nonneg (Matrix.PosDef.nonneg hC)
  have hDnonneg : 0 ≤ φ D :=
    toEuclideanCLM_nonneg_of_matrix_nonneg (Matrix.PosDef.nonneg hD)
  have hCspec : spectrum ℝ (φ C) ⊆ Set.Ioi (0 : ℝ) :=
    toEuclideanCLM_spectrum_Ioi_of_matrix_posDef hC
  have hDspec : spectrum ℝ (φ D) ⊆ Set.Ioi (0 : ℝ) :=
    toEuclideanCLM_spectrum_Ioi_of_matrix_posDef hD
  have hleφ : φ C ≤ φ D :=
    ((show φ C ≤ φ D ↔ C ≤ D from map_le_map_iff φ)).2 hle
  have hCsa : IsSelfAdjoint (φ C) := IsSelfAdjoint.of_nonneg hCnonneg
  have hDsa : IsSelfAdjoint (φ D) := IsSelfAdjoint.of_nonneg hDnonneg
  have h :=
    hmono (A := φ D) (B := φ C) hDsa hCsa hleφ hDspec hCspec
  have hpush : φ (matrixPower s D) ≤ φ (matrixPower s C) := by
    have hneg := neg_le_neg h
    simpa [matrixPower, HansenPedersen.matrixCfcR, φ, powerFn,
      LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR, cfc_neg] using hneg
  exact ((show φ (matrixPower s D) ≤ φ (matrixPower s C) ↔
      matrixPower s D ≤ matrixPower s C from map_le_map_iff φ)).1 hpush

attribute [gcongr] matrixPower_antitone_neg_Icc_posDef

end MatrixScopedInstances

end HiaiPetz
