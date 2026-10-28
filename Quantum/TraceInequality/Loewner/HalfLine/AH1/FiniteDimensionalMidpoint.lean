/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HansenPedersen.Basic
import Quantum.TraceInequality.HiaiPetzTheorem.Basic
import Quantum.TraceInequality.HiaiPetz.Basic
import Quantum.TraceInequality.HiaiPetz.FinMatrixCStar
import Quantum.Analysis.Topology.SOTContinuity

/-!
# Finite-dimensional midpoint-convexity transport

This file supplies the finite-dimensional part of the positive-ray
Hansen--Pedersen midpoint lift without importing the Hansen--Pedersen theorem capsule.
-/

namespace Quantum.TraceInequality.Loewner

open CFC
open scoped CStarAlgebra FinMatrixCStar MatrixOrder Topology

private theorem gap2_starAlgEquiv_real_spectrum_eq
    {A B : Type*} [Ring A] [Ring B] [Star A] [Star B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra ℝ A] [Algebra ℝ B]
    [IsScalarTower ℝ ℂ A] [IsScalarTower ℝ ℂ B]
    (φ : A ≃⋆ₐ[ℂ] B) (a : A) :
    spectrum ℝ (φ a) = spectrum ℝ a := by
  simpa using AlgEquiv.spectrum_eq (φ.restrictScalars ℝ) a

private theorem gap2_starAlgEquiv_cfcR_transport
    {K E : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [ContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint]
    {J : Set ℝ} {f : ℝ → ℝ} {A : K →L[ℂ] K}
    (φ : (K →L[ℂ] K) ≃⋆ₐ[ℂ] (E →L[ℂ] E))
    (hfJ : ContinuousOn f J) (hσA : spectrum ℝ A ⊆ J) (hA : IsSelfAdjoint A) :
    φ (cfc (R := ℝ) f A) = cfc (R := ℝ) f (φ A) := by
  letI : IsScalarTower ℝ ℂ (K →L[ℂ] K) :=
    RestrictScalars.isScalarTower ℝ ℂ (K →L[ℂ] K)
  letI : NormedSpace ℝ (HansenPedersen.Mₙ (Module.finrank ℂ K)) :=
    NormedSpace.restrictScalars ℝ ℂ _
  letI : Algebra ℝ (HansenPedersen.Mₙ (Module.finrank ℂ K)) := inferInstance
  letI : SMul ℝ (HansenPedersen.Mₙ (Module.finrank ℂ K)) := inferInstance
  letI : Module ℝ (HansenPedersen.Mₙ (Module.finrank ℂ K)) := inferInstance
  letI : IsScalarTower ℝ ℂ (HansenPedersen.Mₙ (Module.finrank ℂ K)) :=
    RestrictScalars.isScalarTower ℝ ℂ _
  letI : IsScalarTower ℝ ℂ (E →L[ℂ] E) :=
    RestrictScalars.isScalarTower ℝ ℂ (E →L[ℂ] E)
  let φR := φ.restrictScalars ℝ
  have hφRA : IsSelfAdjoint (φR A) := by
    have h1 : φR (star A) = φR A := congrArg φR hA
    simpa [map_star] using h1
  have hφcont : Continuous φ := (StarAlgEquiv.isometry φ).continuous
  simpa [φR] using
    StarAlgHomClass.map_cfc φR f A (hf := hfJ.mono hσA)
      (hφ := by simpa [φR] using hφcont) (ha := hA) (hφa := hφRA)

private theorem gap2_order_bounds_of_spectrum_subset_Icc
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    {T : K →L[ℂ] K} {α β : ℝ} (hT : IsSelfAdjoint T)
    (hσ : spectrum ℝ T ⊆ Set.Icc α β) :
    (α : ℂ) • (1 : K →L[ℂ] K) ≤ T ∧ T ≤ (β : ℂ) • (1 : K →L[ℂ] K) := by
  constructor
  · exact (algebraMap_le_iff_le_spectrum (R := ℝ) (A := K →L[ℂ] K)
      (p := IsSelfAdjoint) (r := α) (a := T) (ha := hT)).2
      (by intro x hx; exact (hσ hx).1)
  · exact (le_algebraMap_iff_spectrum_le (R := ℝ) (A := K →L[ℂ] K)
      (p := IsSelfAdjoint) (r := β) (a := T) (ha := hT)).2
      (by intro x hx; exact (hσ hx).2)

private theorem gap2_spectrum_subset_Icc_of_order_bounds
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)]
    {T : K →L[ℂ] K} {α β : ℝ} (hT : IsSelfAdjoint T)
    (hlow : (α : ℂ) • (1 : K →L[ℂ] K) ≤ T)
    (hupp : T ≤ (β : ℂ) • (1 : K →L[ℂ] K)) :
    spectrum ℝ T ⊆ Set.Icc α β := by
  intro x hx
  constructor
  · exact (algebraMap_le_iff_le_spectrum (R := ℝ) (A := K →L[ℂ] K)
      (p := IsSelfAdjoint) (r := α) (a := T) (ha := hT)).1 hlow x hx
  · exact (le_algebraMap_iff_spectrum_le (R := ℝ) (A := K →L[ℂ] K)
      (p := IsSelfAdjoint) (r := β) (a := T) (ha := hT)).1 hupp x hx

private theorem gap2_exists_compact_interval_subset_of_two_spectra
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)]
    {J : Set ℝ} {S T : K →L[ℂ] K} (hS : IsSelfAdjoint S)
    (hσS : spectrum ℝ S ⊆ J) (hσT : spectrum ℝ T ⊆ J) (hJ : Convex ℝ J) :
    ∃ α β : ℝ,
      spectrum ℝ S ∪ spectrum ℝ T ⊆ Set.Icc α β ∧ Set.Icc α β ⊆ J := by
  let X : Set ℝ := spectrum ℝ S ∪ spectrum ℝ T
  have hXcompact : IsCompact X := by
    simpa [X] using
      (ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) S).union
        (ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) T)
  have hXne : X.Nonempty :=
    (ContinuousFunctionalCalculus.spectrum_nonempty S hS).mono
      (by intro x hx; exact Or.inl hx)
  refine ⟨sInf X, sSup X,
    subset_Icc_csInf_csSup hXcompact.bddBelow hXcompact.bddAbove, ?_⟩
  have hsInf_mem : sInf X ∈ X := hXcompact.sInf_mem hXne
  have hsSup_mem : sSup X ∈ X := hXcompact.sSup_mem hXne
  have hXJ : X ⊆ J := by
    intro x hx
    rcases hx with hxS | hxT
    · exact hσS hxS
    · exact hσT hxT
  exact hJ.ordConnected.out (hXJ hsInf_mem) (hXJ hsSup_mem)

private lemma gap2_toEuclideanCLM_matrixCfcR
    {n : ℕ} (f : ℝ → ℝ) (m : HansenPedersen.Mₙ n) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (HansenPedersen.matrixCfcR f m) =
      cfc (R := ℝ) f (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) m) := by
  simp [HansenPedersen.matrixCfcR]

/-- A common lower bound of two elements bounds their midpoint. -/
private theorem gap2_le_midpoint {A : Type*} [AddCommGroup A] [PartialOrder A]
    [IsOrderedAddMonoid A] [Module ℝ A] [PosSMulMono ℝ A] {x y z : A}
    (hy : x ≤ y) (hz : x ≤ z) : x ≤ (1 / 2 : ℝ) • (y + z) := by
  have h := smul_le_smul_of_nonneg_left (add_le_add hy hz) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rwa [← two_smul ℝ x, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h

/-- A common upper bound of two elements bounds their midpoint. -/
private theorem gap2_midpoint_le {A : Type*} [AddCommGroup A] [PartialOrder A]
    [IsOrderedAddMonoid A] [Module ℝ A] [PosSMulMono ℝ A] {x y z : A}
    (hy : y ≤ x) (hz : z ≤ x) : (1 / 2 : ℝ) • (y + z) ≤ x := by
  have h := smul_le_smul_of_nonneg_left (add_le_add hy hz) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rwa [← two_smul ℝ x, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h

/-- The midpoint of two self-adjoint operators with spectra in a convex set `J` is self-adjoint
with spectrum in `J`. -/
private theorem gap2_midpoint_isSelfAdjoint_spectrum_subset
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)]
    {J : Set ℝ} (hJ : Convex ℝ J)
    {S T : K →L[ℂ] K} (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (hσS : spectrum ℝ S ⊆ J) (hσT : spectrum ℝ T ⊆ J) :
    IsSelfAdjoint ((1 / 2 : ℝ) • (S + T)) ∧ spectrum ℝ ((1 / 2 : ℝ) • (S + T)) ⊆ J := by
  have hM : IsSelfAdjoint ((1 / 2 : ℝ) • (S + T)) := (IsSelfAdjoint.all _).smul (hS.add hT)
  obtain ⟨α, β, hHull, hIccJ⟩ :=
    gap2_exists_compact_interval_subset_of_two_spectra hS hσS hσT hJ
  have hS_bounds := gap2_order_bounds_of_spectrum_subset_Icc hS
    (fun x hx => hHull (Or.inl hx))
  have hT_bounds := gap2_order_bounds_of_spectrum_subset_Icc hT
    (fun x hx => hHull (Or.inr hx))
  exact ⟨hM, fun x hx => hIccJ (gap2_spectrum_subset_Icc_of_order_bounds hM
    (gap2_le_midpoint hS_bounds.1 hT_bounds.1) (gap2_midpoint_le hS_bounds.2 hT_bounds.2) hx)⟩

/-- A continuous star-algebra equivalence commutes with the midpoint. -/
private theorem gap2_starAlgEquiv_map_midpoint
    {K E : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (φ : (K →L[ℂ] K) ≃⋆ₐ[ℂ] (E →L[ℂ] E)) (hφcont : Continuous φ) (S T : K →L[ℂ] K) :
    φ ((1 / 2 : ℝ) • (S + T)) = (1 / 2 : ℝ) • (φ S + φ T) := by
  rw [map_real_smul φ hφcont, map_add]

/-- `Matrix.toEuclideanCLM` commutes with real scalar multiplication. -/
private theorem gap2_toEuclideanCLM_real_smul {d : ℕ} (r : ℝ) (Y : HansenPedersen.Mₙ d) :
    Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (r • Y) =
      r • Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) Y := by
  have h : r • Y = (r : ℂ) • Y := by
    ext i j
    simp [Complex.real_smul]
  rw [h, map_smul, Complex.coe_smul]

/-- The inverse of `Matrix.toEuclideanCLM` commutes with real scalar multiplication. -/
private theorem gap2_toEuclideanCLM_symm_real_smul {d : ℕ} (r : ℝ)
    (X : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm (r • X) =
      r • (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm X := by
  have h : r • (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm X =
      (r : ℂ) • (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm X := by
    ext i j
    simp [Complex.real_smul]
  rw [h, ← Complex.coe_smul, map_smul]

/-- The matrix real CFC of `toEuclideanCLM.symm X`, sent back by `toEuclideanCLM`, is the
operator real CFC of `X`. -/
private theorem gap2_toEuclideanCLM_matrixCfcR_symm {d : ℕ} (f : ℝ → ℝ)
    (X : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :
    Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
        (HansenPedersen.matrixCfcR f ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm X)) =
      cfc (R := ℝ) f X := by
  rw [gap2_toEuclideanCLM_matrixCfcR, StarAlgEquiv.apply_symm_apply]

/-- The inverse of `Matrix.toEuclideanCLM` preserves the real spectrum. -/
private theorem gap2_toEuclideanCLM_symm_spectrum {d : ℕ}
    (X : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :
    spectrum ℝ ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm X) = spectrum ℝ X := by
  letI : IsScalarTower ℝ ℂ (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :=
    RestrictScalars.isScalarTower ℝ ℂ _
  exact gap2_starAlgEquiv_real_spectrum_eq (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm X

/-- The matrix-model midpoint inequality, sent to operators by `Matrix.toEuclideanCLM`. -/
private theorem gap2_toEuclideanCLM_matrix_midpoint {d : ℕ}
    {J : Set ℝ} {f : ℝ → ℝ}
    (hmat : HansenPedersen.MatrixOperatorMidpointConvexOnInterval J f)
    {X Y : HansenPedersen.Mₙ d} (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y)
    (hσX : spectrum ℝ X ⊆ J) (hσY : spectrum ℝ Y ⊆ J) :
    Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
        (HansenPedersen.matrixCfcR f ((1 / 2 : ℝ) • (X + Y))) ≤
      (1 / 2 : ℝ) •
        (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (HansenPedersen.matrixCfcR f X) +
          Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (HansenPedersen.matrixCfcR f Y)) := by
  rw [← map_add, ← gap2_toEuclideanCLM_real_smul]
  exact (map_le_map_iff (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ))).2 (hmat hX hY hσX hσY)

/-- The matrix-model midpoint inequality, read on operators on `EuclideanSpace ℂ (Fin d)`. -/
private theorem gap2_euclidean_midpoint_of_matrix {d : ℕ}
    {J : Set ℝ} {f : ℝ → ℝ}
    (hmat : HansenPedersen.MatrixOperatorMidpointConvexOnInterval J f)
    {S T : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)}
    (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (hσS : spectrum ℝ S ⊆ J) (hσT : spectrum ℝ T ⊆ J) :
    cfc (R := ℝ) f ((1 / 2 : ℝ) • (S + T)) ≤
      (1 / 2 : ℝ) • (cfc (R := ℝ) f S + cfc (R := ℝ) f T) := by
  have h := gap2_toEuclideanCLM_matrix_midpoint hmat
    (hS.map (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm)
    (hT.map (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm)
    ((gap2_toEuclideanCLM_symm_spectrum S).trans_subset hσS)
    ((gap2_toEuclideanCLM_symm_spectrum T).trans_subset hσT)
  rwa [← map_add, ← gap2_toEuclideanCLM_symm_real_smul, gap2_toEuclideanCLM_matrixCfcR_symm,
    gap2_toEuclideanCLM_matrixCfcR_symm, gap2_toEuclideanCLM_matrixCfcR_symm] at h

/-- Pull the midpoint inequality back along a continuous star-algebra equivalence of operator
algebras. -/
private theorem gap2_midpoint_le_of_starAlgEquiv
    {K E : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [ContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint]
    {J : Set ℝ} {f : ℝ → ℝ} (hfJ : ContinuousOn f J)
    (φ : (K →L[ℂ] K) ≃⋆ₐ[ℂ] (E →L[ℂ] E)) (hφcont : Continuous φ)
    {S T : K →L[ℂ] K} (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (hσS : spectrum ℝ S ⊆ J) (hσT : spectrum ℝ T ⊆ J)
    (hM : IsSelfAdjoint ((1 / 2 : ℝ) • (S + T))) (hσM : spectrum ℝ ((1 / 2 : ℝ) • (S + T)) ⊆ J)
    (hE : cfc (R := ℝ) f ((1 / 2 : ℝ) • (φ S + φ T)) ≤
      (1 / 2 : ℝ) • (cfc (R := ℝ) f (φ S) + cfc (R := ℝ) f (φ T))) :
    cfc (R := ℝ) f ((1 / 2 : ℝ) • (S + T)) ≤
      (1 / 2 : ℝ) • (cfc (R := ℝ) f S + cfc (R := ℝ) f T) := by
  rw [← gap2_starAlgEquiv_map_midpoint φ hφcont S T,
    ← gap2_starAlgEquiv_cfcR_transport φ hfJ hσM hM,
    ← gap2_starAlgEquiv_cfcR_transport φ hfJ hσS hS,
    ← gap2_starAlgEquiv_cfcR_transport φ hfJ hσT hT,
    ← gap2_starAlgEquiv_map_midpoint φ hφcont] at hE
  exact (map_le_map_iff φ).1 hE

private theorem gap2_matrix_midpoint_finite_dimensional
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [FiniteDimensional ℂ K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)]
    {J : Set ℝ} {f : ℝ → ℝ} (hJ : Convex ℝ J) (hfJ : ContinuousOn f J)
    (hmat : HansenPedersen.MatrixOperatorMidpointConvexOnInterval J f)
    {S T : K →L[ℂ] K} (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (hσS : spectrum ℝ S ⊆ J) (hσT : spectrum ℝ T ⊆ J) :
    cfc (R := ℝ) f ((1 / 2 : ℝ) • (S + T)) ≤
      (1 / 2 : ℝ) • (cfc (R := ℝ) f S + cfc (R := ℝ) f T) := by
  let E := EuclideanSpace ℂ (Fin (Module.finrank ℂ K))
  let e : K ≃ₗᵢ[ℂ] E := (stdOrthonormalBasis ℂ K).repr
  let φop : (K →L[ℂ] K) ≃⋆ₐ[ℂ] (E →L[ℂ] E) := e.conjStarAlgEquiv
  letI : IsScalarTower ℝ ℂ (K →L[ℂ] K) := RestrictScalars.isScalarTower ℝ ℂ (K →L[ℂ] K)
  letI : IsScalarTower ℝ ℂ (E →L[ℂ] E) := RestrictScalars.isScalarTower ℝ ℂ (E →L[ℂ] E)
  obtain ⟨hM, hσM⟩ := gap2_midpoint_isSelfAdjoint_spectrum_subset hJ hS hT hσS hσT
  have hσφS : spectrum ℝ (φop S) ⊆ J := by
    rw [gap2_starAlgEquiv_real_spectrum_eq φop S]
    exact hσS
  have hσφT : spectrum ℝ (φop T) ⊆ J := by
    rw [gap2_starAlgEquiv_real_spectrum_eq φop T]
    exact hσT
  exact gap2_midpoint_le_of_starAlgEquiv hfJ φop (StarAlgEquiv.isometry φop).continuous
    hS hT hσS hσT hM hσM
    (gap2_euclidean_midpoint_of_matrix hmat (hS.map φop) (hT.map φop) hσφS hσφT)

private theorem finiteDimensional_midpointConvex_Ioi_of_matrix
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [FiniteDimensional ℂ K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)]
    {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi 0))
    (hmat : HansenPedersen.MatrixOperatorMidpointConvexOnInterval
      (Set.Ioi 0) f) :
    HansenPedersen.HOperatorMidpointConvexOnInterval K (Set.Ioi 0) f := by
  intro S T hS hT hσS hσT
  exact gap2_matrix_midpoint_finite_dimensional (convex_Ioi 0) hf hmat
    hS hT hσS hσT

open CFC Filter
open scoped CStarAlgebra Topology

private noncomputable instance gap2WithLpProdNormedAddCommGroup
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] :
    NormedAddCommGroup (WithLp 2 (E × F)) :=
  WithLp.instProdNormedAddCommGroup (p := 2) (α := E) (β := F)

private noncomputable instance gap2WithLpProdNormedSpace
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] :
    NormedSpace ℂ (WithLp 2 (E × F)) :=
  WithLp.instProdNormedSpace (p := 2) (𝕜 := ℂ) (α := E) (β := F)

private noncomputable instance gap2WithLpProdInnerProductSpace
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    InnerProductSpace ℂ (WithLp 2 (E × F)) :=
  WithLp.instProdInnerProductSpace

private noncomputable instance gap2WithLpProdCompleteSpace
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] :
    CompleteSpace (WithLp 2 (E × F)) :=
  WithLp.instProdCompleteSpace (p := 2) (α := E) (β := F)

private noncomputable instance gap2ULiftInnerProductSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    InnerProductSpace ℂ (ULift E) where
  inner x y := inner ℂ x.down y.down
  norm_sq_eq_re_inner x := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x.down
  conj_inner_symm x y := InnerProductSpace.conj_inner_symm x.down y.down
  add_left x y z := InnerProductSpace.add_left x.down y.down z.down
  smul_left x y r := InnerProductSpace.smul_left x.down y.down r

private instance gap2WithLpProdContinuousAdd
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] :
    ContinuousAdd (WithLp 2 (E × F)) where
  continuous_add := by
    let e : WithLp 2 (E × F) ≃L[ℂ] E × F :=
      WithLp.prodContinuousLinearEquiv 2 ℂ E F
    have hcont : Continuous fun p : WithLp 2 (E × F) × WithLp 2 (E × F) =>
        e.symm (e p.1 + e p.2) := by
      exact e.symm.continuous.comp
        ((e.continuous.comp continuous_fst).add
          (e.continuous.comp continuous_snd))
    simpa using hcont

private noncomputable instance gap2WithLpSubmodulePairCompleteSpace
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {U : Submodule ℂ K} [CompleteSpace U] [CompleteSpace Uᗮ] :
    CompleteSpace (WithLp 2 (↥U × ↥Uᗮ)) := by
  simpa using
    (WithLp.instProdCompleteSpace (p := 2) (α := U) (β := Uᗮ))

private noncomputable instance gap2StarSubmoduleEnd
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {U : Submodule ℂ K} [CompleteSpace U] : Star (U →L[ℂ] U) :=
  @ContinuousLinearMap.instStarId ℂ U _ _ _ ‹CompleteSpace U›

private noncomputable instance gap2CStarAlgebraSubmoduleEnd
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {U : Submodule ℂ K} [CompleteSpace U] : CStarAlgebra (U →L[ℂ] U) :=
  @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace U _ _
    ‹CompleteSpace U›

@[reducible] private noncomputable def gap2CfcComplexEnd
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] :
    ContinuousFunctionalCalculus ℂ (E →L[ℂ] E) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

@[reducible] private noncomputable def gap2CfcRealEnd
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] :
    ContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

private noncomputable instance gap2StarRingSubmoduleEnd
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {U : Submodule ℂ K} [CompleteSpace U] : StarRing (U →L[ℂ] U) :=
  @CStarAlgebra.toStarRing _ (gap2CStarAlgebraSubmoduleEnd (U := U))

private noncomputable instance gap2WithLpSubmodulePairNormedSpace
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {U : Submodule ℂ K} : NormedSpace ℂ (WithLp 2 (↥U × ↥Uᗮ)) :=
  WithLp.instProdNormedSpace (p := 2) (𝕜 := ℂ) (α := ↥U) (β := ↥Uᗮ)

private noncomputable instance gap2WithLpSubmodulePairInnerProductSpace
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {U : Submodule ℂ K} : InnerProductSpace ℂ (WithLp 2 (↥U × ↥Uᗮ)) :=
  WithLp.instProdInnerProductSpace

private noncomputable instance gap2WithLpSubmodulePairIsBoundedSMul
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {U : Submodule ℂ K} : IsBoundedSMul ℂ (WithLp 2 (↥U × ↥Uᗮ)) :=
  IsBoundedSMul.of_norm_smul_le NormedSpace.norm_smul_le

private instance gap2WithLpSubmodulePairContinuousConstSMul
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {U : Submodule ℂ K} : ContinuousConstSMul ℂ (WithLp 2 (↥U × ↥Uᗮ)) where
  continuous_const_smul c := (lipschitzWith_smul c).continuous

private instance gap2ContinuousAddWithLpSubmodulePair
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {U : Submodule ℂ K} :
    ContinuousAdd (WithLp 2 (↥U × ↥Uᗮ)) where
  continuous_add := by
    let e : WithLp 2 (↥U × ↥Uᗮ) ≃L[ℂ] ↥U × ↥Uᗮ :=
      WithLp.prodContinuousLinearEquiv 2 ℂ ↥U ↥Uᗮ
    have hcont :
        Continuous fun p : WithLp 2 (↥U × ↥Uᗮ) × WithLp 2 (↥U × ↥Uᗮ) =>
          e.symm (e p.1 + e p.2) := by
      exact e.symm.continuous.comp
        ((e.continuous.comp continuous_fst).add
          (e.continuous.comp continuous_snd))
    simpa using hcont

private instance gap2ContinuousNegWithLpSubmodulePair
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {U : Submodule ℂ K} : ContinuousNeg (WithLp 2 (↥U × ↥Uᗮ)) where
  continuous_neg := by
    let e : WithLp 2 (↥U × ↥Uᗮ) ≃L[ℂ] ↥U × ↥Uᗮ :=
      WithLp.prodContinuousLinearEquiv 2 ℂ ↥U ↥Uᗮ
    simpa using e.symm.continuous.comp e.continuous.neg

private instance gap2IsTopologicalAddGroupWithLpSubmodulePair
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {U : Submodule ℂ K} : IsTopologicalAddGroup (WithLp 2 (↥U × ↥Uᗮ)) := by
  constructor

private noncomputable instance gap2StarWithLpSubmodulePairEnd
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {U : Submodule ℂ K} [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))] :
    Star ((WithLp 2 (↥U × ↥Uᗮ)) →L[ℂ] (WithLp 2 (↥U × ↥Uᗮ))) :=
  @ContinuousLinearMap.instStarId ℂ (WithLp 2 (↥U × ↥Uᗮ)) _ _ _
    ‹CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))›

private noncomputable instance gap2CStarAlgebraWithLpSubmodulePairEnd
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {U : Submodule ℂ K} [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))] :
    CStarAlgebra
      ((WithLp 2 (↥U × ↥Uᗮ)) →L[ℂ] (WithLp 2 (↥U × ↥Uᗮ))) :=
  @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace
    (WithLp 2 (↥U × ↥Uᗮ)) _ _
      ‹CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))›

private noncomputable def gap2FiniteSpan
    {K ι : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (b : HilbertBasis ι ℂ K) (s : Finset ι) : Submodule ℂ K :=
  Submodule.span ℂ (b '' (s : Set ι))

private lemma gap2FiniteSpan_mono
    {K ι : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (b : HilbertBasis ι ℂ K) : Monotone (gap2FiniteSpan b) := by
  intro s t hst
  exact Submodule.span_mono (by
    intro x hx
    rcases hx with ⟨i, hi, rfl⟩
    exact ⟨i, Set.mem_of_mem_of_subset hi (show (s : Set ι) ⊆ t from hst), rfl⟩)

private noncomputable instance gap2FiniteSpan_finiteDimensional
    {K ι : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (b : HilbertBasis ι ℂ K) (s : Finset ι) :
    FiniteDimensional ℂ (gap2FiniteSpan b s) := by
  classical
  refine FiniteDimensional.span_of_finite ℂ ?_
  exact s.finite_toSet.image b

private lemma gap2FiniteSpan_top_le_closure_iSup
    {K ι : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (b : HilbertBasis ι ℂ K) :
    (⊤ : Submodule ℂ K) ≤ (⨆ s : Finset ι, gap2FiniteSpan b s).topologicalClosure := by
  classical
  simpa [gap2FiniteSpan] using (HilbertBasis.finite_spans_dense (b := b)).ge

private theorem gap2FiniteSpan_starProjection_tendsto_self
    {K ι : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (b : HilbertBasis ι ℂ K) (x : K) :
    Tendsto (fun s : Finset ι => (gap2FiniteSpan b s).starProjection x)
      atTop (𝓝 x) :=
  Submodule.starProjection_tendsto_self (U := fun s : Finset ι => gap2FiniteSpan b s)
    (gap2FiniteSpan_mono b) x (gap2FiniteSpan_top_le_closure_iSup b)

private theorem gap2FiniteSpan_starProjection_norm_le
    {K ι : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (b : HilbertBasis ι ℂ K) :
    ∀ s : Finset ι, ‖(gap2FiniteSpan b s).starProjection‖ ≤ 1 := by
  intro s
  simpa using Submodule.starProjection_norm_le (gap2FiniteSpan b s)

private lemma gap2_sot_mul_of_uniformBound
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {ι : Type*} {l : Filter ι}
    {Aγ Bγ : ι → HansenPedersen.L K} {A B : HansenPedersen.L K}
    (hA : ∀ x, Tendsto (fun i => Aγ i x) l (𝓝 (A x)))
    (hB : ∀ x, Tendsto (fun i => Bγ i x) l (𝓝 (B x)))
    (hbound : ∃ M > 0, ∀ i, ‖Aγ i‖ ≤ M) :
    ∀ x, Tendsto (fun i => (Aγ i * Bγ i) x) l (𝓝 ((A * B) x)) := by
  rcases hbound with ⟨M, hMpos, hM⟩
  intro x
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hBx : Tendsto (fun i => Bγ i x - B x) l (𝓝 (0 : K)) := by
    simpa using (hB x).sub
      (tendsto_const_nhds : Tendsto (fun _ : ι => B x) l (𝓝 (B x)))
  have hterm1 : Tendsto (fun i => Aγ i (Bγ i x - B x)) l (𝓝 (0 : K)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbound' : ∀ i, ‖Aγ i (Bγ i x - B x)‖ ≤ M * ‖Bγ i x - B x‖ := by
      intro i
      calc
        ‖Aγ i (Bγ i x - B x)‖ ≤ ‖Aγ i‖ * ‖Bγ i x - B x‖ :=
          (Aγ i).le_opNorm _
        _ ≤ M * ‖Bγ i x - B x‖ := by
          gcongr
          exact hM i
    apply squeeze_zero (fun _ => norm_nonneg _) hbound'
    simpa using (tendsto_norm.comp hBx).const_mul M
  have hterm2 : Tendsto (fun i => (Aγ i - A) (B x)) l (𝓝 (0 : K)) := by
    simpa using (hA (B x)).sub
      (tendsto_const_nhds : Tendsto (fun _ : ι => A (B x)) l (𝓝 (A (B x))))
  have hsum := hterm1.add hterm2
  have hEq :
      (fun i => (Aγ i * Bγ i) x - (A * B) x) =
        fun i => Aγ i (Bγ i x - B x) + (Aγ i - A) (B x) := by
    funext i
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  simpa [hEq] using (tendsto_norm.comp hsum)

private theorem gap2_blockExtension_tendsto_self
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {ι : Type*} [Preorder ι] [NeBot (atTop : Filter ι)]
    {P : ι → HansenPedersen.L K} {A : HansenPedersen.L K} {t₀ : ℝ}
    (hP : ∀ x, Tendsto (fun i => P i x) atTop (𝓝 x))
    (hPbound : ∀ i, ‖P i‖ ≤ 1) :
    ∀ x, Tendsto
      (fun i => (P i * A * P i + (t₀ : ℂ) • (1 - P i)) x)
      atTop (𝓝 (A x)) := by
  have hconstA : ∀ x, Tendsto (fun _ : ι => A x) atTop (𝓝 (A x)) :=
    fun x => tendsto_const_nhds
  have hPA : ∀ x, Tendsto (fun i => (P i * A) x) atTop (𝓝 (A x)) := by
    simpa using
      (gap2_sot_mul_of_uniformBound
        (Aγ := P) (Bγ := fun _ : ι => A) (A := (1 : HansenPedersen.L K)) (B := A)
        hP hconstA ⟨1, zero_lt_one, hPbound⟩)
  have hPAbound : ∃ M > 0, ∀ i, ‖P i * A‖ ≤ M := by
    refine ⟨‖A‖ + 1, by positivity, ?_⟩
    intro i
    calc
      ‖P i * A‖ ≤ ‖P i‖ * ‖A‖ := norm_mul_le _ _
      _ ≤ 1 * ‖A‖ := mul_le_mul_of_nonneg_right (hPbound i) (norm_nonneg A)
      _ ≤ ‖A‖ + 1 := by linarith
  have hPAP : ∀ x, Tendsto (fun i => (P i * A * P i) x) atTop (𝓝 (A x)) := by
    simpa [mul_assoc] using
      (gap2_sot_mul_of_uniformBound
        (Aγ := fun i => P i * A) (Bγ := P) (A := A) (B := (1 : HansenPedersen.L K))
        hPA hP hPAbound)
  intro x
  have hcomp : Tendsto (fun i => ((t₀ : ℂ) • (1 - P i)) x) atTop (𝓝 (0 : K)) := by
    have hsub : Tendsto (fun i => (1 - P i) x) atTop (𝓝 (0 : K)) := by
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ι => x) atTop (𝓝 x)).sub (hP x)
    simpa using hsub.const_smul (t₀ : ℂ)
  simpa using (hPAP x).add hcomp

private noncomputable def gap2DiagMap
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (a : E →L[ℂ] E) (b : F →L[ℂ] F) :
    WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm :
      E × F →L[ℂ] WithLp 2 (E × F)).comp <|
    (a.prodMap b).comp
      ((WithLp.prodContinuousLinearEquiv 2 ℂ E F) :
        WithLp 2 (E × F) →L[ℂ] E × F)

private lemma gap2DiagMap_apply
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (a : E →L[ℂ] E) (b : F →L[ℂ] F) (x : WithLp 2 (E × F)) :
    gap2DiagMap a b x = WithLp.toLp 2 (a x.fst, b x.snd) := rfl

private lemma gap2DiagMap_star
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (a : E →L[ℂ] E) (b : F →L[ℂ] F) :
    star (gap2DiagMap a b) = gap2DiagMap (star a) (star b) := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  change inner ℂ (WithLp.toLp 2 ((star a) x.fst, (star b) x.snd)) y =
      inner ℂ x (WithLp.toLp 2 (a y.fst, b y.snd))
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  have h1 := ContinuousLinearMap.adjoint_inner_left a y.fst x.fst
  have h2 := ContinuousLinearMap.adjoint_inner_left b y.snd x.snd
  simpa [ContinuousLinearMap.star_eq_adjoint] using congrArg₂ HAdd.hAdd h1 h2

private noncomputable def gap2DiagStarAlgHom
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] :
    ((E →L[ℂ] E) × (F →L[ℂ] F)) →⋆ₐ[ℂ]
      (WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F)) where
  toFun ab := gap2DiagMap ab.1 ab.2
  map_one' := by ext x; rfl
  map_mul' p q := by
    ext x
    apply WithLp.ofLp_injective
    simp [gap2DiagMap_apply, WithLp.ofLp_toLp]
  map_zero' := by ext x; rfl
  map_add' p q := by ext x; rfl
  commutes' r := by ext x; rfl
  map_star' ab := by
    symm
    simpa using gap2DiagMap_star ab.1 ab.2

private theorem gap2DiagStarAlgHom_continuous
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] :
    Continuous (gap2DiagStarAlgHom :
      ((E →L[ℂ] E) × (F →L[ℂ] F)) →
        (WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F))) := by
  let e : WithLp 2 (E × F) ≃L[ℂ] E × F := WithLp.prodContinuousLinearEquiv 2 ℂ E F
  let pre :
      ((E × F) →L[ℂ] (E × F)) →L[ℂ]
        (WithLp 2 (E × F) →L[ℂ] (E × F)) :=
    ((ContinuousLinearMap.compL ℂ (WithLp 2 (E × F)) (E × F) (E × F)).flip
      (e : WithLp 2 (E × F) →L[ℂ] E × F))
  let post :
      (WithLp 2 (E × F) →L[ℂ] (E × F)) →L[ℂ]
        (WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F)) :=
    ContinuousLinearMap.compL ℂ (WithLp 2 (E × F)) (E × F) (WithLp 2 (E × F))
      (e.symm : E × F →L[ℂ] WithLp 2 (E × F))
  have hprod : Continuous fun p : (E →L[ℂ] E) × (F →L[ℂ] F) =>
      p.1.prodMap p.2 := by
    simpa using (ContinuousLinearMap.prodMapL ℂ E E F F).continuous.comp
      (continuous_fst.prodMk continuous_snd)
  simpa [gap2DiagStarAlgHom, gap2DiagMap, e, pre, post] using
    post.continuous.comp (pre.continuous.comp hprod)

private noncomputable def gap2BlockStarAlgHom
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [instCK : CompleteSpace K]
    (U : Submodule ℂ K) [U.HasOrthogonalProjection]
    [instCU : CompleteSpace U] [instCUp : CompleteSpace Uᗮ]
    [instCUcoe : CompleteSpace ↥U] [instCUpcoe : CompleteSpace ↥Uᗮ]
    [instCW : CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))] :
    ((U →L[ℂ] U) × (Uᗮ →L[ℂ] Uᗮ)) →⋆ₐ[ℂ] (K →L[ℂ] K) := by
  let e :
      (WithLp 2 (↥U × ↥Uᗮ) →L[ℂ] WithLp 2 (↥U × ↥Uᗮ)) ≃⋆ₐ[ℂ]
        (K →L[ℂ] K) :=
    @LinearIsometryEquiv.conjStarAlgEquiv ℂ _ (WithLp 2 (↥U × ↥Uᗮ)) _ _ instCW
      K _ _ instCK U.orthogonalDecomposition.symm
  exact (StarAlgHomClass.toStarAlgHom e).comp
    (@gap2DiagStarAlgHom U Uᗮ _ _ instCU _ _ instCUp)

private theorem gap2BlockStarAlgHom_continuous
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [instCK : CompleteSpace K]
    (U : Submodule ℂ K) [U.HasOrthogonalProjection]
    [instCU : CompleteSpace U] [instCUp : CompleteSpace Uᗮ]
    [instCUcoe : CompleteSpace ↥U] [instCUpcoe : CompleteSpace ↥Uᗮ]
    [instCW : CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))] :
    Continuous (gap2BlockStarAlgHom U :
      ((U →L[ℂ] U) × (Uᗮ →L[ℂ] Uᗮ)) → (K →L[ℂ] K)) := by
  let e :
      (WithLp 2 (↥U × ↥Uᗮ) →L[ℂ] WithLp 2 (↥U × ↥Uᗮ)) ≃⋆ₐ[ℂ]
        (K →L[ℂ] K) :=
    @LinearIsometryEquiv.conjStarAlgEquiv ℂ _ (WithLp 2 (↥U × ↥Uᗮ)) _ _ instCW
      K _ _ instCK U.orthogonalDecomposition.symm
  have he : Continuous e := by
    let e' : WithLp 2 (↥U × ↥Uᗮ) ≃L[ℂ] K :=
      U.orthogonalDecomposition.symm.toContinuousLinearEquiv
    let pre :
        ((WithLp 2 (↥U × ↥Uᗮ) →L[ℂ] WithLp 2 (↥U × ↥Uᗮ)) →L[ℂ]
          (K →L[ℂ] WithLp 2 (↥U × ↥Uᗮ))) :=
      ((ContinuousLinearMap.compL ℂ K (WithLp 2 (↥U × ↥Uᗮ))
        (WithLp 2 (↥U × ↥Uᗮ))).flip
          (e'.symm : K →L[ℂ] WithLp 2 (↥U × ↥Uᗮ)))
    let post :
        ((K →L[ℂ] WithLp 2 (↥U × ↥Uᗮ)) →L[ℂ] (K →L[ℂ] K)) :=
      ContinuousLinearMap.compL ℂ K (WithLp 2 (↥U × ↥Uᗮ)) K
        (e' : WithLp 2 (↥U × ↥Uᗮ) →L[ℂ] K)
    simpa [e, e', pre, post, LinearIsometryEquiv.conjStarAlgEquiv_apply,
      ContinuousLinearEquiv.conjContinuousAlgEquiv_apply,
      ContinuousLinearMap.comp_assoc] using post.continuous.comp pre.continuous
  exact he.comp
    (@gap2DiagStarAlgHom_continuous U Uᗮ _ _ instCU _ _ instCUp)

private theorem gap2BlockStarAlgHom_apply
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : Submodule ℂ K) [U.HasOrthogonalProjection]
    [CompleteSpace U] [CompleteSpace Uᗮ]
    [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))]
    (a : U →L[ℂ] U) (b : Uᗮ →L[ℂ] Uᗮ) (x : K) :
    gap2BlockStarAlgHom U (a, b) x =
      U.subtypeL (a (U.orthogonalProjection x)) +
        Uᗮ.subtypeL (b (Uᗮ.orthogonalProjection x)) := by
  change U.orthogonalDecomposition.symm
      (gap2DiagMap a b (U.orthogonalDecomposition x)) = _
  rw [Submodule.orthogonalDecomposition_apply]
  rfl

private theorem gap2BlockStarAlgHom_compression_scalar
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : Submodule ℂ K) [U.HasOrthogonalProjection]
    [CompleteSpace U] [CompleteSpace Uᗮ]
    [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))]
    (A : K →L[ℂ] K) (t₀ : ℝ) :
    gap2BlockStarAlgHom U
        (U.orthogonalProjection ∘L A ∘L U.subtypeL,
          (t₀ : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ)) =
      U.starProjection * A * U.starProjection +
        (t₀ : ℂ) • (1 - U.starProjection) := by
  have hcomp : (1 - U.starProjection : K →L[ℂ] K) = Uᗮ.starProjection := by
    simpa using (Submodule.starProjection_orthogonal U).symm
  rw [hcomp]
  ext x
  rw [gap2BlockStarAlgHom_apply]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply,
    Submodule.starProjection_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply]
  rw [map_smul]
  rfl

@[reducible] private noncomputable def gap2CfcComplexProd
    {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] :
    ContinuousFunctionalCalculus ℂ (A × B) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

@[reducible] private noncomputable def gap2CfcRealProd
    {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [ContinuousFunctionalCalculus ℝ B IsSelfAdjoint] :
    ContinuousFunctionalCalculus ℝ (A × B) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

attribute [local instance] gap2CfcComplexProd gap2CfcRealProd

/-- Real continuous functional calculus commutes with a continuous star-algebra homomorphism
out of a product of C⋆-algebras. -/
private theorem gap2_cfc_map_prod_starAlgHom
    {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
    (φ : (A × B) →⋆ₐ[ℂ] C) (hφ : Continuous φ) {f : ℝ → ℝ} {a : A} {b : B}
    (hf : ContinuousOn f (spectrum ℝ a ∪ spectrum ℝ b))
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    cfc (R := ℝ) f (φ (a, b)) = φ (cfc (R := ℝ) f a, cfc (R := ℝ) f b) := by
  letI : IsScalarTower ℝ ℂ A := RestrictScalars.isScalarTower ℝ ℂ A
  letI : IsScalarTower ℝ ℂ B := RestrictScalars.isScalarTower ℝ ℂ B
  letI : IsScalarTower ℝ ℂ C := RestrictScalars.isScalarTower ℝ ℂ C
  letI : IsScalarTower ℝ ℂ (A × B) := Prod.isScalarTower
  let Φ : (A × B) →⋆ₐ[ℝ] C := φ.restrictScalars ℝ
  have hab : IsSelfAdjoint (a, b) := Prod.ext ha hb
  have hmap := StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ) Φ f (a, b)
    (hf := by rwa [Prod.spectrum_eq]) (hφ := (show Continuous Φ from hφ)) (ha := hab)
    (hφa := hab.map Φ)
  have hprod : cfc (R := ℝ) f (a, b) = (cfc (R := ℝ) f a, cfc (R := ℝ) f b) :=
    cfc_map_prod (R := ℝ) (S := ℝ) (A := A) (B := B) f a b (hf := hf) (hab := hab)
      (ha := ha) (hb := hb)
  rw [hprod] at hmap
  simpa [Φ] using hmap.symm

private theorem gap2BlockStarAlgHom_cfcR
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    (U : Submodule ℂ K) [U.HasOrthogonalProjection]
    [CompleteSpace U] [CompleteSpace Uᗮ]
    [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))]
    [ContinuousFunctionalCalculus ℝ (U →L[ℂ] U) IsSelfAdjoint]
    [ContinuousFunctionalCalculus ℝ (Uᗮ →L[ℂ] Uᗮ) IsSelfAdjoint]
    {f : ℝ → ℝ} {a : U →L[ℂ] U} {b : Uᗮ →L[ℂ] Uᗮ}
    (hf : ContinuousOn f (spectrum ℝ a ∪ spectrum ℝ b))
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    cfc (R := ℝ) f (gap2BlockStarAlgHom U (a, b)) =
      gap2BlockStarAlgHom U (cfc (R := ℝ) f a, cfc (R := ℝ) f b) :=
  gap2_cfc_map_prod_starAlgHom (gap2BlockStarAlgHom U) (gap2BlockStarAlgHom_continuous U) hf ha hb

private theorem gap2Compression_isSelfAdjoint
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : Submodule ℂ K) [U.HasOrthogonalProjection]
    [instCU : CompleteSpace U]
    {T : K →L[ℂ] K} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (U.orthogonalProjection ∘L T ∘L U.subtypeL) := by
  have hsym :
      ((U.orthogonalProjection ∘L T ∘L U.subtypeL : U →L[ℂ] U) :
        U →ₗ[ℂ] U).IsSymmetric := by
    intro x y
    simpa [Submodule.subtypeL_apply] using hT.isSymmetric (x : K) (y : K)
  exact @LinearMap.IsSymmetric.isSelfAdjoint ℂ U _ _ _ instCU _ hsym

private theorem gap2Compression_sub_isPositive
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : Submodule ℂ K) [U.HasOrthogonalProjection] [CompleteSpace U]
    {S T : K →L[ℂ] K} (hST : (T - S).IsPositive) :
    ((U.orthogonalProjection ∘L T ∘L U.subtypeL) -
      (U.orthogonalProjection ∘L S ∘L U.subtypeL)).IsPositive := by
  have hpos := hST.orthogonalProjection_comp U
  simpa [ContinuousLinearMap.comp_sub] using hpos

private theorem gap2Compression_scalar
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : Submodule ℂ K) [U.HasOrthogonalProjection]
    [CompleteSpace U] (r : ℝ) :
    U.orthogonalProjection ∘L
        (((r : ℂ) • (1 : K →L[ℂ] K)) ∘L U.subtypeL) =
      (r : ℂ) • (1 : U →L[ℂ] U) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply]
  rw [map_smul]
  change (r : ℂ) • (↑(U.orthogonalProjection (x : K)) : K) =
    (r : ℂ) • (x : K)
  rw [U.orthogonalProjection_mem_subspace_eq_self]

private theorem gap2Compression_spectrum_subset_Icc
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    (U : Submodule ℂ K) [U.HasOrthogonalProjection]
    [instCU : CompleteSpace U]
    [ContinuousFunctionalCalculus ℝ (U →L[ℂ] U) IsSelfAdjoint]
    [Nontrivial (U →L[ℂ] U)] {T : K →L[ℂ] K} {α β : ℝ}
    (hT : IsSelfAdjoint T)
    (hbounds : (α : ℂ) • (1 : K →L[ℂ] K) ≤ T ∧
      T ≤ (β : ℂ) • (1 : K →L[ℂ] K)) :
    spectrum ℝ (U.orthogonalProjection ∘L T ∘L U.subtypeL) ⊆ Set.Icc α β := by
  letI : PartialOrder (U →L[ℂ] U) := ContinuousLinearMap.instLoewnerPartialOrder
  have hself := gap2Compression_isSelfAdjoint U hT
  refine @gap2_spectrum_subset_Icc_of_order_bounds U _ _ instCU
    (show ContinuousFunctionalCalculus ℝ (U →L[ℂ] U) IsSelfAdjoint from inferInstance)
    (show Nontrivial (U →L[ℂ] U) from inferInstance) _ _ _ hself ?_ ?_
  · rw [ContinuousLinearMap.le_def]
    have hpos := gap2Compression_sub_isPositive U
      ((ContinuousLinearMap.le_def _ _).mp hbounds.1)
    rw [gap2Compression_scalar U α] at hpos
    exact hpos
  · rw [ContinuousLinearMap.le_def]
    have hpos := gap2Compression_sub_isPositive U
      ((ContinuousLinearMap.le_def _ _).mp hbounds.2)
    rw [gap2Compression_scalar U β] at hpos
    exact hpos

private theorem gap2Scalar_isSelfAdjoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (r : ℝ) : IsSelfAdjoint ((r : ℂ) • (1 : E →L[ℂ] E)) := by
  simp [isSelfAdjoint_iff]

private theorem gap2Scalar_spectrum_subset_Icc
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [ContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint]
    {α β r : ℝ} (hr : r ∈ Set.Icc α β) :
    spectrum ℝ ((r : ℂ) • (1 : E →L[ℂ] E)) ⊆ Set.Icc α β := by
  intro x hx
  have hxalg : x ∈ spectrum ℝ (algebraMap ℝ (E →L[ℂ] E) r) := by
    simpa [Algebra.algebraMap_eq_smul_one] using hx
  have hxsingle : x ∈ ({r} : Set ℝ) :=
    CFC.spectrum_algebraMap_subset (R := ℝ) (A := E →L[ℂ] E) r hxalg
  rcases Set.mem_singleton_iff.mp hxsingle with rfl
  exact hr

@[reducible] private noncomputable def gap2PartialOrderSubmoduleEnd
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : Submodule ℂ K) : PartialOrder (U →L[ℂ] U) :=
  ContinuousLinearMap.instLoewnerPartialOrder

attribute [local instance] gap2PartialOrderSubmoduleEnd

private theorem gap2BlockStarAlgHom_scalar_pair
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : Submodule ℂ K) [U.HasOrthogonalProjection]
    [instCUcoe : CompleteSpace ↥U] [instCUpcoe : CompleteSpace ↥Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))] (r : ℝ) :
    gap2BlockStarAlgHom U
        ((r : ℂ) • (1 : U →L[ℂ] U),
          (r : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ)) =
      (r : ℂ) • (1 : K →L[ℂ] K) := by
  ext x
  rw [gap2BlockStarAlgHom_apply]
  change (r : ℂ) • U.starProjection x + (r : ℂ) • Uᗮ.starProjection x =
    (r : ℂ) • x
  rw [← smul_add, U.starProjection_add_starProjection_orthogonal]

private theorem gap2BlockExtension_isSelfAdjoint
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : Submodule ℂ K) [U.HasOrthogonalProjection]
    [instCU : CompleteSpace U] [instCUp : CompleteSpace Uᗮ]
    [instCUcoe : CompleteSpace ↥U] [instCUpcoe : CompleteSpace ↥Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))]
    {T : K →L[ℂ] K} (hT : IsSelfAdjoint T) (t₀ : ℝ) :
    IsSelfAdjoint
      (U.starProjection * T * U.starProjection +
        (t₀ : ℂ) • (1 - U.starProjection)) := by
  let c : Uᗮ →L[ℂ] Uᗮ := (t₀ : ℂ) • 1
  have hcomp := @gap2Compression_isSelfAdjoint K _ _ _ U _ instCU T hT
  have hc : IsSelfAdjoint c :=
    @gap2Scalar_isSelfAdjoint Uᗮ _ _ instCUp t₀
  have hpair : IsSelfAdjoint
      (U.orthogonalProjection ∘L T ∘L U.subtypeL, c) := by
    change (star _, star _) = (_, _)
    exact Prod.ext hcomp hc
  have hmap := hpair.map (gap2BlockStarAlgHom U)
  rw [gap2BlockStarAlgHom_compression_scalar] at hmap
  exact hmap

/-- A real scalar operator `t₀ • 1` with `t₀ ∈ [α, β]` lies between `α • 1` and `β • 1`. -/
private theorem gap2Scalar_order_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [ContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint]
    {α β t₀ : ℝ} (ht₀ : t₀ ∈ Set.Icc α β) :
    (α : ℂ) • (1 : E →L[ℂ] E) ≤ (t₀ : ℂ) • (1 : E →L[ℂ] E) ∧
      (t₀ : ℂ) • (1 : E →L[ℂ] E) ≤ (β : ℂ) • (1 : E →L[ℂ] E) :=
  gap2_order_bounds_of_spectrum_subset_Icc (gap2Scalar_isSelfAdjoint t₀)
    (gap2Scalar_spectrum_subset_Icc ht₀)

/-- `gap2BlockStarAlgHom U` is monotone (used before `gap2BlockStarAlgHom_mono`). -/
private theorem gap2BlockStarAlgHom_le_of_le
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : Submodule ℂ K) [U.HasOrthogonalProjection]
    [instCU : CompleteSpace U] [instCUp : CompleteSpace Uᗮ]
    [instCUcoe : CompleteSpace ↥U] [instCUpcoe : CompleteSpace ↥Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))]
    {p q : (U →L[ℂ] U) × (Uᗮ →L[ℂ] Uᗮ)} (hpq : p ≤ q) :
    gap2BlockStarAlgHom U p ≤ gap2BlockStarAlgHom U q := by
  letI : PartialOrder ((U →L[ℂ] U) × (Uᗮ →L[ℂ] Uᗮ)) := inferInstance
  letI : StarOrderedRing (U →L[ℂ] U) :=
    @ContinuousLinearMap.instStarOrderedRing U _ _ instCU
  letI : StarOrderedRing (Uᗮ →L[ℂ] Uᗮ) :=
    @ContinuousLinearMap.instStarOrderedRing Uᗮ _ _ instCUp
  letI : StarOrderedRing
      ((U →L[ℂ] U) × (Uᗮ →L[ℂ] Uᗮ)) := Prod.instStarOrderedRing
  let φ : ((U →L[ℂ] U) × (Uᗮ →L[ℂ] Uᗮ)) →⋆ₙ+* (K →L[ℂ] K) :=
    { toFun := gap2BlockStarAlgHom U
      map_zero' := map_zero (gap2BlockStarAlgHom U)
      map_add' := map_add (gap2BlockStarAlgHom U)
      map_mul' := map_mul (gap2BlockStarAlgHom U)
      map_star' := map_star (gap2BlockStarAlgHom U) }
  exact NonUnitalStarRingHom.map_le_map_of_map_star φ hpq

private theorem gap2BlockExtension_spectrum_subset_Icc
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)]
    (U : Submodule ℂ K) [U.HasOrthogonalProjection]
    [instCU : CompleteSpace U] [instCUp : CompleteSpace Uᗮ]
    [instCUcoe : CompleteSpace ↥U] [instCUpcoe : CompleteSpace ↥Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))]
    [ContinuousFunctionalCalculus ℝ (U →L[ℂ] U) IsSelfAdjoint]
    [ContinuousFunctionalCalculus ℝ (Uᗮ →L[ℂ] Uᗮ) IsSelfAdjoint]
    {T : K →L[ℂ] K} {α β t₀ : ℝ} (hT : IsSelfAdjoint T)
    (hTbounds : (α : ℂ) • (1 : K →L[ℂ] K) ≤ T ∧
      T ≤ (β : ℂ) • (1 : K →L[ℂ] K))
    (ht₀ : t₀ ∈ Set.Icc α β) :
    spectrum ℝ
        (U.starProjection * T * U.starProjection +
          (t₀ : ℂ) • (1 - U.starProjection)) ⊆ Set.Icc α β := by
  let comp : U →L[ℂ] U := U.orthogonalProjection ∘L T ∘L U.subtypeL
  let c : Uᗮ →L[ℂ] Uᗮ := (t₀ : ℂ) • 1
  have hcompBounds :
      (α : ℂ) • (1 : U →L[ℂ] U) ≤ comp ∧
        comp ≤ (β : ℂ) • (1 : U →L[ℂ] U) := by
    constructor
    · change (comp - (α : ℂ) • (1 : U →L[ℂ] U)).IsPositive
      have hpos := gap2Compression_sub_isPositive U
        ((ContinuousLinearMap.le_def _ _).mp hTbounds.1)
      rw [gap2Compression_scalar U α] at hpos
      exact hpos
    · change (((β : ℂ) • (1 : U →L[ℂ] U)) - comp).IsPositive
      have hpos := gap2Compression_sub_isPositive U
        ((ContinuousLinearMap.le_def _ _).mp hTbounds.2)
      rw [gap2Compression_scalar U β] at hpos
      exact hpos
  have hcBounds :
      (α : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ) ≤ c ∧
        c ≤ (β : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ) :=
    @gap2Scalar_order_bounds Uᗮ _ _ instCUp
      (show ContinuousFunctionalCalculus ℝ (Uᗮ →L[ℂ] Uᗮ) IsSelfAdjoint from inferInstance)
      α β t₀ ht₀
  have hlower := gap2BlockStarAlgHom_le_of_le (instCU := instCU) (instCUp := instCUp) U
    (p := ((α : ℂ) • (1 : U →L[ℂ] U), (α : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ))) (q := (comp, c))
    ((Prod.le_def).2 ⟨hcompBounds.1, hcBounds.1⟩)
  have hupper := gap2BlockStarAlgHom_le_of_le U
    (p := (comp, c)) (q := ((β : ℂ) • (1 : U →L[ℂ] U), (β : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ)))
    ((Prod.le_def).2 ⟨hcompBounds.2, hcBounds.2⟩)
  have hblockSelf := gap2BlockExtension_isSelfAdjoint U hT t₀
  apply gap2_spectrum_subset_Icc_of_order_bounds hblockSelf
  · change gap2BlockStarAlgHom U
        ((α : ℂ) • (1 : U →L[ℂ] U),
          (α : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ)) ≤
        gap2BlockStarAlgHom U (comp, c) at hlower
    rw [gap2BlockStarAlgHom_scalar_pair,
      gap2BlockStarAlgHom_compression_scalar] at hlower
    exact hlower
  · change gap2BlockStarAlgHom U (comp, c) ≤
        gap2BlockStarAlgHom U
          ((β : ℂ) • (1 : U →L[ℂ] U),
            (β : ℂ) • (1 : Uᗮ →L[ℂ] Uᗮ)) at hupper
    rw [gap2BlockStarAlgHom_scalar_pair,
      gap2BlockStarAlgHom_compression_scalar] at hupper
    exact hupper

private theorem gap2BlockStarAlgHom_mono
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : Submodule ℂ K) [U.HasOrthogonalProjection]
    [instCU : CompleteSpace U] [instCUp : CompleteSpace Uᗮ]
    [instCUcoe : CompleteSpace ↥U] [instCUpcoe : CompleteSpace ↥Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))]
    {p q : (U →L[ℂ] U) × (Uᗮ →L[ℂ] Uᗮ)} (hpq : p ≤ q) :
    gap2BlockStarAlgHom U p ≤ gap2BlockStarAlgHom U q := by
  letI : PartialOrder ((U →L[ℂ] U) × (Uᗮ →L[ℂ] Uᗮ)) := inferInstance
  letI : StarOrderedRing (U →L[ℂ] U) :=
    @ContinuousLinearMap.instStarOrderedRing U _ _ instCU
  letI : StarOrderedRing (Uᗮ →L[ℂ] Uᗮ) :=
    @ContinuousLinearMap.instStarOrderedRing Uᗮ _ _ instCUp
  letI : StarOrderedRing
      ((U →L[ℂ] U) × (Uᗮ →L[ℂ] Uᗮ)) := Prod.instStarOrderedRing
  let φ : ((U →L[ℂ] U) × (Uᗮ →L[ℂ] Uᗮ)) →⋆ₙ+* (K →L[ℂ] K) :=
    { toFun := gap2BlockStarAlgHom U
      map_zero' := map_zero (gap2BlockStarAlgHom U)
      map_add' := map_add (gap2BlockStarAlgHom U)
      map_mul' := map_mul (gap2BlockStarAlgHom U)
      map_star' := map_star (gap2BlockStarAlgHom U) }
  exact NonUnitalStarRingHom.map_le_map_of_map_star φ hpq

-- Real-smul block linearity normalization exceeds the default.
private theorem gap2BlockStarAlgHom_midpoint
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : Submodule ℂ K) [U.HasOrthogonalProjection]
    [CompleteSpace U] [CompleteSpace Uᗮ]
    [CompleteSpace ↥U] [CompleteSpace ↥Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))]
    (a b : U →L[ℂ] U) (c : Uᗮ →L[ℂ] Uᗮ) :
    gap2BlockStarAlgHom U ((1 / 2 : ℝ) • (a + b), c) =
      (1 / 2 : ℝ) •
        (gap2BlockStarAlgHom U (a, c) + gap2BlockStarAlgHom U (b, c)) := by
  have hU : (1 / 2 : ℝ) • (a + b) = ((1 / 2 : ℝ) : ℂ) • (a + b) := by
    ext x
    rfl
  have hK : (1 / 2 : ℝ) •
        (gap2BlockStarAlgHom U (a, c) + gap2BlockStarAlgHom U (b, c)) =
      ((1 / 2 : ℝ) : ℂ) •
        (gap2BlockStarAlgHom U (a, c) + gap2BlockStarAlgHom U (b, c)) := by
    ext x
    rfl
  rw [hU, hK]
  rw [← map_add, ← map_smul]
  congr 1
  apply Prod.ext
  · ext x
    simp [smul_add]
  · ext x
    simp only [Prod.smul_snd, Prod.snd_add]
    apply congrArg Subtype.val
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply]
    rw [smul_add]
    rw [← add_smul]
    norm_num

/-- Compression to `U` commutes with the midpoint. -/
private theorem gap2Compression_midpoint
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : Submodule ℂ K) [U.HasOrthogonalProjection] [CompleteSpace U] (A B : K →L[ℂ] K) :
    U.orthogonalProjection ∘L ((1 / 2 : ℝ) • (A + B)) ∘L U.subtypeL =
      (1 / 2 : ℝ) • (U.orthogonalProjection ∘L A ∘L U.subtypeL +
        U.orthogonalProjection ∘L B ∘L U.subtypeL) := by
  letI : IsBoundedSMul ℝ U :=
    IsBoundedSMul.of_norm_smul_le NormedSpace.norm_smul_le
  letI : ContinuousSMul ℝ U := IsBoundedSMul.continuousSMul
  ext x
  apply congrArg Subtype.val
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [show (((1 / 2 : ℝ) • (A + B)) (U.subtypeL x)) =
    (1 / 2 : ℝ) • ((A + B) (U.subtypeL x)) by rfl]
  rw [show (((1 / 2 : ℝ) •
      (U.orthogonalProjection.comp (A.comp U.subtypeL) +
        U.orthogonalProjection.comp (B.comp U.subtypeL))) x) =
    (1 / 2 : ℝ) •
      ((U.orthogonalProjection.comp (A.comp U.subtypeL) +
        U.orthogonalProjection.comp (B.comp U.subtypeL)) x) by rfl]
  rw [map_real_smul U.orthogonalProjection U.orthogonalProjection.continuous]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, map_add]

/-- The block midpoint inequality: a midpoint inequality in the first corner, with a common
second corner `c`, passes through a continuous star-algebra homomorphism out of a product. -/
private theorem gap2_cfc_midpoint_le_of_prod_starAlgHom
    {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
    [PartialOrder A] [instSA : StarOrderedRing A] [PartialOrder B] [instSB : StarOrderedRing B]
    [PartialOrder C] [StarOrderedRing C]
    (φ : (A × B) →⋆ₐ[ℂ] C) (hφ : Continuous φ)
    {f : ℝ → ℝ} {s : Set ℝ} (hfs : ContinuousOn f s)
    {a b : A} {c : B} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hc : IsSelfAdjoint c)
    (hm : IsSelfAdjoint ((1 / 2 : ℝ) • (a + b)))
    (hσa : spectrum ℝ a ⊆ s) (hσb : spectrum ℝ b ⊆ s)
    (hσm : spectrum ℝ ((1 / 2 : ℝ) • (a + b)) ⊆ s) (hσc : spectrum ℝ c ⊆ s)
    (hlocal : cfc (R := ℝ) f ((1 / 2 : ℝ) • (a + b)) ≤
      (1 / 2 : ℝ) • (cfc (R := ℝ) f a + cfc (R := ℝ) f b)) :
    cfc (R := ℝ) f (φ ((1 / 2 : ℝ) • (a + b), c)) ≤
      (1 / 2 : ℝ) • (cfc (R := ℝ) f (φ (a, c)) + cfc (R := ℝ) f (φ (b, c))) := by
  letI : StarOrderedRing (A × B) := Prod.instStarOrderedRing
  let ψ : (A × B) →⋆ₙ+* C :=
    { toFun := φ
      map_zero' := map_zero φ
      map_add' := map_add φ
      map_mul' := map_mul φ
      map_star' := map_star φ }
  have hmono := NonUnitalStarRingHom.map_le_map_of_map_star ψ
    (x := (cfc (R := ℝ) f ((1 / 2 : ℝ) • (a + b)), cfc (R := ℝ) f c))
    (y := ((1 / 2 : ℝ) • (cfc (R := ℝ) f a + cfc (R := ℝ) f b), cfc (R := ℝ) f c))
    ((Prod.le_def).2 ⟨hlocal, le_rfl⟩)
  have hpair : ((1 / 2 : ℝ) • (cfc (R := ℝ) f a + cfc (R := ℝ) f b), cfc (R := ℝ) f c) =
      (1 / 2 : ℝ) • ((cfc (R := ℝ) f a, cfc (R := ℝ) f c) +
        (cfc (R := ℝ) f b, cfc (R := ℝ) f c)) := by
    refine Prod.ext rfl ?_
    change cfc (R := ℝ) f c = (1 / 2 : ℝ) • (cfc (R := ℝ) f c + cfc (R := ℝ) f c)
    rw [← two_smul ℝ (cfc (R := ℝ) f c), smul_smul]
    norm_num
  change φ _ ≤ φ _ at hmono
  rw [hpair, map_real_smul φ hφ, map_add,
    ← gap2_cfc_map_prod_starAlgHom φ hφ (hfs.mono (Set.union_subset hσm hσc)) hm hc,
    ← gap2_cfc_map_prod_starAlgHom φ hφ (hfs.mono (Set.union_subset hσa hσc)) ha hc,
    ← gap2_cfc_map_prod_starAlgHom φ hφ (hfs.mono (Set.union_subset hσb hσc)) hb hc] at hmono
  exact hmono

private theorem gap2BlockExtension_cfcR_midpoint_le
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)]
    (U : Submodule ℂ K) [U.HasOrthogonalProjection]
    [instCU : CompleteSpace U] [instCUp : CompleteSpace Uᗮ]
    [CompleteSpace (WithLp 2 (↥U × ↥Uᗮ))]
    [instCFCU : ContinuousFunctionalCalculus ℝ (U →L[ℂ] U) IsSelfAdjoint]
    [instCFCUp : ContinuousFunctionalCalculus ℝ (Uᗮ →L[ℂ] Uᗮ) IsSelfAdjoint]
    [instNontrivU : Nontrivial (U →L[ℂ] U)]
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0))
    (hfinite : @HansenPedersen.HOperatorMidpointConvexOnInterval U _ _ instCU
      instCFCU instNontrivU (Set.Ioi 0) f)
    {A B : K →L[ℂ] K} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {α β t₀ : ℝ} (hIcc : Set.Icc α β ⊆ Set.Ioi (0 : ℝ))
    (hA_bounds : (α : ℂ) • (1 : K →L[ℂ] K) ≤ A ∧
      A ≤ (β : ℂ) • (1 : K →L[ℂ] K))
    (hB_bounds : (α : ℂ) • (1 : K →L[ℂ] K) ≤ B ∧
      B ≤ (β : ℂ) • (1 : K →L[ℂ] K))
    (ht₀ : t₀ ∈ Set.Icc α β) :
    cfc (R := ℝ) f
        (U.starProjection * ((1 / 2 : ℝ) • (A + B)) * U.starProjection +
          (t₀ : ℂ) • (1 - U.starProjection)) ≤
      (1 / 2 : ℝ) •
        (cfc (R := ℝ) f
            (U.starProjection * A * U.starProjection +
              (t₀ : ℂ) • (1 - U.starProjection)) +
          cfc (R := ℝ) f
            (U.starProjection * B * U.starProjection +
              (t₀ : ℂ) • (1 - U.starProjection))) := by
  let a : U →L[ℂ] U := U.orthogonalProjection ∘L A ∘L U.subtypeL
  let b : U →L[ℂ] U := U.orthogonalProjection ∘L B ∘L U.subtypeL
  let c : Uᗮ →L[ℂ] Uᗮ := (t₀ : ℂ) • 1
  -- The facts are stated without type ascriptions: their types come from the lemmas, which
  -- avoids re-synthesizing the real algebra structures of the corner algebras.
  have ha := gap2Compression_isSelfAdjoint U hA
  have hb := gap2Compression_isSelfAdjoint U hB
  have hc := @gap2Scalar_isSelfAdjoint Uᗮ _ _ instCUp t₀
  have hσa := gap2Compression_spectrum_subset_Icc U hA hA_bounds
  have hσb := gap2Compression_spectrum_subset_Icc U hB hB_bounds
  have hσc := @gap2Scalar_spectrum_subset_Icc Uᗮ _ _ instCUp instCFCUp α β t₀ ht₀
  obtain ⟨hm, hσm⟩ := @gap2_midpoint_isSelfAdjoint_spectrum_subset U _ _ instCU instCFCU
    instNontrivU _ (convex_Icc α β) a b ha hb hσa hσb
  have hres := gap2_cfc_midpoint_le_of_prod_starAlgHom
    (instSA := @ContinuousLinearMap.instStarOrderedRing U _ _ instCU)
    (instSB := @ContinuousLinearMap.instStarOrderedRing Uᗮ _ _ instCUp)
    (gap2BlockStarAlgHom U) (gap2BlockStarAlgHom_continuous U) (hf.mono hIcc) ha hb hc
    hm hσa hσb hσm hσc
    (hfinite ha hb (fun x hx => hIcc (hσa hx)) (fun x hx => hIcc (hσb hx)))
  have hblockA : gap2BlockStarAlgHom U (a, c) =
      U.starProjection * A * U.starProjection +
        (t₀ : ℂ) • (1 - U.starProjection) :=
    gap2BlockStarAlgHom_compression_scalar U A t₀
  have hblockB : gap2BlockStarAlgHom U (b, c) =
      U.starProjection * B * U.starProjection +
        (t₀ : ℂ) • (1 - U.starProjection) :=
    gap2BlockStarAlgHom_compression_scalar U B t₀
  have hblockM :=
    (congrArg (fun x => gap2BlockStarAlgHom U (x, c)) (gap2Compression_midpoint U A B)).symm.trans
      (gap2BlockStarAlgHom_compression_scalar U ((1 / 2 : ℝ) • (A + B)) t₀)
  rw [← hblockM, ← hblockA, ← hblockB]
  exact hres

private theorem gap2_hOperatorMidpoint_Ioi_of_linearIsometryEquiv
    {E K : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [ContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint]
    [Nontrivial (E →L[ℂ] E)]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)]
    (e : E ≃ₗᵢ[ℂ] K) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0))
    (hE : HansenPedersen.HOperatorMidpointConvexOnInterval E (Set.Ioi 0) f) :
    HansenPedersen.HOperatorMidpointConvexOnInterval K (Set.Ioi 0) f := by
  intro A B hA hB hσA hσB
  let φ : (K →L[ℂ] K) ≃⋆ₐ[ℂ] (E →L[ℂ] E) := e.symm.conjStarAlgEquiv
  letI : IsScalarTower ℝ ℂ (E →L[ℂ] E) := RestrictScalars.isScalarTower ℝ ℂ (E →L[ℂ] E)
  letI : IsScalarTower ℝ ℂ (K →L[ℂ] K) := RestrictScalars.isScalarTower ℝ ℂ (K →L[ℂ] K)
  obtain ⟨hM, hσM⟩ := gap2_midpoint_isSelfAdjoint_spectrum_subset (convex_Ioi 0) hA hB hσA hσB
  have hσφA : spectrum ℝ (φ A) ⊆ Set.Ioi 0 := by
    rw [gap2_starAlgEquiv_real_spectrum_eq φ A]
    exact hσA
  have hσφB : spectrum ℝ (φ B) ⊆ Set.Ioi 0 := by
    rw [gap2_starAlgEquiv_real_spectrum_eq φ B]
    exact hσB
  exact gap2_midpoint_le_of_starAlgEquiv hf φ (StarAlgEquiv.isometry φ).continuous
    hA hB hσA hσB hM hσM (hE (hA.map φ) (hB.map φ) hσφA hσφB)

private theorem gap2_le_of_quadratic_form_nonneg
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {S T : K →L[ℂ] K} (hself : IsSelfAdjoint (T - S))
    (hquad : ∀ x : K, 0 ≤ RCLike.re (inner ℂ ((T - S) x) x)) :
    S ≤ T := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff_complex]
  intro x
  refine ⟨?_, hquad x⟩
  have hsymm : (T - S).toLinearMap.IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hself
  exact Complex.conj_eq_iff_re.mp
    ((LinearMap.isSymmetric_iff_inner_map_self_real _).mp hsymm x)

/-- Self-adjointness of the block extension `P T P + t₀ (1 - P)` for a finite-dimensional
subspace. -/
private theorem gap2BlockExtension_isSelfAdjoint_of_finiteDimensional
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : Submodule ℂ K) [FiniteDimensional ℂ U]
    {T : K →L[ℂ] K} (hT : IsSelfAdjoint T) (t₀ : ℝ) :
    IsSelfAdjoint
      (U.starProjection * T * U.starProjection + (t₀ : ℂ) • (1 - U.starProjection)) := by
  letI : CompleteSpace U := U.complete_of_finiteDimensional.completeSpace_coe
  letI : CompleteSpace Uᗮ := inferInstance
  letI : CompleteSpace (WithLp 2 (↥U × ↥Uᗮ)) := inferInstance
  exact gap2BlockExtension_isSelfAdjoint U hT t₀

/-- Spectral window of the block extension `P T P + t₀ (1 - P)` for a finite-dimensional
subspace. -/
private theorem gap2BlockExtension_spectrum_subset_Icc_of_finiteDimensional
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)]
    (U : Submodule ℂ K) [FiniteDimensional ℂ U]
    {T : K →L[ℂ] K} {α β t₀ : ℝ} (hT : IsSelfAdjoint T)
    (hTbounds : (α : ℂ) • (1 : K →L[ℂ] K) ≤ T ∧ T ≤ (β : ℂ) • (1 : K →L[ℂ] K))
    (ht₀ : t₀ ∈ Set.Icc α β) :
    spectrum ℝ
        (U.starProjection * T * U.starProjection + (t₀ : ℂ) • (1 - U.starProjection)) ⊆
      Set.Icc α β := by
  letI instCUs : CompleteSpace U := U.complete_of_finiteDimensional.completeSpace_coe
  letI instCUps : CompleteSpace Uᗮ := inferInstance
  letI : ContinuousFunctionalCalculus ℂ (U →L[ℂ] U) IsStarNormal :=
    @gap2CfcComplexEnd U _ _ instCUs
  letI : ContinuousFunctionalCalculus ℂ (Uᗮ →L[ℂ] Uᗮ) IsStarNormal :=
    @gap2CfcComplexEnd Uᗮ _ _ instCUps
  letI : ContinuousFunctionalCalculus ℝ (U →L[ℂ] U) IsSelfAdjoint :=
    @gap2CfcRealEnd U _ _ instCUs
  letI : ContinuousFunctionalCalculus ℝ (Uᗮ →L[ℂ] Uᗮ) IsSelfAdjoint :=
    @gap2CfcRealEnd Uᗮ _ _ instCUps
  letI : CompleteSpace (WithLp 2 (↥U × ↥Uᗮ)) := inferInstance
  exact gap2BlockExtension_spectrum_subset_Icc U hT hTbounds ht₀

/-- The finite-dimensional hypothesis, transported through a universe lift to a
finite-dimensional space in the base universe. -/
private theorem gap2_hOperatorMidpoint_of_finiteDimensional_lift
    {E0 : Type} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0] [instCE0 : CompleteSpace E0]
    [FiniteDimensional ℂ E0] [Nontrivial E0]
    [instCFCE0 : ContinuousFunctionalCalculus ℝ (E0 →L[ℂ] E0) IsSelfAdjoint]
    [instNE0 : Nontrivial (E0 →L[ℂ] E0)]
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0))
    (hfinite :
      ∀ (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
        [CompleteSpace K] [FiniteDimensional ℂ K]
        [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
        [Nontrivial (HansenPedersen.L K)],
        HansenPedersen.HOperatorMidpointConvexOnInterval K (Set.Ioi 0) f) :
    HansenPedersen.HOperatorMidpointConvexOnInterval E0 (Set.Ioi 0) f := by
  let E := ULift E0
  letI instNACE : NormedAddCommGroup E := by
    dsimp only [E]
    infer_instance
  letI instIPE : InnerProductSpace ℂ E := gap2ULiftInnerProductSpace
  letI instCE : CompleteSpace E := by
    dsimp only [E]
    exact @ULift.instCompleteSpace E0 _ instCE0
  letI instStarE : Star (E →L[ℂ] E) :=
    @ContinuousLinearMap.instStarId ℂ E _ _ instIPE instCE
  letI instCStarE : CStarAlgebra (E →L[ℂ] E) :=
    @instCStarAlgebraContinuousLinearMapComplexIdOfCompleteSpace E _ instIPE instCE
  letI instStarRingE : StarRing (E →L[ℂ] E) :=
    @CStarAlgebra.toStarRing _ instCStarE
  letI instCFCCE : ContinuousFunctionalCalculus ℂ (E →L[ℂ] E) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI instCFCE : ContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  letI instNE : Nontrivial (E →L[ℂ] E) := inferInstance
  have hfiniteLift := @hfinite E instNACE instIPE instCE
    (show FiniteDimensional ℂ E from inferInstance) instCFCE instNE
  exact @gap2_hOperatorMidpoint_Ioi_of_linearIsometryEquiv E E0
    instNACE instIPE instCE instCFCE instNE
    (inferInstance : NormedAddCommGroup E0)
    (inferInstance : InnerProductSpace ℂ E0) instCE0 instCFCE0 instNE0
    (show E ≃ₗᵢ[ℂ] E0 from LinearIsometryEquiv.ulift ℂ E0) f hf hfiniteLift

/-- The block midpoint inequality on a nontrivial finite-dimensional subspace, from the
finite-dimensional hypothesis (transported through a universe lift). -/
private theorem gap2BlockExtension_cfcR_midpoint_le_of_finiteDimensional
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)]
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0))
    (hfinite :
      ∀ (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
        [CompleteSpace K] [FiniteDimensional ℂ K]
        [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
        [Nontrivial (HansenPedersen.L K)],
        HansenPedersen.HOperatorMidpointConvexOnInterval K (Set.Ioi 0) f)
    (U : Submodule ℂ K) [FiniteDimensional ℂ U] [Nontrivial U]
    {A B : K →L[ℂ] K} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {α β t₀ : ℝ} (hIcc : Set.Icc α β ⊆ Set.Ioi (0 : ℝ))
    (hA_bounds : (α : ℂ) • (1 : K →L[ℂ] K) ≤ A ∧ A ≤ (β : ℂ) • (1 : K →L[ℂ] K))
    (hB_bounds : (α : ℂ) • (1 : K →L[ℂ] K) ≤ B ∧ B ≤ (β : ℂ) • (1 : K →L[ℂ] K))
    (ht₀ : t₀ ∈ Set.Icc α β) :
    cfc (R := ℝ) f
        (U.starProjection * ((1 / 2 : ℝ) • (A + B)) * U.starProjection +
          (t₀ : ℂ) • (1 - U.starProjection)) ≤
      (1 / 2 : ℝ) •
        (cfc (R := ℝ) f
            (U.starProjection * A * U.starProjection + (t₀ : ℂ) • (1 - U.starProjection)) +
          cfc (R := ℝ) f
            (U.starProjection * B * U.starProjection + (t₀ : ℂ) • (1 - U.starProjection))) := by
  letI instCUs : CompleteSpace U := U.complete_of_finiteDimensional.completeSpace_coe
  letI instCUps : CompleteSpace Uᗮ := inferInstance
  letI instNUs : Nontrivial (U →L[ℂ] U) := inferInstance
  letI : ContinuousFunctionalCalculus ℂ (U →L[ℂ] U) IsStarNormal :=
    @gap2CfcComplexEnd U _ _ instCUs
  letI : ContinuousFunctionalCalculus ℂ (Uᗮ →L[ℂ] Uᗮ) IsStarNormal :=
    @gap2CfcComplexEnd Uᗮ _ _ instCUps
  letI instCFCUs : ContinuousFunctionalCalculus ℝ (U →L[ℂ] U) IsSelfAdjoint :=
    @gap2CfcRealEnd U _ _ instCUs
  letI : ContinuousFunctionalCalculus ℝ (Uᗮ →L[ℂ] Uᗮ) IsSelfAdjoint :=
    @gap2CfcRealEnd Uᗮ _ _ instCUps
  letI : CompleteSpace (WithLp 2 (↥U × ↥Uᗮ)) := inferInstance
  have hfiniteUs :
      @HansenPedersen.HOperatorMidpointConvexOnInterval U _ _ instCUs
        instCFCUs instNUs (Set.Ioi 0) f :=
    @gap2_hOperatorMidpoint_of_finiteDimensional_lift U _ _ instCUs _ _ instCFCUs instNUs f hf
      hfinite
  exact gap2BlockExtension_cfcR_midpoint_le U hf hfiniteUs hA hB hIcc hA_bounds hB_bounds ht₀

/-- The block midpoint inequality for every finite span, including the empty one. -/
private theorem gap2BlockExtension_cfcR_midpoint_le_of_finiteSpan
    {K ι : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)]
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0))
    (hfinite :
      ∀ (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
        [CompleteSpace K] [FiniteDimensional ℂ K]
        [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
        [Nontrivial (HansenPedersen.L K)],
        HansenPedersen.HOperatorMidpointConvexOnInterval K (Set.Ioi 0) f)
    (b : HilbertBasis ι ℂ K) (s : Finset ι)
    {A B : K →L[ℂ] K} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {α β t₀ : ℝ} (hIcc : Set.Icc α β ⊆ Set.Ioi (0 : ℝ))
    (hA_bounds : (α : ℂ) • (1 : K →L[ℂ] K) ≤ A ∧ A ≤ (β : ℂ) • (1 : K →L[ℂ] K))
    (hB_bounds : (α : ℂ) • (1 : K →L[ℂ] K) ≤ B ∧ B ≤ (β : ℂ) • (1 : K →L[ℂ] K))
    (ht₀ : t₀ ∈ Set.Icc α β) :
    cfc (R := ℝ) f
        ((gap2FiniteSpan b s).starProjection * ((1 / 2 : ℝ) • (A + B)) *
            (gap2FiniteSpan b s).starProjection +
          (t₀ : ℂ) • (1 - (gap2FiniteSpan b s).starProjection)) ≤
      (1 / 2 : ℝ) •
        (cfc (R := ℝ) f
            ((gap2FiniteSpan b s).starProjection * A * (gap2FiniteSpan b s).starProjection +
              (t₀ : ℂ) • (1 - (gap2FiniteSpan b s).starProjection)) +
          cfc (R := ℝ) f
            ((gap2FiniteSpan b s).starProjection * B * (gap2FiniteSpan b s).starProjection +
              (t₀ : ℂ) • (1 - (gap2FiniteSpan b s).starProjection))) := by
  by_cases hs : s = ∅
  · have hP0 : (gap2FiniteSpan b s).starProjection = 0 := by
      subst hs
      simp [gap2FiniteSpan]
    rw [hP0]
    simp only [mul_zero, zero_mul, zero_add, sub_zero]
    exact gap2_le_midpoint le_rfl le_rfl
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    have hbi_mem : b i ∈ gap2FiniteSpan b s := Submodule.subset_span ⟨i, hi, rfl⟩
    have hbi_ne : (⟨b i, hbi_mem⟩ : gap2FiniteSpan b s) ≠ 0 := by
      intro hzero
      exact (b.orthonormal.ne_zero i) (by simpa using congrArg Subtype.val hzero)
    letI : Nontrivial (gap2FiniteSpan b s) := ⟨⟨⟨b i, hbi_mem⟩, 0, hbi_ne⟩⟩
    exact gap2BlockExtension_cfcR_midpoint_le_of_finiteDimensional hf hfinite
      (gap2FiniteSpan b s) hA hB hIcc hA_bounds hB_bounds ht₀

/-- The limit step: the midpoint inequality for block extensions converging strongly to
`A`, `B` and their midpoint passes to the limit. -/
private theorem gap2_midpoint_le_of_blockExtension_limit
    {K ι : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)] [Preorder ι] [NeBot (atTop : Filter ι)]
    {f : ℝ → ℝ} {α β : ℝ} (hfIcc : ContinuousOn f (Set.Icc α β))
    {A B M : K →L[ℂ] K} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hM : IsSelfAdjoint M)
    (hσA : spectrum ℝ A ⊆ Set.Icc α β) (hσB : spectrum ℝ B ⊆ Set.Icc α β)
    (hσM : spectrum ℝ M ⊆ Set.Icc α β)
    {At Bt Mt : ι → K →L[ℂ] K}
    (hAt : ∀ s, IsSelfAdjoint (At s)) (hBt : ∀ s, IsSelfAdjoint (Bt s))
    (hMt : ∀ s, IsSelfAdjoint (Mt s))
    (hσAt : ∀ s, spectrum ℝ (At s) ⊆ Set.Icc α β)
    (hσBt : ∀ s, spectrum ℝ (Bt s) ⊆ Set.Icc α β)
    (hσMt : ∀ s, spectrum ℝ (Mt s) ⊆ Set.Icc α β)
    (hAtT : ∀ x, Tendsto (fun s => At s x) atTop (𝓝 (A x)))
    (hBtT : ∀ x, Tendsto (fun s => Bt s x) atTop (𝓝 (B x)))
    (hMtT : ∀ x, Tendsto (fun s => Mt s x) atTop (𝓝 (M x)))
    (hblock : ∀ s, cfc (R := ℝ) f (Mt s) ≤
      (1 / 2 : ℝ) • (cfc (R := ℝ) f (At s) + cfc (R := ℝ) f (Bt s))) :
    cfc (R := ℝ) f M ≤ (1 / 2 : ℝ) • (cfc (R := ℝ) f A + cfc (R := ℝ) f B) := by
  have hcfA := cfcR_tendsto_sot_of_Icc hfIcc hAt hA hσAt hσA hAtT
  have hcfB := cfcR_tendsto_sot_of_Icc hfIcc hBt hB hσBt hσB hBtT
  have hcfM := cfcR_tendsto_sot_of_Icc hfIcc hMt hM hσMt hσM hMtT
  have hself_target : IsSelfAdjoint
      ((1 / 2 : ℝ) • (cfc (R := ℝ) f A + cfc (R := ℝ) f B) - cfc (R := ℝ) f M) :=
    ((IsSelfAdjoint.all _).smul ((IsSelfAdjoint.cfc (R := ℝ) (f := f) (a := A)).add
      (IsSelfAdjoint.cfc (R := ℝ) (f := f) (a := B)))).sub
      (IsSelfAdjoint.cfc (R := ℝ) (f := f) (a := M))
  refine gap2_le_of_quadratic_form_nonneg hself_target ?_
  intro x
  have hquad_s : ∀ s, 0 ≤ RCLike.re
      (inner ℂ (((1 / 2 : ℝ) • (cfc (R := ℝ) f (At s) + cfc (R := ℝ) f (Bt s)) -
          cfc (R := ℝ) f (Mt s)) x) x) := fun s =>
    ((ContinuousLinearMap.isPositive_iff_complex _).1
      ((ContinuousLinearMap.le_def _ _).mp (hblock s)) x).2
  have hmid_eval : Tendsto
      (fun s => (((1 / 2 : ℝ) • (cfc (R := ℝ) f (At s) + cfc (R := ℝ) f (Bt s)) -
          cfc (R := ℝ) f (Mt s)) x))
      atTop
      (𝓝 (((1 / 2 : ℝ) • (cfc (R := ℝ) f A + cfc (R := ℝ) f B) - cfc (R := ℝ) f M) x)) := by
    have hsum_eval := ((((hcfA x).add (hcfB x)).const_smul (1 / 2 : ℝ)).sub (hcfM x))
    simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply] using hsum_eval
  have hinner :=
    ((continuous_id.inner (𝕜 := ℂ) (continuous_const (y := x))).continuousAt.tendsto.comp
      hmid_eval)
  exact isClosed_Ici.mem_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hinner)
    (Filter.Eventually.of_forall hquad_s)

private theorem allH_midpointConvex_Ioi_of_finiteDimensional
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0))
    (hfinite :
      ∀ (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
        [CompleteSpace K] [FiniteDimensional ℂ K]
        [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
        [Nontrivial (HansenPedersen.L K)],
        HansenPedersen.HOperatorMidpointConvexOnInterval K (Set.Ioi 0) f) :
    HansenPedersen.AllHOperatorMidpointConvexOnInterval.{0}
      (Set.Ioi 0) f := by
  intro K instK instIP instCK instCFCK instNK A B hA hB hσA hσB
  obtain ⟨α, β, hHull, hIcc⟩ :=
    gap2_exists_compact_interval_subset_of_two_spectra hA hσA hσB (convex_Ioi 0)
  obtain ⟨t₀, ht₀σ⟩ :=
    ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) A hA
  have ht₀ : t₀ ∈ Set.Icc α β := hHull (Or.inl ht₀σ)
  have hA_bounds :=
    gap2_order_bounds_of_spectrum_subset_Icc hA (fun x hx => hHull (Or.inl hx))
  have hB_bounds :=
    gap2_order_bounds_of_spectrum_subset_Icc hB (fun x hx => hHull (Or.inr hx))
  obtain ⟨hM, hσM⟩ := gap2_midpoint_isSelfAdjoint_spectrum_subset (convex_Icc α β) hA hB
    (fun x hx => hHull (Or.inl hx)) (fun x hx => hHull (Or.inr hx))
  have hM_bounds :=
    gap2_order_bounds_of_spectrum_subset_Icc hM hσM
  obtain ⟨ι, b, hb⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := K)
  have hP := gap2FiniteSpan_starProjection_tendsto_self b
  have hPbound := gap2FiniteSpan_starProjection_norm_le b
  exact gap2_midpoint_le_of_blockExtension_limit (hf.mono hIcc) hA hB hM
    (fun x hx => hHull (Or.inl hx)) (fun x hx => hHull (Or.inr hx)) hσM
    (fun s => gap2BlockExtension_isSelfAdjoint_of_finiteDimensional (gap2FiniteSpan b s) hA t₀)
    (fun s => gap2BlockExtension_isSelfAdjoint_of_finiteDimensional (gap2FiniteSpan b s) hB t₀)
    (fun s => gap2BlockExtension_isSelfAdjoint_of_finiteDimensional (gap2FiniteSpan b s) hM t₀)
    (fun s => gap2BlockExtension_spectrum_subset_Icc_of_finiteDimensional (gap2FiniteSpan b s)
      hA hA_bounds ht₀)
    (fun s => gap2BlockExtension_spectrum_subset_Icc_of_finiteDimensional (gap2FiniteSpan b s)
      hB hB_bounds ht₀)
    (fun s => gap2BlockExtension_spectrum_subset_Icc_of_finiteDimensional (gap2FiniteSpan b s)
      hM hM_bounds ht₀)
    (gap2_blockExtension_tendsto_self hP hPbound) (gap2_blockExtension_tendsto_self hP hPbound)
    (gap2_blockExtension_tendsto_self hP hPbound)
    (fun s => gap2BlockExtension_cfcR_midpoint_le_of_finiteSpan hf hfinite b s hA hB hIcc
      hA_bounds hB_bounds ht₀)

/-- Matrix midpoint convexity on the positive half-line upgrades to the
all-Hilbert-space formulation, using only the Loewner finite-dimensional and
strong-operator-topology infrastructure. -/
theorem matrixMidpointConvex_to_allHOperatorMidpointConvex_Ioi_core
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    HansenPedersen.MatrixOperatorMidpointConvexOnInterval (Set.Ioi (0 : ℝ)) f →
      HansenPedersen.AllHOperatorMidpointConvexOnInterval.{0} (Set.Ioi (0 : ℝ)) f := by
  intro hmid
  apply allH_midpointConvex_Ioi_of_finiteDimensional.{0} hf
  intro K _ _ _ _ _ _
  exact finiteDimensional_midpointConvex_Ioi_of_matrix hf hmid

end Quantum.TraceInequality.Loewner
