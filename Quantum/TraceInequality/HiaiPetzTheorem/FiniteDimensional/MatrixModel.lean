/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.Instances
import Quantum.TraceInequality.HiaiPetzTheorem.StrongOperatorTopology

import Mathlib.Analysis.InnerProductSpace.l2Space
import Quantum.TraceInequality.HiaiPetzTheorem.Basic

/-!
# Matrix models for finite-dimensional Hilbert spaces

This module transports real and complex functional calculus statements between
finite-dimensional Hilbert-space operators and concrete matrix algebras.  It is
the finite-dimensional layer that lets matrix monotonicity and matrix midpoint
convexity be used for arbitrary finite-dimensional complex Hilbert spaces.

## Main results

* `matrixOperatorMonotoneOnInterval_of_finiteDimensional`: matrix monotonicity
  implies the operator monotonicity inequality on any finite-dimensional
  Hilbert space.
* `matrixOperatorConvexOnInterval_of_finiteDimensional`: matrix midpoint
  convexity implies the corresponding finite-dimensional operator inequality.
* `realCfc_monotone_bridge_sort_named` and
  `realCfc_midpoint_convex_bridge_sort_named`: bridges from real CFC inequalities
  to complex normal CFC inequalities.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021,
  Section 5.1.
-/

namespace HansenPedersen

universe u

open CFC MeasureTheory
open scoped Topology MatrixOrder CStarAlgebra
open Filter
open HansenPedersen.Internal

section NormalCFC514

/-- A complex star-algebra equivalence preserving the real scalar structure
preserves the real spectrum. -/
theorem starAlgEquiv_real_spectrum_eq
    {A B : Type*} [Ring A] [Ring B] [Star A] [Star B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra ℝ A] [Algebra ℝ B]
    [IsScalarTower ℝ ℂ A] [IsScalarTower ℝ ℂ B]
    (φ : A ≃⋆ₐ[ℂ] B) (a : A) :
    spectrum ℝ (φ a) = spectrum ℝ a := by
  simpa using AlgEquiv.spectrum_eq (φ.restrictScalars ℝ) a

/-- Real continuous functional calculus commutes with a continuous star-algebra
equivalence on self-adjoint elements. -/
theorem starAlgEquiv_cfcR_transport
    {K E : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [ContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint]
    {J : Set ℝ} {f : ℝ → ℝ} {A : K →L[ℂ] K}
    (φ : (K →L[ℂ] K) ≃⋆ₐ[ℂ] (E →L[ℂ] E))
    (hfJ : ContinuousOn f J) (hσA : spectrum ℝ A ⊆ J) (hA : IsSelfAdjoint A) :
    φ (cfc (R := ℝ) f A) = cfc (R := ℝ) f (φ A) := by
  let φR := φ.restrictScalars ℝ
  have hφRA : IsSelfAdjoint (φR A) := by
    have h1 : φR (star A) = φR A := congrArg φR hA
    simpa [map_star] using h1
  have hφcont : Continuous φ := (StarAlgEquiv.isometry φ).continuous
  simpa [φR] using
    StarAlgHomClass.map_cfc φR f A (hf := hfJ.mono hσA)
      (hφ := by simpa [φR] using hφcont) (ha := hA) (hφa := hφRA)

/-- Real CFC commutes with a star-algebra equivalence onto a matrix algebra, where the matrix
side uses `matrixCfcR`. -/
theorem starAlgEquiv_matrixCfcR
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint] {n : ℕ}
    (χ : (K →L[ℂ] K) ≃⋆ₐ[ℂ] Mₙ n) {f : ℝ → ℝ} {S : K →L[ℂ] K}
    (hf : ContinuousOn f (spectrum ℝ S)) (hS : IsSelfAdjoint S) :
    χ (cfc (R := ℝ) f S) = matrixCfcR f (χ S) := by
  have h := starAlgEquiv_cfcR_transport
    (χ.trans (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))) hf subset_rfl hS
  change χ (cfc (R := ℝ) f S) = (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm
    (cfc (R := ℝ) f ((χ.trans (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))) S))
  rw [← h]
  exact ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm_apply_apply _).symm

/-- Converts a midpoint real-CFC convexity inequality into the corresponding
complex normal CFC inequality for a named extension `g = fun z => f z.re`. -/
theorem realCfc_midpoint_convex_bridge_sort_named
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [StarOrderedRing (K →L[ℂ] K)] [AddRightMono (K →L[ℂ] K)]
    [NonnegSpectrumClass ℝ (K →L[ℂ] K)]
    [ContinuousFunctionalCalculus ℂ (K →L[ℂ] K) IsStarNormal]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    {f : ℝ → ℝ} {g : ℂ → ℂ} {M A B : K →L[ℂ] K}
    (hg : g = fun z : ℂ => (f z.re : ℂ))
    (hM : IsSelfAdjoint M) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hsub_fc :
      cfc (R := ℝ) f M ≤ (1 / 2 : ℝ) • (cfc (R := ℝ) f A + cfc (R := ℝ) f B)) :
    cfc (R := ℂ) g M ≤ (1 / 2 : ℝ) • (cfc (R := ℂ) g A + cfc (R := ℂ) g B) := by
  subst hg
  have hM_real :
      cfc (R := ℝ) f M = cfc (R := ℂ) (fun z : ℂ => (f z.re : ℂ)) M := by
    simpa using
      (cfc_real_eq_complex (A := K →L[ℂ] K) (f := f) (a := M) hM)
  have hA_real :
      cfc (R := ℝ) f A = cfc (R := ℂ) (fun z : ℂ => (f z.re : ℂ)) A := by
    simpa using
      (cfc_real_eq_complex (A := K →L[ℂ] K) (f := f) (a := A) hA)
  have hB_real :
      cfc (R := ℝ) f B = cfc (R := ℂ) (fun z : ℂ => (f z.re : ℂ)) B := by
    simpa using
      (cfc_real_eq_complex (A := K →L[ℂ] K) (f := f) (a := B) hB)
  rw [← hM_real, ← hA_real, ← hB_real]
  exact hsub_fc

private theorem exists_compact_interval_subset_of_two_spectra
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
  have hXne : X.Nonempty := by
    exact (ContinuousFunctionalCalculus.spectrum_nonempty S hS).mono
      (by intro x hx; exact Or.inl hx)
  have hXbddBelow : BddBelow X := hXcompact.bddBelow
  have hXbddAbove : BddAbove X := hXcompact.bddAbove
  refine ⟨sInf X, sSup X, subset_Icc_csInf_csSup hXbddBelow hXbddAbove, ?_⟩
  have hsInf_mem : sInf X ∈ X := hXcompact.sInf_mem hXne
  have hsSup_mem : sSup X ∈ X := hXcompact.sSup_mem hXne
  have hXJ : X ⊆ J := by
    intro x hx
    rcases hx with hxS | hxT
    · exact hσS hxS
    · exact hσT hxT
  exact hJ.ordConnected.out (hXJ hsInf_mem) (hXJ hsSup_mem)

/-- A common lower bound of two elements bounds their midpoint. -/
private theorem le_midpoint_of_le {A : Type*} [AddCommGroup A] [PartialOrder A]
    [IsOrderedAddMonoid A] [Module ℝ A] [PosSMulMono ℝ A] {x y z : A}
    (hy : x ≤ y) (hz : x ≤ z) : x ≤ (1 / 2 : ℝ) • (y + z) := by
  have h := smul_le_smul_of_nonneg_left (add_le_add hy hz) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rwa [← two_smul ℝ x, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h

/-- A common upper bound of two elements bounds their midpoint. -/
private theorem midpoint_le_of_le {A : Type*} [AddCommGroup A] [PartialOrder A]
    [IsOrderedAddMonoid A] [Module ℝ A] [PosSMulMono ℝ A] {x y z : A}
    (hy : y ≤ x) (hz : z ≤ x) : (1 / 2 : ℝ) • (y + z) ≤ x := by
  have h := smul_le_smul_of_nonneg_left (add_le_add hy hz) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rwa [← two_smul ℝ x, smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h

/-- The midpoint of two self-adjoint operators with spectra in a convex set `J` has spectrum
in `J`. -/
private theorem spectrum_midpoint_subset_of_convex
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)]
    {J : Set ℝ} (hJ : Convex ℝ J)
    {S T : K →L[ℂ] K} (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (hM : IsSelfAdjoint ((1 / 2 : ℝ) • (S + T)))
    (hσS : spectrum ℝ S ⊆ J) (hσT : spectrum ℝ T ⊆ J) :
    spectrum ℝ ((1 / 2 : ℝ) • (S + T)) ⊆ J := by
  obtain ⟨α, β, hHull, hIccJ⟩ :=
    exists_compact_interval_subset_of_two_spectra (K := K) hS hσS hσT hJ
  have hS_bounds := order_bounds_of_spectrum_subset_Icc_clm (K := K) hS
    (fun x hx => hHull (Or.inl hx))
  have hT_bounds := order_bounds_of_spectrum_subset_Icc_clm (K := K) hT
    (fun x hx => hHull (Or.inr hx))
  exact fun x hx => hIccJ (spectrum_subset_Icc_of_order_bounds_clm (K := K) hM
    (le_midpoint_of_le hS_bounds.1 hT_bounds.1) (midpoint_le_of_le hS_bounds.2 hT_bounds.2) hx)

/-- Matrix midpoint convexity on an interval transfers to every
finite-dimensional complex Hilbert space.  The proof moves the pair of
self-adjoint operators to matrices, applies matrix convexity there, and
transports the resulting CFC inequality back. -/
theorem matrixOperatorConvexOnInterval_of_finiteDimensional
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [FiniteDimensional ℂ K] [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)]
    {J : Set ℝ} {f : ℝ → ℝ} (hJ : Convex ℝ J) (hfJ : ContinuousOn f J)
    (hmat : MatrixOperatorMidpointConvexOnInterval J f)
    {S T : K →L[ℂ] K} (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (hσS : spectrum ℝ S ⊆ J) (hσT : spectrum ℝ T ⊆ J) :
    cfc (R := ℝ) f ((1 / 2 : ℝ) • (S + T)) ≤
      (1 / 2 : ℝ) • (cfc (R := ℝ) f S + cfc (R := ℝ) f T) := by
  /- Move the pair to matrices by a star-algebra equivalence, apply matrix midpoint convexity
  there, and pull the inequality back; real CFC commutes with the equivalence. -/
  let φm : (K →L[ℂ] K) ≃⋆ₐ[ℂ] Mₙ (Module.finrank ℂ K) :=
    ((stdOrthonormalBasis ℂ K).repr.conjStarAlgEquiv).trans
      (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℂ K)) (𝕜 := ℂ)).symm
  have hmid : ∀ X Y : K →L[ℂ] K,
      φm ((1 / 2 : ℝ) • (X + Y)) = (1 / 2 : ℝ) • (φm X + φm Y) := by
    intro X Y
    have h := map_smul (φm.toAlgEquiv.restrictScalars ℝ) (1 / 2 : ℝ) (X + Y)
    rw [map_add] at h
    exact h
  have hM : IsSelfAdjoint ((1 / 2 : ℝ) • (S + T)) :=
    IsSelfAdjoint.smul (IsSelfAdjoint.all (1 / 2 : ℝ)) (hS.add hT)
  have hσM := spectrum_midpoint_subset_of_convex hJ hS hT hM hσS hσT
  have hmat' := hmat (hS.map φm) (hT.map φm)
    ((starAlgEquiv_real_spectrum_eq φm S).trans_subset hσS)
    ((starAlgEquiv_real_spectrum_eq φm T).trans_subset hσT)
  rw [← hmid, ← starAlgEquiv_matrixCfcR φm (hfJ.mono hσM) hM,
    ← starAlgEquiv_matrixCfcR φm (hfJ.mono hσS) hS,
    ← starAlgEquiv_matrixCfcR φm (hfJ.mono hσT) hT, ← hmid] at hmat'
  exact (map_le_map_iff φm).1 hmat'

end NormalCFC514

end HansenPedersen
