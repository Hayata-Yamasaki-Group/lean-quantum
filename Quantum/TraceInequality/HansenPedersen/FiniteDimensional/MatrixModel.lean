/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.Instances
import Quantum.TraceInequality.HiaiPetzTheorem.StrongOperatorTopology

import Mathlib.Analysis.InnerProductSpace.l2Space
import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.MatrixModel

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

/-- Matrix monotonicity on an interval transfers to every finite-dimensional
complex Hilbert space by conjugating operators to matrices and transporting
real CFC through the star-algebra equivalences. -/
theorem matrixOperatorMonotoneOnInterval_of_finiteDimensional
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [FiniteDimensional ℂ K] [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    [Nontrivial (K →L[ℂ] K)]
    {J : Set ℝ} {f : ℝ → ℝ} (hfJ : ContinuousOn f J)
    (hmat : Quantum.TraceInequality.MatrixOperatorMonotoneOnInterval J f)
    {S T : K →L[ℂ] K} (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T)
    (hσS : spectrum ℝ S ⊆ J) (hσT : spectrum ℝ T ⊆ J) (hST : S ≤ T) :
    cfc f S ≤ cfc f T := by
  let φm : (K →L[ℂ] K) ≃⋆ₐ[ℂ] Mₙ (Module.finrank ℂ K) :=
    ((stdOrthonormalBasis ℂ K).repr.conjStarAlgEquiv).trans
      (Matrix.toEuclideanCLM (n := Fin (Module.finrank ℂ K)) (𝕜 := ℂ)).symm
  have hmat' : matrixCfcR f (φm S) ≤ matrixCfcR f (φm T) :=
    hmat (hS.map φm) (hT.map φm)
      ((starAlgEquiv_real_spectrum_eq φm S).trans_subset hσS)
      ((starAlgEquiv_real_spectrum_eq φm T).trans_subset hσT)
      ((map_le_map_iff φm).2 hST)
  rw [← starAlgEquiv_matrixCfcR φm (hfJ.mono hσS) hS,
    ← starAlgEquiv_matrixCfcR φm (hfJ.mono hσT) hT] at hmat'
  exact (map_le_map_iff φm).1 hmat'

attribute [gcongr] matrixOperatorMonotoneOnInterval_of_finiteDimensional

/-- Converts an inequality between real CFC values of self-adjoint operators
into the corresponding inequality for the complex normal CFC of
`z ↦ f z.re`. -/
theorem realCfc_monotone_bridge_sort
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [StarOrderedRing (K →L[ℂ] K)] [AddRightMono (K →L[ℂ] K)]
    [NonnegSpectrumClass ℝ (K →L[ℂ] K)]
    [ContinuousFunctionalCalculus ℂ (K →L[ℂ] K) IsStarNormal]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    {f : ℝ → ℝ} {A B : K →L[ℂ] K}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hsub_fc : cfc (R := ℝ) f A ≤ cfc (R := ℝ) f B) :
    cfc (R := ℂ) (fun z : ℂ => (f z.re : ℂ)) A ≤
      cfc (R := ℂ) (fun z : ℂ => (f z.re : ℂ)) B := by
  have hA_real :
      cfc (R := ℝ) f A = cfc (R := ℂ) (fun z : ℂ => (f z.re : ℂ)) A := by
    simpa using
      (cfc_real_eq_complex (A := K →L[ℂ] K) (f := f) (a := A) hA)
  have hB_real :
      cfc (R := ℝ) f B = cfc (R := ℂ) (fun z : ℂ => (f z.re : ℂ)) B := by
    simpa using
      (cfc_real_eq_complex (A := K →L[ℂ] K) (f := f) (a := B) hB)
  rw [← hA_real, ← hB_real]
  exact hsub_fc

attribute [gcongr] realCfc_monotone_bridge_sort

/-- Named-function variant of `realCfc_monotone_bridge_sort`, replacing
`g` by `z ↦ f z.re` through an explicit equality hypothesis. -/
theorem realCfc_monotone_bridge_sort_named
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [StarOrderedRing (K →L[ℂ] K)] [AddRightMono (K →L[ℂ] K)]
    [NonnegSpectrumClass ℝ (K →L[ℂ] K)]
    [ContinuousFunctionalCalculus ℂ (K →L[ℂ] K) IsStarNormal]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    {f : ℝ → ℝ} {g : ℂ → ℂ} {A B : K →L[ℂ] K}
    (hg : g = fun z : ℂ => (f z.re : ℂ))
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hsub_fc : cfc (R := ℝ) f A ≤ cfc (R := ℝ) f B) :
    cfc (R := ℂ) g A ≤ cfc (R := ℂ) g B := by
  subst hg
  exact realCfc_monotone_bridge_sort hA hB hsub_fc

attribute [gcongr] realCfc_monotone_bridge_sort_named

/-- Transport of the matrix real CFC through `Matrix.toEuclideanCLM` on an atom
matrix: the star-algebra equivalence cancels with its inverse in the definition
of `matrixCfcR`.  Extracted from
`matrixOperatorConvexOnInterval_of_finiteDimensional` so that the heavy
equivalence unfolding elaborates once (same pattern as
`toEuclideanCLM_matrixPower` in the HiaiPetz `MatrixPower` family). -/
private lemma toEuclideanCLM_matrixCfcR {n : ℕ} (f : ℝ → ℝ) (m : Mₙ n) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (matrixCfcR f m) =
      cfc (R := ℝ) f (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) m) := by
  simp [matrixCfcR]

end NormalCFC514

end HansenPedersen
