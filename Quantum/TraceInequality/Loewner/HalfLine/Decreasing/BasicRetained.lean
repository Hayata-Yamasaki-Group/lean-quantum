import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.Relevel
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LownerHeinzCore
import Quantum.TraceInequality.Loewner.HalfLine.ClosedPositiveCFCReverse
import Quantum.TraceInequality.Loewner.HalfLine.ConvexRep
import Quantum.TraceInequality.Loewner.HalfLine.Decreasing.Basic

/-!
# Positive-ray decreasing representations: basic predicates

This module is the first stage of the Simon-style half-line decreasing-function
theory: core predicates, the resolvent kernel, scalar antitonicity, and
normalized reciprocal pullbacks.
-/

namespace Quantum.TraceInequality.Loewner

universe u

open CFC

open Set MeasureTheory Filter

open scoped ComplexOrder Matrix MatrixOrder NNReal Topology

noncomputable section

/--
Book-facing direct CFC predicate for positive-ray operator monotone decreasing
functions.

This packages nonnegativity of `g` on `(0,∞)` together with the uniform
operator-antitone CFC predicate from `LownerHeinzCore`.
-/
structure OperatorMonotoneDecreasingOnPositiveCFC (g : ℝ → ℝ) : Prop where
  nonneg : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → 0 ≤ g x
  antitone :
    LownerHeinzCore.OperatorAntitoneOnAll.{0} (Set.Ioi (0 : ℝ)) g

/--
gcongr antitone form of the direct positive-ray decreasing CFC predicate.
It delegates to the bundled `OperatorAntitoneOnAll` field.
-/
@[gcongr]
theorem loewnerHeinz_cfcR_le_loewnerHeinz_cfcR_of_le_of_operatorMonotoneDecreasingOnPositiveCFC
    {g : ℝ → ℝ} (hg : OperatorMonotoneDecreasingOnPositiveCFC g)
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [Nontrivial A]
    {a b : A} (hab : a ≤ b)
    (ha : IsSelfAdjoint a) (hqa : spectrum ℝ a ⊆ Set.Ioi (0 : ℝ))
    (hb : IsSelfAdjoint b) (hqb : spectrum ℝ b ⊆ Set.Ioi (0 : ℝ)) :
    LownerHeinzCore.cfcR g b ≤ LownerHeinzCore.cfcR g a :=
  hg.antitone (𝓑 := A) hb ha hab hqb hqa

private theorem positiveRayOnePointCStarDiagonalMatrix_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ cStarDiagonalMatrix (onePointNode x) := by
  have hdiag : (diagonalMatrix (onePointNode x)).PosSemidef := by
    have hnonneg : 0 ≤ fun _ : Fin 1 => ((x : ℝ) : ℂ) := by
      intro i
      change (0 : ℂ) ≤ ((x : ℝ) : ℂ)
      exact_mod_cast hx
    simpa [diagonalMatrix, onePointNode] using
      (Matrix.PosSemidef.diagonal (R := ℂ) hnonneg)
  simpa [cStarDiagonalMatrix] using
    cStarMatrix_nonneg_of_posSemidef hdiag

private theorem positiveRayOnePointCStarDiagonalMatrix_spectrum_subset_singleton
    (x : ℝ) :
    spectrum ℝ (cStarDiagonalMatrix (onePointNode x)) ⊆
      ({x} : Set ℝ) := by
  intro t ht
  let D : CStarMatrix (Fin 1) (Fin 1) ℂ :=
    cStarDiagonalMatrix (onePointNode x)
  have hpre :
      ((algebraMap ℝ ℂ) ⁻¹' spectrum ℂ D) = spectrum ℝ D := by
    exact
      @spectrum.preimage_algebraMap ℂ ℝ
        (CStarMatrix (Fin 1) (Fin 1) ℂ) _ _ _ _ _ _
        CStarMatrix.instIsScalarTower (a := D)
  change t ∈ spectrum ℝ D at ht
  rw [← hpre] at ht
  simp only [Set.mem_preimage] at ht
  change (t : ℂ) ∈ spectrum ℂ
    (cStarDiagonalMatrix (onePointNode x)) at ht
  rw [cStarDiagonalMatrix] at ht
  rw [CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv] at ht
  change (t : ℂ) ∈ spectrum ℂ
    (((CStarMatrix.ofMatrixStarAlgEquiv (A := ℂ) (n := Fin 1)).toAlgEquiv)
      (diagonalMatrix (onePointNode x))) at ht
  rw [AlgEquiv.spectrum_eq
    ((CStarMatrix.ofMatrixStarAlgEquiv (A := ℂ) (n := Fin 1)).toAlgEquiv)] at ht
  rw [diagonalMatrix, spectrum_diagonal] at ht
  rcases ht with ⟨i, hi⟩
  have hti : t = onePointNode x i := Complex.ofReal_injective hi.symm
  simp [onePointNode, hti]

private theorem positiveRayOnePointCStarDiagonalMatrix_spectrum_subset_Ioi
    {x : ℝ} (hx : 0 < x) :
    spectrum ℝ (cStarDiagonalMatrix (onePointNode x)) ⊆
      Set.Ioi (0 : ℝ) := by
  intro t ht
  have ht' := positiveRayOnePointCStarDiagonalMatrix_spectrum_subset_singleton x ht
  rw [Set.mem_singleton_iff] at ht'
  simpa [ht'] using hx

private theorem positiveRayOnePointCStarMatrix_cfcR_apply
    (g : ℝ → ℝ) (x : ℝ) :
    (LownerHeinzCore.cfcR g
      (cStarDiagonalMatrix (onePointNode x)) 0 0 : ℂ) =
        (g x : ℂ) := by
  let D : CStarMatrix (Fin 1) (Fin 1) ℂ :=
    cStarDiagonalMatrix (onePointNode x)
  let c : ℝ := g x
  have hspectrum : spectrum ℝ D ⊆ ({x} : Set ℝ) := by
    simpa [D] using
      positiveRayOnePointCStarDiagonalMatrix_spectrum_subset_singleton x
  have hsa : IsSelfAdjoint D := by
    rw [isSelfAdjoint_iff]
    have h := (diagonalMatrix_isSelfAdjoint
      (onePointNode x)).star_eq
    simpa [D, cStarDiagonalMatrix] using
      congrArg CStarMatrix.ofMatrix h
  have hmatch : Set.EqOn g (fun _ : ℝ => c) (spectrum ℝ D) := by
    intro t ht
    have ht' := hspectrum ht
    rw [Set.mem_singleton_iff] at ht'
    simp [c, ht']
  have hcfc :
      LownerHeinzCore.cfcR g D =
        algebraMap ℝ (CStarMatrix (Fin 1) (Fin 1) ℂ) c := by
    dsimp [LownerHeinzCore.cfcR]
    calc
      cfc g D = cfc (fun _ : ℝ => c) D := by
        exact cfc_congr hmatch
      _ = algebraMap ℝ (CStarMatrix (Fin 1) (Fin 1) ℂ) c := by
        exact cfc_const c D (ha := hsa)
  have hentry :=
    congrArg (fun M : CStarMatrix (Fin 1) (Fin 1) ℂ => M 0 0) hcfc
  simpa [D, c, cStarDiagonalMatrix, Matrix.algebraMap_matrix_apply]
    using hentry

private theorem antitoneOn_Ioi_of_operatorMonotoneDecreasingOnPositiveCFC
    {g : ℝ → ℝ} (hg : OperatorMonotoneDecreasingOnPositiveCFC g) :
    AntitoneOn g (Set.Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  let Dx : CStarMatrix (Fin 1) (Fin 1) ℂ :=
    cStarDiagonalMatrix (onePointNode x)
  let Dy : CStarMatrix (Fin 1) (Fin 1) ℂ :=
    cStarDiagonalMatrix (onePointNode y)
  have hxpos : 0 < x := by simpa using hx
  have hypos : 0 < y := by simpa using hy
  have hDx_nonneg : 0 ≤ Dx := by
    simpa [Dx] using
      positiveRayOnePointCStarDiagonalMatrix_nonneg (le_of_lt hxpos)
  have hDy_nonneg : 0 ≤ Dy := by
    simpa [Dy] using
      positiveRayOnePointCStarDiagonalMatrix_nonneg (le_of_lt hypos)
  have hDxy : Dx ≤ Dy := by
    simpa [Dx, Dy] using onePointCStarDiagonalMatrix_le hxy
  have hDx_spec : spectrum ℝ Dx ⊆ Set.Ioi (0 : ℝ) := by
    simpa [Dx] using
      positiveRayOnePointCStarDiagonalMatrix_spectrum_subset_Ioi hxpos
  have hDy_spec : spectrum ℝ Dy ⊆ Set.Ioi (0 : ℝ) := by
    simpa [Dy] using
      positiveRayOnePointCStarDiagonalMatrix_spectrum_subset_Ioi hypos
  have hanti :
      LownerHeinzCore.OperatorAntitoneOn
        (𝓐 := CStarMatrix (Fin 1) (Fin 1) ℂ) (Set.Ioi (0 : ℝ)) g := by
    exact hg.antitone (𝓑 := CStarMatrix (Fin 1) (Fin 1) ℂ)
  have hcfc_le : LownerHeinzCore.cfcR g Dy ≤ LownerHeinzCore.cfcR g Dx :=
    hanti (IsSelfAdjoint.of_nonneg hDy_nonneg) (IsSelfAdjoint.of_nonneg hDx_nonneg)
      hDxy hDy_spec hDx_spec
  have hdiff_nonneg :
      0 ≤ LownerHeinzCore.cfcR g Dx - LownerHeinzCore.cfcR g Dy := by
    exact sub_nonneg.mpr hcfc_le
  have hquad := cStarMatrix_quadratic_nonneg_of_nonneg
    hdiff_nonneg (Pi.single (0 : Fin 1) (1 : ℂ))
  have hxentry :
      (LownerHeinzCore.cfcR g Dx 0 0 : ℂ) = (g x : ℂ) := by
    simpa [Dx] using positiveRayOnePointCStarMatrix_cfcR_apply g x
  have hyentry :
      (LownerHeinzCore.cfcR g Dy 0 0 : ℂ) = (g y : ℂ) := by
    simpa [Dy] using positiveRayOnePointCStarMatrix_cfcR_apply g y
  have hcomplex : (0 : ℂ) ≤ ((g x) - (g y) : ℂ) := by
    simpa [Matrix.sub_apply, hxentry, hyentry] using hquad
  have hreal : 0 ≤ g x - g y := by
    exact_mod_cast hcomplex
  linarith

/--
A nonnegative direct CFC decreasing function on `(0,∞)` has a nonnegative limit
at `∞`.
-/
theorem positiveRayOperatorMonotoneDecreasingAtTopLimit_of_cfc
    {g : ℝ → ℝ} (hg : OperatorMonotoneDecreasingOnPositiveCFC g) :
    ∃ c : ℝ, 0 ≤ c ∧ Tendsto g atTop (𝓝 c) :=
  tendsto_atTop_of_antitoneOn_Ioi_nonneg
    (antitoneOn_Ioi_of_operatorMonotoneDecreasingOnPositiveCFC hg)
    hg.nonneg

end

end Quantum.TraceInequality.Loewner
