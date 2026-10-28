import Quantum.TraceInequality.Loewner.Koranyi.FiniteConstruction
import Quantum.TraceInequality.Loewner.Koranyi.FiniteSpectralMeasure
import Quantum.TraceInequality.Loewner.Koranyi.StieltjesTransform
import Quantum.TraceInequality.Loewner.Koranyi.DiracMeasureMass

import Mathlib.Analysis.InnerProductSpace.Basic


namespace Quantum.TraceInequality.Loewner

open MeasureTheory

open scoped UpperHalfPlane
open scoped ComplexOrder
open scoped MatrixOrder

noncomputable section

/-!
Step 56 (finite case): the discrete measure produced by the Korányi construction has uniformly
bounded mass.

More precisely, in the finite-point construction (Step 2), we obtain a self-adjoint operator `A`
and a vector `φ`.  We then consider the discrete measure
`diracMeasure_of_isSymmetric A hSym φ` (Step 3). Its total mass is `‖φ‖^2`
(Step 25), and by the Gram identity at the distinguished point `0`, this equals
`loewnerKernel f 0 0`.

This lemma is used to discharge the "mass bound" hypotheses needed for the normal-family /
diagonal extraction steps (Step 6–7) when applying the construction to a fixed function `f`.
-/

/-- Finite Koranyi data give a Dirac measure with exact Loewner mass and Pick positivity. -/
theorem koranyi_finite_construct_diracMeasure_univ_eq_loewnerKernel_zero_zero
    {n : ℕ} {f : ℝ → ℝ} {y : Fin (n + 1) → ℝ}
    (hy : pointsHyp (n := n) y)
    (hL : (loewnerMatrix (n := n) f y).PosDef) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : FiniteDimensional ℂ H),
      ∃ (v : Fin (n + 1) → H) (φ : H) (A : H →ₗ[ℂ] H) (hA : IsSelfAdjoint A),
        let hSym : A.IsSymmetric := (LinearMap.isSymmetric_iff_isSelfAdjoint A).2 hA
        let μ : Measure ℝ :=
          _root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric A hSym φ
        (∀ i j : Fin (n + 1),
          inner (𝕜 := ℂ) (v i) (v j) = (loewnerKernel f (y i) (y j) : ℂ)) ∧
        φ = v 0 ∧
        μ Set.univ = ENNReal.ofReal (loewnerKernel f 0 0) ∧
        (∀ z : ℂ, 0 < z.im →
          ∃ x : H,
            (A - z • (LinearMap.id : H →ₗ[ℂ] H)) x = φ ∧
              inner (𝕜 := ℂ) φ x = ∫ t, (1 / ((t : ℂ) - z)) ∂μ ∧
                0 ≤ (inner (𝕜 := ℂ) φ x).im) ∧
        (∀ z : ℍ, 0 ≤ (stieltjes μ z).im) := by
  classical
  rcases koranyi_finite_construct (n := n) (f := f) (y := y) hy hL with
    ⟨H, instH, instI, instFD, v, φ, A, hGram, hφ, hA, hAv, hEq, hInterp⟩
  letI : NormedAddCommGroup H := instH
  letI : InnerProductSpace ℂ H := instI
  letI : FiniteDimensional ℂ H := instFD
  have hSym : A.IsSymmetric := (LinearMap.isSymmetric_iff_isSelfAdjoint A).2 hA
  let μ : Measure ℝ := _root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric A hSym φ
  have hmass :
      μ Set.univ = ENNReal.ofReal (‖φ‖ ^ 2) := by
    simpa [μ] using (diracMeasure_of_isSymmetric_univ (T := A) (hT := hSym) (φ := φ))
  have hy0 : y 0 = 0 := hy.1
  have hnorm_sq : ‖φ‖ ^ 2 = loewnerKernel f 0 0 := by
    -- From the Gram identity at `(0,0)`, together with `φ = v 0`.
    have hinner :
        inner (𝕜 := ℂ) φ φ = (loewnerKernel f 0 0 : ℂ) := by
      simpa [hφ, hy0] using (hGram 0 0)
    -- Take real parts and use `re ⟪φ,φ⟫ = ‖φ‖^2`.
    have hre : (inner (𝕜 := ℂ) φ φ).re = loewnerKernel f 0 0 := by
      simpa using congrArg Complex.re hinner
    have hnorm : (inner (𝕜 := ℂ) φ φ).re = ‖φ‖ ^ 2 := by
      simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (x := φ))
    exact hnorm.symm.trans hre
  have hmass' : μ Set.univ = ENNReal.ofReal (loewnerKernel f 0 0) := by
    simpa [hnorm_sq] using hmass
  have hStep3 :
      ∀ z : ℂ,
        0 < z.im →
          ∃ x : H,
            (A - z • (LinearMap.id : H →ₗ[ℂ] H)) x = φ ∧
              inner (𝕜 := ℂ) φ x =
                  ∫ t, (1 / ((t : ℂ) - z)) ∂μ ∧
                0 ≤ (inner (𝕜 := ℂ) φ x).im := by
    intro z hz
    -- This is Step 3, specialized to the self-adjoint operator `A`.
    have hfin :
        ∃ x : H,
          (A - z • (LinearMap.id : H →ₗ[ℂ] H)) x = φ ∧
            inner (𝕜 := ℂ) φ x =
                ∫ t, (1 / ((t : ℂ) - z))
                  ∂(_root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric A hSym φ) ∧
              0 ≤ (inner (𝕜 := ℂ) φ x).im := by
      -- Unfold the definition of `μ` afterwards.
      simpa using
        inner_solution_eq_integral_dirac_of_isSymmetric_im_nonneg_forall
          (T := A) (hT := hSym) (φ := φ) z hz
    rcases hfin with ⟨x, hsol, hx, him⟩
    refine ⟨x, hsol, ?_, him⟩
    simpa [μ] using hx
  have hPick : ∀ z : ℍ, 0 ≤ (stieltjes μ z).im := by
    exact stieltjes_im_nonneg_of_pick_data (A := A) (φ := φ) (μ := μ) hStep3
  refine ⟨H, instH, instI, instFD, v, φ, A, hA, ?_⟩
  dsimp
  refine ⟨?_, hφ, hmass', hStep3, hPick⟩
  intro i j
  exact hGram i j

end

end Quantum.TraceInequality.Loewner
