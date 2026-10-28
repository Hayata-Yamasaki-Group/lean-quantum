import Quantum.TraceInequality.Loewner.Koranyi.FiniteConstruction
import Quantum.TraceInequality.Loewner.Koranyi.FiniteSpectralMeasure


namespace Quantum.TraceInequality.Loewner

open scoped BigOperators
open scoped ComplexOrder
open scoped MatrixOrder

noncomputable section

open MeasureTheory

section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Step 3, packaged for self-adjoint operators: for `z` in the upper half-plane, we obtain a
discrete measure `μ` such that `⟪φ, x⟫` is its Stieltjes transform, and its imaginary part is
nonnegative. -/
theorem inner_solution_eq_integral_dirac_of_isSelfAdjoint_im_nonneg_forall
    (A : E →ₗ[ℂ] E) (hA : IsSelfAdjoint A) (φ : E) :
    ∀ z : ℂ,
      0 < z.im →
        ∃ x : E,
          (A - z • (LinearMap.id : E →ₗ[ℂ] E)) x = φ ∧
            inner (𝕜 := ℂ) φ x =
                ∫ t, (1 / ((t : ℂ) - z))
                  ∂(_root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric A
                      ((LinearMap.isSymmetric_iff_isSelfAdjoint A).2 hA) φ) ∧
              0 ≤ (inner (𝕜 := ℂ) φ x).im := by
  intro z hz
  have hSym : A.IsSymmetric := (LinearMap.isSymmetric_iff_isSelfAdjoint A).2 hA
  simpa [hSym] using
    inner_solution_eq_integral_dirac_of_isSymmetric_im_nonneg_forall A hSym φ z hz

/-- Self-adjoint Step 3 as an existential measure and solution for one upper-half-plane point. -/
theorem inner_solution_eq_integral_dirac_of_isSelfAdjoint_im_nonneg
    (A : E →ₗ[ℂ] E) (hA : IsSelfAdjoint A) (φ : E) (z : ℂ) (hz : 0 < z.im) :
    ∃ μ : Measure ℝ,
      ∃ x : E,
        (A - z • (LinearMap.id : E →ₗ[ℂ] E)) x = φ ∧
          inner (𝕜 := ℂ) φ x = ∫ t, (1 / ((t : ℂ) - z)) ∂μ ∧
            0 ≤ (inner (𝕜 := ℂ) φ x).im := by
  have hSym : A.IsSymmetric := (LinearMap.isSymmetric_iff_isSelfAdjoint A).2 hA
  simpa using
    inner_solution_eq_integral_dirac_of_isSymmetric_im_nonneg (T := A) (hT := hSym) (φ := φ)
      (z := z) hz

end

section

variable {n : ℕ} {f : ℝ → ℝ} {y : Fin (n + 1) → ℝ}

/-- Step 4 (finite case, one-shot): starting from a positive definite Loewner matrix (Step 2),
we obtain a self-adjoint operator `A` and then apply Step 3 to represent the scalar
`⟪φ, x⟫` as a discrete integral with nonnegative imaginary part. -/
theorem koranyi_finite_construct_inner_solution_im_nonneg
    (hy : pointsHyp (n := n) y)
    (hL : (loewnerMatrix (n := n) f y).PosDef) (z : ℂ) (hz : 0 < z.im) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : FiniteDimensional ℂ H),
      ∃ (v : Fin (n + 1) → H) (φ : H) (A : H →ₗ[ℂ] H),
        (∀ i j : Fin (n + 1),
          inner (𝕜 := ℂ) (v i) (v j) = (loewnerKernel f (y i) (y j) : ℂ)) ∧
        φ = v 0 ∧
        IsSelfAdjoint A ∧
        (∀ i, i ≠ 0 → A (v i) = (1 / (y i : ℂ)) • (v i - φ)) ∧
        (∀ i, i ≠ 0 → (v i - (y i : ℂ) • A (v i)) = φ) ∧
        (∀ i, i ≠ 0 →
          (f (y i) : ℂ) = (f 0 : ℂ) + (y i : ℂ) * inner (𝕜 := ℂ) (v i) φ) ∧
        ∃ μ : Measure ℝ,
          ∃ x : H,
            (A - z • (LinearMap.id : H →ₗ[ℂ] H)) x = φ ∧
              inner (𝕜 := ℂ) φ x = ∫ t, (1 / ((t : ℂ) - z)) ∂μ ∧
                0 ≤ (inner (𝕜 := ℂ) φ x).im := by
  classical
  rcases koranyi_finite_construct (n := n) (f := f) (y := y) hy hL with
    ⟨H, instH, instI, instFD, v, φ, A, hGram, hφ, hA, hAv, hEq, hInterp⟩
  letI : NormedAddCommGroup H := instH
  letI : InnerProductSpace ℂ H := instI
  letI : FiniteDimensional ℂ H := instFD
  have hStep3 :
      ∃ μ : Measure ℝ,
        ∃ x : H,
          (A - z • (LinearMap.id : H →ₗ[ℂ] H)) x = φ ∧
            inner (𝕜 := ℂ) φ x = ∫ t, (1 / ((t : ℂ) - z)) ∂μ ∧
              0 ≤ (inner (𝕜 := ℂ) φ x).im := by
    simpa using
      inner_solution_eq_integral_dirac_of_isSelfAdjoint_im_nonneg (A := A) hA (φ := φ) (z := z) hz
  refine ⟨H, instH, instI, instFD, v, φ, A, hGram, hφ, hA, hAv, hEq, hInterp, hStep3⟩

/-- Step 4 (finite case): package the Korányi construction (Step 2) together with the
Stieltjes representation and nonnegativity of the imaginary part (Step 3), in a form where the
measure does not depend on `z`. -/
theorem koranyi_finite_construct_pick_data
    (hy : pointsHyp (n := n) y)
    (hL : (loewnerMatrix (n := n) f y).PosDef) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : FiniteDimensional ℂ H),
      ∃ (v : Fin (n + 1) → H) (φ : H) (A : H →ₗ[ℂ] H),
        (∀ i j : Fin (n + 1),
          inner (𝕜 := ℂ) (v i) (v j) = (loewnerKernel f (y i) (y j) : ℂ)) ∧
        φ = v 0 ∧
        IsSelfAdjoint A ∧
        (∀ i, i ≠ 0 → A (v i) = (1 / (y i : ℂ)) • (v i - φ)) ∧
        (∀ i, i ≠ 0 → (v i - (y i : ℂ) • A (v i)) = φ) ∧
        (∀ i, i ≠ 0 →
          (f (y i) : ℂ) = (f 0 : ℂ) + (y i : ℂ) * inner (𝕜 := ℂ) (v i) φ) ∧
        ∃ μ : Measure ℝ,
          ∀ z : ℂ,
            0 < z.im →
              ∃ x : H,
                (A - z • (LinearMap.id : H →ₗ[ℂ] H)) x = φ ∧
                  inner (𝕜 := ℂ) φ x = ∫ t, (1 / ((t : ℂ) - z)) ∂μ ∧
                    0 ≤ (inner (𝕜 := ℂ) φ x).im := by
  classical
  rcases koranyi_finite_construct (n := n) (f := f) (y := y) hy hL with
    ⟨H, instH, instI, instFD, v, φ, A, hGram, hφ, hA, hAv, hEq, hInterp⟩
  letI : NormedAddCommGroup H := instH
  letI : InnerProductSpace ℂ H := instI
  letI : FiniteDimensional ℂ H := instFD
  have hSym : A.IsSymmetric := (LinearMap.isSymmetric_iff_isSelfAdjoint A).2 hA
  let μ : Measure ℝ := _root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric A hSym φ
  have hStep3 :
      ∀ z : ℂ,
        0 < z.im →
          ∃ x : H,
            (A - z • (LinearMap.id : H →ₗ[ℂ] H)) x = φ ∧
              inner (𝕜 := ℂ) φ x = ∫ t, (1 / ((t : ℂ) - z)) ∂μ ∧
                0 ≤ (inner (𝕜 := ℂ) φ x).im := by
    intro z hz
    rcases
        inner_solution_eq_integral_dirac_of_isSymmetric_im_nonneg_forall A hSym φ z hz with
      ⟨x, hsol, hx, him⟩
    refine ⟨x, hsol, ?_, him⟩
    simpa [μ] using hx
  refine ⟨H, instH, instI, instFD, v, φ, A, hGram, hφ, hA, hAv, hEq, hInterp, μ, hStep3⟩

end

end

end Quantum.TraceInequality.Loewner
