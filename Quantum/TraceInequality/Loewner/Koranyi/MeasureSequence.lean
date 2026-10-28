import Quantum.TraceInequality.Loewner.Koranyi.FiniteMeasureMassBound
import Quantum.TraceInequality.Loewner.Koranyi.PackageStructures


namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set Filter

open scoped UpperHalfPlane
open scoped ComplexOrder
open scoped MatrixOrder

noncomputable section

/-!
Step 57 (bridge): from a family of finite-point Löwner matrices (`PosDef`) we produce a sequence of
discrete measures with a uniform mass bound and Pick property.

This packages the data coming from the finite Korányi construction (Step 2) and the Dirac-measure
mass computation (Step 56).
-/

/-- Finite positive Loewner matrices produce discrete measures with uniform mass and Pick data. -/
theorem exists_measureSeq_of_loewnerMatrix_posDef
    (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hy : ∀ n : ℕ, pointsHyp (n := n) (y n))
    (hL : ∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef) :
    Nonempty (Loewner.RawMeasureSeqPackage f) := by
  classical
  have hex :
      ∀ n : ℕ,
        ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
          (_ : FiniteDimensional ℂ H),
          ∃ (v : Fin (n + 1) → H) (φ : H) (A : H →ₗ[ℂ] H) (hA : IsSelfAdjoint A),
            let hSym : A.IsSymmetric := (LinearMap.isSymmetric_iff_isSelfAdjoint A).2 hA
            let μ : Measure ℝ :=
              _root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric A hSym φ
            (∀ i j : Fin (n + 1),
                inner (𝕜 := ℂ) (v i) (v j) = (loewnerKernel f (y n i) (y n j) : ℂ)) ∧
              φ = v 0 ∧
                μ Set.univ = ENNReal.ofReal (loewnerKernel f 0 0) ∧
                  (∀ z : ℂ,
                      0 < z.im →
                        ∃ x : H,
                          (A - z • (LinearMap.id : H →ₗ[ℂ] H)) x = φ ∧
                            inner (𝕜 := ℂ) φ x = ∫ t, (1 / ((t : ℂ) - z)) ∂μ ∧
                              0 ≤ (inner (𝕜 := ℂ) φ x).im) ∧
                    (∀ z : ℍ, 0 ≤ (stieltjes μ z).im) :=
    fun n =>
      koranyi_finite_construct_diracMeasure_univ_eq_loewnerKernel_zero_zero
        (n := n) (f := f) (y := y n)
        (hy := hy n) (hL := hL n)
  choose H instH instI instFD v φ A hA hKor using hex
  let hSym : ∀ n : ℕ, (A n).IsSymmetric :=
    fun n => (LinearMap.isSymmetric_iff_isSelfAdjoint (A n)).2 (hA n)
  let μn : ℕ → Measure ℝ :=
    fun n => _root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric (A n) (hSym n) (φ n)
  have hμ_univ : ∀ n : ℕ, μn n Set.univ = ENNReal.ofReal (loewnerKernel f 0 0) := by
    intro n
    have hKor' := hKor n
    -- unfold the `let`-bindings in the statement of Step 56
    dsimp [hSym, μn] at hKor'
    exact hKor'.2.2.1
  have hPick : ∀ n : ℕ, ∀ z : ℍ, 0 ≤ (stieltjes (μn n) z).im := by
    intro n z
    have hKor' := hKor n
    dsimp [hSym, μn] at hKor'
    exact hKor'.2.2.2.2 z
  have hmass : ∃ M0 : ENNReal, M0 < ⊤ ∧ ∀ n : ℕ, μn n Set.univ ≤ M0 := by
    refine ⟨ENNReal.ofReal (loewnerKernel f 0 0), by simp, ?_⟩
    intro n
    simp [hμ_univ n]
  rcases hmass with ⟨M0, hM0, hμle⟩
  exact ⟨⟨μn, M0, hM0, hμle, hμ_univ, hPick⟩⟩

end

end Quantum.TraceInequality.Loewner
