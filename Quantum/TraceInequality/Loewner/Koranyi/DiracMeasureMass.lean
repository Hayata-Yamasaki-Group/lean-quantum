import Quantum.TraceInequality.Loewner.Koranyi.FiniteSpectralMeasure

import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace Quantum.TraceInequality.Loewner

open MeasureTheory

noncomputable section

section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-!
Step 25 (utility): total mass of the discrete measure from Step 3.

The measure `diracMeasure_of_isSymmetric T hT φ` is a finite sum of Dirac masses at eigenvalues,
with weights given by squared moduli of the coordinates of `φ` in an orthonormal eigenbasis.
Thus its total mass is exactly `‖φ‖^2`.
-/

/--
The spectral Dirac measure of a symmetric finite-dimensional operator has total
mass `ENNReal.ofReal ‖φ‖^2`.
-/
theorem diracMeasure_of_isSymmetric_univ
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (φ : E) :
    diracMeasure_of_isSymmetric (T := T) (hT := hT) φ Set.univ =
      ENNReal.ofReal (‖φ‖ ^ 2) := by
  classical
  let n : ℕ := Module.finrank ℂ E
  have hn : Module.finrank ℂ E = n := rfl
  let b : OrthonormalBasis (Fin n) ℂ E := hT.eigenvectorBasis (n := n) (hn := hn)
  let cVec : EuclideanSpace ℂ (Fin n) := b.repr φ
  let c : Fin n → ℂ := fun i => cVec.ofLp i
  let μi : Fin n → Measure ℝ := fun i =>
    (ENNReal.ofReal (Complex.normSq (c i))) • Measure.dirac (hT.eigenvalues (n := n) (hn := hn) i)
  let μ : Measure ℝ := ∑ i : Fin n, μi i
  have hμ : μ = diracMeasure_of_isSymmetric (T := T) (hT := hT) φ := by
    simp [diracMeasure_of_isSymmetric, diracMeasure_of_isSymmetricAux, μ, μi, c, cVec, b, n]
  -- Compute the mass: each Dirac atom contributes its weight.
  have hμ_univ :
      μ Set.univ = ∑ i : Fin n, ENNReal.ofReal (Complex.normSq (c i)) := by
    simp [μ, μi]
  -- Convert the sum of `Complex.normSq` to `‖cVec‖^2`, then to `‖φ‖^2` by Parseval.
  have hsum_normsq :
      (∑ i : Fin n, Complex.normSq (c i)) = ‖cVec‖ ^ 2 := by
    -- `EuclideanSpace` is `PiLp 2`, so the squared norm is the sum of squared norms of entries.
    have hnorm_sq :
        ‖cVec‖ ^ 2 = ∑ i : Fin n, ‖cVec.ofLp i‖ ^ 2 := by
      simpa [EuclideanSpace] using
        (PiLp.norm_sq_eq_of_L2
          (β := fun _ : Fin n => ℂ)
          (x := (cVec : PiLp 2 fun _ : Fin n => ℂ)))
    -- Replace `‖cVec.ofLp i‖^2` by `Complex.normSq (c i)`.
    have hterm :
        (∑ i : Fin n, Complex.normSq (c i)) = ∑ i : Fin n, ‖cVec.ofLp i‖ ^ 2 := by
      simp [c, Complex.normSq_eq_norm_sq]
    -- Combine.
    simpa [hterm] using hnorm_sq.symm
  have hnorm_repr : ‖cVec‖ = ‖φ‖ := by
    simp [cVec]
  -- Put everything together in `ENNReal`.
  calc
    diracMeasure_of_isSymmetric (T := T) (hT := hT) φ Set.univ
        = μ Set.univ := by simp [hμ]
    _ = ∑ i : Fin n, ENNReal.ofReal (Complex.normSq (c i)) := hμ_univ
    _ = ENNReal.ofReal (∑ i : Fin n, Complex.normSq (c i)) := by
          have hnonneg :
              ∀ i : Fin n, i ∈ (Finset.univ : Finset (Fin n)) →
                0 ≤ Complex.normSq (c i) := by
            intro i _hi
            exact Complex.normSq_nonneg (c i)
          simpa using
            (ENNReal.ofReal_sum_of_nonneg
              (s := (Finset.univ : Finset (Fin n)))
              (f := fun i => Complex.normSq (c i)) hnonneg).symm
    _ = ENNReal.ofReal (‖cVec‖ ^ 2) := by simp [hsum_normsq]
    _ = ENNReal.ofReal (‖φ‖ ^ 2) := by simp [hnorm_repr]

end

end

end Quantum.TraceInequality.Loewner
