import Quantum.TraceInequality.Loewner.Koranyi.FiniteSpectralMeasure

import Mathlib.MeasureTheory.Function.L1Space.Integrable

namespace Quantum.TraceInequality.Loewner

open scoped BigOperators

open MeasureTheory

noncomputable section

/-!
Step 57a (utility): a shared definition of the kernel `oneSubMulKernelC` and its integrability
against the discrete measures `diracMeasure_of_isSymmetric`.

This file is placed upstream to avoid import cycles: downstream split lemmas can import this file,
and Step57 can use the integrability lemma when building its package.
-/

/-- Complex kernel `1 / (1 - x * t)` used in the eval-at-inverse rewrite. -/
def oneSubMulKernelC (x : ℝ) (t : ℝ) : ℂ :=
  1 / (1 - (x : ℂ) * (t : ℂ))

section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The `1 - x * t` kernel is integrable against the finite discrete spectral measure. -/
lemma integrable_oneSubMulKernelC_diracMeasure_of_isSymmetric
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (φ : E) (x : ℝ) :
    Integrable (fun t : ℝ => oneSubMulKernelC x t)
      (diracMeasure_of_isSymmetric (T := T) (hT := hT) φ) := by
  classical
  -- Unfold the discrete measure into a finite sum of weighted Dirac masses.
  let n : ℕ := Module.finrank ℂ E
  have hn : Module.finrank ℂ E = n := rfl
  let b : OrthonormalBasis (Fin n) ℂ E := hT.eigenvectorBasis (n := n) (hn := hn)
  let eig : Fin n → ℝ := hT.eigenvalues (n := n) (hn := hn)
  let cVec : EuclideanSpace ℂ (Fin n) := b.repr φ
  let c : Fin n → ℂ := fun i => cVec.ofLp i
  let μi : Fin n → Measure ℝ := fun i =>
    (ENNReal.ofReal (Complex.normSq (c i))) • Measure.dirac (eig i)
  have hμ :
      diracMeasure_of_isSymmetric (T := T) (hT := hT) φ = ∑ i : Fin n, μi i := by
    simp [diracMeasure_of_isSymmetric, diracMeasure_of_isSymmetricAux, μi, c, cVec, eig, b, n]
  -- Reduce to integrability against each (scaled) Dirac mass.
  have hsum :
      Integrable (fun t : ℝ => oneSubMulKernelC x t) (∑ i : Fin n, μi i) := by
    -- Rewrite the sum as a `Finset` sum over `univ`.
    have :
        Integrable (fun t : ℝ => oneSubMulKernelC x t)
          (∑ i ∈ (Finset.univ : Finset (Fin n)), μi i) := by
      refine (MeasureTheory.integrable_finset_sum_measure
        (μ := fun i : Fin n => μi i) (s := (Finset.univ : Finset (Fin n)))
        (f := fun t : ℝ => oneSubMulKernelC x t)).2 ?_
      intro i hi
      -- Integrable for a Dirac mass, then scale by a finite coefficient.
      have hdirac :
          Integrable (fun t : ℝ => oneSubMulKernelC x t) (Measure.dirac (eig i)) := by
        exact
          MeasureTheory.integrable_dirac
            (a := eig i) (f := fun t : ℝ => oneSubMulKernelC x t) (by simp)
      simpa [μi] using
        hdirac.smul_measure (c := ENNReal.ofReal (Complex.normSq (c i))) (hc := by simp)
    simpa using this
  simpa [hμ] using hsum

end

end

end Quantum.TraceInequality.Loewner
