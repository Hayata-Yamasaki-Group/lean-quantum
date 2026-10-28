import Quantum.TraceInequality.Loewner.Koranyi.MeasureSequenceAtInv
import Quantum.TraceInequality.Loewner.Koranyi.SupportElimSubseq


namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter Set

open scoped Topology
open scoped UpperHalfPlane
open scoped ComplexOrder
open scoped MatrixOrder

noncomputable section

/-!
Step 58' (bridge): same as Step 58, but starting from the strengthened Step 57' package that also
retains a finite-point evaluation identity for `f` at the points `y n i`.

This is useful when later comparing boundary values / real-point evaluations against the limiting
Pick function.
-/

/-- Variant of the support-elimination package that additionally retains finite-point evaluation
identities for `f` at the interpolation points, for later comparison of boundary and real-point
values against the limiting Pick function. [simon2019] -/
theorem exists_subseq_supportElim_stieltjesDiff_full_of_loewnerMatrix_posDef_with_eval_at_inv
    (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hy : ∀ n : ℕ, pointsHyp (n := n) (y n))
    (hL : ∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef) :
    Nonempty (Loewner.FullEvalInvPackage f y) := by
  classical
  rcases exists_measureSeq_of_loewnerMatrix_posDef_with_eval_at_inv (f := f) (y := y) hy hL with
    ⟨p⟩
  rcases
      exists_subseq_supportElim_stieltjesDiff_full_with_tendsto
        (μn := p.μn) (M0 := p.M0) p.hM0 p.hμle with
    ⟨φ, F, ν, hφ, hconvSt, hconvDiff, hst, hdiff, hFpick, ht, hKoranyi⟩
  exact
    ⟨⟨⟨⟨p.μn, p.M0, p.hM0, p.hμle, p.hMass, φ, hφ, F, ν, hconvSt, hFpick, ht,
          hKoranyi⟩,
        hconvDiff, hst, hdiff⟩,
      p.hEvalInv⟩⟩

/-- Support-elimination package with the finite-point evaluation identity rewritten into the
`1/(1 - y t)` (one-minus-mul) kernel form. [simon2019] -/
theorem exists_supportElimStieltjesDiffSubseq_of_posDef_evalInv_oneSubMul
    (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hy : ∀ n : ℕ, pointsHyp (n := n) (y n))
    (hL : ∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef) :
    Nonempty (Loewner.FullOneSubMulPackage f y) := by
  classical
  rcases
      exists_measureSeq_of_loewnerMatrix_posDef_with_eval_at_inv_one_sub_mul
        (f := f) (y := y) hy hL with
    ⟨p⟩
  rcases
      exists_subseq_supportElim_stieltjesDiff_full_with_tendsto
        (μn := p.μn) (M0 := p.M0) p.hM0 p.hμle with
    ⟨φ, F, ν, hφ, hconvSt, hconvDiff, hst, hdiff, hFpick, ht, hKoranyi⟩
  exact
    ⟨⟨⟨⟨p.μn, p.M0, p.hM0, p.hμle, p.hMass, φ, hφ, F, ν, hconvSt, hFpick, ht,
          hKoranyi⟩,
        hconvDiff, hst, hdiff⟩,
      p.hOneSubMul⟩⟩

/-- As the one-minus-mul support-elimination package, additionally recording integrability of the
`1/(1 - y t)` kernel against each measure. [simon2019] -/
theorem exists_supportElimStieltjesDiffSubseq_of_posDef_evalInv_oneSubMul_kernelIntegrable
    (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hy : ∀ n : ℕ, pointsHyp (n := n) (y n))
    (hL : ∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef) :
    Nonempty (Loewner.FullOneSubMulKernelIntegrablePackage f y) := by
  classical
  rcases
      exists_measureSeq_of_loewnerMatrix_posDef_with_eval_at_inv_one_sub_mul_and_kernelIntegrable
        (f := f) (y := y) hy hL with
    ⟨p⟩
  rcases
      exists_subseq_supportElim_stieltjesDiff_full_with_tendsto
        (μn := p.μn) (M0 := p.M0) p.hM0 p.hμle with
    ⟨φ, F, ν, hφ, hconvSt, hconvDiff, hst, hdiff, hFpick, ht, hKoranyi⟩
  have hIntSubseq :
      ∀ n : ℕ, ∀ x : ℝ, Integrable (fun t : ℝ => oneSubMulKernelC x t) (p.μn (φ n)) :=
    fun n x => p.hKernelIntegrable (φ n) x
  exact
    ⟨⟨⟨⟨⟨p.μn, p.M0, p.hM0, p.hμle, p.hMass, φ, hφ, F, ν, hconvSt, hFpick, ht,
            hKoranyi⟩,
          hconvDiff, hst, hdiff⟩,
        p.hOneSubMul⟩,
      hIntSubseq⟩⟩

end

end Quantum.TraceInequality.Loewner
