import Quantum.TraceInequality.Loewner.Koranyi.MeasureSequence
import Quantum.TraceInequality.Loewner.Koranyi.SupportElimSubseq


namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter Set

open scoped Topology
open scoped UpperHalfPlane
open scoped ComplexOrder
open scoped MatrixOrder

noncomputable section

/-!
Step 59 (bridge): a streamlined consequence of Step 57 + Step 39.

From `PosDef` hypotheses on all finite-point Löwner matrices, we obtain a support-elimination
subsequence package (uniform convergence on `KmHT m`, Pick property, and measure-level convergence
on `ENNReal`), as well as convergence of Korányi-kernel `lintegral`s.
-/

/-- Streamlined support-elimination package: from positive-definiteness of all finite-point Löwner
matrices, obtain uniform Stieltjes convergence on the compacts `KmHT m`, the Pick property,
measure-level convergence on `ENNReal`, and convergence of the Korányi-kernel integrals. [simon2019]
-/
theorem exists_subseq_koranyiKernel_supportElim_with_tendsto_of_loewnerMatrix_posDef
    (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hy : ∀ n : ℕ, pointsHyp (n := n) (y n))
    (hL : ∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef) :
    Nonempty (Loewner.KoranyiLimitPackage f) := by
  classical
  rcases exists_measureSeq_of_loewnerMatrix_posDef (f := f) (y := y) hy hL with
    ⟨p⟩
  rcases
      exists_subseq_tendsto_lintegral_koranyiKernel_supportElim_with_tendsto (μn := p.μn)
        (M0 := p.M0) p.hM0 p.hμle with
    ⟨φ, F, ν, hφ, hconvF, hFpick, ht, hKoranyi⟩
  exact
    ⟨⟨p.μn, p.M0, p.hM0, p.hμle, p.hMass, φ, hφ, F, ν, hconvF, hFpick, ht,
      hKoranyi⟩⟩

end

end Quantum.TraceInequality.Loewner
