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
Step 58 (bridge): from `PosDef` hypotheses on all finite-point Löwner matrices, obtain the
support-elimination subsequence package (Step 54).

This instantiates Step 54 with the discrete measures coming from the Korányi construction,
using Step 56/57 to discharge the uniform mass bound.
-/

/-- From positive-definiteness of all finite-point Löwner matrices, construct the Korányi discrete
measures and extract the support-elimination subsequence package: uniform Stieltjes convergence on
the compacts `KmHT m`, pointwise convergence, and the outside-integral representation. [simon2019]
-/
theorem exists_subseq_supportElim_stieltjesDiff_full_of_loewnerMatrix_posDef
    (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hy : ∀ n : ℕ, pointsHyp (n := n) (y n))
    (hL : ∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef) :
    Nonempty (Loewner.StrictApproxFullPackage f) := by
  classical
  -- Build the discrete measures `μn` from the finite Korányi construction, with a uniform mass
  -- bound.
  rcases exists_measureSeq_of_loewnerMatrix_posDef (f := f) (y := y) hy hL with
    ⟨p⟩
  -- Apply the full support-elimination Stieltjes-difference package.
  rcases
      exists_subseq_supportElim_stieltjesDiff_full_with_tendsto
        (μn := p.μn) (M0 := p.M0) p.hM0 p.hμle with
    ⟨φ, F, ν, hφ, hconvSt, hconvDiff, hst, hdiff, hFpick, ht, hKoranyi⟩
  exact
    ⟨⟨⟨p.μn, p.M0, p.hM0, p.hμle, p.hMass, φ, hφ, F, ν, hconvSt, hFpick, ht,
        hKoranyi⟩,
      hconvDiff, hst, hdiff⟩⟩

end

end Quantum.TraceInequality.Loewner
