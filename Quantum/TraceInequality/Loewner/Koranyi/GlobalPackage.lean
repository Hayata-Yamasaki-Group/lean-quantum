import Quantum.TraceInequality.Loewner.Koranyi.GlobalPosDefBridge
import Quantum.TraceInequality.Loewner.Koranyi.GlobalPosDefBridgeAtInv
import Quantum.TraceInequality.Loewner.Koranyi.KoranyiLimitMonotone
import Quantum.TraceInequality.Loewner.Koranyi.KoranyiLimitMonotoneAnyY
import Quantum.TraceInequality.Loewner.Koranyi.EvalAtInvRewrite
import Quantum.TraceInequality.Loewner.Koranyi.EvalAtInvKernelDiffPackage
import Quantum.TraceInequality.Loewner.Koranyi.EvalAtInvKernelDiffUniformPackage


namespace Quantum.TraceInequality.Loewner

open scoped ComplexOrder
open scoped MatrixOrder
open scoped Topology
open scoped UpperHalfPlane

open Set MeasureTheory Filter

noncomputable section

/-!
Consequences of a global `PosDef` hypothesis on all finite Löwner matrices.

These results assume that every finite Löwner matrix is positive definite, which is stronger
than the positive semidefiniteness assumed by the main theorem; they are not used in the proof
of the public Löwner theorem.  `loewner_fullPackage_of_global_posDef` gives the
support-elimination package (Stieltjes differences and measure-level convergence), and the
later declarations give the Korányi-kernel limits and a weak limit on `ENNReal`.

For the public statements, see `Quantum.TraceInequality.Loewner.LoewnerTheorem`.
-/

/-- Global finite Loewner positivity gives the full support-elimination package. -/
theorem loewner_fullPackage_of_global_posDef
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef) :
    Nonempty (Loewner.StrictApproxFullPackage f) :=
  exists_subseq_supportElim_stieltjesDiff_full_of_global_loewnerMatrix_posDef_canonicalPoints
    (f := f) hL


/-- Add the canonical inverse-point finite evaluation identity to the full package. -/
theorem loewnerFullPackage_of_globalPosDef_evalInv
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef) :
    Nonempty (Loewner.FullEvalInvSubseqPackage f canonicalPoints) :=
  exists_supportElimStieltjesDiffSubseq_of_globalPosDef_evalInv_subseq
    (f := f) hL

/-- Global positivity gives the Koranyi-kernel limit package for canonical points. -/
theorem loewnerKoranyiKernelLimit_of_globalPosDef
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef) :
    Nonempty (Loewner.KoranyiLimitPackage f) :=
 exists_subseq_koranyiKernel_supportElim_with_tendsto_of_global_loewnerMatrix_posDef_canonicalPoints
    (f := f) hL

/-- Global positivity gives the canonical Koranyi-kernel limit with monotone ratio functional. -/
theorem loewnerKoranyiKernelLimitMonotone_of_globalPosDef
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef) :
    Nonempty (Loewner.KoranyiLimitMonotonePackage f) :=
  exists_koranyiKernelSupportElimSubseq_monotone_of_globalPosDef
    (f := f) hL

/-- Arbitrary admissible point families satisfy the monotone Koranyi-kernel limit package. -/
theorem loewner_koranyiKernel_limit_monotone_of_global_posDef_for_points
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef)
    (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hy : ∀ n : ℕ, pointsHyp (n := n) (y n)) :
    Nonempty (Loewner.KoranyiLimitMonotonePackage f) :=
  exists_subseq_koranyiKernel_supportElim_with_tendsto_and_monotone_of_global_loewnerMatrix_posDef
    (f := f) (hL := hL) (y := y) hy

/-- Rewrite the canonical inverse-point evaluation formula in `1 - y * t` form. -/
theorem loewnerFullPackage_of_globalPosDef_evalInv_oneSubMulSubseq
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef) :
    Nonempty (Loewner.FullOneSubMulSubseqPackage f canonicalPoints) :=
  exists_supportElimStieltjesDiffSubseq_of_globalPosDef_evalInv_oneSubMulSubseq
    (f := f) hL

/-- Add pointwise convergence of outside `1 - y * t` kernel differences to the package. -/
theorem loewnerFullPackage_of_globalPosDef_evalInv_oneSubMul_kernelLimit
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef) :
    Nonempty (Loewner.FullOneSubMulSubseqKernelLimitPackage f canonicalPoints) :=
  exists_supportElimStieltjesDiffSubseq_of_globalPosDef_evalInv_oneSubMul_kernelLimit
    (f := f) hL

/-- Upgrade outside `1 - y * t` kernel-difference convergence to uniform compact convergence. -/
theorem loewnerFullPackage_of_globalPosDef_evalInv_oneSubMul_uniformKernelLimit
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef) :
    Nonempty (Loewner.FullOneSubMulSubseqUniformKernelLimitPackage f canonicalPoints) :=
  exists_supportElimStieltjesDiffSubseq_of_globalPosDef_evalInv_oneSubMul_uniformKernelLimit
    (f := f) hL

/-- Extract the monotone Cayley ratio-functional witness from global finite positivity. -/
theorem exists_monotone_ratioFunctional_cayley_of_global_posDef
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef) :
    ∃ ν : FiniteMeasure ENNReal,
      MonotoneOn
        (fun x : ℝ => (ratioFunctional ν (Real.toNNReal (cayley x)) : ENNReal))
        (Set.Ioo (-1 : ℝ) 1) := by
  rcases loewnerKoranyiKernelLimitMonotone_of_globalPosDef (f := f) hL with
    ⟨p⟩
  exact ⟨p.ν, p.hMonotone⟩

/-- Extract the monotone Cayley ratio-functional witness for a chosen admissible point family. -/
theorem exists_monotone_ratioFunctional_cayley_of_global_posDef_for_points
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef)
    (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hy : ∀ n : ℕ, pointsHyp (n := n) (y n)) :
    ∃ ν : FiniteMeasure ENNReal,
      MonotoneOn
        (fun x : ℝ => (ratioFunctional ν (Real.toNNReal (cayley x)) : ENNReal))
        (Set.Ioo (-1 : ℝ) 1) := by
  rcases
      loewner_koranyiKernel_limit_monotone_of_global_posDef_for_points
        (f := f) hL (y := y) hy with
    ⟨p⟩
  exact ⟨p.ν, p.hMonotone⟩

end

end Quantum.TraceInequality.Loewner
