import Quantum.TraceInequality.Loewner.Koranyi.GlobalPosDefBridge
import Quantum.TraceInequality.Loewner.Koranyi.GlobalPosDefInstantiationAtInv


namespace Quantum.TraceInequality.Loewner

open scoped ComplexOrder
open scoped MatrixOrder
open scoped Topology
open scoped UpperHalfPlane

open Set MeasureTheory Filter

noncomputable section

/-!
Step 60' (bridge): global `PosDef` hypothesis instantiated at the explicit canonical points, in the
strengthened Step 58' form (including the finite-point evaluation identity at `1 / y_i`).
-/

/-- Canonical global positivity gives the support-elimination package with inverse evaluation. -/
theorem exists_supportElimStieltjesDiffSubseq_of_globalPosDef_evalInv
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef) :
    Nonempty (Loewner.FullEvalInvPackage f canonicalPoints) := by
  let y : ∀ n : ℕ, Fin (n + 1) → ℝ := fun n => canonicalPoints n
  have hy : ∀ n : ℕ, pointsHyp (n := n) (y n) := by
    intro n
    simpa [y] using pointsHyp_canonicalPoints n
  exact
    exists_supportElimStieltjesDiffSubseq_of_pointsGlobalPosDef_evalInv
      (f := f) hL (y := y) hy

/-!
Step 60'' (convenience): restate the finite-point evaluation identity along the extracted
subsequence `φ`.

The Step 60' theorem provides evaluation at `1 / canonicalPoints n i` for the original sequence
`μn n`. Downstream steps only see the subsequence `μn (φ n)`, so we also expose the corresponding
statement with indices specialized to `φ n`.
-/

/-- Restate the canonical inverse-evaluation formula along the extracted subsequence. -/
theorem exists_supportElimStieltjesDiffSubseq_of_globalPosDef_evalInv_subseq
    (f : ℝ → ℝ)
    (hL :
      ∀ n : ℕ,
        ∀ y : Fin (n + 1) → ℝ,
          pointsHyp (n := n) y → (loewnerMatrix (n := n) f y).PosDef) :
    Nonempty (Loewner.FullEvalInvSubseqPackage f canonicalPoints) := by
  rcases
      exists_supportElimStieltjesDiffSubseq_of_globalPosDef_evalInv
        (f := f) hL with
    ⟨p⟩
  refine ⟨⟨p.toStrictApproxFullPackage, ?_⟩⟩
  intro n i hi
  simpa using p.hEvalInv (p.φ n) i hi

end

end Quantum.TraceInequality.Loewner
