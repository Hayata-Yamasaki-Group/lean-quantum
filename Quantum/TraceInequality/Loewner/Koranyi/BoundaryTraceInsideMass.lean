import Quantum.TraceInequality.Loewner.Koranyi.SignedEvalAxis

namespace Quantum.TraceInequality.Loewner

open Filter

open scoped Topology

noncomputable section

/-!
# Signed-backbone inside mass decay

This file is the foundational layer for the 38-c inside-control gate.  It only
records decay of the original signed-evaluation backbone measure on `[-1, 1]`
and the degenerate exact-zero consumers.  Inside/outside split terms live in
`BoundaryTraceProducer`.
-/

/-- Inside mass on `[-1,1]` decays along the signed-evaluation backbone. -/
structure SignedAxisInsideMassDecay {f : ℝ → ℝ}
    (pkg : StrictApproxSignedEvalPackage f) : Prop where
  tendsto_zero :
    Tendsto
      (fun n =>
        (pkg.μn (pkg.φ n) (Set.Icc (-1 : ℝ) 1)).toReal)
      atTop (𝓝 0)

/-- Exact zero inside mass is a degenerate case of inside mass decay. -/
theorem signedAxisInsideMassDecay_of_forall_measure_Icc_eq_zero
    {f : ℝ → ℝ} {pkg : StrictApproxSignedEvalPackage f}
    (hIcc : ∀ n, pkg.μn (pkg.φ n) (Set.Icc (-1 : ℝ) 1) = 0) :
    SignedAxisInsideMassDecay pkg := by
  refine ⟨?_⟩
  have hzero :
      (fun n => (pkg.μn (pkg.φ n) (Set.Icc (-1 : ℝ) 1)).toReal)
        =ᶠ[atTop] fun _n => (0 : ℝ) := by
    exact Filter.Eventually.of_forall fun n => by simp [hIcc n]
  exact tendsto_const_nhds.congr' hzero.symm

/-- Eventually zero inside mass is enough to obtain inside mass decay. -/
theorem signedAxisInsideMassDecay_of_eventually_measure_Icc_eq_zero
    {f : ℝ → ℝ} {pkg : StrictApproxSignedEvalPackage f}
    (hIcc : ∀ᶠ n in atTop,
      pkg.μn (pkg.φ n) (Set.Icc (-1 : ℝ) 1) = 0) :
    SignedAxisInsideMassDecay pkg := by
  refine ⟨?_⟩
  have hzero :
      (fun n => (pkg.μn (pkg.φ n) (Set.Icc (-1 : ℝ) 1)).toReal)
        =ᶠ[atTop] fun _n => (0 : ℝ) := by
    filter_upwards [hIcc] with n hn
    simp [hn]
  exact tendsto_const_nhds.congr' hzero.symm

end

end Loewner
end TraceInequality
end Quantum
