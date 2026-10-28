import Quantum.TraceInequality.Loewner.Koranyi.BoundaryTrace
import Quantum.TraceInequality.Loewner.Koranyi.LoewnerKernelAxisTendsto

namespace Quantum.TraceInequality.Loewner

open Set MeasureTheory Filter

open scoped ComplexOrder
open scoped MatrixOrder
open scoped Topology
open scoped UpperHalfPlane

noncomputable section

/-!
Signed evaluation axis API for the Cayley/Koranyi boundary trace step.

This file records the branch of `signedPoints` approaching a fixed nonzero
point `x`, together with the finite-dimensional evaluation identity from
`StrictApproxSignedEvalPackage`.  It is an adapter around the
`LoewnerKernelAxisTendsto` utility.
-/

/-- Data for consuming the signed-points evaluation identity along an axis
approaching a fixed nonzero point. -/
structure SignedEvalAxis {f : ℝ → ℝ}
    (pkg : StrictApproxSignedEvalPackage f) (x : ℝ) where
  i : ∀ n : ℕ, Fin (pkg.φ n + 1)
  hi0 : ∀ᶠ n in atTop, i n ≠ 0
  tendsto_signed :
    Tendsto (fun n => signedPoints (pkg.φ n) (i n)) atTop (𝓝 x)
  tendsto_kernel :
    Tendsto
      (fun n => loewnerKernel f (signedPoints (pkg.φ n) (i n)) 0)
      atTop (𝓝 (loewnerKernel f x 0))
  tendsto_ofReal_kernel :
    Tendsto
      (fun n => ENNReal.ofReal (loewnerKernel f (signedPoints (pkg.φ n) (i n)) 0))
      atTop (𝓝 (ENNReal.ofReal (loewnerKernel f x 0)))
  evalEventually :
    ∀ᶠ n in atTop,
      (loewnerKernel f (signedPoints (pkg.φ n) (i n)) 0 : ℂ) =
        ∫ t, (1 / (1 - (signedPoints (pkg.φ n) (i n) : ℂ) * (t : ℂ)))
          ∂(pkg.μn (pkg.φ n))

/-- Build the signed evaluation axis from a signed-evaluation package. -/
noncomputable def signedEvalAxis_of_strictApproxSignedEvalPackage
    {f : ℝ → ℝ} (pkg : StrictApproxSignedEvalPackage f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0)
    (hf : ContinuousAt f x) :
    SignedEvalAxis pkg x := by
  classical
  let hex :=
      _root_.Quantum.TraceInequality.Loewner.exists_indexSeq_axis_tendsto_of_continuousAt
        (φ := pkg.φ) pkg.hφ (f := f) (x := x) hx hx0 hf
  let i := Classical.choose hex
  let hspec := Classical.choose_spec hex
  let hi0 := hspec.1
  let hxT := hspec.2.1
  let hKT := hspec.2.2
  have hENN :
      Tendsto
        (fun n => ENNReal.ofReal (loewnerKernel f (signedPoints (pkg.φ n) (i n)) 0))
        atTop (𝓝 (ENNReal.ofReal (loewnerKernel f x 0))) :=
    _root_.Quantum.TraceInequality.Loewner.tendsto_ofReal_loewnerKernel_zero_of_continuousAt
      (f := f) (xSeq := fun n => signedPoints (pkg.φ n) (i n)) (x := x) hx0 hxT hf
  have hEval :
      ∀ᶠ n in atTop,
        (loewnerKernel f (signedPoints (pkg.φ n) (i n)) 0 : ℂ) =
          ∫ t, (1 / (1 - (signedPoints (pkg.φ n) (i n) : ℂ) * (t : ℂ)))
            ∂(pkg.μn (pkg.φ n)) := by
    filter_upwards [hi0] with n hn
    exact pkg.hEvalSigned n (i n) hn
  exact
    { i := i
      hi0 := hi0
      tendsto_signed := hxT
      tendsto_kernel := hKT
      tendsto_ofReal_kernel := hENN
      evalEventually := hEval }


end

end Loewner
end TraceInequality
end Quantum
