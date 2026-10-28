import Quantum.TraceInequality.Loewner.Koranyi.FinitePickData
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

namespace Quantum.TraceInequality.Loewner

open MeasureTheory

noncomputable section

open scoped BigOperators
open scoped ComplexOrder
open scoped MatrixOrder
open scoped UpperHalfPlane

/-! Step 5 (finite case): package the Stieltjes transform as a Pick function on the upper
half-plane. -/

/-- The Stieltjes transform of a measure `μ`, `z ↦ ∫ 1/(t - z) dμ(t)`, as a function on the upper
half-plane. -/
def stieltjes (μ : Measure ℝ) (z : ℍ) : ℂ :=
  ∫ t, (1 / ((t : ℂ) - (z : ℂ))) ∂μ

/-- Given Pick data (a self-adjoint resolvent representation with nonnegative imaginary inner
product), the Stieltjes transform has nonnegative imaginary part on the upper half-plane, i.e. it
is a Pick/Nevanlinna function. [simon2019] -/
theorem stieltjes_im_nonneg_of_pick_data {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {A : H →ₗ[ℂ] H} {φ : H} {μ : Measure ℝ}
    (h :
      ∀ z : ℂ,
        0 < z.im →
          ∃ x : H,
            (A - z • (LinearMap.id : H →ₗ[ℂ] H)) x = φ ∧
              inner (𝕜 := ℂ) φ x = ∫ t, (1 / ((t : ℂ) - z)) ∂μ ∧
                0 ≤ (inner (𝕜 := ℂ) φ x).im) :
    ∀ z : ℍ, 0 ≤ (stieltjes μ z).im := by
  intro z
  have hz : 0 < (z : ℂ).im := by
    simpa using z.coe_im_pos
  rcases h (z : ℂ) hz with ⟨x, _hsol, hx, him⟩
  have hst : stieltjes μ z = inner (𝕜 := ℂ) φ x := by
    simpa [stieltjes] using hx.symm
  simpa [hst] using him


end

end Quantum.TraceInequality.Loewner
