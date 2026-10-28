import Quantum.Analysis.Spectral.PositiveDefinite
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Characteristic functions are positive definite

This file proves the easy direction of Bochner's theorem.  A finite measure's characteristic
function gives a Gram matrix in `L²(μ)`: the vector belonging to `t` is the bounded wave
`ω ↦ exp (t * ω * I)`.  Its `(i,j)` inner product is exactly
`charFun μ (x j - x i)`.
-/

namespace Quantum
namespace Analysis
namespace Spectral

open Matrix MeasureTheory
open scoped ComplexConjugate ComplexOrder ENNReal InnerProductSpace NNReal

noncomputable section

private def bochnerWave (t : ℝ) (ω : ℝ) : ℂ :=
  Complex.exp (t * ω * Complex.I)

private theorem bochnerWave_aestronglyMeasurable (μ : Measure ℝ) (t : ℝ) :
    AEStronglyMeasurable (bochnerWave t) μ := by
  apply Continuous.aestronglyMeasurable
  unfold bochnerWave
  fun_prop

private theorem bochnerWave_norm (t ω : ℝ) : ‖bochnerWave t ω‖ = 1 := by
  simp [bochnerWave, Complex.norm_exp]

private theorem bochnerWave_memLp (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    MemLp (bochnerWave t) 2 μ := by
  apply MemLp.of_bound (bochnerWave_aestronglyMeasurable μ t) 1
  exact Filter.Eventually.of_forall fun ω => by simp [bochnerWave_norm]

private theorem bochnerWave_inner (s t ω : ℝ) :
    ⟪bochnerWave s ω, bochnerWave t ω⟫_ℂ =
      Complex.exp ((t - s) * ω * Complex.I) := by
  simp only [RCLike.inner_apply, bochnerWave]
  change Complex.exp (t * ω * Complex.I) *
      conj (Complex.exp (s * ω * Complex.I)) = _
  rw [← Complex.exp_conj]
  rw [← Complex.exp_add]
  congr 1
  simp
  ring

/-- The characteristic function of a finite measure on `ℝ` is positive definite.

The proof realizes the kernel matrix as the Gram matrix of the `L²(μ)` waves
`ω ↦ exp (x i * ω * I)`.  This is the integral form of the identity
`∑ i, j, conj (c i) * charFun μ (x j - x i) * c j =
  ∫ ω, ‖∑ i, c i * exp (x i * ω * I)‖ ^ 2 ∂μ`,
with nonnegativity supplied by `Matrix.posSemidef_gram`. -/
theorem isPositiveDefinite_charFun (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsPositiveDefinite (charFun μ) := by
  intro n x
  let v : Fin n → ℝ →₂[μ] ℂ := fun i =>
    (bochnerWave_memLp μ (x i)).toLp (bochnerWave (x i))
  have hgram : (Matrix.gram ℂ v).PosSemidef := Matrix.posSemidef_gram ℂ v
  convert hgram using 1
  ext i j
  simp only [Matrix.of_apply, Matrix.gram_apply]
  rw [MeasureTheory.L2.inner_def, charFun_apply_real]
  apply integral_congr_ae
  have hvi : (v i : ℝ → ℂ) =ᵐ[μ] bochnerWave (x i) := by
    dsimp [v]
    exact (bochnerWave_memLp μ (x i)).coeFn_toLp
  have hvj : (v j : ℝ → ℂ) =ᵐ[μ] bochnerWave (x j) := by
    dsimp [v]
    exact (bochnerWave_memLp μ (x j)).coeFn_toLp
  filter_upwards [hvi, hvj] with ω hi hj
  rw [hi, hj, bochnerWave_inner]
  congr 1
  push_cast
  rfl

end

end Spectral
end Analysis
end Quantum
