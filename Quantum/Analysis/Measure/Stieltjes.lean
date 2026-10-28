import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter
open scoped Topology Interval NNReal ENNReal

noncomputable section

/--
The right-continuous Stieltjes representative of a monotone function agrees
with the original function Lebesgue-a.e.  This is the same discontinuity-set
argument used by Mathlib's `Monotone.ae_hasDerivAt`.
-/
theorem monotone_stieltjesFunction_ae_eq {g : ℝ → ℝ} (hg : Monotone g) :
    (fun y : ℝ => hg.stieltjesFunction y) =ᵐ[volume] g := by
  filter_upwards [hg.countable_not_continuousAt.ae_notMem volume] with y hy
  rw [Classical.not_not, hg.continuousAt_iff_leftLim_eq_rightLim] at hy
  apply le_antisymm _ (hg.le_rightLim (le_refl y))
  rw [← hy]
  exact hg.leftLim_le (le_refl y)

/--
The basic half-open Stieltjes interval evaluation supplied directly by
`StieltjesFunction.measure_Ioc`: a constant test weight integrates to the
constant times the Stieltjes increment.  This is the atomic building block of
the step-function approximation that proves the BV pairing identity in
`hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_closed`
(`IocUniformStep.lean`).
-/
theorem stieltjesFunction_integral_const_Ioc
    (G : StieltjesFunction ℝ) {a b c : ℝ} (hab : a ≤ b) :
    (∫ _y in Set.Ioc a b, c ∂G.measure) = c * (G b - G a) := by
  have hnonneg : 0 ≤ G b - G a := sub_nonneg.mpr (G.mono' hab)
  rw [setIntegral_const]
  simp [Measure.real, StieltjesFunction.measure_Ioc, hnonneg,
    ENNReal.toReal_ofReal, smul_eq_mul, mul_comm]

/--
For a globally monotone function, the absolutely continuous part of its
Stieltjes measure dominates the measure with density `deriv g` with respect to
Lebesgue measure.  This is the Mathlib translation of the nonnegative singular
part in the Stieltjes derivative decomposition.
-/
theorem stieltjes_acPart_measure_le {g : ℝ → ℝ} (hg : Monotone g) :
    volume.withDensity (fun y : ℝ => ENNReal.ofReal (deriv g y)) ≤
      hg.stieltjesFunction.measure := by
  have hae : (fun y : ℝ => ENNReal.ofReal (deriv g y)) =ᵐ[volume]
      (fun y : ℝ => hg.stieltjesFunction.measure.rnDeriv volume y) := by
    filter_upwards [hg.ae_hasDerivAt,
      Measure.rnDeriv_lt_top hg.stieltjesFunction.measure volume] with y hy hfin
    rw [hy.deriv]
    exact ENNReal.ofReal_toReal hfin.ne
  rw [MeasureTheory.withDensity_congr_ae hae]
  exact Measure.withDensity_rnDeriv_le hg.stieltjesFunction.measure volume

end

end Quantum.TraceInequality.Loewner
