import Quantum.TraceInequality.Loewner.UnitInterval.Pick.PoissonInversionCore
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Regular

/-!
# Chapter 3 Proposition 3.5 bridge skeleton

This module contains the final regularity reduction and the abstract
Fubini/approximate-identity bridge used by Proposition 3.5.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set
open Filter
open scoped Topology
open scoped NNReal
open scoped ENNReal

noncomputable section

/-! ### Proposition 3.5 final regularity target -/

/--
Regularity reduction for the last step of book Proposition 3.5.

It is enough to prove that every nonnegative continuous test function supported
in `(-1,1)` and bounded by `1` has zero integral against the raw Herglotz
measure.  The preceding Poisson-kernel work is meant to supply those test
integral identities.
-/
theorem UnitIntervalPickHerglotzUpperRawData.measure_Ioo_eq_zero_of_continuous_test_integrals_zero
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (hzero :
      ∀ (g : ℝ → ℝ), Continuous g →
        EqOn g 0 (Set.Ioo (-1 : ℝ) 1)ᶜ →
        0 ≤ g → g ≤ 1 →
        ∫ x : ℝ, g x ∂(data.measure : Measure ℝ) = 0) :
    (data.measure : Measure ℝ) (Set.Ioo (-1 : ℝ) 1) = 0 := by
  have hsup :=
    isOpen_Ioo.measure_eq_biSup_integral_continuous
      (U := Set.Ioo (-1 : ℝ) 1) (data.measure : Measure ℝ)
  rw [hsup]
  apply ENNReal.iSup_eq_zero.2
  intro g
  apply ENNReal.iSup_eq_zero.2
  intro hg_cont
  apply ENNReal.iSup_eq_zero.2
  intro hg_zero
  apply ENNReal.iSup_eq_zero.2
  intro hg_nonneg
  apply ENNReal.iSup_eq_zero.2
  intro hg_le_one
  rw [hzero g hg_cont hg_zero hg_nonneg hg_le_one]
  simp

/-! ### Proposition 3.5 Fubini / approximate-identity bridge -/

/--
The Proposition 3.5 test-integral sequence.  Its limit is identified in two ways:
the boundary Poisson estimates force it to tend to `0`, while the
approximate-identity/Fubini calculation forces it to tend to the original test
integral against the raw Herglotz measure.
-/
def UnitIntervalPickHerglotzUpperRawData.prop35TestIntegralSeq
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x : ℝ, ∫ y : ℝ,
    g x * unitIntervalHerglotzProp35TestKernel
      (1 / ((n : ℝ) + 1)) x y ∂(data.measure : Measure ℝ)

/--
A continuous test function that vanishes off `(-1,1)` has ordinary support
contained in `(-1,1)`.  The topological support may touch the endpoints, so
later estimates still need the usual cutoff/approximation argument near
`±1`.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35_continuous_test_support_subset_Ioo
    (g : ℝ → ℝ)
    (hg_zero : EqOn g 0 (Set.Ioo (-1 : ℝ) 1)ᶜ) :
    Function.support g ⊆ Set.Ioo (-1 : ℝ) 1 := by
  intro x hx
  by_contra hxI
  exact hx (hg_zero hxI)

/-- Such a test function has compact support, contained in `[-1,1]`. -/
theorem UnitIntervalPickHerglotzUpperRawData.prop35_continuous_test_hasCompactSupport
    (g : ℝ → ℝ)
    (hg_zero : EqOn g 0 (Set.Ioo (-1 : ℝ) 1)ᶜ) :
    HasCompactSupport g := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc ?_
  intro x hx
  have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 :=
    UnitIntervalPickHerglotzUpperRawData.prop35_continuous_test_support_subset_Ioo
      g hg_zero hx
  exact ⟨le_of_lt hxI.1, le_of_lt hxI.2⟩

/--
Fubini swap for the Proposition 3.5 test kernel, with the required product
integrability kept explicit.  For the compactly supported test functions above
it is discharged by
`UnitIntervalPickHerglotzUpperRawData.prop35_testKernel_integrable_prod`
(`MeasureRecoveryDischarge.lean`).
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35_fubini_testKernel
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (ε : ℝ)
    (hInt : Integrable
      (Function.uncurry fun x y : ℝ =>
        g x * unitIntervalHerglotzProp35TestKernel ε x y)
      ((volume : Measure ℝ).prod (data.measure : Measure ℝ))) :
    (∫ x : ℝ, ∫ y : ℝ,
        g x * unitIntervalHerglotzProp35TestKernel ε x y
          ∂(data.measure : Measure ℝ)) =
      ∫ y : ℝ, (∫ x : ℝ,
        g x * unitIntervalHerglotzProp35TestKernel ε x y)
          ∂(data.measure : Measure ℝ) := by
  exact integral_integral_swap (μ := (volume : Measure ℝ))
    (ν := (data.measure : Measure ℝ)) hInt

/--
Limit-uniqueness form of the approximate-identity bridge: once the same
test-integral sequence is shown to tend both to `0` and to the original test
integral, the original test integral is zero.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35_testIntegral_eq_zero_of_tendsto_zero_and_approx
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ)
    (hzero : Tendsto
      (fun n : ℕ => data.prop35TestIntegralSeq g n) atTop (𝓝 0))
    (happrox : Tendsto
      (fun n : ℕ => data.prop35TestIntegralSeq g n) atTop
        (𝓝 (∫ y : ℝ, g y ∂(data.measure : Measure ℝ)))) :
    (∫ y : ℝ, g y ∂(data.measure : Measure ℝ)) = 0 := by
  exact tendsto_nhds_unique happrox hzero

end

end Quantum.TraceInequality.Loewner
