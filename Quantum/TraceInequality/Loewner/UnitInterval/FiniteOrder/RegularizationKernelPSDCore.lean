import Quantum.Analysis.Calculus.EquicontinuousFamily
import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.ClippedComparison
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-!
# Chapter 20 Hiai regularization kernel positivity

This file contains the shifted-node integral formulas and the regularized
Löwner-kernel positive semidefiniteness core for Hiai regularization.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped Interval
open scoped ComplexOrder
open scoped MatrixOrder
open scoped NNReal
open scoped ENNReal
open scoped Convolution

noncomputable section

/--
If `x` lies in the shrunken interval and the mollifier variable lies in
`[-1,1]`, then the sampled point remains in the original normalized interval.
-/
theorem hiaiRegularization_shift_mem_Ioo
    {ε x t : ℝ} (hε : 0 ≤ ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    x - ε * t ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hmul_le : ε * t ≤ ε := by
    simpa using mul_le_mul_of_nonneg_left ht.2 hε
  have hneg_le : -ε ≤ ε * t := by
    have h := mul_le_mul_of_nonneg_left ht.1 hε
    simpa using h
  have hx_left : -1 + ε < x := hx.1
  have hx_right : x < 1 - ε := hx.2
  constructor
  · linarith
  · linarith

/-- Shifted finite nodes for the regularized kernel remain in the original domain. -/
theorem hiaiRegularization_shiftedNodes_mem_Ioo
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    ∀ i, x i - ε * t ∈ Set.Ioo (-1 : ℝ) 1 := by
  intro i
  exact hiaiRegularization_shift_mem_Ioo hε (hx i) ht

/-- Subtracting the same regularization shift preserves injectivity of nodes. -/
theorem hiaiRegularization_shiftedNodes_injective
    {ε t : ℝ} {n : ℕ} {x : Fin n → ℝ}
    (hinj : Function.Injective x) :
    Function.Injective (fun i : Fin n => x i - ε * t) := by
  intro i j hij
  apply hinj
  linarith

/--
For each mollifier parameter, public finite Löwner positivity applies to the
shifted node family used by the regularized kernel.
-/
theorem loewnerKernel_shifted_posSemidef_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hinj : Function.Injective x)
    {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (Matrix.of fun i j : Fin n =>
      (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)).PosSemidef :=
  hpos.posSemidef n (fun i : Fin n => x i - ε * t)
    (hiaiRegularization_shiftedNodes_mem_Ioo hε hx ht)
    (hiaiRegularization_shiftedNodes_injective hinj)

/--
Off the diagonal, the Löwner kernel of the regularization is the regularized
off-diagonal Löwner kernel.  The integrability assumptions isolate the only
analytic input needed for the interval-integral linearity step.
-/
theorem hiaiRegularization_loewnerKernel_offdiag_integral_formula
    {φ f : ℝ → ℝ} {ε x y : ℝ} (hxy : x ≠ y)
    (hxint :
      IntervalIntegrable (fun t : ℝ => φ t * f (x - ε * t))
        volume (-1 : ℝ) 1)
    (hyint :
      IntervalIntegrable (fun t : ℝ => φ t * f (y - ε * t))
        volume (-1 : ℝ) 1) :
    loewnerKernel (hiaiRegularization φ ε f) x y =
      ∫ t in (-1 : ℝ)..1,
        φ t * loewnerKernel f (x - ε * t) (y - ε * t) := by
  rw [loewnerKernel_eq_div
    (f := hiaiRegularization φ ε f) (x := x) (y := y) hxy]
  simp only [hiaiRegularization]
  rw [← intervalIntegral.integral_sub hxint hyint]
  rw [← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr ?_
  intro t _ht
  have hshift : x - ε * t ≠ y - ε * t := by
    intro h
    apply hxy
    linarith
  change
    (φ t * f (x - ε * t) - φ t * f (y - ε * t)) / (x - y) =
      φ t * loewnerKernel f (x - ε * t) (y - ε * t)
  rw [loewnerKernel_eq_div (f := f) (x := x - ε * t) (y := y - ε * t) hshift]
  have hden : x - y ≠ 0 := sub_ne_zero.mpr hxy
  field_simp [hden]
  ring

/--
Continuity of `f` on the unit interval supplies the value integrability needed
for the Hiai regularization integral, as long as the regularized point stays in
the shrunken interval.
-/
theorem hiaiRegularization_value_intervalIntegrable_of_continuousOn
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 ≤ ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hf : ContinuousOn f (Set.Ioo (-1 : ℝ) 1)) :
    IntervalIntegrable (fun t : ℝ => φ t * f (x - ε * t))
      volume (-1 : ℝ) 1 := by
  have hφcont : ContinuousOn φ [[(-1 : ℝ), 1]] :=
    hφ.smooth.continuous.continuousOn
  have hshift : ContinuousOn (fun t : ℝ => x - ε * t) [[(-1 : ℝ), 1]] := by
    fun_prop
  have hmaps : Set.MapsTo (fun t : ℝ => x - ε * t) [[(-1 : ℝ), 1]]
      (Set.Ioo (-1 : ℝ) 1) := by
    intro t ht
    have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    exact hiaiRegularization_shift_mem_Ioo hε hx htIcc
  have hfcomp : ContinuousOn (fun t : ℝ => f (x - ε * t)) [[(-1 : ℝ), 1]] := by
    simpa [Function.comp_def] using hf.comp hshift hmaps
  exact (hφcont.mul hfcomp).intervalIntegrable

/--
Public Löwner positivity already contains differentiability on `(-1,1)`, hence
continuity, which supplies the value integrability needed by the off-diagonal
regularization formula.
-/
theorem hiaiRegularization_value_intervalIntegrable_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 ≤ ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    IntervalIntegrable (fun t : ℝ => φ t * f (x - ε * t))
      volume (-1 : ℝ) 1 :=
  hiaiRegularization_value_intervalIntegrable_of_continuousOn
    (φ := φ) (f := f) hφ hε hx hpos.differentiable.continuousOn

/--
Off the diagonal, the regularized kernel formula has no extra analytic
hypotheses beyond the public continuity bundled in `LoewnerPosOnUnitInterval`.
-/
theorem
    hiaiRegularization_loewnerKernel_offdiag_integral_formula_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x y : ℝ} (hε : 0 ≤ ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hy : y ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) (hxy : x ≠ y) :
    loewnerKernel (hiaiRegularization φ ε f) x y =
      ∫ t in (-1 : ℝ)..1,
        φ t * loewnerKernel f (x - ε * t) (y - ε * t) :=
  hiaiRegularization_loewnerKernel_offdiag_integral_formula
    (φ := φ) (f := f) (ε := ε) (x := x) (y := y) hxy
    (hiaiRegularization_value_intervalIntegrable_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hε hx hpos)
    (hiaiRegularization_value_intervalIntegrable_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hε hy hpos)

/--
Off-diagonal regularized kernel entries are integrable over the Hiai
regularization carrier once the two regularized value functions are interval
integrable.  The denominator is the fixed nonzero scalar `x - y`.
-/
theorem hiaiRegularization_loewnerKernel_offdiag_uIoc_integrable
    {φ f : ℝ → ℝ} {ε x y : ℝ} (hxy : x ≠ y)
    (hxint :
      IntervalIntegrable (fun t : ℝ => φ t * f (x - ε * t))
        volume (-1 : ℝ) 1)
    (hyint :
      IntervalIntegrable (fun t : ℝ => φ t * f (y - ε * t))
        volume (-1 : ℝ) 1) :
    Integrable
      (fun t : ℝ => (φ t : ℂ) *
        (loewnerKernel f (x - ε * t) (y - ε * t) : ℂ))
      (volume.restrict (Ι (-1 : ℝ) 1)) := by
  have hquot :
      IntervalIntegrable
        (fun t : ℝ =>
          (φ t * f (x - ε * t) - φ t * f (y - ε * t)) / (x - y))
        volume (-1 : ℝ) 1 :=
    (hxint.sub hyint).div_const (x - y)
  have hreal :
      IntervalIntegrable
        (fun t : ℝ => φ t * loewnerKernel f (x - ε * t) (y - ε * t))
        volume (-1 : ℝ) 1 := by
    refine hquot.congr ?_
    intro t _ht
    have hshift : x - ε * t ≠ y - ε * t := by
      intro h
      apply hxy
      linarith
    change
      (φ t * f (x - ε * t) - φ t * f (y - ε * t)) / (x - y) =
        φ t * loewnerKernel f (x - ε * t) (y - ε * t)
    rw [loewnerKernel_eq_div (f := f) (x := x - ε * t) (y := y - ε * t) hshift]
    have hden : x - y ≠ 0 := sub_ne_zero.mpr hxy
    field_simp [hden]
    ring
  have hreal_restrict :
      Integrable
        (fun t : ℝ => φ t * loewnerKernel f (x - ε * t) (y - ε * t))
        (volume.restrict (Ι (-1 : ℝ) 1)) :=
    hreal.def'
  have hcomplex :
      Integrable
        (fun t : ℝ =>
          ((φ t * loewnerKernel f (x - ε * t) (y - ε * t) : ℝ) : ℂ))
        (volume.restrict (Ι (-1 : ℝ) 1)) :=
    hreal_restrict.ofReal
  simpa using hcomplex

/--
Public Löwner positivity supplies the value integrability needed for each
off-diagonal regularized kernel entry.
-/
theorem
    hiaiRegularization_loewnerKernel_offdiag_uIoc_integrable_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x y : ℝ} (hε : 0 ≤ ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hy : y ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) (hxy : x ≠ y) :
    Integrable
      (fun t : ℝ => (φ t : ℂ) *
        (loewnerKernel f (x - ε * t) (y - ε * t) : ℂ))
      (volume.restrict (Ι (-1 : ℝ) 1)) :=
  hiaiRegularization_loewnerKernel_offdiag_uIoc_integrable
    (φ := φ) (f := f) (ε := ε) hxy
    (hiaiRegularization_value_intervalIntegrable_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hε hx hpos)
    (hiaiRegularization_value_intervalIntegrable_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hε hy hpos)

/--
The public off-diagonal regularization formula in the complex `uIoc` form used
by the finite quadratic-form PSD transport.
-/
theorem
    hiaiRegularization_loewnerKernel_offdiag_uIoc_formula_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x y : ℝ} (hε : 0 ≤ ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hy : y ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) (hxy : x ≠ y) :
    (loewnerKernel (hiaiRegularization φ ε f) x y : ℂ) =
      ∫ t : ℝ, (φ t : ℂ) *
        (loewnerKernel f (x - ε * t) (y - ε * t) : ℂ)
        ∂(volume.restrict (Ι (-1 : ℝ) 1)) := by
  have hreal :=
    hiaiRegularization_loewnerKernel_offdiag_integral_formula_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hε hx hy hpos hxy
  calc
    (loewnerKernel (hiaiRegularization φ ε f) x y : ℂ)
        = ∫ t in (-1 : ℝ)..1,
            ((φ t * loewnerKernel f (x - ε * t) (y - ε * t) : ℝ) : ℂ) := by
          rw [intervalIntegral.integral_ofReal]
          exact_mod_cast hreal
    _ = ∫ t : ℝ, (φ t : ℂ) *
          (loewnerKernel f (x - ε * t) (y - ε * t) : ℂ)
          ∂(volume.restrict (Ι (-1 : ℝ) 1)) := by
          simp only [Complex.ofReal_mul]
          rw [intervalIntegral.intervalIntegral_eq_integral_uIoc
            (fun t : ℝ =>
              ((φ t * loewnerKernel f (x - ε * t) (y - ε * t)) : ℂ))
            (-1) 1 volume]
          simp

/--
Diagonal entry formula for the Löwner kernel of the Hiai regularization, under
the dominated-derivative hypotheses from
`hiaiRegularization_hasDerivAt_of_dominated_deriv`.
-/
theorem hiaiRegularization_loewnerKernel_diag_integral_formula_of_dominated_deriv
    {φ f : ℝ → ℝ} {ε x : ℝ} {s : Set ℝ} {bound : ℝ → ℝ}
    (hs : s ∈ 𝓝 x)
    (hF_meas : ∀ᶠ z in 𝓝 x,
      AEStronglyMeasurable (fun t : ℝ => φ t * f (z - ε * t))
        (volume.restrict (Ι (-1 : ℝ) 1)))
    (hF_int : Integrable (fun t : ℝ => φ t * f (x - ε * t))
        (volume.restrict (Ι (-1 : ℝ) 1)))
    (hF'_meas : AEStronglyMeasurable (fun t : ℝ => φ t * deriv f (x - ε * t))
        (volume.restrict (Ι (-1 : ℝ) 1)))
    (h_bound : ∀ᵐ t ∂volume.restrict (Ι (-1 : ℝ) 1), ∀ z ∈ s,
      ‖φ t * deriv f (z - ε * t)‖ ≤ bound t)
    (h_bound_int : Integrable bound (volume.restrict (Ι (-1 : ℝ) 1)))
    (h_diff : ∀ᵐ t ∂volume.restrict (Ι (-1 : ℝ) 1), ∀ z ∈ s,
      HasDerivAt (fun z : ℝ => φ t * f (z - ε * t))
        (φ t * deriv f (z - ε * t)) z) :
    loewnerKernel (hiaiRegularization φ ε f) x x =
      ∫ t in (-1 : ℝ)..1,
        φ t * loewnerKernel f (x - ε * t) (x - ε * t) := by
  have hderiv :=
    hiaiRegularization_hasDerivAt_of_dominated_deriv
      (φ := φ) (f := f) (ε := ε) (x := x) (s := s) (bound := bound)
      hs hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
  rw [loewnerKernel_self]
  change
    deriv (fun z : ℝ => ∫ t in (-1 : ℝ)..1, φ t * f (z - ε * t)) x =
      ∫ t in (-1 : ℝ)..1,
        φ t * loewnerKernel f (x - ε * t) (x - ε * t)
  rw [hderiv.deriv]
  refine intervalIntegral.integral_congr ?_
  intro t _ht
  simp [loewnerKernel_self]

/--
Entrywise regularization formula combining the closed off-diagonal formula with
an externally supplied diagonal formula.  This is the shape consumed by the PSD
transport step.
-/
theorem hiaiRegularization_loewnerKernel_entry_integral_formula_of_diag
    {φ f : ℝ → ℝ} {ε x y : ℝ}
    (hdiag : ∀ z : ℝ,
      loewnerKernel (hiaiRegularization φ ε f) z z =
        ∫ t in (-1 : ℝ)..1,
          φ t * loewnerKernel f (z - ε * t) (z - ε * t))
    (hxint :
      IntervalIntegrable (fun t : ℝ => φ t * f (x - ε * t))
        volume (-1 : ℝ) 1)
    (hyint :
      IntervalIntegrable (fun t : ℝ => φ t * f (y - ε * t))
        volume (-1 : ℝ) 1) :
    loewnerKernel (hiaiRegularization φ ε f) x y =
      ∫ t in (-1 : ℝ)..1,
        φ t * loewnerKernel f (x - ε * t) (y - ε * t) := by
  by_cases hxy : x = y
  · subst y
    exact hdiag x
  · exact hiaiRegularization_loewnerKernel_offdiag_integral_formula
      (φ := φ) (f := f) (ε := ε) (x := x) (y := y) hxy hxint hyint

/--
Finite-node entry formula with public off-diagonal entries and externally
supplied diagonal entries.  The remaining analytic blocker is exactly the
diagonal formula on the selected nodes.
-/
theorem hiaiRegularization_loewnerKernel_entry_integral_formula_of_diag_on_nodes
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f)
    (hdiag : ∀ i : Fin n,
      loewnerKernel (hiaiRegularization φ ε f) (x i) (x i) =
        ∫ t in (-1 : ℝ)..1,
          φ t * loewnerKernel f (x i - ε * t) (x i - ε * t)) :
    ∀ i j : Fin n,
      loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) =
        ∫ t in (-1 : ℝ)..1,
          φ t * loewnerKernel f (x i - ε * t) (x j - ε * t) := by
  intro i j
  by_cases hij : x i = x j
  · simpa [hij] using hdiag i
  · exact
      hiaiRegularization_loewnerKernel_offdiag_integral_formula_of_loewnerPosOnUnitInterval
        (φ := φ) (f := f) hφ hε (hx i) (hx j) hpos hij

/--
Finite-node diagonal formulas under the local dominated-derivative hypotheses.
This is the nodewise form of
`hiaiRegularization_loewnerKernel_diag_integral_formula_of_dominated_deriv`.
-/
theorem hiaiRegularization_diag_formula_on_nodes_of_dominated_deriv
    {φ f : ℝ → ℝ} {ε : ℝ} {n : ℕ} {x : Fin n → ℝ}
    {s : Fin n → Set ℝ} {bound : Fin n → ℝ → ℝ}
    (hs : ∀ i : Fin n, s i ∈ 𝓝 (x i))
    (hF_meas : ∀ i : Fin n, ∀ᶠ z in 𝓝 (x i),
      AEStronglyMeasurable (fun t : ℝ => φ t * f (z - ε * t))
        (volume.restrict (Ι (-1 : ℝ) 1)))
    (hF_int : ∀ i : Fin n,
      Integrable (fun t : ℝ => φ t * f (x i - ε * t))
        (volume.restrict (Ι (-1 : ℝ) 1)))
    (hF'_meas : ∀ i : Fin n,
      AEStronglyMeasurable (fun t : ℝ => φ t * deriv f (x i - ε * t))
        (volume.restrict (Ι (-1 : ℝ) 1)))
    (h_bound : ∀ i : Fin n,
      ∀ᵐ t ∂volume.restrict (Ι (-1 : ℝ) 1), ∀ z ∈ s i,
        ‖φ t * deriv f (z - ε * t)‖ ≤ bound i t)
    (h_bound_int : ∀ i : Fin n,
      Integrable (bound i) (volume.restrict (Ι (-1 : ℝ) 1)))
    (h_diff : ∀ i : Fin n,
      ∀ᵐ t ∂volume.restrict (Ι (-1 : ℝ) 1), ∀ z ∈ s i,
        HasDerivAt (fun z : ℝ => φ t * f (z - ε * t))
          (φ t * deriv f (z - ε * t)) z) :
    ∀ i : Fin n,
      loewnerKernel (hiaiRegularization φ ε f) (x i) (x i) =
        ∫ t in (-1 : ℝ)..1,
          φ t * loewnerKernel f (x i - ε * t) (x i - ε * t) := by
  intro i
  exact
    hiaiRegularization_loewnerKernel_diag_integral_formula_of_dominated_deriv
      (φ := φ) (f := f) (ε := ε) (x := x i)
      (s := s i) (bound := bound i)
      (hs i) (hF_meas i) (hF_int i) (hF'_meas i)
      (h_bound i) (h_bound_int i) (h_diff i)

/--
Finite-node entry formula under local dominated-derivative hypotheses.  Public
continuity supplies the off-diagonal entries; the hypotheses above supply the
diagonal entries.
-/
theorem hiaiRegularization_entry_formula_on_nodes_of_dominated_deriv
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f)
    {s : Fin n → Set ℝ} {bound : Fin n → ℝ → ℝ}
    (hs : ∀ i : Fin n, s i ∈ 𝓝 (x i))
    (hF_meas : ∀ i : Fin n, ∀ᶠ z in 𝓝 (x i),
      AEStronglyMeasurable (fun t : ℝ => φ t * f (z - ε * t))
        (volume.restrict (Ι (-1 : ℝ) 1)))
    (hF_int : ∀ i : Fin n,
      Integrable (fun t : ℝ => φ t * f (x i - ε * t))
        (volume.restrict (Ι (-1 : ℝ) 1)))
    (hF'_meas : ∀ i : Fin n,
      AEStronglyMeasurable (fun t : ℝ => φ t * deriv f (x i - ε * t))
        (volume.restrict (Ι (-1 : ℝ) 1)))
    (h_bound : ∀ i : Fin n,
      ∀ᵐ t ∂volume.restrict (Ι (-1 : ℝ) 1), ∀ z ∈ s i,
        ‖φ t * deriv f (z - ε * t)‖ ≤ bound i t)
    (h_bound_int : ∀ i : Fin n,
      Integrable (bound i) (volume.restrict (Ι (-1 : ℝ) 1)))
    (h_diff : ∀ i : Fin n,
      ∀ᵐ t ∂volume.restrict (Ι (-1 : ℝ) 1), ∀ z ∈ s i,
        HasDerivAt (fun z : ℝ => φ t * f (z - ε * t))
          (φ t * deriv f (z - ε * t)) z) :
    ∀ i j : Fin n,
      loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) =
        ∫ t in (-1 : ℝ)..1,
          φ t * loewnerKernel f (x i - ε * t) (x j - ε * t) := by
  exact
    hiaiRegularization_loewnerKernel_entry_integral_formula_of_diag_on_nodes
      (φ := φ) (f := f) hφ hε hx hpos
      (hiaiRegularization_diag_formula_on_nodes_of_dominated_deriv
        (φ := φ) (f := f) (ε := ε) (x := x)
        (s := s) (bound := bound)
        hs hF_meas hF_int hF'_meas h_bound h_bound_int h_diff)

/--
The same finite-node entry formula in the complex `uIoc` form consumed by the
quadratic-form PSD transport.
-/
theorem hiaiRegularization_entry_uIoc_formula_on_nodes_of_dominated_deriv
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f)
    {s : Fin n → Set ℝ} {bound : Fin n → ℝ → ℝ}
    (hs : ∀ i : Fin n, s i ∈ 𝓝 (x i))
    (hF_meas : ∀ i : Fin n, ∀ᶠ z in 𝓝 (x i),
      AEStronglyMeasurable (fun t : ℝ => φ t * f (z - ε * t))
        (volume.restrict (Ι (-1 : ℝ) 1)))
    (hF_int : ∀ i : Fin n,
      Integrable (fun t : ℝ => φ t * f (x i - ε * t))
        (volume.restrict (Ι (-1 : ℝ) 1)))
    (hF'_meas : ∀ i : Fin n,
      AEStronglyMeasurable (fun t : ℝ => φ t * deriv f (x i - ε * t))
        (volume.restrict (Ι (-1 : ℝ) 1)))
    (h_bound : ∀ i : Fin n,
      ∀ᵐ t ∂volume.restrict (Ι (-1 : ℝ) 1), ∀ z ∈ s i,
        ‖φ t * deriv f (z - ε * t)‖ ≤ bound i t)
    (h_bound_int : ∀ i : Fin n,
      Integrable (bound i) (volume.restrict (Ι (-1 : ℝ) 1)))
    (h_diff : ∀ i : Fin n,
      ∀ᵐ t ∂volume.restrict (Ι (-1 : ℝ) 1), ∀ z ∈ s i,
        HasDerivAt (fun z : ℝ => φ t * f (z - ε * t))
          (φ t * deriv f (z - ε * t)) z) :
    ∀ i j : Fin n,
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ) =
        ∫ t : ℝ, (φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)
          ∂(volume.restrict (Ι (-1 : ℝ) 1)) := by
  intro i j
  have hreal :=
    hiaiRegularization_entry_formula_on_nodes_of_dominated_deriv
      (φ := φ) (f := f) hφ hε hx hpos
      (s := s) (bound := bound)
      hs hF_meas hF_int hF'_meas h_bound h_bound_int h_diff i j
  calc
    (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)
        = ∫ t in (-1 : ℝ)..1,
            ((φ t * loewnerKernel f (x i - ε * t) (x j - ε * t) : ℝ) : ℂ) := by
          rw [intervalIntegral.integral_ofReal]
          exact_mod_cast hreal
    _ = ∫ t : ℝ, (φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)
          ∂(volume.restrict (Ι (-1 : ℝ) 1)) := by
          simp only [Complex.ofReal_mul]
          rw [intervalIntegral.intervalIntegral_eq_integral_uIoc
            (fun t : ℝ =>
              ((φ t * loewnerKernel f (x i - ε * t) (x j - ε * t)) : ℂ))
            (-1) 1 volume]
          simp

/--
The quadratic form of a finite Löwner kernel matrix, expanded entrywise.
-/
theorem loewnerKernel_quadraticForm_entry_sum
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ) :
    star c ⬝ᵥ (A.mulVec c) =
      ∑ i : Fin n, ∑ j : Fin n, star (c i) * A i j * c j := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/--
Entrywise regularization formulas assemble into the quadratic-form integral
formula over the interval-integral carrier `volume.restrict (Ι (-1) 1)`.
-/
theorem hiaiRegularization_loewnerKernel_quadratic_uIoc_integral_formula_of_entry
    {φ f : ℝ → ℝ} {ε : ℝ} {n : ℕ} {x : Fin n → ℝ} (c : Fin n → ℂ)
    (hentry : ∀ i j : Fin n,
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ) =
        ∫ t : ℝ, (φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)
          ∂(volume.restrict (Ι (-1 : ℝ) 1)))
    (hterm_int : ∀ i j : Fin n,
      Integrable
        (fun t : ℝ => star (c i) * ((φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)) * c j)
        (volume.restrict (Ι (-1 : ℝ) 1))) :
    star c ⬝ᵥ
        ((Matrix.of fun i j : Fin n =>
          (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)).mulVec c) =
      ∫ t : ℝ,
        (φ t : ℂ) *
          (star c ⬝ᵥ
            ((Matrix.of fun i j : Fin n =>
              (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)).mulVec c))
        ∂(volume.restrict (Ι (-1 : ℝ) 1)) := by
  let μ : Measure ℝ := volume.restrict (Ι (-1 : ℝ) 1)
  let term : Fin n → Fin n → ℝ → ℂ := fun i j t =>
    star (c i) * ((φ t : ℂ) *
      (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)) * c j
  have hconst : ∀ i j : Fin n,
      star (c i) *
          (∫ t : ℝ, (φ t : ℂ) *
            (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ) ∂μ) * c j =
        ∫ t : ℝ, term i j t ∂μ := by
    intro i j
    calc
      star (c i) *
          (∫ t : ℝ, (φ t : ℂ) *
            (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ) ∂μ) * c j
          = (∫ t : ℝ, star (c i) * ((φ t : ℂ) *
            (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)) ∂μ) * c j := by
              exact congrArg (fun z : ℂ => z * c j)
                (MeasureTheory.integral_const_mul (μ := μ) (star (c i))
                  (fun t : ℝ =>
                    (φ t : ℂ) *
                      (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ))).symm
      _ = ∫ t : ℝ, term i j t ∂μ := by
              exact (MeasureTheory.integral_mul_const (μ := μ) (c j)
                (fun t : ℝ =>
                  star (c i) * ((φ t : ℂ) *
                    (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)))).symm
  calc
    star c ⬝ᵥ
        ((Matrix.of fun i j : Fin n =>
          (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)).mulVec c)
        = ∑ i : Fin n, ∑ j : Fin n,
            star (c i) *
              (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ) * c j := by
          simpa using
            (loewnerKernel_quadraticForm_entry_sum
              (Matrix.of fun i j : Fin n =>
                (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)) c)
    _ = ∑ i : Fin n, ∑ j : Fin n,
            star (c i) *
              (∫ t : ℝ, (φ t : ℂ) *
                (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ) ∂μ) * c j := by
          simp [hentry, μ]
    _ = ∑ i : Fin n, ∑ j : Fin n, ∫ t : ℝ, term i j t ∂μ := by
          apply Finset.sum_congr rfl
          intro i _hi
          apply Finset.sum_congr rfl
          intro j _hj
          exact hconst i j
    _ = ∑ i : Fin n, ∫ t : ℝ, ∑ j : Fin n, term i j t ∂μ := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [MeasureTheory.integral_finset_sum Finset.univ]
          intro j _hj
          exact hterm_int i j
    _ = ∫ t : ℝ, ∑ i : Fin n, ∑ j : Fin n, term i j t ∂μ := by
          rw [MeasureTheory.integral_finset_sum Finset.univ]
          intro i _hi
          exact MeasureTheory.integrable_finset_sum Finset.univ
            (fun j _hj => hterm_int i j)
    _ = ∫ t : ℝ,
        (φ t : ℂ) *
          (star c ⬝ᵥ
            ((Matrix.of fun i j : Fin n =>
              (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)).mulVec c))
        ∂μ := by
          congr 1
          ext t
          rw [loewnerKernel_quadraticForm_entry_sum]
          simp [term, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

/--
Conditional PSD transport from entrywise regularization formulas.  This packages
the finite-sum/integral exchange, while keeping the analytic entry formulas as
explicit hypotheses.
-/
theorem regularization_loewnerKernelPSD_of_entry_integral_formula
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hinj : Function.Injective x) (hpos : LoewnerPosOnUnitInterval f)
    (hentry : ∀ i j : Fin n,
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ) =
        ∫ t : ℝ, (φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)
          ∂(volume.restrict (Ι (-1 : ℝ) 1)))
    (hterm_int : ∀ c : Fin n → ℂ, ∀ i j : Fin n,
      Integrable
        (fun t : ℝ => star (c i) * ((φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)) * c j)
        (volume.restrict (Ι (-1 : ℝ) 1))) :
    (Matrix.of fun i j : Fin n =>
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext ?_
    intro i j
    simp [loewnerKernel_swap]
  · intro c
    rw [hiaiRegularization_loewnerKernel_quadratic_uIoc_integral_formula_of_entry
      (φ := φ) (f := f) (ε := ε) (x := x) c hentry (hterm_int c)]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
      have ht_uIcc : t ∈ [[(-1 : ℝ), 1]] := Set.uIoc_subset_uIcc ht
      simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht_uIcc
    have hpsd :=
      loewnerKernel_shifted_posSemidef_of_loewnerPosOnUnitInterval
        (f := f) hpos hε hx hinj htIcc
    exact mul_nonneg
      (by exact_mod_cast hφ.nonneg t)
      (hpsd.dotProduct_mulVec_nonneg c)
end

end Quantum.TraceInequality.Loewner
