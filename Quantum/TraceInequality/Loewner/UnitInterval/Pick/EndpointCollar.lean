import Quantum.TraceInequality.Loewner.UnitInterval.Pick.MeasureDomination
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Regular

/-!
# Chapter 3 weighted Poisson endpoint-collar estimate

This module completes the endpoint-collar estimate and packages the concrete
Proposition 3.5 inversion producer.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set
open Filter
open scoped Topology
open scoped NNReal
open scoped ENNReal

noncomputable section

/-! ### Weighted Poisson endpoint-collar estimate -/

/-- A regularity test function supported in `(-1,1)` vanishes at both endpoints. -/
theorem prop35_test_endpoint_values_zero
    (g : ℝ → ℝ)
    (hg_zero : EqOn g 0 (Set.Ioo (-1 : ℝ) 1)ᶜ) :
    g (-1) = 0 ∧ g 1 = 0 := by
  constructor
  · exact hg_zero (by simp)
  · exact hg_zero (by simp)

/--
Continuity and endpoint vanishing make the test function uniformly small on
the endpoint collars.  The collars are expressed by metric distance from
`-1` or `1`; later estimates can specialize this to interval collars.
-/
theorem prop35_test_small_on_endpoint_collar
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_zero : EqOn g 0 (Set.Ioo (-1 : ℝ) 1)ᶜ)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        (dist x (-1 : ℝ) < δ ∨ dist x (1 : ℝ) < δ) → g x ≤ η := by
  have hleft0 : g (-1) = 0 := (prop35_test_endpoint_values_zero g hg_zero).1
  have hright0 : g 1 = 0 := (prop35_test_endpoint_values_zero g hg_zero).2
  have hcontL : ContinuousAt g (-1 : ℝ) := hg_cont.continuousAt
  have hcontR : ContinuousAt g (1 : ℝ) := hg_cont.continuousAt
  rw [Metric.continuousAt_iff] at hcontL
  rw [Metric.continuousAt_iff] at hcontR
  rcases hcontL η hη with ⟨δl, hδl, hδlprop⟩
  rcases hcontR η hη with ⟨δr, hδr, hδrprop⟩
  refine ⟨min δl δr, lt_min hδl hδr, ?_⟩
  intro x _hx hdist
  rcases hdist with hdist | hdist
  · have hxclose : dist x (-1 : ℝ) < δl :=
      lt_of_lt_of_le hdist (min_le_left _ _)
    have habs : dist (g x) (g (-1)) < η := hδlprop hxclose
    rw [hleft0] at habs
    simpa [Real.dist_eq, abs_of_nonneg (hg_nonneg x)] using habs.le
  · have hxclose : dist x (1 : ℝ) < δr :=
      lt_of_lt_of_le hdist (min_le_right _ _)
    have habs : dist (g x) (g 1) < η := hδrprop hxclose
    rw [hright0] at habs
    simpa [Real.dist_eq, abs_of_nonneg (hg_nonneg x)] using habs.le

/-- The fixed book weight in the Proposition 3.5 test kernel is at most one. -/
theorem unitIntervalHerglotzProp35Weight_le_one (x : ℝ) :
    (Real.pi)⁻¹ * (1 + x ^ (2 : ℕ))⁻¹ ≤ (1 : ℝ) := by
  have hpi : (Real.pi)⁻¹ ≤ (1 : ℝ) := by
    exact inv_le_one_of_one_le₀ (by linarith [Real.two_le_pi])
  have hden_nonneg : 0 ≤ (1 + x ^ (2 : ℕ))⁻¹ := by positivity
  have hden_le : (1 + x ^ (2 : ℕ))⁻¹ ≤ (1 : ℝ) := by
    exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
  exact mul_le_one₀ hpi hden_nonneg hden_le

/--
On the interior compact part, the weighted Poisson integrand is pointwise
bounded by the boundary imaginary part itself.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonIntegrand_le_boundary_im_concrete
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_le_one : ∀ x : ℝ, g x ≤ 1) (n : ℕ) (x : ℝ) :
    data.prop35WeightedPoissonIntegrand g n x ≤
      (data.pick.F (unitIntervalUpperBoundarySeq x n)).im := by
  have him_nonneg : 0 ≤ (data.pick.F (unitIntervalUpperBoundarySeq x n)).im :=
    data.pick.mapsUpper (unitIntervalUpperBoundarySeq_im_pos x n)
  have hfac_nonneg : 0 ≤ (Real.pi)⁻¹ * (1 + x ^ (2 : ℕ))⁻¹ := by positivity
  have hweight_le :
      g x * ((Real.pi)⁻¹ * (1 + x ^ (2 : ℕ))⁻¹) ≤ 1 := by
    exact mul_le_one₀ (hg_le_one x) hfac_nonneg
      (unitIntervalHerglotzProp35Weight_le_one x)
  calc
    data.prop35WeightedPoissonIntegrand g n x ≤
        g x * ((Real.pi)⁻¹ * (1 + x ^ (2 : ℕ))⁻¹) *
          (data.pick.F (unitIntervalUpperBoundarySeq x n)).im :=
          data.prop35WeightedPoissonIntegrand_le_boundary_im g hg_nonneg n x
    _ ≤ 1 * (data.pick.F (unitIntervalUpperBoundarySeq x n)).im := by
          exact mul_le_mul_of_nonneg_right hweight_le him_nonneg
    _ = (data.pick.F (unitIntervalUpperBoundarySeq x n)).im := by ring

/-- Positive collars put the remaining interior interval inside `(-1,1)`. -/
theorem prop35_interiorCompact_subset_Ioo {δ : ℝ} (hδpos : 0 < δ) :
    Set.Icc ((-1 : ℝ) + δ) (1 - δ) ⊆ Set.Ioo (-1 : ℝ) 1 := by
  intro x hx
  rcases hx with ⟨hxL, hxR⟩
  constructor <;> linarith

/--
Uniform boundary-imaginary vanishing on the compact interior interval
`[-1+δ,1-δ]`.
-/
theorem PickExtensionOnUnitInterval.boundary_im_tendstoUniformlyOn_zero_on_prop35_interior
    {f : ℝ → ℝ} (pick : PickExtensionOnUnitInterval f)
    {δ : ℝ} (hδpos : 0 < δ) :
    TendstoUniformlyOn
      (fun n : ℕ => fun x : ℝ =>
        (pick.F (unitIntervalUpperBoundarySeq x n)).im)
      (fun _x : ℝ => 0) atTop
      (Set.Icc ((-1 : ℝ) + δ) (1 - δ)) := by
  exact pickExtension_boundary_im_tendstoUniformlyOn_zero_of_isCompact pick
    isCompact_Icc
    (prop35_interiorCompact_subset_Ioo hδpos)

/--
The weighted Poisson contribution from a fixed compact interior interval tends
to zero.  This is the compact part of the endpoint-collar argument.
-/
theorem UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonInterior_tendsto_zero
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_le_one : ∀ x : ℝ, g x ≤ 1)
    {δ : ℝ} (hδpos : 0 < δ) :
    Tendsto (fun n : ℕ => ∫ x in Set.Icc ((-1 : ℝ) + δ) (1 - δ),
      data.prop35WeightedPoissonIntegrand g n x) atTop (𝓝 0) := by
  let K : Set ℝ := Set.Icc ((-1 : ℝ) + δ) (1 - δ)
  have hKcompact : IsCompact K := isCompact_Icc
  have hKfinite : (volume : Measure ℝ) K < ∞ := hKcompact.measure_lt_top
  have hU : TendstoUniformlyOn
      (fun n : ℕ => fun x : ℝ =>
        (data.pick.F (unitIntervalUpperBoundarySeq x n)).im)
      (fun _x : ℝ => 0) atTop K := by
    simpa [K] using
      data.pick.boundary_im_tendstoUniformlyOn_zero_on_prop35_interior hδpos
  rw [Metric.tendsto_nhds]
  intro ε hε
  let C : ℝ := ε / ((volume : Measure ℝ).real K + 1)
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hUevent := (Metric.tendstoUniformlyOn_iff.mp hU) C hCpos
  filter_upwards [hUevent] with n hn
  have hnorm :
      ‖∫ x in K, data.prop35WeightedPoissonIntegrand g n x
          ∂(volume : Measure ℝ)‖ ≤
        C * (volume : Measure ℝ).real K := by
    refine norm_setIntegral_le_of_norm_le_const hKfinite ?_
    intro x hx
    have him_nonneg :
        0 ≤ (data.pick.F (unitIntervalUpperBoundarySeq x n)).im :=
      data.pick.mapsUpper (unitIntervalUpperBoundarySeq_im_pos x n)
    have hboundary_lt :
        (data.pick.F (unitIntervalUpperBoundarySeq x n)).im < C := by
      have hdist := hn x hx
      simpa [Real.dist_eq, abs_of_nonneg him_nonneg] using hdist
    have hle := data.prop35WeightedPoissonIntegrand_le_boundary_im_concrete
      g hg_nonneg hg_le_one n x
    have hnonneg := data.prop35WeightedPoissonIntegrand_nonneg g hg_nonneg n x
    rw [Real.norm_of_nonneg hnonneg]
    exact hle.trans hboundary_lt.le
  have hprod_lt : C * (volume : Measure ℝ).real K < ε := by
    have hM_nonneg : 0 ≤ (volume : Measure ℝ).real K := ENNReal.toReal_nonneg
    dsimp [C]
    have hden_pos : 0 < (volume : Measure ℝ).real K + 1 := by positivity
    have hM_lt : (volume : Measure ℝ).real K <
        (volume : Measure ℝ).real K + 1 := by linarith
    calc
      ε / ((volume : Measure ℝ).real K + 1) *
          (volume : Measure ℝ).real K
          < ε / ((volume : Measure ℝ).real K + 1) *
              ((volume : Measure ℝ).real K + 1) := by
            exact mul_lt_mul_of_pos_left hM_lt (by positivity)
      _ = ε := by field_simp [hden_pos.ne']
  simpa [K, Real.dist_eq] using hnorm.trans_lt hprod_lt

/-- The endpoint collars inside `[-1,1]`, expressed by distance from the endpoints. -/
def prop35EndpointCollar (δ : ℝ) : Set ℝ :=
  {x : ℝ | x ∈ Set.Icc (-1 : ℝ) 1 ∧
    (dist x (-1 : ℝ) < δ ∨ dist x (1 : ℝ) < δ)}

/-- The endpoint collar is measurable. -/
theorem prop35EndpointCollar_measurableSet (δ : ℝ) :
    MeasurableSet (prop35EndpointCollar δ) := by
  unfold prop35EndpointCollar
  measurability

/-- Indicator of a continuous test function on the endpoint collar is measurable. -/
theorem prop35EndpointCollar_indicator_aestronglyMeasurable
    (g : ℝ → ℝ) (hg_cont : Continuous g) (δ : ℝ) :
    AEStronglyMeasurable ((prop35EndpointCollar δ).indicator g)
      (volume : Measure ℝ) := by
  have hmeas : Measurable ((prop35EndpointCollar δ).indicator g) :=
    hg_cont.measurable.indicator (prop35EndpointCollar_measurableSet δ)
  exact hmeas.aestronglyMeasurable

/-- Nonnegativity is preserved by restricting the test function to the collar. -/
theorem prop35EndpointCollar_indicator_nonneg
    (g : ℝ → ℝ) (hg_nonneg : ∀ x : ℝ, 0 ≤ g x) (δ : ℝ) :
    ∀ x : ℝ, 0 ≤ (prop35EndpointCollar δ).indicator g x := by
  intro x
  by_cases hx : x ∈ prop35EndpointCollar δ
  · simpa [Set.indicator_of_mem hx] using hg_nonneg x
  · simp [Set.indicator_of_notMem hx]

/-- The collar indicator is bounded by `η` when `g` is small on the collar. -/
theorem prop35EndpointCollar_indicator_le
    (g : ℝ → ℝ) {δ η : ℝ} (hη_nonneg : 0 ≤ η)
    (hsmall :
      ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        (dist x (-1 : ℝ) < δ ∨ dist x (1 : ℝ) < δ) → g x ≤ η) :
    ∀ x : ℝ, (prop35EndpointCollar δ).indicator g x ≤ η := by
  intro x
  by_cases hx : x ∈ prop35EndpointCollar δ
  · rcases hx with ⟨hxI, hxdist⟩
    rw [Set.indicator_of_mem (show x ∈ prop35EndpointCollar δ from ⟨hxI, hxdist⟩)]
    exact hsmall x hxI hxdist
  · rw [Set.indicator_of_notMem hx]
    exact hη_nonneg

/-- The compact interior and endpoint collar cover the open interval. -/
theorem prop35_Ioo_subset_interior_union_endpointCollar {δ : ℝ} :
    Set.Ioo (-1 : ℝ) 1 ⊆
      Set.Icc ((-1 : ℝ) + δ) (1 - δ) ∪ prop35EndpointCollar δ := by
  intro x hxI
  by_cases hxK : x ∈ Set.Icc ((-1 : ℝ) + δ) (1 - δ)
  · exact Or.inl hxK
  · right
    rcases hxI with ⟨hxL, hxR⟩
    unfold prop35EndpointCollar
    refine ⟨⟨hxL.le, hxR.le⟩, ?_⟩
    simp only [Set.mem_Icc, not_and_or] at hxK
    rcases hxK with hxleft | hxright
    · left
      rw [Real.dist_eq]
      have hnonneg : 0 ≤ x - (-1 : ℝ) := by linarith
      rw [abs_of_nonneg hnonneg]
      linarith
    · right
      rw [Real.dist_eq]
      have hnonpos : x - (1 : ℝ) ≤ 0 := by linarith
      rw [abs_of_nonpos hnonpos]
      linarith

/-- The compact interior is disjoint from the endpoint collar. -/
theorem prop35_interior_disjoint_endpointCollar {δ : ℝ} :
    Disjoint (Set.Icc ((-1 : ℝ) + δ) (1 - δ)) (prop35EndpointCollar δ) := by
  rw [Set.disjoint_left]
  intro x hxK hxC
  rcases hxK with ⟨hxKL, hxKR⟩
  rcases hxC with ⟨hxI, hxdist⟩
  rcases hxI with ⟨hxIleft, hxIright⟩
  rcases hxdist with hleft | hright
  · rw [Real.dist_eq] at hleft
    have hnonneg : 0 ≤ x - (-1 : ℝ) := by linarith
    rw [abs_of_nonneg hnonneg] at hleft
    linarith
  · rw [Real.dist_eq] at hright
    have hnonpos : x - (1 : ℝ) ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos] at hright
    linarith

/--
If a nonnegative test weight is uniformly bounded by `η`, then its normalized
kernel average is bounded by `4η`; this is the Cauchy-kernel `x`-integral estimate in the
form needed for endpoint collars.
-/
theorem prop35WeightedPoissonKernel_xIntegral_norm_bound_of_test_le
    (u : ℝ → ℝ) (hu_meas : AEStronglyMeasurable u (volume : Measure ℝ))
    {η : ℝ} (hη_nonneg : 0 ≤ η)
    (hu_nonneg : ∀ x : ℝ, 0 ≤ u x)
    (hu_le : ∀ x : ℝ, u x ≤ η)
    (n : ℕ) (y : ℝ) :
    ‖∫ x : ℝ, u x * unitIntervalHerglotzProp35TestKernel
      (1 / ((n : ℝ) + 1)) x y‖ ≤ η * 4 := by
  let ε : ℝ := 1 / ((n : ℝ) + 1)
  have hε : 0 < ε := by positivity
  have hε_le : ε ≤ 1 := unitIntervalHerglotz_prop35Scale_le_one n
  have hK_norm_int : Integrable
      (fun x : ℝ => ‖unitIntervalHerglotzProp35TestKernel ε x y‖)
      (volume : Measure ℝ) :=
    (unitIntervalHerglotzProp35TestKernel_integrable_x (y := y) hε).norm
  have hUK_meas : AEStronglyMeasurable
      (fun x : ℝ => u x * unitIntervalHerglotzProp35TestKernel ε x y)
      (volume : Measure ℝ) := by
    have hK : StronglyMeasurable
        (fun x : ℝ => unitIntervalHerglotzProp35TestKernel ε x y) := by
      have hm : Measurable
          (fun x : ℝ => unitIntervalHerglotzProp35TestKernel ε x y) := by
        unfold unitIntervalHerglotzProp35TestKernel unitIntervalHerglotzPoissonKernel
        fun_prop
      exact hm.stronglyMeasurable
    exact hu_meas.mul hK.aestronglyMeasurable
  have hUK_norm_int : Integrable
      (fun x : ℝ => ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖)
      (volume : Measure ℝ) := by
    refine (hK_norm_int.const_mul η).mono' hUK_meas.norm ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    change ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖ ≤
      η * ‖unitIntervalHerglotzProp35TestKernel ε x y‖
    rw [norm_mul]
    have hu_norm : ‖u x‖ ≤ η := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hu_nonneg x], hu_le x⟩
    exact mul_le_mul_of_nonneg_right hu_norm (norm_nonneg _)
  have hinner_norm := MeasureTheory.norm_integral_le_integral_norm
    (μ := (volume : Measure ℝ))
    (f := fun x : ℝ => u x * unitIntervalHerglotzProp35TestKernel ε x y)
  have hmono :
      (∫ x : ℝ, ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖) ≤
        ∫ x : ℝ, η * ‖unitIntervalHerglotzProp35TestKernel ε x y‖ := by
    refine integral_mono hUK_norm_int (hK_norm_int.const_mul η) ?_
    intro x
    change ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖ ≤
      η * ‖unitIntervalHerglotzProp35TestKernel ε x y‖
    rw [norm_mul]
    have hu_norm : ‖u x‖ ≤ η := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hu_nonneg x], hu_le x⟩
    exact mul_le_mul_of_nonneg_right hu_norm (norm_nonneg _)
  have hK_bound :
      (∫ x : ℝ, ‖unitIntervalHerglotzProp35TestKernel ε x y‖) ≤ 4 :=
    unitIntervalHerglotzProp35TestKernel_xIntegral_norm_bound_concrete hε hε_le
  calc
    ‖∫ x : ℝ, u x * unitIntervalHerglotzProp35TestKernel
      (1 / ((n : ℝ) + 1)) x y‖
        = ‖∫ x : ℝ, u x * unitIntervalHerglotzProp35TestKernel ε x y‖ := by rfl
    _ ≤ ∫ x : ℝ, ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖ := hinner_norm
    _ ≤ ∫ x : ℝ, η * ‖unitIntervalHerglotzProp35TestKernel ε x y‖ := hmono
    _ = η * (∫ x : ℝ, ‖unitIntervalHerglotzProp35TestKernel ε x y‖) := by
          rw [integral_const_mul]
    _ ≤ η * 4 := mul_le_mul_of_nonneg_left hK_bound hη_nonneg

/--
Integral of the norm version of the preceding `4η` estimate.  This is the
input needed for product integrability of indicator-cut collar kernels.
-/
theorem prop35WeightedPoissonKernel_xIntegral_norm_integral_bound_of_test_le
    (u : ℝ → ℝ) (hu_meas : AEStronglyMeasurable u (volume : Measure ℝ))
    {η : ℝ} (hη_nonneg : 0 ≤ η)
    (hu_nonneg : ∀ x : ℝ, 0 ≤ u x)
    (hu_le : ∀ x : ℝ, u x ≤ η)
    (n : ℕ) (y : ℝ) :
    (∫ x : ℝ, ‖u x * unitIntervalHerglotzProp35TestKernel
      (1 / ((n : ℝ) + 1)) x y‖) ≤ η * 4 := by
  let ε : ℝ := 1 / ((n : ℝ) + 1)
  have hε : 0 < ε := by positivity
  have hε_le : ε ≤ 1 := unitIntervalHerglotz_prop35Scale_le_one n
  have hK_norm_int : Integrable
      (fun x : ℝ => ‖unitIntervalHerglotzProp35TestKernel ε x y‖)
      (volume : Measure ℝ) :=
    (unitIntervalHerglotzProp35TestKernel_integrable_x (y := y) hε).norm
  have hUK_meas : AEStronglyMeasurable
      (fun x : ℝ => u x * unitIntervalHerglotzProp35TestKernel ε x y)
      (volume : Measure ℝ) := by
    have hK : StronglyMeasurable
        (fun x : ℝ => unitIntervalHerglotzProp35TestKernel ε x y) := by
      have hm : Measurable
          (fun x : ℝ => unitIntervalHerglotzProp35TestKernel ε x y) := by
        unfold unitIntervalHerglotzProp35TestKernel unitIntervalHerglotzPoissonKernel
        fun_prop
      exact hm.stronglyMeasurable
    exact hu_meas.mul hK.aestronglyMeasurable
  have hUK_norm_int : Integrable
      (fun x : ℝ => ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖)
      (volume : Measure ℝ) := by
    refine (hK_norm_int.const_mul η).mono' hUK_meas.norm ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    change ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖ ≤
      η * ‖unitIntervalHerglotzProp35TestKernel ε x y‖
    rw [norm_mul]
    have hu_norm : ‖u x‖ ≤ η := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hu_nonneg x], hu_le x⟩
    exact mul_le_mul_of_nonneg_right hu_norm (norm_nonneg _)
  have hmono :
      (∫ x : ℝ, ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖) ≤
        ∫ x : ℝ, η * ‖unitIntervalHerglotzProp35TestKernel ε x y‖ := by
    refine integral_mono hUK_norm_int (hK_norm_int.const_mul η) ?_
    intro x
    change ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖ ≤
      η * ‖unitIntervalHerglotzProp35TestKernel ε x y‖
    rw [norm_mul]
    have hu_norm : ‖u x‖ ≤ η := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hu_nonneg x], hu_le x⟩
    exact mul_le_mul_of_nonneg_right hu_norm (norm_nonneg _)
  have hK_bound :
      (∫ x : ℝ, ‖unitIntervalHerglotzProp35TestKernel ε x y‖) ≤ 4 :=
    unitIntervalHerglotzProp35TestKernel_xIntegral_norm_bound_concrete hε hε_le
  calc
    (∫ x : ℝ, ‖u x * unitIntervalHerglotzProp35TestKernel
      (1 / ((n : ℝ) + 1)) x y‖)
        = ∫ x : ℝ, ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖ := by rfl
    _ ≤ ∫ x : ℝ, η * ‖unitIntervalHerglotzProp35TestKernel ε x y‖ := hmono
    _ = η * (∫ x : ℝ, ‖unitIntervalHerglotzProp35TestKernel ε x y‖) := by
          rw [integral_const_mul]
    _ ≤ η * 4 := mul_le_mul_of_nonneg_left hK_bound hη_nonneg

/-- Fixed-`y` integrability for a bounded nonnegative test weight. -/
theorem prop35WeightedPoissonKernel_integrable_x_of_test_le
    (u : ℝ → ℝ) (hu_meas : AEStronglyMeasurable u (volume : Measure ℝ))
    {η : ℝ} (hη_nonneg : 0 ≤ η)
    (hu_nonneg : ∀ x : ℝ, 0 ≤ u x)
    (hu_le : ∀ x : ℝ, u x ≤ η)
    {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    Integrable (fun x : ℝ => u x * unitIntervalHerglotzProp35TestKernel ε x y)
      (volume : Measure ℝ) := by
  have hK_norm_int : Integrable
      (fun x : ℝ => ‖unitIntervalHerglotzProp35TestKernel ε x y‖)
      (volume : Measure ℝ) :=
    (unitIntervalHerglotzProp35TestKernel_integrable_x (y := y) hε).norm
  have hUK_meas : AEStronglyMeasurable
      (fun x : ℝ => u x * unitIntervalHerglotzProp35TestKernel ε x y)
      (volume : Measure ℝ) := by
    have hK : StronglyMeasurable
        (fun x : ℝ => unitIntervalHerglotzProp35TestKernel ε x y) := by
      have hm : Measurable
          (fun x : ℝ => unitIntervalHerglotzProp35TestKernel ε x y) := by
        unfold unitIntervalHerglotzProp35TestKernel unitIntervalHerglotzPoissonKernel
        fun_prop
      exact hm.stronglyMeasurable
    exact hu_meas.mul hK.aestronglyMeasurable
  have hUK_norm_int : Integrable
      (fun x : ℝ => ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖)
      (volume : Measure ℝ) := by
    refine (hK_norm_int.const_mul η).mono' hUK_meas.norm ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    change ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖ ≤
      η * ‖unitIntervalHerglotzProp35TestKernel ε x y‖
    rw [norm_mul]
    have hu_norm : ‖u x‖ ≤ η := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hu_nonneg x], hu_le x⟩
    exact mul_le_mul_of_nonneg_right hu_norm (norm_nonneg _)
  exact (integrable_norm_iff hUK_meas).1 hUK_norm_int

/-- Product integrability for indicator-cut collar kernels. -/
theorem UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonKernel_integrable_prod_of_test_le
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (u : ℝ → ℝ) (hu_meas : Measurable u)
    {η : ℝ} (hη_nonneg : 0 ≤ η)
    (hu_nonneg : ∀ x : ℝ, 0 ≤ u x)
    (hu_le : ∀ x : ℝ, u x ≤ η)
    (n : ℕ) :
    Integrable (Function.uncurry fun x y : ℝ =>
      u x * unitIntervalHerglotzProp35TestKernel (1 / ((n : ℝ) + 1)) x y)
      ((volume : Measure ℝ).prod (data.measure : Measure ℝ)) := by
  let ε : ℝ := 1 / ((n : ℝ) + 1)
  have hε : 0 < ε := by positivity
  let F : ℝ × ℝ → ℝ := Function.uncurry fun x y : ℝ =>
    u x * unitIntervalHerglotzProp35TestKernel ε x y
  have hF : AEStronglyMeasurable F
      ((volume : Measure ℝ).prod (data.measure : Measure ℝ)) := by
    have hm : Measurable F := by
      dsimp [F, Function.uncurry]
      unfold unitIntervalHerglotzProp35TestKernel unitIntervalHerglotzPoissonKernel
      fun_prop
    exact hm.aestronglyMeasurable
  have hnorm_meas : AEStronglyMeasurable
      (fun y : ℝ => ∫ x : ℝ, ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖)
      (data.measure : Measure ℝ) := by
    have hs := hF.norm.prod_swap
    simpa [F, Function.comp_def, Function.uncurry] using
      (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (μ := (data.measure : Measure ℝ)) (ν := (volume : Measure ℝ)) hs)
  have hnorm_int : Integrable
      (fun y : ℝ => ∫ x : ℝ, ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖)
      (data.measure : Measure ℝ) := by
    refine (MeasureTheory.integrable_const (η * 4)).mono' hnorm_meas ?_
    filter_upwards with y
    have hnonneg :
        0 ≤ ∫ x : ℝ, ‖u x * unitIntervalHerglotzProp35TestKernel ε x y‖ := by
      exact integral_nonneg_of_ae
        (MeasureTheory.ae_of_all (volume : Measure ℝ) fun x => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    simpa [ε] using
      prop35WeightedPoissonKernel_xIntegral_norm_integral_bound_of_test_le
        u hu_meas.aestronglyMeasurable hη_nonneg hu_nonneg hu_le n y
  have hprod := (MeasureTheory.integrable_prod_iff' hF).2 ?_
  · simpa [F, Function.uncurry, ε] using hprod
  constructor
  · exact MeasureTheory.ae_of_all (data.measure : Measure ℝ) fun y =>
      prop35WeightedPoissonKernel_integrable_x_of_test_le
        u hu_meas.aestronglyMeasurable hη_nonneg hu_nonneg hu_le hε y
  · exact hnorm_int

/-- Endpoint-collar contribution after Fubini is bounded by `4η` times the mass. -/
theorem UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonEndpointCollar_bound
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    {δ η : ℝ} (hη_nonneg : 0 ≤ η)
    (hsmall :
      ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        (dist x (-1 : ℝ) < δ ∨ dist x (1 : ℝ) < δ) → g x ≤ η)
    (n : ℕ) :
    ‖∫ y : ℝ, (∫ x : ℝ,
        (prop35EndpointCollar δ).indicator g x *
          unitIntervalHerglotzProp35TestKernel
            (1 / ((n : ℝ) + 1)) x y)
        ∂(data.measure : Measure ℝ)‖ ≤
      (η * 4) * (data.measure : Measure ℝ).real Set.univ := by
  refine MeasureTheory.norm_integral_le_of_norm_le_const ?_
  exact MeasureTheory.ae_of_all (data.measure : Measure ℝ) fun y =>
    prop35WeightedPoissonKernel_xIntegral_norm_bound_of_test_le
      ((prop35EndpointCollar δ).indicator g)
      (prop35EndpointCollar_indicator_aestronglyMeasurable g hg_cont δ)
      hη_nonneg
      (prop35EndpointCollar_indicator_nonneg g hg_nonneg δ)
      (prop35EndpointCollar_indicator_le g hη_nonneg hsmall)
      n y

/-- Integrability of the weighted Poisson-side integrand for regularity tests. -/
theorem UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonIntegrand_integrable
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_zero : EqOn g 0 (Set.Ioo (-1 : ℝ) 1)ᶜ)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_le_one : ∀ x : ℝ, g x ≤ 1)
    (n : ℕ) :
    Integrable (fun x : ℝ => data.prop35WeightedPoissonIntegrand g n x)
      (volume : Measure ℝ) := by
  have hprodInt : Integrable (Function.uncurry fun x y : ℝ =>
      g x * unitIntervalHerglotzProp35TestKernel
        (1 / ((n : ℝ) + 1)) x y)
      ((volume : Measure ℝ).prod (data.measure : Measure ℝ)) :=
    data.prop35_testKernel_integrable_prod g
      (by positivity : 0 < 1 / ((n : ℝ) + 1))
      hg_cont hg_zero hg_nonneg hg_le_one
  have hxint : Integrable (fun x : ℝ => ∫ y : ℝ,
      g x * unitIntervalHerglotzProp35TestKernel
        (1 / ((n : ℝ) + 1)) x y ∂(data.measure : Measure ℝ))
      (volume : Measure ℝ) := by
    simpa [Function.uncurry] using
      MeasureTheory.Integrable.integral_prod_left hprodInt
  refine hxint.congr ?_
  filter_upwards with x
  symm
  unfold UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonIntegrand
  calc
    g x * ((Real.pi)⁻¹ * (1 + x ^ (2 : ℕ))⁻¹) *
        (∫ y : ℝ, unitIntervalHerglotzPoissonKernel
          (1 / ((n : ℝ) + 1)) x y ∂(data.measure : Measure ℝ))
      = ∫ y : ℝ,
          g x * ((Real.pi)⁻¹ * (1 + x ^ (2 : ℕ))⁻¹) *
            unitIntervalHerglotzPoissonKernel
              (1 / ((n : ℝ) + 1)) x y ∂(data.measure : Measure ℝ) := by
          rw [← integral_const_mul]
    _ = ∫ y : ℝ,
        g x * unitIntervalHerglotzProp35TestKernel
          (1 / ((n : ℝ) + 1)) x y ∂(data.measure : Measure ℝ) := by
          refine integral_congr_ae ?_
          filter_upwards with y
          unfold unitIntervalHerglotzProp35TestKernel
          ring

/-- The collar set integral is the Fubini-swapped indicator expression. -/
theorem
    UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonEndpointCollar_setIntegral_eq_fubini
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    {δ η : ℝ} (hη_nonneg : 0 ≤ η)
    (hsmall :
      ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        (dist x (-1 : ℝ) < δ ∨ dist x (1 : ℝ) < δ) → g x ≤ η)
    (n : ℕ) :
    (∫ x in prop35EndpointCollar δ,
        data.prop35WeightedPoissonIntegrand g n x) =
      ∫ y : ℝ, (∫ x : ℝ,
        (prop35EndpointCollar δ).indicator g x *
          unitIntervalHerglotzProp35TestKernel
            (1 / ((n : ℝ) + 1)) x y)
        ∂(data.measure : Measure ℝ) := by
  let u : ℝ → ℝ := (prop35EndpointCollar δ).indicator g
  have hu_meas : Measurable u :=
    hg_cont.measurable.indicator (prop35EndpointCollar_measurableSet δ)
  have hu_nonneg : ∀ x : ℝ, 0 ≤ u x := by
    simpa [u] using prop35EndpointCollar_indicator_nonneg g hg_nonneg δ
  have hu_le : ∀ x : ℝ, u x ≤ η := by
    simpa [u] using prop35EndpointCollar_indicator_le g hη_nonneg hsmall
  have hInt : Integrable (Function.uncurry fun x y : ℝ =>
      u x * unitIntervalHerglotzProp35TestKernel
        (1 / ((n : ℝ) + 1)) x y)
      ((volume : Measure ℝ).prod (data.measure : Measure ℝ)) :=
    data.prop35WeightedPoissonKernel_integrable_prod_of_test_le
      u hu_meas hη_nonneg hu_nonneg hu_le n
  have hweighted_fubini :
      data.prop35WeightedPoissonSeq u n = data.prop35FubiniApproxSeq u n := by
    exact (data.prop35TestIntegralSeq_eq_weightedPoissonSeq u n).symm.trans
      (data.prop35TestIntegralSeq_eq_fubiniApproxSeq u n hInt)
  have hleft_u :
      (∫ x in prop35EndpointCollar δ,
          data.prop35WeightedPoissonIntegrand g n x) =
        ∫ x in prop35EndpointCollar δ,
          data.prop35WeightedPoissonIntegrand u n x := by
    refine setIntegral_congr_fun (prop35EndpointCollar_measurableSet δ) ?_
    intro x hx
    unfold UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonIntegrand
    dsimp [u]
    rw [Set.indicator_of_mem hx]
  have hu_support :
      (∫ x in prop35EndpointCollar δ,
          data.prop35WeightedPoissonIntegrand u n x) =
        ∫ x : ℝ, data.prop35WeightedPoissonIntegrand u n x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro x hx
    unfold UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonIntegrand
    dsimp [u]
    rw [Set.indicator_of_notMem hx]
    simp
  rw [hleft_u, hu_support]
  rw [← data.prop35WeightedPoissonSeq_eq_integral_integrand u n]
  simpa [UnitIntervalPickHerglotzUpperRawData.prop35FubiniApproxSeq, u]
    using hweighted_fubini

/-- Endpoint-collar set integral bound in the original weighted-Poisson normal form. -/
theorem
    UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonEndpointCollar_setIntegral_norm_bound
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    {δ η : ℝ} (hη_nonneg : 0 ≤ η)
    (hsmall :
      ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        (dist x (-1 : ℝ) < δ ∨ dist x (1 : ℝ) < δ) → g x ≤ η)
    (n : ℕ) :
    ‖∫ x in prop35EndpointCollar δ,
        data.prop35WeightedPoissonIntegrand g n x‖ ≤
      (η * 4) * (data.measure : Measure ℝ).real Set.univ := by
  rw [data.prop35WeightedPoissonEndpointCollar_setIntegral_eq_fubini
    g hg_cont hg_nonneg hη_nonneg hsmall n]
  exact data.prop35WeightedPoissonEndpointCollar_bound
    g hg_cont hg_nonneg hη_nonneg hsmall n

/-- Split the weighted Poisson sequence into interior and endpoint-collar pieces. -/
theorem UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonSeq_eq_interior_add_endpointCollar
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_zero : EqOn g 0 (Set.Ioo (-1 : ℝ) 1)ᶜ)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_le_one : ∀ x : ℝ, g x ≤ 1)
    (δ : ℝ) (n : ℕ) :
    data.prop35WeightedPoissonSeq g n =
      (∫ x in Set.Icc ((-1 : ℝ) + δ) (1 - δ),
        data.prop35WeightedPoissonIntegrand g n x) +
      ∫ x in prop35EndpointCollar δ,
        data.prop35WeightedPoissonIntegrand g n x := by
  have hint : Integrable (fun x : ℝ => data.prop35WeightedPoissonIntegrand g n x)
      (volume : Measure ℝ) :=
    data.prop35WeightedPoissonIntegrand_integrable
      g hg_cont hg_zero hg_nonneg hg_le_one n
  have hrestrict :
      (∫ x in Set.Icc ((-1 : ℝ) + δ) (1 - δ) ∪ prop35EndpointCollar δ,
        data.prop35WeightedPoissonIntegrand g n x) =
      ∫ x : ℝ, data.prop35WeightedPoissonIntegrand g n x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
    intro x hxnot
    have hxnotI : x ∉ Set.Ioo (-1 : ℝ) 1 := by
      intro hxI
      exact hxnot (prop35_Ioo_subset_interior_union_endpointCollar (δ := δ) hxI)
    exact data.prop35WeightedPoissonIntegrand_eq_zero_of_not_mem_Ioo g hg_zero n hxnotI
  have hsplit :
      (∫ x in Set.Icc ((-1 : ℝ) + δ) (1 - δ) ∪ prop35EndpointCollar δ,
        data.prop35WeightedPoissonIntegrand g n x) =
      (∫ x in Set.Icc ((-1 : ℝ) + δ) (1 - δ),
        data.prop35WeightedPoissonIntegrand g n x) +
      ∫ x in prop35EndpointCollar δ,
        data.prop35WeightedPoissonIntegrand g n x := by
    exact setIntegral_union prop35_interior_disjoint_endpointCollar
      (prop35EndpointCollar_measurableSet δ) hint.integrableOn hint.integrableOn
  rw [data.prop35WeightedPoissonSeq_eq_integral_integrand]
  rw [← hrestrict, hsplit]

/-- Concrete weighted Poisson zero-limit obtained by the interior/collar split. -/
theorem UnitIntervalPickHerglotzUpperRawData.prop35WeightedPoissonSeq_tendsto_zero_concrete
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f)
    (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_zero : EqOn g 0 (Set.Ioo (-1 : ℝ) 1)ᶜ)
    (hg_nonneg : ∀ x : ℝ, 0 ≤ g x)
    (hg_le_one : ∀ x : ℝ, g x ≤ 1) :
    Tendsto (fun n : ℕ => data.prop35WeightedPoissonSeq g n) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let M : ℝ := (data.measure : Measure ℝ).real Set.univ
  let η : ℝ := ε / (8 * (M + 1))
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact ENNReal.toReal_nonneg
  have hηpos : 0 < η := by
    dsimp [η]
    positivity
  rcases prop35_test_small_on_endpoint_collar
      g hg_cont hg_zero hg_nonneg hηpos with
    ⟨δ, hδpos, hsmall⟩
  have hinterior :=
    data.prop35WeightedPoissonInterior_tendsto_zero
      g hg_nonneg hg_le_one hδpos
  have hhalf : 0 < ε / 2 := by positivity
  have hinterior_event := (Metric.tendsto_nhds.mp hinterior) (ε / 2) hhalf
  have hcollar_lt : (η * 4) * M < ε / 2 := by
    have hMlt : M < M + 1 := by linarith
    calc
      (η * 4) * M < (η * 4) * (M + 1) := by
        exact mul_lt_mul_of_pos_left hMlt (by positivity)
      _ = ε / 2 := by
        dsimp [η]
        have hden : 8 * (M + 1) ≠ 0 := by positivity
        field_simp [hden]
        ring
  filter_upwards [hinterior_event] with n hn
  let interior : ℝ :=
    ∫ x in Set.Icc ((-1 : ℝ) + δ) (1 - δ),
      data.prop35WeightedPoissonIntegrand g n x
  let collar : ℝ :=
    ∫ x in prop35EndpointCollar δ,
      data.prop35WeightedPoissonIntegrand g n x
  have hsplit :
      data.prop35WeightedPoissonSeq g n = interior + collar := by
    dsimp [interior, collar]
    exact data.prop35WeightedPoissonSeq_eq_interior_add_endpointCollar
      g hg_cont hg_zero hg_nonneg hg_le_one δ n
  have hinterior_lt : ‖interior‖ < ε / 2 := by
    dsimp [interior]
    simpa [Real.dist_eq] using hn
  have hcollar_le :
      ‖collar‖ ≤ (η * 4) * (data.measure : Measure ℝ).real Set.univ := by
    dsimp [collar]
    exact data.prop35WeightedPoissonEndpointCollar_setIntegral_norm_bound
      g hg_cont hg_nonneg hηpos.le hsmall n
  have hcollar_lt' : ‖collar‖ < ε / 2 := by
    simpa [M] using hcollar_le.trans_lt hcollar_lt
  have hnorm_lt : ‖data.prop35WeightedPoissonSeq g n‖ < ε := by
    calc
      ‖data.prop35WeightedPoissonSeq g n‖ = ‖interior + collar‖ := by rw [hsplit]
      _ ≤ ‖interior‖ + ‖collar‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hinterior_lt hcollar_lt'
      _ = ε := by ring
  simpa [Real.dist_eq] using hnorm_lt

/-- Concrete Proposition 3.5 measure-zero conclusion for the raw Herglotz measure. -/
theorem UnitIntervalPickHerglotzUpperRawData.measure_Ioo_eq_zero_concrete
    {f : ℝ → ℝ} (data : UnitIntervalPickHerglotzUpperRawData f) :
    (data.measure : Measure ℝ) (Set.Ioo (-1 : ℝ) 1) = 0 := by
  refine data.measure_Ioo_eq_zero_of_prop35_limits ?_ ?_
  · intro g hg_cont hg_zero hg_nonneg hg_le_one
    exact data.prop35WeightedPoissonSeq_tendsto_zero_concrete
      g hg_cont hg_zero hg_nonneg hg_le_one
  · intro g hg_cont _hg_zero hg_nonneg hg_le_one
    exact data.prop35FubiniApproxSeq_tendsto_integral_concrete
      g hg_cont hg_nonneg hg_le_one

/-- Concrete producer for the book Proposition 3.5 inversion input. -/
def unitIntervalPickHerglotzProposition35Producer_concrete :
    UnitIntervalPickHerglotzProposition35Producer where
  produce := by
    intro f data
    refine ⟨?_⟩
    intro _hboundary
    exact data.measure_Ioo_eq_zero_concrete

end

end Quantum.TraceInequality.Loewner
