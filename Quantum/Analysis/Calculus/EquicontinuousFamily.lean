import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.Tactic

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter
open scoped Topology Interval NNReal ENNReal

noncomputable section

/-- A fixed mollifier variable turns the ordinary derivative into the scaled difference quotient. -/
theorem diffQuot_tendsto_deriv_mul_neg
    {f : ℝ → ℝ} {x D t : ℝ} (hAt : HasDerivAt f D x) :
    Tendsto
      (fun ε : ℝ => (f (x - ε * t) - f x) / ε)
      (𝓝[>] (0 : ℝ)) (𝓝 ((-t) * D)) := by
  by_cases ht : t = 0
  · subst t
    simp
  · have hto :
        Tendsto (fun ε : ℝ => -ε * t) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have hcont : ContinuousAt (fun ε : ℝ => -ε * t) 0 := by
          fun_prop
        simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        have hεpos : 0 < ε := hε
        simp [ht, hεpos.ne']
    have hbase := hAt.tendsto_slope_zero.comp hto
    have hmul : Tendsto
        (fun ε : ℝ =>
          (-t) * (((-ε * t)⁻¹) * (f (x + (-ε * t)) - f x)))
        (𝓝[>] (0 : ℝ)) (𝓝 ((-t) * D)) := by
      simpa using hbase.const_mul (-t)
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεpos : 0 < ε := hε
    have hεne : ε ≠ 0 := hεpos.ne'
    field_simp [hεne, ht]
    ring_nf

/--
Differentiability at `x` gives a uniform bound for the scaled difference
quotients sampled by `x - ε t`, uniformly for `t ∈ [-1,1]` and small positive
`ε`.
-/
theorem diffQuot_abs_le_eventually_uniform_Icc
    {f : ℝ → ℝ} {x D : ℝ} (hAt : HasDerivAt f D x) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ⦃ε t : ℝ⦄, 0 < ε → ε < δ → t ∈ Set.Icc (-1 : ℝ) 1 →
        |(f (x - ε * t) - f x) / ε| ≤ |D| + 1 := by
  let C : ℝ := |D| + 1
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  have h_event :
      {h : ℝ | |h⁻¹ * (f (x + h) - f x)| ≤ C} ∈ 𝓝[≠] (0 : ℝ) := by
    have hball :
        Metric.ball D 1 ∈ 𝓝 D := Metric.ball_mem_nhds D (by norm_num)
    filter_upwards [hAt.tendsto_slope_zero hball] with h hh
    let q : ℝ := h⁻¹ * (f (x + h) - f x)
    have hdist : |q - D| < 1 := by
      simpa [Real.dist_eq, q] using hh
    calc
      |h⁻¹ * (f (x + h) - f x)| = |(q - D) + D| := by
          dsimp [q]
          ring_nf
      _ ≤ |q - D| + |D| := abs_add_le _ _
      _ ≤ 1 + |D| := add_le_add_left hdist.le |D|
      _ = C := by
          dsimp [C]
          ring_nf
  rcases Metric.mem_nhdsWithin_iff.1 h_event with ⟨δ, hδpos, hδsub⟩
  refine ⟨δ, hδpos, ?_⟩
  intro ε t hεpos hεδ htIcc
  by_cases ht : t = 0
  · subst t
    have hnonneg : 0 ≤ |D| + 1 := by positivity
    simpa using hnonneg
  · let h : ℝ := -ε * t
    have hεne : ε ≠ 0 := hεpos.ne'
    have htne : t ≠ 0 := ht
    have habst : |t| ≤ 1 := by
      exact abs_le.2 ⟨htIcc.1, htIcc.2⟩
    have hdist : dist h 0 < δ := by
      have habsh : |h| = ε * |t| := by
        dsimp [h]
        rw [abs_mul, abs_neg, abs_of_pos hεpos]
      rw [Real.dist_eq, sub_zero, habsh]
      calc
        ε * |t| ≤ ε * 1 := mul_le_mul_of_nonneg_left habst hεpos.le
        _ = ε := by ring_nf
        _ < δ := hεδ
    have hne : h ∈ ({0}ᶜ : Set ℝ) := by
      dsimp [h]
      simp [hεne, htne]
    have hqbound : |h⁻¹ * (f (x + h) - f x)| ≤ C :=
      hδsub ⟨hdist, hne⟩
    have hrel :
        (f (x - ε * t) - f x) / ε =
          (-t) * (h⁻¹ * (f (x + h) - f x)) := by
      dsimp [h]
      field_simp [hεne, htne]
      ring_nf
    rw [hrel]
    calc
      |(-t) * (h⁻¹ * (f (x + h) - f x))|
          = |t| * |h⁻¹ * (f (x + h) - f x)| := by
              rw [abs_mul, abs_neg]
      _ ≤ 1 * C := by
          exact mul_le_mul habst hqbound (abs_nonneg _) (by norm_num)
      _ = |D| + 1 := by
          dsimp [C]
          ring_nf

/--
Differentiation under the Hiai regularization integral, stated with the
dominated-derivative hypotheses required by Mathlib's parametric integral API.
This is the analytic input needed for the diagonal Löwner-kernel entry.
-/
theorem hiaiRegularization_hasDerivAt_of_dominated_deriv
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
    HasDerivAt
      (fun z : ℝ => ∫ t in (-1 : ℝ)..1, φ t * f (z - ε * t))
      (∫ t in (-1 : ℝ)..1, φ t * deriv f (x - ε * t)) x := by
  let μ : Measure ℝ := volume.restrict (Ι (-1 : ℝ) 1)
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ)
      (F := fun z t : ℝ => φ t * f (z - ε * t))
      (F' := fun z t : ℝ => φ t * deriv f (z - ε * t))
      (bound := bound) (x₀ := x) (s := s)
      hs hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
  simpa [μ, intervalIntegral.intervalIntegral_eq_integral_uIoc] using h.2

/--
Pointwise convergence plus eventual local equicontinuity transfers continuity
from a regularized family to the pointwise limit.  This is the abstract
`ε ↓ 0` handoff used below; it is intentionally independent of the Hiai
regularization details.
-/
theorem continuousAt_of_eventual_equi_tendsto
    {ι : Type*} {l : Filter ι} [Filter.NeBot l]
    {F : ι → ℝ → ℝ} {g : ℝ → ℝ} {x : ℝ}
    (hx_tendsto : Filter.Tendsto (fun ε : ι => F ε x) l (𝓝 (g x)))
    (hnear_tendsto :
      ∀ᶠ y in 𝓝 x, Filter.Tendsto (fun ε : ι => F ε y) l (𝓝 (g y)))
    (hequi :
      ∀ η > 0, ∃ U ∈ 𝓝 x,
        ∀ᶠ ε in l, ∀ y ∈ U, dist (F ε y) (F ε x) < η) :
    ContinuousAt g x := by
  change Filter.Tendsto g (𝓝 x) (𝓝 (g x))
  rw [Metric.tendsto_nhds]
  intro η hη
  have hη3 : 0 < η / 3 := by linarith
  rcases hequi (η / 3) hη3 with ⟨U, hU, hequiU⟩
  filter_upwards [hnear_tendsto, hU] with y hy_tendsto hyU
  have hy_close :
      ∀ᶠ ε in l, dist (F ε y) (g y) < η / 3 :=
    (Metric.tendsto_nhds.mp hy_tendsto) (η / 3) hη3
  have hx_close :
      ∀ᶠ ε in l, dist (F ε x) (g x) < η / 3 :=
    (Metric.tendsto_nhds.mp hx_tendsto) (η / 3) hη3
  rcases (hy_close.and (hx_close.and hequiU)).exists with
    ⟨ε, hyε, hxε, hequiε⟩
  have htri :
      dist (g y) (g x) ≤
        dist (g y) (F ε y) +
          (dist (F ε y) (F ε x) + dist (F ε x) (g x)) := by
    calc
      dist (g y) (g x)
          ≤ dist (g y) (F ε y) + dist (F ε y) (g x) :=
        dist_triangle _ _ _
      _ ≤ dist (g y) (F ε y) +
            (dist (F ε y) (F ε x) + dist (F ε x) (g x)) := by
        have htri2 :
            dist (F ε y) (g x) ≤
              dist (F ε y) (F ε x) + dist (F ε x) (g x) :=
          dist_triangle _ _ _
        exact add_le_add le_rfl htri2
  have hequi_y : dist (F ε y) (F ε x) < η / 3 := hequiε y hyU
  have hyε' : dist (g y) (F ε y) < η / 3 := by
    simpa [dist_comm] using hyε
  linarith

/--
An eventual local Lipschitz estimate is enough to provide the eventual local
equicontinuity input used by the `ε ↓ 0` transfer.  This keeps the next analytic
producer focused on a quantitative local bound rather than on filter
bookkeeping.
-/
theorem eventual_equi_of_eventual_local_lipschitz
    {ι : Type*} {l : Filter ι}
    {F : ι → ℝ → ℝ} {x : ℝ}
    (hLip :
      ∃ C : ℝ, 0 ≤ C ∧ ∃ U ∈ 𝓝 x,
        ∀ᶠ i in l, ∀ y ∈ U, dist (F i y) (F i x) ≤ C * dist y x) :
    ∀ η > 0, ∃ U ∈ 𝓝 x,
      ∀ᶠ i in l, ∀ y ∈ U, dist (F i y) (F i x) < η := by
  intro η hη
  rcases hLip with ⟨C, hC, U, hU, hLipU⟩
  let δ : ℝ := η / (2 * (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hden : 0 < 2 * (C + 1) := by positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos hη hden
  let V : Set ℝ := U ∩ Metric.ball x δ
  refine ⟨V, inter_mem hU (Metric.ball_mem_nhds x hδ), ?_⟩
  filter_upwards [hLipU] with i hi
  intro y hy
  have hyU : y ∈ U := hy.1
  have hydist : dist y x < δ := by
    simpa [V, Metric.mem_ball] using hy.2
  have hdist_le : dist y x ≤ δ := le_of_lt hydist
  have hmul_le : C * dist y x ≤ C * δ :=
    mul_le_mul_of_nonneg_left hdist_le hC
  have hC_le : C ≤ C + 1 := by linarith
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ
  have hmul_le' : C * δ ≤ (C + 1) * δ :=
    mul_le_mul_of_nonneg_right hC_le hδ_nonneg
  have hhalf : (C + 1) * δ = η / 2 := by
    dsimp [δ]
    field_simp [hC1.ne']
  have hbound : C * dist y x < η := by
    calc
      C * dist y x ≤ C * δ := hmul_le
      _ ≤ (C + 1) * δ := hmul_le'
      _ = η / 2 := hhalf
      _ < η := by linarith
  exact lt_of_le_of_lt (hi y hyU) hbound

/--
Mathlib's `LipschitzOnWith` interface supplies the local Lipschitz estimate
used by the `ε ↓ 0` transfer, provided the chosen neighborhood contains the
base point.
-/
theorem eventual_local_lipschitz_of_lipschitzOnWith
    {ι : Type*} {l : Filter ι}
    {F : ι → ℝ → ℝ} {x : ℝ}
    (hLip :
      ∃ K : ℝ≥0, ∃ U ∈ 𝓝 x, x ∈ U ∧
        ∀ᶠ i in l, LipschitzOnWith K (F i) U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ U ∈ 𝓝 x,
      ∀ᶠ i in l, ∀ y ∈ U, dist (F i y) (F i x) ≤ C * dist y x := by
  rcases hLip with ⟨K, U, hU, hxU, hLipU⟩
  refine ⟨(K : ℝ), K.2, U, hU, ?_⟩
  filter_upwards [hLipU] with i hi
  intro y hy
  exact hi.dist_le_mul y hy x hxU

end

end Quantum.TraceInequality.Loewner
