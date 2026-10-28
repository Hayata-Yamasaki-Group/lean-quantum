import Quantum.Analysis.Calculus.EquicontinuousFamily
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Tactic

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter
open scoped Topology Interval NNReal ENNReal

noncomputable section

/--
Local uniform-Cauchy control for derivative values from pointwise convergence
of primitives and an eventual Lipschitz bound for the derivatives.  The proof
uses a fixed small secant interval around the base point, so the pointwise
primitive convergence is only used at two fixed endpoints.
-/
theorem deriv_family_eventual_local_uniformCauchy_at_of_lipschitzOnWith
    {ι : Type*} {l : Filter ι} [Filter.NeBot l]
    {G F : ι → ℝ → ℝ} {g : ℝ → ℝ} {y ρ K : ℝ}
    (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hpoint :
      ∀ t ∈ Metric.ball y ρ, Filter.Tendsto (fun i : ι => G i t) l (𝓝 (g t)))
    (hderiv :
      ∀ᶠ i in l, ∀ t ∈ Metric.ball y ρ, HasDerivAt (G i) (F i t) t)
    (hLip :
      ∀ᶠ i in l, LipschitzOnWith (Real.toNNReal K) (F i) (Metric.ball y ρ)) :
    ∀ η > 0, ∃ U ∈ 𝓝 y,
      ∀ᶠ i in l, ∀ᶠ j in l, ∀ z ∈ U,
        dist (F i z) (F j z) < η := by
  intro η hη
  let δ : ℝ := min (ρ / 4) (η / (16 * (K + 1)))
  have hK1 : 0 < K + 1 := by linarith
  have hden_small : 0 < 16 * (K + 1) := by positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by positivity) (div_pos hη hden_small)
  have hδ_le_ρ4 : δ ≤ ρ / 4 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ_le_small : δ ≤ η / (16 * (K + 1)) := by
    dsimp [δ]
    exact min_le_right _ _
  have hδ_lt_ρ : δ < ρ := by nlinarith [hδ_le_ρ4, hρ]
  let p : ℝ := y - δ
  let q : ℝ := y + δ
  have hpq : p < q := by
    dsimp [p, q]
    linarith [hδ]
  have hqmp_pos : 0 < q - p := by
    dsimp [p, q]
    linarith [hδ]
  have hp_ball : p ∈ Metric.ball y ρ := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [p]
    rw [abs_of_nonpos (by linarith : y - δ - y ≤ 0)]
    linarith
  have hq_ball : q ∈ Metric.ball y ρ := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [q]
    rw [abs_of_nonneg (by linarith : 0 ≤ y + δ - y)]
    linarith
  let μ : ℝ := η * (q - p) / 16
  have hμ : 0 < μ := by
    dsimp [μ]
    positivity
  have hpclose :
      ∀ᶠ i in l, dist (G i p) (g p) < μ :=
    (Metric.tendsto_nhds.mp (hpoint p hp_ball)) μ hμ
  have hqclose :
      ∀ᶠ i in l, dist (G i q) (g q) < μ :=
    (Metric.tendsto_nhds.mp (hpoint q hq_ball)) μ hμ
  refine ⟨Metric.ball y δ, Metric.ball_mem_nhds y hδ, ?_⟩
  filter_upwards [hderiv, hLip, hpclose, hqclose] with i hiDeriv hiLip hip hiq
  filter_upwards [hderiv, hLip, hpclose, hqclose] with j hjDeriv hjLip hjp hjq
  intro z hz
  have hz_ball : z ∈ Metric.ball y ρ := by
    exact Metric.mem_ball.mpr <| lt_trans (Metric.mem_ball.mp hz) hδ_lt_ρ
  let sec : ι → ℝ := fun i : ι => (G i q - G i p) / (q - p)
  have approx_i : dist (F i z) (sec i) ≤ K * (2 * δ) := by
    have hcont : ContinuousOn (G i) (Set.Icc p q) := by
      intro t ht
      have ht_ball : t ∈ Metric.ball y ρ := by
        have ht_abs : |t - y| ≤ δ := by
          rw [abs_le]
          dsimp [p, q] at ht
          have hleft : y - δ ≤ t := ht.1
          have hright : t ≤ y + δ := ht.2
          constructor <;> linarith
        have ht_dist : dist t y ≤ δ := by
          simpa [Real.dist_eq] using ht_abs
        exact Metric.mem_ball.mpr (lt_of_le_of_lt ht_dist hδ_lt_ρ)
      exact (hiDeriv t ht_ball).continuousAt.continuousWithinAt
    have hderivIoo : ∀ t ∈ Set.Ioo p q, HasDerivAt (G i) (F i t) t := by
      intro t ht
      have ht_ball : t ∈ Metric.ball y ρ := by
        have ht_abs : |t - y| < δ := by
          rw [abs_lt]
          dsimp [p, q] at ht
          have hleft : y - δ < t := ht.1
          have hright : t < y + δ := ht.2
          constructor <;> linarith
        have ht_dist : dist t y < δ := by
          simpa [Real.dist_eq] using ht_abs
        exact Metric.mem_ball.mpr (lt_trans ht_dist hδ_lt_ρ)
      exact hiDeriv t ht_ball
    rcases exists_hasDerivAt_eq_slope (G i) (F i) hpq hcont hderivIoo with
      ⟨c, hc, hc_eq⟩
    have hc_ball : c ∈ Metric.ball y ρ := by
      have hc_abs : |c - y| < δ := by
        rw [abs_lt]
        dsimp [p, q] at hc
        have hleft : y - δ < c := hc.1
        have hright : c < y + δ := hc.2
        constructor <;> linarith
      have hc_dist : dist c y < δ := by
        simpa [Real.dist_eq] using hc_abs
      exact Metric.mem_ball.mpr (lt_trans hc_dist hδ_lt_ρ)
    have hdist_zc : dist z c ≤ 2 * δ := by
      have hz_y : dist z y < δ := Metric.mem_ball.mp hz
      have hc_y : dist c y < δ := by
        rw [Real.dist_eq]
        have hc_abs : |c - y| < δ := by
          rw [abs_lt]
          dsimp [p, q] at hc
          have hleft : y - δ < c := hc.1
          have hright : c < y + δ := hc.2
          constructor <;> linarith
        simpa [Real.dist_eq] using hc_abs
      exact le_of_lt <| by
        calc
        dist z c ≤ dist z y + dist y c := dist_triangle z y c
        _ < δ + δ := add_lt_add hz_y (by simpa [dist_comm] using hc_y)
        _ = 2 * δ := by ring
    have hLip_zc := hiLip.dist_le_mul z hz_ball c hc_ball
    have hLip_zc' : dist (F i z) (F i c) ≤ K * dist z c := by
      simpa [Real.toNNReal_of_nonneg hK] using hLip_zc
    have hc_eq' : F i c = sec i := by
      simpa [sec] using hc_eq
    rw [← hc_eq']
    exact hLip_zc'.trans (mul_le_mul_of_nonneg_left hdist_zc hK)
  have approx_j : dist (F j z) (sec j) ≤ K * (2 * δ) := by
    have hcont : ContinuousOn (G j) (Set.Icc p q) := by
      intro t ht
      have ht_ball : t ∈ Metric.ball y ρ := by
        have ht_abs : |t - y| ≤ δ := by
          rw [abs_le]
          dsimp [p, q] at ht
          have hleft : y - δ ≤ t := ht.1
          have hright : t ≤ y + δ := ht.2
          constructor <;> linarith
        have ht_dist : dist t y ≤ δ := by
          simpa [Real.dist_eq] using ht_abs
        exact Metric.mem_ball.mpr (lt_of_le_of_lt ht_dist hδ_lt_ρ)
      exact (hjDeriv t ht_ball).continuousAt.continuousWithinAt
    have hderivIoo : ∀ t ∈ Set.Ioo p q, HasDerivAt (G j) (F j t) t := by
      intro t ht
      have ht_ball : t ∈ Metric.ball y ρ := by
        have ht_abs : |t - y| < δ := by
          rw [abs_lt]
          dsimp [p, q] at ht
          have hleft : y - δ < t := ht.1
          have hright : t < y + δ := ht.2
          constructor <;> linarith
        have ht_dist : dist t y < δ := by
          simpa [Real.dist_eq] using ht_abs
        exact Metric.mem_ball.mpr (lt_trans ht_dist hδ_lt_ρ)
      exact hjDeriv t ht_ball
    rcases exists_hasDerivAt_eq_slope (G j) (F j) hpq hcont hderivIoo with
      ⟨c, hc, hc_eq⟩
    have hc_ball : c ∈ Metric.ball y ρ := by
      have hc_abs : |c - y| < δ := by
        rw [abs_lt]
        dsimp [p, q] at hc
        have hleft : y - δ < c := hc.1
        have hright : c < y + δ := hc.2
        constructor <;> linarith
      have hc_dist : dist c y < δ := by
        simpa [Real.dist_eq] using hc_abs
      exact Metric.mem_ball.mpr (lt_trans hc_dist hδ_lt_ρ)
    have hdist_zc : dist z c ≤ 2 * δ := by
      have hz_y : dist z y < δ := Metric.mem_ball.mp hz
      have hc_y : dist c y < δ := by
        rw [Real.dist_eq]
        have hc_abs : |c - y| < δ := by
          rw [abs_lt]
          dsimp [p, q] at hc
          have hleft : y - δ < c := hc.1
          have hright : c < y + δ := hc.2
          constructor <;> linarith
        simpa [Real.dist_eq] using hc_abs
      exact le_of_lt <| by
        calc
        dist z c ≤ dist z y + dist y c := dist_triangle z y c
        _ < δ + δ := add_lt_add hz_y (by simpa [dist_comm] using hc_y)
        _ = 2 * δ := by ring
    have hLip_zc := hjLip.dist_le_mul z hz_ball c hc_ball
    have hLip_zc' : dist (F j z) (F j c) ≤ K * dist z c := by
      simpa [Real.toNNReal_of_nonneg hK] using hLip_zc
    have hc_eq' : F j c = sec j := by
      simpa [sec] using hc_eq
    rw [← hc_eq']
    exact hLip_zc'.trans (mul_le_mul_of_nonneg_left hdist_zc hK)
  have hp_pair : dist (G i p) (G j p) < 2 * μ := by
    have htri : dist (G i p) (G j p) ≤
        dist (G i p) (g p) + dist (g p) (G j p) :=
      dist_triangle _ _ _
    have hjp' : dist (g p) (G j p) < μ := by
      simpa [dist_comm] using hjp
    linarith
  have hq_pair : dist (G i q) (G j q) < 2 * μ := by
    have htri : dist (G i q) (G j q) ≤
        dist (G i q) (g q) + dist (g q) (G j q) :=
      dist_triangle _ _ _
    have hjq' : dist (g q) (G j q) < μ := by
      simpa [dist_comm] using hjq
    linarith
  have hsec_le :
      dist (sec i) (sec j) ≤
        (dist (G i q) (G j q) + dist (G i p) (G j p)) / (q - p) := by
    have hdiff :
        sec i - sec j =
          ((G i q - G j q) - (G i p - G j p)) / (q - p) := by
      dsimp [sec]
      field_simp [hqmp_pos.ne']
      ring
    rw [Real.dist_eq, hdiff, abs_div]
    have habsden : |q - p| = q - p := abs_of_pos hqmp_pos
    rw [habsden]
    refine div_le_div_of_nonneg_right ?_ hqmp_pos.le
    calc
      |(G i q - G j q) - (G i p - G j p)|
          ≤ |G i q - G j q| + |G j p - G i p| := by
            simpa [sub_eq_add_neg] using
              abs_add_le (G i q - G j q) (G j p - G i p)
      _ = |G i q - G j q| + |G i p - G j p| := by
            rw [abs_sub_comm (G j p) (G i p)]
      _ = dist (G i q) (G j q) + dist (G i p) (G j p) := by
            simp [Real.dist_eq]
  have hsec_lt : dist (sec i) (sec j) < η / 4 := by
    have hnum_lt :
        dist (G i q) (G j q) + dist (G i p) (G j p) < 4 * μ := by
      linarith
    have hdiv_lt :
        (dist (G i q) (G j q) + dist (G i p) (G j p)) / (q - p) <
          (4 * μ) / (q - p) :=
      div_lt_div_of_pos_right hnum_lt hqmp_pos
    have htarget : (4 * μ) / (q - p) = η / 4 := by
      dsimp [μ]
      field_simp [hqmp_pos.ne']
      ring
    exact lt_of_le_of_lt hsec_le (by simpa [htarget] using hdiv_lt)
  have happrox_small : K * (2 * δ) ≤ η / 8 := by
    have hδ_nonneg : 0 ≤ δ := le_of_lt hδ
    have hK_le : K ≤ K + 1 := by linarith
    have hmul_le : K * (2 * δ) ≤ (K + 1) * (2 * δ) :=
      mul_le_mul_of_nonneg_right hK_le (by positivity)
    have hsmall : (K + 1) * (2 * δ) ≤ (K + 1) * (2 * (η / (16 * (K + 1)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδ_le_small (by norm_num))
        (by linarith)
    have htarget :
        (K + 1) * (2 * (η / (16 * (K + 1)))) = η / 8 := by
      field_simp [hK1.ne']
      ring
    exact hmul_le.trans (by simpa [htarget] using hsmall)
  have htri :
      dist (F i z) (F j z) ≤
        dist (F i z) (sec i) +
          (dist (sec i) (sec j) + dist (sec j) (F j z)) := by
    calc
      dist (F i z) (F j z)
          ≤ dist (F i z) (sec i) + dist (sec i) (F j z) :=
        dist_triangle _ _ _
      _ ≤ dist (F i z) (sec i) +
            (dist (sec i) (sec j) + dist (sec j) (F j z)) := by
        exact add_le_add le_rfl (dist_triangle _ _ _)
  have approx_j' : dist (sec j) (F j z) ≤ K * (2 * δ) := by
    simpa [dist_comm] using approx_j
  linarith

/--
Every interior point of the normalized interval admits a symmetric ball whose
closed endpoints stay inside the interval.  This is the fixed local geometry
used by the C² handoff scaffolding.
-/
theorem exists_Ioo_ball_data {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ (-1 : ℝ) < x - ρ ∧ x + ρ < 1 ∧
      Metric.ball x ρ ⊆ Set.Ioo (-1 : ℝ) 1 := by
  let m : ℝ := min (x + 1) (1 - x)
  let ρ : ℝ := m / 4
  have hx_left_pos : 0 < x + 1 := by linarith [hx.1]
  have hx_right_pos : 0 < 1 - x := by linarith [hx.2]
  have hm_pos : 0 < m := by
    dsimp [m]
    exact lt_min hx_left_pos hx_right_pos
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρ_le_left_quarter : ρ ≤ (x + 1) / 4 := by
    dsimp [ρ, m]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hρ_le_right_quarter : ρ ≤ (1 - x) / 4 := by
    dsimp [ρ, m]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hleft : (-1 : ℝ) < x - ρ := by
    nlinarith [hρ_le_left_quarter, hx_left_pos]
  have hright : x + ρ < 1 := by
    nlinarith [hρ_le_right_quarter, hx_right_pos]
  refine ⟨ρ, hρ, hleft, hright, ?_⟩
  intro y hy
  have hyIoo : y ∈ Set.Ioo (x - ρ) (x + ρ) := by
    simpa [Real.ball_eq_Ioo] using hy
  constructor
  · exact lt_trans hleft hyIoo.1
  · exact lt_trans hyIoo.2 hright

/--
Local uniform-Cauchy control of a family gives pointwise Cauchy control at any
point of the local set.  This metric helper isolates the filter bookkeeping
needed before taking the `limUnder` limit.
-/
theorem pointwise_cauchy_of_eventual_local_uniformCauchy
    {ι : Type*} {l : Filter ι} [Filter.NeBot l]
    {F : ι → ℝ → ℝ} {x r y : ℝ}
    (hy : y ∈ Metric.ball x r)
    (hcauchy :
      ∀ η > 0, ∀ y ∈ Metric.ball x r,
        ∃ U ∈ 𝓝[Metric.ball x r] y,
          ∀ᶠ i in l, ∀ᶠ j in l, ∀ z ∈ U,
            dist (F i z) (F j z) < η) :
    Cauchy (Filter.map (fun i : ι => F i y) l) := by
  rw [Metric.cauchy_iff]
  refine ⟨Filter.NeBot.map inferInstance (fun i : ι => F i y), ?_⟩
  intro η hη
  have hη2 : 0 < η / 2 := by linarith
  rcases hcauchy (η / 2) hη2 y hy with ⟨U, hU, hUcauchy⟩
  have hyU : y ∈ U := mem_of_mem_nhdsWithin hy hU
  have hclose :
      ∀ᶠ i in l, ∀ᶠ j in l, dist (F i y) (F j y) < η / 2 := by
    filter_upwards [hUcauchy] with i hi
    filter_upwards [hi] with j hj
    exact hj y hyU
  rcases hclose.exists with ⟨i₀, hi₀⟩
  refine ⟨Metric.ball (F i₀ y) (η / 2), ?_, ?_⟩
  · exact hi₀.mono (fun j hj => by simpa [Metric.mem_ball, dist_comm] using hj)
  · intro a ha b hb
    have ha' : dist a (F i₀ y) < η / 2 := by
      simpa [Metric.mem_ball, dist_comm] using ha
    have hb' : dist (F i₀ y) b < η / 2 := by
      simpa [Metric.mem_ball, dist_comm] using hb
    have htri : dist a b ≤ dist a (F i₀ y) + dist (F i₀ y) b :=
      dist_triangle _ _ _
    linarith

/--
Pointwise convergence plus eventual local uniform-Cauchy control gives locally
uniform convergence.  This is the abstract filter interface used by the C²
regularity proof; the uniform-Cauchy estimate itself is
`hiaiRegularization_secondDeriv_localUniformCauchy_of_loewnerPosOnUnitInterval`
(`SecondDerivativeLimit.lean`).
-/
theorem tendstoLocallyUniformlyOn_of_eventual_local_uniformCauchy_and_pointwise
    {ι : Type*} {l : Filter ι} [Filter.NeBot l]
    {F : ι → ℝ → ℝ} {G : ℝ → ℝ} {s : Set ℝ}
    (hpoint :
      ∀ x ∈ s, Filter.Tendsto (fun i : ι => F i x) l (𝓝 (G x)))
    (hcauchy :
      ∀ η > 0, ∀ x ∈ s, ∃ U ∈ 𝓝[s] x,
        ∀ᶠ i in l, ∀ᶠ j in l, ∀ y ∈ U,
          dist (F i y) (F j y) < η) :
    TendstoLocallyUniformlyOn F G l s := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro η hη x hx
  have hη2 : 0 < η / 2 := by linarith
  rcases hcauchy (η / 2) hη2 x hx with ⟨U, hU, hUcauchy⟩
  let V : Set ℝ := U ∩ s
  have hV : V ∈ 𝓝[s] x := inter_mem hU self_mem_nhdsWithin
  refine ⟨V, hV, ?_⟩
  filter_upwards [hUcauchy] with i hi
  intro y hy
  have hyU : y ∈ U := hy.1
  have hys : y ∈ s := hy.2
  have hclose_limit :
      ∀ᶠ j in l, dist (F j y) (G y) < η / 2 :=
    (Metric.tendsto_nhds.mp (hpoint y hys)) (η / 2) hη2
  have hclose_i :
      ∀ᶠ j in l, dist (F i y) (F j y) < η / 2 :=
    hi.mono (fun j hj => hj y hyU)
  rcases (hclose_i.and hclose_limit).exists with ⟨j, hij, hjlim⟩
  have htri :
      dist (G y) (F i y) ≤ dist (G y) (F j y) + dist (F j y) (F i y) :=
    dist_triangle _ _ _
  have hlim' : dist (G y) (F j y) < η / 2 := by
    simpa [dist_comm] using hjlim
  have hij' : dist (F j y) (F i y) < η / 2 := by
    simpa [dist_comm] using hij
  linarith

/--
Pointwise convergence plus eventual local Lipschitz control gives the eventual
local uniform-Cauchy control used by the C² pilot.
-/
theorem eventual_local_uniformCauchy_of_eventual_local_lipschitz_and_pointwise_tendsto
    {ι : Type*} {l : Filter ι} [Filter.NeBot l]
    {F : ι → ℝ → ℝ} {G : ℝ → ℝ} {s : Set ℝ}
    (hpoint :
      ∀ x ∈ s, Filter.Tendsto (fun i : ι => F i x) l (𝓝 (G x)))
    (hLip :
      ∀ x ∈ s, ∃ C : ℝ, 0 ≤ C ∧ ∃ U ∈ 𝓝[s] x,
        ∀ᶠ i in l, ∀ y ∈ U,
          dist (F i y) (F i x) ≤ C * dist y x) :
    ∀ η > 0, ∀ x ∈ s, ∃ U ∈ 𝓝[s] x,
      ∀ᶠ i in l, ∀ᶠ j in l, ∀ y ∈ U,
        dist (F i y) (F j y) < η := by
  intro η hη x hx
  rcases hLip x hx with ⟨C, hC, U, hU, hLipU⟩
  let δ : ℝ := η / (6 * (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hden : 0 < 6 * (C + 1) := by positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos hη hden
  let V : Set ℝ := U ∩ Metric.ball x δ
  have hball : Metric.ball x δ ∈ 𝓝[s] x :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds x hδ)
  refine ⟨V, inter_mem hU hball, ?_⟩
  have hclose :
      ∀ᶠ i in l, dist (F i x) (G x) < η / 3 :=
    (Metric.tendsto_nhds.mp (hpoint x hx)) (η / 3) (by linarith)
  filter_upwards [hLipU, hclose] with i hiLip hiClose
  filter_upwards [hLipU, hclose] with j hjLip hjClose
  intro y hy
  have hyU : y ∈ U := hy.1
  have hydist : dist y x < δ := by
    simpa [V, Metric.mem_ball] using hy.2
  have hdist_le : dist y x ≤ δ := le_of_lt hydist
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ
  have hC_le : C ≤ C + 1 := by linarith
  have hmul_le : C * dist y x ≤ C * δ :=
    mul_le_mul_of_nonneg_left hdist_le hC
  have hmul_le' : C * δ ≤ (C + 1) * δ :=
    mul_le_mul_of_nonneg_right hC_le hδ_nonneg
  have hscale : (C + 1) * δ = η / 6 := by
    dsimp [δ]
    field_simp [hC1.ne']
  have hi_bound : dist (F i y) (F i x) ≤ η / 6 := by
    calc
      dist (F i y) (F i x) ≤ C * dist y x := hiLip y hyU
      _ ≤ C * δ := hmul_le
      _ ≤ (C + 1) * δ := hmul_le'
      _ = η / 6 := hscale
  have hj_bound : dist (F j x) (F j y) ≤ η / 6 := by
    have hj_bound' : dist (F j y) (F j x) ≤ η / 6 := by
      calc
        dist (F j y) (F j x) ≤ C * dist y x := hjLip y hyU
        _ ≤ C * δ := hmul_le
        _ ≤ (C + 1) * δ := hmul_le'
        _ = η / 6 := hscale
    simpa [dist_comm] using hj_bound'
  have hcenter : dist (F i x) (F j x) < 2 * η / 3 := by
    have htri :
        dist (F i x) (F j x) ≤
          dist (F i x) (G x) + dist (G x) (F j x) :=
      dist_triangle _ _ _
    have hjClose' : dist (G x) (F j x) < η / 3 := by
      simpa [dist_comm] using hjClose
    linarith
  have htri :
      dist (F i y) (F j y) ≤
        dist (F i y) (F i x) +
          (dist (F i x) (F j x) + dist (F j x) (F j y)) := by
    calc
      dist (F i y) (F j y)
          ≤ dist (F i y) (F i x) + dist (F i x) (F j y) :=
        dist_triangle _ _ _
      _ ≤ dist (F i y) (F i x) +
            (dist (F i x) (F j x) + dist (F j x) (F j y)) := by
        have htri2 :
            dist (F i x) (F j y) ≤
              dist (F i x) (F j x) + dist (F j x) (F j y) :=
          dist_triangle _ _ _
        exact add_le_add le_rfl htri2
  linarith

/-! ### Pointwise and Lipschitz Cauchy bridge -/

/--
Local third-derivative bounds give the local Lipschitz input for the C² pilot.
For each base point, the producer may choose a smaller ball and a local
constant; Mathlib's mean-value Lipschitz theorem does the metric bookkeeping on
that convex ball.
-/
theorem eventual_local_lipschitz_of_eventual_hasDerivAt_bound_on_ball
    {ι : Type*} {l : Filter ι}
    {F F' : ι → ℝ → ℝ} {x r : ℝ}
    (hderiv :
      ∀ᶠ i in l, ∀ z ∈ Metric.ball x r,
        HasDerivAt (F i) (F' i z) z)
    (hbound :
      ∀ y ∈ Metric.ball x r, ∃ C : ℝ, 0 ≤ C ∧
        ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball y ρ ⊆ Metric.ball x r ∧
          ∀ᶠ i in l, ∀ z ∈ Metric.ball y ρ, |F' i z| ≤ C) :
    ∀ y ∈ Metric.ball x r, ∃ C : ℝ, 0 ≤ C ∧
      ∃ U ∈ 𝓝[Metric.ball x r] y,
        ∀ᶠ i in l, ∀ z ∈ U,
          dist (F i z) (F i y) ≤ C * dist z y := by
  intro y hy
  rcases hbound y hy with ⟨C, hC, ρ, hρ, hball, hboundρ⟩
  refine ⟨C, hC, Metric.ball y ρ,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds y hρ), ?_⟩
  filter_upwards [hderiv, hboundρ] with i hiDeriv hiBound
  intro z hz
  have hyρ : y ∈ Metric.ball y ρ := Metric.mem_ball_self hρ
  have hLip :
      LipschitzOnWith (Real.toNNReal C) (F i) (Metric.ball y ρ) := by
    refine (convex_ball y ρ).lipschitzOnWith_of_nnnorm_deriv_le ?_ ?_
    · intro w hw
      exact (hiDeriv w (hball hw)).differentiableAt
    · intro w hw
      have hderiv_eq : deriv (F i) w = F' i w :=
        (hiDeriv w (hball hw)).deriv
      rw [← NNReal.coe_le_coe, Real.toNNReal_of_nonneg hC,
        coe_nnnorm, Real.norm_eq_abs, hderiv_eq]
      exact hiBound w hw
  have hdist := hLip.dist_le_mul z hz y hyρ
  simpa [Real.toNNReal_of_nonneg hC] using hdist

/-! ### Hankel hlocal handoff interfaces -/

end

end Quantum.TraceInequality.Loewner
