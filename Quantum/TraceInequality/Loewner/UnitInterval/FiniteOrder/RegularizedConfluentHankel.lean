import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.ConfluentHankelC5
import Mathlib.Analysis.Convex.Integral


/-!
# Chapter 20 regularized confluent Hankel package

This file applies the C5 confluent Hankel package to Hiai regularizations and
extracts the local determinant/PSD diagonal bounds used by the finite-order
regularity ladder.
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
open scoped fwdDiff

noncomputable section

/--
Regularized affine pullbacks inherit the confluent three-point Hankel
determinant nonnegativity needed by the `C²` pilot.
-/
theorem hiaiRegularization_affinePullback_confluentLoewnerHankel3_det_nonneg
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r u : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f)
    (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    0 ≤
      (confluentLoewnerHankel3
        (hiaiRegularizationAffinePullback φ ε f x r) u).det := by
  rcases hiaiRegularization_affinePullback_C5_loewnerPosInput
      (φ := φ) (f := f) hφ hε hr hsub hpos with
    ⟨hpull_pos, hpull_c5⟩
  exact
    confluentLoewnerHankel3_det_nonneg_of_loewnerPosOnUnitInterval_C5
      (f := hiaiRegularizationAffinePullback φ ε f x r)
      hpull_pos hpull_c5 hu

/--
Regularized affine pullbacks inherit the full confluent three-point Hankel PSD
matrix, not only its determinant.
-/
theorem hiaiRegularization_affinePullback_confluentLoewnerHankel3_posSemidef
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r u : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f)
    (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    (confluentLoewnerHankel3
      (hiaiRegularizationAffinePullback φ ε f x r) u).PosSemidef := by
  rcases hiaiRegularization_affinePullback_C5_loewnerPosInput
      (φ := φ) (f := f) hφ hε hr hsub hpos with
    ⟨hpull_pos, hpull_c5⟩
  exact
    confluentLoewnerHankel3_posSemidef_of_loewnerPosOnUnitInterval_C5
      (f := hiaiRegularizationAffinePullback φ ε f x r)
      hpull_pos hpull_c5 hu

/--
The affine-coordinate determinant nonnegativity transfers back to the original
regularized coordinate.  The local clip gives a global `C⁵` proxy, so the
generic affine scaling theorem applies without needing global smoothness of the
unclipped regularization.
-/
theorem hiaiRegularization_confluentLoewnerHankel3_det_nonneg
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r u : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f)
    (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    0 ≤
      (confluentLoewnerHankel3
        (fun z : ℝ => hiaiRegularization φ ε f z) (x + r * u)).det := by
  let R : ℝ → ℝ := fun z : ℝ => hiaiRegularization φ ε f z
  let L : ℝ → ℝ :=
    hiaiRegularization φ ε
      (hiaiLocalClip f (x - (ε + r)) (x + (ε + r)))
  let A : ℝ → ℝ := hiaiRegularizationAffinePullback φ ε f x r
  let AL : ℝ → ℝ := fun v : ℝ => L (x + r * v)
  have hleft_mem : x - r ∈ Set.Icc (x - r) (x + r) := by
    constructor
    · rfl
    · linarith [hr]
  have hright_mem : x + r ∈ Set.Icc (x - r) (x + r) := by
    constructor
    · linarith [hr]
    · rfl
  have hleft := hsub hleft_mem
  have hright := hsub hright_mem
  have hη_nonneg : 0 ≤ ε + r := by linarith
  have hxη : x ∈ hiaiRegularizedInterior (ε + r) := by
    dsimp [hiaiRegularizedInterior]
    constructor
    · linarith [hleft.1]
    · linarith [hright.2]
  have hclip : ContDiff ℝ 5 L := by
    dsimp [L]
    exact hiaiRegularization_localClip_contDiff_order5
      (φ := φ) (f := f) (ε := ε) (η := ε + r) (x := x)
      hφ hε hη_nonneg hxη hpos
  have hzsmall : x + r * u ∈ Set.Ioo (x - r) (x + r) := by
    have hmul_left : -r < r * u := by
      nlinarith [mul_lt_mul_of_pos_left hu.1 hr]
    have hmul_right : r * u < r := by
      nlinarith [mul_lt_mul_of_pos_left hu.2 hr]
    constructor <;> linarith
  have hR_eq_L : R =ᶠ[𝓝 (x + r * u)] L := by
    filter_upwards [isOpen_Ioo.mem_nhds hzsmall] with z hz
    dsimp [R, L]
    exact hiaiRegularization_eq_localClip_on_small_interval
      (φ := φ) (f := f) (ε := ε) (δ := r) (x := x) (z := z) hε hz
  have hpre : {v : ℝ | x + r * v ∈ Set.Ioo (x - r) (x + r)} ∈ 𝓝 u := by
    have hcont : ContinuousAt (fun v : ℝ => x + r * v) u := by
      fun_prop
    exact hcont (isOpen_Ioo.mem_nhds hzsmall)
  have hA_eq_AL : A =ᶠ[𝓝 u] AL := by
    filter_upwards [hpre] with v hv
    dsimp [A, AL, L, hiaiRegularizationAffinePullback]
    exact hiaiRegularization_eq_localClip_on_small_interval
      (φ := φ) (f := f) (ε := ε) (δ := r) (x := x) (z := x + r * v) hε hv
  have hA_mat : confluentLoewnerHankel3 A u =
      confluentLoewnerHankel3 AL u :=
    confluentLoewnerHankel3_congr_nhds hA_eq_AL
  have hR_mat : confluentLoewnerHankel3 R (x + r * u) =
      confluentLoewnerHankel3 L (x + r * u) :=
    confluentLoewnerHankel3_congr_nhds hR_eq_L
  have hscaleL :=
    confluentLoewnerHankel3_affinePullback_det_eq
      (F := L) hclip x r u
  have hscaleR :
      (confluentLoewnerHankel3 A u).det =
        r ^ 9 * (confluentLoewnerHankel3 R (x + r * u)).det := by
    rw [hA_mat, hR_mat]
    exact hscaleL
  have haff :=
    hiaiRegularization_affinePullback_confluentLoewnerHankel3_det_nonneg
      (φ := φ) (f := f) hφ hε hr hsub hpos hu
  have haffA : 0 ≤ (confluentLoewnerHankel3 A u).det := by
    simpa [A] using haff
  have hmul_nonneg :
      0 ≤ r ^ 9 * (confluentLoewnerHankel3 R (x + r * u)).det := by
    rw [← hscaleR]
    exact haffA
  have hmul_nonneg' :
      0 ≤ (confluentLoewnerHankel3 R (x + r * u)).det * r ^ 9 := by
    simpa [mul_comm] using hmul_nonneg
  have hrpow : 0 < r ^ 9 := pow_pos hr 9
  have hnonneg : 0 ≤ (confluentLoewnerHankel3 R (x + r * u)).det :=
    nonneg_of_mul_nonneg_left hmul_nonneg' hrpow
  simpa [R] using hnonneg

/--
The affine-coordinate PSD matrix transfers back to the original regularized
coordinate via the same local clip and congruence path as the determinant
version.
-/
theorem hiaiRegularization_confluentLoewnerHankel3_posSemidef
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r u : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f)
    (hu : u ∈ Set.Ioo (-1 : ℝ) 1) :
    (confluentLoewnerHankel3
      (fun z : ℝ => hiaiRegularization φ ε f z) (x + r * u)).PosSemidef := by
  let R : ℝ → ℝ := fun z : ℝ => hiaiRegularization φ ε f z
  let L : ℝ → ℝ :=
    hiaiRegularization φ ε
      (hiaiLocalClip f (x - (ε + r)) (x + (ε + r)))
  let A : ℝ → ℝ := hiaiRegularizationAffinePullback φ ε f x r
  let AL : ℝ → ℝ := fun v : ℝ => L (x + r * v)
  have hleft_mem : x - r ∈ Set.Icc (x - r) (x + r) := by
    constructor
    · rfl
    · linarith [hr]
  have hright_mem : x + r ∈ Set.Icc (x - r) (x + r) := by
    constructor
    · linarith [hr]
    · rfl
  have hleft := hsub hleft_mem
  have hright := hsub hright_mem
  have hη_nonneg : 0 ≤ ε + r := by linarith
  have hxη : x ∈ hiaiRegularizedInterior (ε + r) := by
    dsimp [hiaiRegularizedInterior]
    constructor
    · linarith [hleft.1]
    · linarith [hright.2]
  have hclip : ContDiff ℝ 5 L := by
    dsimp [L]
    exact hiaiRegularization_localClip_contDiff_order5
      (φ := φ) (f := f) (ε := ε) (η := ε + r) (x := x)
      hφ hε hη_nonneg hxη hpos
  have hzsmall : x + r * u ∈ Set.Ioo (x - r) (x + r) := by
    have hmul_left : -r < r * u := by
      nlinarith [mul_lt_mul_of_pos_left hu.1 hr]
    have hmul_right : r * u < r := by
      nlinarith [mul_lt_mul_of_pos_left hu.2 hr]
    constructor
    · linarith
    · linarith
  have hR_eq_L : R =ᶠ[𝓝 (x + r * u)] L := by
    filter_upwards [isOpen_Ioo.mem_nhds hzsmall] with z hz
    dsimp [R, L]
    exact hiaiRegularization_eq_localClip_on_small_interval
      (φ := φ) (f := f) (ε := ε) (δ := r) (x := x) (z := z) hε hz
  have hpre : {v : ℝ | x + r * v ∈ Set.Ioo (x - r) (x + r)} ∈ 𝓝 u := by
    have hcont : ContinuousAt (fun v : ℝ => x + r * v) u := by
      fun_prop
    exact hcont (isOpen_Ioo.mem_nhds hzsmall)
  have hA_eq_AL : A =ᶠ[𝓝 u] AL := by
    filter_upwards [hpre] with v hv
    dsimp [A, AL, L, hiaiRegularizationAffinePullback]
    exact hiaiRegularization_eq_localClip_on_small_interval
      (φ := φ) (f := f) (ε := ε) (δ := r) (x := x) (z := x + r * v) hε hv
  have hA_mat : confluentLoewnerHankel3 A u =
      confluentLoewnerHankel3 AL u :=
    confluentLoewnerHankel3_congr_nhds hA_eq_AL
  have hR_mat : confluentLoewnerHankel3 R (x + r * u) =
      confluentLoewnerHankel3 L (x + r * u) :=
    confluentLoewnerHankel3_congr_nhds hR_eq_L
  have haff :=
    hiaiRegularization_affinePullback_confluentLoewnerHankel3_posSemidef
      (φ := φ) (f := f) hφ hε hr hsub hpos hu
  have hA_psd : (confluentLoewnerHankel3 A u).PosSemidef := by
    simpa [A] using haff
  have hAL_psd : (confluentLoewnerHankel3 AL u).PosSemidef := by
    simpa [hA_mat] using hA_psd
  have hL_psd :
      (confluentLoewnerHankel3 L (x + r * u)).PosSemidef :=
    confluentLoewnerHankel3_posSemidef_of_affinePullback_posSemidef
      (F := L) hclip (x := x) (r := r) (u := u) hr hAL_psd
  have hR_psd : (confluentLoewnerHankel3 R (x + r * u)).PosSemidef := by
    simpa [hR_mat] using hL_psd
  simpa [R] using hR_psd

/--
Local-coordinate form of the regularized confluent Hankel determinant
nonnegativity.  It removes the affine parameter `u` from the main theorem and
is the form used by the next `C²` handoff layer.
-/
theorem hiaiRegularization_confluentLoewnerHankel3_det_nonneg_on_Ioo
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    ∀ y ∈ Set.Ioo (x - r) (x + r),
      0 ≤
        (confluentLoewnerHankel3
          (fun z : ℝ => hiaiRegularization φ ε f z) y).det := by
  intro y hy
  let u : ℝ := (y - x) / r
  have hu : u ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · dsimp [u]
      rw [lt_div_iff₀ hr]
      linarith [hy.1]
    · dsimp [u]
      rw [div_lt_one hr]
      linarith [hy.2]
  have hgeom : x + r * u = y := by
    dsimp [u]
    field_simp [hr.ne']
    ring
  have hdet :=
    hiaiRegularization_confluentLoewnerHankel3_det_nonneg
      (φ := φ) (f := f) hφ hε hr hsub hpos hu
  simpa [hgeom] using hdet

/--
At every interior point, the regularized functions eventually satisfy the
confluent Hankel determinant nonnegativity on one fixed small ball.  This is
the local quantitative input produced by the closed three-point determinant
route.  Local uniform control of the second derivatives is
`hiaiRegularization_secondDeriv_localUniformCauchy_of_loewnerPosOnUnitInterval` in
`SecondDerivativeLimit.lean`.
-/
theorem hiaiRegularization_confluentLoewnerHankel3_det_nonneg_eventually_local
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ ρ : ℝ, 0 < ρ ∧ (-1 : ℝ) < x - ρ ∧ x + ρ < 1 ∧
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x ρ,
          0 ≤
            (confluentLoewnerHankel3
              (fun z : ℝ => hiaiRegularization φ ε f z) y).det := by
  intro x hx
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
  have hε_ltρ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ρ :=
    nhdsWithin_le_nhds (Iio_mem_nhds hρ)
  filter_upwards [self_mem_nhdsWithin, hε_ltρ] with ε hεpos hερ
  intro y hy
  have hε_left_bound : ε + ρ < x + 1 := by
    nlinarith [hερ, hρ_le_left_quarter, hx_left_pos]
  have hε_right_bound : ε + ρ < 1 - x := by
    nlinarith [hερ, hρ_le_right_quarter, hx_right_pos]
  have hsub : Set.Icc (x - ρ) (x + ρ) ⊆ hiaiRegularizedInterior ε := by
    intro z hz
    dsimp [hiaiRegularizedInterior]
    constructor
    · linarith [hz.1, hε_left_bound]
    · linarith [hz.2, hε_right_bound]
  have hyIoo : y ∈ Set.Ioo (x - ρ) (x + ρ) := by
    simpa [Real.ball_eq_Ioo] using hy
  exact
    hiaiRegularization_confluentLoewnerHankel3_det_nonneg_on_Ioo
      (φ := φ) (f := f) hφ hεpos hρ hsub hpos y hyIoo

/-- Local-coordinate form of the regularized confluent Hankel PSD matrix. -/
theorem hiaiRegularization_confluentLoewnerHankel3_posSemidef_on_Ioo
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    ∀ y ∈ Set.Ioo (x - r) (x + r),
      (confluentLoewnerHankel3
        (fun z : ℝ => hiaiRegularization φ ε f z) y).PosSemidef := by
  intro y hy
  let u : ℝ := (y - x) / r
  have hu : u ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · dsimp [u]
      rw [lt_div_iff₀ hr]
      linarith [hy.1]
    · dsimp [u]
      rw [div_lt_one hr]
      linarith [hy.2]
  have hgeom : x + r * u = y := by
    dsimp [u]
    field_simp [hr.ne']
    ring
  have hpsd :=
    hiaiRegularization_confluentLoewnerHankel3_posSemidef
      (φ := φ) (f := f) hφ hε hr hsub hpos hu
  simpa [hgeom] using hpsd

/--
At every interior point, the regularized functions eventually satisfy full
confluent Hankel PSD on one fixed small ball.
-/
theorem hiaiRegularization_confluentLoewnerHankel3_posSemidef_eventually_local
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ ρ : ℝ, 0 < ρ ∧ (-1 : ℝ) < x - ρ ∧ x + ρ < 1 ∧
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x ρ,
          (confluentLoewnerHankel3
            (fun z : ℝ => hiaiRegularization φ ε f z) y).PosSemidef := by
  intro x hx
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
  have hε_ltρ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ρ :=
    nhdsWithin_le_nhds (Iio_mem_nhds hρ)
  filter_upwards [self_mem_nhdsWithin, hε_ltρ] with ε hεpos hερ
  intro y hy
  have hε_left_bound : ε + ρ < x + 1 := by
    nlinarith [hερ, hρ_le_left_quarter, hx_left_pos]
  have hε_right_bound : ε + ρ < 1 - x := by
    nlinarith [hερ, hρ_le_right_quarter, hx_right_pos]
  have hsub : Set.Icc (x - ρ) (x + ρ) ⊆ hiaiRegularizedInterior ε := by
    intro z hz
    dsimp [hiaiRegularizedInterior]
    constructor
    · linarith [hz.1, hε_left_bound]
    · linarith [hz.2, hε_right_bound]
  have hyIoo : y ∈ Set.Ioo (x - ρ) (x + ρ) := by
    simpa [Real.ball_eq_Ioo] using hy
  exact
    hiaiRegularization_confluentLoewnerHankel3_posSemidef_on_Ioo
      (φ := φ) (f := f) hφ hεpos hρ hsub hpos y hyIoo

/--
The eventual local PSD source gives nonnegativity of the middle diagonal entry,
hence nonnegativity of the regularized third derivative.
-/
theorem hiaiRegularization_confluentLoewnerHankel3_middleEntry_nonneg_eventually_local
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ ρ : ℝ, 0 < ρ ∧ (-1 : ℝ) < x - ρ ∧ x + ρ < 1 ∧
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x ρ,
          0 ≤ deriv (deriv (deriv
            (fun z : ℝ => hiaiRegularization φ ε f z))) y := by
  intro x hx
  rcases
    hiaiRegularization_confluentLoewnerHankel3_posSemidef_eventually_local
      (φ := φ) (f := f) hφ hpos x hx with
    ⟨ρ, hρ, hleft, hright, hpsd⟩
  refine ⟨ρ, hρ, hleft, hright, ?_⟩
  filter_upwards [hpsd] with ε hε
  intro y hy
  have hdiag :=
    (hε y hy).diag_nonneg (i := (1 : Fin 3))
  have hentry :
      0 ≤
        deriv (deriv (deriv
          (fun z : ℝ => hiaiRegularization φ ε f z))) y / 6 := by
    simpa [confluentLoewnerHankel3_apply_one_one] using hdiag
  nlinarith

/--
The eventual local PSD source also gives nonnegativity of the lower-right
diagonal entry, hence nonnegativity of the regularized fifth derivative.
-/
theorem hiaiRegularization_confluentLoewnerHankel3_fifthDeriv_nonneg_eventually_local
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ ρ : ℝ, 0 < ρ ∧ (-1 : ℝ) < x - ρ ∧ x + ρ < 1 ∧
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x ρ,
          0 ≤ deriv (deriv (deriv (deriv (deriv
            (fun z : ℝ => hiaiRegularization φ ε f z))))) y := by
  intro x hx
  rcases
    hiaiRegularization_confluentLoewnerHankel3_posSemidef_eventually_local
      (φ := φ) (f := f) hφ hpos x hx with
    ⟨ρ, hρ, hleft, hright, hpsd⟩
  refine ⟨ρ, hρ, hleft, hright, ?_⟩
  filter_upwards [hpsd] with ε hε
  intro y hy
  have hdiag :=
    (hε y hy).diag_nonneg (i := (2 : Fin 3))
  have hentry :
      0 ≤
        deriv (deriv (deriv (deriv (deriv
          (fun z : ℝ => hiaiRegularization φ ε f z))))) y / 120 := by
    simpa [confluentLoewnerHankel3_apply_two_two] using hdiag
  nlinarith

/--
The first-derivative pointwise convergence and the PSD diagonal signs give a
local eventual bound for the ordinary second derivatives of the regularized
functions.  This uses only `Rε' → f'`, the `(0,0)` diagonal nonnegativity, and
the `(1,1)` diagonal convexity source; it does not use second-derivative
pointwise limits.
-/
theorem
    hiaiRegularization_secondDeriv_abs_bound_eventually_local_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ∃ ρ M : ℝ, 0 < ρ ∧ 0 ≤ M ∧
        (-1 : ℝ) < x - 4 * ρ ∧ x + 4 * ρ < 1 ∧
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x ρ,
          |deriv (deriv
            (fun z : ℝ => hiaiRegularization φ ε f z)) y| ≤ M := by
  intro x hx
  rcases
    hiaiRegularization_confluentLoewnerHankel3_posSemidef_eventually_local
      (φ := φ) (f := f) hφ hpos x hx with
    ⟨σ, hσ, hσleft, hσright, hpsdσ⟩
  let ρ : ℝ := σ / 8
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have h4ρ_lt_σ : 4 * ρ < σ := by
    dsimp [ρ]
    linarith [hσ]
  have h2ρ_lt_σ : 2 * ρ < σ := by
    linarith [h4ρ_lt_σ, hρ]
  have hleft4 : (-1 : ℝ) < x - 4 * ρ := by
    linarith [hσleft, h4ρ_lt_σ]
  have hright4 : x + 4 * ρ < 1 := by
    linarith [hσright, h4ρ_lt_σ]
  let a : ℝ := x - 2 * ρ
  let b : ℝ := x + 2 * ρ
  have haIoo : a ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · dsimp [a]
      linarith [hσleft, h2ρ_lt_σ]
    · dsimp [a]
      linarith [hσright, hρ]
  have hbIoo : b ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · dsimp [b]
      linarith [hσleft, hρ]
    · dsimp [b]
      linarith [hσright, h2ρ_lt_σ]
  let B : ℝ := max (|deriv f a| + 1) (|deriv f b| + 1)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  let M : ℝ := B / ρ
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  refine ⟨ρ, M, hρ, hM, hleft4, hright4, ?_⟩
  have hpointA :=
    regularized_deriv_tendsto_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hpos a haIoo
  have hpointB :=
    regularized_deriv_tendsto_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hpos b hbIoo
  have hboundA :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        deriv (fun z : ℝ => hiaiRegularization φ ε f z) a ≤ B := by
    have hnear :=
      hpointA.eventually
        (Metric.ball_mem_nhds (deriv f a) (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hnear] with ε hε
    have habs :
        |deriv (fun z : ℝ => hiaiRegularization φ ε f z) a -
            deriv f a| < 1 := by
      simpa [Real.dist_eq] using hε
    have hle_abs :
        deriv (fun z : ℝ => hiaiRegularization φ ε f z) a -
            deriv f a ≤
          |deriv (fun z : ℝ => hiaiRegularization φ ε f z) a -
            deriv f a| :=
      le_abs_self _
    have hlim_le : deriv f a ≤ |deriv f a| := le_abs_self _
    have hBleft : |deriv f a| + 1 ≤ B := by
      dsimp [B]
      exact le_max_left _ _
    linarith
  have hboundB :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        deriv (fun z : ℝ => hiaiRegularization φ ε f z) b ≤ B := by
    have hnear :=
      hpointB.eventually
        (Metric.ball_mem_nhds (deriv f b) (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hnear] with ε hε
    have habs :
        |deriv (fun z : ℝ => hiaiRegularization φ ε f z) b -
            deriv f b| < 1 := by
      simpa [Real.dist_eq] using hε
    have hle_abs :
        deriv (fun z : ℝ => hiaiRegularization φ ε f z) b -
            deriv f b ≤
          |deriv (fun z : ℝ => hiaiRegularization φ ε f z) b -
            deriv f b| :=
      le_abs_self _
    have hlim_le : deriv f b ≤ |deriv f b| := le_abs_self _
    have hBright : |deriv f b| + 1 ≤ B := by
      dsimp [B]
      exact le_max_right _ _
    linarith
  have hleftMargin : 0 < x - 4 * ρ + 1 := by linarith [hleft4]
  have hrightMargin : 0 < 1 - (x + 4 * ρ) := by linarith [hright4]
  have hε_left : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < x - 4 * ρ + 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds hleftMargin)
  have hε_right : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 - (x + 4 * ρ) :=
    nhdsWithin_le_nhds (Iio_mem_nhds hrightMargin)
  filter_upwards [self_mem_nhdsWithin, hε_left, hε_right, hpsdσ, hboundA, hboundB] with
    ε hεpos hεleft hεright hpsdε hAε hBε
  intro y hy
  let R : ℝ → ℝ := fun w : ℝ => hiaiRegularization φ ε f w
  let Gε : ℝ → ℝ := fun w : ℝ => deriv R w
  have hball4_sub_σ : Metric.ball x (4 * ρ) ⊆ Metric.ball x σ := by
    intro w hw
    exact Metric.mem_ball.mpr <|
      lt_of_lt_of_le (Metric.mem_ball.mp hw) (le_of_lt h4ρ_lt_σ)
  have hball4_reg :
      Metric.ball x (4 * ρ) ⊆ hiaiRegularizedInterior ε := by
    intro w hw
    have hwIoo : w ∈ Set.Ioo (x - 4 * ρ) (x + 4 * ρ) := by
      simpa [Real.ball_eq_Ioo] using hw
    dsimp [hiaiRegularizedInterior]
    constructor
    · linarith [hwIoo.1, hεleft]
    · linarith [hwIoo.2, hεright]
  have hopen : IsOpen (hiaiRegularizedInterior ε) := by
    simpa [hiaiRegularizedInterior] using isOpen_Ioo
  have hC5 :
      ContDiffOn ℝ 5 R (hiaiRegularizedInterior ε) := by
    dsimp [R]
    exact hiaiRegularization_contDiffOn_regularizedInterior_order5
      (φ := φ) (f := f) hφ hεpos hpos
  have hderivC4 :
      ContDiffOn ℝ 4 (deriv R) (hiaiRegularizedInterior ε) := by
    simpa using hC5.deriv_of_isOpen (m := 4) hopen (by decide)
  have hsecondC3 :
      ContDiffOn ℝ 3 (deriv (deriv R))
        (hiaiRegularizedInterior ε) := by
    simpa using hderivC4.deriv_of_isOpen (m := 3) hopen (by decide)
  have hGdiff :
      DifferentiableOn ℝ Gε (Metric.ball x (4 * ρ)) :=
    (hderivC4.mono hball4_reg).differentiableOn (by decide)
  have hGderivDiff :
      DifferentiableOn ℝ (deriv Gε) (Metric.ball x (4 * ρ)) := by
    dsimp [Gε]
    exact (hsecondC3.mono hball4_reg).differentiableOn (by decide)
  have hconv : ConvexOn ℝ (Metric.ball x (4 * ρ)) Gε := by
    refine
      convexOn_of_deriv2_nonneg' (convex_ball x (4 * ρ))
        hGdiff hGderivDiff ?_
    intro w hw
    have hdiag :=
      (hpsdε w (hball4_sub_σ hw)).diag_nonneg (i := (1 : Fin 3))
    have hentry :
        0 ≤ deriv (deriv (deriv R)) w / 6 := by
      dsimp [R]
      simpa [confluentLoewnerHankel3_apply_one_one] using hdiag
    have hthird : 0 ≤ deriv (deriv (deriv R)) w := by
      nlinarith
    simpa [Gε, Function.iterate_succ_apply] using hthird
  have hdiff : ∀ z ∈ Metric.ball x (4 * ρ), DifferentiableAt ℝ Gε z := by
    intro z hz
    exact (hGdiff z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)
  have hnonneg : ∀ z ∈ Metric.ball x (4 * ρ), 0 ≤ Gε z := by
    intro z hz
    have hdiag :=
      (hpsdε z (hball4_sub_σ hz)).diag_nonneg (i := (0 : Fin 3))
    have hentry : 0 ≤ deriv R z := by
      dsimp [R]
      simpa [confluentLoewnerHankel3_apply_zero_zero] using hdiag
    simpa [Gε] using hentry
  have hinner :=
    convex_nonneg_abs_deriv_le_on_inner_ball_of_endpoint_le
      (F := Gε) (x := x) (ρ := ρ) (M := B)
      hρ hB hconv hdiff hnonneg (by simpa [Gε, R, a] using hAε)
      (by simpa [Gε, R, b] using hBε) y hy
  simpa [Gε, R, M] using hinner

/--
The PSD diagonal signs plus first-derivative pointwise convergence give the
local third-derivative bound needed to make `Rε''` locally Lipschitz.  This is
the non-circular replacement for the older pointwise-`Rε''` middle-entry bound.
-/
theorem hiaiRegularization_thirdDeriv_bound_eventually_local_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    (hpos : LoewnerPosOnUnitInterval f) :
    ∀ x ∈ Set.Ioo (-1 : ℝ) 1, ∀ r : ℝ,
      0 < r → Metric.ball x r ⊆ Set.Ioo (-1 : ℝ) 1 →
        (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y ∈ Metric.ball x r,
          0 ≤
            (confluentLoewnerHankel3
              (fun z : ℝ => hiaiRegularization φ ε f z) y).det) →
        ∀ y ∈ Metric.ball x r, ∃ C : ℝ, 0 ≤ C ∧
          ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball y ρ ⊆ Metric.ball x r ∧
            ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ Metric.ball y ρ,
              |deriv (deriv (deriv
                (fun w : ℝ => hiaiRegularization φ ε f w))) z| ≤ C := by
  intro x _hx r _hr hball _hHankel y hy
  have hyIoo : y ∈ Set.Ioo (-1 : ℝ) 1 := hball hy
  rcases
    hiaiRegularization_secondDeriv_abs_bound_eventually_local_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hpos y hyIoo with
    ⟨σ, M, hσ, hM, _hσleft4, _hσright4, hsecondAbs⟩
  rcases
    hiaiRegularization_confluentLoewnerHankel3_posSemidef_eventually_local
      (φ := φ) (f := f) hφ hpos y hyIoo with
    ⟨θ, hθ, hθleft, hθright, hpsdθ⟩
  have hyBallIoo : y ∈ Set.Ioo (x - r) (x + r) := by
    simpa [Real.ball_eq_Ioo] using hy
  let τ : ℝ := min (y - (x - r)) (x + r - y)
  have hτ : 0 < τ := by
    dsimp [τ]
    exact lt_min (by linarith [hyBallIoo.1]) (by linarith [hyBallIoo.2])
  let ρ : ℝ := min (σ / 4) (min (θ / 4) (τ / 4))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hρ_le_σ_quarter : ρ ≤ σ / 4 := by
    dsimp [ρ]
    exact min_le_left _ _
  have hρ_le_θ_quarter : ρ ≤ θ / 4 := by
    dsimp [ρ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ_le_τ_quarter : ρ ≤ τ / 4 := by
    dsimp [ρ]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have h2ρ_lt_σ : 2 * ρ < σ := by nlinarith [hρ_le_σ_quarter, hσ]
  have h2ρ_lt_θ : 2 * ρ < θ := by nlinarith [hρ_le_θ_quarter, hθ]
  have h2ρ_lt_τ : 2 * ρ < τ := by nlinarith [hρ_le_τ_quarter, hτ]
  have hτ_le_left : τ ≤ y - (x - r) := by
    dsimp [τ]
    exact min_le_left _ _
  have hτ_le_right : τ ≤ x + r - y := by
    dsimp [τ]
    exact min_le_right _ _
  have h2ρ_lt_left : 2 * ρ < y - (x - r) :=
    lt_of_lt_of_le h2ρ_lt_τ hτ_le_left
  have h2ρ_lt_right : 2 * ρ < x + r - y :=
    lt_of_lt_of_le h2ρ_lt_τ hτ_le_right
  let a : ℝ := y - 2 * ρ
  let b : ℝ := y + 2 * ρ
  have ha_ball : a ∈ Metric.ball x r := by
    have haIoo : a ∈ Set.Ioo (x - r) (x + r) := by
      dsimp [a]
      constructor <;> linarith
    simpa [Real.ball_eq_Ioo] using haIoo
  have hb_ball : b ∈ Metric.ball x r := by
    have hbIoo : b ∈ Set.Ioo (x - r) (x + r) := by
      dsimp [b]
      constructor <;> linarith
    simpa [Real.ball_eq_Ioo] using hbIoo
  have hρsub : Metric.ball y ρ ⊆ Metric.ball x r := by
    intro z hz
    have hzIoo : z ∈ Set.Ioo (y - ρ) (y + ρ) := by
      simpa [Real.ball_eq_Ioo] using hz
    have hzBallIoo : z ∈ Set.Ioo (x - r) (x + r) := by
      constructor <;> linarith [hzIoo.1, hzIoo.2, h2ρ_lt_left, h2ρ_lt_right, hρ]
    simpa [Real.ball_eq_Ioo] using hzBallIoo
  let A : ℝ := 2 * M
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hoscEv :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        |deriv (deriv
            (fun w : ℝ => hiaiRegularization φ ε f w)) b -
          deriv (deriv
            (fun w : ℝ => hiaiRegularization φ ε f w)) a| ≤ A := by
    filter_upwards [hsecondAbs] with ε hε
    have haσ : a ∈ Metric.ball y σ := by
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp [a]
      rw [abs_of_nonpos (by linarith : y - 2 * ρ - y ≤ 0)]
      linarith
    have hbσ : b ∈ Metric.ball y σ := by
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp [b]
      rw [abs_of_nonneg (by linarith : 0 ≤ y + 2 * ρ - y)]
      linarith
    have ha_bound := hε a haσ
    have hb_bound := hε b hbσ
    have htri :
        |deriv (deriv
            (fun w : ℝ => hiaiRegularization φ ε f w)) b -
          deriv (deriv
            (fun w : ℝ => hiaiRegularization φ ε f w)) a| ≤
          |deriv (deriv
            (fun w : ℝ => hiaiRegularization φ ε f w)) b| +
          |deriv (deriv
            (fun w : ℝ => hiaiRegularization φ ε f w)) a| := by
      simpa [sub_eq_add_neg, abs_neg] using
        abs_add_le
          (deriv (deriv
            (fun w : ℝ => hiaiRegularization φ ε f w)) b)
          (-(deriv (deriv
            (fun w : ℝ => hiaiRegularization φ ε f w)) a))
    dsimp [A]
    linarith
  refine ⟨A / ρ, by positivity, ρ, hρ, hρsub, ?_⟩
  have hleftMargin : 0 < y - θ + 1 := by linarith [hθleft]
  have hrightMargin : 0 < 1 - (y + θ) := by linarith [hθright]
  have hε_left : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < y - θ + 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds hleftMargin)
  have hε_right : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 - (y + θ) :=
    nhdsWithin_le_nhds (Iio_mem_nhds hrightMargin)
  filter_upwards [self_mem_nhdsWithin, hε_left, hε_right, hpsdθ, hoscEv] with
    ε hεpos hεleft hεright hpsdε hoscε
  intro z hz
  let R : ℝ → ℝ := fun w : ℝ => hiaiRegularization φ ε f w
  let Fε : ℝ → ℝ := fun w : ℝ => deriv (deriv (deriv R)) w
  have hball_two_sub_θ : Metric.ball y (2 * ρ) ⊆ Metric.ball y θ := by
    intro w hw
    exact Metric.mem_ball.mpr <|
      lt_of_lt_of_le (Metric.mem_ball.mp hw) (le_of_lt h2ρ_lt_θ)
  have hball_two_reg :
      Metric.ball y (2 * ρ) ⊆ hiaiRegularizedInterior ε := by
    intro w hw
    have hwθ : w ∈ Metric.ball y θ := hball_two_sub_θ hw
    have hwIoo : w ∈ Set.Ioo (y - θ) (y + θ) := by
      simpa [Real.ball_eq_Ioo] using hwθ
    dsimp [hiaiRegularizedInterior]
    constructor
    · linarith [hwIoo.1, hεleft]
    · linarith [hwIoo.2, hεright]
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith [hρ]
  have hIcc_reg : Set.Icc a b ⊆ hiaiRegularizedInterior ε := by
    intro w hw
    have hwθ : w ∈ Set.Ioo (y - θ) (y + θ) := by
      dsimp [a, b] at hw
      constructor <;> linarith [hw.1, hw.2, h2ρ_lt_θ]
    dsimp [hiaiRegularizedInterior]
    constructor
    · linarith [hwθ.1, hεleft]
    · linarith [hwθ.2, hεright]
  have hopen : IsOpen (hiaiRegularizedInterior ε) := by
    simpa [hiaiRegularizedInterior] using isOpen_Ioo
  have hC5 :
      ContDiffOn ℝ 5 R (hiaiRegularizedInterior ε) := by
    dsimp [R]
    exact hiaiRegularization_contDiffOn_regularizedInterior_order5
      (φ := φ) (f := f) hφ hεpos hpos
  have hderivC4 :
      ContDiffOn ℝ 4 (deriv R) (hiaiRegularizedInterior ε) := by
    simpa using hC5.deriv_of_isOpen (m := 4) hopen (by decide)
  have hsecondC3 :
      ContDiffOn ℝ 3 (deriv (deriv R))
        (hiaiRegularizedInterior ε) := by
    simpa using hderivC4.deriv_of_isOpen (m := 3) hopen (by decide)
  have hthirdC2 :
      ContDiffOn ℝ 2 Fε (hiaiRegularizedInterior ε) := by
    dsimp [Fε]
    simpa using hsecondC3.deriv_of_isOpen (m := 2) hopen (by decide)
  have hthirdC2_ball :
      ContDiffOn ℝ 2 Fε (Metric.ball y (2 * ρ)) :=
    hthirdC2.mono hball_two_reg
  have hfourthC1 :
      ContDiffOn ℝ 1 (deriv Fε) (hiaiRegularizedInterior ε) := by
    simpa using hthirdC2.deriv_of_isOpen (m := 1) hopen (by decide)
  have hfourthC1_ball :
      ContDiffOn ℝ 1 (deriv Fε) (Metric.ball y (2 * ρ)) :=
    hfourthC1.mono hball_two_reg
  have hconv : ConvexOn ℝ (Metric.ball y (2 * ρ)) Fε := by
    refine
      convexOn_of_deriv2_nonneg' (convex_ball y (2 * ρ))
        (hthirdC2_ball.differentiableOn (by decide))
        (hfourthC1_ball.differentiableOn (by decide)) ?_
    intro w hw
    have hwθ : w ∈ Metric.ball y θ := hball_two_sub_θ hw
    have hdiag :=
      (hpsdε w hwθ).diag_nonneg (i := (2 : Fin 3))
    have hentry :
        0 ≤ deriv (deriv (deriv (deriv (deriv R)))) w / 120 := by
      dsimp [R]
      simpa [confluentLoewnerHankel3_apply_two_two] using hdiag
    have hfive : 0 ≤ deriv (deriv (deriv (deriv (deriv R)))) w := by
      nlinarith
    simpa [Fε, Function.iterate_succ_apply] using hfive
  have hnonneg : ∀ w ∈ Metric.ball y (2 * ρ), 0 ≤ Fε w := by
    intro w hw
    have hwθ : w ∈ Metric.ball y θ := hball_two_sub_θ hw
    have hdiag :=
      (hpsdε w hwθ).diag_nonneg (i := (1 : Fin 3))
    have hentry :
        0 ≤ deriv (deriv (deriv R)) w / 6 := by
      dsimp [R]
      simpa [confluentLoewnerHankel3_apply_one_one] using hdiag
    dsimp [Fε]
    nlinarith
  have hcont : ContinuousOn Fε (Metric.ball y (2 * ρ)) :=
    hthirdC2_ball.continuousOn
  have hbig_int : IntervalIntegrable Fε volume a b := by
    exact (hthirdC2.continuousOn.mono hIcc_reg).intervalIntegrable_of_Icc hab
  have hsecondC1_Icc :
      ContDiffOn ℝ 1 (deriv (deriv R)) (Set.Icc a b) :=
    (hsecondC3.of_le (by norm_num)).mono hIcc_reg
  have hintegral : ∫ w in a..b, Fε w ≤ A := by
    have hFTC :=
      intervalIntegral.integral_deriv_of_contDiffOn_Icc hsecondC1_Icc hab
    dsimp [Fε, R, a, b] at hFTC ⊢
    rw [hFTC]
    exact (le_abs_self _).trans hoscε
  exact
    convex_nonneg_abs_le_on_inner_ball_of_integral_le
      (F := Fε) (x := y) (ρ := ρ) (A := A)
      hρ hA hconv hnonneg hcont hbig_int hintegral z hz


end

end Quantum.TraceInequality.Loewner
