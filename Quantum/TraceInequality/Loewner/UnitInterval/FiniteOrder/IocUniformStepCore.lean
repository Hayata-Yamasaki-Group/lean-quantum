import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.IocStepCore

/-!
# Chapter 20 uniform Ioc step approximation

This file contains the uniform half-open mesh construction and the convergence
handoff from finite Ioc step approximants to the window-local Stieltjes/BV
pairing used in the finite-order regularity ladder.
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

/-- Width of the uniform half-open mesh on `[x - ε, x + ε]`. -/
noncomputable def hiaiIocUniformStepWidth (ε : ℝ) (n : ℕ) : ℝ :=
  (2 * ε) / ((n + 1 : ℕ) : ℝ)

/-- Left endpoint of the `k`-th interval in the uniform half-open mesh. -/
noncomputable def hiaiIocUniformStepLeft
    (ε x : ℝ) (n k : ℕ) : ℝ :=
  x - ε + (k : ℝ) * hiaiIocUniformStepWidth ε n

/-- Right endpoint of the `k`-th interval in the uniform half-open mesh. -/
noncomputable def hiaiIocUniformStepRight
    (ε x : ℝ) (n k : ℕ) : ℝ :=
  hiaiIocUniformStepLeft ε x n k +
    hiaiIocUniformStepWidth ε n

/-- Right-endpoint sample value of the scaled weight on the uniform mesh. -/
noncomputable def hiaiIocUniformStepWeight
    (φ : ℝ → ℝ) (ε x : ℝ) (n k : ℕ) : ℝ :=
  hiaiScaledMollifierWeight φ ε x
    (hiaiIocUniformStepRight ε x n k)

/--
Uniform half-open step approximation to the scaled weight.  The index type is
kept as `ℕ` with support `Finset.range (n + 1)` so that it can feed the
fixed-index finite-step handoff above.
-/
noncomputable def hiaiIocUniformStepFunction
    (φ : ℝ → ℝ) (ε x : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (Set.Ioc
        (hiaiIocUniformStepLeft ε x n k)
        (hiaiIocUniformStepRight ε x n k)).indicator
      (fun _ : ℝ => hiaiIocUniformStepWeight φ ε x n k) y

/--
Left-endpoint representative on the same uniform half-open mesh.  This is the
Lebesgue-side step function that appears after finite summation by parts in the
Stieltjes/BV pairing argument.
-/
noncomputable def hiaiIocUniformStepLeftRep
    (G : ℝ → ℝ) (ε x : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (Set.Ioc
        (hiaiIocUniformStepLeft ε x n k)
        (hiaiIocUniformStepRight ε x n k)).indicator
      (fun _ : ℝ => G (hiaiIocUniformStepLeft ε x n k)) y

/-- The uniform mesh width is nonnegative when the radius is nonnegative. -/
theorem hiaiIocUniformStepWidth_nonneg
    {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    0 ≤ hiaiIocUniformStepWidth ε n := by
  have hden : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  unfold hiaiIocUniformStepWidth
  exact div_nonneg (mul_nonneg (by norm_num) hε) hden

/-- The uniform mesh width is positive when the radius is positive. -/
theorem hiaiIocUniformStepWidth_pos
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    0 < hiaiIocUniformStepWidth ε n := by
  have hden : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  unfold hiaiIocUniformStepWidth
  exact div_pos (mul_pos (by norm_num) hε) hden

/-- Each uniform atom has ordered left and right endpoints. -/
theorem hiaiIocUniformStep_left_le_right
    {ε x : ℝ} (hε : 0 ≤ ε) (n k : ℕ) :
    hiaiIocUniformStepLeft ε x n k ≤
      hiaiIocUniformStepRight ε x n k := by
  unfold hiaiIocUniformStepRight
  exact le_add_of_nonneg_right
    (hiaiIocUniformStepWidth_nonneg (ε := ε) hε n)

/-- The right endpoint of an atom is the next left endpoint. -/
theorem hiaiIocUniformStep_right_eq_next_left
    (ε x : ℝ) (n k : ℕ) :
    hiaiIocUniformStepRight ε x n k =
      hiaiIocUniformStepLeft ε x n (k + 1) := by
  unfold hiaiIocUniformStepRight hiaiIocUniformStepLeft
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

/-- The uniform mesh width tends to zero as the number of atoms tends to infinity. -/
theorem hiaiIocUniformStepWidth_tendsto_zero
    (ε : ℝ) :
    Tendsto (fun n : ℕ => hiaiIocUniformStepWidth ε n)
      atTop (𝓝 0) := by
  have hden :
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    exact
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp
        (tendsto_add_atTop_nat 1)
  simpa [hiaiIocUniformStepWidth] using
    (hden.const_div_atTop (2 * ε))

/-- Every point in a valid uniform atom lies in the regularization window. -/
theorem hiaiIocUniformStep_mem_window_of_mem_atom
    {ε x : ℝ} (hε : 0 ≤ ε) {n k : ℕ} (hk : k ∈ Finset.range (n + 1))
    {y : ℝ}
    (hy : y ∈ Set.Ioc
      (hiaiIocUniformStepLeft ε x n k)
      (hiaiIocUniformStepRight ε x n k)) :
    y ∈ Set.Ioc (x - ε) (x + ε) := by
  have hwidth_nonneg : 0 ≤ hiaiIocUniformStepWidth ε n :=
    hiaiIocUniformStepWidth_nonneg (ε := ε) hε n
  have hleft_ge :
      x - ε ≤ hiaiIocUniformStepLeft ε x n k := by
    unfold hiaiIocUniformStepLeft
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) hwidth_nonneg)
  have hksucc : k + 1 ≤ n + 1 := by
    have hklt : k < n + 1 := Finset.mem_range.mp hk
    omega
  have hksucc_cast : ((k + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast hksucc
  have hden_pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hquot_nonneg : 0 ≤ (2 * ε) / ((n + 1 : ℕ) : ℝ) := by
    exact div_nonneg (mul_nonneg (by norm_num) hε) hden_pos.le
  have hmul_le :
      ((k + 1 : ℕ) : ℝ) *
          ((2 * ε) / ((n + 1 : ℕ) : ℝ)) ≤
        ((n + 1 : ℕ) : ℝ) *
          ((2 * ε) / ((n + 1 : ℕ) : ℝ)) := by
    exact mul_le_mul_of_nonneg_right hksucc_cast hquot_nonneg
  have hden_ne : ((n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hden_pos
  have hmul_eval :
      ((n + 1 : ℕ) : ℝ) *
          ((2 * ε) / ((n + 1 : ℕ) : ℝ)) = 2 * ε := by
    field_simp [hden_ne]
  have hstep_le : (hiaiIocUniformStepRight ε x n k) ≤ x + ε := by
    rw [hiaiIocUniformStep_right_eq_next_left]
    unfold hiaiIocUniformStepLeft hiaiIocUniformStepWidth
    rw [hmul_eval] at hmul_le
    nlinarith
  exact ⟨lt_of_le_of_lt hleft_ge hy.1, le_trans hy.2 hstep_le⟩

/-- The uniform step approximation vanishes off the half-open window. -/
theorem hiaiIocUniformStepFunction_zero_off_window
    {φ : ℝ → ℝ} {ε x : ℝ} (hε : 0 ≤ ε) (n : ℕ) {y : ℝ}
    (hy : y ∉ Set.Ioc (x - ε) (x + ε)) :
    hiaiIocUniformStepFunction φ ε x n y = 0 := by
  classical
  unfold hiaiIocUniformStepFunction
  refine Finset.sum_eq_zero fun k hk => ?_
  by_cases hatom : y ∈ Set.Ioc
      (hiaiIocUniformStepLeft ε x n k)
      (hiaiIocUniformStepRight ε x n k)
  · have hywin :=
      hiaiIocUniformStep_mem_window_of_mem_atom
        (ε := ε) (x := x) hε hk hatom
    exact (hy hywin).elim
  · exact Set.indicator_of_notMem hatom _

/-- The whole-space integral of the uniform step restricts to its window. -/
theorem hiaiIocUniformStepFunction_integral_eq_Ioc
    (μ : Measure ℝ) {φ : ℝ → ℝ} {ε x : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    (∫ y, hiaiIocUniformStepFunction φ ε x n y ∂μ) =
      ∫ y in Set.Ioc (x - ε) (x + ε),
        hiaiIocUniformStepFunction φ ε x n y ∂μ := by
  have hzero : ∀ y : ℝ, y ∉ Set.Ioc (x - ε) (x + ε) →
      hiaiIocUniformStepFunction φ ε x n y = 0 := by
    intro y hy
    exact hiaiIocUniformStepFunction_zero_off_window
      (φ := φ) hε n hy
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := μ) (s := Set.Ioc (x - ε) (x + ε))
    (f := fun y : ℝ => hiaiIocUniformStepFunction φ ε x n y)
    hzero).symm

/-- The finite uniform step function is integrable against any Stieltjes measure. -/
theorem hiaiIocUniformStepFunction_integrable_stieltjes
    (G : StieltjesFunction ℝ) {φ : ℝ → ℝ} {ε x : ℝ} (n : ℕ) :
    Integrable (hiaiIocUniformStepFunction φ ε x n) G.measure := by
  classical
  unfold hiaiIocUniformStepFunction
  exact integrable_finset_sum (Finset.range (n + 1)) fun k hk => by
    have hμ :
        G.measure
            (Set.Ioc
              (hiaiIocUniformStepLeft ε x n k)
              (hiaiIocUniformStepRight ε x n k)) ≠ ⊤ := by
      rw [StieltjesFunction.measure_Ioc]
      exact ENNReal.ofReal_ne_top
    exact
      (integrableOn_const (μ := G.measure)
        (s := Set.Ioc
          (hiaiIocUniformStepLeft ε x n k)
          (hiaiIocUniformStepRight ε x n k))
        (C := hiaiIocUniformStepWeight φ ε x n k) hμ).integrable_indicator
        measurableSet_Ioc

/--
The Stieltjes integral of the uniform step is the finite sum of weighted
Stieltjes increments over the atoms.
-/
theorem hiaiIocUniformStepFunction_integral_eval
    (G : StieltjesFunction ℝ) {φ : ℝ → ℝ} {ε x : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    (∫ y, hiaiIocUniformStepFunction φ ε x n y ∂G.measure) =
      ∑ k ∈ Finset.range (n + 1),
        hiaiIocUniformStepWeight φ ε x n k *
          (G (hiaiIocUniformStepRight ε x n k) -
            G (hiaiIocUniformStepLeft ε x n k)) := by
  exact
    stieltjesFunction_integral_finite_ioc_const_sum
      (s := Finset.range (n + 1)) G
      (a := fun k : ℕ => hiaiIocUniformStepLeft ε x n k)
      (b := fun k : ℕ => hiaiIocUniformStepRight ε x n k)
      (c := fun k : ℕ => hiaiIocUniformStepWeight φ ε x n k)
      (fun k _hk => hiaiIocUniformStep_left_le_right
        (ε := ε) (x := x) hε n k)

/-- The length of each uniform atom is exactly the mesh width. -/
theorem hiaiIocUniformStepRight_sub_left
    (ε x : ℝ) (n k : ℕ) :
    hiaiIocUniformStepRight ε x n k -
        hiaiIocUniformStepLeft ε x n k =
      hiaiIocUniformStepWidth ε n := by
  unfold hiaiIocUniformStepRight
  ring

/-- The right endpoint of a valid uniform atom lies in the compact window. -/
theorem hiaiIocUniformStep_right_mem_window
    {ε x : ℝ} (hε : 0 < ε) {n k : ℕ}
    (hk : k ∈ Finset.range (n + 1)) :
    hiaiIocUniformStepRight ε x n k ∈
      Set.Icc (x - ε) (x + ε) := by
  have hwidth_pos :
      0 < hiaiIocUniformStepWidth ε n :=
    hiaiIocUniformStepWidth_pos (ε := ε) hε n
  have hatom :
      hiaiIocUniformStepRight ε x n k ∈
        Set.Ioc
          (hiaiIocUniformStepLeft ε x n k)
          (hiaiIocUniformStepRight ε x n k) := by
    unfold hiaiIocUniformStepRight
    exact ⟨by linarith, le_rfl⟩
  have hwin :=
    hiaiIocUniformStep_mem_window_of_mem_atom
      (ε := ε) (x := x) hε.le hk hatom
  exact ⟨hwin.1.le, hwin.2⟩

/--
If a point lies in one atom, then its distance to the right endpoint of that
atom is bounded by the mesh width.
-/
theorem hiaiIocUniformStep_dist_right_le_width_of_mem_atom
    {ε x : ℝ} (hε : 0 ≤ ε) {n k : ℕ} {y : ℝ}
    (hy : y ∈ Set.Ioc
      (hiaiIocUniformStepLeft ε x n k)
      (hiaiIocUniformStepRight ε x n k)) :
    dist y (hiaiIocUniformStepRight ε x n k) ≤
      hiaiIocUniformStepWidth ε n := by
  have hwidth_nonneg :
      0 ≤ hiaiIocUniformStepWidth ε n :=
    hiaiIocUniformStepWidth_nonneg (ε := ε) hε n
  have hright_sub_nonneg :
      0 ≤ hiaiIocUniformStepRight ε x n k - y := by
    exact sub_nonneg.mpr hy.2
  have hdist :
      dist y (hiaiIocUniformStepRight ε x n k) =
        hiaiIocUniformStepRight ε x n k - y := by
    rw [Real.dist_eq]
    have hsub :
        y - hiaiIocUniformStepRight ε x n k =
          -(hiaiIocUniformStepRight ε x n k - y) := by
      ring
    rw [hsub, abs_neg, abs_of_nonneg hright_sub_nonneg]
  have hle :
      hiaiIocUniformStepRight ε x n k - y ≤
        hiaiIocUniformStepRight ε x n k -
          hiaiIocUniformStepLeft ε x n k := by
    exact sub_le_sub_left hy.1.le _
  rw [hdist]
  exact hle.trans_eq (hiaiIocUniformStepRight_sub_left ε x n k)

/--
If a point lies in one atom, then its distance from the left endpoint of that
atom is bounded by the mesh width.  This is the left-endpoint counterpart of
the right-endpoint estimate used for the scaled-weight approximation.
-/
theorem hiaiIocUniformStep_left_dist_le_width_of_mem_atom
    {ε x : ℝ} (hε : 0 ≤ ε) {n k : ℕ} {y : ℝ}
    (hy : y ∈ Set.Ioc
      (hiaiIocUniformStepLeft ε x n k)
      (hiaiIocUniformStepRight ε x n k)) :
    dist (hiaiIocUniformStepLeft ε x n k) y ≤
      hiaiIocUniformStepWidth ε n := by
  have _hwidth_nonneg :
      0 ≤ hiaiIocUniformStepWidth ε n :=
    hiaiIocUniformStepWidth_nonneg (ε := ε) hε n
  have hleft_sub_nonneg :
      0 ≤ y - hiaiIocUniformStepLeft ε x n k := by
    exact sub_nonneg.mpr hy.1.le
  have hdist :
      dist (hiaiIocUniformStepLeft ε x n k) y =
        y - hiaiIocUniformStepLeft ε x n k := by
    rw [Real.dist_eq]
    have hsub :
        hiaiIocUniformStepLeft ε x n k - y =
          -(y - hiaiIocUniformStepLeft ε x n k) := by
      ring
    rw [hsub, abs_neg, abs_of_nonneg hleft_sub_nonneg]
  have hle :
      y - hiaiIocUniformStepLeft ε x n k ≤
        hiaiIocUniformStepRight ε x n k -
          hiaiIocUniformStepLeft ε x n k := by
    exact sub_le_sub_right hy.2 _
  rw [hdist]
  exact hle.trans_eq (hiaiIocUniformStepRight_sub_left ε x n k)

/--
Every point in the half-open window belongs to one atom of the uniform `Ioc`
mesh.  The atom is chosen using `Nat.ceil`, which matches the right-endpoint
sampling convention.
-/
theorem hiaiIocUniformStep_exists_atom_of_mem_window
    {ε x : ℝ} (hε : 0 < ε) {n : ℕ} {y : ℝ}
    (hy : y ∈ Set.Ioc (x - ε) (x + ε)) :
    ∃ k ∈ Finset.range (n + 1),
      y ∈ Set.Ioc
        (hiaiIocUniformStepLeft ε x n k)
        (hiaiIocUniformStepRight ε x n k) := by
  let w := hiaiIocUniformStepWidth ε n
  let r := (y - (x - ε)) / w
  let m : ℕ := Nat.ceil r
  have hw_pos : 0 < w := hiaiIocUniformStepWidth_pos (ε := ε) hε n
  have hr_pos : 0 < r := by
    dsimp [r]
    exact div_pos (sub_pos.mpr hy.1) hw_pos
  have hN_pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hNw : ((n + 1 : ℕ) : ℝ) * w = 2 * ε := by
    dsimp [w, hiaiIocUniformStepWidth]
    field_simp [ne_of_gt hN_pos]
  have hr_le_N : r ≤ ((n + 1 : ℕ) : ℝ) := by
    dsimp [r]
    rw [div_le_iff₀ hw_pos]
    rw [hNw]
    have hdiff_le : y - (x - ε) ≤ 2 * ε := by
      linarith [hy.2]
    exact hdiff_le
  have hm_pos : 1 ≤ m := by
    dsimp [m]
    exact (Nat.one_le_ceil_iff (R := ℝ)).2 hr_pos
  have hm_ne : m ≠ 0 := by omega
  have hm_le_N : m ≤ n + 1 := by
    dsimp [m]
    exact (Nat.ceil_le (α := ℝ) (a := r) (n := n + 1)).2 hr_le_N
  let k : ℕ := m - 1
  have hk_range : k ∈ Finset.range (n + 1) := by
    rw [Finset.mem_range]
    dsimp [k]
    omega
  have hm_props :
      ((m - 1 : ℕ) : ℝ) < r ∧ r ≤ (m : ℝ) := by
    exact (Nat.ceil_eq_iff (R := ℝ) (a := r) (n := m) hm_ne).1 rfl
  refine ⟨k, hk_range, ?_⟩
  have hk_succ_cast : (((k + 1 : ℕ) : ℝ)) = (m : ℝ) := by
    have hk_succ : k + 1 = m := by
      dsimp [k]
      omega
    exact_mod_cast hk_succ
  have hleft_lt : hiaiIocUniformStepLeft ε x n k < y := by
    have hmul : ((k : ℝ) * w) < y - (x - ε) := by
      have hcast : (k : ℝ) = ((m - 1 : ℕ) : ℝ) := rfl
      have h := mul_lt_mul_of_pos_right (by simpa [hcast, r] using hm_props.1) hw_pos
      rw [div_mul_cancel₀ _ hw_pos.ne'] at h
      simpa [r] using h
    dsimp [hiaiIocUniformStepLeft, k]
    linarith
  have hy_le_right : y ≤ hiaiIocUniformStepRight ε x n k := by
    have hmul : y - (x - ε) ≤ (m : ℝ) * w := by
      have h := mul_le_mul_of_nonneg_right hm_props.2 hw_pos.le
      rw [div_mul_cancel₀ _ hw_pos.ne'] at h
      simpa [r] using h
    have hright_eq :
        hiaiIocUniformStepRight ε x n k =
          x - ε + ((k + 1 : ℕ) : ℝ) * w := by
      dsimp [hiaiIocUniformStepRight, hiaiIocUniformStepLeft, w]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring
    rw [hright_eq, hk_succ_cast]
    linarith
  exact ⟨hleft_lt, hy_le_right⟩

/-- Left endpoints of the uniform mesh are monotone in the atom index. -/
theorem hiaiIocUniformStepLeft_mono
    {ε x : ℝ} (hε : 0 ≤ ε) {n j k : ℕ} (hjk : j ≤ k) :
    hiaiIocUniformStepLeft ε x n j ≤
      hiaiIocUniformStepLeft ε x n k := by
  have hwidth_nonneg :
      0 ≤ hiaiIocUniformStepWidth ε n :=
    hiaiIocUniformStepWidth_nonneg (ε := ε) hε n
  have hjk_cast : (j : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hjk
  have hmul :
      (j : ℝ) * hiaiIocUniformStepWidth ε n ≤
        (k : ℝ) * hiaiIocUniformStepWidth ε n :=
    mul_le_mul_of_nonneg_right hjk_cast hwidth_nonneg
  unfold hiaiIocUniformStepLeft
  linarith

/-- Distinct uniform half-open mesh atoms are disjoint. -/
theorem hiaiIocUniformStep_atoms_disjoint
    {ε x : ℝ} (hε : 0 ≤ ε) {n j k : ℕ} (hjk : j ≠ k) :
    Disjoint
      (Set.Ioc
        (hiaiIocUniformStepLeft ε x n j)
        (hiaiIocUniformStepRight ε x n j))
      (Set.Ioc
        (hiaiIocUniformStepLeft ε x n k)
        (hiaiIocUniformStepRight ε x n k)) := by
  rw [Set.disjoint_left]
  intro y hyj hyk
  rcases lt_or_gt_of_ne hjk with hlt | hgt
  · have hright_le_left :
        hiaiIocUniformStepRight ε x n j ≤
          hiaiIocUniformStepLeft ε x n k := by
      rw [hiaiIocUniformStep_right_eq_next_left]
      exact hiaiIocUniformStepLeft_mono
        (ε := ε) (x := x) hε (Nat.succ_le_of_lt hlt)
    exact (not_lt_of_ge (hyj.2.trans hright_le_left)) hyk.1
  · have hright_le_left :
        hiaiIocUniformStepRight ε x n k ≤
          hiaiIocUniformStepLeft ε x n j := by
      rw [hiaiIocUniformStep_right_eq_next_left]
      exact hiaiIocUniformStepLeft_mono
        (ε := ε) (x := x) hε (Nat.succ_le_of_lt hgt)
    exact (not_lt_of_ge (hyk.2.trans hright_le_left)) hyj.1

/-- Evaluation of the uniform step function on an atom. -/
theorem hiaiIocUniformStepFunction_eq_weight_of_mem_atom
    {φ : ℝ → ℝ} {ε x : ℝ} (hε : 0 ≤ ε) {n k : ℕ}
    (hk : k ∈ Finset.range (n + 1)) {y : ℝ}
    (hy : y ∈ Set.Ioc
      (hiaiIocUniformStepLeft ε x n k)
      (hiaiIocUniformStepRight ε x n k)) :
    hiaiIocUniformStepFunction φ ε x n y =
      hiaiIocUniformStepWeight φ ε x n k := by
  classical
  unfold hiaiIocUniformStepFunction
  rw [Finset.sum_eq_single k]
  · simp [Set.indicator_of_mem hy]
  · intro j hj hne
    have hnot : y ∉ Set.Ioc
        (hiaiIocUniformStepLeft ε x n j)
        (hiaiIocUniformStepRight ε x n j) := by
      intro hyj
      have hd :=
        hiaiIocUniformStep_atoms_disjoint
          (ε := ε) (x := x) hε (n := n) (j := j) (k := k) hne
      rw [Set.disjoint_left] at hd
      exact hd hyj hy
    simp [Set.indicator_of_notMem hnot]
  · intro hknot
    exact (hknot hk).elim

/-- Atom evaluation rewritten as the scaled weight at the right endpoint. -/
theorem hiaiIocUniformStepFunction_eq_scaledWeight_at_right_of_mem_atom
    {φ : ℝ → ℝ} {ε x : ℝ} (hε : 0 ≤ ε) {n k : ℕ}
    (hk : k ∈ Finset.range (n + 1)) {y : ℝ}
    (hy : y ∈ Set.Ioc
      (hiaiIocUniformStepLeft ε x n k)
      (hiaiIocUniformStepRight ε x n k)) :
    hiaiIocUniformStepFunction φ ε x n y =
      hiaiScaledMollifierWeight φ ε x
        (hiaiIocUniformStepRight ε x n k) := by
  simpa [hiaiIocUniformStepWeight] using
    hiaiIocUniformStepFunction_eq_weight_of_mem_atom
      (φ := φ) (ε := ε) (x := x) hε hk hy

/-- Evaluation of the left-endpoint representative on an atom. -/
theorem hiaiIocUniformStepLeftRep_eq_value_of_mem_atom
    {G : ℝ → ℝ} {ε x : ℝ} (hε : 0 ≤ ε) {n k : ℕ}
    (hk : k ∈ Finset.range (n + 1)) {y : ℝ}
    (hy : y ∈ Set.Ioc
      (hiaiIocUniformStepLeft ε x n k)
      (hiaiIocUniformStepRight ε x n k)) :
    hiaiIocUniformStepLeftRep G ε x n y =
      G (hiaiIocUniformStepLeft ε x n k) := by
  classical
  unfold hiaiIocUniformStepLeftRep
  rw [Finset.sum_eq_single k]
  · simp [Set.indicator_of_mem hy]
  · intro j hj hne
    have hnot : y ∉ Set.Ioc
        (hiaiIocUniformStepLeft ε x n j)
        (hiaiIocUniformStepRight ε x n j) := by
      intro hyj
      have hd :=
        hiaiIocUniformStep_atoms_disjoint
          (ε := ε) (x := x) hε (n := n) (j := j) (k := k) hne
      rw [Set.disjoint_left] at hd
      exact hd hyj hy
    simp [Set.indicator_of_notMem hnot]
  · intro hknot
    exact (hknot hk).elim

/-- The scaled mollifier weight is continuous in the original variable. -/
theorem hiaiScaledMollifierWeight_continuous
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ) {ε x : ℝ} :
    Continuous fun y : ℝ => hiaiScaledMollifierWeight φ ε x y := by
  have harg : Continuous fun y : ℝ => (x - y) / ε := by
    fun_prop
  have hφcont : Continuous φ := hφ.smooth.continuous
  simpa [hiaiScaledMollifierWeight] using
    continuous_const.mul (hφcont.comp harg)

/-- The scaled mollifier weight is uniformly continuous on the compact window. -/
theorem hiaiScaledMollifierWeight_uniformContinuousOn_window
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ) {ε x : ℝ} :
    UniformContinuousOn
      (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y)
      (Set.Icc (x - ε) (x + ε)) := by
  exact isCompact_Icc.uniformContinuousOn_of_continuous
    (hiaiScaledMollifierWeight_continuous
      (φ := φ) (ε := ε) (x := x) hφ).continuousOn

/--
Uniform approximation of the scaled weight by the uniform half-open steps,
conditional on the elementary atom-cover/evaluation data for the mesh.

This isolates the purely geometric step: locate the unique half-open
atom containing each point of `(x - ε, x + ε]` and evaluate the finite indicator
sum there.  The version with this step proved is
`hiaiIocUniformStepFunction_uniformApprox_scaledWeight` below.
-/
theorem hiaiIocUniformStepFunction_uniformApprox_scaledWeight_of_atomCover
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hatom :
      ∀ᶠ n in atTop, ∀ y ∈ Set.Ioc (x - ε) (x + ε),
        ∃ k ∈ Finset.range (n + 1),
          y ∈ Set.Ioc
            (hiaiIocUniformStepLeft ε x n k)
            (hiaiIocUniformStepRight ε x n k) ∧
          hiaiIocUniformStepFunction φ ε x n y =
            hiaiIocUniformStepWeight φ ε x n k) :
    ∀ δ > 0, ∀ᶠ n in atTop,
      ∀ y ∈ Set.Ioc (x - ε) (x + ε),
        |hiaiIocUniformStepFunction φ ε x n y -
          hiaiScaledMollifierWeight φ ε x y| ≤ δ := by
  intro δ hδ
  rcases Metric.uniformContinuousOn_iff_le.1
      (hiaiScaledMollifierWeight_uniformContinuousOn_window
        (φ := φ) (ε := ε) (x := x) hφ)
      δ hδ with ⟨η, hη_pos, hη⟩
  have hwidth_small :
      ∀ᶠ n in atTop, hiaiIocUniformStepWidth ε n ≤ η := by
    have hlt :
        ∀ᶠ n in atTop, hiaiIocUniformStepWidth ε n < η :=
      (tendsto_order.1
        (hiaiIocUniformStepWidth_tendsto_zero ε)).2 η hη_pos
    exact hlt.mono fun _ hn => hn.le
  filter_upwards [hatom, hwidth_small] with n hcover hwidth_le y hy
  rcases hcover y hy with ⟨k, hk, hyatom, hS⟩
  have hyIcc : y ∈ Set.Icc (x - ε) (x + ε) := ⟨hy.1.le, hy.2⟩
  have hrightIcc :
      hiaiIocUniformStepRight ε x n k ∈
        Set.Icc (x - ε) (x + ε) :=
    hiaiIocUniformStep_right_mem_window
      (ε := ε) (x := x) hε hk
  have hdist :
      dist y (hiaiIocUniformStepRight ε x n k) ≤ η :=
    (hiaiIocUniformStep_dist_right_le_width_of_mem_atom
      (ε := ε) (x := x) hε.le hyatom).trans hwidth_le
  have hWdist :
      dist
        (hiaiScaledMollifierWeight φ ε x y)
        (hiaiScaledMollifierWeight φ ε x
          (hiaiIocUniformStepRight ε x n k)) ≤ δ :=
    hη y hyIcc
      (hiaiIocUniformStepRight ε x n k) hrightIcc hdist
  rw [hS]
  simpa [hiaiIocUniformStepWeight, Real.dist_eq, abs_sub_comm] using hWdist

/--
Uniform approximation of the scaled weight by the concrete uniform half-open
step functions.
-/
theorem hiaiIocUniformStepFunction_uniformApprox_scaledWeight
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) :
    ∀ δ > 0, ∀ᶠ n in atTop,
      ∀ y ∈ Set.Ioc (x - ε) (x + ε),
        |hiaiIocUniformStepFunction φ ε x n y -
          hiaiScaledMollifierWeight φ ε x y| ≤ δ := by
  refine
    hiaiIocUniformStepFunction_uniformApprox_scaledWeight_of_atomCover
      (φ := φ) (ε := ε) (x := x) hφ hε ?_
  exact Eventually.of_forall fun n y hy => by
    rcases hiaiIocUniformStep_exists_atom_of_mem_window
        (ε := ε) (x := x) hε (n := n) hy with
      ⟨k, hk, hyatom⟩
    exact ⟨k, hk, hyatom,
      hiaiIocUniformStepFunction_eq_weight_of_mem_atom
        (φ := φ) (ε := ε) (x := x) hε.le hk hyatom⟩

/--
Uniform pointwise control on the half-open window bounds the `L¹` error with
respect to any measure by `δ` times the window mass.
-/
theorem hiaiIocUniformStepFunction_lintegral_enorm_sub_le
    (μ : Measure ℝ) {φ : ℝ → ℝ} {ε x δ : ℝ} (n : ℕ)
    (hbound :
      ∀ y ∈ Set.Ioc (x - ε) (x + ε),
        |hiaiIocUniformStepFunction φ ε x n y -
          hiaiScaledMollifierWeight φ ε x y| ≤ δ) :
    (∫⁻ y in Set.Ioc (x - ε) (x + ε),
        ‖hiaiIocUniformStepFunction φ ε x n y -
          hiaiScaledMollifierWeight φ ε x y‖ₑ ∂μ) ≤
      ENNReal.ofReal δ * μ (Set.Ioc (x - ε) (x + ε)) := by
  have hae :
      (fun y : ℝ =>
        ‖hiaiIocUniformStepFunction φ ε x n y -
          hiaiScaledMollifierWeight φ ε x y‖ₑ) ≤ᵐ[
          μ.restrict (Set.Ioc (x - ε) (x + ε))]
        fun _ => ENNReal.ofReal δ := by
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun y hy => by
      have hnorm :
          ‖hiaiIocUniformStepFunction φ ε x n y -
            hiaiScaledMollifierWeight φ ε x y‖ₑ =
            ENNReal.ofReal
              |hiaiIocUniformStepFunction φ ε x n y -
                hiaiScaledMollifierWeight φ ε x y| := by
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
      rw [hnorm]
      exact ENNReal.ofReal_le_ofReal (hbound y hy)
  calc
    (∫⁻ y in Set.Ioc (x - ε) (x + ε),
        ‖hiaiIocUniformStepFunction φ ε x n y -
          hiaiScaledMollifierWeight φ ε x y‖ₑ ∂μ)
        ≤ ∫⁻ _y in Set.Ioc (x - ε) (x + ε), ENNReal.ofReal δ ∂μ := by
          exact lintegral_mono_ae hae
    _ = ENNReal.ofReal δ * μ (Set.Ioc (x - ε) (x + ε)) := by
          simp [lintegral_const]

/--
Uniform window approximation gives the `L¹` convergence input needed by the
Stieltjes-side handoff.
-/
theorem hiaiIocUniformStepFunction_L1_tendsto_scaledWeight_of_uniformApprox
    {φ g : ℝ → ℝ} {ε x : ℝ} (hg : Monotone g)
    (hApprox :
      ∀ δ > 0, ∀ᶠ n in atTop,
        ∀ y ∈ Set.Ioc (x - ε) (x + ε),
          |hiaiIocUniformStepFunction φ ε x n y -
            hiaiScaledMollifierWeight φ ε x y| ≤ δ) :
    Tendsto
      (fun n : ℕ =>
        ∫⁻ y in Set.Ioc (x - ε) (x + ε),
          ‖hiaiIocUniformStepFunction φ ε x n y -
            hiaiScaledMollifierWeight φ ε x y‖ₑ
            ∂hg.stieltjesFunction.measure)
      atTop (𝓝 0) := by
  let μ := hg.stieltjesFunction.measure
  let s := Set.Ioc (x - ε) (x + ε)
  have hμ_ne_top : μ s ≠ ⊤ := by
    rw [show s = Set.Ioc (x - ε) (x + ε) by rfl, StieltjesFunction.measure_Ioc]
    exact ENNReal.ofReal_ne_top
  rw [ENNReal.tendsto_atTop_zero]
  intro η hη
  by_cases hη_top : η = ⊤
  · exact ⟨0, fun n _hn => by simp [hη_top]⟩
  let M : ℝ := (μ s).toReal + 1
  have hM_pos : 0 < M := by
    have hnonneg : 0 ≤ (μ s).toReal := ENNReal.toReal_nonneg
    linarith
  have hη_real_pos : 0 < η.toReal :=
    ENNReal.toReal_pos hη.ne' hη_top
  let δ : ℝ := η.toReal / (2 * M)
  have hδ_pos : 0 < δ := by
    exact div_pos hη_real_pos (mul_pos (by norm_num) hM_pos)
  have hδ_nonneg : 0 ≤ δ := hδ_pos.le
  have hbound_event := hApprox δ hδ_pos
  rw [eventually_atTop] at hbound_event
  rcases hbound_event with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have hbound := hN n hn
  have hle :=
    hiaiIocUniformStepFunction_lintegral_enorm_sub_le
      (μ := μ) (φ := φ) (ε := ε) (x := x) (δ := δ) n hbound
  refine hle.trans ?_
  have hleft_ne_top :
      ENNReal.ofReal δ * μ s ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμ_ne_top
  have htoReal_le :
      (ENNReal.ofReal δ * μ s).toReal ≤ η.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ_nonneg]
    have hμ_toReal_le_M : (μ s).toReal ≤ M := by
      dsimp [M]
      linarith
    calc
      δ * (μ s).toReal ≤ δ * M := by
        exact mul_le_mul_of_nonneg_left hμ_toReal_le_M hδ_nonneg
      _ = η.toReal / 2 := by
        dsimp [δ, M]
        field_simp [show (2 : ℝ) * ((μ s).toReal + 1) ≠ 0 by positivity]
      _ ≤ η.toReal := by linarith [hη_real_pos.le]
  exact (ENNReal.toReal_le_toReal hleft_ne_top hη_top).1 htoReal_le

/-- `L¹` convergence of the concrete uniform half-open step approximants. -/
theorem hiaiIocUniformStepFunction_L1_tendsto_scaledWeight
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g) :
    Tendsto
      (fun n : ℕ =>
        ∫⁻ y in Set.Ioc (x - ε) (x + ε),
          ‖hiaiIocUniformStepFunction φ ε x n y -
            hiaiScaledMollifierWeight φ ε x y‖ₑ
            ∂hg.stieltjesFunction.measure)
      atTop (𝓝 0) := by
  exact
    hiaiIocUniformStepFunction_L1_tendsto_scaledWeight_of_uniformApprox
      (φ := φ) (g := g) (ε := ε) (x := x) hg
      (hiaiIocUniformStepFunction_uniformApprox_scaledWeight
        (φ := φ) (ε := ε) (x := x) hφ hε)

/--
Uniform-mesh specialization of the finite-step limit handoff.  The convergence
of the Stieltjes step integrals and the corresponding increment sums is kept
explicit; this theorem only packages those two convergence statements into
the downstream Stieltjes integration-by-parts input.  Both are supplied in
`hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_closed`
(`IocUniformStep.lean`).
-/
theorem hiaiScaledMollifierWeight_IBP_identity_of_iocUniformStepApproximation
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g)
    (hStieltjes :
      Tendsto
        (fun n : ℕ =>
          ∫ y, hiaiIocUniformStepFunction φ ε x n y
              ∂hg.stieltjesFunction.measure)
        atTop
        (𝓝 (∫ y in Set.Ioc (x - ε) (x + ε),
          hiaiScaledMollifierWeight φ ε x y
            ∂hg.stieltjesFunction.measure)))
    (hPairing :
      Tendsto
        (fun n : ℕ =>
          ∑ k ∈ Finset.range (n + 1),
            hiaiIocUniformStepWeight φ ε x n k *
              (hg.stieltjesFunction
                  (hiaiIocUniformStepRight ε x n k) -
                hg.stieltjesFunction
                  (hiaiIocUniformStepLeft ε x n k)))
        atTop
        (𝓝 (∫ y in x - ε..x + ε,
          (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            hg.stieltjesFunction y))) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂hg.stieltjesFunction.measure) =
      -∫ y in x - ε..x + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y * g y := by
  exact
    hiaiScaledMollifierWeight_IBP_identity_of_iocStepApproximation
      (s := fun n : ℕ => Finset.range (n + 1))
      (φ := φ) (g := g) hφ hε hg
      (a := fun n k => hiaiIocUniformStepLeft ε x n k)
      (b := fun n k => hiaiIocUniformStepRight ε x n k)
      (c := fun n k => hiaiIocUniformStepWeight φ ε x n k)
      (fun n k _hk =>
        hiaiIocUniformStep_left_le_right (ε := ε) (x := x) hε.le n k)
      hStieltjes hPairing

/--
Stieltjes-side convergence handoff for the uniform half-open steps.  It keeps
the analytic approximation input as an `L¹` convergence statement on the
half-open window; once that is supplied, the result is exactly the
`hStieltjes` input used by
`hiaiScaledMollifierWeight_IBP_identity_of_iocUniformStepApproximation`.
-/
theorem hiaiIocUniformStepFunction_stieltjesIntegral_tendsto_scaledWeight_of_L1
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g)
    (hStepInt :
      ∀ᶠ n in atTop,
        Integrable (hiaiIocUniformStepFunction φ ε x n)
          (hg.stieltjesFunction.measure.restrict (Set.Ioc (x - ε) (x + ε))))
    (hStepWhole :
      ∀ᶠ n in atTop,
        (∫ y, hiaiIocUniformStepFunction φ ε x n y
            ∂hg.stieltjesFunction.measure) =
          ∫ y in Set.Ioc (x - ε) (x + ε),
            hiaiIocUniformStepFunction φ ε x n y
              ∂hg.stieltjesFunction.measure)
    (hL1 :
      Tendsto
        (fun n : ℕ =>
          ∫⁻ y in Set.Ioc (x - ε) (x + ε),
            ‖hiaiIocUniformStepFunction φ ε x n y -
              hiaiScaledMollifierWeight φ ε x y‖ₑ
              ∂hg.stieltjesFunction.measure)
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        ∫ y, hiaiIocUniformStepFunction φ ε x n y
          ∂hg.stieltjesFunction.measure)
      atTop
      (𝓝 (∫ y in Set.Ioc (x - ε) (x + ε),
        hiaiScaledMollifierWeight φ ε x y
          ∂hg.stieltjesFunction.measure)) := by
  let μ := hg.stieltjesFunction.measure
  let s := Set.Ioc (x - ε) (x + ε)
  let W : ℝ → ℝ := hiaiScaledMollifierWeight φ ε x
  let S : ℕ → ℝ → ℝ := hiaiIocUniformStepFunction φ ε x
  have hW : Integrable W (μ.restrict s) := by
    exact (hiaiScaledMollifierWeight_integrable_stieltjes
      (φ := φ) hφ hε hg).restrict
  have hSet :
      Tendsto
        (fun n : ℕ => ∫ y in s, S n y ∂μ)
        atTop
        (𝓝 (∫ y in s, W y ∂μ)) := by
    exact tendsto_integral_of_L1 W hW hStepInt hL1
  exact hSet.congr' (hStepWhole.mono fun _ hn => hn.symm)

/--
Uniform-step Stieltjes convergence with the analytic input made explicit as an
`L¹` convergence statement on the half-open window; that statement is
`hiaiIocUniformStepFunction_L1_tendsto_scaledWeight` above.  The
step integrability and whole-integral-to-window reduction are supplied by the
closed uniform-mesh support lemmas above.
-/
theorem iocUniformStepFunction_stieltjesIntegral_tendsto_scaledWeight_of_L1
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g)
    (hL1 :
      Tendsto
        (fun n : ℕ =>
          ∫⁻ y in Set.Ioc (x - ε) (x + ε),
            ‖hiaiIocUniformStepFunction φ ε x n y -
              hiaiScaledMollifierWeight φ ε x y‖ₑ
              ∂hg.stieltjesFunction.measure)
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        ∫ y, hiaiIocUniformStepFunction φ ε x n y
          ∂hg.stieltjesFunction.measure)
      atTop
      (𝓝 (∫ y in Set.Ioc (x - ε) (x + ε),
        hiaiScaledMollifierWeight φ ε x y
          ∂hg.stieltjesFunction.measure)) := by
  exact
    hiaiIocUniformStepFunction_stieltjesIntegral_tendsto_scaledWeight_of_L1
      (φ := φ) (g := g) hφ hε hg
      (Eventually.of_forall fun n =>
        (hiaiIocUniformStepFunction_integrable_stieltjes
          hg.stieltjesFunction (φ := φ) n).restrict)
      (Eventually.of_forall fun n =>
        hiaiIocUniformStepFunction_integral_eq_Ioc
          hg.stieltjesFunction.measure (φ := φ) hε.le n)
      hL1

/--
Concrete Stieltjes-side convergence from uniform approximation data.  The only
input is the geometric statement that the half-open mesh step functions uniformly
approximate the scaled weight on their window, proved as
`hiaiIocUniformStepFunction_uniformApprox_scaledWeight` above.
-/
theorem hiaiIocUniformStepFunction_stieltjesIntegral_tendsto_scaledWeight_of_uniformApprox
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g)
    (hApprox :
      ∀ δ > 0, ∀ᶠ n in atTop,
        ∀ y ∈ Set.Ioc (x - ε) (x + ε),
          |hiaiIocUniformStepFunction φ ε x n y -
            hiaiScaledMollifierWeight φ ε x y| ≤ δ) :
    Tendsto
      (fun n : ℕ =>
        ∫ y, hiaiIocUniformStepFunction φ ε x n y
          ∂hg.stieltjesFunction.measure)
      atTop
      (𝓝 (∫ y in Set.Ioc (x - ε) (x + ε),
        hiaiScaledMollifierWeight φ ε x y
          ∂hg.stieltjesFunction.measure)) := by
  exact
    iocUniformStepFunction_stieltjesIntegral_tendsto_scaledWeight_of_L1
      (φ := φ) (g := g) hφ hε hg
      (hiaiIocUniformStepFunction_L1_tendsto_scaledWeight_of_uniformApprox
        (φ := φ) (g := g) (ε := ε) (x := x) hg hApprox)

/--
Stieltjes-side convergence of the concrete uniform half-open steps to the
scaled mollifier weight.  This supplies the `hStieltjes` input; the
finite-increment / volume-pairing side of the BV/Stieltjes identity is
`hiaiIocUniformStep_increment_sum_tendsto_volumePairing` in `IocUniformStep.lean`.
-/
theorem hiaiIocUniformStepFunction_stieltjesIntegral_tendsto_scaledWeight
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g) :
    Tendsto
      (fun n : ℕ =>
        ∫ y, hiaiIocUniformStepFunction φ ε x n y
          ∂hg.stieltjesFunction.measure)
      atTop
      (𝓝 (∫ y in Set.Ioc (x - ε) (x + ε),
        hiaiScaledMollifierWeight φ ε x y
          ∂hg.stieltjesFunction.measure)) := by
  exact
    hiaiIocUniformStepFunction_stieltjesIntegral_tendsto_scaledWeight_of_uniformApprox
      (φ := φ) (g := g) hφ hε hg
      (hiaiIocUniformStepFunction_uniformApprox_scaledWeight
        (φ := φ) (ε := ε) (x := x) hφ hε)

/--
Uniform-step Stieltjes integration-by-parts handoff with the Stieltjes-integral
side already supplied by the concrete uniform approximation.  The only input is
the finite-increment / volume-pairing convergence, supplied by
`hiaiIocUniformStep_increment_sum_tendsto_volumePairing` in
`hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_closed`
(`IocUniformStep.lean`).
-/
theorem hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g)
    (hPairing :
      Tendsto
        (fun n : ℕ =>
          ∑ k ∈ Finset.range (n + 1),
            hiaiIocUniformStepWeight φ ε x n k *
              (hg.stieltjesFunction
                  (hiaiIocUniformStepRight ε x n k) -
                hg.stieltjesFunction
                  (hiaiIocUniformStepLeft ε x n k)))
        atTop
        (𝓝 (∫ y in x - ε..x + ε,
          (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            hg.stieltjesFunction y))) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂hg.stieltjesFunction.measure) =
      -∫ y in x - ε..x + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y * g y := by
  exact
    hiaiScaledMollifierWeight_IBP_identity_of_iocUniformStepApproximation
      (φ := φ) (g := g) hφ hε hg
      (hiaiIocUniformStepFunction_stieltjesIntegral_tendsto_scaledWeight
        (φ := φ) (g := g) hφ hε hg)
      hPairing

/--
If finite summation by parts identifies the increment sums with the
left-endpoint representative volume integrals, then convergence of those
volume integrals supplies the `hPairing` input.  The unconditional form is
`hiaiIocUniformStep_increment_sum_tendsto_volumePairing` in `IocUniformStep.lean`.
-/
theorem hiaiIocUniformStep_increment_sum_tendsto_volumePairing_of_leftRep
    {φ g : ℝ → ℝ} {ε x : ℝ} (hg : Monotone g)
    (hExact :
      ∀ᶠ n in atTop,
        (∑ k ∈ Finset.range (n + 1),
          hiaiIocUniformStepWeight φ ε x n k *
            (hg.stieltjesFunction
                (hiaiIocUniformStepRight ε x n k) -
              hg.stieltjesFunction
                (hiaiIocUniformStepLeft ε x n k))) =
          ∫ y in x - ε..x + ε,
            (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
              hiaiIocUniformStepLeftRep hg.stieltjesFunction ε x n y)
    (hLeft :
      Tendsto
        (fun n : ℕ =>
          ∫ y in x - ε..x + ε,
            (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
              hiaiIocUniformStepLeftRep hg.stieltjesFunction ε x n y)
        atTop
        (𝓝 (∫ y in x - ε..x + ε,
          (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            hg.stieltjesFunction y))) :
    Tendsto
      (fun n : ℕ =>
        ∑ k ∈ Finset.range (n + 1),
          hiaiIocUniformStepWeight φ ε x n k *
            (hg.stieltjesFunction
                (hiaiIocUniformStepRight ε x n k) -
              hg.stieltjesFunction
                (hiaiIocUniformStepLeft ε x n k)))
      atTop
      (𝓝 (∫ y in x - ε..x + ε,
        (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
          hg.stieltjesFunction y)) := by
  exact hLeft.congr' (hExact.mono fun _ hn => hn.symm)

/--
Dominated-convergence bridge for the left-endpoint representatives on the
half-open window.  This is the analytic convergence part left after the finite
summation-by-parts algebra has been separated.
-/
theorem hiaiIocUniformStep_leftRep_volumeIntegral_tendsto_of_dominated
    {φ G : ℝ → ℝ} {ε x : ℝ} {bound : ℝ → ℝ}
    (h_meas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun y : ℝ =>
            (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
              hiaiIocUniformStepLeftRep G ε x n y)
          (volume.restrict (Set.Ioc (x - ε) (x + ε))))
    (h_bound :
      ∀ n : ℕ,
        ∀ᵐ y ∂volume.restrict (Set.Ioc (x - ε) (x + ε)),
          ‖(-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
              hiaiIocUniformStepLeftRep G ε x n y‖ ≤ bound y)
    (h_bound_int :
      Integrable bound (volume.restrict (Set.Ioc (x - ε) (x + ε))))
    (h_lim :
      ∀ᵐ y ∂volume.restrict (Set.Ioc (x - ε) (x + ε)),
        Tendsto
          (fun n : ℕ =>
            (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
              hiaiIocUniformStepLeftRep G ε x n y)
          atTop
          (𝓝 ((-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            G y))) :
    Tendsto
      (fun n : ℕ =>
        ∫ y in Set.Ioc (x - ε) (x + ε),
          (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            hiaiIocUniformStepLeftRep G ε x n y)
      atTop
      (𝓝 (∫ y in Set.Ioc (x - ε) (x + ε),
        (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
          G y)) := by
  exact
    tendsto_integral_of_dominated_convergence bound h_meas h_bound_int
      h_bound h_lim

private theorem sum_range_mul_sub_eq_neg_sum_range_mul_sub
    (W G : ℕ → ℝ) (n : ℕ)
    (hzero : W 0 = 0) (hend : W (n + 1) = 0) :
    (∑ k ∈ Finset.range (n + 1), W (k + 1) * (G (k + 1) - G k)) =
      -∑ k ∈ Finset.range (n + 1), G k * (W (k + 1) - W k) := by
  have hterm : ∀ k : ℕ,
      W (k + 1) * (G (k + 1) - G k) + G k * (W (k + 1) - W k) =
        W (k + 1) * G (k + 1) - W k * G k := by
    intro k
    ring
  have htel :
      (∑ k ∈ Finset.range (n + 1),
          (W (k + 1) * G (k + 1) - W k * G k)) =
        W (n + 1) * G (n + 1) - W 0 * G 0 := by
    clear hzero hend hterm
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hsum :
      (∑ k ∈ Finset.range (n + 1), W (k + 1) * (G (k + 1) - G k)) +
        (∑ k ∈ Finset.range (n + 1), G k * (W (k + 1) - W k)) = 0 := by
    rw [← Finset.sum_add_distrib]
    simp_rw [hterm]
    rw [htel, hzero, hend]
    ring
  linarith

/-- The first left endpoint of the uniform mesh is the left window endpoint. -/
theorem hiaiIocUniformStepLeft_zero
    (ε x : ℝ) (n : ℕ) :
    hiaiIocUniformStepLeft ε x n 0 = x - ε := by
  simp [hiaiIocUniformStepLeft]

/-- The last left endpoint of the uniform mesh is the right window endpoint. -/
theorem hiaiIocUniformStepLeft_last
    (ε x : ℝ) (n : ℕ) :
    hiaiIocUniformStepLeft ε x n (n + 1) = x + ε := by
  unfold hiaiIocUniformStepLeft hiaiIocUniformStepWidth
  have hden : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hden]
  ring

/--
Exact finite summation by parts for the uniform half-open mesh.  The endpoint
terms vanish because the scaled mollifier weight is zero at both window
endpoints.
-/
theorem hiaiIocUniformStep_increment_sum_summationByParts
    {φ G : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      hiaiIocUniformStepWeight φ ε x n k *
        (G (hiaiIocUniformStepRight ε x n k) -
          G (hiaiIocUniformStepLeft ε x n k))) =
      -∑ k ∈ Finset.range (n + 1),
        G (hiaiIocUniformStepLeft ε x n k) *
          (hiaiIocUniformStepWeight φ ε x n k -
            hiaiScaledMollifierWeight φ ε x
              (hiaiIocUniformStepLeft ε x n k)) := by
  let W : ℕ → ℝ := fun k =>
    hiaiScaledMollifierWeight φ ε x
      (hiaiIocUniformStepLeft ε x n k)
  let H : ℕ → ℝ := fun k => G (hiaiIocUniformStepLeft ε x n k)
  have hzero : W 0 = 0 := by
    simp [W, hiaiIocUniformStepLeft_zero,
      hiaiScaledMollifierWeight_boundary_left_zero (φ := φ) hφ hε]
  have hend : W (n + 1) = 0 := by
    simp [W, hiaiIocUniformStepLeft_last,
      hiaiScaledMollifierWeight_boundary_right_zero (φ := φ) hφ hε]
  have hsum :=
    sum_range_mul_sub_eq_neg_sum_range_mul_sub W H n hzero hend
  simpa [W, H, hiaiIocUniformStepWeight,
    hiaiIocUniformStep_right_eq_next_left] using hsum

/-- The derivative of the scaled mollifier weight in the spatial variable is continuous. -/
theorem hiaiScaledMollifierWeight_deriv_y_continuous
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} :
    Continuous
      (fun y : ℝ =>
        deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) := by
  have hderivφ : Continuous (deriv φ) :=
    hφ.smooth.continuous_deriv (by simp [loewnerBookSmoothOrder])
  rw [show
      (fun y : ℝ =>
        deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) =
        fun y : ℝ => ε⁻¹ * (deriv φ ((x - y) / ε) * (-ε⁻¹)) by
        funext y
        exact hiaiScaledMollifierWeight_deriv_y
          (φ := φ) (ε := ε) (x := x) (y := y) hφ]
  fun_prop

/-- The spatial derivative of the scaled weight is interval-integrable. -/
theorem hiaiScaledMollifierWeight_deriv_y_intervalIntegrable
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x a b : ℝ} :
    IntervalIntegrable
      (fun y : ℝ =>
        deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y)
      volume a b :=
  (hiaiScaledMollifierWeight_deriv_y_continuous
    (φ := φ) (ε := ε) (x := x) hφ).intervalIntegrable _ _

/--
On each uniform atom, the increment of the scaled weight is the integral of its
ordinary derivative.  This is the smooth endpoint needed after the finite
summation-by-parts algebra.
-/
theorem hiaiIocUniformStep_weight_increment_eq_deriv_integral
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (n k : ℕ) :
    hiaiIocUniformStepWeight φ ε x n k -
        hiaiScaledMollifierWeight φ ε x
          (hiaiIocUniformStepLeft ε x n k) =
      ∫ y in
        hiaiIocUniformStepLeft ε x n k..
        hiaiIocUniformStepRight ε x n k,
        deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y := by
  let W : ℝ → ℝ := fun y => hiaiScaledMollifierWeight φ ε x y
  have hderiv :
      ∀ y ∈ [[hiaiIocUniformStepLeft ε x n k,
          hiaiIocUniformStepRight ε x n k]],
        HasDerivAt W (deriv W y) y := by
    intro y _hy
    simpa [W, hiaiScaledMollifierWeight_deriv_y
      (φ := φ) (ε := ε) (x := x) (y := y) hφ] using
      hiaiScaledMollifierWeight_hasDerivAt_y
        (φ := φ) (ε := ε) (x := x) (y := y) hφ
  have hint :
      IntervalIntegrable (deriv W) volume
        (hiaiIocUniformStepLeft ε x n k)
        (hiaiIocUniformStepRight ε x n k) := by
    simpa [W] using
      hiaiScaledMollifierWeight_deriv_y_intervalIntegrable
        (φ := φ) (ε := ε) (x := x) hφ
  have hfund :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := W) (f' := deriv W)
      (a := hiaiIocUniformStepLeft ε x n k)
      (b := hiaiIocUniformStepRight ε x n k)
      hderiv hint
  simpa [W, hiaiIocUniformStepWeight] using hfund.symm


end

end Quantum.TraceInequality.Loewner
