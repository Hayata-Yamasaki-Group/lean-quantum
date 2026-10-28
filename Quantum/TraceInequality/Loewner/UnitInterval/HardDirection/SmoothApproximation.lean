import Quantum.TraceInequality.Loewner.UnitInterval.HardDirection.RouteContracts

/-!
# Chapter 20 smooth book approximants

This file contains the canonical parameter facts, scaled regularity producers,
smooth-strict family constructors, and pointwise convergence lemmas for the
Theorem 20.1 book approximants.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory
open Filter

open scoped NNReal
open scoped Topology
open scoped BoundedContinuousFunction
open scoped ComplexOrder
open scoped Matrix
open scoped MatrixOrder

noncomputable section

/-- The canonical perturbation parameter is positive. -/
theorem bookEpsilon_pos (n : ℕ) :
    0 < bookEpsilon n := by
  unfold bookEpsilon
  positivity

/-- The canonical scaling parameter lies in `(0,1)`. -/
theorem bookDelta_mem_Ioo (n : ℕ) :
    bookDelta n ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · unfold bookDelta
    positivity
  · unfold bookDelta
    have hgt : (1 : ℝ) < ((n + 2 : ℕ) : ℝ) := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      norm_num
      linarith
    simpa using inv_lt_one_of_one_lt₀ hgt

/-- The canonical perturbation parameter tends to `0`. -/
theorem bookEpsilon_tendsto_zero :
    Tendsto bookEpsilon atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0)
  simpa [one_div, Nat.cast_add] using
    (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto
      (fun n : ℕ => 1 / (((n : ℝ) + 1))) atTop (𝓝 0))

/-- The canonical scaling parameter tends to `0`. -/
theorem bookDelta_tendsto_zero :
    Tendsto bookDelta atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ)⁻¹) atTop (𝓝 0)
  simpa [Function.comp_def, one_div, Nat.cast_add, add_assoc, add_comm, add_left_comm,
    show (1 : ℝ) + 1 = 2 by norm_num] using
    ((tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto
      (fun n : ℕ => 1 / (((n : ℝ) + 1))) atTop (𝓝 0)).comp
        (tendsto_add_atTop_nat 1))

private theorem book_scaled_mem_Ioo_of_delta_mem_Ioo
    {δ x : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (1 - δ) * x ∈ Set.Ioo (-1 : ℝ) 1 := by
  have ha_pos : 0 < 1 - δ := by linarith [hδ.2]
  have ha_lt_one : 1 - δ < 1 := by linarith [hδ.1]
  have hxabs : |x| ≤ 1 := abs_le.mpr hx
  have habs : |(1 - δ) * x| < 1 := by
    rw [abs_mul, abs_of_nonneg ha_pos.le]
    calc
      (1 - δ) * |x| ≤ (1 - δ) * 1 :=
        mul_le_mul_of_nonneg_left hxabs ha_pos.le
      _ < 1 := by simpa using ha_lt_one
  exact abs_lt.mp habs

/--
Interior smoothness is enough for the scaled part, since
`x ↦ (1 - δ) * x` maps `[-1,1]` strictly into `(-1,1)` when `δ ∈ (0,1)`.
-/
theorem book_scaled_smooth_neighborhood_of_interiorSmooth
    {f : ℝ → ℝ} {δ : ℝ}
    (hfSmooth : ContDiffOn ℝ loewnerBookSmoothOrder f (Set.Ioo (-1 : ℝ) 1))
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ V : Set ℝ, IsOpen V ∧ Set.Icc (-1 : ℝ) 1 ⊆ V ∧
      ContDiffOn ℝ loewnerBookSmoothOrder (fun x : ℝ => f ((1 - δ) * x)) V := by
  let V : Set ℝ := (fun x : ℝ => (1 - δ) * x) ⁻¹' Set.Ioo (-1 : ℝ) 1
  have hVopen : IsOpen V :=
    isOpen_Ioo.preimage (continuous_const.mul continuous_id)
  have hVsub : Set.Icc (-1 : ℝ) 1 ⊆ V := by
    intro x hx
    exact book_scaled_mem_Ioo_of_delta_mem_Ioo hδ hx
  have hlin : ContDiffOn ℝ loewnerBookSmoothOrder (fun x : ℝ => (1 - δ) * x) V := by
    exact contDiffOn_const.mul contDiffOn_id
  have hcomp : ContDiffOn ℝ loewnerBookSmoothOrder (f ∘ fun x : ℝ => (1 - δ) * x) V :=
    hfSmooth.comp hlin (fun _ hx => hx)
  refine ⟨V, hVopen, hVsub, ?_⟩
  simpa [Function.comp_def] using hcomp

/-- On `[-1,1]`, the derivative of the scaled part is continuous. -/
theorem book_scaled_deriv_continuousOn_Icc_of_interiorSmooth
    {f : ℝ → ℝ} {δ : ℝ}
    (hfSmooth : ContDiffOn ℝ loewnerBookSmoothOrder f (Set.Ioo (-1 : ℝ) 1))
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousOn (fun x : ℝ => deriv (fun y : ℝ => f ((1 - δ) * y)) x)
      (Set.Icc (-1 : ℝ) 1) := by
  rcases book_scaled_smooth_neighborhood_of_interiorSmooth
      hfSmooth hδ with ⟨V, hVopen, hVsub, hVsmooth⟩
  exact (hVsmooth.continuousOn_deriv_of_isOpen hVopen
    (by simp [loewnerBookSmoothOrder])).mono hVsub

/--
Interior smoothness gives a finite derivative bound for each scaled part on the
compact interval `[-1,1]`.
-/
theorem book_exists_scaled_deriv_bound_on_Icc_of_interiorSmooth
    {f : ℝ → ℝ} {δ : ℝ}
    (hfSmooth : ContDiffOn ℝ loewnerBookSmoothOrder f (Set.Ioo (-1 : ℝ) 1))
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ K : ℝ≥0, ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ENNReal.ofReal (deriv (fun y : ℝ => f ((1 - δ) * y)) x) ≤
        (K : ENNReal) := by
  let g : ℝ → ℝ := fun x : ℝ => deriv (fun y : ℝ => f ((1 - δ) * y)) x
  have hgcont : ContinuousOn g (Set.Icc (-1 : ℝ) 1) :=
    book_scaled_deriv_continuousOn_Icc_of_interiorSmooth hfSmooth hδ
  have hbdd : BddAbove (g '' Set.Icc (-1 : ℝ) 1) :=
    isCompact_Icc.bddAbove_image hgcont
  rcases hbdd with ⟨C, hC⟩
  refine ⟨Real.toNNReal C, ?_⟩
  intro x hx
  have hle : g x ≤ C := hC ⟨x, hx, rfl⟩
  rw [ENNReal.ofNNReal_toNNReal]
  exact ENNReal.ofReal_le_ofReal hle

/--
Interior smoothness alone supplies the scaled regularity package for arbitrary
positive book parameters.  The strictness and `g₀` contribution are handled by
the later strictification algebra.
-/
noncomputable def bookScaledRegularityFamilyInput_of_interiorSmooth_with_params
    {f : ℝ → ℝ}
    (hfSmooth : ContDiffOn ℝ loewnerBookSmoothOrder f (Set.Ioo (-1 : ℝ) 1))
    (epsilon delta : ℕ → ℝ)
    (epsilon_pos : ∀ n : ℕ, 0 < epsilon n)
    (delta_mem_Ioo : ∀ n : ℕ, delta n ∈ Set.Ioo (0 : ℝ) 1)
    (epsilon_tendsto_zero : Tendsto epsilon atTop (𝓝 0))
    (delta_tendsto_zero : Tendsto delta atTop (𝓝 0)) :
    BookScaledRegularityFamilyInput f where
  epsilon := epsilon
  delta := delta
  epsilon_pos := epsilon_pos
  delta_mem_Ioo := delta_mem_Ioo
  epsilon_tendsto_zero := epsilon_tendsto_zero
  delta_tendsto_zero := delta_tendsto_zero
  K_scaled := fun n =>
    Classical.choose
      (book_exists_scaled_deriv_bound_on_Icc_of_interiorSmooth
        hfSmooth (delta_mem_Ioo n))
  scaled_smooth_neighborhood := by
    intro (n : ℕ)
    exact book_scaled_smooth_neighborhood_of_interiorSmooth
      hfSmooth (delta_mem_Ioo n)
  scaled_deriv_bound_on_Icc := by
    intro n
    exact
      Classical.choose_spec
        (book_exists_scaled_deriv_bound_on_Icc_of_interiorSmooth
          hfSmooth (delta_mem_Ioo n))

/--
Canonical scaled regularity package from interior smoothness, using
`ε_n = (n+1)⁻¹` and `δ_n = (n+2)⁻¹`.
-/
noncomputable def bookScaledRegularityFamilyInput_of_interiorSmooth
    {f : ℝ → ℝ}
    (hfSmooth : ContDiffOn ℝ loewnerBookSmoothOrder f (Set.Ioo (-1 : ℝ) 1)) :
    BookScaledRegularityFamilyInput f :=
  bookScaledRegularityFamilyInput_of_interiorSmooth_with_params
    hfSmooth bookEpsilon bookDelta
    bookEpsilon_pos bookDelta_mem_Ioo
    bookEpsilon_tendsto_zero bookDelta_tendsto_zero

/--
The scaled regularity package plus the proved smoothness of `g₀` supplies a
smooth neighborhood for each full approximant.
-/
theorem bookSmoothApprox_smooth_neighborhood_of_scaledRegularity
    {f : ℝ → ℝ} (h : BookScaledRegularityFamilyInput f) :
    ∀ n : ℕ, ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (-1 : ℝ) 1 ⊆ U ∧
      ContDiffOn ℝ loewnerBookSmoothOrder
        (bookSmoothApprox f (h.epsilon n) (h.delta n)) U := by
  intro n
  rcases h.scaled_smooth_neighborhood n with ⟨U, hUopen, hUsub, hUsmooth⟩
  refine ⟨U ∩ Set.Iio (2 : ℝ), hUopen.inter isOpen_Iio, ?_, ?_⟩
  · intro x hx
    exact ⟨hUsub hx, lt_of_le_of_lt hx.2 (by norm_num)⟩
  · unfold bookSmoothApprox
    have hscaled :
        ContDiffOn ℝ loewnerBookSmoothOrder (fun x : ℝ => f ((1 - h.delta n) * x))
          (U ∩ Set.Iio (2 : ℝ)) :=
      hUsmooth.mono Set.inter_subset_left
    have hg0 :
        ContDiffOn ℝ loewnerBookSmoothOrder bookG0 (U ∩ Set.Iio (2 : ℝ)) :=
      bookG0_contDiffOn_Iio_two.mono Set.inter_subset_right
    have hg0mul :
        ContDiffOn ℝ loewnerBookSmoothOrder (fun x : ℝ => h.epsilon n * bookG0 x)
          (U ∩ Set.Iio (2 : ℝ)) := by
      simpa [smul_eq_mul] using hg0.const_smul (h.epsilon n)
    exact hscaled.add hg0mul

/--
The scaled derivative bound and the `g₀` derivative bound give the derivative
bound for the full approximants.
-/
theorem bookSmoothApprox_deriv_bound_on_Icc_of_scaledRegularity
    {f : ℝ → ℝ} (h : BookScaledRegularityFamilyInput f) :
    ∀ n : ℕ, ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ENNReal.ofReal (deriv (bookSmoothApprox f (h.epsilon n) (h.delta n)) x) ≤
        ((h.K_scaled n + ⟨h.epsilon n, (h.epsilon_pos n).le⟩ : ℝ≥0) : ENNReal) := by
  intro n x hx
  let scaled : ℝ → ℝ := fun x : ℝ => f ((1 - h.delta n) * x)
  rcases h.scaled_smooth_neighborhood n with ⟨U, hUopen, hUsub, hUsmooth⟩
  have hxU : x ∈ U := hUsub hx
  have hscaledDiff : DifferentiableAt ℝ scaled x := by
    exact (hUsmooth.contDiffAt (hUopen.mem_nhds hxU)).differentiableAt
      (by simp [loewnerBookSmoothOrder])
  have hxlt : x < 2 := lt_of_le_of_lt hx.2 (by norm_num)
  have hg0Diff : DifferentiableAt ℝ bookG0 x :=
    (bookG0_hasDerivAt_of_lt_two hxlt).differentiableAt
  have hderiv :
      deriv (bookSmoothApprox f (h.epsilon n) (h.delta n)) x =
        deriv scaled x + h.epsilon n * deriv bookG0 x := by
    calc
      deriv (bookSmoothApprox f (h.epsilon n) (h.delta n)) x
          = deriv (fun y : ℝ => scaled y + h.epsilon n * bookG0 y) x := by
            rfl
      _ = deriv scaled x +
            deriv (fun y : ℝ => h.epsilon n * bookG0 y) x := by
            rw [deriv_fun_add hscaledDiff (hg0Diff.const_mul (h.epsilon n))]
      _ = deriv scaled x + h.epsilon n * deriv bookG0 x := by
            rw [deriv_const_mul (h.epsilon n) hg0Diff]
  let epsNN : ℝ≥0 := ⟨h.epsilon n, (h.epsilon_pos n).le⟩
  have hg0Real :
      h.epsilon n * deriv bookG0 x ≤ h.epsilon n := by
    exact mul_le_of_le_one_right (le_of_lt (h.epsilon_pos n))
      (bookG0_deriv_le_one_on_Icc x hx)
  have hg0ENN :
      ENNReal.ofReal (h.epsilon n * deriv bookG0 x) ≤
        (epsNN : ENNReal) := by
    rw [← ENNReal.ofReal_eq_coe_nnreal (h.epsilon_pos n).le]
    exact ENNReal.ofReal_le_ofReal hg0Real
  calc
    ENNReal.ofReal (deriv (bookSmoothApprox f (h.epsilon n) (h.delta n)) x)
        = ENNReal.ofReal (deriv scaled x + h.epsilon n * deriv bookG0 x) := by
          rw [hderiv]
    _ ≤ ENNReal.ofReal (deriv scaled x) +
          ENNReal.ofReal (h.epsilon n * deriv bookG0 x) :=
          ENNReal.ofReal_add_le
    _ ≤ (h.K_scaled n : ENNReal) + (epsNN : ENNReal) :=
          add_le_add (h.scaled_deriv_bound_on_Icc n x hx) hg0ENN
    _ = ((h.K_scaled n + epsNN : ℝ≥0) : ENNReal) := by
          simp

/--
The scaled regularity contract supplies the existing full regularity package;
the extra bound is exactly the closed `g₀` derivative contribution.
-/
noncomputable def
    bookSmoothApproxRegularityFamilyInput_of_scaledRegularity
    {f : ℝ → ℝ} (h : BookScaledRegularityFamilyInput f) :
    BookSmoothApproxRegularityFamilyInput f where
  epsilon := h.epsilon
  delta := h.delta
  epsilon_pos := h.epsilon_pos
  delta_mem_Ioo := h.delta_mem_Ioo
  epsilon_tendsto_zero := h.epsilon_tendsto_zero
  delta_tendsto_zero := h.delta_tendsto_zero
  K := fun n => h.K_scaled n + ⟨h.epsilon n, (h.epsilon_pos n).le⟩
  smooth_neighborhood := bookSmoothApprox_smooth_neighborhood_of_scaledRegularity h
  deriv_bound_on_Icc :=
    bookSmoothApprox_deriv_bound_on_Icc_of_scaledRegularity h

/--
Regularity plus the `g₀` strict input produces the smooth-strict approximation
family consumed by the Chapter 20 bridge.
-/
noncomputable def bookSmoothStrictFamilyInput_of_regularity_of_g0_strict
    {f : ℝ → ℝ} (hf : GlobalStrictPosDef f)
    (hg0 : GlobalStrictPosDef bookG0)
    (h : BookSmoothApproxRegularityFamilyInput f) :
    BookSmoothStrictFamilyInput f where
  epsilon := h.epsilon
  delta := h.delta
  epsilon_pos := h.epsilon_pos
  delta_mem_Ioo := h.delta_mem_Ioo
  epsilon_tendsto_zero := h.epsilon_tendsto_zero
  delta_tendsto_zero := h.delta_tendsto_zero
  smoothStrict := fun n =>
    { strict :=
        bookSmoothApprox_globalStrictPosDef_of_globalStrictPosDef_of_g0_strict
          hf hg0 (h.epsilon_pos n) (h.delta_mem_Ioo n)
      smooth_neighborhood := h.smooth_neighborhood n
      K := h.K n
      deriv_bound_on_Icc := h.deriv_bound_on_Icc n }

/--
Regularity alone now produces the smooth-strict approximation family, because
the book auxiliary function `g₀` has a closed strict positivity proof.
-/
noncomputable def bookSmoothStrictFamilyInput_of_regularity
    {f : ℝ → ℝ} (hf : GlobalStrictPosDef f)
    (h : BookSmoothApproxRegularityFamilyInput f) :
    BookSmoothStrictFamilyInput f :=
  bookSmoothStrictFamilyInput_of_regularity_of_g0_strict
    hf bookG0_globalStrictPosDef h

/--
Combine a concrete smooth-strict approximation family with the measure-limit
transfer package to obtain the existing approximation-family input.
-/
noncomputable def
    bookApproximationFamilyInput_of_smoothStrictFamilyInput_of_limitTransfer
    {f : ℝ → ℝ} (h : BookSmoothStrictFamilyInput f)
    (limitTransfer :
      BookRouteLimitTransferInput f
        (fun n : ℕ => bookSmoothApprox f (h.epsilon n) (h.delta n))) :
    BookApproximationFamilyInput f where
  epsilon := h.epsilon
  delta := h.delta
  epsilon_tendsto_zero := h.epsilon_tendsto_zero
  delta_tendsto_zero := h.delta_tendsto_zero
  smoothStrict := h.smoothStrict
  limitTransfer := limitTransfer

/--
Regularity plus a matching measure-limit transfer package supplies the concrete
Theorem 20.1 approximation-family input, with the `g₀` strict input discharged.
-/
noncomputable def
    bookApproximationFamilyInput_of_regularityFamilyInput_of_limitTransfer
    {f : ℝ → ℝ} (hf : GlobalStrictPosDef f)
    (h : BookSmoothApproxRegularityFamilyInput f)
    (limitTransfer :
      BookRouteLimitTransferInput f
        (fun n : ℕ => bookSmoothApprox f (h.epsilon n) (h.delta n))) :
    BookApproximationFamilyInput f :=
  bookApproximationFamilyInput_of_smoothStrictFamilyInput_of_limitTransfer
    (bookSmoothStrictFamilyInput_of_regularity hf h) limitTransfer

/--
Scaled regularity plus a matching measure-limit transfer package supplies the
concrete Theorem 20.1 approximation-family input.
-/
noncomputable def
    bookApproximationFamilyInput_of_scaledRegularityFamilyInput_of_limitTransfer
    {f : ℝ → ℝ} (hf : GlobalStrictPosDef f)
    (h : BookScaledRegularityFamilyInput f)
    (limitTransfer :
      BookRouteLimitTransferInput f
        (fun n : ℕ => bookSmoothApprox f (h.epsilon n) (h.delta n))) :
    BookApproximationFamilyInput f :=
  bookApproximationFamilyInput_of_regularityFamilyInput_of_limitTransfer
    hf (bookSmoothApproxRegularityFamilyInput_of_scaledRegularity h)
    limitTransfer

/-- Pointwise convergence of the concrete Theorem 20.1 approximants. -/
theorem bookSmoothApprox_tendsto_of_params
    {f : ℝ → ℝ} {ε δ : ℕ → ℝ} {x : ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    (hf : ContinuousAt f x) :
    Tendsto (fun n : ℕ => bookSmoothApprox f (ε n) (δ n) x)
      atTop (𝓝 (f x)) := by
  have harg : Tendsto (fun n : ℕ => (1 - δ n) * x) atTop (𝓝 x) := by
    have hsub : Tendsto (fun n : ℕ => 1 - δ n) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hδ
    have hmul : Tendsto (fun n : ℕ => (1 - δ n) * x) atTop (𝓝 ((1 - 0) * x)) :=
      hsub.mul tendsto_const_nhds
    simpa using hmul
  have hfpart :
      Tendsto (fun n : ℕ => f ((1 - δ n) * x)) atTop (𝓝 (f x)) :=
    hf.tendsto.comp harg
  have heps :
      Tendsto (fun n : ℕ => ε n * bookG0 x) atTop (𝓝 0) := by
    have hmul :
        Tendsto (fun n : ℕ => ε n * bookG0 x)
          atTop (𝓝 (0 * bookG0 x)) :=
      hε.mul tendsto_const_nhds
    simpa using hmul
  simpa [bookSmoothApprox] using hfpart.add heps

/-- Convergence at the anchor `0` for the concrete Theorem 20.1 approximants. -/
theorem bookSmoothApprox_zero_tendsto_of_params
    {f : ℝ → ℝ} {ε δ : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => bookSmoothApprox f (ε n) (δ n) 0)
      atTop (𝓝 (f 0)) := by
  have heps :
      Tendsto (fun n : ℕ => ε n * bookG0 0) atTop (𝓝 0) := by
    have hmul :
        Tendsto (fun n : ℕ => ε n * bookG0 0)
          atTop (𝓝 (0 * bookG0 0)) :=
      hε.mul tendsto_const_nhds
    simpa using hmul
  simpa [bookSmoothApprox] using tendsto_const_nhds.add heps

/--
Strict global positivity supplies the continuity input needed for pointwise
convergence of the concrete Theorem 20.1 approximants.
-/
theorem bookSmoothApprox_tendsto_of_globalStrictPosDef
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) {ε δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto (fun n : ℕ => bookSmoothApprox f (ε n) (δ n) x)
      atTop (𝓝 (f x)) :=
  bookSmoothApprox_tendsto_of_params hδ hε
    (continuousAt_of_globalStrictPosDef h hx)

end

end Quantum.TraceInequality.Loewner
