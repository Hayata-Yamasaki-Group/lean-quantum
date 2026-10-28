import Quantum.TraceInequality.Loewner.UnitInterval.HardDirection.SmoothApproximation

/-!
# Chapter 20 limit transfer for the book route

This file contains the measure-limit and kernel-convergence machinery that
turns the Chapter 20 approximation packages into interval integral
representations.  The public bridge consumers remain in
`UnitInterval.HardDirectionBridge`.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory
open Filter
open AugmentedLoewnerLocalConstruction

open scoped NNReal
open scoped Topology
open scoped BoundedContinuousFunction
open scoped ComplexOrder
open scoped Matrix
open scoped MatrixOrder

noncomputable section

/--
Build the public interval representation from the measure-level limit-transfer
contract and a chosen representation for each approximant.
-/
noncomputable def integralRepOnUnitInterval_of_bookRouteLimitTransferInput
    {f : ℝ → ℝ} {approximant : ℕ → ℝ → ℝ}
    (h : BookRouteLimitTransferInput f approximant)
    (reps : (n : ℕ) → IntegralRepOnUnitInterval (approximant n)) :
    IntegralRepOnUnitInterval f where
  ν := h.limitMeasure reps
  support := h.limitMeasure_support reps
  formula := by
    intro x hx
    exact h.limitMeasure_formula reps hx

private theorem book_one_add_mul_abs_ge_half {t x : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hx : x ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    (1 / 2 : ℝ) ≤ |1 + t * x| := by
  have ht_abs : |t| ≤ (1 : ℝ) := abs_le.mpr ht
  have hx_abs : |x| < (1 / 2 : ℝ) := abs_lt.mpr hx
  have htx_abs : |t * x| < (1 / 2 : ℝ) := by
    calc
      |t * x| = |t| * |x| := by rw [abs_mul]
      _ ≤ 1 * |x| := mul_le_mul_of_nonneg_right ht_abs (abs_nonneg x)
      _ < 1 * (1 / 2 : ℝ) := mul_lt_mul_of_pos_left hx_abs zero_lt_one
      _ = 1 / 2 := by ring
  have hpos : (1 / 2 : ℝ) < 1 + t * x := by
    have hneg : -(1 / 2 : ℝ) < t * x := (abs_lt.mp htx_abs).1
    linarith
  have hdenpos : 0 < 1 + t * x := by linarith
  rw [abs_of_pos hdenpos]
  exact le_of_lt hpos

private theorem book_kernel_den_norm_ge_half {t x : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hx : x ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    (1 / 2 : ℝ) ≤ ‖(1 + (t : ℂ) * (x : ℂ) : ℂ)‖ := by
  have hhalf := book_one_add_mul_abs_ge_half ht hx
  have hnorm :
      ‖(1 + (t : ℂ) * (x : ℂ) : ℂ)‖ = |1 + t * x| := by
    have h :
        (1 + (t : ℂ) * (x : ℂ) : ℂ) = ((1 + t * x : ℝ) : ℂ) := by
      norm_num
    rw [h, Complex.norm_real, Real.norm_eq_abs]
  simpa [hnorm] using hhalf

private theorem book_kernel_deriv_norm_le_four {t x : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hx : x ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    ‖(1 / (1 + (t : ℂ) * (x : ℂ)) ^ (2 : ℕ) : ℂ)‖ ≤ (4 : ℝ) := by
  have hnorm := book_kernel_den_norm_ge_half ht hx
  have hpos : 0 < ‖(1 + (t : ℂ) * (x : ℂ) : ℂ)‖ :=
    lt_of_lt_of_le (by norm_num) hnorm
  rw [norm_div, norm_one, norm_pow]
  have hsqpos : 0 < ‖(1 + (t : ℂ) * (x : ℂ) : ℂ)‖ ^ (2 : ℕ) :=
    pow_pos hpos 2
  field_simp [hsqpos.ne']
  nlinarith [hnorm, sq_nonneg (2 * ‖(1 + (t : ℂ) * (x : ℂ) : ℂ)‖ - 1)]

private theorem book_kernel_hasDerivAt {t x : ℝ}
    (hden : 1 + t * x ≠ 0) :
    HasDerivAt (fun x : ℝ => ((x : ℂ) / (1 + (t : ℂ) * (x : ℂ))))
      (1 / (1 + (t : ℂ) * (x : ℂ)) ^ (2 : ℕ)) x := by
  have hnum : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
  have hdenC : (1 + (t : ℂ) * (x : ℂ) : ℂ) ≠ 0 := by
    exact_mod_cast hden
  have hdenDeriv :
      HasDerivAt (fun y : ℝ => (1 : ℂ) + (t : ℂ) * (y : ℂ)) (t : ℂ) x := by
    simpa only [Pi.add_apply, zero_add, mul_one] using
      ((hasDerivAt_const (x := x) (c := (1 : ℂ))).add
        (hnum.const_mul (t : ℂ)))
  have h := hnum.div hdenDeriv hdenC
  convert h using 1
  field_simp [hdenC]
  ring

private theorem integralRepOnUnitInterval_ae_mem_Icc
    {f : ℝ → ℝ} (rep : IntegralRepOnUnitInterval f) :
    ∀ᵐ t ∂(rep.ν : Measure ℝ), t ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [ae_iff]
  exact rep.support

private theorem integral_const_one_complex_eq_finiteMeasure_mass
    (ν : FiniteMeasure ℝ) :
    (∫ _t : ℝ, (1 : ℂ) ∂(ν : Measure ℝ)) = ((ν.mass : ℝ) : ℂ) := by
  let μ : Measure ℝ := (ν : Measure ℝ)
  calc
    (∫ _t : ℝ, (1 : ℂ) ∂(ν : Measure ℝ)) =
        (ν : Measure ℝ).real Set.univ • (1 : ℂ) := by
      simp only [MeasureTheory.integral_const, FiniteMeasure.measureReal_eq_coe_coeFn,
        FiniteMeasure.self_eq_mass_mul_normalize, ProbabilityMeasure.coeFn_univ,
        mul_one, Complex.real_smul]
      change ((ν.mass : ℝ) : ℂ) * (1 : ℂ) = ((ν.mass : ℝ) : ℂ)
      ring
    _ = μ.real Set.univ • (1 : ℂ) := by
      simp [μ]
    _ = ((ν.mass : ℝ) : ℂ) := by
      have hreal : μ.real Set.univ = (ν.mass : ℝ) := by
        rw [Measure.real_def]
        have hmassENN : μ Set.univ = (ν.mass : ENNReal) := by
          simp [μ]
        rw [hmassENN, ENNReal.coe_toReal]
      rw [hreal]
      simp

/--
For an interval representation, the kernel integral has derivative equal to the
total representing mass at `0`.
-/
theorem integralRepOnUnitInterval_kernelIntegral_hasDerivAt_zero
    {f : ℝ → ℝ} (rep : IntegralRepOnUnitInterval f) :
    HasDerivAt
      (fun x : ℝ =>
        ∫ t : ℝ, ((x : ℂ) / (1 + (t : ℂ) * (x : ℂ))) ∂(rep.ν : Measure ℝ))
      ((rep.ν.mass : ℝ) : ℂ) 0 := by
  let μ : Measure ℝ := (rep.ν : Measure ℝ)
  haveI : IsFiniteMeasure μ := inferInstance
  let s : Set ℝ := Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)
  have hs : s ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hF_meas :
      ∀ᶠ x : ℝ in 𝓝 (0 : ℝ),
        AEStronglyMeasurable
          (fun t : ℝ => ((x : ℂ) / (1 + (t : ℂ) * (x : ℂ)))) μ := by
    exact Filter.Eventually.of_forall fun (x : ℝ) => by
      have hmeas :
          Measurable (fun t : ℝ => ((x : ℂ) / (1 + (t : ℂ) * (x : ℂ)))) := by
        measurability
      exact hmeas.aestronglyMeasurable
  have hF_int :
      Integrable (fun t : ℝ => ((0 : ℂ) / (1 + (t : ℂ) * (0 : ℝ)))) μ := by
    simp
  have hF'_meas :
      AEStronglyMeasurable
        (fun t : ℝ => (1 / (1 + (t : ℂ) * (0 : ℝ)) ^ (2 : ℕ) : ℂ)) μ := by
    simpa using (measurable_const : Measurable (fun _t : ℝ => (1 : ℂ))).aestronglyMeasurable
  have hBound :
      ∀ᵐ t : ℝ ∂μ, ∀ x : ℝ, x ∈ s →
        ‖(1 / (1 + (t : ℂ) * (x : ℂ)) ^ (2 : ℕ) : ℂ)‖ ≤
          (fun _t : ℝ => (4 : ℝ)) t := by
    filter_upwards [integralRepOnUnitInterval_ae_mem_Icc rep] with t ht x hx
    exact book_kernel_deriv_norm_le_four ht hx
  have hBoundInt : Integrable (fun _t : ℝ => (4 : ℝ)) μ := integrable_const (4 : ℝ)
  have hDiff :
      ∀ᵐ t : ℝ ∂μ, ∀ x : ℝ, x ∈ s →
        HasDerivAt
          (fun x : ℝ => ((x : ℂ) / (1 + (t : ℂ) * (x : ℂ))))
          (1 / (1 + (t : ℂ) * (x : ℂ)) ^ (2 : ℕ)) x := by
    filter_upwards [integralRepOnUnitInterval_ae_mem_Icc rep] with t ht x hx
    have hhalf := book_one_add_mul_abs_ge_half ht hx
    have hden : 1 + t * x ≠ 0 := by
      exact abs_pos.mp (lt_of_lt_of_le (by norm_num) hhalf)
    exact book_kernel_hasDerivAt hden
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (𝕜 := ℝ) (E := ℂ)
      (μ := μ)
      (F := fun x t : ℝ => ((x : ℂ) / (1 + (t : ℂ) * (x : ℂ))))
      (F' := fun x t : ℝ => (1 / (1 + (t : ℂ) * (x : ℂ)) ^ (2 : ℕ) : ℂ))
      (bound := fun _t : ℝ => (4 : ℝ))
      (x₀ := (0 : ℝ)) (s := s)
      hs hF_meas hF_int hF'_meas hBound hBoundInt hDiff
  have hconst :
      (∫ t : ℝ, (1 / (1 + (t : ℂ) * (0 : ℝ)) ^ (2 : ℕ) : ℂ) ∂μ) =
        ((rep.ν.mass : ℝ) : ℂ) := by
    calc
      (∫ t : ℝ, (1 / (1 + (t : ℂ) * (0 : ℝ)) ^ (2 : ℕ) : ℂ) ∂μ)
          = ∫ _t : ℝ, (1 : ℂ) ∂(rep.ν : Measure ℝ) := by
            simp [μ]
      _ = ((rep.ν.mass : ℝ) : ℂ) :=
            integral_const_one_complex_eq_finiteMeasure_mass rep.ν
  rw [hconst] at h
  simpa [μ] using h.2

/-- An interval representation differentiates at `0` with derivative equal to its mass. -/
theorem integralRepOnUnitInterval_hasDerivAt_zero
    {f : ℝ → ℝ} (rep : IntegralRepOnUnitInterval f) :
    HasDerivAt f (rep.ν.mass : ℝ) 0 := by
  have hkernel := integralRepOnUnitInterval_kernelIntegral_hasDerivAt_zero rep
  have hcomplex :
      HasDerivAt (fun x : ℝ => (f x : ℂ)) ((rep.ν.mass : ℝ) : ℂ) 0 := by
    have hright :
        HasDerivAt
          (fun x : ℝ =>
            (f 0 : ℂ) +
              ∫ t : ℝ, ((x : ℂ) / (1 + (t : ℂ) * x))
                ∂(rep.ν : Measure ℝ))
          ((rep.ν.mass : ℝ) : ℂ) 0 :=
      hkernel.const_add (f 0 : ℂ)
    have heq :
        (fun x : ℝ => (f x : ℂ)) =ᶠ[𝓝 (0 : ℝ)]
          fun x : ℝ =>
            (f 0 : ℂ) +
              ∫ t : ℝ, ((x : ℂ) / (1 + (t : ℂ) * x))
                ∂(rep.ν : Measure ℝ) := by
      filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
        (show (0 : ℝ) < 1 by norm_num)] with x hx
      exact rep.formula hx
    exact hright.congr_of_eventuallyEq heq
  have hreal :=
    HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) Complex.reCLM.hasFDerivAt hcomplex
  simpa [Function.comp_def] using hreal

/-- The representing mass is the `ENNReal` form of the derivative at `0`. -/
theorem integralRepOnUnitInterval_mass_eq_ofReal_deriv_zero
    {f : ℝ → ℝ} (rep : IntegralRepOnUnitInterval f) :
    (rep.ν.mass : ENNReal) = ENNReal.ofReal (deriv f 0) := by
  have hderiv :
      deriv f 0 = (rep.ν.mass : ℝ) :=
    (integralRepOnUnitInterval_hasDerivAt_zero rep).deriv
  rw [hderiv, ENNReal.ofReal_coe_nnreal]

/-- A derivative bound at `0` gives the uniform mass bound needed for compactness. -/
theorem integralRepOnUnitInterval_mass_le_of_deriv_bound
    {f : ℝ → ℝ} (rep : IntegralRepOnUnitInterval f) {K : ℝ≥0}
    (hK : ENNReal.ofReal (deriv f 0) ≤ (K : ENNReal)) :
    rep.ν.mass ≤ K := by
  have hmass :
      (rep.ν.mass : ENNReal) ≤ (K : ENNReal) := by
    rw [integralRepOnUnitInterval_mass_eq_ofReal_deriv_zero rep]
    exact hK
  exact ENNReal.coe_le_coe.mp hmass

private abbrev BookInterval : Type :=
  Set.Icc (-1 : ℝ) 1

private theorem bookKernel_den_ne {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (t : BookInterval) :
    (1 : ℂ) + ((t : ℝ) : ℂ) * (x : ℂ) ≠ 0 := by
  have hx_abs : |x| < (1 : ℝ) := abs_lt.mpr hx
  have ht_abs : |(t : ℝ)| ≤ (1 : ℝ) := by
    exact abs_le.mpr t.property
  have hmul_abs : |(t : ℝ) * x| < (1 : ℝ) := by
    calc
      |(t : ℝ) * x| = |(t : ℝ)| * |x| := abs_mul _ _
      _ ≤ 1 * |x| := by
            gcongr
      _ = |x| := one_mul _
      _ < 1 := hx_abs
  have hpos : 0 < 1 + (t : ℝ) * x := by
    have hgt : -(1 : ℝ) < (t : ℝ) * x := (abs_lt.mp hmul_abs).1
    linarith
  have hreal : (1 : ℝ) + (t : ℝ) * x ≠ 0 := ne_of_gt hpos
  exact_mod_cast hreal

private noncomputable def bookKernelInterval
    (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    C(BookInterval, ℂ) where
  toFun t := (x : ℂ) / ((1 : ℂ) + ((t : ℝ) : ℂ) * (x : ℂ))
  continuous_toFun := by
    have hden : Continuous fun t : BookInterval =>
        (1 : ℂ) + ((t : ℝ) : ℂ) * (x : ℂ) := by
      exact continuous_const.add
        ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const)
    exact continuous_const.div hden (bookKernel_den_ne hx)

private noncomputable def bookProjIcc :
    C(ℝ, BookInterval) where
  toFun := Set.projIcc (-1 : ℝ) 1 (by norm_num)
  continuous_toFun := continuous_projIcc

/--
Bounded continuous extension of the book kernel `x / (1 + λ * x)` from
`[-1,1]` to the whole real line, obtained by projecting to `[-1,1]`.
-/
noncomputable def bookKernelExtension
    (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : ℝ →ᵇ ℂ :=
  (BoundedContinuousFunction.mkOfCompact
    (bookKernelInterval x hx)).compContinuous bookProjIcc

/-- On `[-1,1]`, the kernel extension agrees with the original book kernel. -/
theorem bookKernelExtension_eq_on_Icc {x t : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    bookKernelExtension x hx t =
      (x : ℂ) / ((1 : ℂ) + (t : ℂ) * (x : ℂ)) := by
  simp [bookKernelExtension, bookProjIcc,
    bookKernelInterval, Set.projIcc_of_mem (by norm_num) ht]

private theorem book_ae_mem_Icc_of_measure_compl_eq_zero
    {μ : Measure ℝ} (hμ : μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0) :
    ∀ᵐ t ∂μ, t ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [ae_iff]
  change μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0
  exact hμ

/--
For a finite measure supported on `[-1,1]`, integrating the bounded continuous
extension is the same as integrating the original book kernel.
-/
theorem bookKernelExtension_integral_eq
    (μ : FiniteMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (∫ t : ℝ, bookKernelExtension x hx t ∂(μ : Measure ℝ)) =
      ∫ t : ℝ, ((x : ℂ) / ((1 : ℂ) + (t : ℂ) * (x : ℂ)))
        ∂(μ : Measure ℝ) := by
  refine integral_congr_ae ?_
  exact
    (book_ae_mem_Icc_of_measure_compl_eq_zero hμ).mono
      fun t ht => bookKernelExtension_eq_on_Icc hx ht

/--
Weak convergence of finite measures supported on `[-1,1]` gives convergence of
the complex book-kernel integrals.
-/
theorem bookKernel_integral_tendsto_of_measure_tendsto
    {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hμs : ∀ n : ℕ, (μs n : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0)
    (hμ : (μ : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0)
    (hν : Tendsto μs atTop (𝓝 μ)) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto
      (fun n : ℕ =>
        ∫ t : ℝ, ((x : ℂ) / ((1 : ℂ) + (t : ℂ) * (x : ℂ)))
          ∂(μs n : Measure ℝ))
      atTop
      (𝓝
        (∫ t : ℝ, ((x : ℂ) / ((1 : ℂ) + (t : ℂ) * (x : ℂ)))
          ∂(μ : Measure ℝ))) := by
  have hext :=
    (MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto
      (Ω := ℝ) ℂ).1 hν (bookKernelExtension x hx)
  have hleft :
      (fun n : ℕ =>
        ∫ t : ℝ, bookKernelExtension x hx t ∂(μs n : Measure ℝ)) =
        fun n : ℕ =>
          ∫ t : ℝ, ((x : ℂ) / ((1 : ℂ) + (t : ℂ) * (x : ℂ)))
            ∂(μs n : Measure ℝ) := by
    funext n
    exact bookKernelExtension_integral_eq (μs n) (hμs n) hx
  have hright :
      (∫ t : ℝ, bookKernelExtension x hx t ∂(μ : Measure ℝ)) =
        ∫ t : ℝ, ((x : ℂ) / ((1 : ℂ) + (t : ℂ) * (x : ℂ)))
          ∂(μ : Measure ℝ) :=
    bookKernelExtension_integral_eq μ hμ hx
  rw [← hleft, ← hright]
  exact hext

/--
Uniform mass bounds for representing measures supported on `[-1,1]` give a
weakly convergent subsequence and preserve the support condition in the limit.
-/
theorem exists_subseq_tendsto_integralRep_measure_of_mass_bound
    {approximant : ℕ → ℝ → ℝ}
    (reps : (n : ℕ) → IntegralRepOnUnitInterval (approximant n))
    (C : ℝ≥0) (hC : ∀ n : ℕ, (reps n).ν.mass ≤ C) :
    ∃ (ν : FiniteMeasure ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
        Tendsto (fun k : ℕ => (reps (φ k)).ν) atTop (𝓝 ν) ∧
          ((ν : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0) := by
  classical
  let μs : ℕ → FiniteMeasure BookInterval := fun n =>
    (reps n).ν.comap ((↑) : BookInterval → ℝ)
  have hμs_mass : ∀ n : ℕ, (μs n).mass ≤ C := by
    intro n
    exact (FiniteMeasure.mass_comap_le
      ((↑) : BookInterval → ℝ) (reps n).ν).trans (hC n)
  rcases exists_subseq_tendsto_finiteMeasure_BookInterval_of_mass_le
      (μs := μs) (K := C) hμs_mass with
    ⟨μ, φ, hφ, hμ⟩
  let ν : FiniteMeasure ℝ := μ.map ((↑) : BookInterval → ℝ)
  have hmap_eq : ∀ n : ℕ,
      (μs n).map ((↑) : BookInterval → ℝ) = (reps n).ν := by
    intro n
    apply FiniteMeasure.toMeasure_injective
    simp only [μs, FiniteMeasure.toMeasure_map, FiniteMeasure.toMeasure_comap]
    rw [map_comap_subtype_coe (s := Set.Icc (-1 : ℝ) 1) isCompact_Icc.measurableSet]
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    change ((reps n).ν : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0
    exact (reps n).support
  have hν :
      Tendsto (fun k : ℕ => (reps (φ k)).ν) atTop (𝓝 ν) := by
    have hmap :
        Tendsto
          (fun k : ℕ =>
            (μs (φ k)).map ((↑) : BookInterval → ℝ))
          atTop (𝓝 ν) := by
      simpa [ν, Function.comp] using
        (FiniteMeasure.tendsto_map_of_tendsto_of_continuous
          (νs := fun k : ℕ => μs (φ k)) (ν := μ) hμ continuous_subtype_val)
    have hfun :
        (fun k : ℕ =>
          (μs (φ k)).map ((↑) : BookInterval → ℝ)) =
            fun k : ℕ => (reps (φ k)).ν := by
      funext k
      exact hmap_eq (φ k)
    simpa [hfun] using hmap
  have hν_support : ((ν : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0) := by
    change
      Measure.map ((↑) : BookInterval → ℝ)
          (μ : Measure BookInterval)
        (Set.Icc (-1 : ℝ) 1)ᶜ = 0
    rw [Measure.map_apply measurable_subtype_coe isCompact_Icc.measurableSet.compl]
    have hpre :
        ((↑) : BookInterval → ℝ) ⁻¹'
            (Set.Icc (-1 : ℝ) 1)ᶜ = ∅ := by
      ext t
      simp
    rw [hpre, measure_empty]
  exact ⟨ν, φ, hφ, hν, hν_support⟩

/--
Derivative-style mass-bound data supplies the mass-bound transfer contract.
-/
noncomputable def bookRouteMassBoundInput_of_derivativeMassBoundInput
    {f : ℝ → ℝ} {approximant : ℕ → ℝ → ℝ}
    (h : BookRouteDerivativeMassBoundInput f approximant) :
    BookRouteMassBoundInput f approximant where
  approximant_tendsto := h.approximant_tendsto
  approximant_zero_tendsto := h.approximant_zero_tendsto
  massBound := fun _ => h.K
  mass_le := h.mass_le

/--
A uniform derivative bound at `0` supplies the derivative-style mass-bound
contract for any sequence of interval representations.
-/
noncomputable def bookRouteDerivativeMassBoundInput_of_deriv_bound
    {f : ℝ → ℝ} {approximant : ℕ → ℝ → ℝ}
    (approximant_tendsto :
      ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (-1 : ℝ) 1 →
        Tendsto (fun n : ℕ => approximant n x) atTop (𝓝 (f x)))
    (approximant_zero_tendsto :
      Tendsto (fun n : ℕ => approximant n 0) atTop (𝓝 (f 0)))
    (K : ℝ≥0)
    (hK : ∀ n : ℕ, ENNReal.ofReal (deriv (approximant n) 0) ≤ (K : ENNReal)) :
    BookRouteDerivativeMassBoundInput f approximant where
  approximant_tendsto := approximant_tendsto
  approximant_zero_tendsto := approximant_zero_tendsto
  K := K
  mass_le := by
    intro reps n
    exact integralRepOnUnitInterval_mass_le_of_deriv_bound (reps n) (hK n)

/--
Mass-bound data supplies the compactness-level measure-limit contract.
-/
noncomputable def bookRouteMeasureCompactnessInput_of_massBoundInput
    {f : ℝ → ℝ} {approximant : ℕ → ℝ → ℝ}
    (h : BookRouteMassBoundInput f approximant) :
    BookRouteMeasureCompactnessInput f approximant where
  approximant_tendsto := h.approximant_tendsto
  approximant_zero_tendsto := h.approximant_zero_tendsto
  massBound := h.massBound
  mass_le := h.mass_le
  limitMeasure := fun reps =>
    Classical.choose
      (exists_subseq_tendsto_integralRep_measure_of_mass_bound
        (reps := reps) (C := h.massBound reps) (h.mass_le reps))
  subseq := fun reps =>
    Classical.choose
      (Classical.choose_spec
        (exists_subseq_tendsto_integralRep_measure_of_mass_bound
          (reps := reps) (C := h.massBound reps) (h.mass_le reps)))
  subseq_strictMono := by
    intro reps
    exact
      (Classical.choose_spec
        (Classical.choose_spec
          (exists_subseq_tendsto_integralRep_measure_of_mass_bound
            (reps := reps) (C := h.massBound reps) (h.mass_le reps)))).1
  measure_tendsto := by
    intro reps
    exact
      (Classical.choose_spec
        (Classical.choose_spec
          (exists_subseq_tendsto_integralRep_measure_of_mass_bound
            (reps := reps) (C := h.massBound reps) (h.mass_le reps)))).2.1
  limitMeasure_support := by
    intro reps
    exact
      (Classical.choose_spec
        (Classical.choose_spec
          (exists_subseq_tendsto_integralRep_measure_of_mass_bound
            (reps := reps) (C := h.massBound reps) (h.mass_le reps)))).2.2

/--
Measure compactness data supplies kernel convergence via weak convergence and
bounded continuous extension of the book kernel.
-/
noncomputable def bookRouteKernelConvergenceInput_of_measureCompactnessInput
    {f : ℝ → ℝ} {approximant : ℕ → ℝ → ℝ}
    (h : BookRouteMeasureCompactnessInput f approximant) :
    BookRouteKernelConvergenceInput f approximant where
  compactness := h
  kernel_integral_tendsto := by
    intro reps x hx
    let μs : ℕ → FiniteMeasure ℝ := fun k => (reps (h.subseq reps k)).ν
    have hμs :
        ∀ k : ℕ, (μs k : Measure ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
      intro k
      exact (reps (h.subseq reps k)).support
    exact
      bookKernel_integral_tendsto_of_measure_tendsto
        (μs := μs) (μ := h.limitMeasure reps) hμs
        (h.limitMeasure_support reps) (h.measure_tendsto reps) hx

/--
Kernel convergence data over a compactness-only package supplies the combined
measure-limit contract.
-/
noncomputable def bookRouteMeasureLimitInput_of_kernelConvergenceInput
    {f : ℝ → ℝ} {approximant : ℕ → ℝ → ℝ}
    (h : BookRouteKernelConvergenceInput f approximant) :
    BookRouteMeasureLimitInput f approximant where
  approximant_tendsto := h.compactness.approximant_tendsto
  approximant_zero_tendsto := h.compactness.approximant_zero_tendsto
  massBound := h.compactness.massBound
  mass_le := h.compactness.mass_le
  limitMeasure := h.compactness.limitMeasure
  subseq := h.compactness.subseq
  subseq_strictMono := h.compactness.subseq_strictMono
  measure_tendsto := h.compactness.measure_tendsto
  limitMeasure_support := h.compactness.limitMeasure_support
  kernel_integral_tendsto := h.kernel_integral_tendsto

/--
The compactness-level measure-limit contract supplies the previous direct
limit-transfer contract.
-/
noncomputable def bookRouteLimitTransferInput_of_measureLimitInput
    {f : ℝ → ℝ} {approximant : ℕ → ℝ → ℝ}
    (h : BookRouteMeasureLimitInput f approximant) :
    BookRouteLimitTransferInput f approximant where
  approximant_tendsto := h.approximant_tendsto
  approximant_zero_tendsto := h.approximant_zero_tendsto
  limitMeasure := h.limitMeasure
  limitMeasure_support := h.limitMeasure_support
  limitMeasure_formula := by
    intro reps x hx
    let φ : ℕ → ℕ := h.subseq reps
    have hφ : StrictMono φ := h.subseq_strictMono reps
    have hx_real :
        Tendsto (fun k : ℕ => approximant (φ k) x) atTop (𝓝 (f x)) :=
      (h.approximant_tendsto hx).comp hφ.tendsto_atTop
    have hx_complex :
        Tendsto (fun k : ℕ => (approximant (φ k) x : ℂ)) atTop
          (𝓝 (f x : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (f x)).comp hx_real
    have hzero_real :
        Tendsto (fun k : ℕ => approximant (φ k) 0) atTop (𝓝 (f 0)) :=
      h.approximant_zero_tendsto.comp hφ.tendsto_atTop
    have hzero_complex :
        Tendsto (fun k : ℕ => (approximant (φ k) 0 : ℂ)) atTop
          (𝓝 (f 0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (f 0)).comp hzero_real
    have hkernel := h.kernel_integral_tendsto reps hx
    have hrhs :
        Tendsto
          (fun k : ℕ =>
            (approximant (φ k) 0 : ℂ) +
              ∫ t : ℝ, ((x : ℂ) / (1 + (t : ℂ) * x))
                ∂((reps (φ k)).ν : Measure ℝ))
          atTop
          (𝓝
            ((f 0 : ℂ) +
              ∫ t : ℝ, ((x : ℂ) / (1 + (t : ℂ) * x))
                ∂(h.limitMeasure reps : Measure ℝ))) :=
      hzero_complex.add hkernel
    have hseq_eq :
        (fun k : ℕ => (approximant (φ k) x : ℂ)) =
          fun k : ℕ =>
            (approximant (φ k) 0 : ℂ) +
              ∫ t : ℝ, ((x : ℂ) / (1 + (t : ℂ) * x))
                ∂((reps (φ k)).ν : Measure ℝ) := by
      funext k
      exact (reps (φ k)).formula hx
    have hx_limit :
        Tendsto (fun k : ℕ => (approximant (φ k) x : ℂ)) atTop
          (𝓝
            ((f 0 : ℂ) +
              ∫ t : ℝ, ((x : ℂ) / (1 + (t : ℂ) * x))
                ∂(h.limitMeasure reps : Measure ℝ))) := by
      rw [hseq_eq]
      exact hrhs
    exact tendsto_nhds_unique hx_complex hx_limit

/--
The concrete Theorem 20.1 approximation-family contract supplies the generic
approximation-input package.
-/
noncomputable def bookRouteApproximationInput_of_bookApproximationFamilyInput
    {f : ℝ → ℝ} (h : BookApproximationFamilyInput f) :
    BookRouteApproximationInput f where
  approximant := fun n : ℕ => bookSmoothApprox f (h.epsilon n) (h.delta n)
  smoothStrict := h.smoothStrict
  approximant_tendsto := h.limitTransfer.approximant_tendsto
  approximant_zero_tendsto := h.limitTransfer.approximant_zero_tendsto
  limit_integralRep :=
    integralRepOnUnitInterval_of_bookRouteLimitTransferInput h.limitTransfer

/--
Consumer for the approximation package: apply the smooth strict theorem to each
approximant, then use the packaged limit transfer.
-/
noncomputable def integralRepOnUnitInterval_of_bookRouteApproximationInput
    {f : ℝ → ℝ} (h : BookRouteApproximationInput f)
    (smoothRep :
      ∀ g : ℝ → ℝ, SmoothStrictBookRouteInput g → IntegralRepOnUnitInterval g) :
    IntegralRepOnUnitInterval f :=
  h.limit_integralRep fun n => smoothRep (h.approximant n) (h.smoothStrict n)

/--
An approximation-input producer from `GlobalStrictPosDef` gives the abstract
Theorem 20.1 bridge contract.
-/
noncomputable def bookRouteBridge_of_approximationInput
    {f : ℝ → ℝ}
    (toInput : GlobalStrictPosDef f → BookRouteApproximationInput f) :
    BookRouteBridge f where
  reduction := fun h smoothRep =>
    integralRepOnUnitInterval_of_bookRouteApproximationInput
      (toInput h) smoothRep

/--
A producer of the concrete Theorem 20.1 approximation-family input gives the
abstract book-route bridge.
-/
noncomputable def bookRouteBridge_of_bookApproximationFamilyProducer
    {f : ℝ → ℝ}
    (toFamily : GlobalStrictPosDef f → BookApproximationFamilyInput f) :
    BookRouteBridge f :=
  bookRouteBridge_of_approximationInput fun h =>
    bookRouteApproximationInput_of_bookApproximationFamilyInput (toFamily h)

/--
A producer of scaled regularity data and matching measure-limit transfer data
gives the abstract book-route bridge; the `ε g₀` regularity contribution is
added by the closed `g₀` package.
-/
noncomputable def bookRouteBridge_of_scaledRegularityFamilyLimitTransferProducer
    {f : ℝ → ℝ}
    (toScaledRegularity :
      GlobalStrictPosDef f → BookScaledRegularityFamilyInput f)
    (limitTransfer :
      ∀ h : GlobalStrictPosDef f,
        BookRouteLimitTransferInput f
          (fun n : ℕ =>
            bookSmoothApprox f
              ((toScaledRegularity h).epsilon n) ((toScaledRegularity h).delta n))) :
    BookRouteBridge f :=
  bookRouteBridge_of_bookApproximationFamilyProducer fun h =>
    bookApproximationFamilyInput_of_scaledRegularityFamilyInput_of_limitTransfer
      h (toScaledRegularity h) (limitTransfer h)

/--
The packaged scaled-regularity and measure-limit inputs give the abstract
book-route bridge.
-/
noncomputable def bookRouteBridge_of_scaledRegularityLimitTransferInput
    {f : ℝ → ℝ} (input : BookScaledRegularityLimitTransferInput f) :
    BookRouteBridge f :=
  bookRouteBridge_of_scaledRegularityFamilyLimitTransferProducer
    input.toScaledRegularity input.limitTransfer

/--
The compactness-level input supplies the previous limit-transfer package.
-/
noncomputable def bookScaledRegularityLimitTransferInput_of_measureLimitInput
    {f : ℝ → ℝ} (input : BookScaledRegularityMeasureLimitInput f) :
    BookScaledRegularityLimitTransferInput f where
  toScaledRegularity := input.toScaledRegularity
  limitTransfer := fun h =>
    bookRouteLimitTransferInput_of_measureLimitInput (input.measureLimit h)

/--
The separated compactness/kernel-convergence input supplies the
compactness-level package.
-/
noncomputable def bookScaledRegularityMeasureLimitInput_of_kernelConvergenceInput
    {f : ℝ → ℝ} (input : BookScaledRegularityKernelConvergenceInput f) :
    BookScaledRegularityMeasureLimitInput f where
  toScaledRegularity := input.toScaledRegularity
  measureLimit := fun h =>
    bookRouteMeasureLimitInput_of_kernelConvergenceInput
      (input.kernelConvergence h)

/--
The measure-compactness input supplies the separated kernel-convergence
package.
-/
noncomputable def bookScaledRegularityKernelConvergenceInput_of_measureCompactnessInput
    {f : ℝ → ℝ} (input : BookScaledRegularityMeasureCompactnessInput f) :
    BookScaledRegularityKernelConvergenceInput f where
  toScaledRegularity := input.toScaledRegularity
  kernelConvergence := fun h =>
    bookRouteKernelConvergenceInput_of_measureCompactnessInput
      (input.measureCompactness h)

/--
The mass-bound input supplies the measure-compactness package by weak
compactness on `[-1,1]`.
-/
noncomputable def bookScaledRegularityMeasureCompactnessInput_of_massBoundInput
    {f : ℝ → ℝ} (input : BookScaledRegularityMassBoundInput f) :
    BookScaledRegularityMeasureCompactnessInput f where
  toScaledRegularity := input.toScaledRegularity
  measureCompactness := fun h =>
    bookRouteMeasureCompactnessInput_of_massBoundInput
      (input.massBound h)

/--
The derivative-style input supplies the mass-bound package.
-/
noncomputable def bookScaledRegularityMassBoundInput_of_derivativeMassBoundInput
    {f : ℝ → ℝ} (input : BookScaledRegularityDerivativeMassBoundInput f) :
    BookScaledRegularityMassBoundInput f where
  toScaledRegularity := input.toScaledRegularity
  massBound := fun h =>
    bookRouteMassBoundInput_of_derivativeMassBoundInput
      (input.derivativeMassBound h)

/--
A scaled-regularity producer and a uniform derivative bound at `0` for the
concrete approximants supply the derivative mass-bound package.
-/
noncomputable def bookScaledRegularityDerivativeMassBoundInput_of_deriv_bound
    {f : ℝ → ℝ}
    (toScaledRegularity :
      GlobalStrictPosDef f → BookScaledRegularityFamilyInput f)
    (K : GlobalStrictPosDef f → ℝ≥0)
    (hK :
      ∀ h : GlobalStrictPosDef f, ∀ n : ℕ,
        ENNReal.ofReal
          (deriv
            (bookSmoothApprox f
              ((toScaledRegularity h).epsilon n) ((toScaledRegularity h).delta n)) 0) ≤
          (K h : ENNReal)) :
    BookScaledRegularityDerivativeMassBoundInput f where
  toScaledRegularity := toScaledRegularity
  derivativeMassBound := by
    intro h
    let input := toScaledRegularity h
    refine
      bookRouteDerivativeMassBoundInput_of_deriv_bound
        (f := f)
        (approximant := fun n : ℕ =>
          bookSmoothApprox f (input.epsilon n) (input.delta n))
        ?_ ?_ (K h) ?_
    · intro x hx
      exact bookSmoothApprox_tendsto_of_globalStrictPosDef h
        input.delta_tendsto_zero input.epsilon_tendsto_zero hx
    · exact bookSmoothApprox_zero_tendsto_of_params
        (ε := input.epsilon) (δ := input.delta) input.epsilon_tendsto_zero
    · intro n
      simpa [input] using hK h n


end

end Quantum.TraceInequality.Loewner
