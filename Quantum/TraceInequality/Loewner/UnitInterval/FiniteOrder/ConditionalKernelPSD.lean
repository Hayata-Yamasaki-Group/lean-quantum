import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.RegularizedDerivativeContinuity

/-!
# Chapter 20 conditional kernel PSD packaging

This file contains the smooth-Hiai input wrapper, conditional nodewise
dominated-derivative PSD bridges, and the public Löwner quadratic-form
repackaging used before finite-difference source arguments.
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
Conditional packaging for the later book-smooth Hiai input.  Every finite order
`C^m` is supplied by `hiaiRegularization_affinePullback_contDiffOn_anyOrder`
(`RegularizationSmoothness.lean`); the book-smooth order is kept as the explicit
argument here.
-/
noncomputable def hiaiRegularization_affinePullback_smoothHiaiInput
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hsub : Set.Icc (x - r) (x + r) ⊆ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f)
    (hsmooth :
      ContDiffOn ℝ loewnerBookSmoothOrder
        (hiaiRegularizationAffinePullback φ ε f x r)
        (Set.Ioo (-1 : ℝ) 1)) :
    LoewnerPosInteriorSmoothInput
      (hiaiRegularizationAffinePullback φ ε f x r) where
  pos :=
    hiaiRegularization_affinePullback_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hε hr hsub hpos
  interiorSmooth := hsmooth

/--
The diagonal-lower-bound bridge specialized to the existing nodewise
dominated-derivative hypotheses.  In this conditional case the diagonal lower
bound comes from the closed exact diagonal formula, so the theorem is mainly a
compatibility layer.  `regularization_loewnerKernelPSD`
(`RegularizationKernelPSD.lean`) obtains the diagonal lower bound instead from
the clipped Stieltjes convolution.
-/
theorem regularization_loewnerKernelPSD_of_dominated_deriv_on_nodes_diag_ge
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hinj : Function.Injective x) (hpos : LoewnerPosOnUnitInterval f)
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
          (φ t * deriv f (z - ε * t)) z)
    (hdiag_int : ∀ i : Fin n,
      Integrable
        (fun t : ℝ => (φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x i - ε * t) : ℂ))
        (volume.restrict (Ι (-1 : ℝ) 1))) :
    (Matrix.of fun i j : Fin n =>
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)).PosSemidef := by
  have hentry :=
    hiaiRegularization_entry_uIoc_formula_on_nodes_of_dominated_deriv
      (φ := φ) (f := f) hφ hε hx hpos
      (s := s) (bound := bound)
      hs hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
  have hentry_int :=
    hiaiRegularization_loewnerKernel_entry_integrable_on_nodes_of_diag
      (φ := φ) (f := f) hφ hε hx hpos hdiag_int
  exact
    regularization_loewnerKernelPSD_of_offdiag_integral_formula_diag_ge
      (φ := φ) (f := f) hφ hε hx hinj hpos hentry_int
      (by
        intro i j hij
        exact hentry i j)
      (by
        intro i
        rw [← hentry i i])

/--
Conditional PSD transport with nodewise dominated-derivative hypotheses.  The
unconditional PSD transport from `LoewnerPosOnUnitInterval` alone is
`regularization_loewnerKernelPSD` in `RegularizationKernelPSD.lean`.
-/
theorem regularization_loewnerKernelPSD_of_dominated_deriv_on_nodes
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hinj : Function.Injective x) (hpos : LoewnerPosOnUnitInterval f)
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
          (φ t * deriv f (z - ε * t)) z)
    (hterm_int : ∀ c : Fin n → ℂ, ∀ i j : Fin n,
      Integrable
        (fun t : ℝ => star (c i) * ((φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)) * c j)
        (volume.restrict (Ι (-1 : ℝ) 1))) :
    (Matrix.of fun i j : Fin n =>
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)).PosSemidef := by
  exact
    regularization_loewnerKernelPSD_of_entry_integral_formula
      (φ := φ) (f := f) hφ hε hx hinj hpos
      (hiaiRegularization_entry_uIoc_formula_on_nodes_of_dominated_deriv
        (φ := φ) (f := f) hφ hε hx hpos
        (s := s) (bound := bound)
        hs hF_meas hF_int hF'_meas h_bound h_bound_int h_diff)
      hterm_int

/--
Nodewise dominated-derivative PSD transport with the finite quadratic-form
integrability reduced to entrywise integrability.  This removes the test-vector
coefficients from the hypotheses.  The unconditional PSD transport is
`regularization_loewnerKernelPSD` in `RegularizationKernelPSD.lean`.
-/
theorem
    regularization_loewnerKernelPSD_of_dominated_deriv_on_nodes_entryIntegrable
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hinj : Function.Injective x) (hpos : LoewnerPosOnUnitInterval f)
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
          (φ t * deriv f (z - ε * t)) z)
    (hentry_int : ∀ i j : Fin n,
      Integrable
        (fun t : ℝ => (φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ))
        (volume.restrict (Ι (-1 : ℝ) 1))) :
    (Matrix.of fun i j : Fin n =>
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)).PosSemidef := by
  exact
    regularization_loewnerKernelPSD_of_dominated_deriv_on_nodes
      (φ := φ) (f := f) hφ hε hx hinj hpos
      (s := s) (bound := bound)
      hs hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
      (hiaiRegularization_loewnerKernel_entryTerm_integrable_of_entry_integrable
        (φ := φ) (f := f) (ε := ε) (x := x) hentry_int)

/--
Nodewise dominated-derivative PSD transport where finite term integrability is
supplied automatically off the diagonal from public continuity; only diagonal
entry integrability remains explicit.
-/
theorem
    regularization_loewnerKernelPSD_of_dominated_deriv_on_nodes_publicTermIntegrable
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hinj : Function.Injective x) (hpos : LoewnerPosOnUnitInterval f)
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
          (φ t * deriv f (z - ε * t)) z)
    (hdiag_int : ∀ i : Fin n,
      Integrable
        (fun t : ℝ => (φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x i - ε * t) : ℂ))
        (volume.restrict (Ι (-1 : ℝ) 1))) :
    (Matrix.of fun i j : Fin n =>
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)).PosSemidef := by
  exact
    regularization_loewnerKernelPSD_of_dominated_deriv_on_nodes
      (φ := φ) (f := f) hφ hε hx hinj hpos
      (s := s) (bound := bound)
      hs hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
      (hiaiRegularization_entryTerm_integrable_of_publicOffdiag
        (φ := φ) (f := f) hφ hε hx hpos hdiag_int)

/--
Conditional PSD transport for Hiai regularization.

Once the entry formulas have been assembled into the quadratic-form integral
identity, positivity follows by integrating the shifted public PSD quadratic
forms against the nonnegative mollifier.
-/
theorem regularization_loewnerKernelPSD_of_diag_integral_formula
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hinj : Function.Injective x) (hpos : LoewnerPosOnUnitInterval f)
    (hquad_formula : ∀ c : Fin n → ℂ,
      star c ⬝ᵥ
          ((Matrix.of fun i j : Fin n =>
            (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)).mulVec c) =
        ∫ t : ℝ,
          (φ t : ℂ) *
            (star c ⬝ᵥ
              ((Matrix.of fun i j : Fin n =>
                (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)).mulVec c))
          ∂(volume.restrict (Set.Icc (-1 : ℝ) 1))) :
    (Matrix.of fun i j : Fin n =>
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · refine Matrix.IsHermitian.ext ?_
    intro i j
    simp [loewnerKernel_swap]
  · intro c
    rw [hquad_formula c]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hpsd :=
      loewnerKernel_shifted_posSemidef_of_loewnerPosOnUnitInterval
        (f := f) hpos hε hx hinj ht
    exact mul_nonneg
      (by exact_mod_cast hφ.nonneg t)
      (hpsd.dotProduct_mulVec_nonneg c)

/--
Public finite Löwner positivity, in the quadratic-test form used by the Hiai
regularity step.

This is only a repackaging of `LoewnerPosOnUnitInterval.posSemidef`; it does not
itself prove the regularization step that transports PSD to the mollified
functions, which is `regularization_loewnerKernelPSD`
(`RegularizationKernelPSD.lean`).
-/
theorem loewnerKernel_quadratic_nonneg_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (h : LoewnerPosOnUnitInterval f) {n : ℕ}
    {x : Fin n → ℝ} (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    (hinj : Function.Injective x) (v : Fin n → ℂ) :
    0 ≤
      star v ⬝ᵥ
        (Matrix.of
          (fun i j : Fin n => (loewnerKernel f (x i) (x j) : ℂ))).mulVec v :=
  (h.posSemidef n x hx hinj).dotProduct_mulVec_nonneg v

/-- Real-valued PSD form of an arbitrary principal public Löwner matrix. -/
theorem loewnerKernel_real_posSemidef_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) {n : ℕ}
    {x : Fin n → ℝ} (hx : ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1)
    (hinj : Function.Injective x) :
    (Matrix.of
      (fun i j : Fin n => loewnerKernel f (x i) (x j))).PosSemidef := by
  have hpsdC := hpos.posSemidef n x hx hinj
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, Matrix.of_apply, loewnerKernel_swap]
  · intro w
    have hquadC :=
      hpsdC.dotProduct_mulVec_nonneg (fun i : Fin n => (w i : ℂ))
    have hquadC' :
        0 ≤
          ((star w ⬝ᵥ
            (Matrix.mulVec
              (Matrix.of
                (fun i j : Fin n => loewnerKernel f (x i) (x j))) w) : ℝ) : ℂ) := by
      simpa [Matrix.mulVec, dotProduct, Matrix.of_apply,
        Complex.ofReal_sum, Complex.ofReal_mul] using hquadC
    exact (RCLike.ofReal_nonneg (K := ℂ)).1 hquadC'

end

end Quantum.TraceInequality.Loewner
