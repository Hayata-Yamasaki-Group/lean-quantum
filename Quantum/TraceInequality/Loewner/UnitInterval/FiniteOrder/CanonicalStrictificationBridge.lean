import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.FiniteOrderLadder
import Quantum.TraceInequality.Loewner.RealComplexOrder
import Mathlib.Algebra.Group.ForwardDiff -- finite-difference moments for the finite-order ladder
import Mathlib.Analysis.Calculus.ParametricIntegral -- dominated differentiation under integral
import Mathlib.Analysis.Calculus.Taylor -- finite-order Taylor limits for the smooth Hiai C3 body
import Mathlib.Analysis.Calculus.UniformLimitsDeriv -- local uniform derivative-limit transfer
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Chapter 20 canonical strictification bridge

This file contains the final canonical strictification bridge and public wrappers
that turn finite-order regularity into the interval integral representation.
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

private lemma natCast_withTopENat_le {m n : ℕ} (h : m ≤ n) :
    (m : WithTop ℕ∞) ≤ (n : ℕ) :=
  WithTop.coe_le_coe.mpr (WithTop.coe_le_coe.mpr h)

private lemma natCast_withTopENat_lt {m n : ℕ} (h : m < n) :
    (m : WithTop ℕ∞) < (n : ℕ) :=
  WithTop.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr h)

/-- Public Löwner positivity forces the anchor derivative to be nonnegative. -/
theorem deriv_nonneg_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (h : LoewnerPosOnUnitInterval f) :
    0 ≤ deriv f 0 := by
  have hL :=
    h.posSemidef 1 (fun _ : Fin 1 => (0 : ℝ))
      (by
        intro i
        fin_cases i
        norm_num)
      (by
        intro i j _hij
        fin_cases i
        fin_cases j
        rfl)
  have hdiag := hL.diag_nonneg (i := (0 : Fin 1))
  simpa [loewnerKernel] using hdiag

/--
The public Löwner-positive input gives positive semidefinite Löwner matrices on
any point family satisfying the Chapter 27 `pointsHyp` convention.
-/
theorem loewnerMatrix_posSemidef_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (h : LoewnerPosOnUnitInterval f) {n : ℕ}
    {y : Fin (n + 1) → ℝ} (hy : pointsHyp (n := n) y) :
    (loewnerMatrix (n := n) f y).PosSemidef := by
  simpa [loewnerMatrix] using
    h.posSemidef (n + 1) y hy.2.2.1 hy.2.1

/-- A positive contraction preserves the `pointsHyp` convention. -/
theorem book_pointsHyp_const_mul_of_pos_of_le_one
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {n : ℕ}
    {y : Fin (n + 1) → ℝ} (hy : pointsHyp (n := n) y) :
    pointsHyp (n := n) (fun i : Fin (n + 1) => a * y i) := by
  refine ⟨by simp [hy.1], ?_, ?_, ?_⟩
  · intro i j hij
    exact hy.2.1 (mul_left_cancel₀ ha.ne' hij)
  · intro i
    have hyi := hy.2.2.1 i
    constructor
    · change -1 < a * y i
      by_cases hneg : y i < 0
      · have hle : 1 * y i ≤ a * y i :=
          mul_le_mul_of_nonpos_right ha1 (le_of_lt hneg)
        linarith [hyi.1, hle]
      · have hy_nonneg : 0 ≤ y i := le_of_not_gt hneg
        have hprod_nonneg : 0 ≤ a * y i := mul_nonneg ha.le hy_nonneg
        linarith
    · change a * y i < 1
      by_cases hneg : y i < 0
      · have hprod_neg : a * y i < 0 := mul_neg_of_pos_of_neg ha hneg
        linarith
      · have hlt_a : a * y i < a * 1 := mul_lt_mul_of_pos_left hyi.2 ha
        have ha_le_one : a * 1 ≤ 1 := by simpa using ha1
        exact lt_of_lt_of_le hlt_a ha_le_one
  · intro i hi
    exact mul_ne_zero ha.ne' (hy.2.2.2 i hi)

private theorem loewnerMatrix_comp_const_mul_eq_smul_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hf : LoewnerPosOnUnitInterval f)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {n : ℕ}
    {y : Fin (n + 1) → ℝ} (hy : pointsHyp (n := n) y) :
    loewnerMatrix (n := n) (fun x : ℝ => f (a * x)) y =
      a • loewnerMatrix (n := n) f (fun i : Fin (n + 1) => a * y i) := by
  ext i j
  by_cases hij : y i = y j
  · have hymem : a * y i ∈ Set.Ioo (-1 : ℝ) 1 :=
      (book_pointsHyp_const_mul_of_pos_of_le_one ha ha1 hy).2.2.1 i
    have hlin : HasDerivAt (fun x : ℝ => a * x) a (y i) := by
      simpa using (hasDerivAt_id (y i)).const_mul a
    have hdf := (differentiableAt_of_loewnerPosOnUnitInterval hf hymem).hasDerivAt
    have hcomp : HasDerivAt (fun x : ℝ => f (a * x))
        (a * deriv f (a * y i)) (y i) := by
      simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
        hdf.comp (y i) hlin
    simp [loewnerMatrix, loewnerKernel, hij.symm, hcomp.deriv]
  · have hscaled : a * y i ≠ a * y j := by
      intro h
      exact hij (mul_left_cancel₀ ha.ne' h)
    have hsub : y i - y j ≠ 0 := sub_ne_zero.mpr hij
    simp [loewnerMatrix, loewnerKernel_eq_div (f := fun x : ℝ => f (a * x)) hij,
      loewnerKernel_eq_div (f := f) hscaled]
    field_simp [ha.ne', hsub]

private theorem loewnerMatrix_add_const_mul_eq_of_differentiableAt
    {f g : ℝ → ℝ} {n : ℕ} {y : Fin (n + 1) → ℝ}
    (hf : ∀ i : Fin (n + 1), DifferentiableAt ℝ f (y i))
    (hg : ∀ i : Fin (n + 1), DifferentiableAt ℝ g (y i)) (ε : ℝ) :
    loewnerMatrix (n := n) (fun x : ℝ => f x + ε * g x) y =
      loewnerMatrix (n := n) f y + ε • loewnerMatrix (n := n) g y := by
  ext i j
  by_cases hij : y i = y j
  · have hdf := (hf i).hasDerivAt
    have hdg := (hg i).hasDerivAt
    have hsum : HasDerivAt (fun x : ℝ => f x + ε * g x)
        (deriv f (y i) + ε * deriv g (y i)) (y i) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hdf.add (hdg.const_mul ε)
    simp [loewnerMatrix, loewnerKernel, hij.symm, hsum.deriv]
  · have hsub : y i - y j ≠ 0 := sub_ne_zero.mpr hij
    simp [loewnerMatrix, loewnerKernel_eq_div (f := fun x : ℝ => f x + ε * g x) hij,
      loewnerKernel_eq_div (f := f) hij, loewnerKernel_eq_div (f := g) hij]
    field_simp [hsub]
    ring

/--
Book strictification algebra: a public semidefinite Löwner input becomes strict
after the interior scaling and the positive `ε g₀` perturbation.
-/
theorem bookSmoothApprox_globalStrictPosDef_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hf : LoewnerPosOnUnitInterval f)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    GlobalStrictPosDef (bookSmoothApprox f ε δ) := by
  intro n y hy
  let a : ℝ := 1 - δ
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith [hδ.2]
  have ha_le : a ≤ 1 := by
    dsimp [a]
    linarith [hδ.1]
  have hscaledPSD :
      (loewnerMatrix (n := n) (fun x : ℝ => f (a * x)) y).PosSemidef := by
    have hbase :
        (loewnerMatrix (n := n) f (fun i : Fin (n + 1) => a * y i)).PosSemidef :=
      loewnerMatrix_posSemidef_of_loewnerPosOnUnitInterval hf
        (book_pointsHyp_const_mul_of_pos_of_le_one ha_pos ha_le hy)
    rw [loewnerMatrix_comp_const_mul_eq_smul_of_loewnerPosOnUnitInterval
      hf ha_pos ha_le hy]
    exact hbase.smul (α := ℝ) ha_pos.le
  have hscaledDiff :
      ∀ i : Fin (n + 1), DifferentiableAt ℝ (fun x : ℝ => f (a * x)) (y i) := by
    intro i
    have hymem : a * y i ∈ Set.Ioo (-1 : ℝ) 1 :=
      (book_pointsHyp_const_mul_of_pos_of_le_one ha_pos ha_le hy).2.2.1 i
    have hdf := differentiableAt_of_loewnerPosOnUnitInterval hf hymem
    have hlin : DifferentiableAt ℝ (fun x : ℝ => a * x) (y i) :=
      ((hasDerivAt_id (y i)).const_mul a).differentiableAt
    exact hdf.comp (y i) hlin
  have hg0Diff :
      ∀ i : Fin (n + 1), DifferentiableAt ℝ bookG0 (y i) := by
    intro i
    exact differentiableAt_of_globalStrictPosDef
      bookG0_globalStrictPosDef (hy.2.2.1 i)
  have hg0Pos :
      (ε • loewnerMatrix (n := n) bookG0 y).PosDef :=
    (bookG0_globalStrictPosDef n y hy).smul (α := ℝ) hε
  rw [show
      loewnerMatrix (n := n) (bookSmoothApprox f ε δ) y =
        loewnerMatrix (n := n)
          (fun x : ℝ => f (a * x) + ε * bookG0 x) y by
        rfl]
  rw [loewnerMatrix_add_const_mul_eq_of_differentiableAt hscaledDiff hg0Diff ε]
  exact Matrix.PosDef.posSemidef_add hscaledPSD hg0Pos

/--
The canonical Chapter 20 approximants are smooth strict book-route inputs when
the original public input is Löwner positive and smooth on the interior.
-/
noncomputable def
    bookCanonicalStrictificationApproximant_globalStrictSmoothNeighborhoodInput
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (hfSmooth : ContDiffOn ℝ loewnerBookSmoothOrder f (Set.Ioo (-1 : ℝ) 1)) (n : ℕ) :
    GlobalStrictSmoothNeighborhoodInput
      (bookCanonicalStrictificationApproximant f n) where
  strict := by
    simpa [bookCanonicalStrictificationApproximant] using
      bookSmoothApprox_globalStrictPosDef_of_loewnerPosOnUnitInterval
        hpos (bookEpsilon_pos n) (bookDelta_mem_Ioo n)
  smooth_neighborhood := by
    have hsmooth :=
      (bookSmoothApprox_smooth_neighborhood_of_scaledRegularity
        (bookScaledRegularityFamilyInput_of_interiorSmooth hfSmooth)) n
    simpa [bookCanonicalStrictificationApproximant,
      bookScaledRegularityFamilyInput_of_interiorSmooth,
      bookScaledRegularityFamilyInput_of_interiorSmooth_with_params] using
        hsmooth

/--
The public Löwner-positive input, interior smoothness, and the canonical
measure-limit transfer package assemble the explicit Theorem 20.1
strictification input.
-/
noncomputable def
    bookStrictificationInput_of_loewnerPosOnUnitInterval_of_interiorSmooth_of_limitTransfer
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (hfSmooth : ContDiffOn ℝ loewnerBookSmoothOrder f (Set.Ioo (-1 : ℝ) 1))
    (limitTransfer :
      BookRouteLimitTransferInput f
        (bookCanonicalStrictificationApproximant f)) :
    BookStrictificationInput f where
  pos := hpos
  approximant := bookCanonicalStrictificationApproximant f
  smoothStrict :=
    bookCanonicalStrictificationApproximant_globalStrictSmoothNeighborhoodInput
      hpos hfSmooth
  limitTransfer := limitTransfer

/--
The canonical Chapter 20 approximants converge pointwise to the original
function on the normalized interval.
-/
theorem bookCanonicalStrictificationApproximant_tendsto_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Tendsto
      (fun n : ℕ => bookCanonicalStrictificationApproximant f n x)
      atTop (𝓝 (f x)) := by
  simpa [bookCanonicalStrictificationApproximant] using
    bookSmoothApprox_tendsto_of_params
      bookDelta_tendsto_zero bookEpsilon_tendsto_zero
      (continuousAt_of_loewnerPosOnUnitInterval hpos hx)

/-- The canonical Chapter 20 approximants converge at the anchor `0`. -/
theorem bookCanonicalStrictificationApproximant_zero_tendsto
    {f : ℝ → ℝ} :
    Tendsto
      (fun n : ℕ => bookCanonicalStrictificationApproximant f n 0)
      atTop (𝓝 (f 0)) := by
  simpa [bookCanonicalStrictificationApproximant] using
    bookSmoothApprox_zero_tendsto_of_params
      (f := f) (ε := bookEpsilon) (δ := bookDelta)
      bookEpsilon_tendsto_zero

/--
The concrete canonical perturbation has the book derivative formula at `0`
under the public Löwner-positive input.
-/
theorem bookSmoothApprox_hasDerivAt_zero_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) (ε δ : ℝ) :
    HasDerivAt (bookSmoothApprox f ε δ)
      ((1 - δ) * deriv f 0 + ε * deriv bookG0 0) 0 := by
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  have hdf := (differentiableAt_of_loewnerPosOnUnitInterval hpos h0mem).hasDerivAt
  have hdf_arg : HasDerivAt f (deriv f 0) ((1 - δ) * 0) := by
    simpa using hdf
  have hlin : HasDerivAt (fun x : ℝ => (1 - δ) * x) (1 - δ) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (1 - δ)
  have hscaled :
      HasDerivAt (fun x : ℝ => f ((1 - δ) * x)) ((1 - δ) * deriv f 0) 0 := by
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
      hdf_arg.comp 0 hlin
  have hg0raw :=
    (bookG0_hasDerivAt_of_lt_two (x := (0 : ℝ)) (by norm_num)).const_mul ε
  have hg0 :
      HasDerivAt (fun x : ℝ => ε * bookG0 x)
        (ε * deriv bookG0 0) 0 := by
    simpa [bookG0_deriv_eq_of_lt_two (x := (0 : ℝ)) (by norm_num)] using
      hg0raw
  simpa [bookSmoothApprox] using hscaled.add hg0

/-- Derivative form of the book identity for `f_{ε,δ}` at `0`. -/
theorem bookSmoothApprox_deriv_zero_eq_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) (ε δ : ℝ) :
    deriv (bookSmoothApprox f ε δ) 0 =
      (1 - δ) * deriv f 0 + ε * deriv bookG0 0 :=
  (bookSmoothApprox_hasDerivAt_zero_of_loewnerPosOnUnitInterval
    hpos ε δ).deriv

/--
The book derivative identity is bounded by the derivative of `f` at `0` plus
the size of the positive perturbation parameter.
-/
theorem bookSmoothApprox_deriv_zero_bound_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) {ε δ : ℝ} {Kf E : ℝ≥0}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (hε : 0 ≤ ε)
    (hKf : ENNReal.ofReal (deriv f 0) ≤ (Kf : ENNReal))
    (hE : ENNReal.ofReal ε ≤ (E : ENNReal)) :
    ENNReal.ofReal (deriv (bookSmoothApprox f ε δ) 0) ≤
      ((Kf + E : ℝ≥0) : ENNReal) := by
  have hderiv_nonneg : 0 ≤ deriv f 0 :=
    deriv_nonneg_of_loewnerPosOnUnitInterval hpos
  have hscale_le_one : 1 - δ ≤ 1 := by linarith [hδ.1]
  have hscaled_le : (1 - δ) * deriv f 0 ≤ deriv f 0 :=
    mul_le_of_le_one_left hderiv_nonneg hscale_le_one
  have hg0_le : deriv bookG0 0 ≤ 1 :=
    bookG0_deriv_le_one_on_Icc 0 (by norm_num)
  have heps_le : ε * deriv bookG0 0 ≤ ε :=
    mul_le_of_le_one_right hε hg0_le
  rw [bookSmoothApprox_deriv_zero_eq_of_loewnerPosOnUnitInterval hpos ε δ]
  calc
    ENNReal.ofReal ((1 - δ) * deriv f 0 + ε * deriv bookG0 0)
        ≤ ENNReal.ofReal ((1 - δ) * deriv f 0) +
            ENNReal.ofReal (ε * deriv bookG0 0) :=
          ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (deriv f 0) + ENNReal.ofReal ε :=
          add_le_add (ENNReal.ofReal_le_ofReal hscaled_le)
            (ENNReal.ofReal_le_ofReal heps_le)
    _ ≤ (Kf : ENNReal) + (E : ENNReal) :=
          add_le_add hKf hE
    _ = ((Kf + E : ℝ≥0) : ENNReal) := by
          simp

/-- Canonical derivative bound used in the book equation (20.5) mass estimate. -/
theorem bookCanonicalStrictificationApproximant_deriv_zero_bound
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) (n : ℕ) :
    ENNReal.ofReal
        (deriv (bookCanonicalStrictificationApproximant f n) 0) ≤
      ((Real.toNNReal (deriv f 0) + 1 : ℝ≥0) : ENNReal) := by
  have hKf :
      ENNReal.ofReal (deriv f 0) ≤
        (Real.toNNReal (deriv f 0) : ENNReal) := by
    rw [ENNReal.ofNNReal_toNNReal]
  have hE :
      ENNReal.ofReal (bookEpsilon n) ≤ ((1 : ℝ≥0) : ENNReal) := by
    simpa using ENNReal.ofReal_le_ofReal (bookEpsilon_le_one n)
  simpa [bookCanonicalStrictificationApproximant] using
    bookSmoothApprox_deriv_zero_bound_of_loewnerPosOnUnitInterval
      hpos (bookDelta_mem_Ioo n) (bookEpsilon_pos n).le
      hKf hE

/--
The canonical approximants satisfy the derivative-style mass-bound input needed
for the Chapter 20 limit-transfer pipeline.
-/
noncomputable def
    canonicalStrictificationApproximant_derivativeMassBoundInput_of_loewnerPos
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    BookRouteDerivativeMassBoundInput f
      (bookCanonicalStrictificationApproximant f) :=
  bookRouteDerivativeMassBoundInput_of_deriv_bound
    (f := f)
    (approximant := bookCanonicalStrictificationApproximant f)
    (fun {x} hx =>
      bookCanonicalStrictificationApproximant_tendsto_of_loewnerPosOnUnitInterval
        hpos (x := x) hx)
    bookCanonicalStrictificationApproximant_zero_tendsto
    (Real.toNNReal (deriv f 0) + 1)
    (bookCanonicalStrictificationApproximant_deriv_zero_bound hpos)

/--
Canonical Chapter 20 approximants have the full measure-limit transfer package.
This composes the existing derivative-mass, compactness, kernel-convergence, and
limit-transfer pipeline.
-/
noncomputable def
    canonicalStrictificationApproximant_limitTransferInput_of_loewnerPos
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    BookRouteLimitTransferInput f
      (bookCanonicalStrictificationApproximant f) :=
  let hderiv :=
    canonicalStrictificationApproximant_derivativeMassBoundInput_of_loewnerPos
      hpos
  bookRouteLimitTransferInput_of_measureLimitInput
    (bookRouteMeasureLimitInput_of_kernelConvergenceInput
      (bookRouteKernelConvergenceInput_of_measureCompactnessInput
        (bookRouteMeasureCompactnessInput_of_massBoundInput
          (bookRouteMassBoundInput_of_derivativeMassBoundInput
            hderiv))))

/--
Representation input for the canonical Chapter 20 strictification sequence.

This is the non-smooth input left after the canonical measure-limit transfer
has been discharged from `LoewnerPosOnUnitInterval`.  It is supplied for every
Löwner-positive function by
`canonicalApproximantRepresentationInput_of_loewnerPos_of_publicSmoothRegularity`
applied to `publicSmoothRegularity_of_finiteOrderRegularityInput` (both below).
It does not assert that the canonical approximants are smooth; it only records
the representations needed by the already-proved limit-transfer consumer.
-/
structure BookCanonicalApproximantRepresentationInput (f : ℝ → ℝ) where
  rep :
    ∀ n : ℕ,
      IntegralRepOnUnitInterval
        (bookCanonicalStrictificationApproximant f n)

/--
With the explicit interior smoothness used in the book-route Theorem 20.1
reduction, each canonical Chapter 20 strictification approximant is a smooth
strict input, hence has the interval representation by the closed strict
book-route theorem.
-/
noncomputable def
    bookCanonicalApproximantRepresentationInput_of_interiorSmooth
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (hfSmooth : ContDiffOn ℝ loewnerBookSmoothOrder f (Set.Ioo (-1 : ℝ) 1)) :
    BookCanonicalApproximantRepresentationInput f where
  rep := fun n =>
    strict_hard_direction_unitInterval_bookRoute_of_smoothNeighborhood
      (bookCanonicalStrictificationApproximant_globalStrictSmoothNeighborhoodInput
        hpos hfSmooth n)

/--
Packaged smooth public input supplies the canonical approximant representation
input.  This is not the broad non-smooth public hard direction; it only records
the already-book-route smooth source.
-/
noncomputable def
    bookCanonicalApproximantRepresentationInput_of_loewnerPosInteriorSmoothInput
    {f : ℝ → ℝ} (h : LoewnerPosInteriorSmoothInput f) :
    BookCanonicalApproximantRepresentationInput f :=
  bookCanonicalApproximantRepresentationInput_of_interiorSmooth
    h.pos h.interiorSmooth

/--
If the canonical Chapter 20 approximants have interval representations, the
already-closed canonical limit-transfer package passes them to the original
public Löwner-positive function.
-/
noncomputable def
    integralRepOnUnitInterval_of_loewnerPosOnUnitInterval_of_canonicalApproximantRepresentationInput
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (input : BookCanonicalApproximantRepresentationInput f) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_bookRouteLimitTransferInput
    (canonicalStrictificationApproximant_limitTransferInput_of_loewnerPos
      hpos)
    input.rep

/--
If a public regularity theorem supplies interior smoothness for every public
Löwner-positive function, then the canonical approximant representation input
is discharged by the already-closed smooth-source bridge.

This is a thin bridge only: the regularity theorem it takes as an argument is
`publicSmoothRegularity_of_finiteOrderRegularityInput` below.
-/
noncomputable def
    canonicalApproximantRepresentationInput_of_loewnerPos_of_publicSmoothRegularity
    {f : ℝ → ℝ}
    (regularity :
      ∀ {g : ℝ → ℝ}, LoewnerPosOnUnitInterval g →
        ContDiffOn ℝ loewnerBookSmoothOrder g (Set.Ioo (-1 : ℝ) 1))
    (hpos : LoewnerPosOnUnitInterval f) :
    BookCanonicalApproximantRepresentationInput f :=
  bookCanonicalApproximantRepresentationInput_of_interiorSmooth
    hpos (regularity hpos)

/--
Broad public hard direction conditional on a public smooth-regularity theorem.
The measure-limit and canonical representation consumers are already closed;
only the public smoothness theorem is supplied as an argument here, and it is
`publicSmoothRegularity_of_finiteOrderRegularityInput` below.
-/
noncomputable def
    integralRepresentationOnUnitInterval_of_loewnerPos_of_publicSmoothRegularity
    {f : ℝ → ℝ}
    (regularity :
      ∀ {g : ℝ → ℝ}, LoewnerPosOnUnitInterval g →
        ContDiffOn ℝ loewnerBookSmoothOrder g (Set.Ioo (-1 : ℝ) 1))
    (hpos : LoewnerPosOnUnitInterval f) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_loewnerPosOnUnitInterval_of_canonicalApproximantRepresentationInput
    hpos
    (canonicalApproximantRepresentationInput_of_loewnerPos_of_publicSmoothRegularity
      regularity hpos)

/--
Finite-order public regularity input for the Chapter 20 strictification bridge.

This is not a representation producer.  It records the book/Hiai regularity
ladder supplied below from public Löwner positivity.
-/
structure PublicFiniteOrderRegularityInput : Prop where
  regularity :
    ∀ m : ℕ, ∀ {f : ℝ → ℝ},
      LoewnerPosOnUnitInterval f →
        ContDiffOn ℝ m f (Set.Ioo (-1 : ℝ) 1)

/--
Public Löwner positivity supplies the finite-order regularity package from the
Chapter 20 ladder.
-/
theorem publicFiniteOrderRegularityInput_of_loewnerPosOnUnitInterval :
    PublicFiniteOrderRegularityInput where
  regularity := by
    intro m f hpos
    exact publicFiniteOrderRegularity_of_loewnerPosOnUnitInterval m hpos

/-- Public Löwner positivity gives `C∞` regularity on the interior. -/
theorem publicCInftyRegularity_of_finiteOrderRegularityInput :
    ∀ {f : ℝ → ℝ}, LoewnerPosOnUnitInterval f →
      ContDiffOn ℝ loewnerBookSmoothOrder f (Set.Ioo (-1 : ℝ) 1) := by
  intro f hpos
  rw [contDiffOn_infty]
  intro m
  exact publicFiniteOrderRegularity_of_loewnerPosOnUnitInterval m hpos

/-- Public book `C∞` regularity needed by the canonical approximant bridge. -/
theorem publicSmoothRegularity_of_finiteOrderRegularityInput :
    ∀ {f : ℝ → ℝ}, LoewnerPosOnUnitInterval f →
      ContDiffOn ℝ loewnerBookSmoothOrder f (Set.Ioo (-1 : ℝ) 1) :=
  publicCInftyRegularity_of_finiteOrderRegularityInput

/--
Broad public hard direction conditional on the finite-order Hiai/Loewner
regularity ladder.  The representation side is supplied by the already-closed
canonical bridge.
-/
noncomputable def
    integralRepOnUnitInterval_of_loewnerPosOnUnitInterval_of_finiteOrderRegularityInput
    {f : ℝ → ℝ} (_input : PublicFiniteOrderRegularityInput)
    (hpos : LoewnerPosOnUnitInterval f) :
    IntegralRepOnUnitInterval f :=
  integralRepresentationOnUnitInterval_of_loewnerPos_of_publicSmoothRegularity
    publicSmoothRegularity_of_finiteOrderRegularityInput
    hpos

/--
Smooth public hard direction reconstructed through the canonical approximant
representation input.  This is a bookkeeping wrapper for the smooth source; the
broad non-smooth case is
`integralRepOnUnitInterval_of_loewnerPosOnUnitInterval_of_finiteOrderRegularityInput`
above, with input `publicFiniteOrderRegularityInput_of_loewnerPosOnUnitInterval`.
-/
noncomputable def
    integralRepOnUnitInterval_of_loewnerPosInteriorSmooth_via_canonicalApproximants
    {f : ℝ → ℝ} (h : LoewnerPosInteriorSmoothInput f) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_loewnerPosOnUnitInterval_of_canonicalApproximantRepresentationInput
    h.pos
    (bookCanonicalApproximantRepresentationInput_of_loewnerPosInteriorSmoothInput h)

/--
The explicit strictification package gives the public interval representation.

Each smooth strict approximant is represented by the book-route smooth strict
representation consumer, and the packaged Chapter 20 limit transfer passes to
the original function.
-/
noncomputable def integralRepOnUnitInterval_of_bookStrictificationInput
    {f : ℝ → ℝ} (h : BookStrictificationInput f) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_bookRouteLimitTransferInput
    h.limitTransfer
    (fun n : ℕ =>
      strict_hard_direction_unitInterval_bookRoute_of_smoothNeighborhood
        (h.smoothStrict n))

/--
Conditional public hard direction from the canonical Theorem 20.1
strictification data: the only further input is the canonical limit-transfer
producer, supplied by
`canonicalStrictificationApproximant_limitTransferInput_of_loewnerPos` in
`integralRepOnUnitInterval_of_loewnerPosOnUnitInterval_of_interiorSmooth` below.
-/
noncomputable def
    integralRepOnUnitInterval_of_loewnerPosOnUnitInterval_of_interiorSmooth_of_limitTransfer
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (hfSmooth : ContDiffOn ℝ loewnerBookSmoothOrder f (Set.Ioo (-1 : ℝ) 1))
    (limitTransfer :
      BookRouteLimitTransferInput f
        (bookCanonicalStrictificationApproximant f)) :
    IntegralRepOnUnitInterval f :=
  let input :=
    bookStrictificationInput_of_loewnerPosOnUnitInterval_of_interiorSmooth_of_limitTransfer
      hpos hfSmooth limitTransfer
  integralRepOnUnitInterval_of_bookStrictificationInput input

/--
Book-route hard direction from the public Löwner-positive input plus the
explicit interior smoothness used in Theorem 20.1.  The canonical limit-transfer
producer is supplied internally.
-/
noncomputable def integralRepOnUnitInterval_of_loewnerPosOnUnitInterval_of_interiorSmooth
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (hfSmooth : ContDiffOn ℝ loewnerBookSmoothOrder f (Set.Ioo (-1 : ℝ) 1)) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_loewnerPosOnUnitInterval_of_interiorSmooth_of_limitTransfer
    hpos hfSmooth
    (canonicalStrictificationApproximant_limitTransferInput_of_loewnerPos
      hpos)

end

end Quantum.TraceInequality.Loewner
