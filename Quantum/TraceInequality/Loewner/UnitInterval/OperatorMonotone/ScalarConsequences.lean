import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.ScalarConsequencesCore

/-!
# Chapter 3 scalar continuity from reflection

This file contains the reflection and right-jump half of the scalar
continuity consequences of full two-by-two CFC order comparison.
-/

namespace Quantum.TraceInequality.Loewner

universe u

noncomputable section

open scoped ComplexOrder
open scoped Matrix
open scoped MatrixOrder
open scoped Matrix.Norms.L2Operator
open scoped Polynomial
open scoped Topology

/-! ### Reflection for the right jump -/

/-- Reflection of a scalar function across the origin with the order-preserving sign. -/
def reflect (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => - f (-t)

/-- The interval CFC domain is invariant under negation. -/
lemma cFCFiniteMatrixDomain_neg {A : Type u} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a : A}
    (ha : a ∈ {a : A | IsSelfAdjoint a ∧ quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1}) :
    (-a) ∈ {a : A | IsSelfAdjoint a ∧ quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1} := by
  rcases ha with ⟨hsa, hsigma⟩
  refine ⟨hsa.neg, ?_⟩
  intro r hr
  have hneg_mem : -r ∈ quasispectrum ℝ a := by
    rw [Unitization.quasispectrum_eq_spectrum_inr' ℝ ℂ] at hr ⊢
    have hr' : r ∈ spectrum ℝ (-(a : Unitization ℂ A)) := by
      simpa [Unitization.inr_neg] using hr
    have hrneg : r ∈ -spectrum ℝ (a : Unitization ℂ A) := by
      rw [spectrum.neg_eq]
      exact hr'
    simpa [Set.mem_neg] using hrneg
  have hI := hsigma hneg_mem
  exact ⟨by linarith [hI.2], by linarith [hI.1]⟩

/-- The real quasispectrum of `-a` is the pointwise negation of that of `a`. -/
lemma quasispectrum_neg {A : Type u} [NonUnitalCStarAlgebra A] (a : A) :
    quasispectrum ℝ (-a) = (fun r : ℝ => -r) '' quasispectrum ℝ a := by
  ext r
  constructor
  · intro hr
    have hneg_mem : -r ∈ quasispectrum ℝ a := by
      rw [Unitization.quasispectrum_eq_spectrum_inr' ℝ ℂ] at hr ⊢
      have hr' : r ∈ spectrum ℝ (-(a : Unitization ℂ A)) := by
        simpa [Unitization.inr_neg] using hr
      have hrneg : r ∈ -spectrum ℝ (a : Unitization ℂ A) := by
        rw [spectrum.neg_eq]
        exact hr'
      simpa [Set.mem_neg] using hrneg
    exact ⟨-r, hneg_mem, by simp⟩
  · rintro ⟨s, hs, rfl⟩
    rw [Unitization.quasispectrum_eq_spectrum_inr' ℝ ℂ] at hs ⊢
    have hsneg : -s ∈ -spectrum ℝ (a : Unitization ℂ A) := by
      simpa [Set.mem_neg] using hs
    have hsneg' : -s ∈ spectrum ℝ (-(a : Unitization ℂ A)) := by
      simpa [spectrum.neg_eq] using hsneg
    simpa [Unitization.inr_neg] using hsneg'

/--
Composition with negation for non-unital CFC without assuming continuity of the
scalar function up front.

If the scalar function is continuous on the reflected quasispectrum, this is
Mathlib's `cfcₙ_comp_neg`.  If it is not, both sides are the `cfcₙ` junk value,
and the same equality still holds.
-/
lemma cfcₙ_comp_neg_no_cont {A : Type u} [NonUnitalCStarAlgebra A]
    (f : ℝ → ℝ) (a : A) (ha : IsSelfAdjoint a) (hf0 : f 0 = 0) :
    cfcₙ (fun x : ℝ => f (-x)) a = cfcₙ f (-a) := by
  by_cases hf : ContinuousOn f ((fun x : ℝ => -x) '' quasispectrum ℝ a)
  · simpa using
      (cfcₙ_comp_neg (R := ℝ) (A := A) (f := f) (a := a)
        (hf := hf) (h0 := hf0) (ha := ha))
  · have hnot_right : ¬ ContinuousOn f (quasispectrum ℝ (-a)) := by
      simpa [quasispectrum_neg (a := a)] using hf
    have hnot_left :
        ¬ ContinuousOn (fun x : ℝ => f (-x)) (quasispectrum ℝ a) := by
      intro hc
      have hiff :=
        (Homeomorph.neg ℝ).isEmbedding.isInducing.continuousOn_image_iff
          (g := f) (s := quasispectrum ℝ a)
      have himg : ContinuousOn f ((fun x : ℝ => -x) '' quasispectrum ℝ a) := by
        exact hiff.mpr (by simpa [Function.comp_def] using hc)
      exact hf himg
    rw [cfcₙ_apply_of_not_continuousOn (a := a) hnot_left,
      cfcₙ_apply_of_not_continuousOn (a := -a) hnot_right]

/--
The normalized CFC expression for `reflect f` is the negative CFC of `f`
at `-a`.
-/
lemma cfcₙ_reflect_normalized_eq_neg_cfcₙ_neg
    {A : Type u} [NonUnitalCStarAlgebra A] (f : ℝ → ℝ) {a : A}
    (ha : IsSelfAdjoint a) :
    cfcₙ (fun x : ℝ => reflect f x - reflect f 0) a =
      -cfcₙ (fun x : ℝ => f x - f 0) (-a) := by
  let h : ℝ → ℝ := fun x => f x - f 0
  have hfun :
      (fun x : ℝ => reflect f x - reflect f 0) =
        fun x : ℝ => -h (-x) := by
    funext x
    simp [reflect, h]
    ring
  rw [hfun, cfcₙ_neg,
    cfcₙ_comp_neg_no_cont (f := h) (a := a) (ha := ha)
      (hf0 := by simp [h])]

/-- Finite matrix monotonicity is invariant under the book reflection. -/
theorem unitIntervalFiniteMatrixMonotone_reflect {f : ℝ → ℝ}
    (hfinite : UnitIntervalFiniteMatrixMonotone.{u} f) :
    UnitIntervalFiniteMatrixMonotone.{u} (reflect f) where
  cfc_monotone_finite := by
    intro A _ _ _ _ a ha b hb hab
    have hnorm_a :=
      cfcₙ_reflect_normalized_eq_neg_cfcₙ_neg (f := f) (a := a) ha.1
    have hnorm_b :=
      cfcₙ_reflect_normalized_eq_neg_cfcₙ_neg (f := f) (a := b) hb.1
    have hneg_b := cFCFiniteMatrixDomain_neg hb
    have hneg_a := cFCFiniteMatrixDomain_neg ha
    have hle_neg : -b ≤ -a := by
      exact neg_le_neg hab
    have hmono := hfinite.cfc_monotone_finite (A := A)
    have hbase :
        cfcₙ (fun x : ℝ => f x - f 0) (-b) ≤
          cfcₙ (fun x : ℝ => f x - f 0) (-a) :=
      hmono hneg_b hneg_a hle_neg
    change cfcₙ (fun x : ℝ => reflect f x - reflect f 0) a ≤
      cfcₙ (fun x : ℝ => reflect f x - reflect f 0) b
    rw [hnorm_a, hnorm_b]
    exact neg_le_neg hbase

/-- W version: invariance of matrix monotonicity under the reflection of the book. -/
theorem unitIntervalMatrixMonotone_reflect {f : ℝ → ℝ}
    (hmatrix : UnitIntervalMatrixMonotone f) :
    UnitIntervalMatrixMonotone (reflect f) where
  cfc_monotone_matrix := by
    intro n a ha b hb hab
    haveI : StarOrderedRing (CStarMatrix (Fin n) (Fin n) ℂ) :=
      CStarMatrix.instStarOrderedRing
    haveI : IsOrderedAddMonoid (CStarMatrix (Fin n) (Fin n) ℂ) :=
      StarOrderedRing.toIsOrderedAddMonoid
    have hnorm_a :=
      cfcₙ_reflect_normalized_eq_neg_cfcₙ_neg (f := f) (a := a) ha.1
    have hnorm_b :=
      cfcₙ_reflect_normalized_eq_neg_cfcₙ_neg (f := f) (a := b) hb.1
    have hneg_b :=
      @cFCFiniteMatrixDomain_neg (CStarMatrix (Fin n) (Fin n) ℂ)
        inferInstance CStarMatrix.instPartialOrder
        CStarMatrix.instStarOrderedRing b hb
    have hneg_a :=
      @cFCFiniteMatrixDomain_neg (CStarMatrix (Fin n) (Fin n) ℂ)
        inferInstance CStarMatrix.instPartialOrder
        CStarMatrix.instStarOrderedRing a ha
    have hle_neg : -b ≤ -a := by
      exact @neg_le_neg (CStarMatrix (Fin n) (Fin n) ℂ) inferInstance
        CStarMatrix.instPartialOrder StarOrderedRing.toIsOrderedAddMonoid
        a b hab
    have hmono := hmatrix.cfc_monotone_matrix n
    have hbase :
        cfcₙ (fun x : ℝ => f x - f 0) (-b) ≤
          cfcₙ (fun x : ℝ => f x - f 0) (-a) :=
      hmono hneg_b hneg_a hle_neg
    have hbase_neg :
        -cfcₙ (fun x : ℝ => f x - f 0) (-a) ≤
          -cfcₙ (fun x : ℝ => f x - f 0) (-b) := by
      exact @neg_le_neg (CStarMatrix (Fin n) (Fin n) ℂ) inferInstance
        CStarMatrix.instPartialOrder StarOrderedRing.toIsOrderedAddMonoid
        (cfcₙ (fun x : ℝ => f x - f 0) (-b))
        (cfcₙ (fun x : ℝ => f x - f 0) (-a)) hbase
    calc
      cfcₙ (fun x : ℝ => reflect f x - reflect f 0) a =
          -cfcₙ (fun x : ℝ => f x - f 0) (-a) := hnorm_a
      _ ≤ -cfcₙ (fun x : ℝ => f x - f 0) (-b) := hbase_neg
      _ = cfcₙ (fun x : ℝ => reflect f x - reflect f 0) b :=
        hnorm_b.symm

/-- Negation sends a left-neighborhood of `-x` to a right-neighborhood of `x`. -/
lemma neg_tendsto_nhdsLT_to_nhdsGT (x : ℝ) :
    Filter.Tendsto (fun t : ℝ => -t) (𝓝[<] (-x)) (𝓝[>] x) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (by
      simpa using
        ((continuousAt_neg (x := -x)).tendsto.mono_left inf_le_left)) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [Set.mem_Ioi]
  rw [Set.mem_Iio] at ht
  linarith

/--
The left scalar limit of the reflected function is the negative of the right
scalar limit of the original function, once the reflected finite-matrix
monotonicity is available.
-/
theorem scalarLeftLimitValue_reflect_eq_neg_rightLimit
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    (hreflect : UnitIntervalMatrixMonotone (reflect f))
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    scalarLeftLimitValue (reflect f) (-x) =
      -scalarRightLimitValue f x := by
  have hxneg : -x ∈ Set.Ioo (-1 : ℝ) 1 := by
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hleft :=
    scalarLeftLimit_tendsto hreflect hxneg
  have hright :=
    (scalarRightLimit_tendsto hfinite hx).comp
      (neg_tendsto_nhdsLT_to_nhdsGT x)
  have hright_reflect :
      Filter.Tendsto (reflect f) (𝓝[<] (-x))
        (𝓝 (-scalarRightLimitValue f x)) := by
    simpa [reflect] using
      ((continuousAt_neg (x := scalarRightLimitValue f x)).tendsto.comp hright)
  exact tendsto_nhds_unique hleft hright_reflect

/-! ### Scalar continuity from full two-by-two CFC order comparison -/

/-- The left scalar limit from full `2×2` CFC order comparison is below the point value. -/
theorem scalarLeftLimit_le_value_of_twoByTwo_cfc_order
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    scalarLeftLimitValue f x ≤ f x := by
  have hmono := scalarMonotoneOn_Ioo_of_twoByTwo_cfc_order h2
  refine csSup_le (Set.image_nonempty.mpr (Set.nonempty_Ioo.mpr hx.1)) ?_
  intro z hz
  rcases hz with ⟨a, ha, rfl⟩
  exact hmono ⟨ha.1, lt_trans ha.2 hx.2⟩ hx (le_of_lt ha.2)

/-- The right scalar limit from full `2×2` CFC order comparison is above the point value. -/
theorem scalarValue_le_rightLimit_of_twoByTwo_cfc_order
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    f x ≤ scalarRightLimitValue f x := by
  have hmono := scalarMonotoneOn_Ioo_of_twoByTwo_cfc_order h2
  refine le_csInf (Set.image_nonempty.mpr (Set.nonempty_Ioo.mpr hx.2)) ?_
  intro z hz
  rcases hz with ⟨a, ha, rfl⟩
  exact hmono hx ⟨lt_trans hx.1 ha.1, ha.2⟩ (le_of_lt ha.1)

/-- The lower left-path branch sees the scalar left limit under full `2×2` comparison. -/
theorem scalarLeftLimit_tendsto_twoPointEigenLow_leftPath_of_twoByTwo_cfc_order
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Filter.Tendsto
      (fun δ : ℝ => f (twoPointOrderRayEigenLow x (x - δ) δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (scalarLeftLimitValue f x)) :=
  (scalarLeftLimit_tendsto_of_twoByTwo_cfc_order h2 hx).comp
    (twoPointOrderRayEigenLow_leftPath_tendsto_left x)

/-- The moving node `x - δ` sees the scalar left limit under full `2×2` comparison. -/
theorem scalarLeftLimit_tendsto_x_sub_delta_of_twoByTwo_cfc_order
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Filter.Tendsto (fun δ : ℝ => f (x - δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (scalarLeftLimitValue f x)) :=
  (scalarLeftLimit_tendsto_of_twoByTwo_cfc_order h2 hx).comp
    (x_sub_delta_tendsto_left x)

/--
Full `2×2` CFC order comparison gives positivity of the CFC difference along
the left special path `(x, x - δ, δ)`.
-/
theorem twoPointCFCOrderRayDifference_nonneg_leftPath_eventually_of_twoByTwo_cfc_order
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      0 ≤ twoPointCFCOrderRayDifference f x (x - δ) δ := by
  filter_upwards
    [twoPointCStarDiagonal_leftPath_mem_domain_eventually hx,
      twoPointCStarOrderRay_leftPath_mem_domain_eventually hx,
      self_mem_nhdsWithin] with δ hbase hray hδpos
  have hle_ray :
      cStarDiagonalMatrix (twoPointNodes x (x - δ)) ≤
        twoPointCStarOrderRayMatrix x (x - δ) δ :=
    twoPointCStarOrderRay_le_of_nonneg x (x - δ) (le_of_lt hδpos)
  have hle :=
    h2 hbase hray hle_ray
  simpa [twoPointCFCOrderRayDifference] using sub_nonneg.mpr hle

/--
Full `2×2` CFC order comparison gives nonnegative named quadratic tests along
the left special path.
-/
theorem
  twoPointCFCOrderRayDifference_testVector_nonneg_leftPath_eventually_of_twoByTwo_cfc_order
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (c : Fin 2 → ℂ) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      0 ≤ twoPointCFCOrderRayDifferenceTest f x (x - δ) δ c := by
  filter_upwards
    [twoPointCFCOrderRayDifference_nonneg_leftPath_eventually_of_twoByTwo_cfc_order
      h2 hx] with δ hnonneg
  simpa [twoPointCFCOrderRayDifferenceTest] using
    cStarMatrix_quadratic_nonneg_of_nonneg hnonneg c

/--
The left-special-path null-vector test converges to the scalar left jump under
full `2×2` CFC order comparison.
-/
theorem
  twoPointCFCOrderRayDifference_leftPath_nullVector_tendsto_leftGap_of_twoByTwo_cfc_order
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Filter.Tendsto
      (fun δ : ℝ =>
        twoPointCFCOrderRayDifferenceTest f x (x - δ) δ
          twoPointOrderRayLeftPathNullVector)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((scalarLeftLimitValue f x - f x : ℝ) : ℂ)) := by
  let β : ℝ := twoPointOrderRayLeftPathHighCoeff
  let L : ℝ := scalarLeftLimitValue f x
  have hformula :
      (fun δ : ℝ =>
        twoPointCFCOrderRayDifferenceTest f x (x - δ) δ
          twoPointOrderRayLeftPathNullVector)
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun δ : ℝ =>
        (((1 + β ^ 2) *
            f (twoPointOrderRayEigenLow x (x - δ) δ) -
          f x - β ^ 2 * f (x - δ) : ℝ) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    simpa [β] using
      twoPointCFCOrderRayDifference_leftPath_nullVector_formula
        f x hδ
  have hlow :
      Filter.Tendsto
        (fun δ : ℝ => f (twoPointOrderRayEigenLow x (x - δ) δ))
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    simpa [L] using
      scalarLeftLimit_tendsto_twoPointEigenLow_leftPath_of_twoByTwo_cfc_order
        h2 hx
  have hnode :
      Filter.Tendsto (fun δ : ℝ => f (x - δ))
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    simpa [L] using
      scalarLeftLimit_tendsto_x_sub_delta_of_twoByTwo_cfc_order h2 hx
  have hlow_scaled :
      Filter.Tendsto
        (fun δ : ℝ =>
          (1 + β ^ 2) * f (twoPointOrderRayEigenLow x (x - δ) δ))
        (𝓝[>] (0 : ℝ)) (𝓝 ((1 + β ^ 2) * L)) :=
    hlow.const_mul (1 + β ^ 2)
  have hnode_scaled :
      Filter.Tendsto (fun δ : ℝ => β ^ 2 * f (x - δ))
        (𝓝[>] (0 : ℝ)) (𝓝 (β ^ 2 * L)) :=
    hnode.const_mul (β ^ 2)
  have hreal :
      Filter.Tendsto
        (fun δ : ℝ =>
          (1 + β ^ 2) *
              f (twoPointOrderRayEigenLow x (x - δ) δ) -
            f x - β ^ 2 * f (x - δ))
        (𝓝[>] (0 : ℝ))
        (𝓝 ((1 + β ^ 2) * L - f x - β ^ 2 * L)) :=
    (hlow_scaled.sub tendsto_const_nhds).sub hnode_scaled
  have htarget : (1 + β ^ 2) * L - f x - β ^ 2 * L = L - f x := by
    ring
  exact (Filter.tendsto_ofReal_iff.mpr (by simpa [htarget] using hreal)).congr'
    hformula.symm

/-- Left jump exclusion from full `2×2` CFC order comparison. -/
theorem scalarNoLeftJump_of_twoByTwo_cfc_order
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    scalarLeftLimitValue f x = f x := by
  have hnonneg_eventually :
      ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        0 ≤ twoPointCFCOrderRayDifferenceTest f x (x - δ) δ
          twoPointOrderRayLeftPathNullVector :=
  twoPointCFCOrderRayDifference_testVector_nonneg_leftPath_eventually_of_twoByTwo_cfc_order
      h2 hx twoPointOrderRayLeftPathNullVector
  have hlim :=
    twoPointCFCOrderRayDifference_leftPath_nullVector_tendsto_leftGap_of_twoByTwo_cfc_order
      h2 hx
  have hnonnegC :
      0 ≤ ((scalarLeftLimitValue f x - f x : ℝ) : ℂ) :=
    ge_of_tendsto hlim hnonneg_eventually
  have hnonnegR : 0 ≤ scalarLeftLimitValue f x - f x := by
    exact_mod_cast hnonnegC
  have hle := scalarLeftLimit_le_value_of_twoByTwo_cfc_order h2 hx
  linarith

/-- Full `2×2` CFC order comparison is invariant under the book reflection. -/
theorem twoByTwo_cfc_order_reflect
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B) :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => reflect f t - reflect f 0) A ≤
            cfcₙ (fun t : ℝ => reflect f t - reflect f 0) B := by
  intro A B hA hB hAB
  haveI : StarOrderedRing (CStarMatrix (Fin 2) (Fin 2) ℂ) :=
    CStarMatrix.instStarOrderedRing
  haveI : IsOrderedAddMonoid (CStarMatrix (Fin 2) (Fin 2) ℂ) :=
    StarOrderedRing.toIsOrderedAddMonoid
  have hnorm_A :=
    cfcₙ_reflect_normalized_eq_neg_cfcₙ_neg (f := f) (a := A) hA.1
  have hnorm_B :=
    cfcₙ_reflect_normalized_eq_neg_cfcₙ_neg (f := f) (a := B) hB.1
  have hneg_B :=
    @cFCFiniteMatrixDomain_neg (CStarMatrix (Fin 2) (Fin 2) ℂ)
      inferInstance CStarMatrix.instPartialOrder
      CStarMatrix.instStarOrderedRing B hB
  have hneg_A :=
    @cFCFiniteMatrixDomain_neg (CStarMatrix (Fin 2) (Fin 2) ℂ)
      inferInstance CStarMatrix.instPartialOrder
      CStarMatrix.instStarOrderedRing A hA
  have hAB_neg : -B ≤ -A := by
    exact @neg_le_neg (CStarMatrix (Fin 2) (Fin 2) ℂ) inferInstance
      CStarMatrix.instPartialOrder StarOrderedRing.toIsOrderedAddMonoid
      A B hAB
  have hbase :
      cfcₙ (fun x : ℝ => f x - f 0) (-B) ≤
        cfcₙ (fun x : ℝ => f x - f 0) (-A) :=
    h2 hneg_B hneg_A hAB_neg
  have hbase_neg :
      -cfcₙ (fun x : ℝ => f x - f 0) (-A) ≤
        -cfcₙ (fun x : ℝ => f x - f 0) (-B) := by
    exact @neg_le_neg (CStarMatrix (Fin 2) (Fin 2) ℂ) inferInstance
      CStarMatrix.instPartialOrder StarOrderedRing.toIsOrderedAddMonoid
      (cfcₙ (fun x : ℝ => f x - f 0) (-B))
      (cfcₙ (fun x : ℝ => f x - f 0) (-A)) hbase
  calc
    cfcₙ (fun t : ℝ => reflect f t - reflect f 0) A =
        -cfcₙ (fun x : ℝ => f x - f 0) (-A) := hnorm_A
    _ ≤ -cfcₙ (fun x : ℝ => f x - f 0) (-B) := hbase_neg
    _ = cfcₙ (fun t : ℝ => reflect f t - reflect f 0) B := hnorm_B.symm

/--
The left scalar limit of the reflected function is the negative of the right
scalar limit of the original function under full `2×2` CFC order comparison.
-/
theorem scalarLeftLimitValue_reflect_eq_neg_rightLimit_of_twoByTwo_cfc_order
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
      cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    scalarLeftLimitValue (reflect f) (-x) =
      -scalarRightLimitValue f x := by
  have hreflect :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => reflect f t - reflect f 0) A ≤
            cfcₙ (fun t : ℝ => reflect f t - reflect f 0) B := by
    intro A B hA hB hAB
    exact twoByTwo_cfc_order_reflect h2 hA hB hAB
  have hxneg : -x ∈ Set.Ioo (-1 : ℝ) 1 := by
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hleft :=
    scalarLeftLimit_tendsto_of_twoByTwo_cfc_order
      hreflect hxneg
  have hright :=
    (scalarRightLimit_tendsto_of_twoByTwo_cfc_order h2 hx).comp
      (neg_tendsto_nhdsLT_to_nhdsGT x)
  have hright_reflect :
      Filter.Tendsto (reflect f) (𝓝[<] (-x))
        (𝓝 (-scalarRightLimitValue f x)) := by
    simpa [reflect] using
      ((continuousAt_neg (x := scalarRightLimitValue f x)).tendsto.comp hright)
  exact tendsto_nhds_unique hleft hright_reflect

/-- Right jump exclusion from full `2×2` CFC order comparison. -/
theorem scalarNoRightJump_of_twoByTwo_cfc_order
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
      cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    scalarRightLimitValue f x = f x := by
  have hreflect :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => reflect f t - reflect f 0) A ≤
            cfcₙ (fun t : ℝ => reflect f t - reflect f 0) B := by
    intro A B hA hB hAB
    exact twoByTwo_cfc_order_reflect h2 hA hB hAB
  have hxneg : -x ∈ Set.Ioo (-1 : ℝ) 1 := by
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hleft :=
    scalarNoLeftJump_of_twoByTwo_cfc_order
      hreflect hxneg
  have hlimit :=
    scalarLeftLimitValue_reflect_eq_neg_rightLimit_of_twoByTwo_cfc_order
      h2 hx
  have hneg_eq : -scalarRightLimitValue f x = -f x := by
    calc
      -scalarRightLimitValue f x =
          scalarLeftLimitValue (reflect f) (-x) := hlimit.symm
      _ = reflect f (-x) := hleft
      _ = -f x := by simp [reflect]
  exact neg_injective hneg_eq

/-- Full `2×2` CFC order comparison gives scalar continuity at every interior point. -/
theorem twoByTwo_cfc_order_localContinuity
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ContinuousAt f x := by
  have hleftT := scalarLeftLimit_tendsto_of_twoByTwo_cfc_order h2 hx
  have hrightT := scalarRightLimit_tendsto_of_twoByTwo_cfc_order h2 hx
  have hleftEq := scalarNoLeftJump_of_twoByTwo_cfc_order h2 hx
  have hrightEq := scalarNoRightJump_of_twoByTwo_cfc_order h2 hx
  refine continuousAt_iff_continuous_left'_right'.2 ⟨?_, ?_⟩
  · simpa [ContinuousWithinAt, hleftEq] using hleftT
  · simpa [ContinuousWithinAt, hrightEq] using hrightT


end

end Quantum.TraceInequality.Loewner
