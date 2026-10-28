import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.Relevel
import Quantum.TraceInequality.Loewner.HalfLine.AH1
import Quantum.TraceInequality.Loewner.HalfLine.AH1Retained
import Quantum.Analysis.CStar.FiniteDimensionalStructure.PrimitivesRetained
import Quantum.TraceInequality.HansenPedersen.Basic
import Quantum.TraceInequality.JensenOperatorInequalityIImpIVRetained
import Quantum.TraceInequality.LownerHeinz.ReciprocalRetained

/-!
# Bendat--Sherman slope criterion on the positive ray

This file closes the positive-ray specialization of Hiai, Corollary 2.7.8.
The removable value at the base point is obtained by comparing the continuous
local divided differences.  In the representation steps we keep the normalized
kernel intact: it is uniformly bounded on every compact positive spectrum, so
the finite representing measure is enough and no extra moment hypothesis is
introduced.
-/

namespace Quantum.TraceInequality.Loewner

universe u v

open CFC Set MeasureTheory Filter

open scoped NNReal Topology MatrixOrder CStarAlgebra ComplexOrder FinMatrixCStar

noncomputable section

/-! ### A finite-measure divided-difference calculation -/

private def interiorDividedKuboDensity (s t : ℝ) : ENNReal :=
  ENNReal.ofReal (t ^ 2 / (s + t))

private def interiorDividedKuboKernel (s y t : ℝ) : ℝ :=
  (1 + t) * (y * s + t * (y + s)) / ((y + t) * (s + t))

private theorem measurable_interiorDividedKuboDensity (s : ℝ) :
    Measurable (interiorDividedKuboDensity s) := by
  unfold interiorDividedKuboDensity
  fun_prop

private theorem interiorDividedKuboDensity_ne_top_ae
    (s : ℝ) (μ : Measure ℝ) :
    ∀ᵐ t ∂μ, interiorDividedKuboDensity s t < (⊤ : ENNReal) := by
  exact ae_of_all _ fun t => by
    simp [interiorDividedKuboDensity]

private theorem interiorDividedKuboDensity_toReal
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (interiorDividedKuboDensity s t).toReal = t ^ 2 / (s + t) := by
  rw [interiorDividedKuboDensity, ENNReal.toReal_ofReal]
  positivity

private theorem interiorDividedKuboKernel_eq_dividedDifference
    {s y t : ℝ} (hs : 0 < s) (hy : 0 < y) (ht : 0 < t)
    (hys : y ≠ s) :
    interiorDividedKuboKernel s y t =
      (positiveRayOperatorConvexFiniteRightDerivativeKernel y t -
          positiveRayOperatorConvexFiniteRightDerivativeKernel s t) /
        (y - s) := by
  rw [eq_div_iff (sub_ne_zero.mpr hys)]
  unfold interiorDividedKuboKernel
    positiveRayOperatorConvexFiniteRightDerivativeKernel
  field_simp
  ring

private theorem interiorDividedKuboKernel_sub_one
    {s y t : ℝ} (hs : 0 < s) (hy : 0 < y) (ht : 0 < t) :
    interiorDividedKuboKernel s y t - interiorDividedKuboKernel s 1 t =
      (t ^ 2 / (s + t)) * halfLineKernel y t := by
  unfold interiorDividedKuboKernel halfLineKernel
  field_simp
  ring

private theorem interiorDividedKuboKernel_nonneg
    {s y t : ℝ} (hs : 0 < s) (hy : 0 < y) (ht : 0 < t) :
    0 ≤ interiorDividedKuboKernel s y t := by
  unfold interiorDividedKuboKernel
  positivity

private theorem interiorDividedKuboKernel_le_bound
    {s y t : ℝ} (hs : 0 < s) (hy : 0 < y) (ht : 0 < t) :
    interiorDividedKuboKernel s y t ≤
      2 * (1 + y) * (1 + s) := by
  have hst : 0 < s + t := by linarith
  have hyt : 0 < y + t := by linarith
  have hden : 0 < (y + t) * (s + t) := mul_pos hyt hst
  let C : ℝ := 2 * (1 + y) * (1 + s)
  have hC_two : 2 ≤ C := by
    dsimp [C]
    nlinarith [mul_pos hy hs]
  have hC_one : 1 ≤ C := by linarith
  have hC_ys : y * s + y + s ≤ C := by
    dsimp [C]
    nlinarith [mul_pos hy hs]
  have hC_sum : y + s ≤ C := by linarith [mul_pos hy hs]
  have hC_mid : y * s + y + s ≤ C * (y + s) := by
    by_cases hsum : 1 ≤ y + s
    · exact le_trans hC_ys (le_mul_of_one_le_right (by positivity) hsum)
    · have hsum' : y + s < 1 := lt_of_not_ge hsum
      have hys_le : y * s ≤ y + s := by nlinarith [mul_pos hy hs]
      calc
        y * s + y + s ≤ 2 * (y + s) := by linarith
        _ ≤ C * (y + s) :=
          mul_le_mul_of_nonneg_right hC_two (by positivity)
  unfold interiorDividedKuboKernel
  rw [div_le_iff₀ hden]
  change
    (1 + t) * (y * s + t * (y + s)) ≤
      C * ((y + t) * (s + t))
  calc
    (1 + t) * (y * s + t * (y + s)) =
        y * s + t * (y * s + y + s) + t ^ 2 * (y + s) := by ring
    _ ≤ C * (y * s) + t * (C * (y + s)) + t ^ 2 * C := by
      exact add_le_add
        (add_le_add
          (by
            simpa using
              (mul_le_mul_of_nonneg_right hC_one (mul_nonneg hy.le hs.le)))
          (mul_le_mul_of_nonneg_left hC_mid ht.le))
        (mul_le_mul_of_nonneg_left hC_sum (sq_nonneg t))
    _ = C * ((y + t) * (s + t)) := by ring

private theorem interiorDividedKuboKernel_integrable
    {q : ℝ → ℝ} (rep : PositiveRayKuboAndoRep q)
    {s y : ℝ} (hs : 0 < s) (hy : 0 < y) :
    Integrable (fun t : ℝ => interiorDividedKuboKernel s y t)
      (rep.ν : Measure ℝ) := by
  let C : ℝ := 2 * (1 + y) * (1 + s)
  refine Integrable.mono (integrable_const C)
    (by
      unfold interiorDividedKuboKernel
      exact
        ((measurable_const.add measurable_id).mul
          (measurable_const.add (measurable_id.mul measurable_const))).div
            ((measurable_const.add measurable_id).mul
              (measurable_const.add measurable_id)) |>.aestronglyMeasurable)
    ?_
  filter_upwards [positiveRayKuboAndoRep_ae_mem_Ioi rep] with t ht
  have htpos : 0 < t := ht
  have hnonneg := interiorDividedKuboKernel_nonneg hs hy htpos
  rw [Real.norm_of_nonneg hnonneg]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  rw [Real.norm_of_nonneg hC]
  exact interiorDividedKuboKernel_le_bound hs hy htpos

private theorem finiteRightDerivativeKernel_integrable
    {q : ℝ → ℝ} (rep : PositiveRayKuboAndoRep q)
    {y : ℝ} (hy : 0 < y) :
    Integrable
      (fun t : ℝ => positiveRayOperatorConvexFiniteRightDerivativeKernel y t)
      (rep.ν : Measure ℝ) := by
  refine Integrable.mono (integrable_const (y * max y 1))
    (by
      unfold positiveRayOperatorConvexFiniteRightDerivativeKernel
      exact
        (measurable_const.mul (measurable_const.add measurable_id)).div
          (measurable_const.add measurable_id) |>.aestronglyMeasurable)
    ?_
  filter_upwards [positiveRayKuboAndoRep_ae_mem_Ioi rep] with t ht
  have htpos : 0 < t := ht
  have hden : 0 < y + t := by linarith
  have hkernel_nonneg :
      0 ≤ positiveRayOperatorConvexFiniteRightDerivativeKernel y t := by
    unfold positiveRayOperatorConvexFiniteRightDerivativeKernel
    positivity
  rw [Real.norm_of_nonneg hkernel_nonneg]
  have hbound_nonneg : 0 ≤ y * max y 1 := by positivity
  rw [Real.norm_of_nonneg hbound_nonneg]
  unfold positiveRayOperatorConvexFiniteRightDerivativeKernel
  by_cases hy1 : y ≤ 1
  · have hle : y * (1 + t) ≤ y + t := by nlinarith
    rw [div_le_iff₀ hden]
    have hmax : max y 1 = 1 := max_eq_right hy1
    rw [hmax, mul_one]
    nlinarith
  · have hge : 1 ≤ y := le_of_not_ge hy1
    have hle : y * (1 + t) ≤ y * (y + t) := by nlinarith
    rw [div_le_iff₀ hden]
    have hmax : max y 1 = y := max_eq_left hge
    rw [hmax]
    nlinarith

private def interiorDividedHalfLineMeasure
    {q : ℝ → ℝ} (rep : PositiveRayKuboAndoRep q) (s : ℝ) : Measure ℝ :=
  (rep.ν : Measure ℝ).withDensity (interiorDividedKuboDensity s)

private theorem interiorDividedHalfLineMeasure_support
    {q : ℝ → ℝ} (rep : PositiveRayKuboAndoRep q) (s : ℝ) :
    interiorDividedHalfLineMeasure rep s (Set.Ici (0 : ℝ))ᶜ = 0 := by
  have hac :
      interiorDividedHalfLineMeasure rep s ≪ (rep.ν : Measure ℝ) :=
    withDensity_absolutelyContinuous _ _
  apply hac
  exact measure_mono_null
    (compl_subset_compl.mpr (Set.Ioi_subset_Ici_self : Set.Ioi (0 : ℝ) ⊆ Set.Ici 0))
    rep.support

private theorem interiorDividedKuboDensity_mul_weight_le_one
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    interiorDividedKuboDensity s t * halfLineWeight t ≤ 1 := by
  have hst : 0 < s + t := by linarith
  have h1t : 0 < 1 + t := by linarith
  have hnonneg : 0 ≤ t ^ 2 / (s + t) := by positivity
  have hprod : t ^ 2 / (s + t) * (1 + t)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ h1t]
    rw [div_le_iff₀ hst]
    nlinarith [mul_pos hs h1t]
  calc
    interiorDividedKuboDensity s t * halfLineWeight t =
        ENNReal.ofReal (t ^ 2 / (s + t)) * ENNReal.ofReal ((1 + t)⁻¹) := rfl
    _ = ENNReal.ofReal (t ^ 2 / (s + t) * (1 + t)⁻¹) := by
      rw [ENNReal.ofReal_mul hnonneg]
    _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hprod
    _ = 1 := ENNReal.ofReal_one

private theorem interiorDividedHalfLineMeasure_weight_lintegral_lt_top
    {q : ℝ → ℝ} (rep : PositiveRayKuboAndoRep q)
    {s : ℝ} (hs : 0 < s) :
    (∫⁻ t : ℝ, halfLineWeight t ∂interiorDividedHalfLineMeasure rep s) < ⊤ := by
  have hrewrite :
      (∫⁻ t : ℝ, halfLineWeight t ∂interiorDividedHalfLineMeasure rep s) =
        ∫⁻ t : ℝ, interiorDividedKuboDensity s t * halfLineWeight t
          ∂(rep.ν : Measure ℝ) := by
    simpa [interiorDividedHalfLineMeasure] using
      (lintegral_withDensity_eq_lintegral_mul
        (rep.ν : Measure ℝ)
        (measurable_interiorDividedKuboDensity s)
        measurable_halfLineWeight)
  rw [hrewrite]
  calc
    (∫⁻ t : ℝ, interiorDividedKuboDensity s t * halfLineWeight t
        ∂(rep.ν : Measure ℝ)) ≤
        ∫⁻ _t : ℝ, (1 : ENNReal) ∂(rep.ν : Measure ℝ) := by
      apply lintegral_mono_ae
      filter_upwards [positiveRayKuboAndoRep_ae_mem_Ioi rep] with t ht
      exact interiorDividedKuboDensity_mul_weight_le_one hs ht
    _ = (rep.ν : Measure ℝ) Set.univ := by simp
    _ < ⊤ := measure_lt_top _ _

private def interiorDividedSlope
    {q : ℝ → ℝ} (ell s : ℝ) (rep : PositiveRayKuboAndoRep q) : ℝ → ℝ :=
  fun y =>
    ell + q 0 + (rep.b : ℝ) * (y + s) +
      ∫ t : ℝ, interiorDividedKuboKernel s y t ∂(rep.ν : Measure ℝ)

private theorem interiorDividedHalfLineMeasure_integral
    {q : ℝ → ℝ} (rep : PositiveRayKuboAndoRep q)
    {s y : ℝ} (hs : 0 < s) (hy : 0 < y) :
    (∫ t : ℝ, halfLineKernel y t ∂interiorDividedHalfLineMeasure rep s) =
      ∫ t : ℝ,
        (interiorDividedKuboKernel s y t - interiorDividedKuboKernel s 1 t)
        ∂(rep.ν : Measure ℝ) := by
  calc
    (∫ t : ℝ, halfLineKernel y t ∂interiorDividedHalfLineMeasure rep s) =
        ∫ t : ℝ,
          (interiorDividedKuboDensity s t).toReal • halfLineKernel y t
          ∂(rep.ν : Measure ℝ) := by
      exact integral_withDensity_eq_integral_toReal_smul
        (measurable_interiorDividedKuboDensity s)
        (interiorDividedKuboDensity_ne_top_ae s (rep.ν : Measure ℝ)) _
    _ = ∫ t : ℝ,
        (interiorDividedKuboKernel s y t - interiorDividedKuboKernel s 1 t)
        ∂(rep.ν : Measure ℝ) := by
      apply integral_congr_ae
      filter_upwards [positiveRayKuboAndoRep_ae_mem_Ioi rep] with t ht
      have htpos : 0 < t := ht
      rw [interiorDividedKuboDensity_toReal hs htpos]
      simpa [smul_eq_mul] using
        (interiorDividedKuboKernel_sub_one hs hy htpos).symm

private noncomputable def halfLineIntegralRep_interiorDividedSlope
    {q : ℝ → ℝ} (ell : ℝ) {s : ℝ} (hs : 0 < s)
    (rep : PositiveRayKuboAndoRep q) :
    HalfLineIntegralRep (interiorDividedSlope ell s rep) where
  b := rep.b
  μ := interiorDividedHalfLineMeasure rep s
  support := interiorDividedHalfLineMeasure_support rep s
  weight_lintegral_lt_top :=
    interiorDividedHalfLineMeasure_weight_lintegral_lt_top rep hs
  formula := by
    intro y hy
    have hypos : 0 < y := hy
    have hint_y := interiorDividedKuboKernel_integrable rep hs hypos
    have hint_one := interiorDividedKuboKernel_integrable rep hs zero_lt_one
    rw [interiorDividedHalfLineMeasure_integral rep hs hypos]
    rw [integral_sub hint_y hint_one]
    simp [interiorDividedSlope, interiorDividedKuboKernel]
    ring

private theorem finiteRightDerivativeKernel_integral_eq
    {q : ℝ → ℝ} (rep : PositiveRayKuboAndoRep q)
    {y : ℝ} (_hy : 0 < y) :
    (∫ t : ℝ, positiveRayOperatorConvexFiniteRightDerivativeKernel y t
        ∂(rep.ν : Measure ℝ)) =
      y * ∫ t : ℝ, positiveRayKuboAndoKernel y t
        ∂(rep.ν : Measure ℝ) := by
  calc
    (∫ t : ℝ, positiveRayOperatorConvexFiniteRightDerivativeKernel y t
        ∂(rep.ν : Measure ℝ)) =
        ∫ t : ℝ, y * positiveRayKuboAndoKernel y t
          ∂(rep.ν : Measure ℝ) := by
      apply integral_congr_ae
      filter_upwards [positiveRayKuboAndoRep_ae_mem_Ioi rep] with t ht
      unfold positiveRayOperatorConvexFiniteRightDerivativeKernel
        positiveRayKuboAndoKernel
      ring
    _ = y * ∫ t : ℝ, positiveRayKuboAndoKernel y t
        ∂(rep.ν : Measure ℝ) := by rw [integral_const_mul]

private theorem interiorDividedKuboKernel_integral_eq
    {q : ℝ → ℝ} (rep : PositiveRayKuboAndoRep q)
    {s y : ℝ} (hs : 0 < s) (hy : 0 < y) (hys : y ≠ s) :
    (∫ t : ℝ, interiorDividedKuboKernel s y t ∂(rep.ν : Measure ℝ)) =
      ((∫ t : ℝ, positiveRayOperatorConvexFiniteRightDerivativeKernel y t
          ∂(rep.ν : Measure ℝ)) -
        ∫ t : ℝ, positiveRayOperatorConvexFiniteRightDerivativeKernel s t
          ∂(rep.ν : Measure ℝ)) / (y - s) := by
  have hint_y := finiteRightDerivativeKernel_integrable rep hy
  have hint_s := finiteRightDerivativeKernel_integrable rep hs
  calc
    (∫ t : ℝ, interiorDividedKuboKernel s y t ∂(rep.ν : Measure ℝ)) =
        ∫ t : ℝ,
          (positiveRayOperatorConvexFiniteRightDerivativeKernel y t -
              positiveRayOperatorConvexFiniteRightDerivativeKernel s t) /
            (y - s) ∂(rep.ν : Measure ℝ) := by
      apply integral_congr_ae
      filter_upwards [positiveRayKuboAndoRep_ae_mem_Ioi rep] with t ht
      exact interiorDividedKuboKernel_eq_dividedDifference hs hy ht hys
    _ = ((∫ t : ℝ, positiveRayOperatorConvexFiniteRightDerivativeKernel y t
          ∂(rep.ν : Measure ℝ)) -
        ∫ t : ℝ, positiveRayOperatorConvexFiniteRightDerivativeKernel s t
          ∂(rep.ν : Measure ℝ)) / (y - s) := by
      simp_rw [div_eq_mul_inv, mul_comm _ (y - s)⁻¹]
      rw [integral_const_mul, integral_sub hint_y hint_s]

private theorem interiorDividedSlope_eq_dividedDifference
    {q : ℝ → ℝ} (ell : ℝ) {s y : ℝ} (hs : 0 < s) (hy : 0 < y)
    (hys : y ≠ s) (rep : PositiveRayKuboAndoRep q) :
    interiorDividedSlope ell s rep y =
      (y * (ell + q y) - s * (ell + q s)) / (y - s) := by
  have hqy := rep.formula hy.le
  have hqs := rep.formula hs.le
  have hIy := finiteRightDerivativeKernel_integral_eq rep hy
  have hIs := finiteRightDerivativeKernel_integral_eq rep hs
  have hID := interiorDividedKuboKernel_integral_eq rep hs hy hys
  unfold interiorDividedSlope
  rw [hID, hIy, hIs]
  rw [hqy, hqs]
  field_simp [sub_ne_zero.mpr hys]
  ring

private theorem operatorMonotoneOnPositive_interiorDividedSlope
    {q : ℝ → ℝ} (ell : ℝ) {s : ℝ} (hs : 0 < s)
    (rep : PositiveRayKuboAndoRep q) :
    OperatorMonotoneOnPositive.{u} (interiorDividedSlope ell s rep) := by
  rw [operatorMonotoneOnPositive_iff_nonempty_halfLineIntegralRep]
  exact ⟨halfLineIntegralRep_interiorDividedSlope ell hs rep⟩

/-! ### Moving an interior point to the closed endpoint -/

private def interiorEndpointShift (f : ℝ → ℝ) (r ell : ℝ) : ℝ → ℝ :=
  fun y => f (r + y) - f r - ell * y

private theorem positiveRayMat_spectrum_subset_Ioi_of_posDef
    {n : ℕ} {X : HansenPedersen.Mₙ n} (hX : X.PosDef) :
    spectrum ℝ X ⊆ Set.Ioi (0 : ℝ) := by
  intro x hx
  rw [Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues
    (𝕜 := ℂ) hX.isHermitian] at hx
  rcases hx with ⟨i, rfl⟩
  exact hX.eigenvalues_pos i

private theorem positiveRayMatrixOperatorConvex_of_operatorConvexOnPositive
    {f : ℝ → ℝ} (hf : OperatorConvexOnPositive f) :
    PositiveRayMatrixOperatorConvex (positiveRayMatrixCfc f) := by
  intro n X Y θ hX hY hθ0 hθ1
  cases n with
  | zero => exact le_of_eq (Subsingleton.elim _ _)
  | succ n =>
      have hθ'0 : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
      have hθ'1 : 1 - θ ≤ 1 := by linarith
      have hmain :=
        (hf.operatorConvexOn (𝓑 := HansenPedersen.Mₙ (n + 1)))
          hX.isHermitian hY.isHermitian hθ'0 hθ'1
          (positiveRayMat_spectrum_subset_Ioi_of_posDef hX)
          (positiveRayMat_spectrum_subset_Ioi_of_posDef hY)
      rw [positiveRayMatrixCfc_eq_cfcR_of_isHermitian X hX.isHermitian,
        positiveRayMatrixCfc_eq_cfcR_of_isHermitian Y hY.isHermitian]
      have hcombo :
          positiveRayMatrixConvexCombo θ X Y =
            (1 - (1 - θ)) • X + (1 - θ) • Y := by
        ext i j
        simp only [positiveRayMatrixConvexCombo, Matrix.add_apply, Matrix.smul_apply,
          smul_eq_mul, Complex.real_smul]
        ring_nf
      rw [hcombo]
      have hcomboHerm :
          ((1 - (1 - θ)) • X + (1 - θ) • Y).IsHermitian := by
        rw [← hcombo]
        exact positiveRay_isHermitian_convexCombo θ hX.isHermitian hY.isHermitian
      rw [positiveRayMatrixCfc_eq_cfcR_of_isHermitian _ hcomboHerm]
      simpa using hmain

private theorem operatorConvexOnPositive_continuousOn
    {f : ℝ → ℝ} (hf : OperatorConvexOnPositive f) :
    ContinuousOn f (Set.Ioi (0 : ℝ)) := by
  have hmatrix : PositiveRayMatrixOperatorConvex (positiveRayMatrixCfc f) :=
    @positiveRayMatrixOperatorConvex_of_operatorConvexOnPositive f (@hf)
  exact PositiveRayScalarConvex.continuousOn_Ioi
    (positiveRayScalarConvex_of_matrixOperatorConvex hmatrix)

private theorem positiveRayMatrixCfc_interiorEndpointShift_eq
    {f : ℝ → ℝ} (hfcont : ContinuousOn f (Set.Ioi (0 : ℝ)))
    {r ell : ℝ} (hr : 0 < r) {n : ℕ} {X : HansenPedersen.Mₙ n}
    (hXherm : X.IsHermitian) (hXnonneg : X.PosSemidef) :
    positiveRayMatrixCfc (interiorEndpointShift f r ell) n X =
      positiveRayMatrixCfc f n (X + r • (1 : HansenPedersen.Mₙ n)) -
        algebraMap ℝ (HansenPedersen.Mₙ n) (f r) - ell • X := by
  have hshiftPos : (X + r • (1 : HansenPedersen.Mₙ n)).PosDef :=
    positiveRayMat_add_pos_scalar_one_posDef hXnonneg hr
  have hshiftSpec :
      spectrum ℝ (X + r • (1 : HansenPedersen.Mₙ n)) ⊆ Set.Ioi (0 : ℝ) :=
    positiveRayMat_spectrum_subset_Ioi_of_posDef hshiftPos
  have hXSpec : spectrum ℝ X ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    rw [Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues
      (𝕜 := ℂ) hXherm] at hx
    rcases hx with ⟨i, rfl⟩
    exact hXnonneg.eigenvalues_nonneg i
  let shift : ℝ → ℝ := fun y => r + y
  have hshiftCont : ContinuousOn shift (spectrum ℝ X) := by
    exact continuous_const.add continuous_id |>.continuousOn
  have hshiftImage : shift '' spectrum ℝ X ⊆ Set.Ioi (0 : ℝ) := by
    rintro z ⟨x, hx, rfl⟩
    have hx0 : 0 ≤ x := hXSpec hx
    dsimp [shift]
    simpa only [Set.mem_Ioi] using add_pos_of_pos_of_nonneg hr hx0
  have hfShift : ContinuousOn f (shift '' spectrum ℝ X) :=
    hfcont.mono hshiftImage
  have hcomp :
      cfc (fun y : ℝ => f (shift y)) X =
        cfc f (cfc shift X) :=
    cfc_comp' f shift X hfShift hshiftCont
  have hcfcShift : cfc shift X = X + r • (1 : HansenPedersen.Mₙ n) := by
    calc
      cfc shift X = cfc (fun _y : ℝ => r) X + cfc id X := by
        dsimp [shift]
        exact cfc_add X (fun _y : ℝ => r) id
      _ = algebraMap ℝ (HansenPedersen.Mₙ n) r + X := by
        have hconst := cfc_const r X hXherm
        have hid := cfc_id ℝ X hXherm
        rw [hconst, hid]
      _ = X + r • (1 : HansenPedersen.Mₙ n) := by
        simp [add_comm, Algebra.smul_def]
  have hfCompCont : ContinuousOn (fun y : ℝ => f (r + y)) (spectrum ℝ X) :=
    hfShift.comp hshiftCont fun x hx => ⟨x, hx, rfl⟩
  have hconstCfc :
      cfc (fun _y : ℝ => f r) X = algebraMap ℝ (HansenPedersen.Mₙ n) (f r) :=
    cfc_const (f r) X hXherm
  have hlinearCfc : cfc (fun y : ℝ => ell * y) X = ell • X := by
    calc
      cfc (fun y : ℝ => ell * y) X = ell • cfc id X :=
        cfc_const_mul ell id X
      _ = ell • X := congrArg (fun Z : HansenPedersen.Mₙ n => ell • Z)
        (cfc_id ℝ X hXherm)
  rw [positiveRayMatrixCfc_eq_cfcR_of_isHermitian X hXherm,
    positiveRayMatrixCfc_eq_cfcR_of_isHermitian _ hshiftPos.isHermitian]
  change cfc (interiorEndpointShift f r ell) X =
    cfc f (X + r • (1 : HansenPedersen.Mₙ n)) -
      algebraMap ℝ (HansenPedersen.Mₙ n) (f r) - ell • X
  unfold interiorEndpointShift
  calc
    cfc (fun y : ℝ => f (r + y) - f r - ell * y) X =
        cfc (fun y : ℝ => f (r + y) - f r) X -
          cfc (fun y : ℝ => ell * y) X := by
      exact cfc_sub _ _ X
        (hf := hfCompCont.sub continuousOn_const)
        (hg := continuousOn_const.mul continuousOn_id)
    _ = (cfc (fun y : ℝ => f (r + y)) X -
          cfc (fun _y : ℝ => f r) X) -
          cfc (fun y : ℝ => ell * y) X := by
      rw [cfc_sub (hf := hfCompCont) (hg := continuousOn_const)]
    _ = cfc f (X + r • (1 : HansenPedersen.Mₙ n)) -
          algebraMap ℝ (HansenPedersen.Mₙ n) (f r) - ell • X := by
      rw [hconstCfc, hlinearCfc]
      rw [show (fun y : ℝ => f (r + y)) = fun y : ℝ => f (shift y) by rfl,
        hcomp, hcfcShift]

private theorem closedMatrixConvex_interiorEndpointShift
    {f : ℝ → ℝ} (hf : OperatorConvexOnPositive f)
    {r ell : ℝ} (hr : 0 < r) :
    PositiveRayClosedMatrixOperatorConvex
      (positiveRayMatrixCfc (interiorEndpointShift f r ell)) := by
  intro n X Y θ hXherm hYherm hXnonneg hYnonneg hθ0 hθ1
  cases n with
  | zero => exact le_of_eq (Subsingleton.elim _ _)
  | succ n =>
      have hfcont := operatorConvexOnPositive_continuousOn (@hf)
      have hXr : (X + r • (1 : HansenPedersen.Mₙ (n + 1))).PosDef :=
        positiveRayMat_add_pos_scalar_one_posDef hXnonneg hr
      have hYr : (Y + r • (1 : HansenPedersen.Mₙ (n + 1))).PosDef :=
        positiveRayMat_add_pos_scalar_one_posDef hYnonneg hr
      have hmatrix :=
        @positiveRayMatrixOperatorConvex_of_operatorConvexOnPositive f (@hf)
      have hmain := hmatrix hXr hYr hθ0 hθ1
      have hcomboHerm :=
        positiveRay_isHermitian_convexCombo θ hXherm hYherm
      have hcomboNonneg :=
        positiveRayMatrixConvexCombo_posSemidef hXnonneg hYnonneg hθ0 hθ1
      rw [positiveRayMatrixCfc_interiorEndpointShift_eq hfcont hr
          hcomboHerm hcomboNonneg,
        positiveRayMatrixCfc_interiorEndpointShift_eq hfcont hr
          hXherm hXnonneg,
        positiveRayMatrixCfc_interiorEndpointShift_eq hfcont hr
          hYherm hYnonneg]
      rw [← positiveRayMatrixConvexCombo_add_scalar_one]
      let Z : HansenPedersen.Mₙ (n + 1) :=
        algebraMap ℝ (HansenPedersen.Mₙ (n + 1)) (f r) +
          ell • positiveRayMatrixConvexCombo θ X Y
      calc
        positiveRayMatrixCfc f (n + 1)
              (positiveRayMatrixConvexCombo θ
                (X + r • (1 : HansenPedersen.Mₙ (n + 1)))
                (Y + r • (1 : HansenPedersen.Mₙ (n + 1)))) -
              algebraMap ℝ (HansenPedersen.Mₙ (n + 1)) (f r) -
              ell • positiveRayMatrixConvexCombo θ X Y =
            positiveRayMatrixCfc f (n + 1)
              (positiveRayMatrixConvexCombo θ
                (X + r • (1 : HansenPedersen.Mₙ (n + 1)))
                (Y + r • (1 : HansenPedersen.Mₙ (n + 1)))) - Z := by
          dsimp [Z]
          abel
        _ ≤ positiveRayMatrixConvexCombo θ
              (positiveRayMatrixCfc f (n + 1) (X + r • (1 : HansenPedersen.Mₙ (n + 1))))
              (positiveRayMatrixCfc f (n + 1) (Y + r • (1 : HansenPedersen.Mₙ (n + 1)))) -
            Z := sub_le_sub_right hmain Z
        _ = positiveRayMatrixConvexCombo θ
              (positiveRayMatrixCfc f (n + 1) (X + r • (1 : HansenPedersen.Mₙ (n + 1))) -
                algebraMap ℝ (HansenPedersen.Mₙ (n + 1)) (f r) - ell • X)
              (positiveRayMatrixCfc f (n + 1) (Y + r • (1 : HansenPedersen.Mₙ (n + 1))) -
                algebraMap ℝ (HansenPedersen.Mₙ (n + 1)) (f r) - ell • Y) := by
          dsimp [Z, positiveRayMatrixConvexCombo]
          module

private theorem convexOn_Ioi_of_operatorConvexOnPositive
    {f : ℝ → ℝ} (hf : OperatorConvexOnPositive f) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) f := by
  refine ⟨convex_Ioi (0 : ℝ), ?_⟩
  intro x hx y hy a b ha hb hab
  have hb_eq : b = 1 - a := by linarith
  have ha1 : a ≤ 1 := by linarith
  have hscalar : PositiveRayScalarConvex f :=
    @positiveRayScalarConvex_of_matrixOperatorConvex f
      (@positiveRayMatrixOperatorConvex_of_operatorConvexOnPositive f (@hf))
  simpa [hb_eq, smul_eq_mul] using hscalar hx hy ha ha1

private def interiorLowerSlope (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  (f r - f (r / 2)) / (r - r / 2)

private def interiorUpperSlope (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  (f (2 * r) - f r) / (2 * r - r)

private theorem endpointLinearControl_interiorEndpointShift
    {f : ℝ → ℝ} (hf : OperatorConvexOnPositive f)
    {r : ℝ} (hr : 0 < r) :
    PositiveRayEndpointLinearControl
      (fun y : ℝ => interiorEndpointShift f r (interiorLowerSlope f r) y -
        interiorEndpointShift f r (interiorLowerSlope f r) 0) := by
  let ell : ℝ := interiorLowerSlope f r
  let U : ℝ := interiorUpperSlope f r
  have hconv := convexOn_Ioi_of_operatorConvexOnPositive (@hf)
  have hrhalf : 0 < r / 2 := by positivity
  have hr2 : 0 < 2 * r := by linarith
  have hhalf_r : r / 2 < r := by linarith
  have hr_2r : r < 2 * r := by linarith
  have hC : 0 ≤ U - ell := by
    have hmono := hconv.slope_mono_adjacent
      (show r / 2 ∈ Set.Ioi (0 : ℝ) by exact hrhalf)
      (show 2 * r ∈ Set.Ioi (0 : ℝ) by exact hr2)
      hhalf_r hr_2r
    simpa [ell, U, interiorLowerSlope, interiorUpperSlope] using hmono
  refine ⟨U - ell, hC, ?_⟩
  have hsmall : ∀ᶠ y in 𝓝[>] (0 : ℝ), y < r :=
    (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with y hy0 hyr
  have hy : 0 < y := by simpa using hy0
  have hry : r < r + y := by linarith
  have hry2 : r + y < 2 * r := by linarith
  let m : ℝ := (f (r + y) - f r) / ((r + y) - r)
  have hlower : ell ≤ m := by
    have hmono := hconv.slope_mono_adjacent
      (show r / 2 ∈ Set.Ioi (0 : ℝ) by exact hrhalf)
      (show r + y ∈ Set.Ioi (0 : ℝ) by exact add_pos hr hy)
      hhalf_r hry
    simpa [ell, m, interiorLowerSlope] using hmono
  have hupper : m ≤ U := by
    have hmono := hconv.secant_mono
      (show r ∈ Set.Ioi (0 : ℝ) by exact hr)
      (show r + y ∈ Set.Ioi (0 : ℝ) by exact add_pos hr hy)
      (show 2 * r ∈ Set.Ioi (0 : ℝ) by exact hr2)
      (by linarith) (by linarith) (by linarith)
    simpa [m, U, interiorUpperSlope] using hmono
  have hm : f (r + y) - f r = y * m := by
    dsimp [m]
    field_simp [ne_of_gt hy]
    ring
  change 0 ≤ interiorEndpointShift f r (interiorLowerSlope f r) y -
      interiorEndpointShift f r (interiorLowerSlope f r) 0 ∧
    interiorEndpointShift f r (interiorLowerSlope f r) y -
        interiorEndpointShift f r (interiorLowerSlope f r) 0 ≤
      (U - ell) * y
  simp only [interiorEndpointShift, add_zero, sub_self, mul_zero, sub_zero]
  change 0 ≤ f (r + y) - f r - ell * y ∧
    f (r + y) - f r - ell * y ≤ (U - ell) * y
  rw [hm]
  constructor
  · nlinarith
  · nlinarith

private structure LocalInteriorSlopeData (f : ℝ → ℝ) (r : ℝ) where
  k : ℝ → ℝ
  monotone : OperatorMonotoneOnPositive.{u} k
  formula :
    ∀ {y : ℝ}, 0 < y → y ≠ 1 - r →
      k y = (f (r + y) - f 1) / (r + y - 1)

private noncomputable def localInteriorSlopeData
    {f : ℝ → ℝ} (hf : OperatorConvexOnPositive f)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    LocalInteriorSlopeData.{u} f r := by
  let ell : ℝ := interiorLowerSlope f r
  let H : ℝ → ℝ := interiorEndpointShift f r ell
  have hclosed : PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc H) := by
    exact closedMatrixConvex_interiorEndpointShift (@hf) hr
  have hlin : PositiveRayEndpointLinearControl (fun y : ℝ => H y - H 0) := by
    exact endpointLinearControl_interiorEndpointShift (@hf) hr
  let hex := exists_endpointQuotient_rightContinuous_of_closedMatrixConvex_endpointControl
    hclosed hlin
  let d : ℝ := Classical.choose hex
  have hd := Classical.choose_spec hex
  have hright := hd.1
  have hquot := hd.2
  let q : ℝ → ℝ := positiveRayEndpointQuotient H d
  have hmatrix : UnitIntervalMatrixMonotone (positiveCayleyPullback q) := by
    apply unitIntervalMatrixMonotone_of_finiteMatrixMonotone
    refine ⟨?_⟩
    intro A _ _ _ _ a ha b hb hab
    exact positiveRay_cfcₙ_sub_endpoint_le
      (h := H) (d := d) hclosed hlin
      ha.1 hb.1 ha.2 hb.2 hab
  have hqclosed : OperatorMonotoneOnClosedPositive.{0} q := by
    exact operatorMonotoneOnClosedPositive_endpointQuotient_of_unitIntervalFiniteMatrixMonotone
      hmatrix hright
  let rep : PositiveRayKuboAndoRep q :=
    positiveRayKuboAndoRep_of_operatorMonotoneOnClosedPositive hqclosed
  let s : ℝ := 1 - r
  have hs : 0 < s := by dsimp [s]; linarith
  let k : ℝ → ℝ := interiorDividedSlope ell s rep
  have hk : OperatorMonotoneOnPositive.{u} k := by
    exact operatorMonotoneOnPositive_interiorDividedSlope ell hs rep
  refine ⟨k, hk, ?_⟩
  intro y hy hys
  have hqy : H y = y * q y := by
    have := hquot (show y ∈ Set.Ioi (0 : ℝ) by exact hy)
    have hH0 : H 0 = 0 := by simp [H, interiorEndpointShift]
    simpa [q, d, hH0] using this
  have hqs : H s = s * q s := by
    have := hquot (show s ∈ Set.Ioi (0 : ℝ) by exact hs)
    have hH0 : H 0 = 0 := by simp [H, interiorEndpointShift]
    simpa [q, d, hH0] using this
  have hkraw := interiorDividedSlope_eq_dividedDifference ell hs hy hys rep
  change interiorDividedSlope ell s rep y =
    (f (r + y) - f 1) / (r + y - 1)
  rw [hkraw]
  have hFy : y * (ell + q y) = f (r + y) - f r := by
    dsimp [H, interiorEndpointShift] at hqy
    nlinarith
  have hFs : s * (ell + q s) = f 1 - f r := by
    have hrs : r + s = 1 := by dsimp [s]; ring
    dsimp [H, interiorEndpointShift] at hqs
    rw [hrs] at hqs
    nlinarith
  rw [hFy, hFs]
  have hden : y - s = r + y - 1 := by
    dsimp [s]
    ring
  rw [hden]
  ring

/-! ### The removable value at the base point -/

private theorem continuousAt_positiveToUnitCayley_of_pos
    {x : ℝ} (hx : 0 < x) :
    ContinuousAt positiveToUnitCayley x := by
  unfold positiveToUnitCayley
  exact (continuousAt_id.sub continuousAt_const).div
    (continuousAt_id.add continuousAt_const) (by linarith)

private theorem operatorMonotoneOnPositive_continuousAt
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnPositive.{u} h)
    {x : ℝ} (hx : 0 < x) : ContinuousAt h x := by
  have hpick : LoewnerPosOnUnitInterval (positiveCayleyPullback h) :=
    loewnerPosOnUnitInterval_of_operatorMonotone
      (operatorMonotoneOnUnitInterval_toZero hh.to_unitInterval)
  have hpull :
      ContinuousOn (positiveCayleyPullback h) (Set.Ioo (-1 : ℝ) 1) :=
    (publicFiniteOrderRegularity_of_loewnerPosOnUnitInterval 1 hpick).continuousOn
  have hy : positiveToUnitCayley x ∈ Set.Ioo (-1 : ℝ) 1 :=
    positiveToUnitCayley_mem_Ioo hx
  have hcomp : ContinuousAt
      (fun z : ℝ => positiveCayleyPullback h (positiveToUnitCayley z)) x :=
    (hpull.continuousAt (isOpen_Ioo.mem_nhds hy)).comp
      (continuousAt_positiveToUnitCayley_of_pos hx)
  have heq :
      (fun z : ℝ => positiveCayleyPullback h (positiveToUnitCayley z)) =ᶠ[𝓝 x] h := by
    filter_upwards [Ioi_mem_nhds hx] with z hz
    simp [positiveCayleyPullback,
      unitToPositiveCayley_positiveToUnitCayley hz]
  exact hcomp.congr heq

private theorem localInteriorSlope_base_value_eq
    {f : ℝ → ℝ}
    {r₁ r₂ : ℝ} (hr₁1 : r₁ < 1) (hr₂1 : r₂ < 1)
    (d₁ : LocalInteriorSlopeData.{u} f r₁)
    (d₂ : LocalInteriorSlopeData.{v} f r₂) :
    d₁.k (1 - r₁) = d₂.k (1 - r₂) := by
  have hs₁ : 0 < 1 - r₁ := by linarith
  have hs₂ : 0 < 1 - r₂ := by linarith
  have hc₁ : ContinuousAt (fun x : ℝ => d₁.k (x - r₁)) 1 := by
    have hinner : ContinuousAt (fun x : ℝ => x - r₁) 1 :=
      continuousAt_id.sub continuousAt_const
    simpa [Function.comp_def] using
      (operatorMonotoneOnPositive_continuousAt d₁.monotone hs₁).comp_of_eq
        hinner (by ring)
  have hc₂ : ContinuousAt (fun x : ℝ => d₂.k (x - r₂)) 1 := by
    have hinner : ContinuousAt (fun x : ℝ => x - r₂) 1 :=
      continuousAt_id.sub continuousAt_const
    simpa [Function.comp_def] using
      (operatorMonotoneOnPositive_continuousAt d₂.monotone hs₂).comp_of_eq
        hinner (by ring)
  have heq :
      (fun x : ℝ => d₁.k (x - r₁)) =ᶠ[𝓝[≠] (1 : ℝ)]
        (fun x : ℝ => d₂.k (x - r₂)) := by
    have hx₁ : ∀ᶠ x : ℝ in 𝓝[≠] (1 : ℝ), r₁ < x :=
      Filter.Eventually.filter_mono inf_le_left (Ioi_mem_nhds hr₁1)
    have hx₂ : ∀ᶠ x : ℝ in 𝓝[≠] (1 : ℝ), r₂ < x :=
      Filter.Eventually.filter_mono inf_le_left (Ioi_mem_nhds hr₂1)
    filter_upwards [hx₁, hx₂, self_mem_nhdsWithin] with x hxr₁ hxr₂ hxne
    have hx1 : x ≠ 1 := by simpa using hxne
    rw [d₁.formula (by linarith) (by
        intro heq
        apply hx1
        linarith),
      d₂.formula (by linarith) (by
        intro heq
        apply hx1
        linarith)]
    congr 1 <;> ring_nf
  have ht₁ : Tendsto (fun x : ℝ => d₁.k (x - r₁)) (𝓝[≠] (1 : ℝ))
      (𝓝 (d₁.k (1 - r₁))) := by
    simpa using hc₁.tendsto.mono_left inf_le_left
  have ht₂ : Tendsto (fun x : ℝ => d₂.k (x - r₂)) (𝓝[≠] (1 : ℝ))
      (𝓝 (d₂.k (1 - r₂))) := by
    simpa using hc₂.tendsto.mono_left inf_le_left
  exact tendsto_nhds_unique (ht₁.congr' heq) ht₂

private def positiveRaySlopeFromCanonical
    (f : ℝ → ℝ) {r₀ : ℝ} (d₀ : LocalInteriorSlopeData.{u} f r₀) : ℝ → ℝ :=
  fun x => if x = 1 then d₀.k (1 - r₀) else (f x - f 1) / (x - 1)

private theorem positiveRaySlopeFromCanonical_formula
    {f : ℝ → ℝ} {r₀ : ℝ} (d₀ : LocalInteriorSlopeData.{u} f r₀)
    {x : ℝ} :
    f x = f 1 + (x - 1) * positiveRaySlopeFromCanonical f d₀ x := by
  by_cases hx : x = 1
  · subst x
    simp [positiveRaySlopeFromCanonical]
  · simp only [positiveRaySlopeFromCanonical, if_neg hx]
    field_simp [sub_ne_zero.mpr hx]
    ring

private theorem positiveRaySlopeFromCanonical_eq_local
    {f : ℝ → ℝ} {r₀ r : ℝ}
    (hr₀1 : r₀ < 1) (hr1 : r < 1)
    (d₀ : LocalInteriorSlopeData.{u} f r₀)
    (d : LocalInteriorSlopeData.{v} f r)
    {x : ℝ} (hrx : r < x) :
    positiveRaySlopeFromCanonical f d₀ x = d.k (x - r) := by
  by_cases hx : x = 1
  · subst x
    simp only [positiveRaySlopeFromCanonical, if_pos]
    exact localInteriorSlope_base_value_eq hr₀1 hr1 d₀ d
  · rw [d.formula (by linarith) (by
        intro heq
        apply hx
        linarith)]
    simp only [positiveRaySlopeFromCanonical, if_neg hx]
    congr 1 <;> ring_nf

private theorem spectrum_cfc_unitToPositiveCayley_subset_Ioi
    {A : Type*} [NonUnitalCStarAlgebra A]
    {a : A} (ha_sa : IsSelfAdjoint a)
    (ha : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1) :
    spectrum ℝ (cfc unitToPositiveCayley (a : Unitization ℂ A)) ⊆
      Set.Ioi (0 : ℝ) := by
  have ha_inr : IsSelfAdjoint (a : Unitization ℂ A) :=
    (Unitization.isSelfAdjoint_inr (R := ℂ)).mpr ha_sa
  have hs : spectrum ℝ (a : Unitization ℂ A) ⊆ Set.Ioo (-1 : ℝ) 1 :=
    spectrum_unitization_inr_subset_of_quasispectrum_subset ha
  have hcont : ContinuousOn unitToPositiveCayley
      (spectrum ℝ (a : Unitization ℂ A)) :=
    continuousOn_unitToPositiveCayley_of_subset_Ioo hs
  rw [cfc_map_spectrum unitToPositiveCayley (a : Unitization ℂ A)
    ha_inr hcont]
  rintro y ⟨x, hx, rfl⟩
  exact unitToPositiveCayley_mem_Ioi (hs hx)

private theorem operatorMonotoneOnPositive_positiveRaySlopeFromCanonical
    {f : ℝ → ℝ} (hf : OperatorConvexOnPositive f)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀1 : r₀ < 1)
    (d₀ : LocalInteriorSlopeData.{u} f r₀) :
    OperatorMonotoneOnPositive.{u} (positiveRaySlopeFromCanonical f d₀) := by
  let h : ℝ → ℝ := positiveRaySlopeFromCanonical f d₀
  refine operatorMonotoneOnPositive_of_unitIntervalFiniteMatrixMonotone
    (unitIntervalMatrixMonotone_of_finiteMatrixMonotone ?_)
  refine ⟨?_⟩
  intro A _ _ _ _ a ha b hb hab
  let ua : Unitization ℂ A := (a : Unitization ℂ A)
  let ub : Unitization ℂ A := (b : Unitization ℂ A)
  let pa : Unitization ℂ A := cfc unitToPositiveCayley ua
  let pb : Unitization ℂ A := cfc unitToPositiveCayley ub
  haveI : StarOrderedRing (Unitization ℂ A) := Unitization.instStarOrderedRing
  haveI : NonnegSpectrumClass ℝ (Unitization ℂ A) :=
    @CStarAlgebra.instNonnegSpectrumClass (Unitization ℂ A) inferInstance
      Unitization.instPartialOrder Unitization.instStarOrderedRing
  have hpa_sa : IsSelfAdjoint pa := by
    dsimp [pa, ua]
    exact cfc_predicate unitToPositiveCayley (a : Unitization ℂ A)
  have hpb_sa : IsSelfAdjoint pb := by
    dsimp [pb, ub]
    exact cfc_predicate unitToPositiveCayley (b : Unitization ℂ A)
  have hpa_spec : spectrum ℝ pa ⊆ Set.Ioi (0 : ℝ) := by
    simpa [pa, ua] using spectrum_cfc_unitToPositiveCayley_subset_Ioi ha.1 ha.2
  have hpb_spec : spectrum ℝ pb ⊆ Set.Ioi (0 : ℝ) := by
    simpa [pb, ub] using spectrum_cfc_unitToPositiveCayley_subset_Ioi hb.1 hb.2
  have hp_le : pa ≤ pb := by
    simpa [pa, pb, ua, ub] using
      cfc_unitToPositiveCayley_mono_of_interval
        (A := A) ha.1 hb.1 ha.2 hb.2 hab
  have hpa_ne : (spectrum ℝ pa).Nonempty :=
    ContinuousFunctionalCalculus.spectrum_nonempty pa hpa_sa
  have hpb_ne : (spectrum ℝ pb).Nonempty :=
    ContinuousFunctionalCalculus.spectrum_nonempty pb hpb_sa
  have hpa_bdd : BddBelow (spectrum ℝ pa) := (spectrum.isCompact pa).bddBelow
  have hpb_bdd : BddBelow (spectrum ℝ pb) := (spectrum.isCompact pb).bddBelow
  let ma : ℝ := sInf (spectrum ℝ pa)
  let mb : ℝ := sInf (spectrum ℝ pb)
  have hma_mem : ma ∈ spectrum ℝ pa := by
    exact (spectrum.isCompact pa).isClosed.csInf_mem hpa_ne hpa_bdd
  have hmb_mem : mb ∈ spectrum ℝ pb := by
    exact (spectrum.isCompact pb).isClosed.csInf_mem hpb_ne hpb_bdd
  have hma : 0 < ma := hpa_spec hma_mem
  have hmb : 0 < mb := hpb_spec hmb_mem
  have hma_le : ∀ x ∈ spectrum ℝ pa, ma ≤ x := by
    intro x hx
    exact csInf_le hpa_bdd hx
  have hmb_le : ∀ x ∈ spectrum ℝ pb, mb ≤ x := by
    intro x hx
    exact csInf_le hpb_bdd hx
  let r : ℝ := min (min ma mb) 1 / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    dsimp [r]
    have := min_le_right (min ma mb) 1
    linarith
  have h2r_ma : 2 * r ≤ ma := by
    dsimp [r]
    have := min_le_left ma mb
    have := min_le_left (min ma mb) 1
    linarith
  have h2r_mb : 2 * r ≤ mb := by
    dsimp [r]
    have := min_le_right ma mb
    have := min_le_left (min ma mb) 1
    linarith
  let ya : Unitization ℂ A := pa - algebraMap ℝ (Unitization ℂ A) r
  let yb : Unitization ℂ A := pb - algebraMap ℝ (Unitization ℂ A) r
  have hya_sa : IsSelfAdjoint ya := hpa_sa.sub
    (IsSelfAdjoint.algebraMap (A := Unitization ℂ A) (r := r)
      (hr := IsSelfAdjoint.all r))
  have hyb_sa : IsSelfAdjoint yb := hpb_sa.sub
    (IsSelfAdjoint.algebraMap (A := Unitization ℂ A) (r := r)
      (hr := IsSelfAdjoint.all r))
  let shift : ℝ → ℝ := fun x => x - r
  have hcfcShiftA : cfc shift pa = ya := by
    dsimp [shift, ya]
    rw [cfc_sub (fun x : ℝ => x) (fun _x : ℝ => r) pa,
      cfc_const r pa hpa_sa]
    have hid := cfc_id ℝ pa hpa_sa
    simpa only [id_eq] using congrArg
      (fun z : Unitization ℂ A => z - algebraMap ℝ (Unitization ℂ A) r) hid
  have hcfcShiftB : cfc shift pb = yb := by
    dsimp [shift, yb]
    rw [cfc_sub (fun x : ℝ => x) (fun _x : ℝ => r) pb,
      cfc_const r pb hpb_sa]
    have hid := cfc_id ℝ pb hpb_sa
    simpa only [id_eq] using congrArg
      (fun z : Unitization ℂ A => z - algebraMap ℝ (Unitization ℂ A) r) hid
  have hspecYa : spectrum ℝ ya = shift '' spectrum ℝ pa := by
    rw [← hcfcShiftA]
    exact cfc_map_spectrum shift pa hpa_sa
      (continuous_id.sub continuous_const).continuousOn
  have hspecYb : spectrum ℝ yb = shift '' spectrum ℝ pb := by
    rw [← hcfcShiftB]
    exact cfc_map_spectrum shift pb hpb_sa
      (continuous_id.sub continuous_const).continuousOn
  have hya : IsStrictlyPositive ya := by
    apply (@CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos
      (Unitization ℂ A) Unitization.instPartialOrder _ _ _
      Unitization.instStarOrderedRing _ _ _ _ _ (a := ya)).2
    refine ⟨hya_sa, ?_⟩
    intro x hx
    rw [hspecYa] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    dsimp [shift]
    have hz_lower := hma_le z hz
    linarith
  have hyb : IsStrictlyPositive yb := by
    apply (@CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos
      (Unitization ℂ A) Unitization.instPartialOrder _ _ _
      Unitization.instStarOrderedRing _ _ _ _ _ (a := yb)).2
    refine ⟨hyb_sa, ?_⟩
    intro x hx
    rw [hspecYb] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    dsimp [shift]
    have hz_lower := hmb_le z hz
    linarith
  have hy_le : ya ≤ yb := sub_le_sub_right hp_le _
  let d : LocalInteriorSlopeData.{0} f r := localInteriorSlopeData (@hf) hr hr1
  have hkmono :
      cfc (fun y : ℝ => d.k y - d.k 0) ya ≤
        cfc (fun y : ℝ => d.k y - d.k 0) yb :=
    @positiveCayley_cfc_transport_of_strictPositive d.k (Unitization ℂ A)
      d.monotone inferInstance Unitization.instPartialOrder
      Unitization.instStarOrderedRing _ _ hya hyb hy_le
  have hfin_pa : (spectrum ℝ pa).Finite :=
    spectrum_real_finite_of_finiteDimensional_complex pa
  have hfin_pb : (spectrum ℝ pb).Finite :=
    spectrum_real_finite_of_finiteDimensional_complex pb
  have hfin_ya : (spectrum ℝ ya).Finite :=
    spectrum_real_finite_of_finiteDimensional_complex ya
  have hfin_yb : (spectrum ℝ yb).Finite :=
    spectrum_real_finite_of_finiteDimensional_complex yb
  have hlocalA : ∀ x ∈ spectrum ℝ pa, h x = d.k (x - r) := by
    intro x hx
    exact positiveRaySlopeFromCanonical_eq_local hr₀1 hr1 d₀ d (by
      have hx_lower := hma_le x hx
      linarith)
  have hlocalB : ∀ x ∈ spectrum ℝ pb, h x = d.k (x - r) := by
    intro x hx
    exact positiveRaySlopeFromCanonical_eq_local hr₀1 hr1 d₀ d (by
      have hx_lower := hmb_le x hx
      linarith)
  have htranslateA :
      cfc (fun x : ℝ => h x - h 0) pa =
        cfc (fun y : ℝ => d.k y - d.k 0) ya +
          algebraMap ℝ (Unitization ℂ A) (d.k 0 - h 0) := by
    calc
      cfc (fun x : ℝ => h x - h 0) pa =
          cfc (fun x : ℝ => d.k (shift x) - h 0) pa := by
        apply cfc_congr
        intro x hx
        change h x - h 0 = d.k (shift x) - h 0
        rw [hlocalA x hx]
      _ = cfc (fun y : ℝ => d.k y - h 0) ya := by
        rw [← hcfcShiftA]
        exact cfc_comp' (g := fun y : ℝ => d.k y - h 0) (f := shift) (a := pa)
          (hg := (hfin_pa.image shift).continuousOn _)
          (hf := hfin_pa.continuousOn _)
      _ = cfc (fun y : ℝ => (d.k y - d.k 0) + (d.k 0 - h 0)) ya := by
        apply cfc_congr
        intro y _hy
        ring
      _ = cfc (fun y : ℝ => d.k y - d.k 0) ya +
          algebraMap ℝ (Unitization ℂ A) (d.k 0 - h 0) := by
        exact cfc_add_const (r := d.k 0 - h 0)
          (f := fun y : ℝ => d.k y - d.k 0) (a := ya)
          (hf := hfin_ya.continuousOn _)
  have htranslateB :
      cfc (fun x : ℝ => h x - h 0) pb =
        cfc (fun y : ℝ => d.k y - d.k 0) yb +
          algebraMap ℝ (Unitization ℂ A) (d.k 0 - h 0) := by
    calc
      cfc (fun x : ℝ => h x - h 0) pb =
          cfc (fun x : ℝ => d.k (shift x) - h 0) pb := by
        apply cfc_congr
        intro x hx
        change h x - h 0 = d.k (shift x) - h 0
        rw [hlocalB x hx]
      _ = cfc (fun y : ℝ => d.k y - h 0) yb := by
        rw [← hcfcShiftB]
        exact cfc_comp' (g := fun y : ℝ => d.k y - h 0) (f := shift) (a := pb)
          (hg := (hfin_pb.image shift).continuousOn _)
          (hf := hfin_pb.continuousOn _)
      _ = cfc (fun y : ℝ => (d.k y - d.k 0) + (d.k 0 - h 0)) yb := by
        apply cfc_congr
        intro y _hy
        ring
      _ = cfc (fun y : ℝ => d.k y - d.k 0) yb +
          algebraMap ℝ (Unitization ℂ A) (d.k 0 - h 0) := by
        exact cfc_add_const (r := d.k 0 - h 0)
          (f := fun y : ℝ => d.k y - d.k 0) (a := yb)
          (hf := hfin_yb.continuousOn _)
  have hmono :
      cfc (fun x : ℝ => h x - h 0) pa ≤
        cfc (fun x : ℝ => h x - h 0) pb := by
    rw [htranslateA, htranslateB]
    exact add_le_add hkmono (le_refl _)
  have htarget_unit :
      cfc (fun y : ℝ => positiveCayleyPullback h y - positiveCayleyPullback h 0) ua ≤
        cfc (fun y : ℝ => positiveCayleyPullback h y - positiveCayleyPullback h 0) ub := by
    have heqa := cfc_pullback_eq_cfc_halfline_add_const
      (h := h) (A := A) (a := a) ha.1 ha.2
    have heqb := cfc_pullback_eq_cfc_halfline_add_const
      (h := h) (A := A) (a := b) hb.1 hb.2
    have hwith_const :
        cfc (fun y : ℝ => positiveCayleyPullback h y - positiveCayleyPullback h 0) ua +
            algebraMap ℝ (Unitization ℂ A) (h 1 - h 0) ≤
          cfc (fun y : ℝ => positiveCayleyPullback h y - positiveCayleyPullback h 0) ub +
            algebraMap ℝ (Unitization ℂ A) (h 1 - h 0) := by
      rw [heqa, heqb]
      simpa [pa, pb, ua, ub] using hmono
    exact (add_le_add_iff_right
      (algebraMap ℝ (Unitization ℂ A) (h 1 - h 0))).1 hwith_const
  rw [← Unitization.inr_le_iff
    (cfcₙ (fun y : ℝ => positiveCayleyPullback h y - positiveCayleyPullback h 0) a)
    (cfcₙ (fun y : ℝ => positiveCayleyPullback h y - positiveCayleyPullback h 0) b)
    (cfcₙ_predicate _ a) (cfcₙ_predicate _ b)]
  rw [Unitization.real_cfcₙ_eq_cfc_inr a
      (fun y : ℝ => positiveCayleyPullback h y - positiveCayleyPullback h 0) (by simp),
    Unitization.real_cfcₙ_eq_cfc_inr b
      (fun y : ℝ => positiveCayleyPullback h y - positiveCayleyPullback h 0) (by simp)]
  exact htarget_unit

/-! ### Integrating the normalized quadratic kernels -/

private def positiveRayOperatorConvexNormalizedBasicKernel (t x : ℝ) : ℝ :=
  (1 + t) * positiveRayOperatorConvexKernel x t

private def positiveRayOperatorConvexBasicFiniteMeasure
    {f : ℝ → ℝ} (rep : PositiveRayOperatorConvexRepBasic f) : Measure ℝ :=
  rep.μ.withDensity halfLineWeight

private theorem positiveRayOperatorConvexBasicFiniteMeasure_isFinite
    {f : ℝ → ℝ} (rep : PositiveRayOperatorConvexRepBasic f) :
    IsFiniteMeasure (positiveRayOperatorConvexBasicFiniteMeasure rep) := by
  exact isFiniteMeasure_withDensity rep.weight_lintegral_lt_top.ne

private theorem positiveRayOperatorConvexBasicFiniteMeasure_ae_mem_Ici
    {f : ℝ → ℝ} (rep : PositiveRayOperatorConvexRepBasic f) :
    ∀ᵐ t ∂positiveRayOperatorConvexBasicFiniteMeasure rep,
      t ∈ Set.Ici (0 : ℝ) := by
  have hac : positiveRayOperatorConvexBasicFiniteMeasure rep ≪ rep.μ :=
    withDensity_absolutelyContinuous _ _
  exact hac.ae_le ((mem_ae_iff).mpr rep.support)

private theorem positiveRayOperatorConvexNormalizedBasicKernel_density_eq
    {x t : ℝ} (ht : 0 ≤ t) :
    (halfLineWeight t).toReal •
        positiveRayOperatorConvexNormalizedBasicKernel t x =
      positiveRayOperatorConvexKernel x t := by
  have h1t : 0 < 1 + t := by linarith
  rw [halfLineWeight, ENNReal.toReal_ofReal (inv_nonneg.mpr h1t.le)]
  simp only [smul_eq_mul, positiveRayOperatorConvexNormalizedBasicKernel]
  field_simp [h1t.ne']

private theorem positiveRayOperatorConvexNormalizedBasicKernel_integral_eq
    {f : ℝ → ℝ} (rep : PositiveRayOperatorConvexRepBasic f)
    {x : ℝ} :
    (∫ t : ℝ, positiveRayOperatorConvexNormalizedBasicKernel t x
        ∂positiveRayOperatorConvexBasicFiniteMeasure rep) =
      ∫ t : ℝ, positiveRayOperatorConvexKernel x t ∂rep.μ := by
  have hwd :
      (∫ t : ℝ, positiveRayOperatorConvexNormalizedBasicKernel t x
          ∂positiveRayOperatorConvexBasicFiniteMeasure rep) =
        ∫ t : ℝ, (halfLineWeight t).toReal •
          positiveRayOperatorConvexNormalizedBasicKernel t x ∂rep.μ := by
    simpa [positiveRayOperatorConvexBasicFiniteMeasure] using
      (integral_withDensity_eq_integral_toReal_smul
        (μ := rep.μ) measurable_halfLineWeight
        (ae_of_all rep.μ fun t => by simp [halfLineWeight])
        (fun t : ℝ => positiveRayOperatorConvexNormalizedBasicKernel t x))
  rw [hwd]
  apply integral_congr_ae
  filter_upwards [(mem_ae_iff).mpr rep.support] with t ht
  exact positiveRayOperatorConvexNormalizedBasicKernel_density_eq ht

private theorem positiveRayOperatorConvexNormalizedBasicKernel_denominator_pos
    {t x : ℝ} (ht : t ∈ Set.Ici (0 : ℝ)) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    0 < x + t := by
  exact add_pos_of_pos_of_nonneg hx ht

private theorem positiveRayOperatorConvexNormalizedBasicKernel_joint_continuousOn
    {A : Type*} [CStarAlgebra A] {a : A}
    (hspec : spectrum ℝ a ⊆ Set.Ioi (0 : ℝ)) :
    ContinuousOn
      (Function.uncurry positiveRayOperatorConvexNormalizedBasicKernel)
      (Set.Ici (0 : ℝ) ×ˢ spectrum ℝ a) := by
  intro p hp
  rcases hp with ⟨ht, hx⟩
  have hden : p.2 + p.1 ≠ 0 :=
    (positiveRayOperatorConvexNormalizedBasicKernel_denominator_pos ht (hspec hx)).ne'
  unfold positiveRayOperatorConvexNormalizedBasicKernel
    positiveRayOperatorConvexKernel
  change ContinuousWithinAt
    (fun p : ℝ × ℝ => (1 + p.1) * ((p.2 - 1) ^ 2 / (p.2 + p.1)))
    (Set.Ici (0 : ℝ) ×ˢ spectrum ℝ a) p
  exact
    ((continuous_const.add continuous_fst).continuousAt.mul
      (((continuous_snd.sub continuous_const).pow 2).continuousAt.div
        (continuous_snd.add continuous_fst).continuousAt hden)).continuousWithinAt

private def positiveRayOperatorConvexNormalizedBasicKernelBound (x : ℝ) : ℝ :=
  ‖x - 1‖ ^ 2 * max x⁻¹ 1

private theorem positiveRayOperatorConvexNormalizedBasicKernel_norm_le
    {t x : ℝ} (ht : 0 ≤ t) (hx : 0 < x) :
    ‖positiveRayOperatorConvexNormalizedBasicKernel t x‖ ≤
      positiveRayOperatorConvexNormalizedBasicKernelBound x := by
  have hxt : 0 < x + t := by linarith
  have h1t : 0 < 1 + t := by linarith
  have hratio :
      (1 + t) / (x + t) ≤ max x⁻¹ 1 := by
    by_cases hx1 : x ≤ 1
    · have hmul : x * (1 + t) ≤ x + t := by nlinarith
      have hmax : max x⁻¹ (1 : ℝ) = x⁻¹ := by
        rw [max_eq_left]
        exact (one_le_inv₀ hx).2 hx1
      rw [hmax, div_le_iff₀ hxt]
      have hxinv : x⁻¹ * (x + t) = (x + t) / x := by field_simp
      rw [hxinv, le_div_iff₀ hx]
      nlinarith
    · have hx1' : 1 ≤ x := le_of_not_ge hx1
      have hmax : max x⁻¹ (1 : ℝ) = 1 := by
        rw [max_eq_right]
        exact inv_le_one_of_one_le₀ hx1'
      rw [hmax, div_le_one hxt]
      linarith
  have hkernel_nonneg :
      0 ≤ positiveRayOperatorConvexNormalizedBasicKernel t x := by
    unfold positiveRayOperatorConvexNormalizedBasicKernel
      positiveRayOperatorConvexKernel
    positivity
  rw [Real.norm_of_nonneg hkernel_nonneg]
  unfold positiveRayOperatorConvexNormalizedBasicKernel
    positiveRayOperatorConvexKernel
    positiveRayOperatorConvexNormalizedBasicKernelBound
  simp only [Real.norm_eq_abs, sq_abs]
  have hsq : 0 ≤ (x - 1) ^ 2 := sq_nonneg _
  calc
    (1 + t) * ((x - 1) ^ 2 / (x + t)) =
        (x - 1) ^ 2 * ((1 + t) / (x + t)) := by ring
    _ ≤ (x - 1) ^ 2 * max x⁻¹ 1 :=
      mul_le_mul_of_nonneg_left hratio hsq

private theorem positiveRayOperatorConvexNormalizedBasicKernel_exists_bound
    {A : Type*} [CStarAlgebra A] {a : A}
    (hspec : spectrum ℝ a ⊆ Set.Ioi (0 : ℝ)) :
    ∃ C : ℝ, ∀ t ∈ Set.Ici (0 : ℝ), ∀ x ∈ spectrum ℝ a,
      ‖positiveRayOperatorConvexNormalizedBasicKernel t x‖ ≤ C := by
  have hcont : ContinuousOn positiveRayOperatorConvexNormalizedBasicKernelBound
      (spectrum ℝ a) := by
    intro x hx
    have hx0 : x ≠ 0 := (hspec hx).ne'
    exact
      (((continuousAt_id.sub continuousAt_const).norm.pow 2).mul
        ((continuousAt_inv₀ hx0).max continuousAt_const)).continuousWithinAt
  obtain ⟨C, hC⟩ :=
    (spectrum.isCompact a).exists_bound_of_continuousOn hcont
  refine ⟨C, ?_⟩
  intro t ht x hx
  have hbound := hC x hx
  have hcoeff_nonneg :
      0 ≤ positiveRayOperatorConvexNormalizedBasicKernelBound x := by
    unfold positiveRayOperatorConvexNormalizedBasicKernelBound
    positivity
  rw [Real.norm_of_nonneg hcoeff_nonneg] at hbound
  exact (positiveRayOperatorConvexNormalizedBasicKernel_norm_le ht (hspec hx)).trans hbound

private theorem cfc_positiveRayOperatorConvexNormalizedBasicKernel
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [Nontrivial A]
    {X : A} (hX : IsSelfAdjoint X)
    (hspec : spectrum ℝ X ⊆ Set.Ioi (0 : ℝ))
    {t : ℝ} (ht : 0 ≤ t) :
    cfc (positiveRayOperatorConvexNormalizedBasicKernel t) X =
      (1 + t) •
        (X - algebraMap ℝ A (2 + t) +
          (1 + t) ^ 2 • cfc (fun x : ℝ => 1 / (x + t)) X) := by
  let recip : ℝ → ℝ := fun x => 1 / (x + t)
  have hrecip : ContinuousOn recip (spectrum ℝ X) := by
    intro x hx
    have hden : x + t ≠ 0 := by
      have hx0 : 0 < x := hspec hx
      linarith
    exact (continuousAt_const.div (continuousAt_id.add continuousAt_const) hden).continuousWithinAt
  have haff : ContinuousOn (fun x : ℝ => x - (2 + t)) (spectrum ℝ X) :=
    (continuous_id.sub continuous_const).continuousOn
  have hscaled : ContinuousOn (fun x : ℝ => (1 + t) ^ 2 * recip x)
      (spectrum ℝ X) := continuousOn_const.mul hrecip
  have hsum : ContinuousOn
      (fun x : ℝ => (x - (2 + t)) + (1 + t) ^ 2 * recip x)
      (spectrum ℝ X) := haff.add hscaled
  calc
    cfc (positiveRayOperatorConvexNormalizedBasicKernel t) X =
        cfc (fun x : ℝ =>
          (1 + t) * ((x - (2 + t)) + (1 + t) ^ 2 * recip x)) X := by
      apply cfc_congr
      intro x hx
      have hden : x + t ≠ 0 := by
        have hx0 : 0 < x := hspec hx
        linarith
      unfold positiveRayOperatorConvexNormalizedBasicKernel
        positiveRayOperatorConvexKernel
      dsimp [recip]
      field_simp [hden]
      ring
    _ = (1 + t) • cfc
        (fun x : ℝ => (x - (2 + t)) + (1 + t) ^ 2 * recip x) X := by
      exact cfc_const_mul (1 + t) _ X hsum
    _ = (1 + t) •
        (cfc (fun x : ℝ => x - (2 + t)) X +
          cfc (fun x : ℝ => (1 + t) ^ 2 * recip x) X) := by
      congr 1
      exact cfc_add X _ _ haff hscaled
    _ = (1 + t) •
        (X - algebraMap ℝ A (2 + t) +
          (1 + t) ^ 2 • cfc recip X) := by
      rw [cfc_sub (fun x : ℝ => x) (fun _x : ℝ => 2 + t) X,
        cfc_const (2 + t) X hX,
        cfc_const_mul ((1 + t) ^ 2) recip X hrecip]
      have hid := cfc_id ℝ X hX
      simpa only [id_eq] using congrArg
        (fun z : A => (1 + t) •
          (z - algebraMap ℝ A (2 + t) + (1 + t) ^ 2 • cfc recip X)) hid

private theorem positiveRayOperatorConvexNormalizedBasicKernel_operatorConvexOnPositive
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [Nontrivial A]
    {t : ℝ} (ht : 0 ≤ t) :
    LownerHeinzCore.OperatorConvexOn (𝓐 := A) (Set.Ioi (0 : ℝ))
      (positiveRayOperatorConvexNormalizedBasicKernel t) := by
  intro X Y θ hX hY hθ0 hθ1 hspecX hspecY
  let C : A := (1 - θ) • X + θ • Y
  have hC : IsSelfAdjoint C := by
    simpa [C] using LownerHeinzCore.isSelfAdjoint_convexCombo θ hX hY
  have hspecC : spectrum ℝ C ⊆ Set.Ioi (0 : ℝ) := by
    simpa [C] using LownerHeinzCore.spectrum_convexCombo_Ioi
      (A := X) (B := Y) (t := θ) hX hY hθ0 hθ1 hspecX hspecY
  let recip : ℝ → ℝ := fun x => 1 / (x + t)
  have hrecip :
      cfc recip C ≤ (1 - θ) • cfc recip X + θ • cfc recip Y := by
    by_cases ht0 : t = 0
    · subst t
      simpa [recip] using
        (LownerHeinzCore.one_div_operatorConvexOn_Ioi (𝓐 := A)
          hX hY hθ0 hθ1 hspecX hspecY)
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      exact
        (LownerHeinzCore.one_div_add_t_operatorConvexOn_Ici
          (𝓐 := A) t htpos hX hY hθ0 hθ1
          (fun x hx => by
            change 0 ≤ x
            exact (hspecX hx).le)
          (fun x hx => by
            change 0 ≤ x
            exact (hspecY hx).le))
  have hrecip_scaled :
      (1 + t) ^ 2 • cfc recip C ≤
        (1 + t) ^ 2 • ((1 - θ) • cfc recip X + θ • cfc recip Y) :=
    smul_le_smul_of_nonneg_left hrecip (sq_nonneg (1 + t))
  have hinside :
      C - algebraMap ℝ A (2 + t) + (1 + t) ^ 2 • cfc recip C ≤
        (1 - θ) •
            (X - algebraMap ℝ A (2 + t) + (1 + t) ^ 2 • cfc recip X) +
          θ • (Y - algebraMap ℝ A (2 + t) +
            (1 + t) ^ 2 • cfc recip Y) := by
    calc
      C - algebraMap ℝ A (2 + t) + (1 + t) ^ 2 • cfc recip C ≤
          C - algebraMap ℝ A (2 + t) +
            (1 + t) ^ 2 • ((1 - θ) • cfc recip X + θ • cfc recip Y) :=
        add_le_add (le_refl _) hrecip_scaled
      _ = (1 - θ) •
            (X - algebraMap ℝ A (2 + t) + (1 + t) ^ 2 • cfc recip X) +
          θ • (Y - algebraMap ℝ A (2 + t) +
            (1 + t) ^ 2 • cfc recip Y) := by
        dsimp [C]
        module
  have hscaled := smul_le_smul_of_nonneg_left hinside (by linarith : 0 ≤ 1 + t)
  change cfc (positiveRayOperatorConvexNormalizedBasicKernel t) C ≤
    (1 - θ) • cfc (positiveRayOperatorConvexNormalizedBasicKernel t) X +
      θ • cfc (positiveRayOperatorConvexNormalizedBasicKernel t) Y
  rw [cfc_positiveRayOperatorConvexNormalizedBasicKernel hC hspecC ht,
    cfc_positiveRayOperatorConvexNormalizedBasicKernel hX hspecX ht,
    cfc_positiveRayOperatorConvexNormalizedBasicKernel hY hspecY ht]
  dsimp [recip] at hscaled
  convert hscaled using 1
  all_goals module

private def positiveRayOperatorConvexNormalizedBasicIntegral
    {f : ℝ → ℝ} (rep : PositiveRayOperatorConvexRepBasic f) (x : ℝ) : ℝ :=
  ∫ t : ℝ in Set.Ici (0 : ℝ),
    positiveRayOperatorConvexNormalizedBasicKernel t x
      ∂positiveRayOperatorConvexBasicFiniteMeasure rep

private theorem positiveRayOperatorConvexNormalizedBasicKernel_cfc_integrableOn
    {f : ℝ → ℝ} (rep : PositiveRayOperatorConvexRepBasic f)
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [Nontrivial A]
    {X : A} (hX : IsSelfAdjoint X)
    (hspec : spectrum ℝ X ⊆ Set.Ioi (0 : ℝ)) :
    IntegrableOn
      (fun t : ℝ => cfc (positiveRayOperatorConvexNormalizedBasicKernel t) X)
      (Set.Ici (0 : ℝ)) (positiveRayOperatorConvexBasicFiniteMeasure rep) := by
  letI : IsFiniteMeasure (positiveRayOperatorConvexBasicFiniteMeasure rep) :=
    positiveRayOperatorConvexBasicFiniteMeasure_isFinite rep
  obtain ⟨C, hC⟩ :=
    positiveRayOperatorConvexNormalizedBasicKernel_exists_bound hspec
  refine integrableOn_cfc measurableSet_Ici
    (fun t x => positiveRayOperatorConvexNormalizedBasicKernel t x)
    (fun _t => C) X
    (positiveRayOperatorConvexNormalizedBasicKernel_joint_continuousOn hspec)
    ?_ (integrable_const C).hasFiniteIntegral hX
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht x hx
  exact hC t ht x hx

private theorem cfc_positiveRayOperatorConvexNormalizedBasicIntegral
    {f : ℝ → ℝ} (rep : PositiveRayOperatorConvexRepBasic f)
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [Nontrivial A]
    {X : A} (hX : IsSelfAdjoint X)
    (hspec : spectrum ℝ X ⊆ Set.Ioi (0 : ℝ)) :
    cfc (positiveRayOperatorConvexNormalizedBasicIntegral rep) X =
      ∫ t : ℝ in Set.Ici (0 : ℝ),
        cfc (positiveRayOperatorConvexNormalizedBasicKernel t) X
          ∂positiveRayOperatorConvexBasicFiniteMeasure rep := by
  letI : IsFiniteMeasure (positiveRayOperatorConvexBasicFiniteMeasure rep) :=
    positiveRayOperatorConvexBasicFiniteMeasure_isFinite rep
  obtain ⟨C, hC⟩ :=
    positiveRayOperatorConvexNormalizedBasicKernel_exists_bound hspec
  unfold positiveRayOperatorConvexNormalizedBasicIntegral
  exact cfc_setIntegral measurableSet_Ici
    (fun t x => positiveRayOperatorConvexNormalizedBasicKernel t x)
    (fun _t => C) X
    (positiveRayOperatorConvexNormalizedBasicKernel_joint_continuousOn hspec)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht x hx
      exact hC t ht x hx)
    (integrable_const C).hasFiniteIntegral hX

private theorem positiveRayOperatorConvexNormalizedBasicIntegral_operatorConvexOnPositive
    {f : ℝ → ℝ} (rep : PositiveRayOperatorConvexRepBasic f)
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [Nontrivial A] :
    LownerHeinzCore.OperatorConvexOn (𝓐 := A) (Set.Ioi (0 : ℝ))
      (positiveRayOperatorConvexNormalizedBasicIntegral rep) := by
  intro X Y θ hX hY hθ0 hθ1 hspecX hspecY
  let C : A := (1 - θ) • X + θ • Y
  have hC : IsSelfAdjoint C := by
    simpa [C] using LownerHeinzCore.isSelfAdjoint_convexCombo θ hX hY
  have hspecC : spectrum ℝ C ⊆ Set.Ioi (0 : ℝ) := by
    simpa [C] using LownerHeinzCore.spectrum_convexCombo_Ioi
      (A := X) (B := Y) (t := θ) hX hY hθ0 hθ1 hspecX hspecY
  letI : IsFiniteMeasure (positiveRayOperatorConvexBasicFiniteMeasure rep) :=
    positiveRayOperatorConvexBasicFiniteMeasure_isFinite rep
  change cfc (positiveRayOperatorConvexNormalizedBasicIntegral rep) C ≤
    (1 - θ) • cfc (positiveRayOperatorConvexNormalizedBasicIntegral rep) X +
      θ • cfc (positiveRayOperatorConvexNormalizedBasicIntegral rep) Y
  rw [cfc_positiveRayOperatorConvexNormalizedBasicIntegral rep hC hspecC,
    cfc_positiveRayOperatorConvexNormalizedBasicIntegral rep hX hspecX,
    cfc_positiveRayOperatorConvexNormalizedBasicIntegral rep hY hspecY]
  have hIX :=
    positiveRayOperatorConvexNormalizedBasicKernel_cfc_integrableOn rep hX hspecX
  have hIY :=
    positiveRayOperatorConvexNormalizedBasicKernel_cfc_integrableOn rep hY hspecY
  change Integrable _
    ((positiveRayOperatorConvexBasicFiniteMeasure rep).restrict (Set.Ici (0 : ℝ))) at hIX hIY
  have hIXs := Integrable.smul (1 - θ) hIX
  have hIYs := Integrable.smul θ hIY
  have hmono :
      (∫ t : ℝ in Set.Ici (0 : ℝ),
          cfc (positiveRayOperatorConvexNormalizedBasicKernel t) C
            ∂positiveRayOperatorConvexBasicFiniteMeasure rep) ≤
        ∫ t : ℝ in Set.Ici (0 : ℝ),
          ((1 - θ) • cfc (positiveRayOperatorConvexNormalizedBasicKernel t) X +
            θ • cfc (positiveRayOperatorConvexNormalizedBasicKernel t) Y)
            ∂positiveRayOperatorConvexBasicFiniteMeasure rep := by
    refine setIntegral_mono_on_ae
      (positiveRayOperatorConvexNormalizedBasicKernel_cfc_integrableOn rep hC hspecC)
      (hIXs.add hIYs) measurableSet_Ici ?_
    filter_upwards with t ht
    exact positiveRayOperatorConvexNormalizedBasicKernel_operatorConvexOnPositive
      (A := A) ht hX hY hθ0 hθ1 hspecX hspecY
  calc
    (∫ t : ℝ in Set.Ici (0 : ℝ),
        cfc (positiveRayOperatorConvexNormalizedBasicKernel t) C
          ∂positiveRayOperatorConvexBasicFiniteMeasure rep) ≤
        ∫ t : ℝ in Set.Ici (0 : ℝ),
          ((1 - θ) • cfc (positiveRayOperatorConvexNormalizedBasicKernel t) X +
            θ • cfc (positiveRayOperatorConvexNormalizedBasicKernel t) Y)
            ∂positiveRayOperatorConvexBasicFiniteMeasure rep := hmono
    _ = (∫ t : ℝ in Set.Ici (0 : ℝ),
          (1 - θ) • cfc (positiveRayOperatorConvexNormalizedBasicKernel t) X
            ∂positiveRayOperatorConvexBasicFiniteMeasure rep) +
        ∫ t : ℝ in Set.Ici (0 : ℝ),
          θ • cfc (positiveRayOperatorConvexNormalizedBasicKernel t) Y
            ∂positiveRayOperatorConvexBasicFiniteMeasure rep :=
      integral_add hIXs hIYs
    _ = (1 - θ) • (∫ t : ℝ in Set.Ici (0 : ℝ),
          cfc (positiveRayOperatorConvexNormalizedBasicKernel t) X
            ∂positiveRayOperatorConvexBasicFiniteMeasure rep) +
        θ • (∫ t : ℝ in Set.Ici (0 : ℝ),
          cfc (positiveRayOperatorConvexNormalizedBasicKernel t) Y
            ∂positiveRayOperatorConvexBasicFiniteMeasure rep) := by
      rw [integral_smul, integral_smul]

private theorem operatorConvexOnPositive_of_nontrivial
    {f : ℝ → ℝ}
    (h : ∀ {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
      [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [Nontrivial A],
      LownerHeinzCore.OperatorConvexOn (𝓐 := A) (Set.Ioi (0 : ℝ)) f) :
    OperatorConvexOnPositive f := by
  intro A _ _ _ _
  by_cases hA : Nontrivial A
  · letI : Nontrivial A := hA
    exact h
  · letI : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
    intro X Y t _ _ _ _ _ _
    apply le_of_eq
    apply Subsingleton.elim

private theorem operatorConvexOnPositive_positiveRayOperatorConvexNormalizedBasicIntegral
    {f : ℝ → ℝ} (rep : PositiveRayOperatorConvexRepBasic f) :
    OperatorConvexOnPositive (positiveRayOperatorConvexNormalizedBasicIntegral rep) := by
  apply operatorConvexOnPositive_of_nontrivial
  intro A _ _ _ _ _
  exact positiveRayOperatorConvexNormalizedBasicIntegral_operatorConvexOnPositive rep

private theorem positiveRayOperatorConvexNormalizedBasicIntegral_eq
    {f : ℝ → ℝ} (rep : PositiveRayOperatorConvexRepBasic f)
    {x : ℝ} :
    positiveRayOperatorConvexNormalizedBasicIntegral rep x =
      ∫ t : ℝ, positiveRayOperatorConvexKernel x t ∂rep.μ := by
  have hrestrict :
      (positiveRayOperatorConvexBasicFiniteMeasure rep).restrict (Set.Ici (0 : ℝ)) =
        positiveRayOperatorConvexBasicFiniteMeasure rep :=
    Measure.restrict_eq_self_of_ae_mem
      (positiveRayOperatorConvexBasicFiniteMeasure_ae_mem_Ici rep)
  unfold positiveRayOperatorConvexNormalizedBasicIntegral
  change (∫ t : ℝ, positiveRayOperatorConvexNormalizedBasicKernel t x
      ∂(positiveRayOperatorConvexBasicFiniteMeasure rep).restrict (Set.Ici (0 : ℝ))) = _
  rw [hrestrict]
  exact positiveRayOperatorConvexNormalizedBasicKernel_integral_eq rep

private theorem operatorConvexOnPositive_add
    {g k : ℝ → ℝ} (hg : OperatorConvexOnPositive g)
    (hk : OperatorConvexOnPositive k) :
    OperatorConvexOnPositive (fun x => g x + k x) := by
  have hgcont := operatorConvexOnPositive_continuousOn (@hg)
  have hkcont := operatorConvexOnPositive_continuousOn (@hk)
  apply operatorConvexOnPositive_of_nontrivial
  intro A _ _ _ _ _ X Y θ hX hY hθ0 hθ1 hspecX hspecY
  let C : A := (1 - θ) • X + θ • Y
  have hC : IsSelfAdjoint C := by
    simpa [C] using LownerHeinzCore.isSelfAdjoint_convexCombo θ hX hY
  have hspecC : spectrum ℝ C ⊆ Set.Ioi (0 : ℝ) := by
    simpa [C] using LownerHeinzCore.spectrum_convexCombo_Ioi
      (A := X) (B := Y) (t := θ) hX hY hθ0 hθ1 hspecX hspecY
  have hgineq := hg hX hY hθ0 hθ1 hspecX hspecY
  have hkineq := hk hX hY hθ0 hθ1 hspecX hspecY
  have hgc := hgcont.mono hspecC
  have hkc := hkcont.mono hspecC
  have hgX := hgcont.mono hspecX
  have hkX := hkcont.mono hspecX
  have hgY := hgcont.mono hspecY
  have hkY := hkcont.mono hspecY
  change cfc (fun x => g x + k x) C ≤
    (1 - θ) • cfc (fun x => g x + k x) X +
      θ • cfc (fun x => g x + k x) Y
  rw [cfc_add C g k hgc hkc, cfc_add X g k hgX hkX,
    cfc_add Y g k hgY hkY]
  convert add_le_add hgineq hkineq using 1
  all_goals module

private theorem operatorConvexOnPositive_const_mul
    {g : ℝ → ℝ} (hg : OperatorConvexOnPositive g)
    {c : ℝ} (hc : 0 ≤ c) :
    OperatorConvexOnPositive (fun x => c * g x) := by
  have hgcont := operatorConvexOnPositive_continuousOn (@hg)
  apply operatorConvexOnPositive_of_nontrivial
  intro A _ _ _ _ _ X Y θ hX hY hθ0 hθ1 hspecX hspecY
  let C : A := (1 - θ) • X + θ • Y
  have hC : IsSelfAdjoint C := by
    simpa [C] using LownerHeinzCore.isSelfAdjoint_convexCombo θ hX hY
  have hspecC : spectrum ℝ C ⊆ Set.Ioi (0 : ℝ) := by
    simpa [C] using LownerHeinzCore.spectrum_convexCombo_Ioi
      (A := X) (B := Y) (t := θ) hX hY hθ0 hθ1 hspecX hspecY
  have hgineq := hg hX hY hθ0 hθ1 hspecX hspecY
  have hgc := hgcont.mono hspecC
  have hgX := hgcont.mono hspecX
  have hgY := hgcont.mono hspecY
  have hscaled := smul_le_smul_of_nonneg_left hgineq hc
  change cfc (fun x => c * g x) C ≤
    (1 - θ) • cfc (fun x => c * g x) X +
      θ • cfc (fun x => c * g x) Y
  rw [cfc_const_mul c g C hgc, cfc_const_mul c g X hgX,
    cfc_const_mul c g Y hgY]
  convert hscaled using 1
  all_goals module

private theorem operatorConvexOnPositive_affineAtOne (c a : ℝ) :
    OperatorConvexOnPositive (fun x => c + a * (x - 1)) := by
  apply operatorConvexOnPositive_of_nontrivial
  intro A _ _ _ _ _ X Y θ hX hY hθ0 hθ1 hspecX hspecY
  let C : A := (1 - θ) • X + θ • Y
  have hC : IsSelfAdjoint C := by
    simpa [C] using LownerHeinzCore.isSelfAdjoint_convexCombo θ hX hY
  have heval : ∀ {Z : A}, IsSelfAdjoint Z →
      cfc (fun x : ℝ => c + a * (x - 1)) Z =
        algebraMap ℝ A c + a • (Z - algebraMap ℝ A 1) := by
    intro Z hZ
    have hsub : ContinuousOn (fun x : ℝ => x - 1) (spectrum ℝ Z) :=
      (continuous_id.sub continuous_const).continuousOn
    rw [cfc_add Z (fun _x : ℝ => c) (fun x : ℝ => a * (x - 1)),
      cfc_const c Z hZ, cfc_const_mul a (fun x : ℝ => x - 1) Z hsub,
      cfc_sub (fun x : ℝ => x) (fun _x : ℝ => 1) Z,
      cfc_const 1 Z hZ]
    have hid := cfc_id ℝ Z hZ
    simpa only [id_eq] using congrArg
      (fun z : A => algebraMap ℝ A c + a • (z - algebraMap ℝ A 1)) hid
  change cfc (fun x : ℝ => c + a * (x - 1)) C ≤
    (1 - θ) • cfc (fun x : ℝ => c + a * (x - 1)) X +
      θ • cfc (fun x : ℝ => c + a * (x - 1)) Y
  rw [heval hC, heval hX, heval hY]
  apply le_of_eq
  dsimp [C]
  module

private theorem operatorConvexOnPositive_squareAtOne :
    OperatorConvexOnPositive (fun x : ℝ => (x - 1) ^ 2) := by
  apply operatorConvexOnPositive_of_nontrivial
  intro A _ _ _ _ _ X Y θ hX hY hθ0 hθ1 hspecX hspecY
  let C : A := (1 - θ) • X + θ • Y
  have hC : IsSelfAdjoint C := by
    simpa [C] using LownerHeinzCore.isSelfAdjoint_convexCombo θ hX hY
  let I : A := algebraMap ℝ A 1
  let X₁ : A := X - I
  let Y₁ : A := Y - I
  let C₁ : A := C - I
  have hC₁ : C₁ = (1 - θ) • X₁ + θ • Y₁ := by
    dsimp [C₁, X₁, Y₁, C]
    module
  have hDsa : IsSelfAdjoint (X - Y) := hX.sub hY
  have hsq : 0 ≤ (X - Y) * (X - Y) := by
    simpa [mul_assoc] using
      hDsa.conjugate_nonneg (zero_le_one : (0 : A) ≤ 1)
  have hcoef : 0 ≤ θ * (1 - θ) :=
    mul_nonneg hθ0 (sub_nonneg.mpr hθ1)
  have hdiff :
      (1 - θ) • (X₁ ^ 2) + θ • (Y₁ ^ 2) - C₁ ^ 2 =
        (θ * (1 - θ)) • ((X - Y) * (X - Y)) := by
    rw [hC₁]
    dsimp [X₁, Y₁, I]
    simp only [pow_two, add_mul, mul_add, sub_mul, mul_sub,
      smul_mul_assoc, mul_smul_comm]
    module
  have hmain : C₁ ^ 2 ≤ (1 - θ) • (X₁ ^ 2) + θ • (Y₁ ^ 2) := by
    rw [← sub_nonneg, hdiff]
    exact smul_nonneg hcoef hsq
  have heval : ∀ {Z : A}, IsSelfAdjoint Z →
      cfc (fun x : ℝ => (x - 1) ^ 2) Z =
        (Z - algebraMap ℝ A 1) ^ 2 := by
    intro Z hZ
    have hsub : ContinuousOn (fun x : ℝ => x - 1) (spectrum ℝ Z) :=
      (continuous_id.sub continuous_const).continuousOn
    rw [cfc_pow (fun x : ℝ => x - 1) 2 Z hsub,
      cfc_sub (fun x : ℝ => x) (fun _x : ℝ => 1) Z,
      cfc_const 1 Z hZ]
    have hid := cfc_id ℝ Z hZ
    simpa only [id_eq] using congrArg
      (fun z : A => (z - algebraMap ℝ A 1) ^ 2) hid
  change cfc (fun x : ℝ => (x - 1) ^ 2) C ≤
    (1 - θ) • cfc (fun x : ℝ => (x - 1) ^ 2) X +
      θ • cfc (fun x : ℝ => (x - 1) ^ 2) Y
  rw [heval hC, heval hX, heval hY]
  exact hmain

private def positiveRayOperatorConvexBasicModel
    {f : ℝ → ℝ} (rep : PositiveRayOperatorConvexRepBasic f) (x : ℝ) : ℝ :=
  f 1 + rep.a * (x - 1) + (rep.b : ℝ) * (x - 1) ^ 2 +
    positiveRayOperatorConvexNormalizedBasicIntegral rep x

private theorem operatorConvexOnPositive_positiveRayOperatorConvexBasicModel
    {f : ℝ → ℝ} (rep : PositiveRayOperatorConvexRepBasic f) :
    OperatorConvexOnPositive (positiveRayOperatorConvexBasicModel rep) := by
  have haff : OperatorConvexOnPositive (fun x => f 1 + rep.a * (x - 1)) :=
    @operatorConvexOnPositive_affineAtOne (f 1) rep.a
  have hsquare : OperatorConvexOnPositive (fun x => (rep.b : ℝ) * (x - 1) ^ 2) :=
    @operatorConvexOnPositive_const_mul (fun x : ℝ => (x - 1) ^ 2)
      (@operatorConvexOnPositive_squareAtOne) (rep.b : ℝ) rep.b.coe_nonneg
  have hint :
      OperatorConvexOnPositive (positiveRayOperatorConvexNormalizedBasicIntegral rep) :=
    @operatorConvexOnPositive_positiveRayOperatorConvexNormalizedBasicIntegral f rep
  have hpoly : OperatorConvexOnPositive
      (fun x => (f 1 + rep.a * (x - 1)) + (rep.b : ℝ) * (x - 1) ^ 2) :=
    @operatorConvexOnPositive_add _ _ (@haff) (@hsquare)
  have htotal : OperatorConvexOnPositive
      (fun x => ((f 1 + rep.a * (x - 1)) + (rep.b : ℝ) * (x - 1) ^ 2) +
        positiveRayOperatorConvexNormalizedBasicIntegral rep x) :=
    @operatorConvexOnPositive_add _ _ (@hpoly) (@hint)
  apply operatorConvexOnPositive_of_nontrivial
  intro A _ _ _ _ _ X Y θ hX hY hθ0 hθ1 hspecX hspecY
  simpa only [positiveRayOperatorConvexBasicModel] using
    htotal hX hY hθ0 hθ1 hspecX hspecY

private theorem operatorConvexOnPositive_congr_Ioi
    {f g : ℝ → ℝ}
    (hfg : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → f x = g x)
    (hg : OperatorConvexOnPositive g) :
    OperatorConvexOnPositive f := by
  apply operatorConvexOnPositive_of_nontrivial
  intro A _ _ _ _ _ X Y θ hX hY hθ0 hθ1 hspecX hspecY
  let C : A := (1 - θ) • X + θ • Y
  have hC : IsSelfAdjoint C := by
    simpa [C] using LownerHeinzCore.isSelfAdjoint_convexCombo θ hX hY
  have hspecC : spectrum ℝ C ⊆ Set.Ioi (0 : ℝ) := by
    simpa [C] using LownerHeinzCore.spectrum_convexCombo_Ioi
      (A := X) (B := Y) (t := θ) hX hY hθ0 hθ1 hspecX hspecY
  have hineq := hg hX hY hθ0 hθ1 hspecX hspecY
  have hCeq : cfc f C = cfc g C := by
    apply cfc_congr
    intro x hx
    exact hfg (hspecC hx)
  have hXeq : cfc f X = cfc g X := by
    apply cfc_congr
    intro x hx
    exact hfg (hspecX hx)
  have hYeq : cfc f Y = cfc g Y := by
    apply cfc_congr
    intro x hx
    exact hfg (hspecY hx)
  change cfc f C ≤ (1 - θ) • cfc f X + θ • cfc f Y
  rw [hCeq, hXeq, hYeq]
  exact hineq

private theorem operatorConvexOnPositive_of_positiveRayOperatorConvexRepBasic
    {f : ℝ → ℝ} (rep : PositiveRayOperatorConvexRepBasic f) :
    OperatorConvexOnPositive f := by
  apply operatorConvexOnPositive_congr_Ioi
    (g := positiveRayOperatorConvexBasicModel rep)
  · intro x hx
    rw [rep.formula hx]
    unfold positiveRayOperatorConvexBasicModel
    rw [positiveRayOperatorConvexNormalizedBasicIntegral_eq rep]
  · exact (@operatorConvexOnPositive_positiveRayOperatorConvexBasicModel f rep)

private theorem operatorConvexOnPositive_of_slope_operatorMonotone
    {f h : ℝ → ℝ} (hh : OperatorMonotoneOnPositive.{u} h)
    (hf : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
      f x = f 1 + (x - 1) * h x) :
    OperatorConvexOnPositive f := by
  obtain ⟨rep⟩ :=
    (operatorMonotoneOnPositive_iff_nonempty_halfLineIntegralRep.mp hh)
  exact @operatorConvexOnPositive_of_positiveRayOperatorConvexRepBasic f
    (positiveRayOperatorConvexRepBasic_of_halfLineIntegralRep hf rep)

private theorem exists_slope_operatorMonotone_of_operatorConvexOnPositive
    {f : ℝ → ℝ} (hf : OperatorConvexOnPositive f) :
    ∃ h : ℝ → ℝ,
      OperatorMonotoneOnPositive.{u} h ∧
      ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
        f x = f 1 + (x - 1) * h x := by
  let r₀ : ℝ := 1 / 2
  have hr₀ : 0 < r₀ := by norm_num [r₀]
  have hr₀1 : r₀ < 1 := by norm_num [r₀]
  let d₀ : LocalInteriorSlopeData.{u} f r₀ :=
    localInteriorSlopeData (@hf) hr₀ hr₀1
  let h : ℝ → ℝ := positiveRaySlopeFromCanonical f d₀
  refine ⟨h, ?_, ?_⟩
  · exact operatorMonotoneOnPositive_positiveRaySlopeFromCanonical
      (@hf) hr₀ hr₀1 d₀
  · intro x _hx
    exact positiveRaySlopeFromCanonical_formula d₀

/--
Positive-ray Bendat--Sherman slope criterion; see Hiai, Corollary 2.7.8.

The value of the divided difference at `x = 1` is filled by the common limit
of its interior-base representations.  In the reverse direction the
half-line representing measure is normalized by `(1+t)⁻¹`; the resulting
quadratic kernels are uniformly bounded on each positive spectrum, so no
additional moment assumption is needed.
-/
theorem operatorConvexOnPositive_iff_exists_slope_operatorMonotone
    {f : ℝ → ℝ} :
    OperatorConvexOnPositive f ↔
      ∃ h : ℝ → ℝ,
        OperatorMonotoneOnPositive.{u} h ∧
        ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
          f x = f 1 + (x - 1) * h x := by
  constructor
  · exact exists_slope_operatorMonotone_of_operatorConvexOnPositive
  · rintro ⟨h, hh, hf⟩
    exact (@operatorConvexOnPositive_of_slope_operatorMonotone f h hh hf)

end

end Quantum.TraceInequality.Loewner
