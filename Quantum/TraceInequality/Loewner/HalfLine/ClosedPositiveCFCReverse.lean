import Quantum.TraceInequality.Loewner.LoewnerTheorem
import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.Relevel
import Quantum.TraceInequality.Loewner.HalfLine.CayleyCFCInternal

/-!
# Reverse bridge from direct closed-positive CFC monotonicity

This file contains the first reverse step in Appendix A: direct CFC monotonicity
on the closed positive cone implies operator monotonicity on the open positive
half-line.  Endpoint right-continuity is intentionally kept separate.
-/

namespace Quantum
namespace TraceInequality
namespace Loewner

universe u

open Set Filter

open scoped Topology

noncomputable section


/--
Direct closed-positive CFC monotonicity makes the positive Cayley pullback
finite-matrix monotone on the normalized interval.
-/
theorem finiteMatrixMonotone_positiveCayleyPullback_of_closedPositiveCFC
    {h : ℝ → ℝ}
    (hh : OperatorMonotoneOnClosedPositiveCFC.{0} h) :
    UnitIntervalFiniteMatrixMonotone.{0} (positiveCayleyPullback h) := by
  refine ⟨?_⟩
  intro A _ _ _ hfd a ha b hb hab
  let ua : Unitization ℂ A := (a : Unitization ℂ A)
  let ub : Unitization ℂ A := (b : Unitization ℂ A)
  let pa : Unitization ℂ A := cfc unitToPositiveCayley ua
  let pb : Unitization ℂ A := cfc unitToPositiveCayley ub
  haveI : StarOrderedRing (Unitization ℂ A) := Unitization.instStarOrderedRing
  have hpa_nonneg : 0 ≤ pa := by
    simpa [pa, ua] using cfc_unitToPositiveCayley_nonneg_of_interval
      (A := A) (a := a) ha.1 ha.2
  have hpb_nonneg : 0 ≤ pb := by
    simpa [pb, ub] using cfc_unitToPositiveCayley_nonneg_of_interval
      (A := A) (a := b) hb.1 hb.2
  have hp_le : pa ≤ pb := by
    simpa [pa, pb, ua, ub] using
      cfc_unitToPositiveCayley_mono_of_interval
        (A := A) ha.1 hb.1 ha.2 hb.2 hab
  have hmonoₙ :
      cfcₙ (fun x : ℝ => h x - h 0) pa ≤
        cfcₙ (fun x : ℝ => h x - h 0) pb :=
    @OperatorMonotoneOnClosedPositiveCFC.cfc_monotone _ hh
      (Unitization ℂ A) _ Unitization.instPartialOrder
      Unitization.instStarOrderedRing pa hpa_nonneg pb hpb_nonneg hp_le
  have hmono :
      cfc (fun x : ℝ => h x - h 0) pa ≤
        cfc (fun x : ℝ => h x - h 0) pb := by
    have hfin_pa : (quasispectrum ℝ pa).Finite :=
      quasispectrum_finite_of_finiteDimensional_complex pa
    have hfin_pb : (quasispectrum ℝ pb).Finite :=
      quasispectrum_finite_of_finiteDimensional_complex pb
    have hmono' := hmonoₙ
    rw [cfcₙ_eq_cfc (hf := hfin_pa.continuousOn _),
      cfcₙ_eq_cfc (hf := hfin_pb.continuousOn _)] at hmono'
    exact hmono'
  have htarget_unit :
      cfc (fun y : ℝ =>
          positiveCayleyPullback h y - positiveCayleyPullback h 0) ua ≤
        cfc (fun y : ℝ =>
          positiveCayleyPullback h y - positiveCayleyPullback h 0) ub := by
    have heqa := cfc_pullback_eq_cfc_halfline_add_const
      (h := h) (A := A) (a := a) ha.1 ha.2
    have heqb := cfc_pullback_eq_cfc_halfline_add_const
      (h := h) (A := A) (a := b) hb.1 hb.2
    have hwith_const :
        cfc (fun y : ℝ =>
            positiveCayleyPullback h y - positiveCayleyPullback h 0) ua +
            algebraMap ℝ (Unitization ℂ A) (h 1 - h 0) ≤
          cfc (fun y : ℝ =>
            positiveCayleyPullback h y - positiveCayleyPullback h 0) ub +
            algebraMap ℝ (Unitization ℂ A) (h 1 - h 0) := by
      rw [heqa, heqb]
      simpa [pa, pb, ua, ub] using
        (show
          cfc (fun x : ℝ => h x - h 0) pa ≤
            cfc (fun x : ℝ => h x - h 0) pb from hmono)
    exact (add_le_add_iff_right
      (algebraMap ℝ (Unitization ℂ A) (h 1 - h 0))).1 hwith_const
  rw [← Unitization.inr_le_iff
    (cfcₙ
      (fun y : ℝ =>
        positiveCayleyPullback h y - positiveCayleyPullback h 0) a)
    (cfcₙ
      (fun y : ℝ =>
        positiveCayleyPullback h y - positiveCayleyPullback h 0) b)
    (cfcₙ_predicate
      (fun y : ℝ =>
        positiveCayleyPullback h y - positiveCayleyPullback h 0) a)
    (cfcₙ_predicate
      (fun y : ℝ =>
        positiveCayleyPullback h y - positiveCayleyPullback h 0) b)]
  rw [Unitization.real_cfcₙ_eq_cfc_inr a
    (fun y : ℝ =>
      positiveCayleyPullback h y - positiveCayleyPullback h 0) (by simp),
    Unitization.real_cfcₙ_eq_cfc_inr b
    (fun y : ℝ =>
      positiveCayleyPullback h y - positiveCayleyPullback h 0) (by simp)]
  exact htarget_unit

/--
Direct closed-positive CFC monotonicity implies operator monotonicity on the open
positive half-line.
-/
theorem operatorMonotoneOnPositive_of_closedPositiveCFC
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnClosedPositiveCFC.{0} h) :
    OperatorMonotoneOnPositive.{u} h := by
  let hfinite :
      UnitIntervalFiniteMatrixMonotone.{0} (positiveCayleyPullback h) :=
    finiteMatrixMonotone_positiveCayleyPullback_of_closedPositiveCFC hh
  let hui :
      OperatorMonotoneOnUnitInterval.{0} (positiveCayleyPullback h) :=
    operatorMonotoneOnUnitInterval_of_finiteMatrixMonotone
      (unitIntervalMatrixMonotone_of_finiteMatrixMonotone hfinite)
  exact ⟨operatorMonotoneOnUnitInterval_relevel hui⟩

/--
Finite matrix monotonicity of the Cayley pullback gives open positive-ray
operator monotonicity.
-/
theorem operatorMonotoneOnPositive_of_unitIntervalFiniteMatrixMonotone
    {h : ℝ → ℝ}
    (hfinite : UnitIntervalMatrixMonotone (positiveCayleyPullback h)) :
    OperatorMonotoneOnPositive.{u} h := by
  let hui :
      OperatorMonotoneOnUnitInterval.{0} (positiveCayleyPullback h) :=
    operatorMonotoneOnUnitInterval_of_finiteMatrixMonotone hfinite
  exact ⟨operatorMonotoneOnUnitInterval_relevel hui⟩

/--
Direct closed-positive CFC monotonicity plus right-continuity at zero gives the
closed-positive monotonicity package.
-/
theorem operatorMonotoneOnClosedPositive_of_closedPositiveCFC_of_rightContinuous
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnClosedPositiveCFC.{0} h)
    (h0 : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0))) :
    OperatorMonotoneOnClosedPositive.{u} h :=
  { to_open := operatorMonotoneOnPositive_of_closedPositiveCFC hh
    right_continuous_at_zero := h0 }

/--
Finite matrix monotonicity of the Cayley pullback plus endpoint continuity gives
closed-positive monotonicity.
-/
theorem operatorMonotoneOnClosedPositive_of_unitIntervalFiniteMatrixMonotone
    {h : ℝ → ℝ}
    (hfinite : UnitIntervalMatrixMonotone (positiveCayleyPullback h))
    (h0 : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0))) :
    OperatorMonotoneOnClosedPositive.{u} h :=
  { to_open :=
      operatorMonotoneOnPositive_of_unitIntervalFiniteMatrixMonotone
        hfinite
    right_continuous_at_zero := h0 }

/--
Finite matrix monotonicity of the Cayley pullback and endpoint continuity imply
direct closed-positive CFC monotonicity.
-/
theorem operatorMonotoneOnClosedPositiveCFC_of_unitIntervalFiniteMatrixMonotone
    {h : ℝ → ℝ}
    (hfinite : UnitIntervalMatrixMonotone (positiveCayleyPullback h))
    (h0 : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0))) :
    OperatorMonotoneOnClosedPositiveCFC.{0} h :=
  operatorMonotoneOnClosedPositiveCFC_of_endpoint
    (operatorMonotoneOnClosedPositive_of_unitIntervalFiniteMatrixMonotone
      hfinite h0)

/--
The endpoint-refined direct CFC package yields closed-positive operator
monotonicity.
-/
theorem operatorMonotoneOnClosedPositive_of_closedPositiveCFCWithEndpoint
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnClosedPositiveCFCWithEndpoint.{0} h) :
    OperatorMonotoneOnClosedPositive.{u} h :=
  operatorMonotoneOnClosedPositive_of_closedPositiveCFC_of_rightContinuous
    hh.to_cfc hh.right_continuous_at_zero

/--
Construct a positive-ray Kubo--Ando representation from direct CFC monotonicity
and right-continuity at zero.
-/
noncomputable def positiveRayKuboAndoRep_of_closedPositiveCFC_of_rightContinuous
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnClosedPositiveCFC.{0} h)
    (h0 : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0))) :
    PositiveRayKuboAndoRep h :=
  positiveRayKuboAndoRep_of_operatorMonotoneOnClosedPositive
    (operatorMonotoneOnClosedPositive_of_closedPositiveCFC_of_rightContinuous.{0}
      hh h0)

/--
Construct a positive-ray Kubo--Ando representation from the endpoint-refined
direct CFC package.
-/
noncomputable def positiveRayKuboAndoRep_of_closedPositiveCFCWithEndpoint
    {h : ℝ → ℝ} (hh : OperatorMonotoneOnClosedPositiveCFCWithEndpoint.{0} h) :
    PositiveRayKuboAndoRep h :=
  positiveRayKuboAndoRep_of_operatorMonotoneOnClosedPositive
    (operatorMonotoneOnClosedPositive_of_closedPositiveCFCWithEndpoint.{0} hh)

/--
Positive-ray Kubo--Ando representations are equivalent to the endpoint-refined
direct closed-positive CFC package.
-/
theorem nonempty_positiveRayKuboAndoRep_iff_closedPositiveCFCWithEndpoint
    {h : ℝ → ℝ} :
    Nonempty (PositiveRayKuboAndoRep h) ↔
      OperatorMonotoneOnClosedPositiveCFCWithEndpoint.{0} h := by
  constructor
  · rintro ⟨rep⟩
    have hcfc : OperatorMonotoneOnClosedPositiveCFC.{0} h :=
      operatorMonotoneOnClosedPositiveCFC_of_positiveRayKuboAndoRep rep
    have hclosed : OperatorMonotoneOnClosedPositive.{0} h :=
      operatorMonotoneOnClosedPositive_of_positiveRayKuboAndoRep rep
    exact
      { to_cfc := hcfc
        right_continuous_at_zero := hclosed.right_continuous_at_zero }
  · intro hh
    exact ⟨positiveRayKuboAndoRep_of_closedPositiveCFCWithEndpoint hh⟩

end

end Loewner
end TraceInequality
end Quantum
