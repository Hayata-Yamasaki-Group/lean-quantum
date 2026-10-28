import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.Relevel
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.HalfLine.Decreasing.EndpointEquivalence
import Quantum.TraceInequality.Loewner.HalfLine.CayleyCFCInternal
import Quantum.TraceInequality.Loewner.HalfLine.Decreasing.BasicRetained
import Quantum.TraceInequality.Loewner.HalfLine.Decreasing.CFCBridgeNormalized
import Quantum.TraceInequality.Loewner.HalfLine.Decreasing.ReciprocalTransportRetained

/-!
# Positive-ray decreasing representations: normalized CFC bridge

This module is the normalized CFC-bridge stage of the Simon-style half-line
decreasing-function theory, reducing endpoint production to normalized
reciprocal pullbacks and finite-dimensional CFC composition contracts.
-/

namespace Quantum.TraceInequality.Loewner

universe u

open CFC

open Set MeasureTheory Filter

open scoped ComplexOrder Matrix MatrixOrder NNReal Topology

noncomputable section

/-! ### Direct CFC-to-endpoint producer contracts -/

/--
Producer for the direct-CFC-to-endpoint direction in the decreasing positive
half-line theorem.
-/
structure PositiveRayOperatorMonotoneDecreasingCFCToEndpointProducer where
  withEndpoint_of_cfc :
    ∀ {g : ℝ → ℝ},
      OperatorMonotoneDecreasingOnPositiveCFC g →
        OperatorMonotoneDecreasingOnPositiveWithEndpoint.{u} g

/--
Producer for the first half of the direct-CFC-to-endpoint bridge: direct CFC
decreasing gives the open reciprocal-transport predicate.
-/
structure PositiveRayOperatorMonotoneDecreasingCFCToOpenReciprocalProducer where
  openReciprocal_of_cfc :
    ∀ {g : ℝ → ℝ},
      OperatorMonotoneDecreasingOnPositiveCFC g →
        OperatorMonotoneDecreasingOnPositive.{u} g

/--
Producer reducing the open reciprocal witness construction to closed-positive
CFC monotonicity of the canonical reciprocal witness.
-/
structure PositiveRayOperatorMonotoneDecreasingCFCToClosedPositiveReciprocalProducer where
  closedPositiveReciprocal_of_cfc :
    ∀ {g : ℝ → ℝ},
      OperatorMonotoneDecreasingOnPositiveCFC g →
        OperatorMonotoneOnClosedPositiveCFC.{0}
          (positiveRayDecreasingReciprocalWitness g)

/--
Producer reducing the direct-CFC-to-endpoint bridge to an explicitly chosen
endpoint value for the reciprocal witness.
-/
structure PositiveRayOperatorMonotoneDecreasingCFCToEndpointReciprocalProducer where
  endpointReciprocal_of_cfc :
    ∀ {g : ℝ → ℝ},
      OperatorMonotoneDecreasingOnPositiveCFC g →
        ∃ c : ℝ,
          0 ≤ c ∧
            OperatorMonotoneOnClosedPositiveCFC.{0}
              (positiveRayDecreasingReciprocalWitnessWithEndpoint g c) ∧
            Tendsto (positiveRayDecreasingReciprocalWitnessWithEndpoint g c)
              (𝓝[>] (0 : ℝ)) (𝓝 c)

/--
Producer for the scalar endpoint value and right-continuity of the endpoint
reciprocal witness.
-/
structure PositiveRayOperatorMonotoneDecreasingEndpointValueProducer where
  endpointValue_of_cfc :
    ∀ {g : ℝ → ℝ},
      OperatorMonotoneDecreasingOnPositiveCFC g →
        ∃ c : ℝ,
          0 ≤ c ∧
            Tendsto (positiveRayDecreasingReciprocalWitnessWithEndpoint g c)
              (𝓝[>] (0 : ℝ)) (𝓝 c)

/--
Producer reducing endpoint value data to the existence of a finite scalar limit
of the direct decreasing function at infinity.
-/
structure PositiveRayOperatorMonotoneDecreasingAtTopLimitProducer where
  atTopLimit_of_cfc :
    ∀ {g : ℝ → ℝ},
      OperatorMonotoneDecreasingOnPositiveCFC g →
        ∃ c : ℝ, 0 ≤ c ∧ Tendsto g atTop (𝓝 c)

/-- Concrete scalar at-top endpoint limit producer. -/
def positiveRayOperatorMonotoneDecreasingAtTopLimitProducer :
    PositiveRayOperatorMonotoneDecreasingAtTopLimitProducer where
  atTopLimit_of_cfc :=
    positiveRayOperatorMonotoneDecreasingAtTopLimit_of_cfc

/--
Build the endpoint value producer from the existence of the scalar limit
`g(x) → c` as `x → ∞`.
-/
def endpointValueProducer_of_atTopLimitProducer
    (producer : PositiveRayOperatorMonotoneDecreasingAtTopLimitProducer) :
    PositiveRayOperatorMonotoneDecreasingEndpointValueProducer where
  endpointValue_of_cfc := by
    intro g hg
    rcases producer.atTopLimit_of_cfc hg with ⟨c, hc_nonneg, hlim⟩
    exact
      ⟨c, hc_nonneg,
        positiveRayDecreasingReciprocalWitnessWithEndpoint_tendsto_nhdsGT_of_tendsto_atTop
          hlim⟩

/--
Producer for the closed-positive CFC monotonicity of an endpoint reciprocal
witness once the scalar endpoint data has been chosen.
-/
structure PositiveRayOperatorMonotoneDecreasingEndpointReciprocalClosedCFCProducer where
  closedPositiveCFC_of_endpoint :
    ∀ {g : ℝ → ℝ} {c : ℝ},
      OperatorMonotoneDecreasingOnPositiveCFC g →
        0 ≤ c →
          Tendsto (positiveRayDecreasingReciprocalWitnessWithEndpoint g c)
            (𝓝[>] (0 : ℝ)) (𝓝 c) →
            OperatorMonotoneOnClosedPositiveCFC.{0}
              (positiveRayDecreasingReciprocalWitnessWithEndpoint g c)

/--
Producer for the open-positive monotonicity part of the endpoint reciprocal
witness.
-/
structure PositiveRayOperatorMonotoneDecreasingEndpointReciprocalOpenProducer where
  openPositive_of_endpoint :
    ∀ {g : ℝ → ℝ} {c : ℝ},
      OperatorMonotoneDecreasingOnPositiveCFC g →
        0 ≤ c →
          Tendsto (positiveRayDecreasingReciprocalWitnessWithEndpoint g c)
            (𝓝[>] (0 : ℝ)) (𝓝 c) →
            OperatorMonotoneOnPositive.{u}
              (positiveRayDecreasingReciprocalWitnessWithEndpoint g c)

/--
Producer for the normalized-interval monotonicity of the endpoint reciprocal
witness.
-/
structure PositiveRayOperatorMonotoneDecreasingEndpointReciprocalUnitIntervalProducer where
  unitInterval_of_endpoint :
    ∀ {g : ℝ → ℝ} {c : ℝ},
      OperatorMonotoneDecreasingOnPositiveCFC g →
        0 ≤ c →
          Tendsto (positiveRayDecreasingReciprocalWitnessWithEndpoint g c)
            (𝓝[>] (0 : ℝ)) (𝓝 c) →
            OperatorMonotoneOnUnitInterval.{0}
              (positiveCayleyPullback
                (positiveRayDecreasingReciprocalWitnessWithEndpoint g c))

/--
Producer for the unit-interval monotonicity of the normalized reciprocal
pullback.  This is independent of the endpoint value used to extend the
reciprocal witness to zero.
-/
structure PositiveRayOperatorMonotoneDecreasingNormalizedPullbackProducer where
  unitInterval_of_cfc :
    ∀ {g : ℝ → ℝ},
      OperatorMonotoneDecreasingOnPositiveCFC g →
        OperatorMonotoneOnUnitInterval.{0}
          (positiveRayDecreasingNormalizedReciprocalPullback g)

/--
Build normalized reciprocal pullback monotonicity from an explicit CFC
composition identity for the fixed function `g`, together with the direct CFC
antitonicity of `g`.
-/
theorem normalizedPullback_of_normalizedCFCComposition
    {g : ℝ → ℝ} (hg : OperatorMonotoneDecreasingOnPositiveCFC g)
    (hcomp :
      ∀ {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A]
        [StarOrderedRing A] {a : A},
        IsSelfAdjoint a →
          quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1 →
            ((cfcₙ
                (fun y : ℝ =>
                  positiveRayDecreasingNormalizedReciprocalPullback g y -
                    positiveRayDecreasingNormalizedReciprocalPullback g 0) a : A) :
              Unitization ℂ A) =
              LownerHeinzCore.cfcR g (positiveRayNormalizedCayleyParameter a) -
                algebraMap ℝ (Unitization ℂ A) (g 1)) :
    OperatorMonotoneOnUnitInterval.{0}
      (positiveRayDecreasingNormalizedReciprocalPullback g) := by
  refine ⟨?_⟩
  intro (A : Type) _ _ _ a ha b hb hab
  let qa : Unitization ℂ A := positiveRayNormalizedCayleyParameter a
  let qb : Unitization ℂ A := positiveRayNormalizedCayleyParameter b
  have hqa_nonneg : 0 ≤ qa := by
    simpa [qa] using
      positiveRayNormalizedCayleyParameter_nonneg
        (A := A) (a := a) ha.1 ha.2
  have hqb_nonneg : 0 ≤ qb := by
    simpa [qb] using
      positiveRayNormalizedCayleyParameter_nonneg
        (A := A) (a := b) hb.1 hb.2
  have hq_le : qb ≤ qa := by
    simpa [qa, qb] using
      positiveRayNormalizedCayleyParameter_antitone
        (A := A) ha.1 hb.1 ha.2 hb.2 hab
  have hqa_spec : spectrum ℝ qa ⊆ Set.Ioi (0 : ℝ) := by
    simpa [qa] using
      positiveRayNormalizedCayleyParameter_spectrum_subset_Ioi
        (A := A) (a := a) ha.1 ha.2
  have hqb_spec : spectrum ℝ qb ⊆ Set.Ioi (0 : ℝ) := by
    simpa [qb] using
      positiveRayNormalizedCayleyParameter_spectrum_subset_Ioi
        (A := A) (a := b) hb.1 hb.2
  have hgmono :
      LownerHeinzCore.cfcR g qa ≤ LownerHeinzCore.cfcR g qb := by
    have hanti :
        LownerHeinzCore.OperatorAntitoneOn
          (𝓐 := Unitization ℂ A) (Set.Ioi (0 : ℝ)) g := by
      exact
        @OperatorMonotoneDecreasingOnPositiveCFC.antitone g hg
          (Unitization ℂ A) inferInstance Unitization.instPartialOrder
          Unitization.instStarOrderedRing inferInstance
    have hqa_sa : IsSelfAdjoint qa :=
      @IsSelfAdjoint.of_nonneg (Unitization ℂ A) inferInstance Unitization.instPartialOrder
        inferInstance Unitization.instStarOrderedRing qa hqa_nonneg
    have hqb_sa : IsSelfAdjoint qb :=
      @IsSelfAdjoint.of_nonneg (Unitization ℂ A) inferInstance Unitization.instPartialOrder
        inferInstance Unitization.instStarOrderedRing qb hqb_nonneg
    dsimp [LownerHeinzCore.OperatorAntitoneOn] at hanti
    exact hanti hqa_sa hqb_sa hq_le hqa_spec hqb_spec
  have hle_unit :
      ((cfcₙ
          (fun y : ℝ =>
            positiveRayDecreasingNormalizedReciprocalPullback g y -
              positiveRayDecreasingNormalizedReciprocalPullback g 0) a : A) :
        Unitization ℂ A) ≤
      ((cfcₙ
          (fun y : ℝ =>
            positiveRayDecreasingNormalizedReciprocalPullback g y -
              positiveRayDecreasingNormalizedReciprocalPullback g 0) b : A) :
        Unitization ℂ A) := by
    rw [hcomp (A := A) ha.1 ha.2, hcomp (A := A) hb.1 hb.2]
    exact sub_le_sub_right hgmono (algebraMap ℝ (Unitization ℂ A) (g 1))
  rw [← Unitization.inr_le_iff
    (cfcₙ
      (fun y : ℝ =>
        positiveRayDecreasingNormalizedReciprocalPullback g y -
          positiveRayDecreasingNormalizedReciprocalPullback g 0) a)
    (cfcₙ
      (fun y : ℝ =>
        positiveRayDecreasingNormalizedReciprocalPullback g y -
          positiveRayDecreasingNormalizedReciprocalPullback g 0) b)
    (cfcₙ_predicate
      (fun y : ℝ =>
        positiveRayDecreasingNormalizedReciprocalPullback g y -
          positiveRayDecreasingNormalizedReciprocalPullback g 0) a)
    (cfcₙ_predicate
      (fun y : ℝ =>
        positiveRayDecreasingNormalizedReciprocalPullback g y -
          positiveRayDecreasingNormalizedReciprocalPullback g 0) b)]
  exact hle_unit

/-! ### Producer chain from normalized pullback to endpoints -/

/--
Compatibility wrapper from the older structure producer to the theorem-style
normalized pullback bridge.
-/
def normalizedPullbackProducer_of_cfcCompositionProducer
    (producer :
      PositiveRayOperatorMonotoneDecreasingNormalizedCFCCompositionProducer) :
    PositiveRayOperatorMonotoneDecreasingNormalizedPullbackProducer where
  unitInterval_of_cfc := by
    intro g hg
    exact
      normalizedPullback_of_normalizedCFCComposition
        hg (fun {A} _ _ _ {a} ha hqa =>
          producer.normalized_cfc_eq (g := g) (A := A) (a := a) ha hqa)

/--
Build the endpoint reciprocal unit-interval producer from normalized reciprocal
pullback monotonicity.
-/
def endpointReciprocalUnitIntervalProducer_of_normalizedPullbackProducer
    (producer :
      PositiveRayOperatorMonotoneDecreasingNormalizedPullbackProducer) :
    PositiveRayOperatorMonotoneDecreasingEndpointReciprocalUnitIntervalProducer where
  unitInterval_of_endpoint := by
    intro g c hg _hc_nonneg _hcont
    exact
      OperatorMonotoneOnUnitInterval.congr_on_Ioo
        (producer.unitInterval_of_cfc hg)
        (fun y hy =>
          positiveCayleyPullback_endpointReciprocal_eq_normalizedReciprocalPullback_on_Ioo
            (g := g) (c := c) hy)

/--
Build the endpoint reciprocal open-positive producer from normalized-interval
monotonicity of the Cayley pullback.
-/
def endpointReciprocalOpenProducer_of_unitIntervalProducer
    (producer :
      PositiveRayOperatorMonotoneDecreasingEndpointReciprocalUnitIntervalProducer) :
    PositiveRayOperatorMonotoneDecreasingEndpointReciprocalOpenProducer.{u} where
  openPositive_of_endpoint := by
    intro g c hg hc_nonneg hcont
    let h : ℝ → ℝ :=
      positiveRayDecreasingReciprocalWitnessWithEndpoint g c
    let hunit : OperatorMonotoneOnUnitInterval.{0} (positiveCayleyPullback h) :=
      producer.unitInterval_of_endpoint hg hc_nonneg hcont
    exact ⟨operatorMonotoneOnUnitInterval_relevel hunit⟩

/--
Build the closed-positive CFC endpoint reciprocal producer from open-positive
monotonicity and endpoint right-continuity.
-/
def endpointReciprocalClosedCFCProducer_of_openProducer
    (openProducer :
      PositiveRayOperatorMonotoneDecreasingEndpointReciprocalOpenProducer.{u}) :
    PositiveRayOperatorMonotoneDecreasingEndpointReciprocalClosedCFCProducer where
  closedPositiveCFC_of_endpoint := by
    intro g c hg hc_nonneg hcont
    let h : ℝ → ℝ :=
      positiveRayDecreasingReciprocalWitnessWithEndpoint g c
    let hclosed : OperatorMonotoneOnClosedPositive.{0} h :=
      { to_open :=
          ⟨operatorMonotoneOnUnitInterval_toZero
            (openProducer.openPositive_of_endpoint hg hc_nonneg hcont).to_unitInterval⟩
        right_continuous_at_zero := by
          simpa [h, positiveRayDecreasingReciprocalWitnessWithEndpoint_zero]
            using hcont }
    simpa [h] using operatorMonotoneOnClosedPositiveCFC_of_endpoint hclosed

/--
Build the endpoint-valued reciprocal producer from separate scalar endpoint and
closed-positive CFC producers.
-/
def cfcToEndpointReciprocalProducer_of_endpointValueClosedCFCProducers
    (endpoint : PositiveRayOperatorMonotoneDecreasingEndpointValueProducer)
    (closed :
      PositiveRayOperatorMonotoneDecreasingEndpointReciprocalClosedCFCProducer) :
    PositiveRayOperatorMonotoneDecreasingCFCToEndpointReciprocalProducer where
  endpointReciprocal_of_cfc := by
    intro g hg
    rcases endpoint.endpointValue_of_cfc hg with ⟨c, hc_nonneg, hcont⟩
    exact
      ⟨c, hc_nonneg,
        closed.closedPositiveCFC_of_endpoint hg hc_nonneg hcont,
        hcont⟩

/--
Build the open reciprocal producer from closed-positive CFC monotonicity of
the canonical reciprocal witness.
-/
def cfcToOpenReciprocalProducer_of_closedPositiveReciprocalProducer
    (producer :
      PositiveRayOperatorMonotoneDecreasingCFCToClosedPositiveReciprocalProducer) :
    PositiveRayOperatorMonotoneDecreasingCFCToOpenReciprocalProducer.{u} where
  openReciprocal_of_cfc := by
    intro g hg
    let h : ℝ → ℝ := positiveRayDecreasingReciprocalWitness g
    exact
      { nonneg := hg.nonneg
        reciprocal_witness :=
          ⟨h,
            operatorMonotoneOnPositive_of_closedPositiveCFC
              (producer.closedPositiveReciprocal_of_cfc hg),
            by
              intro x hx
              exact positiveRayDecreasingReciprocalWitness_formula hx⟩ }

/--
Build the direct-CFC-to-endpoint producer from an endpoint-valued reciprocal
witness.
-/
def cfcToEndpointProducer_of_endpointReciprocalProducer
    (producer :
      PositiveRayOperatorMonotoneDecreasingCFCToEndpointReciprocalProducer) :
    PositiveRayOperatorMonotoneDecreasingCFCToEndpointProducer.{u} where
  withEndpoint_of_cfc := by
    intro g hg
    rcases producer.endpointReciprocal_of_cfc hg with
      ⟨c, hc_nonneg, hclosed, hcont⟩
    let h : ℝ → ℝ :=
      positiveRayDecreasingReciprocalWitnessWithEndpoint g c
    exact
      { nonneg := hg.nonneg
        reciprocal_witness :=
          ⟨h,
            operatorMonotoneOnPositive_of_closedPositiveCFC hclosed,
            by
              intro x hx
              exact
                positiveRayDecreasingReciprocalWitnessWithEndpoint_formula
                  (c := c) hx,
            by
              simpa [h] using hc_nonneg,
            by
              simpa [h] using hcont⟩ }

/--
Producer for the endpoint data of an open reciprocal witness obtained from
direct CFC decreasing.
-/
structure PositiveRayOperatorMonotoneDecreasingOpenReciprocalEndpointDataProducer where
  endpointData_of_openReciprocal_witness :
    ∀ {g h : ℝ → ℝ},
      OperatorMonotoneDecreasingOnPositiveCFC g →
        OperatorMonotoneDecreasingOnPositive.{u} g →
          OperatorMonotoneOnPositive.{u} h →
            (∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → g x = h x⁻¹) →
              0 ≤ h 0 ∧ Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0))

/--
Build the direct-CFC-to-endpoint producer from an open reciprocal producer and
endpoint data for the resulting reciprocal witness.
-/
def cfcToEndpointProducer_of_openReciprocalEndpointDataProducers
    (toOpen : PositiveRayOperatorMonotoneDecreasingCFCToOpenReciprocalProducer.{u})
    (endpoint :
      PositiveRayOperatorMonotoneDecreasingOpenReciprocalEndpointDataProducer.{u}) :
    PositiveRayOperatorMonotoneDecreasingCFCToEndpointProducer.{u} where
  withEndpoint_of_cfc := by
    intro g hg
    let hopen : OperatorMonotoneDecreasingOnPositive.{u} g :=
      toOpen.openReciprocal_of_cfc hg
    rcases hopen.reciprocal_witness with ⟨h, hh, h_formula⟩
    rcases endpoint.endpointData_of_openReciprocal_witness hg hopen hh h_formula with
      ⟨h0, hcont⟩
    exact
      { nonneg := hopen.nonneg
        reciprocal_witness := ⟨h, hh, h_formula, h0, hcont⟩ }

end

end Quantum.TraceInequality.Loewner
