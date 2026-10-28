import Quantum.TraceInequality.Loewner.LoewnerTheorem
import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.Relevel
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.HalfLine.Decreasing.CFCBridgeNormalized
import Quantum.TraceInequality.Loewner.HalfLine.Decreasing.CFCBridgeNormalizedRetained
import Quantum.TraceInequality.Loewner.HalfLine.Decreasing.CFCBridgeReciprocalClosure

/-!
# Positive-ray decreasing representations: reciprocal CFC closure

This module is the reciprocal CFC-closure stage of the Simon-style half-line
decreasing-function theory, deriving the reverse bridge and closing the
continuous and finite-matrix normalized pullback routes.
-/

namespace Quantum.TraceInequality.Loewner

universe u

open CFC

open Set MeasureTheory Filter

open scoped ComplexOrder Matrix MatrixOrder NNReal Topology

noncomputable section

/-! ### Reciprocal CFC composition for the reverse bridge -/

/--
Producer for the CFC composition step: a positive-ray operator monotone
reciprocal witness `h` and the identity `g x = h x⁻¹` on `(0,∞)` make `g`
operator antitone on `(0,∞)`.
-/
structure PositiveRayOperatorMonotoneDecreasingReciprocalCFCCompositionProducer where
  antitone_of_reciprocal :
    ∀ {g h : ℝ → ℝ},
      OperatorMonotoneOnPositive.{u} h →
        (∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → g x = h x⁻¹) →
          LownerHeinzCore.OperatorAntitoneOnAll.{0} (Set.Ioi (0 : ℝ)) g
-- LW2-D-PRIVATE-FIXTURE-END chk_d_priv_05

private theorem isStrictlyPositive_cfc_one_div_of_spectrum_Ioi
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] {a : A}
    (ha_nonneg : 0 ≤ a) (ha_spec : spectrum ℝ a ⊆ Set.Ioi (0 : ℝ)) :
    IsStrictlyPositive (cfc (fun x : ℝ => 1 / x) a) := by
  have ha_sa : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha_nonneg
  have hcont :
      ContinuousOn (fun x : ℝ => 1 / x) (spectrum ℝ a) := by
    intro x hx
    have hxpos : 0 < x := by simpa using ha_spec hx
    simpa [one_div] using
      (continuousAt_inv₀ (ne_of_gt hxpos)).continuousWithinAt
  have hspectrum :
      spectrum ℝ (cfc (fun x : ℝ => 1 / x) a) =
        (fun x : ℝ => 1 / x) '' spectrum ℝ a := by
    simpa using
      (cfc_map_spectrum (R := ℝ) (A := A) (p := IsSelfAdjoint)
        (f := fun x : ℝ => 1 / x) (a := a) (ha := ha_sa) (hf := hcont))
  refine
    (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos
      (R := ℝ) (cfc (fun x : ℝ => 1 / x) a)).2 ?_
  intro y hy
  rw [hspectrum] at hy
  rcases hy with ⟨x, hx, hxy⟩
  rw [← hxy]
  exact one_div_pos.mpr (by simpa using ha_spec hx)
-- LW2-D-PRIVATE-FIXTURE-END chk_d_priv_06

/--
Simon Chapter 20/Hiai Proposition 2.28 bridge: a positive-ray monotone
reciprocal witness makes the original function CFC-antitone on `(0,∞)`.
-/
theorem operatorAntitoneOnAll_of_operatorMonotoneOnPositive_reciprocal
    {g h : ℝ → ℝ} (hh : OperatorMonotoneOnPositive.{u} h)
    (h_formula : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → g x = h x⁻¹) :
    LownerHeinzCore.OperatorAntitoneOnAll.{0} (Set.Ioi (0 : ℝ)) g := by
  let hh0 : OperatorMonotoneOnPositive.{0} h :=
    ⟨operatorMonotoneOnUnitInterval_toZero hh.to_unitInterval⟩
  intro A _ _ _ _ a b ha_sa hb_sa hba ha_spec hb_spec
  have ha_nonneg : 0 ≤ a := by
    have h' : algebraMap ℝ A (0 : ℝ) ≤ a :=
      (algebraMap_le_iff_le_spectrum (R := ℝ) (A := A) (p := IsSelfAdjoint)
        (r := (0 : ℝ)) (a := a) (ha := ha_sa)).2 (by
          intro x hx
          exact le_of_lt (ha_spec hx))
    simpa using h'
  have hb_nonneg : 0 ≤ b := by
    have h' : algebraMap ℝ A (0 : ℝ) ≤ b :=
      (algebraMap_le_iff_le_spectrum (R := ℝ) (A := A) (p := IsSelfAdjoint)
        (r := (0 : ℝ)) (a := b) (ha := hb_sa)).2 (by
          intro x hx
          exact le_of_lt (hb_spec hx))
    simpa using h'
  let ainv : A := LownerHeinzCore.cfcR (fun x : ℝ => 1 / x) a
  let binv : A := LownerHeinzCore.cfcR (fun x : ℝ => 1 / x) b
  have hinv_le : ainv ≤ binv := by
    have hanti := LownerHeinzCore.one_div_operatorAntitoneOn_Ioi (𝓐 := A)
    dsimp [LownerHeinzCore.OperatorAntitoneOn] at hanti
    simpa [ainv, binv] using
      hanti ha_sa hb_sa hba ha_spec hb_spec
  have hainv_pos : IsStrictlyPositive ainv := by
    simpa [ainv, LownerHeinzCore.cfcR] using
      isStrictlyPositive_cfc_one_div_of_spectrum_Ioi
        (A := A) ha_nonneg ha_spec
  have hbinv_pos : IsStrictlyPositive binv := by
    simpa [binv, LownerHeinzCore.cfcR] using
      isStrictlyPositive_cfc_one_div_of_spectrum_Ioi
        (A := A) hb_nonneg hb_spec
  have hmono :
      cfc (fun x : ℝ => h x - h 0) ainv ≤
        cfc (fun x : ℝ => h x - h 0) binv :=
    positiveCayley_cfc_transport_of_strictPositive
      hh0 hainv_pos hbinv_pos hinv_le
  have ha_eq :=
    cfc_reciprocal_formula_eq
      (A := A) hh h_formula ha_nonneg ha_spec
  have hb_eq :=
    cfc_reciprocal_formula_eq
      (A := A) hh h_formula hb_nonneg hb_spec
  rw [ha_eq, hb_eq]
  simpa [ainv, binv, add_comm, add_left_comm, add_assoc] using
    add_le_add_right hmono (algebraMap ℝ A (h 0))

/-- Concrete reciprocal CFC composition producer. -/
def positiveRayOperatorMonotoneDecreasingReciprocalCFCCompositionProducer :
    PositiveRayOperatorMonotoneDecreasingReciprocalCFCCompositionProducer.{u} where
  antitone_of_reciprocal :=
    operatorAntitoneOnAll_of_operatorMonotoneOnPositive_reciprocal

/--
If `g = 1 / f` is positive-ray decreasing and `f` is positive, then `f` is
positive-ray operator monotone.
-/
theorem operatorMonotoneOnPositive_of_reciprocal_decreasing
    {f g : ℝ → ℝ}
    (hfpos : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → 0 < f x)
    (hgf : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → g x = (f x)⁻¹)
    (hg : OperatorMonotoneDecreasingOnPositive.{u} g) :
    OperatorMonotoneOnPositive.{u} f := by
  rcases hg.reciprocal_witness with ⟨h, hh, h_formula⟩
  have hganti : LownerHeinzCore.OperatorAntitoneOnAll.{0} (Set.Ioi (0 : ℝ)) g := by
    intro 𝓑 _ _ _ _
    exact
      @operatorAntitoneOnAll_of_operatorMonotoneOnPositive_reciprocal
        g h hh h_formula 𝓑 inferInstance inferInstance inferInstance
        inferInstance
  exact @operatorMonotoneOnPositive_of_reciprocal_operatorAntitoneOnAll
    f g hfpos hgf
    (fun hA hB hBA hAs hBs => hganti hA hB hBA hAs hBs)

/--
The endpoint-refined reciprocal predicate gives the direct CFC predicate once
the reciprocal CFC composition step is supplied.
-/
theorem operatorMonotoneDecreasingOnPositiveCFC_of_withEndpoint_of_reciprocalCFCCompositionProducer
    (producer : PositiveRayOperatorMonotoneDecreasingReciprocalCFCCompositionProducer.{u})
    {g : ℝ → ℝ} (hg : OperatorMonotoneDecreasingOnPositiveWithEndpoint.{u} g) :
    OperatorMonotoneDecreasingOnPositiveCFC g := by
  rcases hg.reciprocal_witness with ⟨h, hh, h_formula, _h0, _hcont⟩
  exact
    { nonneg := hg.nonneg
      antitone := by
        intro 𝓑 _ _ _ _
        exact producer.antitone_of_reciprocal hh h_formula }

/-! ### Direct CFC equivalence via split producers -/

/--
Producer isolating the bridge between the direct CFC decreasing predicate and
the endpoint-refined reciprocal-transport predicate. Hiai Proposition 2.28 is
`positiveCFC_iff_nonempty_rep` below. Its proof reaches
`positiveCFC_iff_nonempty_rep_of_splitProducers` through wrapper theorems; that
theorem builds this producer from the two split producers and passes it to
`positiveCFC_iff_nonempty_rep_of_cfcEndpointProducer`.
-/
structure PositiveRayOperatorMonotoneDecreasingCFCEndpointProducer where
  withEndpoint_of_cfc :
    ∀ {g : ℝ → ℝ},
      OperatorMonotoneDecreasingOnPositiveCFC g →
        OperatorMonotoneDecreasingOnPositiveWithEndpoint.{u} g
  cfc_of_withEndpoint :
    ∀ {g : ℝ → ℝ},
      OperatorMonotoneDecreasingOnPositiveWithEndpoint.{u} g →
        OperatorMonotoneDecreasingOnPositiveCFC g

/--
Build the CFC-endpoint producer from the direct-CFC-to-endpoint producer and
the reciprocal CFC composition producer.
-/
def positiveRayOperatorMonotoneDecreasingCFCEndpointProducer_of_splitProducers
    (toEndpoint : PositiveRayOperatorMonotoneDecreasingCFCToEndpointProducer.{u})
    (composition : PositiveRayOperatorMonotoneDecreasingReciprocalCFCCompositionProducer.{u}) :
    PositiveRayOperatorMonotoneDecreasingCFCEndpointProducer.{u} where
  withEndpoint_of_cfc := toEndpoint.withEndpoint_of_cfc
  cfc_of_withEndpoint :=
    operatorMonotoneDecreasingOnPositiveCFC_of_withEndpoint_of_reciprocalCFCCompositionProducer
      composition

/--
Producer-dependent form of Hiai Proposition 2.28 from the direct CFC predicate
to the resolvent representation.
-/
theorem positiveCFC_iff_nonempty_rep_of_cfcEndpointProducer
    (producer : PositiveRayOperatorMonotoneDecreasingCFCEndpointProducer.{u})
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositiveCFC g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) := by
  constructor
  · intro hg
    exact operatorMonotoneDecreasingOnPositiveWithEndpoint_iff_nonempty_rep.mp
      (producer.withEndpoint_of_cfc hg)
  · intro hrep
    exact producer.cfc_of_withEndpoint
      (operatorMonotoneDecreasingOnPositiveWithEndpoint_iff_nonempty_rep.mpr hrep)

/--
Producer-dependent form of Hiai Proposition 2.28 after splitting the
CFC-endpoint bridge into two lower-level producer responsibilities.  Both
producers are constructed on the way to `positiveCFC_iff_nonempty_rep` below.
-/
theorem positiveCFC_iff_nonempty_rep_of_splitProducers
    (toEndpoint : PositiveRayOperatorMonotoneDecreasingCFCToEndpointProducer.{u})
    (composition : PositiveRayOperatorMonotoneDecreasingReciprocalCFCCompositionProducer.{u})
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositiveCFC g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  positiveCFC_iff_nonempty_rep_of_cfcEndpointProducer
    (positiveRayOperatorMonotoneDecreasingCFCEndpointProducer_of_splitProducers
      toEndpoint composition)

/--
Specialize the producer-dependent Hiai Proposition 2.28 equivalence using the
concrete reciprocal CFC composition producer.
-/
theorem positiveCFC_iff_nonempty_rep_of_cfcToEndpointProducer
    (toEndpoint : PositiveRayOperatorMonotoneDecreasingCFCToEndpointProducer.{u})
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositiveCFC g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  positiveCFC_iff_nonempty_rep_of_splitProducers
    toEndpoint positiveRayOperatorMonotoneDecreasingReciprocalCFCCompositionProducer

/--
Reduce the direct CFC decreasing/resolvent equivalence to an open reciprocal
producer plus endpoint data.
-/
theorem positiveCFC_iff_nonempty_rep_of_openReciprocalEndpointDataProducers
    (toOpen : PositiveRayOperatorMonotoneDecreasingCFCToOpenReciprocalProducer.{u})
    (endpoint :
      PositiveRayOperatorMonotoneDecreasingOpenReciprocalEndpointDataProducer.{u})
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositiveCFC g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  positiveCFC_iff_nonempty_rep_of_cfcToEndpointProducer
    (cfcToEndpointProducer_of_openReciprocalEndpointDataProducers
      toOpen endpoint)

/--
Reduce the direct CFC decreasing/resolvent equivalence to a producer of the
endpoint reciprocal witness.
-/
theorem positiveCFC_iff_nonempty_rep_of_endpointReciprocalProducer
    (producer :
      PositiveRayOperatorMonotoneDecreasingCFCToEndpointReciprocalProducer)
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositiveCFC g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  positiveCFC_iff_nonempty_rep_of_cfcToEndpointProducer
    (cfcToEndpointProducer_of_endpointReciprocalProducer.{0}
      producer)

/--
Reduce the direct CFC decreasing/resolvent equivalence to endpoint-value data
and closed-positive CFC monotonicity of the endpoint reciprocal witness.
-/
theorem positiveCFC_iff_nonempty_rep_of_endpointValueClosedCFCProducers
    (endpoint : PositiveRayOperatorMonotoneDecreasingEndpointValueProducer)
    (closed :
      PositiveRayOperatorMonotoneDecreasingEndpointReciprocalClosedCFCProducer)
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositiveCFC g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  positiveCFC_iff_nonempty_rep_of_endpointReciprocalProducer
    (cfcToEndpointReciprocalProducer_of_endpointValueClosedCFCProducers
      endpoint closed)

/--
Endpoint value data plus open-positive monotonicity of the endpoint reciprocal
witness imply the producer-dependent direct CFC decreasing equivalence.
-/
theorem positiveCFC_iff_nonempty_rep_of_endpointValueOpenProducers
    (endpoint : PositiveRayOperatorMonotoneDecreasingEndpointValueProducer)
    (openProducer :
      PositiveRayOperatorMonotoneDecreasingEndpointReciprocalOpenProducer.{u})
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositiveCFC g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  positiveCFC_iff_nonempty_rep_of_endpointValueClosedCFCProducers
    endpoint
    (endpointReciprocalClosedCFCProducer_of_openProducer
      openProducer)

/--
Endpoint value data plus normalized-interval monotonicity of the endpoint
reciprocal witness imply the producer-dependent direct CFC decreasing
equivalence.
-/
theorem positiveCFC_iff_nonempty_rep_of_endpointValueUnitIntervalProducers
    (endpoint : PositiveRayOperatorMonotoneDecreasingEndpointValueProducer)
    (unitInterval :
      PositiveRayOperatorMonotoneDecreasingEndpointReciprocalUnitIntervalProducer)
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositiveCFC g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  positiveCFC_iff_nonempty_rep_of_endpointValueOpenProducers
    endpoint
    (endpointReciprocalOpenProducer_of_unitIntervalProducer.{0}
      unitInterval)

/--
Endpoint value data plus normalized reciprocal pullback monotonicity imply the
producer-dependent direct CFC decreasing equivalence.
-/
theorem positiveCFC_iff_nonempty_rep_of_endpointValueNormalizedPullbackProducers
    (endpoint : PositiveRayOperatorMonotoneDecreasingEndpointValueProducer)
    (normalized :
      PositiveRayOperatorMonotoneDecreasingNormalizedPullbackProducer)
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositiveCFC g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  positiveCFC_iff_nonempty_rep_of_endpointValueUnitIntervalProducers
    endpoint
    (endpointReciprocalUnitIntervalProducer_of_normalizedPullbackProducer
      normalized)

/--
At-top scalar endpoint limits plus normalized reciprocal pullback monotonicity
imply the producer-dependent direct CFC decreasing equivalence.
-/
theorem positiveCFC_iff_nonempty_rep_of_atTopLimitNormalizedPullbackProducers
    (atTopLimit : PositiveRayOperatorMonotoneDecreasingAtTopLimitProducer)
    (normalized :
      PositiveRayOperatorMonotoneDecreasingNormalizedPullbackProducer)
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositiveCFC g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  positiveCFC_iff_nonempty_rep_of_endpointValueNormalizedPullbackProducers
    (endpointValueProducer_of_atTopLimitProducer
      atTopLimit)
    normalized

/--
Normalized reciprocal pullback monotonicity is now the only producer input
needed for the direct CFC decreasing/resolvent representation equivalence.
-/
theorem positiveCFC_iff_nonempty_rep_of_normalizedPullbackProducer
    (normalized :
      PositiveRayOperatorMonotoneDecreasingNormalizedPullbackProducer)
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositiveCFC g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  positiveCFC_iff_nonempty_rep_of_atTopLimitNormalizedPullbackProducers
    positiveRayOperatorMonotoneDecreasingAtTopLimitProducer normalized

/--
CFC composition for the normalized reciprocal pullback is the only producer
input needed for the direct CFC decreasing/resolvent representation equivalence.
-/
theorem positiveCFC_iff_nonempty_rep_of_normalizedCFCCompositionProducer
    (producer :
      PositiveRayOperatorMonotoneDecreasingNormalizedCFCCompositionProducer)
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositiveCFC g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  positiveCFC_iff_nonempty_rep_of_normalizedPullbackProducer
    (normalizedPullbackProducer_of_cfcCompositionProducer
      producer)

/--
An explicit CFC composition identity for each fixed directly CFC-decreasing
function is enough for the direct CFC decreasing/resolvent representation
equivalence.
-/
theorem positiveCFC_iff_nonempty_rep_of_normalizedCFCComposition
    (hcomp :
      ∀ {g : ℝ → ℝ},
        OperatorMonotoneDecreasingOnPositiveCFC g →
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
                    algebraMap ℝ (Unitization ℂ A) (g 1))
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositiveCFC g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  positiveCFC_iff_nonempty_rep_of_normalizedPullbackProducer
    { unitInterval_of_cfc := by
        intro g hg
        exact
          normalizedPullback_of_normalizedCFCComposition
            hg (hcomp (g := g) hg) }

/--
Local continuity of each fixed directly CFC-decreasing function on the relevant
spectral image is enough to supply the CFC composition identity needed for
Hiai Proposition 2.28.
-/
theorem positiveCFC_iff_nonempty_rep_of_normalizedCFCCompositionContinuity
    (hcont :
      ∀ {g : ℝ → ℝ},
        OperatorMonotoneDecreasingOnPositiveCFC g →
          ∀ {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A]
            [StarOrderedRing A] {a : A},
            IsSelfAdjoint a →
              quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1 →
                ContinuousOn g
                  ((fun y : ℝ => (unitToPositiveCayley y)⁻¹) ''
                    spectrum ℝ (a : Unitization ℂ A)))
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositiveCFC g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  positiveCFC_iff_nonempty_rep_of_normalizedCFCComposition
    (fun {g} hg {A} _ _ _ {a} ha_sa ha =>
      normalizedCFCComposition_of_continuousOn
        (g := g) (A := A) (a := a) ha_sa ha
        (hcont (g := g) hg (A := A) (a := a) ha_sa ha))

/--
Positive-ray continuity of each directly CFC-decreasing function is enough for
the direct CFC decreasing/resolvent representation equivalence.
-/
theorem positiveCFC_iff_nonempty_rep_of_continuousOn_Ioi
    (hcont :
      ∀ {g : ℝ → ℝ},
        OperatorMonotoneDecreasingOnPositiveCFC g →
          ContinuousOn g (Set.Ioi (0 : ℝ)))
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositiveCFC g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  positiveCFC_iff_nonempty_rep_of_normalizedCFCCompositionContinuity
    (fun {g} hg {A} _ _ _ {a} ha_sa ha =>
      normalizedCFCCompositionContinuity_of_continuousOn_Ioi
        (g := g) (A := A) (a := a) (hcont (g := g) hg) ha_sa ha)

/--
Continuity of the normalized reciprocal pullback on the normalized interval
supplies the positive-ray continuity needed by the normalized CFC composition
bridge.
-/
theorem positiveCFC_iff_nonempty_rep_of_normalizedPullbackContinuousOn
    (hcont :
      ∀ {g : ℝ → ℝ},
        OperatorMonotoneDecreasingOnPositiveCFC g →
          ContinuousOn (positiveRayDecreasingNormalizedReciprocalPullback g)
            (Set.Ioo (-1 : ℝ) 1))
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositiveCFC g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  positiveCFC_iff_nonempty_rep_of_continuousOn_Ioi
    (fun {g} hg =>
      continuousOn_Ioi_of_normalizedReciprocalPullback_continuousOn
        (g := g) (hcont (g := g) hg))

/--
Finite-dimensional normalized-interval CFC monotonicity of the normalized
reciprocal pullback supplies the continuity input needed for the direct CFC
decreasing/resolvent representation equivalence.
-/
theorem positiveCFC_iff_nonempty_rep_of_normalizedPullbackFiniteMatrixMonotone
    (hfinite :
      ∀ {g : ℝ → ℝ},
        OperatorMonotoneDecreasingOnPositiveCFC g →
          UnitIntervalMatrixMonotone
            (positiveRayDecreasingNormalizedReciprocalPullback g))
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositiveCFC g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  positiveCFC_iff_nonempty_rep_of_normalizedPullbackContinuousOn
    (fun {g} hg =>
      continuousOn_normalizedReciprocalPullback_of_finiteMatrixMonotone
        (g := g) (hfinite (g := g) hg))

/--
The direct CFC decreasing predicate gives finite-dimensional CFC monotonicity
of the normalized reciprocal pullback.  The only CFC composition input is the
finite-spectrum version above.
-/
theorem finiteMatrixMonotone_reciprocalPullback_of_cfcDecreasing
    {g : ℝ → ℝ} (hg : OperatorMonotoneDecreasingOnPositiveCFC g) :
    UnitIntervalFiniteMatrixMonotone.{0}
      (positiveRayDecreasingNormalizedReciprocalPullback g) := by
  refine ⟨?_⟩
  intro (A : Type) _ _ _ _ a ha b hb hab
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
    rw [normalizedCFCComposition_of_finiteDimensional
        (g := g) (A := A) (a := a) ha.1 ha.2,
      normalizedCFCComposition_of_finiteDimensional
        (g := g) (A := A) (a := b) hb.1 hb.2]
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

/--
Book-facing full equivalence for Hiai Proposition 2.28 in the direct CFC
decreasing formulation.
-/
theorem positiveCFC_iff_nonempty_rep
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositiveCFC g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  positiveCFC_iff_nonempty_rep_of_normalizedPullbackFiniteMatrixMonotone
    (fun {g} hg =>
      unitIntervalMatrixMonotone_of_finiteMatrixMonotone
        (finiteMatrixMonotone_reciprocalPullback_of_cfcDecreasing
          (g := g) hg))

/--
Reduce the direct CFC decreasing/resolvent equivalence to closed-positive
reciprocal production plus open endpoint data.
-/
theorem positiveCFC_iff_nonempty_rep_of_closedPositiveReciprocalEndpointDataProducers
    (closed :
      PositiveRayOperatorMonotoneDecreasingCFCToClosedPositiveReciprocalProducer)
    (endpoint :
      PositiveRayOperatorMonotoneDecreasingOpenReciprocalEndpointDataProducer.{u})
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositiveCFC g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  positiveCFC_iff_nonempty_rep_of_openReciprocalEndpointDataProducers
    (cfcToOpenReciprocalProducer_of_closedPositiveReciprocalProducer.{u}
      closed)
    endpoint

end

end Quantum.TraceInequality.Loewner
