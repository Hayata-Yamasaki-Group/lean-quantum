import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.Relevel
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.HalfLine.Decreasing.ResolventKuboAndo

/-!
# Positive-ray decreasing representations: endpoint equivalence

This module is the endpoint-equivalence stage of the Simon-style half-line
decreasing-function theory, connecting finite resolvent representations with
positive-ray operator monotone decreasing predicates and endpoint data.
-/

namespace Quantum.TraceInequality.Loewner

universe u

open CFC

open Set MeasureTheory Filter

open scoped ComplexOrder Matrix MatrixOrder NNReal Topology

noncomputable section

/-! ### Producer hierarchy for endpoint equivalence -/

/--
Producer contract for the full Hiai Proposition 2.28 equivalence between
positive-ray operator monotone decreasing functions and finite resolvent
representations.

The representation-level reciprocal Kubo--Ando conversion is already proved in
this file.  These fields retain the legacy decomposition of the two directions;
the producer-free theorem below supplies both directions unconditionally.
-/
structure PositiveRayOperatorMonotoneDecreasingEquivalenceProducer where
  operatorMonotoneDecreasingOnPositive_of_rep :
    ∀ {g : ℝ → ℝ},
      PositiveRayOperatorMonotoneDecreasingRep g →
        OperatorMonotoneDecreasingOnPositive.{u} g
  rep_of_operatorMonotoneDecreasingOnPositive :
    ∀ {g : ℝ → ℝ},
      OperatorMonotoneDecreasingOnPositive.{u} g →
        Nonempty (PositiveRayOperatorMonotoneDecreasingRep g)

/--
Reduced producer contract: the reverse direction is lowered to constructing a
Kubo--Ando representation for a reciprocal witness.
-/
structure PositiveRayOperatorMonotoneDecreasingKuboAndoProducer where
  operatorMonotoneDecreasingOnPositive_of_rep :
    ∀ {g : ℝ → ℝ},
      PositiveRayOperatorMonotoneDecreasingRep g →
        OperatorMonotoneDecreasingOnPositive.{u} g
  reciprocalKuboAndoRep_of_operatorMonotoneDecreasingOnPositive :
    ∀ {g : ℝ → ℝ},
      OperatorMonotoneDecreasingOnPositive.{u} g →
        ∃ h : ℝ → ℝ,
          (∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → g x = h x⁻¹) ∧
            0 ≤ h 0 ∧ Nonempty (PositiveRayKuboAndoRep h)

/-- Build the full equivalence producer from the reduced Kubo--Ando producer. -/
noncomputable def
    positiveRayOperatorMonotoneDecreasingEquivalenceProducer_of_kuboAndoProducer
    (producer : PositiveRayOperatorMonotoneDecreasingKuboAndoProducer.{u}) :
    PositiveRayOperatorMonotoneDecreasingEquivalenceProducer.{u} where
  operatorMonotoneDecreasingOnPositive_of_rep :=
    producer.operatorMonotoneDecreasingOnPositive_of_rep
  rep_of_operatorMonotoneDecreasingOnPositive := by
    intro g hg
    rcases producer.reciprocalKuboAndoRep_of_operatorMonotoneDecreasingOnPositive hg
      with ⟨h, h_formula, h0, ⟨rep⟩⟩
    exact
      ⟨positiveRayOperatorMonotoneDecreasingRep_of_reciprocalKuboAndoRep
        h_formula rep h0⟩

/--
Further reduced producer contract: the reverse direction is lowered to proving
that a reciprocal witness extends to the closed-positive monotonicity package.
-/
structure PositiveRayOperatorMonotoneDecreasingClosedPositiveProducer where
  operatorMonotoneDecreasingOnPositive_of_rep :
    ∀ {g : ℝ → ℝ},
      PositiveRayOperatorMonotoneDecreasingRep g →
        OperatorMonotoneDecreasingOnPositive.{u} g
  closedPositiveReciprocal_of_operatorMonotoneDecreasingOnPositive :
    ∀ {g : ℝ → ℝ},
      OperatorMonotoneDecreasingOnPositive.{u} g →
        ∃ h : ℝ → ℝ,
          (∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → g x = h x⁻¹) ∧
            0 ≤ h 0 ∧ OperatorMonotoneOnClosedPositive.{u} h

/-- Build the Kubo--Ando reduced producer from a closed-positive producer. -/
noncomputable def
    positiveRayOperatorMonotoneDecreasingKuboAndoProducer_of_closedPositiveProducer
    (producer : PositiveRayOperatorMonotoneDecreasingClosedPositiveProducer.{u}) :
    PositiveRayOperatorMonotoneDecreasingKuboAndoProducer.{u} where
  operatorMonotoneDecreasingOnPositive_of_rep :=
    producer.operatorMonotoneDecreasingOnPositive_of_rep
  reciprocalKuboAndoRep_of_operatorMonotoneDecreasingOnPositive := by
    intro g hg
    rcases producer.closedPositiveReciprocal_of_operatorMonotoneDecreasingOnPositive hg
      with ⟨h, h_formula, h0, hclosed⟩
    exact
      ⟨h, h_formula, h0,
        ⟨positiveRayKuboAndoRep_of_operatorMonotoneOnClosedPositive hclosed⟩⟩

/-- Build the full equivalence producer from a closed-positive producer. -/
noncomputable def
    positiveRayOperatorMonotoneDecreasingEquivalenceProducer_of_closedPositiveProducer
    (producer : PositiveRayOperatorMonotoneDecreasingClosedPositiveProducer.{u}) :
    PositiveRayOperatorMonotoneDecreasingEquivalenceProducer.{u} :=
  positiveRayOperatorMonotoneDecreasingEquivalenceProducer_of_kuboAndoProducer
    (positiveRayOperatorMonotoneDecreasingKuboAndoProducer_of_closedPositiveProducer
      producer)

/--
Endpoint reduced producer: the reverse direction is lowered to an open-positive
reciprocal witness plus right-continuity at `0`.
-/
structure PositiveRayOperatorMonotoneDecreasingEndpointProducer where
  operatorMonotoneDecreasingOnPositive_of_rep :
    ∀ {g : ℝ → ℝ},
      PositiveRayOperatorMonotoneDecreasingRep g →
        OperatorMonotoneDecreasingOnPositive.{u} g
  endpointReciprocal_of_operatorMonotoneDecreasingOnPositive :
    ∀ {g : ℝ → ℝ},
      OperatorMonotoneDecreasingOnPositive.{u} g →
        ∃ h : ℝ → ℝ,
          (∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → g x = h x⁻¹) ∧
            0 ≤ h 0 ∧ OperatorMonotoneOnPositive.{u} h ∧
              Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0))

/-- Build the closed-positive producer from an endpoint producer. -/
noncomputable def
    positiveRayOperatorMonotoneDecreasingClosedPositiveProducer_of_endpointProducer
    (producer : PositiveRayOperatorMonotoneDecreasingEndpointProducer.{u}) :
    PositiveRayOperatorMonotoneDecreasingClosedPositiveProducer.{u} where
  operatorMonotoneDecreasingOnPositive_of_rep :=
    producer.operatorMonotoneDecreasingOnPositive_of_rep
  closedPositiveReciprocal_of_operatorMonotoneDecreasingOnPositive := by
    intro g hg
    rcases producer.endpointReciprocal_of_operatorMonotoneDecreasingOnPositive hg
      with ⟨h, h_formula, h0, hopen, hcont⟩
    exact
      ⟨h, h_formula, h0,
        { to_open := hopen
          right_continuous_at_zero := hcont }⟩

/-- Build the full equivalence producer from an endpoint producer. -/
noncomputable def
    positiveRayOperatorMonotoneDecreasingEquivalenceProducer_of_endpointProducer
    (producer : PositiveRayOperatorMonotoneDecreasingEndpointProducer.{u}) :
    PositiveRayOperatorMonotoneDecreasingEquivalenceProducer.{u} :=
  positiveRayOperatorMonotoneDecreasingEquivalenceProducer_of_closedPositiveProducer
    (positiveRayOperatorMonotoneDecreasingClosedPositiveProducer_of_endpointProducer
      producer)

/-! ### Concrete forward bridge and endpoint data -/

/--
Forward producer: the representation-to-monotonicity direction is reduced to
constructing a positive-ray monotone reciprocal witness for each resolvent
representation.
-/
structure PositiveRayOperatorMonotoneDecreasingForwardProducer where
  reciprocalMonotone_of_rep :
    ∀ {g : ℝ → ℝ},
      PositiveRayOperatorMonotoneDecreasingRep g →
        ∃ h : ℝ → ℝ,
          OperatorMonotoneOnPositive.{u} h ∧
            ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → g x = h x⁻¹

/--
Reverse producer: the monotonicity-to-representation direction is reduced to
the endpoint reciprocal witness already used by the endpoint producer.
-/
structure PositiveRayOperatorMonotoneDecreasingEndpointReverseProducer where
  endpointReciprocal_of_operatorMonotoneDecreasingOnPositive :
    ∀ {g : ℝ → ℝ},
      OperatorMonotoneDecreasingOnPositive.{u} g →
        ∃ h : ℝ → ℝ,
          (∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → g x = h x⁻¹) ∧
            0 ≤ h 0 ∧ OperatorMonotoneOnPositive.{u} h ∧
              Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0))

/--
Concrete forward producer: a resolvent representation supplies its reciprocal
Kubo--Ando witness, hence the reciprocal-transport monotonicity direction.
-/
noncomputable def positiveRayOperatorMonotoneDecreasingForwardProducer :
    PositiveRayOperatorMonotoneDecreasingForwardProducer.{u} where
  reciprocalMonotone_of_rep := by
    intro g rep
    refine
      ⟨positiveRayKuboAndoOfOperatorMonotoneDecreasingRep rep,
        operatorMonotoneOnPositive_of_positiveRayKuboAndoRep
          (positiveRayKuboAndoRep_of_operatorMonotoneDecreasingRep rep), ?_⟩
    intro x hx
    have hxpos : 0 < x := by simpa using hx
    have hxinv_ne : x⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hxpos)
    simp [positiveRayKuboAndoOfOperatorMonotoneDecreasingRep, hxinv_ne]

/-- Build the endpoint producer from separated forward and reverse producers. -/
def positiveRayOperatorMonotoneDecreasingEndpointProducer_of_forwardReverseProducer
    (forward : PositiveRayOperatorMonotoneDecreasingForwardProducer.{u})
    (reverse : PositiveRayOperatorMonotoneDecreasingEndpointReverseProducer.{u}) :
    PositiveRayOperatorMonotoneDecreasingEndpointProducer.{u} where
  operatorMonotoneDecreasingOnPositive_of_rep := by
    intro g rep
    rcases forward.reciprocalMonotone_of_rep rep with ⟨h, hh, h_formula⟩
    exact
      operatorMonotoneDecreasingOnPositive_of_rep_of_reciprocalMonotone
        rep hh h_formula
  endpointReciprocal_of_operatorMonotoneDecreasingOnPositive :=
    reverse.endpointReciprocal_of_operatorMonotoneDecreasingOnPositive

/-- Build the endpoint producer from the concrete forward producer and a reverse producer. -/
noncomputable def
    positiveRayOperatorMonotoneDecreasingEndpointProducer_of_endpointReverseProducer
    (reverse : PositiveRayOperatorMonotoneDecreasingEndpointReverseProducer.{u}) :
    PositiveRayOperatorMonotoneDecreasingEndpointProducer.{u} :=
  positiveRayOperatorMonotoneDecreasingEndpointProducer_of_forwardReverseProducer
    positiveRayOperatorMonotoneDecreasingForwardProducer reverse

/--
Endpoint-data producer: once the reciprocal witness already stored in
`OperatorMonotoneDecreasingOnPositive` is fixed, the remaining reverse
endpoint content is nonnegativity at zero and right continuity at zero.
-/
structure PositiveRayOperatorMonotoneDecreasingEndpointDataProducer where
  endpointData_of_reciprocal_witness :
    ∀ {g h : ℝ → ℝ},
      OperatorMonotoneDecreasingOnPositive.{u} g →
        OperatorMonotoneOnPositive.{u} h →
          (∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → g x = h x⁻¹) →
            0 ≤ h 0 ∧ Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0))

/--
Build the endpoint reverse producer from endpoint data for the reciprocal
witness already carried by `OperatorMonotoneDecreasingOnPositive`.
-/
def positiveRayOperatorMonotoneDecreasingEndpointReverseProducer_of_endpointDataProducer
    (producer : PositiveRayOperatorMonotoneDecreasingEndpointDataProducer.{u}) :
    PositiveRayOperatorMonotoneDecreasingEndpointReverseProducer.{u} where
  endpointReciprocal_of_operatorMonotoneDecreasingOnPositive := by
    intro g hg
    rcases hg.reciprocal_witness with ⟨h, hh, h_formula⟩
    rcases producer.endpointData_of_reciprocal_witness hg hh h_formula with
      ⟨h0, hcont⟩
    exact ⟨h, h_formula, h0, hh, hcont⟩

/-! ### Endpoint-refined predicate and resolvent equivalence -/

/-- Forget the endpoint data in the endpoint-refined reciprocal predicate. -/
theorem
    OperatorMonotoneDecreasingOnPositiveWithEndpoint.to_operatorMonotoneDecreasingOnPositive
    {g : ℝ → ℝ} (hg : OperatorMonotoneDecreasingOnPositiveWithEndpoint.{u} g) :
    OperatorMonotoneDecreasingOnPositive.{u} g := by
  rcases hg.reciprocal_witness with ⟨h, hh, h_formula, _h0, _hcont⟩
  exact
    { nonneg := hg.nonneg
      reciprocal_witness := ⟨h, hh, h_formula⟩ }

/--
A decreasing resolvent representation gives the endpoint-refined reciprocal
transport predicate.
-/
theorem operatorMonotoneDecreasingOnPositiveWithEndpoint_of_rep
    {g : ℝ → ℝ} (rep : PositiveRayOperatorMonotoneDecreasingRep g) :
    OperatorMonotoneDecreasingOnPositiveWithEndpoint.{u} g := by
  let h : ℝ → ℝ := positiveRayKuboAndoOfOperatorMonotoneDecreasingRep rep
  let hrep : PositiveRayKuboAndoRep h :=
    positiveRayKuboAndoRep_of_operatorMonotoneDecreasingRep rep
  refine
    { nonneg := rep.nonneg_on_Ioi
      reciprocal_witness := ⟨h,
        operatorMonotoneOnPositive_of_positiveRayKuboAndoRep hrep, ?_, ?_, ?_⟩ }
  · intro x hx
    have hxpos : 0 < x := by simpa using hx
    have hxinv_ne : x⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hxpos)
    simp [h, positiveRayKuboAndoOfOperatorMonotoneDecreasingRep, hxinv_ne]
  · simp [h, positiveRayKuboAndoOfOperatorMonotoneDecreasingRep]
  · let hclosed : OperatorMonotoneOnClosedPositive.{u} h :=
      operatorMonotoneOnClosedPositive_of_positiveRayKuboAndoRep hrep
    exact hclosed.right_continuous_at_zero

/--
A decreasing resolvent representation gives the theorem-facing
positive-ray operator monotone decreasing predicate.
-/
theorem operatorMonotoneDecreasingOnPositive_of_rep
    {g : ℝ → ℝ} (rep : PositiveRayOperatorMonotoneDecreasingRep g) :
    OperatorMonotoneDecreasingOnPositive.{u} g := by
  have hendpoint := operatorMonotoneDecreasingOnPositiveWithEndpoint_of_rep rep
  rcases hendpoint.reciprocal_witness with ⟨h, hh, h_formula, _h0, _hcont⟩
  exact
    { nonneg := hendpoint.nonneg
      reciprocal_witness := ⟨h, hh, h_formula⟩ }

/--
The endpoint-refined reciprocal predicate gives a decreasing resolvent
representation.
-/
theorem positiveRayOperatorMonotoneDecreasingRep_of_operatorMonotoneDecreasingOnPositiveWithEndpoint
    {g : ℝ → ℝ} (hg : OperatorMonotoneDecreasingOnPositiveWithEndpoint.{u} g) :
    Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) := by
  rcases hg.reciprocal_witness with ⟨h, hh, h_formula, h0, hcont⟩
  let hclosed : OperatorMonotoneOnClosedPositive.{u} h :=
    { to_open := hh
      right_continuous_at_zero := hcont }
  exact
    ⟨positiveRayOperatorMonotoneDecreasingRep_of_reciprocalKuboAndoRep
      h_formula (positiveRayKuboAndoRep_of_operatorMonotoneOnClosedPositive hclosed) h0⟩

/--
Producer-free equivalence between the endpoint-refined reciprocal predicate and
the decreasing resolvent representation.
-/
theorem operatorMonotoneDecreasingOnPositiveWithEndpoint_iff_nonempty_rep
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositiveWithEndpoint.{u} g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) := by
  constructor
  · exact
      positiveRayOperatorMonotoneDecreasingRep_of_operatorMonotoneDecreasingOnPositiveWithEndpoint
  · rintro ⟨rep⟩
    exact operatorMonotoneDecreasingOnPositiveWithEndpoint_of_rep rep

/-! ### Producer-free endpoint completion -/

/--
The canonical reciprocal witness acquires its endpoint value from the finite
nonnegative at-top limit of the decreasing function.  Values away from zero
agree with the reciprocal witness already carried by the open predicate.
-/
noncomputable def positiveRayOperatorMonotoneDecreasingEndpointReverseProducer :
    PositiveRayOperatorMonotoneDecreasingEndpointReverseProducer.{u} where
  endpointReciprocal_of_operatorMonotoneDecreasingOnPositive := by
    intro g hg
    rcases hg.reciprocal_witness with ⟨h, hh, h_formula⟩
    rcases positiveRayOperatorMonotoneDecreasingAtTopLimit hg with
      ⟨c, hc_nonneg, hc_limit⟩
    let h₀ : ℝ → ℝ :=
      positiveRayDecreasingReciprocalWitnessWithEndpoint g c
    have h₀_open : OperatorMonotoneOnPositive.{u} h₀ := by
      refine
        { to_unitInterval := operatorMonotoneOnUnitInterval_zeroTo
            ((operatorMonotoneOnUnitInterval_toZero hh.to_unitInterval).congr_on_Ioo ?_) }
      intro y hy
      let z : ℝ := unitToPositiveCayley y
      have hz : z ∈ Set.Ioi (0 : ℝ) := by
        simpa [z] using unitToPositiveCayley_mem_Ioi hy
      have hzpos : 0 < z := by simpa using hz
      have hzinv : z⁻¹ ∈ Set.Ioi (0 : ℝ) := by
        exact inv_pos.mpr hzpos
      change h₀ z = h z
      calc
        h₀ z = g z⁻¹ := by
          simp [h₀, positiveRayDecreasingReciprocalWitnessWithEndpoint,
            ne_of_gt hzpos]
        _ = h (z⁻¹)⁻¹ := h_formula z⁻¹ hzinv
        _ = h z := by rw [inv_inv]
    have h₀_formula :
        ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) → g x = h₀ x⁻¹ := by
      intro x hx
      simpa [h₀] using
        (positiveRayDecreasingReciprocalWitnessWithEndpoint_formula
          (g := g) (c := c) hx)
    have h₀_cont : Tendsto h₀ (𝓝[>] (0 : ℝ)) (𝓝 (h₀ 0)) := by
      simpa [h₀] using
        positiveRayDecreasingReciprocalWitnessWithEndpoint_tendsto_nhdsGT_of_tendsto_atTop
          hc_limit
    exact ⟨h₀, h₀_formula, by simpa [h₀] using hc_nonneg, h₀_open, h₀_cont⟩

/--
Hiai Theorem 2.7.11 on the decreasing positive ray.  The forward endpoint
continuity is the finite-measure dominated-convergence result for the
Kubo--Ando kernel; the reverse endpoint is the canonical reciprocal extension
above.
-/
theorem operatorMonotoneDecreasingOnPositive_iff_nonempty_rep
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositive.{u} g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) := by
  constructor
  · intro hg
    rcases
        positiveRayOperatorMonotoneDecreasingEndpointReverseProducer
          |>.endpointReciprocal_of_operatorMonotoneDecreasingOnPositive hg with
      ⟨h, h_formula, h0, hh, hcont⟩
    let hclosed : OperatorMonotoneOnClosedPositive.{u} h :=
      { to_open := hh
        right_continuous_at_zero := hcont }
    exact
      ⟨positiveRayOperatorMonotoneDecreasingRep_of_reciprocalKuboAndoRep
        h_formula
        (positiveRayKuboAndoRep_of_operatorMonotoneOnClosedPositive hclosed)
        h0⟩
  · rintro ⟨rep⟩
    exact operatorMonotoneDecreasingOnPositive_of_rep rep

/-- Producer-free compatibility name for the unconditional equivalence. -/
theorem operatorMonotoneDecreasingOnPositive_iff_nonempty_rep_of_producer
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositive.{u} g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  operatorMonotoneDecreasingOnPositive_iff_nonempty_rep

/-- Closed-positive compatibility name for the unconditional equivalence. -/
theorem operatorMonotoneDecreasingOnPositive_iff_nonempty_rep_of_closedPositiveProducer
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositive.{u} g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  operatorMonotoneDecreasingOnPositive_iff_nonempty_rep

/-- Endpoint compatibility name for the unconditional equivalence. -/
theorem operatorMonotoneDecreasingOnPositive_iff_nonempty_rep_of_endpointProducer
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositive.{u} g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  operatorMonotoneDecreasingOnPositive_iff_nonempty_rep

/-- Forward/reverse compatibility name for the unconditional equivalence. -/
theorem operatorMonotoneDecreasingOnPositive_iff_nonempty_rep_of_forwardReverseProducer
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositive.{u} g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  operatorMonotoneDecreasingOnPositive_iff_nonempty_rep

/-- Endpoint-reverse compatibility name for the unconditional equivalence. -/
theorem operatorMonotoneDecreasingOnPositive_iff_nonempty_rep_of_endpointReverseProducer
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositive.{u} g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  operatorMonotoneDecreasingOnPositive_iff_nonempty_rep

/-- Endpoint-data compatibility name for the unconditional equivalence. -/
theorem operatorMonotoneDecreasingOnPositive_iff_nonempty_rep_of_endpointDataProducer
    {g : ℝ → ℝ} :
    OperatorMonotoneDecreasingOnPositive.{u} g ↔
      Nonempty (PositiveRayOperatorMonotoneDecreasingRep g) :=
  operatorMonotoneDecreasingOnPositive_iff_nonempty_rep

end

end Quantum.TraceInequality.Loewner
