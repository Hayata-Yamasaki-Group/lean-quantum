/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.HalfLine.KuboAndo

/-!
# Loewner-native entry condition for the Hiai--Petz route

This file keeps the entry to the Hiai--Petz application on the Loewner side:
an endpoint extension which is operator monotone on the closed positive
half-line.  The compatibility bridge from the Hiai--Petz finite-matrix
`ConditionI` is intentionally not included here.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

universe u

open Set Filter
open scoped Topology

noncomputable section

/-- Extend a positive-ray function by prescribing its endpoint value at `0`. -/
def positiveRayEndpointExtension (f : ℝ → ℝ) (c : ℝ) : ℝ → ℝ :=
  fun x => if x = 0 then c else f x

/-- The endpoint extension agrees with the original function on the open positive ray. -/
theorem positiveRayEndpointExtension_eq_of_pos {f : ℝ → ℝ} {c x : ℝ}
    (hx : x ∈ Set.Ioi (0 : ℝ)) :
    positiveRayEndpointExtension f c x = f x := by
  have hxne : x ≠ 0 := ne_of_gt (by simpa using hx)
  simp [positiveRayEndpointExtension, hxne]

/-- The endpoint extension has the prescribed value at `0`. -/
theorem positiveRayEndpointExtension_zero {f : ℝ → ℝ} {c : ℝ} :
    positiveRayEndpointExtension f c 0 = c := by
  simp [positiveRayEndpointExtension]

/-- The Cayley map from `(0,∞)` to `(-1,1)` is monotone. -/
theorem positiveToUnitCayley_le_positiveToUnitCayley {x y : ℝ}
    (hx : x ∈ Set.Ioi (0 : ℝ)) (hy : y ∈ Set.Ioi (0 : ℝ)) (hxy : x ≤ y) :
    positiveToUnitCayley x ≤ positiveToUnitCayley y := by
  have hx0 : 0 < x := by simpa using hx
  have hy0 : 0 < y := by simpa using hy
  have hxden : 0 < x + 1 := by linarith
  have hyden : 0 < y + 1 := by linarith
  unfold positiveToUnitCayley
  rw [div_le_div_iff₀ hxden hyden]
  nlinarith

/-- Positive-ray operator monotonicity implies ordinary scalar monotonicity on `(0,∞)`. -/
theorem operatorMonotoneOnPositive_monotoneOn_Ioi {f : ℝ → ℝ}
    (hf : OperatorMonotoneOnPositive.{u} f) :
    MonotoneOn f (Set.Ioi (0 : ℝ)) := by
  have hfinite :
      UnitIntervalFiniteMatrixMonotone.{0} (positiveCayleyPullback f) :=
    finiteMatrixMonotone_of_operatorMonotoneOnUnitInterval
      (operatorMonotoneOnUnitInterval_toZero hf.to_unitInterval)
  have hpullMono :
      MonotoneOn (positiveCayleyPullback f) (Set.Ioo (-1 : ℝ) 1) :=
    scalarMonotoneOn_Ioo_of_finiteMatrixMonotone
      (unitIntervalMatrixMonotone_of_finiteMatrixMonotone hfinite)
  intro x hx y hy hxy
  have hxI : positiveToUnitCayley x ∈ Set.Ioo (-1 : ℝ) 1 :=
    positiveToUnitCayley_mem_Ioo hx
  have hyI : positiveToUnitCayley y ∈ Set.Ioo (-1 : ℝ) 1 :=
    positiveToUnitCayley_mem_Ioo hy
  have hxyI : positiveToUnitCayley x ≤ positiveToUnitCayley y :=
    positiveToUnitCayley_le_positiveToUnitCayley hx hy hxy
  have hpull_le :
      positiveCayleyPullback f (positiveToUnitCayley x) ≤
        positiveCayleyPullback f (positiveToUnitCayley y) :=
    hpullMono hxI hyI hxyI
  simpa [positiveCayleyPullback, unitToPositiveCayley_positiveToUnitCayley hx,
    unitToPositiveCayley_positiveToUnitCayley hy] using hpull_le

/-- Endpoint value obtained as the infimum over the small positive interval `(0,1)`. -/
def positiveRayEndpointLimitValue (f : ℝ → ℝ) : ℝ :=
  sInf (f '' Set.Ioo (0 : ℝ) 1)

/--
If a positive-ray operator monotone function is bounded below by `0` on the
open positive ray, then it has a finite right limit at `0`.
-/
theorem operatorMonotoneOnPositive_tendsto_endpoint_of_nonneg {f : ℝ → ℝ}
    (hf : OperatorMonotoneOnPositive.{u} f)
    (hnonneg : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 ≤ f x) :
    ∃ c : ℝ, Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  refine ⟨positiveRayEndpointLimitValue f, ?_⟩
  have hmono : MonotoneOn f (Set.Ioi (0 : ℝ)) :=
    operatorMonotoneOnPositive_monotoneOn_Ioi hf
  have hmono_right : MonotoneOn f (Set.Ioo (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact hmono (by exact hx.1) (by exact hy.1) hxy
  have hnonempty : (Set.Ioo (0 : ℝ) 1).Nonempty :=
    Set.nonempty_Ioo.mpr zero_lt_one
  have hbdd : BddBelow (f '' Set.Ioo (0 : ℝ) 1) := by
    refine ⟨0, ?_⟩
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact hnonneg (by exact hx.1)
  simpa [positiveRayEndpointLimitValue] using
    MonotoneOn.tendsto_nhdsWithin_Ioo_right hnonempty hmono_right hbdd

/--
Positive-ray operator monotonicity is invariant under changing values off the
open positive ray.
-/
theorem operatorMonotoneOnPositive_congr_on_Ioi {f g : ℝ → ℝ}
    (hf : OperatorMonotoneOnPositive.{u} f)
    (hfg : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → g x = f x) :
    OperatorMonotoneOnPositive.{u} g where
  to_unitInterval := by
    refine ⟨?_⟩
    intro A _ _ _ a ha b hb hab
    have hzero : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
    have heqPull :
        ∀ y : ℝ, y ∈ Set.Ioo (-1 : ℝ) 1 →
          positiveCayleyPullback g y = positiveCayleyPullback f y := by
      intro y hy
      exact hfg (unitToPositiveCayley_mem_Ioi hy)
    have hca :
        cfcₙ (fun x : ℝ => positiveCayleyPullback g x - positiveCayleyPullback g 0) a =
          cfcₙ (fun x : ℝ => positiveCayleyPullback f x - positiveCayleyPullback f 0) a := by
      apply cfcₙ_congr
      intro x hx
      have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := ha.2 hx
      change positiveCayleyPullback g x - positiveCayleyPullback g 0 =
        positiveCayleyPullback f x - positiveCayleyPullback f 0
      rw [heqPull x hxI, heqPull 0 hzero]
    have hcb :
        cfcₙ (fun x : ℝ => positiveCayleyPullback g x - positiveCayleyPullback g 0) b =
          cfcₙ (fun x : ℝ => positiveCayleyPullback f x - positiveCayleyPullback f 0) b := by
      apply cfcₙ_congr
      intro x hx
      have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := hb.2 hx
      change positiveCayleyPullback g x - positiveCayleyPullback g 0 =
        positiveCayleyPullback f x - positiveCayleyPullback f 0
      rw [heqPull x hxI, heqPull 0 hzero]
    change cfcₙ (fun x : ℝ => positiveCayleyPullback g x - positiveCayleyPullback g 0) a ≤
      cfcₙ (fun x : ℝ => positiveCayleyPullback g x - positiveCayleyPullback g 0) b
    rw [hca, hcb]
    exact hf.to_unitInterval.cfc_monotone ha hb hab
/--
If an endpoint value is supplied as the right limit, the corresponding endpoint
extension is operator monotone on the closed positive half-line.
-/
theorem closedPositive_extension_of_operatorMonotoneOnPositive_tendsto_endpoint
    {f : ℝ → ℝ} {c : ℝ}
    (hf : OperatorMonotoneOnPositive.{u} f)
    (hc : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    ∃ f₀ : ℝ → ℝ,
      (∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → f₀ x = f x) ∧
        OperatorMonotoneOnClosedPositive.{u} f₀ := by
  let f₀ : ℝ → ℝ := positiveRayEndpointExtension f c
  have hagree : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → f₀ x = f x := by
    intro x hx
    exact positiveRayEndpointExtension_eq_of_pos hx
  have hopen : OperatorMonotoneOnPositive.{u} f₀ :=
    operatorMonotoneOnPositive_congr_on_Ioi hf hagree
  have hlim : Tendsto f₀ (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    have heq : f₀ =ᶠ[𝓝[>] (0 : ℝ)] f := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact positiveRayEndpointExtension_eq_of_pos hx
    exact hc.congr' heq.symm
  have hlim0 : Tendsto f₀ (𝓝[>] (0 : ℝ)) (𝓝 (f₀ 0)) := by
    simpa [f₀, positiveRayEndpointExtension_zero] using hlim
  exact ⟨f₀, hagree, { to_open := hopen, right_continuous_at_zero := hlim0 }⟩

/--
Nonnegative positive-ray operator monotonicity supplies the closed-positive
endpoint extension required by the Kubo--Ando theorem.
-/
theorem closedPositive_extension_of_operatorMonotoneOnPositive_nonneg
    {f : ℝ → ℝ}
    (hf : OperatorMonotoneOnPositive.{u} f)
    (hnonneg : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → 0 ≤ f x) :
    ∃ f₀ : ℝ → ℝ,
      (∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → f₀ x = f x) ∧
        OperatorMonotoneOnClosedPositive.{u} f₀ := by
  rcases operatorMonotoneOnPositive_tendsto_endpoint_of_nonneg hf hnonneg with ⟨c, hc⟩
  exact closedPositive_extension_of_operatorMonotoneOnPositive_tendsto_endpoint hf hc

/--
Loewner-native condition (i) for the Hiai--Petz route.

The function `f` is used only on `(0, ∞)`.  The endpoint value is supplied by an
extension `f₀` which agrees with `f` on the positive ray and is operator
monotone on the closed positive half-line.
-/
def LoewnerConditionI (f : ℝ → ℝ) : Prop :=
  ∃ f₀ : ℝ → ℝ,
    (∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → f₀ x = f x) ∧
      OperatorMonotoneOnClosedPositive.{u} f₀

/--
The Loewner-native Hiai--Petz entry condition is exactly what is needed to
apply the existing positive-ray Kubo--Ando representation theorem.
-/
theorem loewnerConditionI_to_positiveRayKuboAndoRep
    {f : ℝ → ℝ} (hf : LoewnerConditionI.{u} f) :
    ∃ f₀ : ℝ → ℝ,
      (∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → f₀ x = f x) ∧
        Nonempty (PositiveRayKuboAndoRep f₀) := by
  rcases hf with ⟨f₀, hagree, hclosed⟩
  exact
    ⟨f₀, hagree,
      ⟨positiveRayKuboAndoRep_of_operatorMonotoneOnClosedPositive hclosed⟩⟩

/--
An explicit endpoint-extension form of the Loewner entry bridge.

This is the same mathematical content as `loewnerConditionI_to_positiveRayKuboAndoRep`,
but the endpoint extension package is displayed directly in the statement.
-/
theorem positiveRayKuboAndoRep_of_closedPositive_extension
    {f : ℝ → ℝ}
    (hf : ∃ f₀ : ℝ → ℝ,
      (∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → f₀ x = f x) ∧
        OperatorMonotoneOnClosedPositive.{u} f₀) :
    ∃ f₀ : ℝ → ℝ,
      (∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → f₀ x = f x) ∧
        Nonempty (PositiveRayKuboAndoRep f₀) := by
  rcases hf with ⟨f₀, hagree, hclosed⟩
  exact
    ⟨f₀, hagree,
      ⟨positiveRayKuboAndoRep_of_operatorMonotoneOnClosedPositive hclosed⟩⟩

end

end Quantum.TraceInequality.Loewner.HiaiPetz
