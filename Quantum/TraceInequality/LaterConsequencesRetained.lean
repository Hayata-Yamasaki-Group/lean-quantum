/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

-- The shift-approximation lemmas are public in `Quantum/TraceInequality/ShiftApproximation.lean`.
-- The private declarations of this file belong to three proof steps:
-- (1) the midpoint scalar inequality of Lemma 5.1.10,
-- (2) the CFC limit of the shifted reciprocal in Lemma 5.1.10
--     (one_div_add_t_tendsto_one_div etc.),
-- (3) the condition-conversion route of Corollary 5.1.11 (conditionV/VI bridges, reversal of the reciprocal order).
-- They are specific to this proof route and are kept private.

import Quantum.TraceInequality.HiaiPetzTheorem.Core
import Quantum.TraceInequality.CoreRetained
import Quantum.TraceInequality.HansenPedersen.FiniteDimensional.Surface
import Quantum.TraceInequality.HiaiPetzTheorem.FiniteDimensional.Surface
import Quantum.TraceInequality.HansenPedersen.MonotoneConvexEquivalence.Basic
import Quantum.TraceInequality.HansenPedersen.MonotoneConvexEquivalence.VI2Instances
import Quantum.TraceInequality.HansenPedersen.MonotoneConvexEquivalence.ConditionVIToII
import Quantum.TraceInequality.HansenPedersen.MonotoneConvexEquivalence.Surface
import Quantum.TraceInequality.HansenPedersen.ShiftApproximation
import Quantum.TraceInequality.HansenPedersen.LaterConsequences
import Quantum.TraceInequality.LiebAndo.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheoremRetained

/-!
# Later consequences of the Hansen--Pedersen route

This file collects the downstream Hiai--Yanagi Chapter 5.1 consequences that
depend on the shared interval operator-monotonicity and operator-convexity
predicates and the monotone--convex equivalence layer.
Source: the Hansen--Pedersen development of these interval predicates.
It contains the reciprocal-function Lemma 5.1.10, the
positive-function equivalences of Corollary 5.1.11, and the proved examples
from Example 5.1.12.  The unproved aggregate examples and Furuta statement are
isolated under `HansenPedersen.Frontier`.

## Main results

* `one_div_operatorConvex_and_neg_one_div_operatorMonotone_Ioi`: Lemma 5.1.10
  on `(0,∞)`.
* `allHOperatorMonotone_equivalences_of_pos`: Corollary 5.1.11 for positive
  functions on `(0,∞)`.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021,
  Lemma 5.1.10, Corollary 5.1.11, Example 5.1.12, and Theorem 5.1.19.
-/

namespace HansenPedersen

universe u

open CFC MeasureTheory
open scoped Topology

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]

section NormalCFC510Plus

/- Instance caches: same pattern as
`CompressionInequality/RatioMonotoneToProjection.lean` — the real-scalar action
on `L ℋ` and its order/topology compatibility classes each trigger a deep,
non-cached `synthInstance` derivation re-run at many use sites of the CFC
arguments below. Section-level reducible local instances turn each search into
a head-match. -/

attribute [local instance] instModuleRealLHScoped

attribute [local instance] instPosSMulMonoRealLHScoped

attribute [local instance] instSMulPosMonoRealLHScoped

attribute [local instance] instContinuousSMulRealLHScoped

attribute [local instance] instStarModuleRealLHScoped

attribute [local instance] instAlgebraRealLHScoped

attribute [local instance] instSMulRealLHScoped

attribute [local instance] instMulActionRealLHScoped

attribute [local instance] instSMulZeroClassRealLHScoped

attribute [local instance] instAddRightMonoLHScoped

attribute [local instance] instAddLeftMonoLHScoped

attribute [local instance] instAddRightReflectLELHScoped

attribute [local instance] instStarMulLHScoped

attribute [local instance] instMonoidLHScoped

omit [Nontrivial (L ℋ)] in
/-- Monotonicity half of **Lemma 5.1.10**.
Source: Hiai–Yanagi, Lemma 5.1.10. -/
theorem neg_one_div_operatorMonotoneOnInterval_Ioi :
    OperatorMonotoneOnInterval (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -(1 / x)) := by
  intro A B hA hB hAs hBs hAB
  have hanti :
      cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) B ≤
        cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) A :=
    (LownerHeinzTheorem.one_div_operatorAntitoneOn_Ioi (ℋ := ℋ)) hB hA hAB hBs hAs
  have hneg :
      -(cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) A) ≤
        -(cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) B) :=
    neg_le_neg hanti
  simpa [cfcR, LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR, cfc_neg] using hneg

/-- **Lemma 5.1.10** as a single conjunction.
Source: Hiai–Yanagi, Lemma 5.1.10. -/
theorem one_div_operatorConvex_and_neg_one_div_operatorMonotone_Ioi :
    OperatorConvexOnInterval (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x) ∧
    OperatorMonotoneOnInterval (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -(1 / x)) := by
  exact ⟨one_div_operatorConvexOnInterval_Ioi (ℋ := ℋ),
    neg_one_div_operatorMonotoneOnInterval_Ioi (ℋ := ℋ)⟩

private lemma one_div_add_t_tendsto_one_div {A : L ℋ} (hA : IsSelfAdjoint A)
    (As : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)) :
    Filter.Tendsto
      (fun p : ℝ => cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / (x + p)) A)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) A)) := by
  /- Step 1: Put A and small shifts in one compact window away from zero. -/
  rcases (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := A) (ha := hA)).2
      (by intro x hx; exact As hx) with ⟨α, hαpos, hαA⟩
  let β : ℝ := ‖A‖ + 1
  let Ap : ℝ → L ℋ := fun p => A + (p : ℝ) • (1 : L ℋ)
  have hAupper : A ≤ (β : ℂ) • (1 : L ℋ) := by
    have hAupper' : A ≤ (‖A‖ : ℝ) • (1 : L ℋ) := by
      simpa [Algebra.algebraMap_eq_smul_one] using hA.le_algebraMap_norm_self
    calc
      A ≤ (‖A‖ : ℝ) • (1 : L ℋ) := hAupper'
      _ ≤ (β : ℝ) • (1 : L ℋ) := by
        have hβ : ‖A‖ ≤ β := by
          dsimp [β]
          linarith
        dsimp [β]
        exact smul_le_smul_of_nonneg_right hβ
          (zero_le_one : (0 : L ℋ) ≤ (1 : L ℋ))
  have hσA_Icc : spectrum ℝ A ⊆ Set.Icc α β := by
    exact HansenPedersen.spectrum_subset_Icc_of_order_bounds_clm
      (K := ℋ) hA hαA hAupper
  have hsmall :
      Set.Ioi (0 : ℝ) ∩ Set.Iio 1 ∈ 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ) := by
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ?_
    refine ⟨Set.Iio (1 : ℝ), Iio_mem_nhds zero_lt_one, ?_⟩
    intro x hx
    exact ⟨hx.2, hx.1⟩
  /- Step 2: Show the shifted operator path A + p * 1 converges back to A. -/
  have hAp_tendsto : Filter.Tendsto Ap (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds A) := by
    have hptendsto :
        Filter.Tendsto (fun p : ℝ => p) (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
          (nhds 0) :=
      nhdsWithin_le_nhds
    simpa [Ap] using tendsto_const_nhds.add (hptendsto.smul_const (1 : L ℋ))
  /- Step 3: Apply CFC continuity on the fixed compact window for the reciprocal function. -/
  have hcf_tendsto :
      Filter.Tendsto
        (fun p : ℝ => cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) (Ap p))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) A)) := by
    simpa [cfcR, Ap] using
      Filter.Tendsto.cfc (A := L ℋ) (hs := isCompact_Icc) (f := fun x : ℝ ↦ 1 / x) hAp_tendsto
        (by
          refine Filter.mem_of_superset hsmall ?_
          intro p hp
          rcases hp with ⟨hp0, hp1⟩
          have hAp_sa : IsSelfAdjoint (Ap p) := by
            have hscalar : IsSelfAdjoint ((p : ℝ) • (1 : L ℋ)) := by
              simpa [Algebra.algebraMap_eq_smul_one] using
                (IsSelfAdjoint.algebraMap (A := L ℋ) (r := p) (hr := IsSelfAdjoint.all (p : ℝ)))
            exact hA.add hscalar
          have hlow : (α : ℂ) • (1 : L ℋ) ≤ Ap p := by
            have hp_nonneg : (0 : L ℋ) ≤ (p : ℝ) • (1 : L ℋ) := by
              exact smul_nonneg hp0.le (zero_le_one : (0 : L ℋ) ≤ (1 : L ℋ))
            simpa [Ap] using le_add_of_nonneg_right hp_nonneg |> fun h => le_trans hαA h
          have hupp : Ap p ≤ (β : ℂ) • (1 : L ℋ) := by
            have hpupper : (p : ℝ) • (1 : L ℋ) ≤ (1 : ℝ) • (1 : L ℋ) := by
              exact smul_le_smul_of_nonneg_right hp1.le
                (zero_le_one : (0 : L ℋ) ≤ (1 : L ℋ))
            calc
              Ap p = A + (p : ℝ) • (1 : L ℋ) := rfl
              _ ≤ (‖A‖ : ℝ) • (1 : L ℋ) + (1 : ℝ) • (1 : L ℋ) := by
                    have hAupper' : A ≤ (‖A‖ : ℝ) • (1 : L ℋ) := by
                      simpa [Algebra.algebraMap_eq_smul_one] using hA.le_algebraMap_norm_self
                    exact add_le_add hAupper' hpupper
              _ = (β : ℝ) • (1 : L ℋ) := by simp [β, add_smul]
          exact HansenPedersen.spectrum_subset_Icc_of_order_bounds_clm
            (K := ℋ) hAp_sa hlow hupp)
        (by
          filter_upwards [self_mem_nhdsWithin] with p hp
          have hscalar : IsSelfAdjoint ((p : ℝ) • (1 : L ℋ)) := by
            simpa [Algebra.algebraMap_eq_smul_one] using
              (IsSelfAdjoint.algebraMap (A := L ℋ) (r := p) (hr := IsSelfAdjoint.all (p : ℝ)))
          exact hA.add hscalar)
        hσA_Icc
        hA
        (by
          intro x hx
          simpa [one_div] using
            (continuousAt_inv₀ (ne_of_gt (lt_of_lt_of_le hαpos hx.1))).continuousWithinAt)
  /- Step 4: Identify the shifted reciprocal as composing reciprocal CFC with A + p * 1. -/
  have hrepr :
      ∀ᶠ p : ℝ in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / (x + p)) A =
          cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) (Ap p) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    have hcont_shift : ContinuousOn (fun x : ℝ ↦ x + p) (spectrum ℝ A) :=
      continuousOn_id.add continuousOn_const
    have hcont_inv :
        ContinuousOn (fun x : ℝ ↦ 1 / x) ((fun x : ℝ ↦ x + p) '' spectrum ℝ A) := by
      intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      have hy0 : 0 < y := by
        simpa [Set.mem_Ioi] using As hy
      have hyp : 0 < y + p := add_pos hy0 hp
      simpa [one_div] using (continuousAt_inv₀ (ne_of_gt hyp)).continuousWithinAt
    have hadd :
        cfcR (ℋ := ℋ) (fun x : ℝ ↦ x + p) A = Ap p := by
      have hfun : (fun x : ℝ ↦ x + p) = fun x : ℝ ↦ p + x := by
        funext x
        ring
      have hadd' :
          cfcR (ℋ := ℋ) (fun x : ℝ ↦ p + x) A = (p : ℝ) • (1 : L ℋ) + A := by
        simpa [cfcR, cfc_id' (R := ℝ) (a := A) (ha := hA), Algebra.algebraMap_eq_smul_one,
          add_comm, add_left_comm, add_assoc] using
        (cfc_add_const (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint)
          (r := p) (f := fun x : ℝ ↦ x) (a := A)
          (hf := continuousOn_id) (ha := hA))
      rw [hfun, hadd']
      simp [Ap, add_comm]
    calc
      cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / (x + p)) A
          = cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x)
              (cfcR (ℋ := ℋ) (fun x : ℝ ↦ x + p) A) := by
              simpa [cfcR, one_div] using
              (cfc_comp' (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint)
                (g := fun x : ℝ ↦ 1 / x) (f := fun x : ℝ ↦ x + p) (a := A)
                (hg := hcont_inv) (hf := hcont_shift) (ha := hA))
      _ = cfcR (ℋ := ℋ) (fun x : ℝ ↦ 1 / x) (Ap p) := by rw [hadd]
  /- Step 5: Replace the convergent shifted-CFC path by the eventually equal reciprocal path. -/
  refine hcf_tendsto.congr' ?_
  filter_upwards [hrepr] with p hp
  exact hp.symm

/-- Book-statement convexity for **Lemma 5.1.10**, packaged separately from the short proof used by
`one_div_operatorConvexOnInterval_Ioi`. The midpoint step is recorded separately by
`one_div_operatorMidpointConvexOnInterval_Ioi_book`.
Source: Hiai–Yanagi, Lemma 5.1.10. -/
theorem one_div_operatorConvexOnInterval_Ioi_book :
    OperatorConvexOnInterval (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x) := by
  let F : ℝ → ℝ → ℝ := fun p x => 1 / (x + p)
  refine operatorConvexOn_of_tendsto_Ioi (ℋ := ℋ) (F := F)
    (f := fun x : ℝ ↦ 1 / x) ?_ ?_
  · intro A hA As
    simpa [F] using one_div_add_t_tendsto_one_div (ℋ := ℋ) hA As
  · filter_upwards [self_mem_nhdsWithin] with p hp
    intro A B t hA hB ht0 ht1 As Bs
    exact (LownerHeinzTheorem.one_div_add_t_operatorConvexOn_Ici (ℋ := ℋ) p hp)
      hA hB ht0 ht1
      (by
        intro x hx
        exact le_of_lt (by simpa [Set.mem_Ioi] using As hx))
      (by
        intro x hx
        exact le_of_lt (by simpa [Set.mem_Ioi] using Bs hx))

/-- Book-facing auxiliary theorem for **Lemma 5.1.10**. It has the same conjunction statement as
`one_div_operatorConvex_and_neg_one_div_operatorMonotone_Ioi`, with a separate proof
following the midpoint argument in the source.
Source: Hiai–Yanagi, Lemma 5.1.10. -/
theorem one_div_operatorConvex_and_neg_one_div_operatorMonotone_Ioi_book :
    OperatorConvexOnInterval (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x) ∧
    OperatorMonotoneOnInterval (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -(1 / x)) := by
  exact ⟨one_div_operatorConvexOnInterval_Ioi_book (ℋ := ℋ),
    neg_one_div_operatorMonotoneOnInterval_Ioi_book (ℋ := ℋ)⟩

omit [Nontrivial (L ℋ)] in
/-- Source: Hiai–Yanagi, Example 5.1.12(3). -/
theorem rpow_operatorMonotoneOnInterval_Ici {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    OperatorMonotoneOnInterval (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x ^ p) := by
  exact operatorMonotoneOnInterval_of_operatorMonotoneOn_Ici (ℋ := ℋ)
    (LownerHeinzTheorem.power_Icc_zero_one_operatorMonotoneOn_Ici (ℋ := ℋ) p hp)

/-- Source: Hiai–Yanagi, Example 5.1.12(3). -/
theorem rpow_operatorConcaveOnInterval_Ici {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    OperatorConcaveOnInterval (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x ^ p) := by
  simpa [OperatorConcaveOnInterval] using
    (LownerHeinzTheorem.power_Icc_zero_one_operatorConcaveOn_Ici (ℋ := ℋ) p hp)

/-- Source: Hiai–Yanagi, Example 5.1.12(4). -/
theorem rpow_operatorConvexOnInterval_Ici {p : ℝ} (hp : p ∈ Set.Icc (1 : ℝ) 2) :
    OperatorConvexOnInterval (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x ^ p) := by
  simpa [OperatorConvexOnInterval] using
    (LownerHeinzTheorem.power_Icc_one_two_operatorConvexOn_Ici (ℋ := ℋ) p hp)

/-- Source: Hiai–Yanagi, Example 5.1.12(6). -/
theorem log_operatorMonotoneOnInterval_Ioi :
    OperatorMonotoneOnInterval (ℋ := ℋ) (Set.Ioi (0 : ℝ)) Real.log := by
  exact operatorMonotoneOnInterval_of_operatorMonotoneOn_Ioi (ℋ := ℋ)
    (LownerHeinzTheorem.log_operatorMonotoneOn_Ioi (ℋ := ℋ))

/-- Source: Hiai–Yanagi, Example 5.1.12(6). -/
theorem log_operatorConcaveOnInterval_Ioi :
    OperatorConcaveOnInterval (ℋ := ℋ) (Set.Ioi (0 : ℝ)) Real.log := by
  simpa [OperatorConcaveOnInterval] using
    (LownerHeinzTheorem.log_operatorConcaveOn_Ioi (ℋ := ℋ))

/-- The current repo proves `t log t` on `(0,∞)`; the exact `[0,∞)` extension in the book
is kept in `HansenPedersen.Frontier.OperatorMonotoneConvexExamplesStatement`.
Source: Hiai–Yanagi, Example 5.1.12(7). -/
theorem mul_log_operatorConvexOnInterval_Ioi :
    OperatorConvexOnInterval (ℋ := ℋ) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ x * Real.log x) := by
  simpa [OperatorConvexOnInterval] using
    (LownerHeinzTheorem.mul_log_operatorConvexOn_Ioi (ℋ := ℋ))

end NormalCFC510Plus

end HansenPedersen
