/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

-- The shift-approximation lemmas used here are the public ones of
-- `Quantum/TraceInequality/ShiftApproximation.lean`. The private declarations of this file
-- belong to the Hiai--Petz condition-conversion chain. The spectral/inner-product forms specific
-- to `jArg` are public without suffix; only the `neg` variants remain private helpers.

/-
Condition conversion layer for the Hiai-Petz quasi-entropy data-processing proof.

This file is split out of `HiaiPetz.MainEquivalence` so that the expensive
finite-dimensional CFC transport and shift-to-boundary arguments are compiled
behind a separate `.olean` boundary.
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
import Quantum.TraceInequality.HansenPedersen.MatrixFunctionalCalculus
import Quantum.TraceInequality.HiaiPetzTheorem.MatrixFunctionalCalculus
import Quantum.TraceInequality.HansenPedersen.LaterConsequences
import Quantum.TraceInequality.HansenPedersen.ShiftApproximation
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Quantum.TraceInequality.HiaiPetz.AmbientSubmodule.JOperatorInequalities
import Quantum.TraceInequality.HiaiPetz.Core.Basic

/-!
# Condition conversions for the Hiai–Petz quasi-entropy data-processing proof

This module is the conversion layer between the equivalent formulations of the
operator condition on a function `f : ℝ → ℝ` used in the Hiai–Petz quasi-entropy
data-processing proof.  It relates the matrix-only monotone condition to the
all-Hilbert-space operator-monotone and operator-concave conditions on `(0, ∞)`,
and transports these to the closed half-ray `[0, ∞)` through the shift
`t ↦ f (t + p)` with `p > 0`, together with the finite-dimensional continuous
functional calculus transport used to descend the all-Hilbert-space statements
back to matrices.

## Main definitions

* `ShiftedAllHOperatorConvexNeg`: for every `p > 0`, the negated shift
  `t ↦ -(f (t + p))` is all-Hilbert-space operator convex on `[0, ∞)`.
* `ShiftedInverseInequalityNeg`: for every `p > 0`, the negated shift
  `t ↦ -(f (t + p))` satisfies the inverse-inequality condition `ConditionII`.

## Main results

* `QuasiEntropyDataProcessing.matrixMonotoneCondition_of_allHOperatorMonotoneOnIoi`:
  descend the all-Hilbert-space operator-monotone condition on `(0, ∞)` to matrices.
* `QuasiEntropyDataProcessing.allHOperatorMonotoneOnIoi_iff_matrixMonotoneCondition`:
  the continuous-function bridge between all-Hilbert-space operator monotonicity
  and the matrix-only condition.
* `shiftedAllHOperatorMonotone_of_matrixMonotoneCondition` and
  `shiftedAllHOperatorConvexNeg_of_matrixMonotoneCondition`: produce the shifted
  operator-monotone and operator-convex conditions on `[0, ∞)`.
* `shiftedInverseInequalityNeg_of_shiftedAllHOperatorConvexNeg`: pass from the
  shifted operator convexity to the shifted inverse inequality.
* `matrixMonotoneCondition_of_allHOperatorConcave_Ioi`: descend the
  operator-concave formulation to the matrix-only condition.
-/

namespace HiaiPetz

open Matrix Unitary
open scoped MatrixOrder
open scoped ComplexOrder
open scoped CStarAlgebra
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

private theorem allHOperatorMonotone_iff_concave_Ioi.{v} (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    :
    HansenPedersen.AllHOperatorMonotoneOnInterval.{v} (Set.Ioi (0 : ℝ)) f ↔
      HansenPedersen.AllHOperatorConcaveOnInterval.{v} (Set.Ioi (0 : ℝ)) f := by
  have h11 := HansenPedersen.allHOperatorMonotone_equivalences_of_pos.{v} (f := f) hf hpos
  have hmono_iff_q :
      HansenPedersen.AllHOperatorMonotoneOnInterval.{v} (Set.Ioi (0 : ℝ)) f ↔
        HansenPedersen.AllHOperatorMonotoneOnInterval.{v} (Set.Ioi (0 : ℝ))
          (fun t : ℝ ↦ t / f t) := h11.1
  have hq_iff_conc :
      HansenPedersen.AllHOperatorMonotoneOnInterval.{v} (Set.Ioi (0 : ℝ))
          (fun t : ℝ ↦ t / f t) ↔
        HansenPedersen.AllHOperatorConcaveOnInterval.{v} (Set.Ioi (0 : ℝ)) f := h11.2.1
  constructor
  · intro hmono
    exact hq_iff_conc.mp (hmono_iff_q.mp hmono)
  · intro hconc
    exact hmono_iff_q.mpr (hq_iff_conc.mpr hconc)

private theorem allHOperatorMonotone_implies_convex_inv_Ioi.{v} (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hmono :
      HansenPedersen.AllHOperatorMonotoneOnInterval.{v} (Set.Ioi (0 : ℝ)) f) :
    HansenPedersen.AllHOperatorConvexOnInterval.{v} (Set.Ioi (0 : ℝ))
      (fun x : ℝ ↦ (f x)⁻¹) := by
  have h11 := HansenPedersen.allHOperatorMonotone_equivalences_of_pos.{v} (f := f) hf hpos
  simpa [one_div] using
    h11.2.2 ((allHOperatorMonotone_iff_concave_Ioi.{v} f hf hpos).mp hmono)

private theorem allHOperatorMonotone_implies_ratioMonotone_Ioi.{v} (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hmono :
      HansenPedersen.AllHOperatorMonotoneOnInterval.{v} (Set.Ioi (0 : ℝ)) f) :
    HansenPedersen.AllHOperatorMonotoneOnInterval.{v} (Set.Ioi (0 : ℝ))
      (fun t : ℝ ↦ t / f t) := by
  have h11 := HansenPedersen.allHOperatorMonotone_equivalences_of_pos.{v} (f := f) hf hpos
  exact h11.1.mp hmono

private theorem allHOperatorMonotone_implies_allHOperatorConvex_neg_Ioi.{v} (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    HansenPedersen.AllHOperatorMonotoneOnInterval.{v} (Set.Ioi (0 : ℝ)) f →
      HansenPedersen.AllHOperatorConvexOnInterval.{v} (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -f
        x) := by
  intro hmono
  exact
    (HansenPedersen.allHOperatorConcaveOnInterval_iff_convexOnInterval_neg.{v}
      (Set.Ioi (0 : ℝ)) f).1
    ((allHOperatorMonotone_iff_concave_Ioi.{v} f hf hpos).mp hmono)

/-- For positive-definite matrices `A` and `B`, the real spectrum of the argument
operator `jArg A B` is contained in the closed half-ray `[0, ∞)`. -/
theorem spectrum_jArg_subset_halfOpenRay_top
    {n : ℕ} {A B : Mₙ n}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    spectrum ℝ (jArg A B) ⊆ HansenPedersen.halfOpenRay ⊤ := by
  intro x hx
  exact ⟨le_of_lt (HiaiPetz.spectrum_jArg_subset_Ioi_of_posDef hA hB hx), by simp⟩

/-- Inner-product form of the shift-to-boundary limit: for self-adjoint `A` with
spectrum in `(0, ∞)` and `f` continuous on `(0, ∞)`, the real part of the inner
product `⟪X, cfc (f (· + p)) A X⟫` converges, as `p → 0⁺`, to the real part of
`⟪X, cfc f A X⟫`. -/
theorem shifted_cfc_inner_tendsto_Ioi
    {f : ℝ → ℝ} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    [Nontrivial (HansenPedersen.L K)]
    {A : HansenPedersen.L K}
    (hA : IsSelfAdjoint A)
    (hσA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (X : K) :
    Filter.Tendsto
      (fun p : ℝ =>
        Complex.re
          (inner ℂ X
            ((HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ f (x + p)) A) X)))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds
        (Complex.re
          (inner ℂ X
            ((HansenPedersen.cfcR (ℋ := K) f A) X)))) := by
  have hcfc :
      Filter.Tendsto
        (fun p : ℝ ↦ HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ f (x + p)) A)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (HansenPedersen.cfcR (ℋ := K) f A)) :=
    HansenPedersen.shifted_cfc_tendsto_Ioi (f := f) (K := K) hA hσA hf
  let evX : HansenPedersen.L K →L[ℂ] K :=
    ContinuousLinearMap.apply ℂ K X
  have hvec :
      Filter.Tendsto
        (fun p : ℝ =>
          evX (HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ f (x + p)) A))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (evX (HansenPedersen.cfcR (ℋ := K) f A))) := by
    simpa [evX] using evX.continuous.continuousAt.tendsto.comp hcfc
  let iX : K →L[ℂ] ℂ := innerSL ℂ X
  have hinner :
      Filter.Tendsto
        (fun p : ℝ =>
          iX (evX (HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ f (x + p)) A)))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (iX (evX (HansenPedersen.cfcR (ℋ := K) f A)))) := by
    simpa [iX] using iX.continuous.continuousAt.tendsto.comp hvec
  have hre :
      Filter.Tendsto
        (fun p : ℝ =>
          Complex.re
            (inner ℂ X
              (evX (HansenPedersen.cfcR (ℋ := K) (fun x : ℝ ↦ f (x + p)) A))))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds
          (Complex.re
            (inner ℂ X (evX (HansenPedersen.cfcR (ℋ := K) f A))))) := by
    simpa [iX] using
      Complex.continuous_re.continuousAt.tendsto.comp hinner
  simpa [evX] using hre

private theorem allHOperatorConvex_neg_shift_Ici_local.{v} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hconvNeg :
      HansenPedersen.AllHOperatorConvexOnInterval.{v} (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -f x))
    {p : ℝ} (hp0 : 0 < p) :
    HansenPedersen.AllHOperatorConvexOnInterval.{v}
      (HansenPedersen.halfOpenRay ⊤) (fun t : ℝ ↦ -(f (t + p))) := by
  have hconc :
      HansenPedersen.AllHOperatorConcaveOnInterval.{v} (Set.Ioi (0 : ℝ)) f :=
    (HansenPedersen.allHOperatorConcaveOnInterval_iff_convexOnInterval_neg.{v}
      (Set.Ioi (0 : ℝ)) f).2 hconvNeg
  have hconcShift :
      HansenPedersen.AllHOperatorConcaveOnInterval.{v}
        (HansenPedersen.halfOpenRay ⊤) (fun t : ℝ ↦ f (t + p)) :=
    HansenPedersen.allHOperatorConcave_shift_Ici.{v} (hf := hf) (hconc := hconc) hp0
  exact
    (HansenPedersen.allHOperatorConcaveOnInterval_iff_convexOnInterval_neg.{v}
      (HansenPedersen.halfOpenRay ⊤) (fun t : ℝ ↦ f (t + p))).1 hconcShift

/-- The property that, for every `p > 0`, the negated shifted function
`t ↦ -(f (t + p))` is all-Hilbert-space operator convex on the closed half-ray
`[0, ∞)`. -/
def ShiftedAllHOperatorConvexNeg (f : ℝ → ℝ) : Prop :=
  ∀ ⦃p : ℝ⦄, 0 < p →
    HansenPedersen.AllHOperatorConvexOnInterval.{0}
      (HansenPedersen.halfOpenRay ⊤) (fun t : ℝ ↦ -(f (t + p)))

private theorem allHOperatorConvex_neg_implies_shiftedAllHOperatorConvexNeg
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    HansenPedersen.AllHOperatorConvexOnInterval.{0} (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -f x) →
      ShiftedAllHOperatorConvexNeg f := by
  intro hconvNeg p hp0
  exact allHOperatorConvex_neg_shift_Ici_local.{0} (hf := hf) (hconvNeg := hconvNeg) hp0

private theorem allHOperatorConvex_neg_Ioi_of_matrixMonotoneCondition
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hI : QuasiEntropyDataProcessing.MatrixMonotoneCondition f) :
    HansenPedersen.AllHOperatorConvexOnInterval.{0} (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -f x) := by
  exact allHOperatorMonotone_implies_allHOperatorConvex_neg_Ioi.{0} f hf hpos
    (HansenPedersen.matrixMonotoneImpliesAllHOperatorMonotone
      (J := Set.Ioi (0 : ℝ)) (f := f) (convex_Ioi (0 : ℝ)) hf hI)

/-- If `f` is continuous and positive on `(0, ∞)`, then the matrix-monotone
condition on `f` implies `ShiftedAllHOperatorConvexNeg f`, i.e. all-Hilbert-space
operator convexity of every negated shift `t ↦ -(f (t + p))` on `[0, ∞)`. -/
theorem shiftedAllHOperatorConvexNeg_of_matrixMonotoneCondition
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    QuasiEntropyDataProcessing.MatrixMonotoneCondition f → ShiftedAllHOperatorConvexNeg f := by
  intro hI
  exact allHOperatorConvex_neg_implies_shiftedAllHOperatorConvexNeg f hf
    (allHOperatorConvex_neg_Ioi_of_matrixMonotoneCondition f hf hpos hI)

private theorem matrixMonotone_of_shiftedAllHOperatorConvexNeg
    (f : ℝ → ℝ)
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hshiftConvNeg : ShiftedAllHOperatorConvexNeg f)
    {p : ℝ} (hp : 0 < p) :
    HansenPedersen.ConvexityCharacterization.ConditionI.{0} (⊤ : WithTop ℝ)
      (fun t : ℝ ↦ -(f (t + p))) := by
  refine ⟨hshiftConvNeg hp, ?_⟩
  have hp_mem : p ∈ Set.Ioi (0 : ℝ) := hp
  have hp_pos : 0 < f p := hpos p hp_mem
  simpa using (neg_nonpos.mpr hp_pos.le)

private theorem shiftedInverseInequalityFixed_of_shiftedAllHOperatorConvexNeg
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hshiftConvNeg : ShiftedAllHOperatorConvexNeg f)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (HansenPedersen.L K) IsSelfAdjoint]
    [Nontrivial (HansenPedersen.L K)]
    {A C : HansenPedersen.L K}
    (hA : IsSelfAdjoint A)
    (hσA : spectrum ℝ A ⊆ HansenPedersen.halfOpenRay ⊤)
    {p : ℝ} (hp : 0 < p)
    (hC : ‖C‖ ≤ 1) :
    HansenPedersen.cfcR (ℋ := K) (fun t : ℝ ↦ -(f (t + p))) (star C * A * C) ≤
      star C * HansenPedersen.cfcR (ℋ := K) (fun t : ℝ ↦ -(f (t + p))) A * C := by
  have hfshift :
      ContinuousOn (fun t : ℝ ↦ -(f (t + p))) (HansenPedersen.halfOpenRay ⊤) :=
    (HansenPedersen.continuousOn_shift_Ici (f := f) hf hp).neg
  have hIshift :
      HansenPedersen.ConvexityCharacterization.ConditionI.{0} (⊤ : WithTop ℝ)
        (fun t : ℝ ↦ -(f (t + p))) :=
    matrixMonotone_of_shiftedAllHOperatorConvexNeg (f := f) (hpos := hpos) hshiftConvNeg hp
  have htop : (((0 : ℝ) : WithTop ℝ) < (⊤ : WithTop ℝ)) :=
    WithTop.coe_lt_top (a := (0 : ℝ))
  exact HansenPedersen.ConvexityCharacterization.conditionI_implies_conditionII_fixed
    (f := fun t : ℝ ↦ -(f (t + p))) hfshift htop hIshift hA hσA hC

/-- The property that, for every `p > 0`, the negated shifted function
`t ↦ -(f (t + p))` satisfies the inverse-inequality condition
`ConvexityCharacterization.ConditionII` with endpoint `⊤`. -/
def ShiftedInverseInequalityNeg (f : ℝ → ℝ) : Prop :=
  ∀ ⦃p : ℝ⦄, 0 < p →
    HansenPedersen.ConvexityCharacterization.ConditionII.{0} (⊤ : WithTop ℝ)
      (fun t : ℝ ↦ -(f (t + p)))

/-- Under continuity and positivity of `f` on `(0, ∞)`,
`ShiftedAllHOperatorConvexNeg f` implies `ShiftedInverseInequalityNeg f`; that is,
shifted operator convexity of the negated shifts yields the corresponding shifted
inverse inequalities. -/
theorem shiftedInverseInequalityNeg_of_shiftedAllHOperatorConvexNeg
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    ShiftedAllHOperatorConvexNeg f → ShiftedInverseInequalityNeg f := by
  intro hshiftConvNeg p hp K _ _ _ _ _ A C hA hσA hC
  exact shiftedInverseInequalityFixed_of_shiftedAllHOperatorConvexNeg
    (f := f) (hf := hf) (hpos := hpos) hshiftConvNeg
    (K := K) (A := A) (C := C) hA hσA hp hC


/-- If `f` is continuous on `(0, ∞)` and satisfies the matrix-monotone condition,
then for every `p > 0` the shifted function `t ↦ f (t + p)` is all-Hilbert-space
operator monotone on the closed half-ray `[0, ∞)`. -/
theorem shiftedAllHOperatorMonotone_of_matrixMonotoneCondition
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hI : QuasiEntropyDataProcessing.MatrixMonotoneCondition f) :
    ∀ ⦃p : ℝ⦄, 0 < p →
      HansenPedersen.AllHOperatorMonotoneOnInterval.{0}
        (HansenPedersen.halfOpenRay ⊤) (fun t : ℝ ↦ f (t + p)) := by
  intro p hp
  exact HansenPedersen.allHOperatorMonotone_shift_Ici.{0} (hf := hf)
    (hmono :=
      HiaiPetz.MatrixFunctionalCalculus.allHOperatorMonotoneOnIoi_of_matrixMonotoneCondition hf hI)
    hp

/-- If `f` is continuous and positive on `(0, ∞)` and is all-Hilbert-space
operator concave there, then `f` satisfies the matrix-monotone condition.  This
combines the operator monotone/concave equivalence with the descent to matrices. -/
theorem matrixMonotoneCondition_of_allHOperatorConcave_Ioi
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x)
    (hconc :
      HansenPedersen.AllHOperatorConcaveOnInterval.{0} (Set.Ioi (0 : ℝ)) f) :
    QuasiEntropyDataProcessing.MatrixMonotoneCondition f := by
  exact HiaiPetz.MatrixFunctionalCalculus.matrixMonotoneCondition_of_allHOperatorMonotoneOnIoi
    ((allHOperatorMonotone_iff_concave_Ioi.{0} f hf hpos).2 hconc)


end MatrixScopedInstances

end HiaiPetz
