import Quantum.TraceInequality.Loewner.Statement
import Quantum.TraceInequality.Loewner.Koranyi.DyadicPointFamily
import Quantum.TraceInequality.Loewner.Koranyi.RawWitness

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set

noncomputable section

open scoped ComplexOrder
open scoped MatrixOrder

/--
Raw finite-dimensional witness at the dyadic stage `m`.

This is the theorem-34 route before any weak-limit or support-elimination step:
we instantiate the strict positive-definite hypothesis on the stage-`m`
dyadic point family.
-/
noncomputable def rawDyadicWitnessOfGlobalStrictPosDef
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) (m : ℕ) :
    RawFiniteWitness f (zeroAnchoredDyadicPointFamily m) :=
  rawFiniteWitness_of_posDef
    (hy := pointsHyp_zeroAnchoredDyadicPointFamily m)
    (hL := h (nonzeroInteriorDyadicPointCount m) (zeroAnchoredDyadicPointFamily m)
      (pointsHyp_zeroAnchoredDyadicPointFamily m))

/--
The current raw route needs the stage-wise nondegeneracy condition that makes
`A` invertible. Later theorem-34 passes should either discharge this condition
or replace it with an equivalent construction.
-/
def RawDyadicNondegenerate {f : ℝ → ℝ} (h : GlobalStrictPosDef f) (m : ℕ) : Prop :=
  let W := rawDyadicWitnessOfGlobalStrictPosDef h m
  W.A (W.v 0) ∉
    Submodule.span ℂ
      (Set.range fun i : { i : Fin (nonzeroInteriorDyadicPointCount m + 1) // i ≠ 0 } =>
        W.v i.1 - W.v 0)

private noncomputable def rawDyadicA_bijective
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) (m : ℕ)
    (hnd : RawDyadicNondegenerate h m) :
    Function.Bijective (rawDyadicWitnessOfGlobalStrictPosDef h m).A :=
  (rawDyadicWitnessOfGlobalStrictPosDef h m).A_bijective_of_not_mem_vSubV0 hnd

/-- The self-adjoint raw operator `T = A⁻¹` at dyadic stage `m`. -/
noncomputable def rawDyadicOperator
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) (m : ℕ)
    (hnd : RawDyadicNondegenerate h m) :
    (rawDyadicWitnessOfGlobalStrictPosDef h m).H →ₗ[ℂ]
      (rawDyadicWitnessOfGlobalStrictPosDef h m).H :=
  let W := rawDyadicWitnessOfGlobalStrictPosDef h m
  W.Ainv (rawDyadicA_bijective h m hnd)

/-- The transformed vector `ψ = A⁻¹ φ` used to build the raw discrete measure. -/
noncomputable def rawDyadicPsi
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) (m : ℕ)
    (hnd : RawDyadicNondegenerate h m) :
    (rawDyadicWitnessOfGlobalStrictPosDef h m).H :=
  let W := rawDyadicWitnessOfGlobalStrictPosDef h m
  rawDyadicOperator h m hnd W.φ

/-- The raw dyadic operator `T = A⁻¹` is symmetric (self-adjoint). -/
theorem rawDyadicOperator_isSymmetric
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) (m : ℕ)
    (hnd : RawDyadicNondegenerate h m) :
    (rawDyadicOperator h m hnd).IsSymmetric := by
  let W := rawDyadicWitnessOfGlobalStrictPosDef h m
  let hA_bij := rawDyadicA_bijective h m hnd
  have hsa : IsSelfAdjoint (W.Ainv hA_bij) := W.Ainv_isSelfAdjoint hA_bij
  exact (LinearMap.isSymmetric_iff_isSelfAdjoint _).2 hsa

/-- Raw discrete measure attached to the dyadic stage. -/
noncomputable def rawDyadicMeasure
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) (m : ℕ)
    (hnd : RawDyadicNondegenerate h m) : Measure ℝ :=
  Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric
    (T := rawDyadicOperator h m hnd)
    (hT := rawDyadicOperator_isSymmetric h m hnd)
    (rawDyadicPsi h m hnd)

/-- The squared-inverse-distance integral of the raw dyadic Dirac measure at a family point is
bounded by the derivative of `f` at that point. [simon2019] -/
theorem rawDyadic_lintegral_sqInvDist_le_deriv_at_family
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) (m : ℕ)
    (hnd : RawDyadicNondegenerate h m) (i : Fin (nonzeroInteriorDyadicPointCount m + 1)) :
    (∫⁻ t, Quantum.TraceInequality.Loewner.sqInvDist (zeroAnchoredDyadicPointFamily m i) t
        ∂(rawDyadicMeasure h m hnd)) ≤
      ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) := by
  let W := rawDyadicWitnessOfGlobalStrictPosDef h m
  let hA_bij := rawDyadicA_bijective h m hnd
  let T := W.Ainv hA_bij
  let ψ := T W.φ
  let hT : T.IsSymmetric :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint T).2 (W.Ainv_isSelfAdjoint hA_bij)
  simpa [rawDyadicMeasure, rawDyadicOperator, rawDyadicPsi, W, hA_bij, T, ψ, hT] using
    W.lintegral_sqInvDist_diracMeasure_le_of_transformed_witness_deriv hA_bij i

/--
Local theorem-34 estimate on the nonzero strictly interior dyadic grid.

This is the part supplied by the raw witness and Step45. The remaining theorem-34
work is to combine these local estimates with an open-center dyadic cover and a
uniform derivative bound.
-/
theorem rawDyadic_lintegral_sqInvDist_le_deriv_of_mem_nonzeroInteriorDyadicIndices
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) (m : ℕ)
    (hnd : RawDyadicNondegenerate h m) (k : ℤ)
    (hk : k ∈ nonzeroInteriorDyadicIndices m) :
    (∫⁻ t, Quantum.TraceInequality.Loewner.sqInvDist (dyadicGridPoint m k) t
        ∂(rawDyadicMeasure h m hnd)) ≤
      ENNReal.ofReal (deriv f (dyadicGridPoint m k)) := by
  let i : Fin (nonzeroInteriorDyadicPointCount m) := nonzeroInteriorDyadicPointIndex m k hk
  have hpoint : zeroAnchoredDyadicPointFamily m i.succ = dyadicGridPoint m k := by
    simpa [i] using zeroAnchoredDyadicPointFamily_succ_openIndex m k hk
  simpa [hpoint] using
    rawDyadic_lintegral_sqInvDist_le_deriv_at_family h m hnd i.succ


/-- Sum bound over the full dyadic family `0 + nonzeroInteriorDyadicIndices m`. -/
theorem measure_Icc_le_sum_measure_dyadicFamilyClosedBall
    (μ : Measure ℝ) (m : ℕ) :
    μ (Set.Icc (-1 : ℝ) 1) ≤
      (Finset.univ : Finset (Fin (nonzeroInteriorDyadicPointCount m + 1))).sum
        (fun i =>
          μ (Metric.closedBall (zeroAnchoredDyadicPointFamily m i) (dyadicGridRadius m))) := by
  have hμmono :
      μ (Set.Icc (-1 : ℝ) 1) ≤
        μ (⋃ i : Fin (nonzeroInteriorDyadicPointCount m + 1),
          Metric.closedBall (zeroAnchoredDyadicPointFamily m i) (dyadicGridRadius m)) :=
    measure_mono (Icc_subset_iUnion_zeroAnchoredDyadicPointFamily_closedBall m)
  have hUnion :
      μ (⋃ i : Fin (nonzeroInteriorDyadicPointCount m + 1),
          Metric.closedBall (zeroAnchoredDyadicPointFamily m i) (dyadicGridRadius m)) ≤
        (Finset.univ : Finset (Fin (nonzeroInteriorDyadicPointCount m + 1))).sum
          (fun i =>
            μ (Metric.closedBall (zeroAnchoredDyadicPointFamily m i) (dyadicGridRadius m))) := by
    simpa using
      (measure_biUnion_finset_le (μ := μ)
        (I := (Finset.univ : Finset (Fin (nonzeroInteriorDyadicPointCount m + 1))))
        (s := fun i : Fin (nonzeroInteriorDyadicPointCount m + 1) =>
          Metric.closedBall (zeroAnchoredDyadicPointFamily m i) (dyadicGridRadius m)))
  exact hμmono.trans hUnion

/-- Cover bound: if the squared-inverse-distance integral at every dyadic family point is at most
`K`, then the measure of `[-1, 1]` is bounded by `(count + 1) · radius² · K`. -/
theorem measure_Icc_le_mul_lintegral_sqInvDist_of_uniform_bound_dyadicFamily
    (μ : Measure ℝ) (m : ℕ) (K : ENNReal)
    (hK :
      ∀ i : Fin (nonzeroInteriorDyadicPointCount m + 1),
        (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist
          (zeroAnchoredDyadicPointFamily m i) y ∂μ) ≤ K) :
    μ (Set.Icc (-1 : ℝ) 1) ≤
      (nonzeroInteriorDyadicPointCount m + 1) *
        ((ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ)) * K := by
  have hcover_sum :=
    measure_Icc_le_sum_measure_dyadicFamilyClosedBall (μ := μ) (m := m)
  have hrpos : 0 < dyadicGridRadius m := dyadicGridRadius_pos m
  have hball :
      ∀ i : Fin (nonzeroInteriorDyadicPointCount m + 1),
        μ (Metric.closedBall (zeroAnchoredDyadicPointFamily m i) (dyadicGridRadius m)) ≤
          ((ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ)) * K := by
    intro i
    have h1 :=
      Quantum.TraceInequality.Loewner.measure_closedBall_le_mul_lintegral_sqInvDist
        (μ := μ) (c := zeroAnchoredDyadicPointFamily m i) (r := dyadicGridRadius m) hrpos
    exact h1.trans (by gcongr; exact hK i)
  have hsum_le :
      (Finset.univ : Finset (Fin (nonzeroInteriorDyadicPointCount m + 1))).sum
          (fun i =>
            μ (Metric.closedBall (zeroAnchoredDyadicPointFamily m i) (dyadicGridRadius m))) ≤
        (Finset.univ : Finset (Fin (nonzeroInteriorDyadicPointCount m + 1))).sum
          (fun _i => ((ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ)) * K) := by
    exact Finset.sum_le_sum fun i _hi => hball i
  have hsum :
      (Finset.univ : Finset (Fin (nonzeroInteriorDyadicPointCount m + 1))).sum
          (fun _i => ((ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ)) * K) =
        (nonzeroInteriorDyadicPointCount m + 1) *
          ((ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ)) * K := by
    simp [Finset.sum_const, Fintype.card_fin, mul_assoc, mul_comm]
  calc
    μ (Set.Icc (-1 : ℝ) 1) ≤
          (Finset.univ : Finset (Fin (nonzeroInteriorDyadicPointCount m + 1))).sum
          (fun i =>
            μ (Metric.closedBall (zeroAnchoredDyadicPointFamily m i)
              (dyadicGridRadius m))) := hcover_sum
    _ ≤ (Finset.univ : Finset (Fin (nonzeroInteriorDyadicPointCount m + 1))).sum
          (fun _i => ((ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ)) * K) := hsum_le
    _ =
        (nonzeroInteriorDyadicPointCount m + 1) *
          ((ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ)) * K := hsum

/-- Combining the cover bound with the uniform derivative bound: the raw dyadic measure of
`[-1, 1]` is bounded by `(count + 1) · radius² · K`. [simon2019] -/
theorem rawDyadic_insideMass_le_of_uniform_deriv_bound_dyadicFamily_of_nondegenerate
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) (m : ℕ)
    (hnd : RawDyadicNondegenerate h m) (K : ENNReal)
    (hK :
      ∀ i : Fin (nonzeroInteriorDyadicPointCount m + 1),
        ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) ≤ K) :
    rawDyadicMeasure h m hnd (Set.Icc (-1 : ℝ) 1) ≤
      (nonzeroInteriorDyadicPointCount m + 1) *
        ((ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ)) * K := by
  exact
    measure_Icc_le_mul_lintegral_sqInvDist_of_uniform_bound_dyadicFamily
      (μ := rawDyadicMeasure h m hnd) (m := m) (K := K)
      fun i => (rawDyadic_lintegral_sqInvDist_le_deriv_at_family h m hnd i).trans (hK i)

end

end Loewner
end TraceInequality
end Quantum
