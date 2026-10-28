import Quantum.TraceInequality.Loewner.Koranyi.BoundaryTraceStagewiseInsideMass
import Quantum.TraceInequality.Loewner.Koranyi.RawDyadicInsideMass
import Quantum.TraceInequality.Loewner.Koranyi.DyadicMassZero

namespace Quantum.TraceInequality.Loewner

open Filter MeasureTheory

open scoped NNReal
open scoped Topology

noncomputable section

/-!
# Stagewise inverse-square bounds

This file is a consumer layer for the 38-c-pre frontier.  It does not produce
the inverse-square estimates.  It only turns a stagewise inverse-square bound
on the canonical signed-evaluation backbone into the stagewise real inside-mass
bound consumed by `BoundaryTraceStagewiseInsideMass`.
-/

/-- The ENNReal dyadic-cover bound induced by a stagewise inverse-square bound. -/
def signedAxisStagewiseSqInvDistENNRealBound {f : ℝ → ℝ}
    (pkg : StrictApproxSignedEvalPackage f) (K : ℕ → ℝ≥0) (n : ℕ) : ENNReal :=
  ((nonzeroInteriorDyadicPointCount (pkg.φ n) + 1 : ℕ) : ENNReal) *
    ((ENNReal.ofReal (dyadicGridRadius (pkg.φ n))) ^ (2 : ℕ)) *
      (K n : ENNReal)

/-- The real upper bound associated with `signedAxisStagewiseSqInvDistENNRealBound`. -/
def signedAxisStagewiseSqInvDistRealBound {f : ℝ → ℝ}
    (pkg : StrictApproxSignedEvalPackage f) (K : ℕ → ℝ≥0) (n : ℕ) : ℝ :=
  (signedAxisStagewiseSqInvDistENNRealBound pkg K n).toReal

/--
A stagewise inverse-square bound for the signed-evaluation backbone at the
canonical stage `m = pkg.φ n`.
-/
structure SignedAxisStagewiseSqInvDistBound {f : ℝ → ℝ}
    (pkg : StrictApproxSignedEvalPackage f) where
  K : ℕ → ℝ≥0
  hK_bound :
    ∀ n : ℕ, ∀ i : Fin (nonzeroInteriorDyadicPointCount (pkg.φ n) + 1),
      (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist
            (zeroAnchoredDyadicPointFamily (pkg.φ n) i) y ∂(pkg.μn (pkg.φ n))) ≤
        (K n : ENNReal)
  tendsto_zero :
    Tendsto (fun n => signedAxisStagewiseSqInvDistRealBound pkg K n) atTop (𝓝 0)

private lemma nonzeroInteriorDyadicPointCount_succ_le_pow (m : ℕ) :
    nonzeroInteriorDyadicPointCount m + 1 ≤ (2 : ℕ) ^ (m + 3) := by
  have hsub : insert (0 : ℤ) (nonzeroInteriorDyadicIndices m) ⊆ dyadicGridIndices m := by
    intro k hk
    rw [Finset.mem_insert] at hk
    rcases hk with rfl | hk
    · exact dyadicGridIndices_contains_zero m
    · exact nonzeroInteriorDyadicIndices_subset_dyadicGridIndices m hk
  have hnot : (0 : ℤ) ∉ nonzeroInteriorDyadicIndices m := by
    simp [nonzeroInteriorDyadicIndices]
  have hcard_sub :
      (insert (0 : ℤ) (nonzeroInteriorDyadicIndices m)).card ≤ (dyadicGridIndices m).card :=
    Finset.card_le_card hsub
  have hcard : nonzeroInteriorDyadicPointCount m + 1 ≤ (dyadicGridIndices m).card := by
    simpa [nonzeroInteriorDyadicPointCount, Finset.card_insert_of_notMem hnot, Nat.add_comm] using
      hcard_sub
  have hpow : (dyadicGridIndices m).card ≤ (2 : ℕ) ^ (m + 3) := by
    simpa [dyadicGridIndices] using
      _root_.Quantum.TraceInequality.Loewner.dyadicCenters_card_le_pow (m := m)
  exact hcard.trans hpow

private lemma signedAxisStagewiseSqInvDist_prefactor_le (m : ℕ) :
    ((nonzeroInteriorDyadicPointCount m + 1 : ℕ) : ENNReal) *
        ((ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ)) ≤
      ENNReal.ofReal (8 * dyadicGridRadius m) := by
  have hcard :
      ((nonzeroInteriorDyadicPointCount m + 1 : ℕ) : ENNReal) ≤
        (((2 : ℕ) ^ (m + 3) : ℕ) : ENNReal) := by
    exact_mod_cast nonzeroInteriorDyadicPointCount_succ_le_pow m
  calc
    ((nonzeroInteriorDyadicPointCount m + 1 : ℕ) : ENNReal) *
        ((ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ)) ≤
        (((2 : ℕ) ^ (m + 3) : ℕ) : ENNReal) *
          ((ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ)) := by
          gcongr
    _ = ENNReal.ofReal (8 * dyadicGridRadius m) := by
          simpa [dyadicGridRadius] using
            _root_.Quantum.TraceInequality.Loewner.ennreal_prefactor_eq (m := m)

private lemma signedAxisStagewiseSqInvDistENNRealBound_ne_top
    {f : ℝ → ℝ} (pkg : StrictApproxSignedEvalPackage f)
    (K : ℕ → ℝ≥0) (n : ℕ) :
    signedAxisStagewiseSqInvDistENNRealBound pkg K n ≠ ⊤ := by
  unfold signedAxisStagewiseSqInvDistENNRealBound
  exact
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (by simp)))
      (by simp)

/-- Stagewise inverse-square bounds give the real stagewise inside-mass bound. -/
def signedAxisStagewiseInsideMassBound_of_sqInvDist_bound
    {f : ℝ → ℝ} {pkg : StrictApproxSignedEvalPackage f}
    (hbound : SignedAxisStagewiseSqInvDistBound pkg) :
    SignedAxisStagewiseInsideMassBound pkg := by
  refine
    { B := signedAxisStagewiseSqInvDistRealBound pkg hbound.K
      nonneg := ?_
      bound := ?_
      tendsto_zero := hbound.tendsto_zero }
  · exact Eventually.of_forall fun _n => ENNReal.toReal_nonneg
  · exact Eventually.of_forall fun n => by
      have hstage :
          (pkg.μn (pkg.φ n)) (Set.Icc (-1 : ℝ) 1) ≤
            signedAxisStagewiseSqInvDistENNRealBound pkg hbound.K n := by
        simpa [signedAxisStagewiseSqInvDistENNRealBound] using
          (measure_Icc_le_mul_lintegral_sqInvDist_of_uniform_bound_dyadicFamily
            (μ := pkg.μn (pkg.φ n)) (m := pkg.φ n) (K := (hbound.K n : ENNReal))
            (hbound.hK_bound n))
      have hfinite :
          signedAxisStagewiseSqInvDistENNRealBound pkg hbound.K n ≠ ⊤ :=
        signedAxisStagewiseSqInvDistENNRealBound_ne_top pkg hbound.K n
      simpa [signedAxisStagewiseSqInvDistRealBound] using
        ENNReal.toReal_mono hfinite hstage

/--
If the stagewise inverse-square constants are eventually bounded by a fixed
finite constant, then the dyadic-cover prefactor tends to zero along the
canonical stages `pkg.φ n`.
-/
def signedAxisStagewiseSqInvDistBound_of_eventually_le_const
    {f : ℝ → ℝ} {pkg : StrictApproxSignedEvalPackage f} {K : ℕ → ℝ≥0}
    (hK_bound :
      ∀ n : ℕ, ∀ i : Fin (nonzeroInteriorDyadicPointCount (pkg.φ n) + 1),
        (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist
              (zeroAnchoredDyadicPointFamily (pkg.φ n) i) y ∂(pkg.μn (pkg.φ n))) ≤
          (K n : ENNReal))
    (C : ℝ≥0) (hK_le : ∀ᶠ n in atTop, K n ≤ C) :
    SignedAxisStagewiseSqInvDistBound pkg := by
  refine
    { K := K
      hK_bound := hK_bound
      tendsto_zero := ?_ }
  have hradius :
      Tendsto (fun n : ℕ => dyadicGridRadius (pkg.φ n)) atTop (𝓝 (0 : ℝ)) := by
    have hφ : Tendsto pkg.φ atTop atTop := pkg.hφ.tendsto_atTop
    simpa [dyadicGridRadius] using
      _root_.Quantum.TraceInequality.Loewner.tendsto_dyadicRadius_zero.comp hφ
  have hUpper :
      Tendsto (fun n : ℕ => (8 * (C : ℝ)) * dyadicGridRadius (pkg.φ n))
        atTop (𝓝 0) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      hradius.const_mul (8 * (C : ℝ))
  have hBound :
      ∀ᶠ n in atTop,
        signedAxisStagewiseSqInvDistRealBound pkg K n ≤
          (8 * (C : ℝ)) * dyadicGridRadius (pkg.φ n) := by
    filter_upwards [hK_le] with n hn
    have hpref := signedAxisStagewiseSqInvDist_prefactor_le (pkg.φ n)
    have hK_en : (K n : ENNReal) ≤ (C : ENNReal) := by
      exact_mod_cast hn
    have hENN :
        signedAxisStagewiseSqInvDistENNRealBound pkg K n ≤
          ENNReal.ofReal (8 * dyadicGridRadius (pkg.φ n)) * (C : ENNReal) := by
      unfold signedAxisStagewiseSqInvDistENNRealBound
      calc
        ((nonzeroInteriorDyadicPointCount (pkg.φ n) + 1 : ℕ) : ENNReal) *
            ((ENNReal.ofReal (dyadicGridRadius (pkg.φ n))) ^ (2 : ℕ)) *
              (K n : ENNReal) ≤
            ENNReal.ofReal (8 * dyadicGridRadius (pkg.φ n)) * (K n : ENNReal) := by
              gcongr
        _ ≤ ENNReal.ofReal (8 * dyadicGridRadius (pkg.φ n)) * (C : ENNReal) := by
              gcongr
    have hfinite :
        ENNReal.ofReal (8 * dyadicGridRadius (pkg.φ n)) * (C : ENNReal) ≠ ⊤ := by
      have hC : (C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC
    have hreal := ENNReal.toReal_mono hfinite hENN
    have hright :
        (ENNReal.ofReal (8 * dyadicGridRadius (pkg.φ n)) * (C : ENNReal)).toReal =
          8 * dyadicGridRadius (pkg.φ n) * (C : ℝ) := by
      have hnonneg : 0 ≤ 8 * dyadicGridRadius (pkg.φ n) := by
        exact mul_nonneg (by norm_num) (le_of_lt (dyadicGridRadius_pos (pkg.φ n)))
      have hCnonneg : 0 ≤ (C : ℝ) := by
        exact_mod_cast C.2
      calc
        (ENNReal.ofReal (8 * dyadicGridRadius (pkg.φ n)) * (C : ENNReal)).toReal =
            (ENNReal.ofReal (8 * dyadicGridRadius (pkg.φ n)) *
              ENNReal.ofReal (C : ℝ)).toReal := by
              simp
        _ = (ENNReal.ofReal ((8 * dyadicGridRadius (pkg.φ n)) * (C : ℝ))).toReal := by
              rw [ENNReal.ofReal_mul hnonneg]
        _ = (8 * dyadicGridRadius (pkg.φ n)) * (C : ℝ) := by
              exact ENNReal.toReal_ofReal (mul_nonneg hnonneg hCnonneg)
    rw [hright] at hreal
    simpa [signedAxisStagewiseSqInvDistRealBound, mul_assoc, mul_comm, mul_left_comm] using
      hreal
  exact squeeze_zero'
    (Eventually.of_forall fun _n => ENNReal.toReal_nonneg) hBound hUpper

/-- A pointwise uniform bound is a convenient special case of the eventual version. -/
def signedAxisStagewiseSqInvDistBound_of_forall_le_const
    {f : ℝ → ℝ} {pkg : StrictApproxSignedEvalPackage f} {K : ℕ → ℝ≥0}
    (hK_bound :
      ∀ n : ℕ, ∀ i : Fin (nonzeroInteriorDyadicPointCount (pkg.φ n) + 1),
        (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist
              (zeroAnchoredDyadicPointFamily (pkg.φ n) i) y ∂(pkg.μn (pkg.φ n))) ≤
          (K n : ENNReal))
    (C : ℝ≥0) (hK_le : ∀ n, K n ≤ C) :
    SignedAxisStagewiseSqInvDistBound pkg :=
  signedAxisStagewiseSqInvDistBound_of_eventually_le_const hK_bound C
    (Eventually.of_forall hK_le)

/-- Stagewise inverse-square bounds imply inside mass decay. -/
theorem signedAxisInsideMassDecay_of_sqInvDist_bound
    {f : ℝ → ℝ} {pkg : StrictApproxSignedEvalPackage f}
    (hbound : SignedAxisStagewiseSqInvDistBound pkg) :
    SignedAxisInsideMassDecay pkg :=
  signedAxisInsideMassDecay_of_stagewise_insideMass_bound
    (signedAxisStagewiseInsideMassBound_of_sqInvDist_bound hbound)

/-- Stagewise inverse-square bounds close the inside-vanishing gate on any signed axis. -/
theorem signedAxisInsideVanishing_of_sqInvDist_bound
    {f : ℝ → ℝ} {pkg : StrictApproxSignedEvalPackage f} {x : ℝ}
    (axis : SignedEvalAxis pkg x) (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hbound : SignedAxisStagewiseSqInvDistBound pkg) :
    SignedAxisInsideVanishing pkg axis :=
  signedAxisInsideVanishing_of_stagewise_insideMass_bound axis hx
    (signedAxisStagewiseInsideMassBound_of_sqInvDist_bound hbound)

end

end Loewner
end TraceInequality
end Quantum
