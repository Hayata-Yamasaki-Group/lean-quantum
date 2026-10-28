/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/
import Quantum.TraceInequality.HansenPedersen.MonotoneConvexEquivalence.VI2Instances

/-!
# Endpoint monotonicity and the contraction inequality

This file proves the two nontrivial endpoint directions used in the
Hiai–Yanagi Theorem 5.1.8 surface theorem.  The first direction derives
operator monotonicity of `-f` on `[0, ∞)` from operator convexity and
nonpositivity of `f`; the second derives the contraction Jensen inequality
from that monotonicity by a Julia-block dilation and a regularized limit.

## Main results

* `ConvexityCharacterization.conditionI_implies_conditionVI_fixed`: fixed
  Hilbert-space form of `(i) → (vi)` at `α = ⊤`.
* `ConvexityCharacterization.conditionVI_implies_conditionII_fixed`: fixed
  Hilbert-space form of `(vi) → (ii)` at `α = ⊤`.

## References

* Hiai--Yanagi, *Hilbert spaces and linear operators*,
  Ohmsha, 2021, Section 5.1, Theorem 5.1.8.
-/

namespace HansenPedersen

universe u

open CFC MeasureTheory
open scoped Topology
open Filter

namespace ConvexityCharacterization

section ConditionItoVI

variable {K : Type u}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]

attribute [local instance]
  instModuleRealLKScopedI6
  instPosSMulMonoRealLKScopedI6
  instSMulPosMonoRealLKScopedI6
  instContinuousSMulRealLKScopedI6
  instStarModuleRealLKScopedI6
  instAlgebraRealLKScopedI6
  instSMulRealLKScopedI6
  instMulActionRealLKScopedI6
  instSMulZeroClassRealLKScopedI6
  instAddRightMonoLKScopedI6
  instAddLeftMonoLKScopedI6
  instAddRightReflectLELKScopedI6

omit [Nontrivial (L K)] in
private lemma cfcR_nonpos_of_nonpos {f : ℝ → ℝ} {A : L K}
    (hf : ContinuousOn f (halfOpenRay ⊤))
    (hA0 : 0 ≤ A)
    (hneg : ∀ t ∈ halfOpenRay ⊤, f t ≤ 0) :
    cfcR (ℋ := K) f A ≤ 0 := by
  have hσA : spectrum ℝ A ⊆ halfOpenRay ⊤ :=
    spectrum_subset_halfOpenRay_top_of_nonneg (ℋ := K) hA0
  have hcf :=
    cfc_mono (R := ℝ) (A := L K) (p := IsSelfAdjoint) (a := A)
      (f := f) (g := fun _ : ℝ ↦ 0)
      (h := by
        intro x hx
        exact hneg x (hσA hx))
      (hf := hf.mono hσA) (hg := continuousOn_const)
  simpa [cfcR] using hcf
private lemma spectrum_subset_Icc_zero_norm_of_nonneg {A : L K}
    (hA : IsSelfAdjoint A) (hA0 : 0 ≤ A) :
    spectrum ℝ A ⊆ Set.Icc (0 : ℝ) ‖A‖ := by
  have hAβ : A ≤ (‖A‖ : ℝ) • (1 : L K) := by
    simpa [Algebra.algebraMap_eq_smul_one] using hA.le_algebraMap_norm_self
  exact HansenPedersen.spectrum_subset_Icc_of_order_bounds_clm
    (K := K) (T := A) (α := 0) (β := ‖A‖) hA
    (by simpa [Algebra.algebraMap_eq_smul_one] using hA0)
    (by simpa [Algebra.algebraMap_eq_smul_one] using hAβ)

/-- Fixed-Hilbert-space form of `(i) → (vi)` in Theorem 5.1.8.  Under
continuity and nonpositivity of `f` on `[0, ∞)`, operator convexity with
`f 0 ≤ 0` makes `-f` operator monotone on the nonnegative half-line.
Source: Hiai–Yanagi, Theorem 5.1.8. -/
theorem conditionI_implies_conditionVI_fixed {f : ℝ → ℝ}
    (hf : ContinuousOn f (halfOpenRay ⊤))
    (hneg : ∀ t ∈ halfOpenRay ⊤, f t ≤ 0)
    (hI : ConditionI.{u} ⊤ f) :
    HOperatorMonotoneOnInterval K (halfOpenRay ⊤) (fun t : ℝ ↦ -f t) := by
  intro A B hA hB hσA hσB hAB
  /- Step 1: Place A and B in the positive cone and put B in a compact spectral interval. -/
  have hA0 : 0 ≤ A := by
    exact nonneg_of_isSelfAdjoint_of_spectrum_subset_Ici hA (by simpa [halfOpenRay_top] using hσA)
  have hB0 : 0 ≤ B := by
    exact nonneg_of_isSelfAdjoint_of_spectrum_subset_Ici hB (by simpa [halfOpenRay_top] using hσB)
  let β : ℝ := ‖B‖
  have hβ_nonneg : 0 ≤ β := norm_nonneg B
  have hσB_Icc : spectrum ℝ B ⊆ Set.Icc (0 : ℝ) β := by
    simpa [β] using spectrum_subset_Icc_zero_norm_of_nonneg (K := K) hB hB0
  have hfIcc : ContinuousOn f (Set.Icc (0 : ℝ) β) := by
    refine hf.mono ?_
    intro x hx
    simpa [halfOpenRay_top] using hx.1
  /- Step 2: Regularize B by scaling and prepare the positive Condition I direction. -/
  let Bε : ℝ → L K := fun ε ↦ (1 - ε) • B
  let Yε : ℝ → L K := fun ε ↦ ((1 - ε) / ε) • (B - A)
  have hsmall :
      Set.Ioi (0 : ℝ) ∩ Set.Iio 1 ∈ 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ) := by
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ?_
    refine ⟨Set.Iio (1 : ℝ), Iio_mem_nhds zero_lt_one, ?_⟩
    intro x hx
    exact ⟨hx.2, hx.1⟩
  have hBε_tendsto : Tendsto Bε (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 B) := by
    have hε_tendsto : Tendsto (fun ε : ℝ ↦ ε) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hcoeff : Tendsto (fun ε : ℝ ↦ 1 - ε) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 1) := by
      simpa [sub_eq_add_neg] using tendsto_const_nhds.sub hε_tendsto
    simpa [Bε] using hcoeff.smul_const B
  /- Step 3: Use CFC continuity for the scaled path inside the compact spectral interval. -/
  have hcfBε_tendsto :
      Tendsto (fun ε : ℝ ↦ cfcR (ℋ := K) f (Bε ε))
        (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (cfcR (ℋ := K) f B)) := by
    simpa [cfcR, Bε] using
      Filter.Tendsto.cfc (A := L K) (hs := isCompact_Icc) (f := f)
        hBε_tendsto
        (by
          refine Filter.mem_of_superset hsmall ?_
          intro ε hε
          rcases hε with ⟨hεpos, hεlt1⟩
          have hεpos' : 0 < ε := hεpos
          have hεlt1' : ε < 1 := hεlt1
          have hBε0 : (0 : L K) ≤ Bε ε := by
            exact smul_nonneg (sub_nonneg.mpr hεlt1'.le) hB0
          have hBεβ : Bε ε ≤ (β : ℝ) • (1 : L K) := by
            calc
              Bε ε = (1 - ε) • B := by rfl
              _ ≤ (1 - ε) • ((β : ℝ) • (1 : L K)) := by
                    exact smul_le_smul_of_nonneg_left
                      (by
                        simpa [β, Algebra.algebraMap_eq_smul_one] using
                          hB.le_algebraMap_norm_self)
                      (sub_nonneg.mpr hεlt1'.le)
              _ ≤ (β : ℝ) • (1 : L K) := by
                    have hscale : 1 - ε ≤ 1 := by linarith
                    simpa [smul_smul, β, mul_comm, mul_left_comm, mul_assoc] using
                      smul_le_smul_of_nonneg_right hscale
                        (show (0 : L K) ≤ (β : ℝ) • (1 : L K) by
                          simpa [Algebra.algebraMap_eq_smul_one] using
                            smul_nonneg hβ_nonneg
                              (show (0 : L K) ≤ (1 : L K) by exact zero_le_one))
          exact HansenPedersen.spectrum_subset_Icc_of_order_bounds_clm
            (K := K) (T := Bε ε) (α := 0) (β := β)
            (by simpa [Bε] using ((IsSelfAdjoint.all (1 - ε)).smul hB))
            (by simpa [Algebra.algebraMap_eq_smul_one] using hBε0)
            (by simpa [Algebra.algebraMap_eq_smul_one] using hBεβ))
        (by
          refine Filter.mem_of_superset hsmall ?_
          intro ε _hε
          simpa [Bε] using ((IsSelfAdjoint.all (1 - ε)).smul hB))
        hσB_Icc hB hfIcc
  have hrhs_tendsto :
      Tendsto (fun ε : ℝ ↦ (1 - ε) • cfcR (ℋ := K) f A)
        (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (cfcR (ℋ := K) f A)) := by
    have hε_tendsto : Tendsto (fun ε : ℝ ↦ ε) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hcoeff : Tendsto (fun ε : ℝ ↦ 1 - ε) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 1) := by
      simpa [sub_eq_add_neg] using tendsto_const_nhds.sub hε_tendsto
    simpa using hcoeff.smul_const (cfcR (ℋ := K) f A)
  /- Step 4: Apply Condition I to Bε = (1 - ε)A + εYε and drop f(Yε). -/
  have hEventually :
      ∀ᶠ ε : ℝ in 𝓝[Set.Ioi (0 : ℝ)] 0,
        cfcR (ℋ := K) f (Bε ε) ≤ (1 - ε) • cfcR (ℋ := K) f A := by
    refine Filter.mem_of_superset hsmall ?_
    intro ε hε
    rcases hε with ⟨hεpos, hεlt1⟩
    have hεpos' : 0 < ε := hεpos
    have hεlt1' : ε < 1 := hεlt1
    have hdiff0 : (0 : L K) ≤ B - A := sub_nonneg.mpr hAB
    have hYε0 : (0 : L K) ≤ Yε ε := by
      refine smul_nonneg ?_ hdiff0
      have : 0 ≤ (1 - ε) / ε := by
        exact div_nonneg (sub_nonneg.mpr hεlt1'.le) hεpos'.le
      simpa [Yε] using this
    have hσYε : spectrum ℝ (Yε ε) ⊆ halfOpenRay ⊤ :=
      spectrum_subset_halfOpenRay_top_of_nonneg (ℋ := K) hYε0
    have hconv :=
      (hI.1 K) (A := A) (B := Yε ε) (t := ε)
        hA (IsSelfAdjoint.of_nonneg hYε0) hεpos'.le hεlt1'.le hσA hσYε
    have hlhs :
        (1 - ε) • A + ε • Yε ε = Bε ε := by
      calc
        (1 - ε) • A + ε • Yε ε
            = (1 - ε) • A + (1 - ε) • (B - A) := by
                have hεne : ε ≠ 0 := hεpos'.ne'
                simp [Yε, smul_smul, div_eq_mul_inv, hεne, mul_comm]
        _ = (1 - ε) • B := by
              rw [smul_sub]
              abel
        _ = Bε ε := by rfl
    have hYε_nonpos : cfcR (ℋ := K) f (Yε ε) ≤ 0 :=
      cfcR_nonpos_of_nonpos (K := K) hf hYε0 hneg
    have hdrop : (1 - ε) • cfcR (ℋ := K) f A + ε • cfcR (ℋ := K) f (Yε ε) ≤
        (1 - ε) • cfcR (ℋ := K) f A := by
      have hterm : ε • cfcR (ℋ := K) f (Yε ε) ≤ 0 := by
        simpa [zero_smul] using smul_le_smul_of_nonneg_left hYε_nonpos hεpos'.le
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hterm ((1 - ε) • cfcR (ℋ := K) f A)
    have hconv' :
        cfcR (ℋ := K) f (Bε ε) ≤
          (1 - ε) • cfcR (ℋ := K) f A + ε • cfcR (ℋ := K) f (Yε ε) := by
      simpa [hlhs, Bε] using hconv
    exact le_trans hconv' hdrop
  /- Step 5: Pass the eventual inequality to the limit and negate to obtain monotonicity of -f. -/
  have hmono : cfcR (ℋ := K) f B ≤ cfcR (ℋ := K) f A :=
    le_of_tendsto_of_tendsto hcfBε_tendsto hrhs_tendsto hEventually
  simpa [cfcR, cfc_neg] using neg_le_neg hmono
end ConditionItoVI
section ConditionVItoII
variable {K : Type u}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)]

attribute [local instance]
  instModuleRealLKScopedVI2
  instPosSMulMonoRealLKScopedVI2
  instSMulPosMonoRealLKScopedVI2
  instContinuousSMulRealLKScopedVI2
  instStarModuleRealLKScopedVI2
  instAlgebraRealLKScopedVI2
  instSMulRealLKScopedVI2
  instMulActionRealLKScopedVI2
  instSMulZeroClassRealLKScopedVI2
  instAddRightMonoLKScopedVI2
  instAddLeftMonoLKScopedVI2
  instAddRightReflectLELKScopedVI2
  instStarMulLKScopedVI2
  instMonoidLKScopedVI2
  instStarMulLPairScopedVI2
  instMonoidLPairScopedVI2
  instModuleRealLPairScopedVI2
  instCFCRealLPairScopedVI2

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] in
private lemma spectrum_zero_subset_halfOpenRay_top :
    spectrum ℝ (0 : L K) ⊆ halfOpenRay ⊤ := by
  intro x hx
  have hx0 : x = 0 := by
    simpa [spectrum.zero_eq] using hx
  subst hx0
  simp [halfOpenRay_top]
omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
private lemma fst_le_of_diag_le_block {a b c d e g : L K}
    (ha : IsSelfAdjoint a) (hc : IsSelfAdjoint c)
    (h : HansenPedersen.Internal.diagMapCLM a b ≤ blockCLM c d e g) :
    a ≤ c := by
  rw [ContinuousLinearMap.le_def] at h ⊢
  rw [ContinuousLinearMap.isPositive_iff']
  constructor
  · exact hc.sub ha
  · intro x
    have hx := h.inner_nonneg_left (WithLp.toLp 2 (x, 0))
    simpa [HansenPedersen.Internal.diagMapCLM_apply, blockCLM_apply,
      WithLp.prod_inner_apply] using hx
omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
private lemma compressed_le_norm_smul_one {A C : L K}
    (hA : IsSelfAdjoint A)
    (hCnorm : ‖C‖ ≤ 1) :
    star C * A * C ≤ (‖A‖ : ℝ) • (1 : L K) := by
  have hA_le : A ≤ (‖A‖ : ℝ) • (1 : L K) := by
    simpa [Algebra.algebraMap_eq_smul_one] using hA.le_algebraMap_norm_self
  have hCA : star C * A * C ≤ (‖A‖ : ℝ) • (star C * C) := by
    simpa [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_assoc] using
      star_left_conjugate_le_conjugate hA_le C
  calc
    star C * A * C ≤ (‖A‖ : ℝ) • (star C * C) := hCA
    _ ≤ (‖A‖ : ℝ) • (1 : L K) := by
        exact smul_le_smul_of_nonneg_left
          (HansenPedersen.ConvexityCharacterization.star_mul_self_le_one_of_norm_le_one
            (K := K) hCnorm)
          (norm_nonneg _)
private theorem regularized_limit_le {f : ℝ → ℝ} {A M C : L K}
    (hf : ContinuousOn f (halfOpenRay ⊤))
    (hM0 : 0 ≤ M)
    (hMself : IsSelfAdjoint M)
    (hMnorm : M ≤ (‖A‖ : ℝ) • (1 : L K))
    (hEventually :
      ∀ᶠ ε : ℝ in 𝓝[Set.Ioi (0 : ℝ)] 0,
        cfcR (ℋ := K) f (M + ε • (1 : L K)) ≤ star C * cfcR (ℋ := K) f A * C) :
    cfcR (ℋ := K) f M ≤ star C * cfcR (ℋ := K) f A * C := by
  let β : ℝ := ‖A‖ + 1
  have hIcc_sub : Set.Icc (0 : ℝ) β ⊆ halfOpenRay ⊤ := by
    intro x hx
    simpa [halfOpenRay_top] using hx.1
  have hfIcc : ContinuousOn f (Set.Icc (0 : ℝ) β) := hf.mono hIcc_sub
  let Mε : ℝ → L K := fun ε ↦ M + ε • (1 : L K)
  have hMε_tendsto : Tendsto Mε (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 M) := by
    have hε_tendsto : Tendsto (fun ε : ℝ ↦ ε) (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa [Mε] using tendsto_const_nhds.add (hε_tendsto.smul_const (1 : L K))
  have hcfMε_tendsto :
      Tendsto (fun ε : ℝ ↦ cfcR (ℋ := K) f (Mε ε))
        (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (cfcR (ℋ := K) f M)) := by
    have hsmall :
        Set.Ioi (0 : ℝ) ∩ Set.Iio 1 ∈ 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ) := by
      refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ?_
      refine ⟨Set.Iio (1 : ℝ), Iio_mem_nhds zero_lt_one, ?_⟩
      intro x hx
      exact ⟨hx.2, hx.1⟩
    simpa [cfcR, Mε] using
      Filter.Tendsto.cfc (A := L K) (hs := isCompact_Icc) (f := f)
        hMε_tendsto
        (by
          refine Filter.mem_of_superset hsmall ?_
          intro ε hε
          rcases hε with ⟨hεpos, hεlt1⟩
          have hεpos' : 0 < ε := hεpos
          have hεlt1' : ε < 1 := hεlt1
          have hMε0 : (0 : L K) ≤ Mε ε := by
            exact add_nonneg hM0 (by
              simpa [Algebra.algebraMap_eq_smul_one] using
                smul_nonneg hεpos'.le (show (0 : L K) ≤ (1 : L K) by exact zero_le_one))
          have hMεβ : Mε ε ≤ (β : ℝ) • (1 : L K) := by
            calc
              Mε ε = M + ε • (1 : L K) := by rfl
              _ ≤ (‖A‖ : ℝ) • (1 : L K) + ε • (1 : L K) := by
                    exact add_le_add hMnorm le_rfl
              _ ≤ (β : ℝ) • (1 : L K) := by
                    have hβeq :
                        (‖A‖ : ℝ) • (1 : L K) + ε • (1 : L K) =
                          ((‖A‖ + ε : ℝ)) • (1 : L K) := by
                      simp [add_smul, add_comm]
                    rw [hβeq]
                    exact smul_le_smul_of_nonneg_right (by linarith)
                      (show (0 : L K) ≤ (1 : L K) by exact zero_le_one)
          exact HansenPedersen.spectrum_subset_Icc_of_order_bounds_clm
            (K := K) (T := Mε ε) (α := 0) (β := β)
            (hMself.add ((IsSelfAdjoint.all ε).smul (IsSelfAdjoint.one _)))
            (by simpa [Algebra.algebraMap_eq_smul_one] using hMε0)
            (by simpa [Algebra.algebraMap_eq_smul_one] using hMεβ))
        (by
          refine Filter.mem_of_superset hsmall ?_
          intro ε _hε
          simpa [Mε] using (hMself.add ((IsSelfAdjoint.all ε).smul (IsSelfAdjoint.one _))))
        (by
          have hβ_nonneg : 0 ≤ β := by
            dsimp [β]
            positivity
          refine HansenPedersen.spectrum_subset_Icc_of_order_bounds_clm
            (K := K) (T := M) (α := 0) (β := β) hMself
            ?_ ?_
          · simpa [Algebra.algebraMap_eq_smul_one] using hM0
          · have hMβ' : M ≤ (β : ℝ) • (1 : L K) := by
              calc
                M ≤ (‖A‖ : ℝ) • (1 : L K) := hMnorm
                _ ≤ (β : ℝ) • (1 : L K) := by
                    exact smul_le_smul_of_nonneg_right
                      (by linarith [norm_nonneg A])
                      (show (0 : L K) ≤ (1 : L K) by exact zero_le_one)
            simpa [Algebra.algebraMap_eq_smul_one] using hMβ')
        hMself hfIcc
  exact le_of_tendsto_of_tendsto hcfMε_tendsto tendsto_const_nhds hEventually
omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
/-- Scalar core of `julia_block_le_regularized_diag`: the real part of the quadratic form of
the block `blockCLM (ε • 1) S (star S) (μ • 1 - R)` at `(x, y)` is nonnegative for
`μ = ‖R‖ + ‖S‖ ^ 2 / ε + 1` (Cauchy--Schwarz plus `2ab ≤ εa² + b²/ε`). -/
private lemma julia_regularized_re_nonneg (S R : L K) (x y : K) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ RCLike.re (inner ℂ ((ε • (1 : L K)) x + S y) x +
      inner ℂ ((star S) x + ((‖R‖ + ‖S‖ ^ 2 / ε + 1 : ℝ) • (1 : L K) - R) y) y) := by
  have hsmul : ∀ (r : ℝ) (v : K), RCLike.re (inner ℂ ((r • (1 : L K)) v) v) = r * ‖v‖ ^ 2 := by
    intro r v
    have h : inner ℂ ((r : ℂ) • v) v = ((r * ‖v‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
      simp
    change RCLike.re (inner ℂ ((r : ℂ) • v) v) = r * ‖v‖ ^ 2
    rw [h]
    exact Complex.ofReal_re _
  have hS1 : -(‖S‖ * ‖x‖ * ‖y‖) ≤ RCLike.re (inner ℂ (S y) x) := by
    have habs : |RCLike.re (inner ℂ (S y) x)| ≤ ‖S‖ * ‖x‖ * ‖y‖ := by
      calc
        |RCLike.re (inner ℂ (S y) x)| ≤ ‖inner ℂ (S y) x‖ := RCLike.abs_re_le_norm _
        _ ≤ ‖S y‖ * ‖x‖ := norm_inner_le_norm _ _
        _ ≤ ‖S‖ * ‖y‖ * ‖x‖ := by
              gcongr
              exact ContinuousLinearMap.le_opNorm S y
        _ = ‖S‖ * ‖x‖ * ‖y‖ := by ring
    exact neg_le_of_abs_le habs
  have hS2 : -(‖S‖ * ‖x‖ * ‖y‖) ≤ RCLike.re (inner ℂ ((star S) x) y) := by
    have hEq : inner ℂ ((star S) x) y = inner ℂ x (S y) := by
      simpa [ContinuousLinearMap.star_eq_adjoint] using
        (ContinuousLinearMap.adjoint_inner_left S y x)
    rw [hEq]
    have habs : |RCLike.re (inner ℂ x (S y))| ≤ ‖S‖ * ‖x‖ * ‖y‖ := by
      calc
        |RCLike.re (inner ℂ x (S y))| ≤ ‖inner ℂ x (S y)‖ := RCLike.abs_re_le_norm _
        _ ≤ ‖x‖ * ‖S y‖ := norm_inner_le_norm _ _
        _ ≤ ‖x‖ * (‖S‖ * ‖y‖) := by
              gcongr
              exact ContinuousLinearMap.le_opNorm S y
        _ = ‖S‖ * ‖x‖ * ‖y‖ := by ring
    exact neg_le_of_abs_le habs
  have hR : RCLike.re (inner ℂ (R y) y) ≤ ‖R‖ * ‖y‖ ^ 2 := by
    calc
      RCLike.re (inner ℂ (R y) y) ≤ ‖inner ℂ (R y) y‖ := RCLike.re_le_norm _
      _ ≤ ‖R y‖ * ‖y‖ := norm_inner_le_norm _ _
      _ ≤ ‖R‖ * ‖y‖ * ‖y‖ := by
            gcongr
            exact ContinuousLinearMap.le_opNorm R y
      _ = ‖R‖ * ‖y‖ ^ 2 := by ring
  have htwo : 2 * ‖S‖ * ‖x‖ * ‖y‖ ≤ ε * ‖x‖ ^ 2 + (‖S‖ ^ 2 / ε) * ‖y‖ ^ 2 := by
    simpa [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (two_mul_le_add_mul_sq (a := ‖x‖) (b := ‖S‖ * ‖y‖) hε)
  rw [inner_add_left, inner_add_left, ContinuousLinearMap.sub_apply, inner_sub_left, map_add,
    map_add, map_add, map_sub, hsmul, hsmul]
  nlinarith [sq_nonneg ‖y‖]

omit [ContinuousFunctionalCalculus ℝ (L K) IsSelfAdjoint] [Nontrivial (L K)] in
/-- Quadratic-form dominance for the Julia block operator: the self-adjoint block
`blockCLM M (-S) (-star S) R` is dominated by the regularized diagonal
`diagMapCLM (M + ε • 1) ((‖R‖ + ‖S‖ ^ 2 / ε + 1) • 1)`.  This is the heavy
analytic core of the `(vi) → (ii)` limit argument (Cauchy--Schwarz plus the
`2ab ≤ εa² + b²/ε` trick on the block quadratic form), factored out of
`conditionVI_implies_conditionII_fixed` so that it elaborates once over atoms
instead of inside the large limit proof. -/
private lemma julia_block_le_regularized_diag {M R S : L K}
    (hMself : IsSelfAdjoint M)
    (hXself : IsSelfAdjoint (blockCLM M (-S) (-(star S)) R))
    {ε : ℝ} (hεpos' : 0 < ε) :
    blockCLM M (-S) (-(star S)) R ≤
      HansenPedersen.Internal.diagMapCLM (M + ε • (1 : L K))
        ((‖R‖ + ‖S‖ ^ 2 / ε + 1 : ℝ) • (1 : L K)) := by
  /- Step 1: Choose the diagonal regularizer large enough to absorb R and the S-cross terms. -/
  let X : L (WithLp 2 (K × K)) := blockCLM M (-S) (-(star S)) R
  let μ : ℝ := ‖R‖ + ‖S‖ ^ 2 / ε + 1
  let Breg : L (WithLp 2 (K × K)) :=
    HansenPedersen.Internal.diagMapCLM (M + ε • (1 : L K)) ((μ : ℝ) • (1 : L K))
  have hμpos : 0 < μ := by
    dsimp [μ]
    positivity
  have hBregself : IsSelfAdjoint Breg :=
    HansenPedersen.Internal.isSelfAdjoint_diagMapCLM
      (hMself.add ((IsSelfAdjoint.all ε).smul (IsSelfAdjoint.one _)))
      (((IsSelfAdjoint.all μ).smul (IsSelfAdjoint.one _)))
  change X ≤ Breg
  /- Step 2: Rewrite the desired order as positivity of an explicit block difference. -/
  have hBminusX :
      Breg - X = blockCLM (ε • (1 : L K)) S (star S) ((μ : ℝ) • (1 : L K) - R) := by
    dsimp only [Breg, X]
    rw [show
        HansenPedersen.Internal.diagMapCLM (M + ε • (1 : L K))
          (((μ : ℝ)) • (1 : L K)) =
          blockCLM (M + ε • (1 : L K)) 0 0 (((μ : ℝ)) • (1 : L K)) by
          simp [blockCLM_zero_zero]]
    rw [sub_eq_add_neg,
      show -(blockCLM M (-S) (-(star S)) R) = blockCLM (-M) S (star S) (-R) by
        ext z
        apply WithLp.ofLp_injective
        ext <;> simp [blockCLM_apply, add_comm],
      blockCLM_add]
    simp [sub_eq_add_neg, add_comm]
  /- Step 3: Positivity only needs the real part of the block quadratic form; it is bounded
  below blockwise in `julia_regularized_re_nonneg`. -/
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_def']
  refine ⟨hBregself.sub hXself, fun z => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, hBminusX, blockCLM_apply,
    WithLp.prod_inner_apply]
  exact julia_regularized_re_nonneg S R z.fst z.snd hεpos'

/-- Fixed-Hilbert-space form of `(vi) → (ii)` in Theorem 5.1.8.  It derives
the Jensen contraction inequality from operator monotonicity of `-f`, using a
Julia-block dilation followed by a regularized limiting argument.
Source: Hiai–Yanagi, Theorem 5.1.8. -/
theorem conditionVI_implies_conditionII_fixed {f : ℝ → ℝ}
    (hf : ContinuousOn f (halfOpenRay ⊤))
    (hneg : ∀ t ∈ halfOpenRay ⊤, f t ≤ 0)
    (hVI : ConditionVI.{u} f)
    {A C : L K}
    (hA : IsSelfAdjoint A)
    (hσA : spectrum ℝ A ⊆ halfOpenRay ⊤)
    (hC : ‖C‖ ≤ 1) :
    cfcR (ℋ := K) f (star C * A * C) ≤ star C * cfcR (ℋ := K) f A * C := by
  /- Step 1: Build the Julia dilation of C so the compression appears as the first block. -/
  haveI : Nontrivial K := HansenPedersen.nontrivial_of_nontrivial_L
  haveI : Nontrivial (WithLp 2 (K × K)) := inferInstance
  have hA0 : (0 : L K) ≤ A := by
    exact nonneg_of_isSelfAdjoint_of_spectrum_subset_Ici hA (by simpa [halfOpenRay_top] using hσA)
  let E : L K := HansenPedersen.ConvexityCharacterization.defectLeft (K := K) C
  let D : L K := HansenPedersen.ConvexityCharacterization.defectRight (K := K) C
  let M : L K := star C * A * C
  let R : L K := E * A * E
  let S : L K := star C * A * E
  let A0 : L (WithLp 2 (K × K)) := HansenPedersen.Internal.diagMapCLM A 0
  let U0 : L (WithLp 2 (K × K)) := blockCLM C (-E) D (star C)
  let U : unitary (L (WithLp 2 (K × K))) := ⟨U0,
    HansenPedersen.ConvexityCharacterization.julia_block_mem_unitary (K := K) hC⟩
  let X : L (WithLp 2 (K × K)) := star (↑U : L (WithLp 2 (K × K))) * A0 * (↑U : L _)
  have hEstar : star E = E :=
    (HansenPedersen.ConvexityCharacterization.defectLeft_selfAdjoint (K := K) C).star_eq
  have hDstar : star D = D :=
    (HansenPedersen.ConvexityCharacterization.defectRight_selfAdjoint (K := K) C).star_eq
  have hA0self : IsSelfAdjoint A0 :=
    HansenPedersen.Internal.isSelfAdjoint_diagMapCLM hA (IsSelfAdjoint.zero _)
  have hσA0 : spectrum ℝ A0 ⊆ halfOpenRay ⊤ := by
    simpa [A0] using spectrum_diagMapCLM_subset_halfOpenRay
      (K := K) hA (IsSelfAdjoint.zero _) hσA spectrum_zero_subset_halfOpenRay_top
  have hXself : IsSelfAdjoint X := hA0self.conjugate' _
  have hσX : spectrum ℝ X ⊆ halfOpenRay ⊤ :=
    (Unitary.spectrum_star_left_conjugate (R := ℝ) (a := A0) (U := U)).trans_subset hσA0
  have hM0 : (0 : L K) ≤ M := by
    simpa [M] using star_left_conjugate_nonneg hA0 C
  have hMself : IsSelfAdjoint M := by
    simpa [M] using star_mul_selfAdjoint_mul (K := K) (T := A) (C := C) hA
  have hR0 : (0 : L K) ≤ R := by
    simpa [R, E, hEstar] using star_left_conjugate_nonneg hA0 E
  have hRself : IsSelfAdjoint R := by
    simpa [R, E, hEstar] using star_mul_selfAdjoint_mul (K := K) (T := A) (C := E) hA
  /- Step 2: Identify the dilated conjugate X as a Julia block with compression and defect terms. -/
  have hXblock :
      X = blockCLM M (-S) (-(star S)) R := by
    dsimp [X, U, U0, A0, M, R, S, E]
    rw [show HansenPedersen.Internal.diagMapCLM A 0 = blockCLM A 0 0 0 by
      simp [blockCLM_zero_zero]]
    rw [blockCLM_star, blockCLM_mul, blockCLM_mul]
    simp [E, D, hEstar, hDstar, mul_assoc, add_comm, hA.star_eq]
  /- Step 3: Dominate X by a regularized diagonal block and use monotonicity of -f. -/
  let Bε : ℝ → L (WithLp 2 (K × K)) := fun ε =>
    HansenPedersen.Internal.diagMapCLM (M + ε • (1 : L K))
      (((‖R‖ + ‖S‖ ^ 2 / ε + 1 : ℝ)) • (1 : L K))
  have hEventually :
      ∀ᶠ ε : ℝ in 𝓝[Set.Ioi (0 : ℝ)] 0,
        cfcR (ℋ := K) f (M + ε • (1 : L K)) ≤ star C * cfcR (ℋ := K) f A * C := by
    have hsmall :
        Set.Ioi (0 : ℝ) ∩ Set.Iio 1 ∈ 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ) := by
      refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ?_
      refine ⟨Set.Iio (1 : ℝ), Iio_mem_nhds zero_lt_one, ?_⟩
      intro ε hε
      exact ⟨hε.2, hε.1⟩
    refine Filter.mem_of_superset hsmall ?_
    intro ε hε
    rcases hε with ⟨hεpos, hεlt1⟩
    have hεpos' : 0 < ε := hεpos
    have hεlt1' : ε < 1 := hεlt1
    let μ : ℝ := ‖R‖ + ‖S‖ ^ 2 / ε + 1
    have hμpos : 0 < μ := by
      dsimp [μ]
      positivity
    have hMεself : IsSelfAdjoint (M + ε • (1 : L K)) := by
      exact hMself.add ((IsSelfAdjoint.all ε).smul (IsSelfAdjoint.one _))
    have hμself : IsSelfAdjoint (((μ : ℝ)) • (1 : L K)) := by
      exact ((IsSelfAdjoint.all μ).smul (IsSelfAdjoint.one _))
    have hσMε : spectrum ℝ (M + ε • (1 : L K)) ⊆ halfOpenRay ⊤ := by
      exact spectrum_subset_halfOpenRay_top_of_nonneg (ℋ := K) (add_nonneg hM0 (by
        simpa [Algebra.algebraMap_eq_smul_one] using
          smul_nonneg hεpos'.le (show (0 : L K) ≤ (1 : L K) by exact zero_le_one)))
    have hσμ : spectrum ℝ (((μ : ℝ)) • (1 : L K)) ⊆ halfOpenRay ⊤ := by
      exact spectrum_subset_halfOpenRay_top_of_nonneg (ℋ := K) (by
        simpa [Algebra.algebraMap_eq_smul_one] using
          smul_nonneg hμpos.le (show (0 : L K) ≤ (1 : L K) by exact zero_le_one))
    have hBεself : IsSelfAdjoint (Bε ε) :=
      HansenPedersen.Internal.isSelfAdjoint_diagMapCLM hMεself hμself
    have hσBε : spectrum ℝ (Bε ε) ⊆ halfOpenRay ⊤ :=
      spectrum_diagMapCLM_subset_halfOpenRay (K := K) hMεself hμself hσMε hσμ
    have hXleB : X ≤ Bε ε := by
      rw [hXblock]
      dsimp [Bε]
      exact julia_block_le_regularized_diag hMself (by rw [← hXblock]; exact hXself) hεpos'
    have hVIblock := hVI (WithLp 2 (K × K))
    have hmono := hVIblock hXself hBεself hσX hσBε hXleB
    have hmonf :
        cfcR (ℋ := WithLp 2 (K × K)) f (Bε ε) ≤
          cfcR (ℋ := WithLp 2 (K × K)) f X := by
      simpa [cfcR, cfc_neg] using hmono
    let F0 : L (WithLp 2 (K × K)) :=
      HansenPedersen.Internal.diagMapCLM (cfcR (ℋ := K) f A) (cfcR (ℋ := K) f 0)
    /- Step 4: Compute the functional calculus of the regularized diagonal block componentwise. -/
    have hcfB :
        cfcR (ℋ := WithLp 2 (K × K)) f (Bε ε) =
          HansenPedersen.Internal.diagMapCLM (cfcR (ℋ := K) f (M + ε • (1 : L K)))
            (cfcR (ℋ := K) f (((μ : ℝ)) • (1 : L K))) := by
      have hcfB' := cfcR_diagMapCLM (K := K) hf hMεself hμself hσMε hσμ
      simpa [Bε] using hcfB'
    have hcfA0 :
        cfcR (ℋ := WithLp 2 (K × K)) f A0 = F0 := by
      have hcfA0' := cfcR_diagMapCLM (K := K) hf hA (IsSelfAdjoint.zero _)
        hσA spectrum_zero_subset_halfOpenRay_top
      simpa [A0, F0] using hcfA0'
    /- Step 5: Transport f(A0) through the unitary and expand the block matrix. -/
    have hcfX :
        cfcR (ℋ := WithLp 2 (K × K)) f X =
          star (↑U : L (WithLp 2 (K × K))) * F0 * (↑U : L _) := by
      rw [← hcfA0]
      exact cfcR_unitary_conj (K := WithLp 2 (K × K)) hf hA0self hσA0 U
    have hcfXblock :
        cfcR (ℋ := WithLp 2 (K × K)) f X =
          blockCLM
            (star C * cfcR (ℋ := K) f A * C + D * cfcR (ℋ := K) f 0 * D)
            (-(star C * cfcR (ℋ := K) f A * E) + D * cfcR (ℋ := K) f 0 * star C)
            (-(E * cfcR (ℋ := K) f A * C) + C * cfcR (ℋ := K) f 0 * D)
            (E * cfcR (ℋ := K) f A * E + C * cfcR (ℋ := K) f 0 * star C) := by
      rw [hcfX]
      dsimp [F0, U, U0]
      rw [show HansenPedersen.Internal.diagMapCLM (cfcR (ℋ := K) f A) (cfcR (ℋ := K) f 0) =
            blockCLM (cfcR (ℋ := K) f A) 0 0 (cfcR (ℋ := K) f 0) by
            simp [blockCLM_zero_zero]]
      rw [blockCLM_star, blockCLM_mul, blockCLM_mul]
      simp [E, D, hEstar, hDstar, mul_assoc, add_comm]
    have hdiag :
        HansenPedersen.Internal.diagMapCLM
            (cfcR (ℋ := K) f (M + ε • (1 : L K)))
            (cfcR (ℋ := K) f (((μ : ℝ)) • (1 : L K))) ≤
          blockCLM
            (star C * cfcR (ℋ := K) f A * C + D * cfcR (ℋ := K) f 0 * D)
            (-(star C * cfcR (ℋ := K) f A * E) + D * cfcR (ℋ := K) f 0 * star C)
            (-(E * cfcR (ℋ := K) f A * C) + C * cfcR (ℋ := K) f 0 * D)
            (E * cfcR (ℋ := K) f A * E + C * cfcR (ℋ := K) f 0 * star C) := by
      rw [hcfB, hcfXblock] at hmonf
      exact hmonf
    have hcf0_nonpos : cfcR (ℋ := K) f (0 : L K) ≤ 0 := by
      exact cfcR_nonpos_of_nonpos (K := K) hf (show (0 : L K) ≤ (0 : L K) by exact le_rfl) hneg
    /- Step 6: Extract the first diagonal block and drop the nonpositive defect contribution. -/
    have hDterm_nonpos : D * cfcR (ℋ := K) f 0 * D ≤ 0 := by
      calc
        D * cfcR (ℋ := K) f 0 * D = (f 0 : ℝ) • (D * D) := by
          simp [cfcR, Algebra.algebraMap_eq_smul_one, D]
        _ ≤ (0 : ℝ) • (D * D) := by
          have hf0 : f 0 ≤ 0 := hneg 0 (by simp [halfOpenRay_top])
          exact smul_le_smul_of_nonneg_right hf0
            (by simpa [D, hDstar] using star_mul_self_nonneg D)
        _ = 0 := by simp
    have hleftSelf :
        IsSelfAdjoint (cfcR (ℋ := K) f (M + ε • (1 : L K))) := by
      change IsSelfAdjoint (cfc (R := ℝ) f (M + ε • (1 : L K)))
      exact IsSelfAdjoint.cfc (R := ℝ) (A := L K) (f := f) (a := M + ε • (1 : L K))
    have hcfAself : IsSelfAdjoint (cfcR (ℋ := K) f A) := by
      change IsSelfAdjoint (cfc (R := ℝ) f A)
      exact IsSelfAdjoint.cfc (R := ℝ) (A := L K) (f := f) (a := A)
    have hcf0self : IsSelfAdjoint (cfcR (ℋ := K) f 0) := by
      change IsSelfAdjoint (cfc (R := ℝ) f (0 : L K))
      exact IsSelfAdjoint.cfc (R := ℝ) (A := L K) (f := f) (a := (0 : L K))
    have hrightSelf :
        IsSelfAdjoint (star C * cfcR (ℋ := K) f A * C + D * cfcR (ℋ := K) f 0 * D) := by
      exact
        (star_mul_selfAdjoint_mul (K := K) (T := cfcR (ℋ := K) f A) (C := C) hcfAself).add
        (by
          simpa [D, hDstar] using
            (star_mul_selfAdjoint_mul (K := K) (T := cfcR (ℋ := K) f 0) (C := D)
              hcf0self))
    let P : L K := star C * cfcR (ℋ := K) f A * C
    have hblock :
        cfcR (ℋ := K) f (M + ε • (1 : L K)) ≤
          P + D * cfcR (ℋ := K) f 0 * D := by
      simpa [P] using fst_le_of_diag_le_block (K := K) hleftSelf hrightSelf hdiag
    have hdrop0 :
        P + D * cfcR (ℋ := K) f 0 * D ≤ P + 0 := by
      exact add_le_add_right hDterm_nonpos P
    have hdrop :
        P + D * cfcR (ℋ := K) f 0 * D ≤ P := by
      exact le_trans hdrop0 (le_of_eq (add_zero P))
    change cfcR (ℋ := K) f (M + ε • (1 : L K)) ≤ P
    exact le_trans hblock hdrop
  /- Step 7: Let ε tend to zero to pass from the regularized compression back to C^* A C. -/
  have hMβ : M ≤ (‖A‖ : ℝ) • (1 : L K) := by
    change star C * A * C ≤ (‖A‖ : ℝ) • (1 : L K)
    exact compressed_le_norm_smul_one (K := K) hA hC
  change cfcR (ℋ := K) f (star C * A * C) ≤ star C * cfcR (ℋ := K) f A * C
  exact regularized_limit_le (K := K) (A := A) (M := M) (C := C)
    hf hM0 hMself hMβ hEventually
end ConditionVItoII
end ConvexityCharacterization
end HansenPedersen
