import Quantum.Analysis.Measure.Stieltjes
import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.DominatedData

/-!
# Chapter 20 Ioc step pairing core

This file contains the Stieltjes/BV pairing diagnostics and finite half-open
step handoff lemmas that precede the uniform mesh construction.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped Interval
open scoped ComplexOrder
open scoped MatrixOrder
open scoped NNReal
open scoped ENNReal

noncomputable section

/--
The clipped extension agrees with `f` on every point sampled by the Hiai
regularization integral.
-/
theorem hiaiLocalClip_eq_shift
    {f : ℝ → ℝ} {ε x t : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    hiaiLocalClip f (x - ε) (x + ε) (x - ε * t) = f (x - ε * t) := by
  have hmul_le : ε * t ≤ ε := by
    simpa using mul_le_mul_of_nonneg_left ht.2 hε
  have hneg_le : -ε ≤ ε * t := by
    have h := mul_le_mul_of_nonneg_left ht.1 hε
    simpa using h
  exact hiaiLocalClip_eq_on_Icc
    (f := f) (a := x - ε) (b := x + ε) (y := x - ε * t)
    ⟨by linarith, by linarith⟩

/--
On the open part of the regularization carrier, the derivative of the clipped
extension agrees with the derivative of `f` at the sampled point.
-/
theorem hiaiLocalClip_deriv_eq_shift
    {f : ℝ → ℝ} {ε x t : ℝ} (hε : 0 < ε) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (hiaiLocalClip f (x - ε) (x + ε)) (x - ε * t) =
      deriv f (x - ε * t) := by
  have hmul_lt : ε * t < ε := by
    simpa using mul_lt_mul_of_pos_left ht.2 hε
  have hneg_lt : -ε < ε * t := by
    have h := mul_lt_mul_of_pos_left ht.1 hε
    simpa using h
  exact hiaiLocalClip_deriv_eq_on_Ioo
    (f := f) (a := x - ε) (b := x + ε) (y := x - ε * t)
    ⟨by linarith, by linarith⟩

/--
On the mollifier carrier, the absolutely continuous derivative of the clipped
extension gives the same interval integral as the averaged diagonal Löwner
kernel of `f`.  The equality is only used under the integral, so endpoint
values of the clipped derivative are irrelevant.
-/
theorem hiaiLocalClip_diagKernel_intervalIntegral_eq
    {φ f : ℝ → ℝ} {ε x : ℝ} (hε : 0 < ε) :
    (∫ t in (-1 : ℝ)..1,
        φ t * loewnerKernel f (x - ε * t) (x - ε * t)) =
      ∫ t in (-1 : ℝ)..1,
        φ t * deriv (hiaiLocalClip f (x - ε) (x + ε)) (x - ε * t) := by
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume (-1 : ℝ), Measure.ae_ne volume (1 : ℝ)] with
    t ht_left ht_right ht
  have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
    have ht_uIcc : t ∈ [[(-1 : ℝ), 1]] := Set.uIoc_subset_uIcc ht
    simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht_uIcc
  have htIoo : t ∈ Set.Ioo (-1 : ℝ) 1 := by
    exact ⟨lt_of_le_of_ne htIcc.1 ht_left.symm, lt_of_le_of_ne htIcc.2 ht_right⟩
  rw [loewnerKernel_self,
    hiaiLocalClip_deriv_eq_shift (f := f) (ε := ε) (x := x) hε htIoo]

/--
For a monotone clipped function, the with-density integral against the
Lebesgue a.c. derivative measure is the ordinary integral weighted by the
pointwise derivative.  This is the measure-theoretic part of the
`withDensity` side of the Hiai diagonal argument.
-/
theorem hiaiLocalClip_acPart_integral_eq_scaledWeight_volume_integral
    {φ g : ℝ → ℝ} {ε x : ℝ} (hg : Monotone g) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂(volume.withDensity (fun y : ℝ => ENNReal.ofReal (deriv g y)))) =
      ∫ y, hiaiScaledMollifierWeight φ ε x y * deriv g y := by
  have hmeas : AEMeasurable (fun y : ℝ => ENNReal.ofReal (deriv g y)) volume := by
    have hae : (fun y : ℝ => ENNReal.ofReal (deriv g y)) =ᵐ[volume]
        (fun y : ℝ => hg.stieltjesFunction.measure.rnDeriv volume y) := by
      filter_upwards [hg.ae_hasDerivAt,
        Measure.rnDeriv_lt_top hg.stieltjesFunction.measure volume] with y hy hfin
      rw [hy.deriv]
      exact ENNReal.ofReal_toReal hfin.ne
    exact (Measure.measurable_rnDeriv hg.stieltjesFunction.measure volume).aemeasurable.congr
      hae.symm
  have htop : ∀ᵐ y : ℝ ∂volume, ENNReal.ofReal (deriv g y) < ⊤ := by
    filter_upwards with y
    simp
  rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas htop]
  have hderiv_nonneg : 0 ≤ᵐ[volume] (fun y : ℝ => deriv g y) := by
    filter_upwards [hg.ae_hasDerivAt] with y hy
    rw [hy.deriv]
    exact ENNReal.toReal_nonneg
  refine integral_congr_ae ?_
  filter_upwards [hderiv_nonneg] with y hy
  simp [ENNReal.toReal_ofReal hy, mul_comm]

/--
The scaled mollifier weight is supported on the window `[x - ε, x + ε]`, so its
ordinary integral may be restricted to that interval.
-/
theorem hiaiScaledMollifierWeight_volume_integral_eq_window
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y * g y) =
      ∫ y in x - ε..x + ε, hiaiScaledMollifierWeight φ ε x y * g y := by
  let F : ℝ → ℝ := fun y => hiaiScaledMollifierWeight φ ε x y * g y
  have hzero : ∀ y : ℝ, y ∉ Set.Icc (x - ε) (x + ε) → F y = 0 := by
    intro y hy
    by_cases hW : hiaiScaledMollifierWeight φ ε x y = 0
    · simp [F, hW]
    · have hywin := hiaiScaledMollifierWeight_mem_window_of_ne_zero
        (φ := φ) hφ hε hW
      exact (hy hywin).elim
  have hset : (∫ y in Set.Icc (x - ε) (x + ε), F y) = ∫ y, F y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := volume) (s := Set.Icc (x - ε) (x + ε)) (f := F) hzero
  have hle : x - ε ≤ x + ε := by linarith
  calc
    (∫ y, hiaiScaledMollifierWeight φ ε x y * g y) = ∫ y, F y := rfl
    _ = ∫ y in Set.Icc (x - ε) (x + ε), F y := hset.symm
    _ = ∫ y in Set.Ioc (x - ε) (x + ε), F y := by
          exact integral_Icc_eq_integral_Ioc
    _ = ∫ y in x - ε..x + ε, F y := by
          rw [intervalIntegral.integral_of_le hle]
    _ = ∫ y in x - ε..x + ε,
          hiaiScaledMollifierWeight φ ε x y * g y := rfl

/--
If the Stieltjes measure agrees with its absolutely continuous derivative part
on the support window of the scaled mollifier weight, then the desired
Stieltjes integration-by-parts identity follows from the already closed volume
integration-by-parts formula.  This is not the public monotone case: it isolates
the BV/Stieltjes step as the replacement of this local absolute continuity
hypothesis.  The monotone case is
`hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_closed`
(`IocUniformStep.lean`).
-/
theorem
    hiaiScaledMollifierWeight_stieltjesIntegrationByParts_identity_of_restrict_acPart
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g)
    (hg_deriv : ∀ y ∈ [[x - ε, x + ε]], HasDerivAt g (deriv g y) y)
    (hW_int : IntervalIntegrable
      (fun y : ℝ => deriv (fun y : ℝ =>
        hiaiScaledMollifierWeight φ ε x y) y)
      volume (x - ε) (x + ε))
    (hg_int : IntervalIntegrable (deriv g) volume (x - ε) (x + ε))
    (hrestrict :
      hg.stieltjesFunction.measure.restrict (Set.Icc (x - ε) (x + ε)) =
        (volume.withDensity (fun y : ℝ => ENNReal.ofReal (deriv g y))).restrict
          (Set.Icc (x - ε) (x + ε))) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂hg.stieltjesFunction.measure) =
      -∫ y in x - ε..x + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y * g y := by
  let W : ℝ → ℝ := hiaiScaledMollifierWeight φ ε x
  let s : Set ℝ := Set.Icc (x - ε) (x + ε)
  let μ : Measure ℝ := hg.stieltjesFunction.measure
  let ν : Measure ℝ := volume.withDensity (fun y : ℝ => ENNReal.ofReal (deriv g y))
  have hzero : ∀ y : ℝ, y ∉ s → W y = 0 := by
    intro y hy
    by_cases hW : W y = 0
    · exact hW
    · have hywin := hiaiScaledMollifierWeight_mem_window_of_ne_zero
        (φ := φ) hφ hε hW
      exact (hy hywin).elim
  have hμ_set : (∫ y in s, W y ∂μ) = ∫ y, W y ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := μ) (s := s) (f := W) hzero
  have hν_set : (∫ y in s, W y ∂ν) = ∫ y, W y ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := ν) (s := s) (f := W) hzero
  have hstieltjes_volume :
      (∫ y, hiaiScaledMollifierWeight φ ε x y
          ∂hg.stieltjesFunction.measure) =
        ∫ y in x - ε..x + ε,
          hiaiScaledMollifierWeight φ ε x y * deriv g y := by
    have hmeasure :
        (∫ y, W y ∂μ) = ∫ y, W y ∂ν := by
      calc
        (∫ y, W y ∂μ) = ∫ y in s, W y ∂μ := hμ_set.symm
        _ = ∫ y in s, W y ∂ν := by
              rw [show μ.restrict s = ν.restrict s by simpa [μ, ν, s] using hrestrict]
        _ = ∫ y, W y ∂ν := hν_set
    have hac :=
      hiaiLocalClip_acPart_integral_eq_scaledWeight_volume_integral
        (φ := φ) (g := g) (ε := ε) (x := x) hg
    have hvol : (∫ y, W y ∂ν) =
        ∫ y, hiaiScaledMollifierWeight φ ε x y * deriv g y := by
      simpa [W, ν] using hac
    have hwindow :=
      hiaiScaledMollifierWeight_volume_integral_eq_window
        (φ := φ) (g := deriv g) (ε := ε) (x := x) hφ hε
    calc
      (∫ y, hiaiScaledMollifierWeight φ ε x y
          ∂hg.stieltjesFunction.measure)
          = ∫ y, W y ∂μ := rfl
      _ = ∫ y, W y ∂ν := hmeasure
      _ = ∫ y, hiaiScaledMollifierWeight φ ε x y * deriv g y := hvol
      _ = ∫ y in x - ε..x + ε,
          hiaiScaledMollifierWeight φ ε x y * deriv g y := hwindow
  exact
    hiaiScaledMollifierWeight_stieltjesIntegrationByParts_identity_of_volumeFormula
      (φ := φ) (g := g) hφ hε hg hg_deriv hW_int hg_int hstieltjes_volume

/--
Diagnostic form of the BV/Stieltjes integration-by-parts step.  If the
full Stieltjes measure pairing with the smooth compactly supported scaled
weight has already been identified with the distributional derivative pairing,
then it has exactly the `hibp` shape used by the downstream Hiai regularization
handoffs.

This differs from
`hiaiScaledMollifierWeight_stieltjesIntegrationByParts_identity_of_volumeFormula`,
which assumes the Stieltjes integral has already been rewritten as an
absolutely continuous volume integral, and from
`hiaiScaledMollifierWeight_stieltjesIntegrationByParts_identity_of_restrict_acPart`,
which obtains that volume formula from a local a.c. equality of measures.  In
the public monotone case the identity, including the singular Stieltjes
contribution, is proved by uniform half-open steps in
`hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_closed`
(`IocUniformStep.lean`).
-/
theorem
    hiaiScaledMollifierWeight_stieltjesIntegrationByParts_identity_of_BVPairing
    {φ g : ℝ → ℝ} {ε x : ℝ} (hg : Monotone g)
    (hBVPairing :
      (∫ y, hiaiScaledMollifierWeight φ ε x y
          ∂hg.stieltjesFunction.measure) =
        ∫ y in x - ε..x + ε,
          (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) * g y) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂hg.stieltjesFunction.measure) =
      -∫ y in x - ε..x + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y * g y := by
  rw [hBVPairing]
  simp_rw [neg_mul]
  rw [intervalIntegral.integral_neg]

/--
If the full Stieltjes/BV pairing has been proved for the right-continuous
Stieltjes representative, then it supplies the `hBVPairing` input for the
original monotone function.  The only extra step is replacing
`hg.stieltjesFunction` by `g` in the Lebesgue interval integral, using the
a.e. equality above.
-/
theorem
    hiaiScaledMollifierWeight_BVPairing_of_rightContinuousRep
    {φ g : ℝ → ℝ} {ε x : ℝ} (hg : Monotone g)
    (hBVPairing_right :
      (∫ y, hiaiScaledMollifierWeight φ ε x y
          ∂hg.stieltjesFunction.measure) =
        ∫ y in x - ε..x + ε,
          (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            hg.stieltjesFunction y) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂hg.stieltjesFunction.measure) =
      ∫ y in x - ε..x + ε,
        (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) * g y := by
  rw [hBVPairing_right]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [monotone_stieltjesFunction_ae_eq hg] with y hy _hywin
  rw [hy]

/--
Right-continuous-representative form of the full Stieltjes/BV IBP identity.
This is a conditional diagnostic: its mathematical input is the BV pairing for
`hg.stieltjesFunction`, but the mismatch between that representative and the
original monotone function has been removed.  The identity itself is proved
by uniform half-open steps in
`hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_closed`
(`IocUniformStep.lean`).
-/
theorem
    hiaiScaledMollifierWeight_IBP_identity_of_rightContinuousRep
    {φ g : ℝ → ℝ} {ε x : ℝ} (hg : Monotone g)
    (hBVPairing_right :
      (∫ y, hiaiScaledMollifierWeight φ ε x y
          ∂hg.stieltjesFunction.measure) =
        ∫ y in x - ε..x + ε,
          (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            hg.stieltjesFunction y) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂hg.stieltjesFunction.measure) =
      -∫ y in x - ε..x + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y * g y := by
  exact
    hiaiScaledMollifierWeight_stieltjesIntegrationByParts_identity_of_BVPairing
      hg
      (hiaiScaledMollifierWeight_BVPairing_of_rightContinuousRep
        (φ := φ) (g := g) (ε := ε) (x := x) hg hBVPairing_right)

/--
Window-local form of the BV/Stieltjes pairing.  Since the scaled
mollifier weight is supported on `[x - ε, x + ε]`, it is enough to prove the
pairing identity on that compact window.  This is conditional on the
Stieltjes/BV pairing on the window itself, where
`StieltjesFunction.measure_Icc` and `StieltjesFunction.measure_Ioc` apply.  The
integration-by-parts identity is proved by uniform half-open steps in
`hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_closed`
(`IocUniformStep.lean`).
-/
theorem
    hiaiScaledMollifierWeight_BVPairing_rightContinuousRep_of_windowPairing
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g)
    (hwindowPairing :
      (∫ y in Set.Icc (x - ε) (x + ε),
          hiaiScaledMollifierWeight φ ε x y
            ∂hg.stieltjesFunction.measure) =
        ∫ y in x - ε..x + ε,
          (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            hg.stieltjesFunction y) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂hg.stieltjesFunction.measure) =
      ∫ y in x - ε..x + ε,
        (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
          hg.stieltjesFunction y := by
  have hzero : ∀ y : ℝ, y ∉ Set.Icc (x - ε) (x + ε) →
      hiaiScaledMollifierWeight φ ε x y = 0 := by
    intro y hy
    by_cases hW : hiaiScaledMollifierWeight φ ε x y = 0
    · exact hW
    · have hywin := hiaiScaledMollifierWeight_mem_window_of_ne_zero
        (φ := φ) hφ hε hW
      exact (hy hywin).elim
  have hset :
      (∫ y in Set.Icc (x - ε) (x + ε),
          hiaiScaledMollifierWeight φ ε x y
            ∂hg.stieltjesFunction.measure) =
        ∫ y, hiaiScaledMollifierWeight φ ε x y
          ∂hg.stieltjesFunction.measure :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := hg.stieltjesFunction.measure)
      (s := Set.Icc (x - ε) (x + ε))
      (f := fun y : ℝ => hiaiScaledMollifierWeight φ ε x y)
      hzero
  calc
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂hg.stieltjesFunction.measure)
        = ∫ y in Set.Icc (x - ε) (x + ε),
            hiaiScaledMollifierWeight φ ε x y
              ∂hg.stieltjesFunction.measure := hset.symm
    _ = ∫ y in x - ε..x + ε,
        (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
          hg.stieltjesFunction y := hwindowPairing

/--
The left endpoint atom of a Stieltjes window does not contribute to the scaled
mollifier weight: the weight is zero at `x - ε`.  Hence the compact-window
Stieltjes integral can be reduced from `Icc` to `Ioc` for any measure.  This is
the endpoint bookkeeping needed before applying `StieltjesFunction.measure_Ioc`.
-/
theorem hiaiScaledMollifierWeight_Icc_integral_eq_Ioc
    {φ : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (μ : Measure ℝ) :
    (∫ y in Set.Icc (x - ε) (x + ε),
        hiaiScaledMollifierWeight φ ε x y ∂μ) =
      ∫ y in Set.Ioc (x - ε) (x + ε),
        hiaiScaledMollifierWeight φ ε x y ∂μ := by
  have hle : x - ε ≤ x + ε := by linarith
  have hzero_left : ∀ y ∈ Set.Icc (x - ε) (x - ε),
      hiaiScaledMollifierWeight φ ε x y = 0 := by
    intro y hy
    have hy_eq : y = x - ε := le_antisymm hy.2 hy.1
    subst y
    exact hiaiScaledMollifierWeight_boundary_left_zero
      (φ := φ) hφ hε
  have hcover :
      Set.Ioc (x - ε) (x + ε) ∪ Set.Icc (x - ε) (x - ε) =
        Set.Icc (x - ε) (x + ε) := by
    rw [Set.union_comm]
    exact Set.Icc_union_Ioc_eq_Icc le_rfl hle
  calc
    (∫ y in Set.Icc (x - ε) (x + ε),
        hiaiScaledMollifierWeight φ ε x y ∂μ)
        = ∫ y in Set.Ioc (x - ε) (x + ε) ∪ Set.Icc (x - ε) (x - ε),
            hiaiScaledMollifierWeight φ ε x y ∂μ := by
          rw [hcover]
    _ = ∫ y in Set.Ioc (x - ε) (x + ε),
          hiaiScaledMollifierWeight φ ε x y ∂μ := by
          exact MeasureTheory.integral_union_eq_left_of_forall
            (μ := μ) (s := Set.Ioc (x - ε) (x + ε))
            (t := Set.Icc (x - ε) (x - ε))
            measurableSet_Icc hzero_left

/--
It is enough to prove the right-continuous Stieltjes pairing on the half-open
window `(x - ε, x + ε]`.  The analytic step after this reduction is the
`Ioc` Stieltjes pairing, where `StieltjesFunction.measure_Ioc` gives the
interval masses; it is carried out by uniform half-open steps in
`hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_closed`
(`IocUniformStep.lean`).
-/
theorem hiaiScaledMollifierWeight_BVPairing_rightContinuousRep_of_IocPairing
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g)
    (hIocPairing :
      (∫ y in Set.Ioc (x - ε) (x + ε),
          hiaiScaledMollifierWeight φ ε x y
            ∂hg.stieltjesFunction.measure) =
        ∫ y in x - ε..x + ε,
          (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            hg.stieltjesFunction y) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂hg.stieltjesFunction.measure) =
      ∫ y in x - ε..x + ε,
        (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
          hg.stieltjesFunction y :=
  hiaiScaledMollifierWeight_BVPairing_rightContinuousRep_of_windowPairing
    (φ := φ) (g := g) hφ hε hg
    (by
      rw [hiaiScaledMollifierWeight_Icc_integral_eq_Ioc
        (φ := φ) hφ hε hg.stieltjesFunction.measure]
      exact hIocPairing)

/--
Half-open-window version of the diagnostic in the downstream `hibp` shape.
The proof using `StieltjesFunction.measure_Ioc` is
`hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_closed`
(`IocUniformStep.lean`), which goes through this theorem.
-/
theorem hiaiScaledMollifierWeight_IBP_identity_of_IocPairing
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g)
    (hIocPairing :
      (∫ y in Set.Ioc (x - ε) (x + ε),
          hiaiScaledMollifierWeight φ ε x y
            ∂hg.stieltjesFunction.measure) =
        ∫ y in x - ε..x + ε,
          (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            hg.stieltjesFunction y) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂hg.stieltjesFunction.measure) =
      -∫ y in x - ε..x + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y * g y := by
  exact
    hiaiScaledMollifierWeight_IBP_identity_of_rightContinuousRep
      (φ := φ) (g := g) (ε := ε) (x := x) hg
      (hiaiScaledMollifierWeight_BVPairing_rightContinuousRep_of_IocPairing
        (φ := φ) (g := g) hφ hε hg hIocPairing)

/--
Version of `stieltjesFunction_integral_const_Ioc` for a test weight
which is constant on the half-open interval.  This keeps the `measure_Ioc`
frontier explicit while avoiding any unsupported full Stieltjes/BV
integration-by-parts theorem.
-/
theorem stieltjesFunction_integral_eq_const_Ioc
    (G : StieltjesFunction ℝ) {a b c : ℝ} {w : ℝ → ℝ} (hab : a ≤ b)
    (hw : Set.EqOn w (fun _ : ℝ => c) (Set.Ioc a b)) :
    (∫ y in Set.Ioc a b, w y ∂G.measure) = c * (G b - G a) := by
  calc
    (∫ y in Set.Ioc a b, w y ∂G.measure)
        = ∫ _y in Set.Ioc a b, c ∂G.measure := by
          exact setIntegral_congr_fun measurableSet_Ioc hw
    _ = c * (G b - G a) :=
          stieltjesFunction_integral_const_Ioc G hab

/--
Whole-space version for a single half-open step atom.  It rewrites the
indicator integral to the set integral over `Ioc`, then uses
`StieltjesFunction.measure_Ioc`.
-/
theorem stieltjesFunction_integral_indicator_const_Ioc
    (G : StieltjesFunction ℝ) {a b c : ℝ} (hab : a ≤ b) :
    (∫ y, (Set.Ioc a b).indicator (fun _ : ℝ => c) y ∂G.measure) =
      c * (G b - G a) := by
  rw [integral_indicator measurableSet_Ioc]
  exact stieltjesFunction_integral_const_Ioc G hab

/--
Finite sums of half-open constant step atoms are evaluated term by term by
`measure_Ioc`.  Disjoint step partitions are the intended downstream use case,
but the integral identity itself follows from finite linearity and does not
need disjointness.
-/
theorem stieltjesFunction_integral_finite_ioc_const_sum
    {ι : Type*} (s : Finset ι) (G : StieltjesFunction ℝ)
    (a b c : ι → ℝ) (hle : ∀ i ∈ s, a i ≤ b i) :
    (∫ y, ∑ i ∈ s,
        (Set.Ioc (a i) (b i)).indicator (fun _ : ℝ => c i) y ∂G.measure) =
      ∑ i ∈ s, c i * (G (b i) - G (a i)) := by
  have hInt : ∀ i ∈ s,
      Integrable
        ((Set.Ioc (a i) (b i)).indicator (fun _ : ℝ => c i))
        G.measure := by
    intro i _hi
    have hμ : G.measure (Set.Ioc (a i) (b i)) ≠ ⊤ := by
      rw [StieltjesFunction.measure_Ioc]
      exact ENNReal.ofReal_ne_top
    exact
      (integrableOn_const (μ := G.measure)
        (s := Set.Ioc (a i) (b i)) (C := c i) hμ).integrable_indicator
        measurableSet_Ioc
  rw [integral_finset_sum s hInt]
  exact Finset.sum_congr rfl fun i hi =>
    stieltjesFunction_integral_indicator_const_Ioc G (hle i hi)

/--
The same finite-step evaluation for the right-continuous Stieltjes
representative attached to a monotone function.  This is a closed building
block for later approximation of the scaled mollifier weight by half-open
step functions.
-/
theorem hiaiScaledMollifierWeight_iocStepPairing_rightContinuousRep
    {ι : Type*} (s : Finset ι) {g : ℝ → ℝ} (hg : Monotone g)
    (a b c : ι → ℝ) (hle : ∀ i ∈ s, a i ≤ b i) :
    (∫ y, ∑ i ∈ s,
        (Set.Ioc (a i) (b i)).indicator (fun _ : ℝ => c i) y
          ∂hg.stieltjesFunction.measure) =
      ∑ i ∈ s,
        c i * (hg.stieltjesFunction (b i) - hg.stieltjesFunction (a i)) :=
  stieltjesFunction_integral_finite_ioc_const_sum
    s hg.stieltjesFunction a b c hle

/--
Finite `Ioc` step evaluations can be used under a limit: if the explicit
Stieltjes increment sums converge to `L`, then the corresponding finite step
integrals converge to the same `L`.
-/
theorem stieltjesFunction_integral_finite_ioc_const_sum_tendsto_pairing
    {ι : Type*} (s : ℕ → Finset ι) (G : StieltjesFunction ℝ)
    (a b c : ℕ → ι → ℝ)
    (hle : ∀ n i, i ∈ s n → a n i ≤ b n i) {L : ℝ}
    (hL :
      Tendsto
        (fun n : ℕ =>
          ∑ i ∈ s n, c n i * (G (b n i) - G (a n i)))
        atTop (𝓝 L)) :
    Tendsto
      (fun n : ℕ =>
        ∫ y, ∑ i ∈ s n,
          (Set.Ioc (a n i) (b n i)).indicator (fun _ : ℝ => c n i) y
            ∂G.measure)
      atTop (𝓝 L) := by
  refine hL.congr' ?_
  exact Filter.Eventually.of_forall fun n =>
    (stieltjesFunction_integral_finite_ioc_const_sum
      (s n) G (a n) (b n) (c n) (fun i hi => hle n i hi)).symm

/--
Limit handoff from finite half-open step approximations to the downstream
Stieltjes integration-by-parts input.  The theorem does not construct the
approximating steps; it only says that once the Stieltjes-integral side and the
finite increment-sum side have the required limits, the existing `hibp` input
follows by uniqueness of limits.
-/
theorem hiaiScaledMollifierWeight_IBP_identity_of_iocStepApproximation
    {ι : Type*} (s : ℕ → Finset ι)
    {φ g : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε) (hg : Monotone g)
    (a b c : ℕ → ι → ℝ)
    (hle : ∀ n i, i ∈ s n → a n i ≤ b n i)
    (hStieltjes :
      Tendsto
        (fun n : ℕ =>
          ∫ y, ∑ i ∈ s n,
            (Set.Ioc (a n i) (b n i)).indicator (fun _ : ℝ => c n i) y
              ∂hg.stieltjesFunction.measure)
        atTop
        (𝓝 (∫ y in Set.Ioc (x - ε) (x + ε),
          hiaiScaledMollifierWeight φ ε x y
            ∂hg.stieltjesFunction.measure)))
    (hPairing :
      Tendsto
        (fun n : ℕ =>
          ∑ i ∈ s n,
            c n i *
              (hg.stieltjesFunction (b n i) - hg.stieltjesFunction (a n i)))
        atTop
        (𝓝 (∫ y in x - ε..x + ε,
          (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            hg.stieltjesFunction y))) :
    (∫ y, hiaiScaledMollifierWeight φ ε x y
        ∂hg.stieltjesFunction.measure) =
      -∫ y in x - ε..x + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y * g y := by
  have hStepToPairing :
      Tendsto
        (fun n : ℕ =>
          ∫ y, ∑ i ∈ s n,
            (Set.Ioc (a n i) (b n i)).indicator (fun _ : ℝ => c n i) y
              ∂hg.stieltjesFunction.measure)
        atTop
        (𝓝 (∫ y in x - ε..x + ε,
          (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            hg.stieltjesFunction y)) :=
    stieltjesFunction_integral_finite_ioc_const_sum_tendsto_pairing
      s hg.stieltjesFunction a b c hle hPairing
  have hIocPairing :
      (∫ y in Set.Ioc (x - ε) (x + ε),
          hiaiScaledMollifierWeight φ ε x y
            ∂hg.stieltjesFunction.measure) =
        ∫ y in x - ε..x + ε,
          (-deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε x y) y) *
            hg.stieltjesFunction y :=
    tendsto_nhds_unique hStieltjes hStepToPairing
  exact
    hiaiScaledMollifierWeight_IBP_identity_of_IocPairing
      (φ := φ) (g := g) hφ hε hg hIocPairing

end

end Quantum.TraceInequality.Loewner
