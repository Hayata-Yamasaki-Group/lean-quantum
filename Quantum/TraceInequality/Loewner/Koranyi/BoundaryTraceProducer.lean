import Quantum.TraceInequality.Loewner.Koranyi.BoundaryTraceCore
import Quantum.TraceInequality.Loewner.Koranyi.BoundaryTraceInsideMass
import Quantum.TraceInequality.Loewner.Koranyi.SignedEvalAxis
import Quantum.TraceInequality.Loewner.Koranyi.SignedPointsSplitPackage
import Quantum.TraceInequality.Loewner.Koranyi.DyadicMassZero

namespace Quantum.TraceInequality.Loewner

open Filter MeasureTheory

open scoped NNReal
open scoped Topology

noncomputable section

/-!
# Signed-axis inside/outside producer contracts

This file still does not prove the analytic inside/outside estimates.  It
records the small consumer layer: if the signed-axis inside contribution
vanishes and the outside contribution converges to the Cayley/Koranyi
candidate, then the candidate identification needed by `BoundaryTraceCore`
follows.

The actual inside/outside terms are currently implemented by reusing the
signed-points split definitions internally.  They are exposed here only through
responsibility-named interfaces.
-/

/-- The signed-axis inside correction term, restricted to `[-1, 1]`. -/
def signedAxisInsideTerm {f : ℝ → ℝ} (pkg : StrictApproxSignedEvalPackage f)
    {x : ℝ} (axis : SignedEvalAxis pkg x) (n : ℕ) : ℝ :=
  _root_.Quantum.TraceInequality.Loewner.corrIccR
    (pkg.μn (pkg.φ n)) (signedPoints (pkg.φ n) (axis.i n))

/-- The signed-axis outside term, restricted to the complement of `[-1, 1]`. -/
def signedAxisOutsideTerm {f : ℝ → ℝ} (pkg : StrictApproxSignedEvalPackage f)
    {x : ℝ} (axis : SignedEvalAxis pkg x) (n : ℕ) : ℝ :=
  _root_.Quantum.TraceInequality.Loewner.outIccR
    (pkg.μn (pkg.φ n)) (signedPoints (pkg.φ n) (axis.i n))

/-- The real Cayley/Koranyi candidate associated with a strict approximation package. -/
def signedAxisCandidateReal {f : ℝ → ℝ} (pkg : StrictApproxSignedEvalPackage f)
    (x : ℝ) : ℝ :=
  ((ratioFunctional pkg.ν (Real.toNNReal (cayley x)) : ℝ≥0) : ℝ)

/-- Inside contribution vanishes along the chosen signed axis. -/
structure SignedAxisInsideVanishing {f : ℝ → ℝ}
    (pkg : StrictApproxSignedEvalPackage f) {x : ℝ}
    (axis : SignedEvalAxis pkg x) : Prop where
  tendsto_zero :
    Tendsto (fun n => signedAxisInsideTerm pkg axis n) atTop (𝓝 0)

/-- Outside contribution converges to the Cayley/Koranyi candidate along the same axis. -/
structure SignedAxisOutsideConvergence {f : ℝ → ℝ}
    (pkg : StrictApproxSignedEvalPackage f) {x : ℝ}
    (axis : SignedEvalAxis pkg x) : Prop where
  tendsto_candidate :
    Tendsto (fun n => signedAxisOutsideTerm pkg axis n) atTop
      (𝓝 (signedAxisCandidateReal pkg x))

/-- If the inside mass is eventually zero on the signed backbone, the inside contribution
vanishes along the signed axis. -/
theorem signedAxisInsideVanishing_of_eventually_measure_Icc_eq_zero
    {f : ℝ → ℝ} {pkg : StrictApproxSignedEvalPackage f} {x : ℝ}
    (axis : SignedEvalAxis pkg x)
    (hIcc : ∀ᶠ n in atTop,
      pkg.μn (pkg.φ n) _root_.Quantum.TraceInequality.Loewner.closedUnitInterval = 0) :
    SignedAxisInsideVanishing pkg axis := by
  refine ⟨?_⟩
  have hzero :
      (fun n => signedAxisInsideTerm pkg axis n) =ᶠ[atTop] fun _n => (0 : ℝ) := by
    filter_upwards [hIcc] with n hn
    simp [signedAxisInsideTerm, _root_.Quantum.TraceInequality.Loewner.corrIccR,
      Measure.restrict_eq_zero.mpr hn]
  exact tendsto_const_nhds.congr' hzero.symm

private lemma denom_lower_bound_of_closedUnitInterval
    {r y t : ℝ} (hr0 : 0 ≤ r)
    (hy : y ∈ Set.Icc (-r) r) (ht : t ∈ _root_.Quantum.TraceInequality.Loewner.closedUnitInterval) :
    1 - r ≤ |1 - y * t| := by
  have ht_abs : |t| ≤ 1 := abs_le.2 ht
  have hy_abs : |y| ≤ r := abs_le.2 hy
  have hyt_abs : |y * t| ≤ r := by
    calc
      |y * t| = |y| * |t| := by simp [abs_mul]
      _ ≤ r * 1 := by gcongr
      _ = r := by simp
  have h' : (1 : ℝ) - |y * t| ≤ |1 - y * t| := by
    simpa [abs_one] using (abs_sub_abs_le_abs_sub (1 : ℝ) (y * t))
  have h1 : 1 - r ≤ 1 - |y * t| := sub_le_sub_left hyt_abs _
  exact le_trans h1 h'

private lemma abs_oneSubMulKernelR_le_of_Icc
    {r y t : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hy : y ∈ Set.Icc (-r) r) (ht : t ∈ _root_.Quantum.TraceInequality.Loewner.closedUnitInterval) :
    |_root_.Quantum.TraceInequality.Loewner.oneSubMulKernelR y t| ≤ 1 / (1 - r) := by
  have hden : 1 - r ≤ |1 - y * t| :=
    denom_lower_bound_of_closedUnitInterval (r := r) (y := y) (t := t) hr0 hy ht
  have hpos : 0 < 1 - r := sub_pos.mpr hr1
  calc
    |_root_.Quantum.TraceInequality.Loewner.oneSubMulKernelR y t|
        = |(1 : ℝ) / (1 - y * t)| := by
          simp [_root_.Quantum.TraceInequality.Loewner.oneSubMulKernelR]
    _ = 1 / |1 - y * t| := by
          simp
    _ ≤ 1 / (1 - r) := by
          exact one_div_le_one_div_of_le hpos hden

private lemma norm_corrIccR_le_mass
    (μ : Measure ℝ) {y r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hy : y ∈ Set.Icc (-r) r) (hμ : μ Set.univ < ⊤) :
    ‖_root_.Quantum.TraceInequality.Loewner.corrIccR μ y‖ ≤
      (1 / (1 - r)) *
        (μ _root_.Quantum.TraceInequality.Loewner.closedUnitInterval).toReal := by
  haveI : IsFiniteMeasure (μ.restrict _root_.Quantum.TraceInequality.Loewner.closedUnitInterval) :=
    ⟨lt_of_le_of_lt
        (Measure.restrict_le_self (μ := μ)
          (s := _root_.Quantum.TraceInequality.Loewner.closedUnitInterval) Set.univ)
        hμ⟩
  have hs : MeasurableSet _root_.Quantum.TraceInequality.Loewner.closedUnitInterval :=
    isClosed_Icc.measurableSet
  have h_ae :
      ∀ᵐ t : ℝ ∂(μ.restrict _root_.Quantum.TraceInequality.Loewner.closedUnitInterval),
        ‖_root_.Quantum.TraceInequality.Loewner.oneSubMulKernelR y t‖ ≤ (1 / (1 - r)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hs] with t ht
    have hbound :=
      abs_oneSubMulKernelR_le_of_Icc (r := r) (y := y) (t := t) hr0 hr1 hy ht
    simpa [Real.norm_eq_abs] using hbound
  have hnorm :
      ‖_root_.Quantum.TraceInequality.Loewner.corrIccR μ y‖ ≤
        (1 / (1 - r)) *
          (μ.restrict _root_.Quantum.TraceInequality.Loewner.closedUnitInterval).real Set.univ := by
    simpa [_root_.Quantum.TraceInequality.Loewner.corrIccR] using
      (MeasureTheory.norm_integral_le_of_norm_le_const
        (μ := μ.restrict _root_.Quantum.TraceInequality.Loewner.closedUnitInterval)
        (f := fun t : ℝ => _root_.Quantum.TraceInequality.Loewner.oneSubMulKernelR y t)
        (C := (1 / (1 - r))) h_ae)
  have hmass :
      (μ.restrict _root_.Quantum.TraceInequality.Loewner.closedUnitInterval).real Set.univ =
        (μ _root_.Quantum.TraceInequality.Loewner.closedUnitInterval).toReal := by
    simp [Measure.real]
  simpa [hmass] using hnorm

/-- Inside mass decay on `[-1,1]` forces the signed-axis inside correction to vanish. -/
theorem signedAxisInsideVanishing_of_insideMassDecay
    {f : ℝ → ℝ} {pkg : StrictApproxSignedEvalPackage f} {x : ℝ}
    (axis : SignedEvalAxis pkg x) (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (hdecay : SignedAxisInsideMassDecay pkg) :
    SignedAxisInsideVanishing pkg axis := by
  refine ⟨?_⟩
  let r : ℝ := (|x| + 1) / 2
  have hx_abs_lt : |x| < 1 := abs_lt.2 hx
  have hr0 : 0 ≤ r := by
    dsimp [r]
    nlinarith [abs_nonneg x]
  have hr1 : r < 1 := by
    dsimp [r]
    linarith
  have hx_r : |x| < r := by
    dsimp [r]
    linarith
  have hAbsT :
      Tendsto
        (fun n => |signedPoints (pkg.φ n) (axis.i n)|)
        atTop (𝓝 |x|) :=
    (continuous_abs.tendsto x).comp axis.tendsto_signed
  have hEventuallyAbs :
      ∀ᶠ n in atTop, |signedPoints (pkg.φ n) (axis.i n)| < r :=
    hAbsT.eventually (Iio_mem_nhds hx_r)
  have hBound :
      ∀ᶠ n in atTop,
        ‖signedAxisInsideTerm pkg axis n‖ ≤
          (1 / (1 - r)) *
            (pkg.μn (pkg.φ n)
              _root_.Quantum.TraceInequality.Loewner.closedUnitInterval).toReal := by
    filter_upwards [hEventuallyAbs] with n hn
    have hy : signedPoints (pkg.φ n) (axis.i n) ∈ Set.Icc (-r) r := by
      exact abs_le.1 (le_of_lt hn)
    have hμfinite : pkg.μn (pkg.φ n) Set.univ < ⊤ :=
      lt_of_le_of_lt (pkg.hμle (pkg.φ n)) pkg.hM0
    simpa [signedAxisInsideTerm] using
      norm_corrIccR_le_mass (μ := pkg.μn (pkg.φ n))
        (y := signedPoints (pkg.φ n) (axis.i n))
        (r := r) hr0 hr1 hy hμfinite
  have hUpper :
      Tendsto
        (fun n =>
          (1 / (1 - r)) *
            (pkg.μn (pkg.φ n) _root_.Quantum.TraceInequality.Loewner.closedUnitInterval).toReal)
        atTop (𝓝 0) := by
    simpa using hdecay.tendsto_zero.const_mul (1 / (1 - r))
  have hNorm :
      Tendsto (fun n => ‖signedAxisInsideTerm pkg axis n‖) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) hBound hUpper
  exact tendsto_zero_iff_norm_tendsto_zero.2 hNorm

/-- A Chapter 27-style inverse-square bound for each signed-backbone measure gives inside
vanishing along the signed axis. -/
theorem signedAxisInsideVanishing_of_uniform_sqInvDist_bound
    {f : ℝ → ℝ} {pkg : StrictApproxSignedEvalPackage f} {x : ℝ}
    (axis : SignedEvalAxis pkg x) {K : ℕ → ENNReal}
    (hK : ∀ n, K n < ⊤)
    (hbound : ∀ n m k, k ∈ _root_.Quantum.TraceInequality.Loewner.dyadicCenters m →
      (∫⁻ y,
          _root_.Quantum.TraceInequality.Loewner.sqInvDist
            (_root_.Quantum.TraceInequality.Loewner.dyadicCenter m k) y
          ∂(pkg.μn (pkg.φ n))) ≤ K n) :
    SignedAxisInsideVanishing pkg axis :=
  signedAxisInsideVanishing_of_eventually_measure_Icc_eq_zero axis
    (Filter.Eventually.of_forall fun n => by
      simpa [_root_.Quantum.TraceInequality.Loewner.closedUnitInterval] using
        _root_.Quantum.TraceInequality.Loewner.measure_Icc_eq_zero_of_uniform_sqInvDist_bound
          (μ := pkg.μn (pkg.φ n)) (K := K n) (hK := hK n) (hKbound := hbound n))

/-- The still-open Chapter 27 inverse-square obligation for the signed backbone. -/
structure SignedAxisUniformSqInvDistBound {f : ℝ → ℝ}
    (pkg : StrictApproxSignedEvalPackage f) where
  K : ℕ → ENNReal
  hK : ∀ n, K n < ⊤
  bound : ∀ n m k, k ∈ _root_.Quantum.TraceInequality.Loewner.dyadicCenters m →
    (∫⁻ y,
        _root_.Quantum.TraceInequality.Loewner.sqInvDist
          (_root_.Quantum.TraceInequality.Loewner.dyadicCenter m k) y
        ∂(pkg.μn (pkg.φ n))) ≤ K n

/-- A signed-backbone inverse-square contract forces inside mass decay. -/
theorem signedAxisInsideMassDecay_of_uniform_sqInvDist_contract
    {f : ℝ → ℝ} {pkg : StrictApproxSignedEvalPackage f}
    (hbound : SignedAxisUniformSqInvDistBound pkg) :
    SignedAxisInsideMassDecay pkg :=
  signedAxisInsideMassDecay_of_eventually_measure_Icc_eq_zero
    (Filter.Eventually.of_forall fun n => by
      simpa [_root_.Quantum.TraceInequality.Loewner.closedUnitInterval] using
        _root_.Quantum.TraceInequality.Loewner.measure_Icc_eq_zero_of_uniform_sqInvDist_bound
          (μ := pkg.μn (pkg.φ n)) (K := hbound.K n) (hK := hbound.hK n)
          (hKbound := hbound.bound n))

/-- A signed-backbone inverse-square contract is enough to close inside vanishing. -/
theorem signedAxisInsideVanishing_of_uniform_sqInvDist_contract
    {f : ℝ → ℝ} {pkg : StrictApproxSignedEvalPackage f} {x : ℝ}
    (axis : SignedEvalAxis pkg x)
    (hbound : SignedAxisUniformSqInvDistBound pkg) :
    SignedAxisInsideVanishing pkg axis :=
  signedAxisInsideVanishing_of_uniform_sqInvDist_bound axis hbound.hK hbound.bound

/-- The finite-dimensional signed evaluation identity splits into outside and inside terms. -/
theorem signedEvalAxis_kernel_eq_outside_add_inside_eventually
    {f : ℝ → ℝ} {pkg : StrictApproxSignedEvalPackage f} {x : ℝ}
    (axis : SignedEvalAxis pkg x) :
    ∀ᶠ n in atTop,
      loewnerKernel f (signedPoints (pkg.φ n) (axis.i n)) 0 =
        signedAxisOutsideTerm pkg axis n + signedAxisInsideTerm pkg axis n := by
  filter_upwards [axis.hi0] with n hn
  exact
    _root_.Quantum.TraceInequality.Loewner.signedPoints_split_eq_from_single_package_R
      (f := f) (μn := pkg.μn) (φ := pkg.φ)
      pkg.hEvalSigned pkg.hKernelIntegrableSubseq n (axis.i n) hn

/-- Inside/outside convergence along a signed axis identifies the Cayley/Koranyi candidate. -/
theorem boundaryTraceCandidateIdentification_of_signedAxisSplit
    {f : ℝ → ℝ} {pkg : StrictApproxSignedEvalPackage f} {x : ℝ}
    (axis : SignedEvalAxis pkg x)
    (hInside : SignedAxisInsideVanishing pkg axis)
    (hOutside : SignedAxisOutsideConvergence pkg axis) :
    BoundaryTraceCandidateIdentification pkg.toStrictApproxPackage x := by
  have hsum :
      Tendsto
        (fun n => signedAxisOutsideTerm pkg axis n + signedAxisInsideTerm pkg axis n)
        atTop (𝓝 (signedAxisCandidateReal pkg x + 0)) :=
    hOutside.tendsto_candidate.add hInside.tendsto_zero
  have hsplit := signedEvalAxis_kernel_eq_outside_add_inside_eventually (pkg := pkg) axis
  have hsum_kernel :
      Tendsto
        (fun n => signedAxisOutsideTerm pkg axis n + signedAxisInsideTerm pkg axis n)
        atTop (𝓝 (loewnerKernel f x 0)) := by
    have heq :
        (fun n => signedAxisOutsideTerm pkg axis n + signedAxisInsideTerm pkg axis n) =ᶠ[atTop]
          (fun n => loewnerKernel f (signedPoints (pkg.φ n) (axis.i n)) 0) := by
      filter_upwards [hsplit] with n hn
      exact hn.symm
    exact axis.tendsto_kernel.congr' heq.symm
  have hreal :
      signedAxisCandidateReal pkg x = loewnerKernel f x 0 := by
    simpa using tendsto_nhds_unique hsum hsum_kernel
  refine ⟨?_⟩
  rw [← hreal]
  simp [signedAxisCandidateReal]

end

end Loewner
end TraceInequality
end Quantum
