import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.TwoPointSpectralExtractionCore

/-!
# Chapter 3 concrete two-point spectral formula

This file contains the explicit `2×2` spectral branches and CFC entry
formulae used by the two-point order-ray spectral extraction layer.
-/

namespace Quantum.TraceInequality.Loewner

universe u

noncomputable section

open scoped ComplexOrder
open scoped Matrix
open scoped MatrixOrder
open scoped Matrix.Norms.L2Operator
open scoped Polynomial
open scoped Topology

/--
Trace of the concrete real `2×2` order-ray matrix
`[[x + ε, ε], [ε, y + ε]]`.
-/
def twoPointOrderRayTrace (x y ε : ℝ) : ℝ :=
  x + y + 2 * ε

/--
Spectral gap of the concrete real `2×2` order-ray matrix
`[[x + ε, ε], [ε, y + ε]]`.
-/
def twoPointOrderRayGap (x y ε : ℝ) : ℝ :=
  Real.sqrt ((x - y) ^ 2 + 4 * ε ^ 2)

/-- Lower eigenvalue normal form for the concrete `2×2` order ray. -/
def twoPointOrderRayEigenLow (x y ε : ℝ) : ℝ :=
  (twoPointOrderRayTrace x y ε -
    twoPointOrderRayGap x y ε) / 2

/-- Upper eigenvalue normal form for the concrete `2×2` order ray. -/
def twoPointOrderRayEigenHigh (x y ε : ℝ) : ℝ :=
  (twoPointOrderRayTrace x y ε +
    twoPointOrderRayGap x y ε) / 2

/-- For a positive order-ray parameter, the two spectral branches are separated. -/
theorem twoPointOrderRayEigenLow_lt_high_of_pos
    (x y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    twoPointOrderRayEigenLow x y ε <
      twoPointOrderRayEigenHigh x y ε := by
  have hpos : 0 < (x - y) ^ 2 + 4 * ε ^ 2 := by
    nlinarith [sq_nonneg (x - y), sq_pos_of_ne_zero (ne_of_gt hε)]
  have hgap : 0 < twoPointOrderRayGap x y ε := by
    simpa [twoPointOrderRayGap] using Real.sqrt_pos.2 hpos
  unfold twoPointOrderRayEigenLow twoPointOrderRayEigenHigh
  linarith

/--
Scalar characteristic polynomial normal form for the concrete real `2×2`
order-ray matrix.
-/
def twoPointOrderRayCharpoly (x y ε t : ℝ) : ℝ :=
  t ^ 2 - twoPointOrderRayTrace x y ε * t +
    ((x + ε) * (y + ε) - ε ^ 2)

/--
The scalar characteristic polynomial factors through the two explicit spectral
branches of the concrete `2×2` order ray.
-/
theorem twoPointOrderRay_charpoly_factor
    (x y ε t : ℝ) :
    twoPointOrderRayCharpoly x y ε t =
      (t - twoPointOrderRayEigenLow x y ε) *
        (t - twoPointOrderRayEigenHigh x y ε) := by
  unfold twoPointOrderRayCharpoly
    twoPointOrderRayEigenLow twoPointOrderRayEigenHigh
    twoPointOrderRayTrace twoPointOrderRayGap
  have hsqrt :
      (Real.sqrt ((x - y) ^ 2 + 4 * ε ^ 2)) ^ 2 =
        (x - y) ^ 2 + 4 * ε ^ 2 := by
    exact Real.sq_sqrt (by nlinarith [sq_nonneg (x - y), sq_nonneg ε])
  have harg :
      -(x * y * 2) + x ^ 2 + y ^ 2 + ε ^ 2 * 4 =
        (x - y) ^ 2 + 4 * ε ^ 2 := by
    ring
  ring_nf
  rw [harg, hsqrt]
  ring

/-- Spectral slope of the affine interpolant on the two eigenvalue branches. -/
def twoPointOrderRaySpectralSlope
    (f : ℝ → ℝ) (x y ε : ℝ) : ℝ :=
  (f (twoPointOrderRayEigenHigh x y ε) -
      f (twoPointOrderRayEigenLow x y ε)) /
    (twoPointOrderRayEigenHigh x y ε -
      twoPointOrderRayEigenLow x y ε)

/--
Spectral intercept for the normalized function `t ↦ f t - f 0`.

This is the intercept of the affine function matching the normalized scalar
function on the two spectral branches.
-/
def twoPointOrderRaySpectralIntercept
    (f : ℝ → ℝ) (x y ε : ℝ) : ℝ :=
  f (twoPointOrderRayEigenLow x y ε) - f 0 -
    twoPointOrderRaySpectralSlope f x y ε *
      twoPointOrderRayEigenLow x y ε

/-- The affine spectral interpolant for the normalized scalar function. -/
def twoPointOrderRaySpectralAffine
    (f : ℝ → ℝ) (x y ε t : ℝ) : ℝ :=
  twoPointOrderRaySpectralSlope f x y ε * t +
    twoPointOrderRaySpectralIntercept f x y ε

/-- The concrete `2×2` order-ray matrix has the expected scalar charpoly. -/
lemma twoPointOrderRayMatrix_charpoly_eval_ofReal
    (x y ε t : ℝ) :
    (twoPointOrderRayMatrix x y ε).charpoly.eval (t : ℂ) =
      (twoPointOrderRayCharpoly x y ε t : ℂ) := by
  rw [Matrix.charpoly_fin_two]
  have htrace :
      (ε • Matrix.vecMulVec (fun _ : Fin 2 => (1 : ℂ))
          (star fun _ : Fin 2 => (1 : ℂ))).trace =
        (ε : ℂ) * 2 := by
    simp [Matrix.trace, Matrix.vecMulVec_apply]
    ring
  simp [twoPointOrderRayMatrix, diagonalPerturbation,
    diagonalMatrix, rankOnePerturbation, twoPointNodes,
    twoPointOrderRayCharpoly, twoPointOrderRayTrace,
    Matrix.det_fin_two, Matrix.vecMulVec_apply, htrace]
  ring_nf

/-- The spectral affine interpolant matches `f - f 0` at the lower branch. -/
lemma twoPointOrderRaySpectralAffine_low
    (f : ℝ → ℝ) (x y ε : ℝ) :
    twoPointOrderRaySpectralAffine f x y ε
        (twoPointOrderRayEigenLow x y ε) =
      f (twoPointOrderRayEigenLow x y ε) - f 0 := by
  simp [twoPointOrderRaySpectralAffine,
    twoPointOrderRaySpectralIntercept]

/-- The spectral affine interpolant matches `f - f 0` at the upper branch. -/
lemma twoPointOrderRaySpectralAffine_high
    (f : ℝ → ℝ) (x y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    twoPointOrderRaySpectralAffine f x y ε
        (twoPointOrderRayEigenHigh x y ε) =
      f (twoPointOrderRayEigenHigh x y ε) - f 0 := by
  have hlt := twoPointOrderRayEigenLow_lt_high_of_pos x y hε
  have hne :
      twoPointOrderRayEigenHigh x y ε -
        twoPointOrderRayEigenLow x y ε ≠ 0 := by
    linarith
  unfold twoPointOrderRaySpectralAffine
    twoPointOrderRaySpectralIntercept
    twoPointOrderRaySpectralSlope
  field_simp [hne]
  ring

/-- The real spectrum of the concrete order-ray matrix is contained in its two branches. -/
lemma twoPointOrderRayMatrix_spectrum_subset_eigenLowHigh
    (x y ε : ℝ) :
    spectrum ℝ (twoPointOrderRayMatrix x y ε) ⊆
      ({twoPointOrderRayEigenLow x y ε,
        twoPointOrderRayEigenHigh x y ε} : Set ℝ) := by
  intro t ht
  have htC : (t : ℂ) ∈ spectrum ℂ (twoPointOrderRayMatrix x y ε) := by
    simpa [Set.mem_preimage] using
      (show t ∈ (algebraMap ℝ ℂ) ⁻¹'
          spectrum ℂ (twoPointOrderRayMatrix x y ε) by
        rwa [spectrum.preimage_algebraMap ℂ])
  have hroot :
      Polynomial.IsRoot
        (twoPointOrderRayMatrix x y ε).charpoly (t : ℂ) :=
    (Matrix.mem_spectrum_iff_isRoot_charpoly).mp htC
  have hpolyC :
      (twoPointOrderRayCharpoly x y ε t : ℂ) = 0 := by
    simpa [Polynomial.IsRoot.def,
      twoPointOrderRayMatrix_charpoly_eval_ofReal x y ε t] using hroot
  have hpolyR : twoPointOrderRayCharpoly x y ε t = 0 :=
    Complex.ofReal_injective hpolyC
  rw [twoPointOrderRay_charpoly_factor] at hpolyR
  rcases mul_eq_zero.mp hpolyR with hlow | hhigh
  · left
    linarith
  · right
    simpa using sub_eq_zero.mp hhigh

/-- CStarMatrix-copy version of the two-branch spectrum containment. -/
lemma twoPointCStarOrderRayMatrix_spectrum_subset_eigenLowHigh
    (x y ε : ℝ) :
    spectrum ℝ (twoPointCStarOrderRayMatrix x y ε) ⊆
      ({twoPointOrderRayEigenLow x y ε,
        twoPointOrderRayEigenHigh x y ε} : Set ℝ) := by
  simpa [twoPointCStarOrderRayMatrix, cStarDiagonalPerturbation,
    twoPointOrderRayMatrix] using
    twoPointOrderRayMatrix_spectrum_subset_eigenLowHigh x y ε

/-- The real quasispectrum of the concrete CStar order ray is finite. -/
lemma twoPointCStarOrderRayMatrix_quasispectrum_finite
    (x y ε : ℝ) :
    (quasispectrum ℝ (twoPointCStarOrderRayMatrix x y ε)).Finite := by
  have hfinite :
      ({0, twoPointOrderRayEigenLow x y ε,
        twoPointOrderRayEigenHigh x y ε} : Set ℝ).Finite := by
    simp
  refine hfinite.subset ?_
  intro t ht
  have htq : t = 0 ∨ t ∈ spectrum ℝ (twoPointCStarOrderRayMatrix x y ε) :=
    (mem_quasispectrum_iff
      (a := twoPointCStarOrderRayMatrix x y ε) (x := t)).mp ht
  rcases htq with rfl | hs
  · left
    rfl
  · right
    exact twoPointCStarOrderRayMatrix_spectrum_subset_eigenLowHigh x y ε hs

/-- Arbitrary normalized scalar functions are continuous on the finite order-ray quasispectrum. -/
lemma twoPointCStarOrderRayMatrix_continuousOn_normalized
    (f : ℝ → ℝ) (x y ε : ℝ) :
    ContinuousOn (fun t : ℝ => f t - f 0)
      (quasispectrum ℝ (twoPointCStarOrderRayMatrix x y ε)) :=
  (twoPointCStarOrderRayMatrix_quasispectrum_finite x y ε).continuousOn
    (fun t : ℝ => f t - f 0)

/--
On the concrete order-ray matrix, the normalized CFC is equal to unital CFC of
the affine spectral interpolant.
-/
lemma twoPointCStarOrderRayMatrix_cfcₙ_eq_cfc_spectralAffine
    (f : ℝ → ℝ) (x y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    cfcₙ (fun t : ℝ => f t - f 0)
        (twoPointCStarOrderRayMatrix x y ε) =
      cfc (twoPointOrderRaySpectralAffine f x y ε)
        (twoPointCStarOrderRayMatrix x y ε) := by
  let M : CStarMatrix (Fin 2) (Fin 2) ℂ :=
    twoPointCStarOrderRayMatrix x y ε
  have hnorm_cont :
      ContinuousOn (fun t : ℝ => f t - f 0) (quasispectrum ℝ M) := by
    simpa [M] using
      twoPointCStarOrderRayMatrix_continuousOn_normalized f x y ε
  have hspectrum :
      spectrum ℝ M ⊆
        ({twoPointOrderRayEigenLow x y ε,
          twoPointOrderRayEigenHigh x y ε} : Set ℝ) := by
    simpa [M] using
      twoPointCStarOrderRayMatrix_spectrum_subset_eigenLowHigh x y ε
  have hcongr :
      cfc (fun t : ℝ => f t - f 0) M =
        cfc (twoPointOrderRaySpectralAffine f x y ε) M := by
    apply cfc_congr
    intro t ht
    have ht' := hspectrum ht
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ht'
    rcases ht' with htlow | hthigh
    · simpa [htlow] using
        (twoPointOrderRaySpectralAffine_low f x y ε).symm
    · simpa [hthigh] using
        (twoPointOrderRaySpectralAffine_high f x y hε).symm
  change cfcₙ (fun t : ℝ => f t - f 0) M =
    cfc (twoPointOrderRaySpectralAffine f x y ε) M
  calc
    cfcₙ (fun t : ℝ => f t - f 0) M =
        cfc (fun t : ℝ => f t - f 0) M := by
      exact cfcₙ_eq_cfc (a := M) (hf := hnorm_cont) (hf0 := by simp)
    _ = cfc (twoPointOrderRaySpectralAffine f x y ε) M := hcongr

/-- Unital CFC of the affine spectral interpolant is an affine matrix expression. -/
lemma twoPointCStarOrderRayMatrix_cfc_spectralAffine_eq
    (f : ℝ → ℝ) (x y ε : ℝ) :
    cfc (twoPointOrderRaySpectralAffine f x y ε)
        (twoPointCStarOrderRayMatrix x y ε) =
      twoPointOrderRaySpectralSlope f x y ε •
          twoPointCStarOrderRayMatrix x y ε +
        algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ)
          (twoPointOrderRaySpectralIntercept f x y ε) := by
  let M : CStarMatrix (Fin 2) (Fin 2) ℂ :=
    twoPointCStarOrderRayMatrix x y ε
  have hsa : IsSelfAdjoint M := by
    simpa [M, twoPointCStarOrderRayMatrix] using
      (cStarDiagonalPerturbation_isSelfAdjoint
        (twoPointNodes x y) (fun _ : Fin 2 => (1 : ℂ)) ε)
  change cfc
      (fun t : ℝ =>
        twoPointOrderRaySpectralSlope f x y ε * t +
          twoPointOrderRaySpectralIntercept f x y ε) M =
    twoPointOrderRaySpectralSlope f x y ε • M +
      algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ)
        (twoPointOrderRaySpectralIntercept f x y ε)
  calc
    cfc
        (fun t : ℝ =>
          twoPointOrderRaySpectralSlope f x y ε * t +
            twoPointOrderRaySpectralIntercept f x y ε) M =
        cfc
          (fun t : ℝ =>
            twoPointOrderRaySpectralIntercept f x y ε +
              twoPointOrderRaySpectralSlope f x y ε * t) M := by
      congr 1
      ext t
      ring
    _ =
        algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ)
            (twoPointOrderRaySpectralIntercept f x y ε) +
          cfc (fun t : ℝ => twoPointOrderRaySpectralSlope f x y ε * t) M := by
      exact cfc_const_add
        (twoPointOrderRaySpectralIntercept f x y ε)
        (fun t : ℝ => twoPointOrderRaySpectralSlope f x y ε * t)
        M (ha := hsa)
    _ =
        algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ)
            (twoPointOrderRaySpectralIntercept f x y ε) +
          twoPointOrderRaySpectralSlope f x y ε • M := by
      congr 1
      simpa using
        (cfc_const_mul_id (twoPointOrderRaySpectralSlope f x y ε)
          M (ha := hsa))
    _ =
        twoPointOrderRaySpectralSlope f x y ε • M +
          algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ)
            (twoPointOrderRaySpectralIntercept f x y ε) := by
      abel

/--
Entrywise spectral formula for the normalized CFC of the concrete order-ray
matrix.

The affine coefficients are the exact interpolant through the two spectral
branches `twoPointOrderRayEigenLow/High`.
-/
theorem twoPointCStarOrderRayMatrix_cfcₙ_entry_spectralFormula
    (f : ℝ → ℝ) (x y : ℝ) {ε : ℝ} (hε : 0 < ε) (i j : Fin 2) :
    (cfcₙ (fun t : ℝ => f t - f 0)
        (twoPointCStarOrderRayMatrix x y ε)) i j =
      (twoPointOrderRaySpectralSlope f x y ε : ℂ) *
          (twoPointCStarOrderRayMatrix x y ε) i j +
        if i = j then
          (twoPointOrderRaySpectralIntercept f x y ε : ℂ)
        else 0 := by
  have hmatrix :
      cfcₙ (fun t : ℝ => f t - f 0)
          (twoPointCStarOrderRayMatrix x y ε) =
        twoPointOrderRaySpectralSlope f x y ε •
            twoPointCStarOrderRayMatrix x y ε +
          algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ)
            (twoPointOrderRaySpectralIntercept f x y ε) := by
    rw [twoPointCStarOrderRayMatrix_cfcₙ_eq_cfc_spectralAffine
        f x y hε]
    exact twoPointCStarOrderRayMatrix_cfc_spectralAffine_eq f x y ε
  have hentry := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) ℂ => M i j) hmatrix
  simpa [Matrix.algebraMap_matrix_apply] using hentry

/--
Named entry normal form for the CFC order-ray difference matrix.

The scalar `ε`-`δ` extraction is intentionally not done here; this definition
only freezes the exact matrix entry that the next scalar estimate will analyze.
-/
def twoPointCFCOrderRayDifferenceEntryFormula
    (f : ℝ → ℝ) (x y ε : ℝ) (i j : Fin 2) : ℂ :=
  (CStarMatrix.ofMatrix.symm
    (twoPointCFCOrderRayDifference f x y ε)) i j

/-- The CFC order-ray difference has the named entry normal form. -/
theorem twoPointCFCOrderRayDifference_entry_formula
    (f : ℝ → ℝ) (x y ε : ℝ) (i j : Fin 2) :
    (CStarMatrix.ofMatrix.symm
      (twoPointCFCOrderRayDifference f x y ε)) i j =
        twoPointCFCOrderRayDifferenceEntryFormula f x y ε i j :=
  rfl

/-- Direct-entry version of `twoPointCFCOrderRayDifference_entry_formula`. -/
theorem twoPointCFCOrderRayDifference_entry_direct_formula
    (f : ℝ → ℝ) (x y ε : ℝ) (i j : Fin 2) :
    (twoPointCFCOrderRayDifference f x y ε) i j =
        twoPointCFCOrderRayDifferenceEntryFormula f x y ε i j := by
  rw [← twoPointCFCOrderRayDifference_entry_formula
    (f := f) (x := x) (y := y) (ε := ε) (i := i) (j := j)]
  rfl

/-- Diagonal specialization of the CFC order-ray difference entry formula. -/
theorem twoPointCFCOrderRayDifference_diag_formula
    (f : ℝ → ℝ) (x y ε : ℝ) (i : Fin 2) :
    (CStarMatrix.ofMatrix.symm
      (twoPointCFCOrderRayDifference f x y ε)) i i =
        twoPointCFCOrderRayDifferenceEntryFormula f x y ε i i :=
  twoPointCFCOrderRayDifference_entry_formula f x y ε i i

/-- Off-diagonal specialization of the CFC order-ray difference entry formula. -/
theorem twoPointCFCOrderRayDifference_offdiag_formula
    (f : ℝ → ℝ) (x y ε : ℝ) :
    (CStarMatrix.ofMatrix.symm
      (twoPointCFCOrderRayDifference f x y ε)) 0 1 =
        twoPointCFCOrderRayDifferenceEntryFormula f x y ε 0 1 :=
  twoPointCFCOrderRayDifference_entry_formula f x y ε 0 1

/--
Exact spectral formula for entries of the CFC order-ray difference.

The perturbed CFC term is evaluated by the two spectral branches.  The
unperturbed diagonal-base CFC term is retained explicitly; later scalar
extraction nodes analyze the resulting `ε`-asymptotics.
-/
theorem twoPointCFCOrderRayDifference_entry_spectralFormula
    (f : ℝ → ℝ) (x y : ℝ) {ε : ℝ} (hε : 0 < ε) (i j : Fin 2) :
    twoPointCFCOrderRayDifferenceEntryFormula f x y ε i j =
      ((twoPointOrderRaySpectralSlope f x y ε : ℂ) *
          (twoPointCStarOrderRayMatrix x y ε) i j +
        if i = j then
          (twoPointOrderRaySpectralIntercept f x y ε : ℂ)
        else 0) -
        (cfcₙ (fun t : ℝ => f t - f 0)
          (cStarDiagonalMatrix (twoPointNodes x y))) i j := by
  simp [twoPointCFCOrderRayDifferenceEntryFormula,
    twoPointCFCOrderRayDifference,
    twoPointCStarOrderRayMatrix_cfcₙ_entry_spectralFormula f x y hε i j]

/--
Off-diagonal specialization of the exact spectral formula for the CFC
order-ray difference.
-/
theorem twoPointCFCOrderRayDifference_offdiag_spectralFormula
    (f : ℝ → ℝ) (x y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    twoPointCFCOrderRayDifferenceEntryFormula f x y ε 0 1 =
      (twoPointOrderRaySpectralSlope f x y ε : ℂ) * (ε : ℂ) -
        (cfcₙ (fun t : ℝ => f t - f 0)
          (cStarDiagonalMatrix (twoPointNodes x y))) 0 1 := by
  have hentry :
      (twoPointCStarOrderRayMatrix x y ε) 0 1 = (ε : ℂ) := by
    simp [twoPointCStarOrderRayMatrix, cStarDiagonalPerturbation,
      diagonalPerturbation, diagonalMatrix,
      rankOnePerturbation, twoPointNodes, Matrix.vecMulVec_apply]
  rw [twoPointCFCOrderRayDifference_entry_spectralFormula f x y hε 0 1,
    hentry]
  simp

/-- The spectral gap of the concrete `2×2` order ray tends to `|x - y|`. -/
lemma twoPointOrderRayGap_tendsto_abs_sub (x y : ℝ) :
    Filter.Tendsto (fun ε : ℝ => twoPointOrderRayGap x y ε)
      (𝓝[>] (0 : ℝ)) (𝓝 |x - y|) := by
  have harg_cont :
      ContinuousAt (fun ε : ℝ => (x - y) ^ 2 + 4 * ε ^ 2) 0 := by
    fun_prop
  have harg :
      Filter.Tendsto (fun ε : ℝ => (x - y) ^ 2 + 4 * ε ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 ((x - y) ^ 2)) := by
    simpa using harg_cont.tendsto.mono_left nhdsWithin_le_nhds
  have hsqrt :
      Filter.Tendsto
        (fun ε : ℝ => Real.sqrt ((x - y) ^ 2 + 4 * ε ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt ((x - y) ^ 2))) :=
    (Real.continuous_sqrt.tendsto _).comp harg
  simpa [twoPointOrderRayGap, Real.sqrt_sq_eq_abs] using hsqrt

/-- The lower spectral branch tends to the smaller endpoint. -/
lemma twoPointOrderRayEigenLow_tendsto_min (x y : ℝ) :
    Filter.Tendsto (fun ε : ℝ => twoPointOrderRayEigenLow x y ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (min x y)) := by
  have htrace :
      Filter.Tendsto (fun ε : ℝ => twoPointOrderRayTrace x y ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (x + y)) := by
    have hcont : ContinuousAt (fun ε : ℝ => x + y + 2 * ε) 0 := by
      fun_prop
    simpa [twoPointOrderRayTrace] using
      hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hgap := twoPointOrderRayGap_tendsto_abs_sub x y
  have hlim :
      Filter.Tendsto
        (fun ε : ℝ =>
          (twoPointOrderRayTrace x y ε -
            twoPointOrderRayGap x y ε) / 2)
        (𝓝[>] (0 : ℝ)) (𝓝 ((x + y - |x - y|) / 2)) :=
    (htrace.sub hgap).div_const 2
  have hmin : (x + y - |x - y|) / 2 = min x y := by
    by_cases hxy : x ≤ y
    · rw [min_eq_left hxy, abs_of_nonpos (sub_nonpos.mpr hxy)]
      ring
    · have hyx : y ≤ x := le_of_lt (lt_of_not_ge hxy)
      rw [min_eq_right hyx, abs_of_nonneg (sub_nonneg.mpr hyx)]
      ring
  simpa [twoPointOrderRayEigenLow, hmin] using hlim

/-- The upper spectral branch tends to the larger endpoint. -/
lemma twoPointOrderRayEigenHigh_tendsto_max (x y : ℝ) :
    Filter.Tendsto (fun ε : ℝ => twoPointOrderRayEigenHigh x y ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (max x y)) := by
  have htrace :
      Filter.Tendsto (fun ε : ℝ => twoPointOrderRayTrace x y ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (x + y)) := by
    have hcont : ContinuousAt (fun ε : ℝ => x + y + 2 * ε) 0 := by
      fun_prop
    simpa [twoPointOrderRayTrace] using
      hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hgap := twoPointOrderRayGap_tendsto_abs_sub x y
  have hlim :
      Filter.Tendsto
        (fun ε : ℝ =>
          (twoPointOrderRayTrace x y ε +
            twoPointOrderRayGap x y ε) / 2)
        (𝓝[>] (0 : ℝ)) (𝓝 ((x + y + |x - y|) / 2)) :=
    (htrace.add hgap).div_const 2
  have hmax : (x + y + |x - y|) / 2 = max x y := by
    by_cases hxy : x ≤ y
    · rw [max_eq_right hxy, abs_of_nonpos (sub_nonpos.mpr hxy)]
      ring
    · have hyx : y ≤ x := le_of_lt (lt_of_not_ge hxy)
      rw [max_eq_left hyx, abs_of_nonneg (sub_nonneg.mpr hyx)]
      ring
  simpa [twoPointOrderRayEigenHigh, hmax] using hlim

/--
The spectral affine slope tends to the raw divided difference.

The local continuity assumptions are essential: for an arbitrary scalar
function, the branch values `f(e_±(ε))` need not converge to the endpoint
values.
-/
theorem twoPointOrderRaySpectralSlope_tendsto_rawDividedDifference
    {f : ℝ → ℝ} {x y : ℝ} (hxy : x ≠ y)
    (hcx : ContinuousAt f x) (hcy : ContinuousAt f y) :
    Filter.Tendsto (fun ε : ℝ => twoPointOrderRaySpectralSlope f x y ε)
      (𝓝[>] (0 : ℝ))
      (𝓝 (twoPointRawDividedDifference f x y)) := by
  by_cases hlt : x < y
  · have hlow :
        Filter.Tendsto
          (fun ε : ℝ => twoPointOrderRayEigenLow x y ε)
          (𝓝[>] (0 : ℝ)) (𝓝 x) := by
      simpa [min_eq_left (le_of_lt hlt)] using
        twoPointOrderRayEigenLow_tendsto_min x y
    have hhigh :
        Filter.Tendsto
          (fun ε : ℝ => twoPointOrderRayEigenHigh x y ε)
          (𝓝[>] (0 : ℝ)) (𝓝 y) := by
      simpa [max_eq_right (le_of_lt hlt)] using
        twoPointOrderRayEigenHigh_tendsto_max x y
    have hnum :
        Filter.Tendsto
          (fun ε : ℝ =>
            f (twoPointOrderRayEigenHigh x y ε) -
              f (twoPointOrderRayEigenLow x y ε))
          (𝓝[>] (0 : ℝ)) (𝓝 (f y - f x)) :=
      (hcy.tendsto.comp hhigh).sub (hcx.tendsto.comp hlow)
    have hden :
        Filter.Tendsto
          (fun ε : ℝ =>
            twoPointOrderRayEigenHigh x y ε -
              twoPointOrderRayEigenLow x y ε)
          (𝓝[>] (0 : ℝ)) (𝓝 (y - x)) :=
      hhigh.sub hlow
    have hden_ne : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
    simpa [twoPointOrderRaySpectralSlope,
      twoPointRawDividedDifference] using hnum.div hden hden_ne
  · have hyltx : y < x := lt_of_le_of_ne (le_of_not_gt hlt) hxy.symm
    have hlow :
        Filter.Tendsto
          (fun ε : ℝ => twoPointOrderRayEigenLow x y ε)
          (𝓝[>] (0 : ℝ)) (𝓝 y) := by
      simpa [min_eq_right (le_of_lt hyltx)] using
        twoPointOrderRayEigenLow_tendsto_min x y
    have hhigh :
        Filter.Tendsto
          (fun ε : ℝ => twoPointOrderRayEigenHigh x y ε)
          (𝓝[>] (0 : ℝ)) (𝓝 x) := by
      simpa [max_eq_left (le_of_lt hyltx)] using
        twoPointOrderRayEigenHigh_tendsto_max x y
    have hnum :
        Filter.Tendsto
          (fun ε : ℝ =>
            f (twoPointOrderRayEigenHigh x y ε) -
              f (twoPointOrderRayEigenLow x y ε))
          (𝓝[>] (0 : ℝ)) (𝓝 (f x - f y)) :=
      (hcx.tendsto.comp hhigh).sub (hcy.tendsto.comp hlow)
    have hden :
        Filter.Tendsto
          (fun ε : ℝ =>
            twoPointOrderRayEigenHigh x y ε -
              twoPointOrderRayEigenLow x y ε)
          (𝓝[>] (0 : ℝ)) (𝓝 (x - y)) :=
      hhigh.sub hlow
    have hden_ne : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hlim :
        Filter.Tendsto
          (fun ε : ℝ => twoPointOrderRaySpectralSlope f x y ε)
          (𝓝[>] (0 : ℝ)) (𝓝 ((f x - f y) / (x - y))) := by
      simpa [twoPointOrderRaySpectralSlope] using
        hnum.div hden hden_ne
    have htarget :
        (f x - f y) / (x - y) =
          twoPointRawDividedDifference f x y := by
      unfold twoPointRawDividedDifference
      field_simp [sub_ne_zero.mpr hxy, sub_ne_zero.mpr hxy.symm]
      ring
    simpa [htarget] using hlim

/-- The diagonal base CFC term has no off-diagonal entry at distinct nodes. -/
lemma twoPointCStarDiagonalMatrix_cfcₙ_offdiag_zero
    (f : ℝ → ℝ) {x y : ℝ} (hxy : x ≠ y) :
    (cfcₙ (fun t : ℝ => f t - f 0)
      (cStarDiagonalMatrix (twoPointNodes x y))) 0 1 = 0 := by
  let D : CStarMatrix (Fin 2) (Fin 2) ℂ :=
    cStarDiagonalMatrix (twoPointNodes x y)
  let a : ℝ := twoPointRawDividedDifference f x y
  let b : ℝ := f x - f 0 - a * x
  have hspectrum :
      spectrum ℝ D ⊆ ({x, y} : Set ℝ) := by
    intro t ht
    rw [← spectrum.preimage_algebraMap ℂ] at ht
    simp only [Set.mem_preimage] at ht
    change (t : ℂ) ∈ spectrum ℂ
      (cStarDiagonalMatrix (twoPointNodes x y)) at ht
    rw [cStarDiagonalMatrix] at ht
    rw [CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv] at ht
    change (t : ℂ) ∈ spectrum ℂ
      (((CStarMatrix.ofMatrixStarAlgEquiv (A := ℂ) (n := Fin 2)).toAlgEquiv)
        (diagonalMatrix (twoPointNodes x y))) at ht
    rw [AlgEquiv.spectrum_eq
      ((CStarMatrix.ofMatrixStarAlgEquiv (A := ℂ) (n := Fin 2)).toAlgEquiv)] at ht
    rw [diagonalMatrix, spectrum_diagonal] at ht
    rcases ht with ⟨i, hi⟩
    have hti : t = twoPointNodes x y i := Complex.ofReal_injective hi.symm
    fin_cases i <;> simp [hti, twoPointNodes]
  have hfinite :
      (quasispectrum ℝ D).Finite := by
    have hset : ({0, x, y} : Set ℝ).Finite := by
      simp
    refine hset.subset ?_
    intro t ht
    have htq : t = 0 ∨ t ∈ spectrum ℝ D :=
      (mem_quasispectrum_iff (a := D) (x := t)).mp ht
    rcases htq with ht | ht
    · left
      simpa using ht
    · right
      exact hspectrum ht
  have hcont :
      ContinuousOn (fun t : ℝ => f t - f 0) (quasispectrum ℝ D) :=
    hfinite.continuousOn _
  have hsa : IsSelfAdjoint D := by
    rw [isSelfAdjoint_iff]
    have h := (diagonalMatrix_isSelfAdjoint
      (twoPointNodes x y)).star_eq
    simpa [D, cStarDiagonalMatrix] using congrArg CStarMatrix.ofMatrix h
  have hmatch :
      Set.EqOn (fun t : ℝ => f t - f 0) (fun t : ℝ => a * t + b)
        (spectrum ℝ D) := by
    intro t ht
    have ht' := hspectrum ht
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ht'
    rcases ht' with htX | htY
    · simp [htX, a, b]
    · have hyx : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
      simp [htY, a, b, twoPointRawDividedDifference]
      field_simp [hyx]
      ring
  have hcfc :
      cfcₙ (fun t : ℝ => f t - f 0) D =
        a • D + algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ) b := by
    calc
      cfcₙ (fun t : ℝ => f t - f 0) D =
          cfc (fun t : ℝ => f t - f 0) D := by
        exact cfcₙ_eq_cfc (a := D) (hf := hcont) (hf0 := by simp)
      _ = cfc (fun t : ℝ => a * t + b) D := by
        exact cfc_congr hmatch
      _ = cfc (fun t : ℝ => b + a * t) D := by
        congr 1
        ext t
        ring
      _ = algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ) b +
          cfc (fun t : ℝ => a * t) D := by
        exact cfc_const_add b (fun t : ℝ => a * t) D (ha := hsa)
      _ = algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ) b + a • D := by
        congr 1
        simpa using (cfc_const_mul_id a D (ha := hsa))
      _ = a • D + algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ) b := by
        abel
  have hentry := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) ℂ => M 0 1) hcfc
  simpa [D, cStarDiagonalMatrix, diagonalMatrix,
    twoPointNodes, Matrix.algebraMap_matrix_apply] using hentry

/--
Entry formula for the two-point diagonal base CFC at distinct nodes.

This extends the existing off-diagonal zero lemma with the two diagonal
entries needed by the special-path jump-exclusion test.
-/
lemma twoPointCStarDiagonalMatrix_cfcₙ_entry_formula
    (f : ℝ → ℝ) {x y : ℝ} (hxy : x ≠ y) (i j : Fin 2) :
    (cfcₙ (fun t : ℝ => f t - f 0)
      (cStarDiagonalMatrix (twoPointNodes x y))) i j =
        if i = j then ((f (twoPointNodes x y i) - f 0 : ℝ) : ℂ)
        else 0 := by
  let D : CStarMatrix (Fin 2) (Fin 2) ℂ :=
    cStarDiagonalMatrix (twoPointNodes x y)
  let a : ℝ := twoPointRawDividedDifference f x y
  let b : ℝ := f x - f 0 - a * x
  have hspectrum :
      spectrum ℝ D ⊆ ({x, y} : Set ℝ) := by
    intro t ht
    rw [← spectrum.preimage_algebraMap ℂ] at ht
    simp only [Set.mem_preimage] at ht
    change (t : ℂ) ∈ spectrum ℂ
      (cStarDiagonalMatrix (twoPointNodes x y)) at ht
    rw [cStarDiagonalMatrix] at ht
    rw [CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv] at ht
    change (t : ℂ) ∈ spectrum ℂ
      (((CStarMatrix.ofMatrixStarAlgEquiv (A := ℂ) (n := Fin 2)).toAlgEquiv)
        (diagonalMatrix (twoPointNodes x y))) at ht
    rw [AlgEquiv.spectrum_eq
      ((CStarMatrix.ofMatrixStarAlgEquiv (A := ℂ) (n := Fin 2)).toAlgEquiv)] at ht
    rw [diagonalMatrix, spectrum_diagonal] at ht
    rcases ht with ⟨k, hk⟩
    have htk : t = twoPointNodes x y k := Complex.ofReal_injective hk.symm
    fin_cases k <;> simp [htk, twoPointNodes]
  have hfinite :
      (quasispectrum ℝ D).Finite := by
    have hset : ({0, x, y} : Set ℝ).Finite := by
      simp
    refine hset.subset ?_
    intro t ht
    have htq : t = 0 ∨ t ∈ spectrum ℝ D :=
      (mem_quasispectrum_iff (a := D) (x := t)).mp ht
    rcases htq with ht | ht
    · left
      simpa using ht
    · right
      exact hspectrum ht
  have hcont :
      ContinuousOn (fun t : ℝ => f t - f 0) (quasispectrum ℝ D) :=
    hfinite.continuousOn _
  have hsa : IsSelfAdjoint D := by
    rw [isSelfAdjoint_iff]
    have h := (diagonalMatrix_isSelfAdjoint
      (twoPointNodes x y)).star_eq
    simpa [D, cStarDiagonalMatrix] using congrArg CStarMatrix.ofMatrix h
  have hmatch :
      Set.EqOn (fun t : ℝ => f t - f 0) (fun t : ℝ => a * t + b)
        (spectrum ℝ D) := by
    intro t ht
    have ht' := hspectrum ht
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ht'
    rcases ht' with htX | htY
    · simp [htX, a, b]
    · have hyx : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
      simp [htY, a, b, twoPointRawDividedDifference]
      field_simp [hyx]
      ring
  have hcfc :
      cfcₙ (fun t : ℝ => f t - f 0) D =
        a • D + algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ) b := by
    calc
      cfcₙ (fun t : ℝ => f t - f 0) D =
          cfc (fun t : ℝ => f t - f 0) D := by
        exact cfcₙ_eq_cfc (a := D) (hf := hcont) (hf0 := by simp)
      _ = cfc (fun t : ℝ => a * t + b) D := by
        exact cfc_congr hmatch
      _ = cfc (fun t : ℝ => b + a * t) D := by
        congr 1
        ext t
        ring
      _ = algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ) b +
          cfc (fun t : ℝ => a * t) D := by
        exact cfc_const_add b (fun t : ℝ => a * t) D (ha := hsa)
      _ = algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ) b + a • D := by
        congr 1
        simpa using (cfc_const_mul_id a D (ha := hsa))
      _ = a • D + algebraMap ℝ (CStarMatrix (Fin 2) (Fin 2) ℂ) b := by
        abel
  have hentry := congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) ℂ => M i j) hcfc
  fin_cases i <;> fin_cases j
  · have hentry00 :
        (cfcₙ (fun t : ℝ => f t - f 0)
          (cStarDiagonalMatrix (twoPointNodes x y))) 0 0 =
          (a : ℂ) * (x : ℂ) + (b : ℂ) := by
      simpa [D, cStarDiagonalMatrix, diagonalMatrix,
        twoPointNodes, CStarMatrix.algebraMap_apply] using hentry
    have hcalc : (a : ℂ) * (x : ℂ) + (b : ℂ) = (f x - f 0 : ℂ) := by
      simp [b]
    simp [twoPointNodes, hentry00, hcalc]
  · have hentry01 :
        (cfcₙ (fun t : ℝ => f t - f 0)
          (cStarDiagonalMatrix (twoPointNodes x y))) 0 1 = 0 := by
      simpa [D, cStarDiagonalMatrix, diagonalMatrix,
        twoPointNodes, CStarMatrix.algebraMap_apply] using hentry
    simp [hentry01]
  · have hentry10 :
        (cfcₙ (fun t : ℝ => f t - f 0)
          (cStarDiagonalMatrix (twoPointNodes x y))) 1 0 = 0 := by
      simpa [D, cStarDiagonalMatrix, diagonalMatrix,
        twoPointNodes, CStarMatrix.algebraMap_apply] using hentry
    simp [hentry10]
  · have hentry11 :
        (cfcₙ (fun t : ℝ => f t - f 0)
          (cStarDiagonalMatrix (twoPointNodes x y))) 1 1 =
          (a : ℂ) * (y : ℂ) + (b : ℂ) := by
      simpa [D, cStarDiagonalMatrix, diagonalMatrix,
        twoPointNodes, CStarMatrix.algebraMap_apply] using hentry
    have hyx : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
    have hcalc : (a : ℂ) * (y : ℂ) + (b : ℂ) = (f y - f 0 : ℂ) := by
      have hyxC : (y : ℂ) - (x : ℂ) ≠ 0 := by
        exact_mod_cast hyx
      simp [a, b, twoPointRawDividedDifference]
      field_simp [hyxC]
      ring_nf
    simp [twoPointNodes, hentry11, hcalc]


end

end Quantum.TraceInequality.Loewner
