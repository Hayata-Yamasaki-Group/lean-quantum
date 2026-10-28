import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.TwoPointSpectralExtraction

/-!
# Chapter 3 scalar consequences of two-by-two CFC order

This file contains the scalar consequences of full two-by-two CFC order
comparison: scalar monotonicity, one-point monotonicity, jump exclusion,
reflection, and interior scalar continuity.
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

/-! ### Scalar consequences of full two-by-two CFC order comparison -/

/-- Pointwise ordered diagonal node lists give ordered CStar diagonal matrices. -/
lemma cStarDiagonalMatrix_le_of_pointwise {n : ℕ}
    {x y : Fin n → ℝ} (hxy : ∀ i, x i ≤ y i) :
    cStarDiagonalMatrix x ≤ cStarDiagonalMatrix y := by
  rw [← sub_nonneg]
  have hpos :
      (diagonalMatrix y - diagonalMatrix x).PosSemidef := by
    have hdiag :
        (diagonalMatrix y - diagonalMatrix x) =
          Matrix.diagonal (fun i : Fin n => ((y i - x i : ℝ) : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [diagonalMatrix]
      · simp [diagonalMatrix, Matrix.diagonal_apply_ne _ hij]
    rw [hdiag]
    refine Matrix.PosSemidef.diagonal ?_
    change ∀ i : Fin n, (0 : ℂ) ≤ ((y i - x i : ℝ) : ℂ)
    intro i
    exact_mod_cast sub_nonneg.mpr (hxy i)
  have hnonneg :
      0 ≤ (CStarMatrix.ofMatrix
        (diagonalMatrix y - diagonalMatrix x) :
          CStarMatrix (Fin n) (Fin n) ℂ) :=
    cStarMatrix_nonneg_of_posSemidef hpos
  simpa [cStarDiagonalMatrix, sub_eq_add_neg] using hnonneg

/--
Full `2×2` CFC order comparison restricts to ordinary scalar monotonicity on
the open unit interval.
-/
theorem scalarMonotoneOn_Ioo_of_twoByTwo_cfc_order
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B) :
    MonotoneOn f (Set.Ioo (-1 : ℝ) 1) := by
  intro x hx y hy hxy
  by_cases hlt : x < y
  · let m : ℝ := (x + y) / 2
    let X : Fin 2 → ℝ := twoPointNodes x m
    let Y : Fin 2 → ℝ := twoPointNodes y m
    have hxm : x ≠ m := by
      dsimp [m]
      linarith
    have hym : y ≠ m := by
      dsimp [m]
      linarith
    have hm : m ∈ Set.Ioo (-1 : ℝ) 1 := by
      dsimp [m]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have hXmem : ∀ i : Fin 2, X i ∈ Set.Ioo (-1 : ℝ) 1 := by
      intro i
      fin_cases i <;> simpa [X, twoPointNodes] using (by
        first | exact hx | exact hm)
    have hYmem : ∀ i : Fin 2, Y i ∈ Set.Ioo (-1 : ℝ) 1 := by
      intro i
      fin_cases i <;> simpa [Y, twoPointNodes] using (by
        first | exact hy | exact hm)
    let DX : CStarMatrix (Fin 2) (Fin 2) ℂ := cStarDiagonalMatrix X
    let DY : CStarMatrix (Fin 2) (Fin 2) ℂ := cStarDiagonalMatrix Y
    have hDX : DX ∈ cStarFiniteMatrixDomain 2 := by
      simpa [DX] using cStarDiagonalMatrix_mem_domain X hXmem
    have hDY : DY ∈ cStarFiniteMatrixDomain 2 := by
      simpa [DY] using cStarDiagonalMatrix_mem_domain Y hYmem
    have hDXY : DX ≤ DY := by
      refine (show cStarDiagonalMatrix X ≤ cStarDiagonalMatrix Y from ?_)
      refine cStarDiagonalMatrix_le_of_pointwise ?_
      intro i
      fin_cases i <;> simp [X, Y, twoPointNodes, hxy]
    have hcfc_le :
        cfcₙ (fun t : ℝ => f t - f 0) DX ≤
          cfcₙ (fun t : ℝ => f t - f 0) DY :=
      h2 hDX hDY hDXY
    have hdiff_nonneg :
        0 ≤ cfcₙ (fun t : ℝ => f t - f 0) DY -
          cfcₙ (fun t : ℝ => f t - f 0) DX := by
      exact sub_nonneg.mpr hcfc_le
    have hquad := cStarMatrix_quadratic_nonneg_of_nonneg
      hdiff_nonneg (Pi.single (0 : Fin 2) (1 : ℂ))
    have hxentry :
        (cfcₙ (fun t : ℝ => f t - f 0) DX 0 0 : ℂ) =
          (f x - f 0 : ℂ) := by
      simpa [DX, X, twoPointNodes] using
        twoPointCStarDiagonalMatrix_cfcₙ_entry_formula
          (f := f) hxm (0 : Fin 2) (0 : Fin 2)
    have hyentry :
        (cfcₙ (fun t : ℝ => f t - f 0) DY 0 0 : ℂ) =
          (f y - f 0 : ℂ) := by
      simpa [DY, Y, twoPointNodes] using
        twoPointCStarDiagonalMatrix_cfcₙ_entry_formula
          (f := f) hym (0 : Fin 2) (0 : Fin 2)
    have hcomplex :
        (0 : ℂ) ≤ ((f y - f 0) - (f x - f 0) : ℂ) := by
      simpa [Matrix.sub_apply, hxentry, hyentry] using hquad
    have hreal : 0 ≤ (f y - f 0) - (f x - f 0) := by
      exact_mod_cast hcomplex
    linarith
  · have hxy_eq : x = y := le_antisymm hxy (le_of_not_gt hlt)
    simp [hxy_eq]

/-! ### Two-point CFC entry asymptotics -/

/--
The normalized off-diagonal CFC difference quotient tends to the raw divided
difference.
-/
theorem twoPointCFCOrderRayDifference_offdiag_asymptotic
    {f : ℝ → ℝ} {x y : ℝ} (hxy : x ≠ y)
    (hcx : ContinuousAt f x) (hcy : ContinuousAt f y) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (ε : ℂ)⁻¹ *
          twoPointCFCOrderRayDifferenceEntryFormula f x y ε 0 1)
      (𝓝[>] (0 : ℝ))
      (𝓝 (twoPointRawDividedDifference f x y : ℂ)) := by
  have hslope :
      Filter.Tendsto
        (fun ε : ℝ => (twoPointOrderRaySpectralSlope f x y ε : ℂ))
        (𝓝[>] (0 : ℝ))
        (𝓝 (twoPointRawDividedDifference f x y : ℂ)) :=
    Filter.tendsto_ofReal_iff.mpr
      (twoPointOrderRaySpectralSlope_tendsto_rawDividedDifference
        hxy hcx hcy)
  have heq :
      (fun ε : ℝ =>
        (ε : ℂ)⁻¹ *
          twoPointCFCOrderRayDifferenceEntryFormula f x y ε 0 1)
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε : ℝ => (twoPointOrderRaySpectralSlope f x y ε : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hbase :=
      twoPointCStarDiagonalMatrix_cfcₙ_offdiag_zero (f := f) hxy
    rw [twoPointCFCOrderRayDifference_offdiag_spectralFormula
        f x y hε, hbase]
    have hεC : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hε)
    field_simp [hεC]
    ring
  exact hslope.congr' heq.symm

/--
Off-diagonal contribution to a fixed quadratic test, normalized by the
order-ray parameter.
-/
theorem twoPointCFCOrderRayDifference_offdiagTestContribution_asymptotic
    {f : ℝ → ℝ} {x y : ℝ} (hxy : x ≠ y)
    (hcx : ContinuousAt f x) (hcy : ContinuousAt f y) (a b : ℂ) :
    Filter.Tendsto
      (fun ε : ℝ =>
        star a *
          ((ε : ℂ)⁻¹ *
            twoPointCFCOrderRayDifferenceEntryFormula f x y ε 0 1) *
          b)
      (𝓝[>] (0 : ℝ))
      (𝓝 (star a * (twoPointRawDividedDifference f x y : ℂ) * b)) := by
  exact (tendsto_const_nhds.mul
    (twoPointCFCOrderRayDifference_offdiag_asymptotic hxy hcx hcy)).mul
      tendsto_const_nhds

/--
The diagonal entries of the CFC order-ray difference themselves tend to zero.

This is intentionally unnormalized.  The signed lower/upper extraction still
needs first-order control of these diagonal terms after division by the
order-ray parameter.
-/
theorem twoPointCFCOrderRayDifference_diagEntry_asymptotic
    {f : ℝ → ℝ} {x y : ℝ} (hxy : x ≠ y)
    (hcx : ContinuousAt f x) (hcy : ContinuousAt f y) (i : Fin 2) :
    Filter.Tendsto
      (fun ε : ℝ =>
        twoPointCFCOrderRayDifferenceEntryFormula f x y ε i i)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
  have hslopeC :
      Filter.Tendsto
        (fun ε : ℝ => (twoPointOrderRaySpectralSlope f x y ε : ℂ))
        (𝓝[>] (0 : ℝ))
        (𝓝 (twoPointRawDividedDifference f x y : ℂ)) :=
    Filter.tendsto_ofReal_iff.mpr
      (twoPointOrderRaySpectralSlope_tendsto_rawDividedDifference
        hxy hcx hcy)
  fin_cases i
  · have hformula :
        (fun ε : ℝ =>
          twoPointCFCOrderRayDifferenceEntryFormula f x y ε 0 0)
          =ᶠ[𝓝[>] (0 : ℝ)]
        (fun ε : ℝ =>
          ((twoPointOrderRaySpectralSlope f x y ε : ℂ) *
              ((x + ε : ℝ) -
                twoPointOrderRayEigenLow x y ε : ℝ) +
            ((f (twoPointOrderRayEigenLow x y ε) - f 0 : ℝ) : ℂ) -
            ((f x - f 0 : ℝ) : ℂ))) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hbase :=
        twoPointCStarDiagonalMatrix_cfcₙ_entry_formula
          (f := f) hxy (0 : Fin 2) (0 : Fin 2)
      have hM :
          (twoPointCStarOrderRayMatrix x y ε) 0 0 =
            ((x + ε : ℝ) : ℂ) := by
        simp [twoPointCStarOrderRayMatrix,
          cStarDiagonalPerturbation, diagonalPerturbation,
          diagonalMatrix, rankOnePerturbation,
          twoPointNodes, Matrix.vecMulVec_apply]
      rw [twoPointCFCOrderRayDifference_entry_spectralFormula
          f x y hε (0 : Fin 2) (0 : Fin 2),
        hbase, hM]
      simp [twoPointNodes, twoPointOrderRaySpectralIntercept]
      ring
    by_cases hlt : x < y
    · have hlow :
          Filter.Tendsto
            (fun ε : ℝ => twoPointOrderRayEigenLow x y ε)
            (𝓝[>] (0 : ℝ)) (𝓝 x) := by
        simpa [min_eq_left (le_of_lt hlt)] using
          twoPointOrderRayEigenLow_tendsto_min x y
      have hdiff :
          Filter.Tendsto
            (fun ε : ℝ =>
              ((x + ε : ℝ) - twoPointOrderRayEigenLow x y ε : ℝ))
            (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
        have hxeps :
            Filter.Tendsto (fun ε : ℝ => x + ε)
              (𝓝[>] (0 : ℝ)) (𝓝 x) := by
          have hcont : ContinuousAt (fun ε : ℝ => x + ε) 0 := by
            fun_prop
          simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
        simpa using hxeps.sub hlow
      have hf_low :
          Filter.Tendsto
            (fun ε : ℝ => f (twoPointOrderRayEigenLow x y ε))
            (𝓝[>] (0 : ℝ)) (𝓝 (f x)) :=
        hcx.tendsto.comp hlow
      have htarget :
          Filter.Tendsto
            (fun ε : ℝ =>
              ((twoPointOrderRaySpectralSlope f x y ε : ℂ) *
                  ((x + ε : ℝ) -
                    twoPointOrderRayEigenLow x y ε : ℝ) +
                ((f (twoPointOrderRayEigenLow x y ε) - f 0 : ℝ) : ℂ) -
                ((f x - f 0 : ℝ) : ℂ)))
            (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
        have hprod :
            Filter.Tendsto
              (fun ε : ℝ =>
                (twoPointOrderRaySpectralSlope f x y ε : ℂ) *
                  (((x + ε : ℝ) -
                    twoPointOrderRayEigenLow x y ε : ℝ) : ℂ))
              (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
          simpa using hslopeC.mul (Filter.tendsto_ofReal_iff.mpr hdiff)
        have hvalue :
            Filter.Tendsto
              (fun ε : ℝ =>
                ((f (twoPointOrderRayEigenLow x y ε) - f 0 : ℝ) : ℂ))
              (𝓝[>] (0 : ℝ)) (𝓝 ((f x - f 0 : ℝ) : ℂ)) :=
          Filter.tendsto_ofReal_iff.mpr (hf_low.sub tendsto_const_nhds)
        have htend :
            Filter.Tendsto
              (fun ε : ℝ =>
                (twoPointOrderRaySpectralSlope f x y ε : ℂ) *
                    (((x + ε : ℝ) -
                      twoPointOrderRayEigenLow x y ε : ℝ) : ℂ) +
                  ((f (twoPointOrderRayEigenLow x y ε) - f 0 : ℝ) : ℂ) -
                  ((f x - f 0 : ℝ) : ℂ))
              (𝓝[>] (0 : ℝ))
              (𝓝 (0 + ((f x - f 0 : ℝ) : ℂ) -
                ((f x - f 0 : ℝ) : ℂ))) :=
          (hprod.add hvalue).sub tendsto_const_nhds
        simpa using htend
      exact htarget.congr' hformula.symm
    · have hyltx : y < x := lt_of_le_of_ne (le_of_not_gt hlt) hxy.symm
      have hlow :
          Filter.Tendsto
            (fun ε : ℝ => twoPointOrderRayEigenLow x y ε)
            (𝓝[>] (0 : ℝ)) (𝓝 y) := by
        simpa [min_eq_right (le_of_lt hyltx)] using
          twoPointOrderRayEigenLow_tendsto_min x y
      have hdiff :
          Filter.Tendsto
            (fun ε : ℝ =>
              ((x + ε : ℝ) - twoPointOrderRayEigenLow x y ε : ℝ))
            (𝓝[>] (0 : ℝ)) (𝓝 (x - y)) := by
        have hxeps :
            Filter.Tendsto (fun ε : ℝ => x + ε)
              (𝓝[>] (0 : ℝ)) (𝓝 x) := by
          have hcont : ContinuousAt (fun ε : ℝ => x + ε) 0 := by
            fun_prop
          simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
        exact hxeps.sub hlow
      have hf_low :
          Filter.Tendsto
            (fun ε : ℝ => f (twoPointOrderRayEigenLow x y ε))
            (𝓝[>] (0 : ℝ)) (𝓝 (f y)) :=
        hcy.tendsto.comp hlow
      have hprod :
          Filter.Tendsto
            (fun ε : ℝ =>
              (twoPointOrderRaySpectralSlope f x y ε : ℂ) *
                (((x + ε : ℝ) -
                  twoPointOrderRayEigenLow x y ε : ℝ) : ℂ))
            (𝓝[>] (0 : ℝ))
            (𝓝 ((twoPointRawDividedDifference f x y : ℂ) *
              ((x - y : ℝ) : ℂ))) := by
        exact hslopeC.mul (Filter.tendsto_ofReal_iff.mpr hdiff)
      have hvalue :
          Filter.Tendsto
            (fun ε : ℝ =>
              ((f (twoPointOrderRayEigenLow x y ε) - f 0 : ℝ) : ℂ))
            (𝓝[>] (0 : ℝ)) (𝓝 ((f y - f 0 : ℝ) : ℂ)) :=
        Filter.tendsto_ofReal_iff.mpr (hf_low.sub tendsto_const_nhds)
      have htarget :
          (twoPointRawDividedDifference f x y : ℂ) *
              ((x - y : ℝ) : ℂ) +
            ((f y - f 0 : ℝ) : ℂ) - ((f x - f 0 : ℝ) : ℂ) = 0 := by
        have htargetR :
            twoPointRawDividedDifference f x y * (x - y) +
                (f y - f 0) - (f x - f 0) = 0 := by
          have hyx : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
          unfold twoPointRawDividedDifference
          field_simp [hyx]
          ring
        exact_mod_cast htargetR
      have htend :
          Filter.Tendsto
            (fun ε : ℝ =>
              ((twoPointOrderRaySpectralSlope f x y ε : ℂ) *
                  ((x + ε : ℝ) -
                    twoPointOrderRayEigenLow x y ε : ℝ) +
                ((f (twoPointOrderRayEigenLow x y ε) - f 0 : ℝ) : ℂ) -
                ((f x - f 0 : ℝ) : ℂ)))
            (𝓝[>] (0 : ℝ))
            (𝓝 ((twoPointRawDividedDifference f x y : ℂ) *
              ((x - y : ℝ) : ℂ) +
              ((f y - f 0 : ℝ) : ℂ) - ((f x - f 0 : ℝ) : ℂ))) :=
        (hprod.add hvalue).sub tendsto_const_nhds
      rw [htarget] at htend
      simpa using htend.congr' hformula.symm
  · have hformula :
        (fun ε : ℝ =>
          twoPointCFCOrderRayDifferenceEntryFormula f x y ε 1 1)
          =ᶠ[𝓝[>] (0 : ℝ)]
        (fun ε : ℝ =>
          ((twoPointOrderRaySpectralSlope f x y ε : ℂ) *
              ((y + ε : ℝ) -
                twoPointOrderRayEigenLow x y ε : ℝ) +
            ((f (twoPointOrderRayEigenLow x y ε) - f 0 : ℝ) : ℂ) -
            ((f y - f 0 : ℝ) : ℂ))) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hbase :=
        twoPointCStarDiagonalMatrix_cfcₙ_entry_formula
          (f := f) hxy (1 : Fin 2) (1 : Fin 2)
      have hM :
          (twoPointCStarOrderRayMatrix x y ε) 1 1 =
            ((y + ε : ℝ) : ℂ) := by
        simp [twoPointCStarOrderRayMatrix,
          cStarDiagonalPerturbation, diagonalPerturbation,
          diagonalMatrix, rankOnePerturbation,
          twoPointNodes, Matrix.vecMulVec_apply]
      rw [twoPointCFCOrderRayDifference_entry_spectralFormula
          f x y hε (1 : Fin 2) (1 : Fin 2),
        hbase, hM]
      simp [twoPointNodes, twoPointOrderRaySpectralIntercept]
      ring
    by_cases hlt : x < y
    · have hlow :
          Filter.Tendsto
            (fun ε : ℝ => twoPointOrderRayEigenLow x y ε)
            (𝓝[>] (0 : ℝ)) (𝓝 x) := by
        simpa [min_eq_left (le_of_lt hlt)] using
          twoPointOrderRayEigenLow_tendsto_min x y
      have hdiff :
          Filter.Tendsto
            (fun ε : ℝ =>
              ((y + ε : ℝ) - twoPointOrderRayEigenLow x y ε : ℝ))
            (𝓝[>] (0 : ℝ)) (𝓝 (y - x)) := by
        have hyeps :
            Filter.Tendsto (fun ε : ℝ => y + ε)
              (𝓝[>] (0 : ℝ)) (𝓝 y) := by
          have hcont : ContinuousAt (fun ε : ℝ => y + ε) 0 := by
            fun_prop
          simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
        exact hyeps.sub hlow
      have hf_low :
          Filter.Tendsto
            (fun ε : ℝ => f (twoPointOrderRayEigenLow x y ε))
            (𝓝[>] (0 : ℝ)) (𝓝 (f x)) :=
        hcx.tendsto.comp hlow
      have hprod :
          Filter.Tendsto
            (fun ε : ℝ =>
              (twoPointOrderRaySpectralSlope f x y ε : ℂ) *
                (((y + ε : ℝ) -
                  twoPointOrderRayEigenLow x y ε : ℝ) : ℂ))
            (𝓝[>] (0 : ℝ))
            (𝓝 ((twoPointRawDividedDifference f x y : ℂ) *
              ((y - x : ℝ) : ℂ))) :=
        hslopeC.mul (Filter.tendsto_ofReal_iff.mpr hdiff)
      have hvalue :
          Filter.Tendsto
            (fun ε : ℝ =>
              ((f (twoPointOrderRayEigenLow x y ε) - f 0 : ℝ) : ℂ))
            (𝓝[>] (0 : ℝ)) (𝓝 ((f x - f 0 : ℝ) : ℂ)) :=
        Filter.tendsto_ofReal_iff.mpr (hf_low.sub tendsto_const_nhds)
      have htarget :
          (twoPointRawDividedDifference f x y : ℂ) *
              ((y - x : ℝ) : ℂ) +
            ((f x - f 0 : ℝ) : ℂ) - ((f y - f 0 : ℝ) : ℂ) = 0 := by
        have htargetR :
            twoPointRawDividedDifference f x y * (y - x) +
                (f x - f 0) - (f y - f 0) = 0 := by
          have hyx : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
          unfold twoPointRawDividedDifference
          field_simp [hyx]
          ring
        exact_mod_cast htargetR
      have htend :
          Filter.Tendsto
            (fun ε : ℝ =>
              ((twoPointOrderRaySpectralSlope f x y ε : ℂ) *
                  ((y + ε : ℝ) -
                    twoPointOrderRayEigenLow x y ε : ℝ) +
                ((f (twoPointOrderRayEigenLow x y ε) - f 0 : ℝ) : ℂ) -
                ((f y - f 0 : ℝ) : ℂ)))
            (𝓝[>] (0 : ℝ))
            (𝓝 ((twoPointRawDividedDifference f x y : ℂ) *
              ((y - x : ℝ) : ℂ) +
              ((f x - f 0 : ℝ) : ℂ) - ((f y - f 0 : ℝ) : ℂ))) :=
        (hprod.add hvalue).sub tendsto_const_nhds
      rw [htarget] at htend
      simpa using htend.congr' hformula.symm
    · have hyltx : y < x := lt_of_le_of_ne (le_of_not_gt hlt) hxy.symm
      have hlow :
          Filter.Tendsto
            (fun ε : ℝ => twoPointOrderRayEigenLow x y ε)
            (𝓝[>] (0 : ℝ)) (𝓝 y) := by
        simpa [min_eq_right (le_of_lt hyltx)] using
          twoPointOrderRayEigenLow_tendsto_min x y
      have hdiff :
          Filter.Tendsto
            (fun ε : ℝ =>
              ((y + ε : ℝ) - twoPointOrderRayEigenLow x y ε : ℝ))
            (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
        have hyeps :
            Filter.Tendsto (fun ε : ℝ => y + ε)
              (𝓝[>] (0 : ℝ)) (𝓝 y) := by
          have hcont : ContinuousAt (fun ε : ℝ => y + ε) 0 := by
            fun_prop
          simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
        simpa using hyeps.sub hlow
      have hf_low :
          Filter.Tendsto
            (fun ε : ℝ => f (twoPointOrderRayEigenLow x y ε))
            (𝓝[>] (0 : ℝ)) (𝓝 (f y)) :=
        hcy.tendsto.comp hlow
      have hprod :
          Filter.Tendsto
            (fun ε : ℝ =>
              (twoPointOrderRaySpectralSlope f x y ε : ℂ) *
                (((y + ε : ℝ) -
                  twoPointOrderRayEigenLow x y ε : ℝ) : ℂ))
            (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
        simpa using hslopeC.mul (Filter.tendsto_ofReal_iff.mpr hdiff)
      have hvalue :
          Filter.Tendsto
            (fun ε : ℝ =>
              ((f (twoPointOrderRayEigenLow x y ε) - f 0 : ℝ) : ℂ))
          (𝓝[>] (0 : ℝ)) (𝓝 ((f y - f 0 : ℝ) : ℂ)) :=
        Filter.tendsto_ofReal_iff.mpr (hf_low.sub tendsto_const_nhds)
      have htarget :
          Filter.Tendsto
            (fun ε : ℝ =>
              ((twoPointOrderRaySpectralSlope f x y ε : ℂ) *
                  ((y + ε : ℝ) -
                    twoPointOrderRayEigenLow x y ε : ℝ) +
                ((f (twoPointOrderRayEigenLow x y ε) - f 0 : ℝ) : ℂ) -
                ((f y - f 0 : ℝ) : ℂ)))
            (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
        have htend :
            Filter.Tendsto
              (fun ε : ℝ =>
                (twoPointOrderRaySpectralSlope f x y ε : ℂ) *
                    (((y + ε : ℝ) -
                      twoPointOrderRayEigenLow x y ε : ℝ) : ℂ) +
                  ((f (twoPointOrderRayEigenLow x y ε) - f 0 : ℝ) : ℂ) -
                  ((f y - f 0 : ℝ) : ℂ))
              (𝓝[>] (0 : ℝ))
              (𝓝 (0 + ((f y - f 0 : ℝ) : ℂ) -
                ((f y - f 0 : ℝ) : ℂ))) :=
          (hprod.add hvalue).sub tendsto_const_nhds
        simpa using htend
      exact htarget.congr' hformula.symm

/-! ### Named positivity tests for two-point differences -/

/-- Standard basis vector used for diagonal tests in the `2×2` CFC difference. -/
def twoPointCFCOrderRayDifferenceStdBasis (i : Fin 2) : Fin 2 → ℂ :=
  Pi.single i (1 : ℂ)

/-- Named two-coordinate test vector used by the scalar extraction layer. -/
def twoPointCFCOrderRayDifferenceTestVector (a b : ℂ) : Fin 2 → ℂ :=
  fun i => if i = 0 then a else b

/--
Named quadratic test of the CFC order-ray difference against an arbitrary
vector.
-/
def twoPointCFCOrderRayDifferenceTest
    (f : ℝ → ℝ) (x y ε : ℝ) (c : Fin 2 → ℂ) : ℂ :=
  star c ⬝ᵥ
    ((CStarMatrix.ofMatrix.symm
      (twoPointCFCOrderRayDifference f x y ε)) *ᵥ c)

/--
Named diagonal entry test, phrased as the quadratic test against a standard
basis vector.
-/
def twoPointCFCOrderRayDifferenceDiagEntryTest
    (f : ℝ → ℝ) (x y ε : ℝ) (i : Fin 2) : ℂ :=
  twoPointCFCOrderRayDifferenceTest f x y ε
    (twoPointCFCOrderRayDifferenceStdBasis i)

/--
A centered raw divided-difference estimate gives the lower signed quotient
bound for the concrete two-point order-ray quotient.

This bridge is purely metric: it does not prove the centered estimate from
CFC positivity, but it fixes the way the center value `D` will be used in the
signed-bounds producer.
-/
theorem twoPointOrderRayQuotient_lower_of_rawCenter
    {f : ℝ → ℝ} {x D : ℝ}
    (hcenter :
      ∀ ε > 0,
        ∃ δ > 0,
          ∀ y ∈ Set.Ioo (-1 : ℝ) 1, y ≠ x → dist y x < δ →
            dist (twoPointRawDividedDifference f x y) D < ε) :
    ∀ ε > 0,
      ∃ δ > 0,
        ∀ y ∈ Set.Ioo (-1 : ℝ) 1, y ≠ x → dist y x < δ →
          twoPointOrderRayCenter f x D - ε <
            twoPointOrderRayQuotient f x y := by
  intro ε hε
  rcases hcenter ε hε with ⟨δ, hδ, hδcenter⟩
  refine ⟨δ, hδ, ?_⟩
  intro y hy hyx hydist
  have hdist := hδcenter y hy hyx hydist
  have hraw_lower :
      D - ε < twoPointRawDividedDifference f x y := by
    have hdist' :
        |twoPointRawDividedDifference f x y - D| < ε := by
      simpa [Real.dist_eq] using hdist
    linarith [(abs_sub_lt_iff.1 hdist').2]
  simpa [twoPointOrderRayCenter,
    twoPointOrderRayQuotient_eq_rawDividedDifference] using hraw_lower

/--
A centered raw divided-difference estimate gives the upper signed quotient
bound for the concrete two-point order-ray quotient.
-/
theorem twoPointOrderRayQuotient_upper_of_rawCenter
    {f : ℝ → ℝ} {x D : ℝ}
    (hcenter :
      ∀ ε > 0,
        ∃ δ > 0,
          ∀ y ∈ Set.Ioo (-1 : ℝ) 1, y ≠ x → dist y x < δ →
            dist (twoPointRawDividedDifference f x y) D < ε) :
    ∀ ε > 0,
      ∃ δ > 0,
        ∀ y ∈ Set.Ioo (-1 : ℝ) 1, y ≠ x → dist y x < δ →
          twoPointOrderRayQuotient f x y <
            twoPointOrderRayCenter f x D + ε := by
  intro ε hε
  rcases hcenter ε hε with ⟨δ, hδ, hδcenter⟩
  refine ⟨δ, hδ, ?_⟩
  intro y hy hyx hydist
  have hdist := hδcenter y hy hyx hydist
  have hraw_upper :
      twoPointRawDividedDifference f x y < D + ε := by
    have hdist' :
        |twoPointRawDividedDifference f x y - D| < ε := by
      simpa [Real.dist_eq] using hdist
    linarith [(abs_sub_lt_iff.1 hdist').1]
  simpa [twoPointOrderRayCenter,
    twoPointOrderRayQuotient_eq_rawDividedDifference] using hraw_upper

/-! ### One-point scalar monotonicity extraction -/

/-- One-point node family used to recover scalar monotonicity from CFC monotonicity. -/
def onePointNode (x : ℝ) : Fin 1 → ℝ :=
  fun _ => x

/-- The one-point diagonal CStarMatrix is monotone in its scalar node. -/
lemma onePointCStarDiagonalMatrix_le {x y : ℝ} (hxy : x ≤ y) :
    cStarDiagonalMatrix (onePointNode x) ≤
      cStarDiagonalMatrix (onePointNode y) := by
  rw [← sub_nonneg]
  have hdiag :
      (diagonalMatrix (onePointNode y) -
        diagonalMatrix (onePointNode x)).PosSemidef := by
    have hnonneg : 0 ≤ fun _ : Fin 1 => ((y - x : ℝ) : ℂ) := by
      intro i
      simpa using
        (show (0 : ℂ) ≤ ((y - x : ℝ) : ℂ) by
          exact_mod_cast sub_nonneg.mpr hxy)
    simpa [diagonalMatrix, onePointNode, sub_eq_add_neg] using
      (Matrix.PosSemidef.diagonal (R := ℂ) hnonneg)
  simpa [cStarDiagonalMatrix, sub_eq_add_neg] using
    cStarMatrix_nonneg_of_posSemidef hdiag

/--
One-point CFC evaluation for the normalized scalar function `t ↦ f t - f 0`.

This is the scalar specialization used to turn finite-dimensional CFC
monotonicity back into ordinary scalar monotonicity on `(-1,1)`.
-/
theorem onePointCStarMatrix_cfcₙ_apply (f : ℝ → ℝ) (x : ℝ) :
    (cfcₙ (fun t : ℝ => f t - f 0)
      (cStarDiagonalMatrix (onePointNode x)) 0 0 : ℂ) =
        (f x - f 0 : ℂ) := by
  let D : CStarMatrix (Fin 1) (Fin 1) ℂ :=
    cStarDiagonalMatrix (onePointNode x)
  let g : ℝ → ℝ := fun t => f t - f 0
  let c : ℝ := f x - f 0
  have hspectrum : spectrum ℝ D ⊆ ({x} : Set ℝ) := by
    intro t ht
    change t ∈ spectrum ℝ
      (cStarDiagonalMatrix (onePointNode x)) at ht
    rw [cStarDiagonalMatrix] at ht
    change t ∈ spectrum ℝ (diagonalMatrix (onePointNode x)) at ht
    rw [← spectrum.preimage_algebraMap ℂ] at ht
    simp only [Set.mem_preimage] at ht
    change (t : ℂ) ∈ spectrum ℂ (diagonalMatrix (onePointNode x)) at ht
    rw [diagonalMatrix, spectrum_diagonal] at ht
    rcases ht with ⟨i, hi⟩
    have hti : t = onePointNode x i := Complex.ofReal_injective hi.symm
    simp [onePointNode, hti]
  have hfinite : (quasispectrum ℝ D).Finite := by
    have hset : ({0, x} : Set ℝ).Finite := by
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
  have hcont : ContinuousOn g (quasispectrum ℝ D) :=
    hfinite.continuousOn _
  have hsa : IsSelfAdjoint D := by
    rw [isSelfAdjoint_iff]
    have h := (diagonalMatrix_isSelfAdjoint
      (onePointNode x)).star_eq
    simpa [D, cStarDiagonalMatrix] using congrArg CStarMatrix.ofMatrix h
  have hmatch : Set.EqOn g (fun _ : ℝ => c) (spectrum ℝ D) := by
    intro t ht
    have ht' := hspectrum ht
    rw [Set.mem_singleton_iff] at ht'
    simp [g, c, ht']
  have hcfc :
      cfcₙ g D =
        algebraMap ℝ (CStarMatrix (Fin 1) (Fin 1) ℂ) c := by
    calc
      cfcₙ g D = cfc g D := by
        exact cfcₙ_eq_cfc (a := D) (hf := hcont) (hf0 := by simp [g])
      _ = cfc (fun _ : ℝ => c) D := by
        exact cfc_congr hmatch
      _ = algebraMap ℝ (CStarMatrix (Fin 1) (Fin 1) ℂ) c := by
        exact cfc_const c D (ha := hsa)
  have hentry := congrArg (fun M : CStarMatrix (Fin 1) (Fin 1) ℂ => M 0 0) hcfc
  simpa [D, g, c, cStarDiagonalMatrix, Matrix.algebraMap_matrix_apply] using hentry

/-- Finite matrix monotonicity restricts to ordinary scalar monotonicity on `(-1,1)`. -/
theorem scalarMonotoneOn_Ioo_of_finiteMatrixMonotone
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f) :
    MonotoneOn f (Set.Ioo (-1 : ℝ) 1) := by
  intro x hx y hy hxy
  let Dx : CStarMatrix (Fin 1) (Fin 1) ℂ :=
    cStarDiagonalMatrix (onePointNode x)
  let Dy : CStarMatrix (Fin 1) (Fin 1) ℂ :=
    cStarDiagonalMatrix (onePointNode y)
  have hxnode : ∀ i : Fin 1, onePointNode x i ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro i
    simpa [onePointNode] using hx
  have hynode : ∀ i : Fin 1, onePointNode y i ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro i
    simpa [onePointNode] using hy
  have hDx : Dx ∈ cStarFiniteMatrixDomain 1 := by
    simpa [Dx] using cStarDiagonalMatrix_mem_domain
      (onePointNode x) hxnode
  have hDy : Dy ∈ cStarFiniteMatrixDomain 1 := by
    simpa [Dy] using cStarDiagonalMatrix_mem_domain
      (onePointNode y) hynode
  have hDxy : Dx ≤ Dy := by
    simpa [Dx, Dy] using onePointCStarDiagonalMatrix_le hxy
  haveI : StarOrderedRing (CStarMatrix (Fin 1) (Fin 1) ℂ) :=
    CStarMatrix.instStarOrderedRing
  haveI : FiniteDimensional ℂ (CStarMatrix (Fin 1) (Fin 1) ℂ) := by
    change FiniteDimensional ℂ (Matrix (Fin 1) (Fin 1) ℂ)
    infer_instance
  have hcfc_le :
      cfcₙ (fun t : ℝ => f t - f 0) Dx ≤
        cfcₙ (fun t : ℝ => f t - f 0) Dy :=
    hfinite.cfc_monotone_matrix 1 hDx hDy hDxy
  have hdiff_nonneg :
      0 ≤ cfcₙ (fun t : ℝ => f t - f 0) Dy -
        cfcₙ (fun t : ℝ => f t - f 0) Dx := by
    exact sub_nonneg.mpr hcfc_le
  have hquad := cStarMatrix_quadratic_nonneg_of_nonneg
    hdiff_nonneg (Pi.single (0 : Fin 1) (1 : ℂ))
  have hxentry :
      (cfcₙ (fun t : ℝ => f t - f 0) Dx 0 0 : ℂ) =
        (f x - f 0 : ℂ) := by
    simpa [Dx] using onePointCStarMatrix_cfcₙ_apply f x
  have hyentry :
      (cfcₙ (fun t : ℝ => f t - f 0) Dy 0 0 : ℂ) =
        (f y - f 0 : ℂ) := by
    simpa [Dy] using onePointCStarMatrix_cfcₙ_apply f y
  have hcomplex :
      (0 : ℂ) ≤ ((f y - f 0) - (f x - f 0) : ℂ) := by
    simpa [Matrix.sub_apply, hxentry, hyentry] using hquad
  have hreal : 0 ≤ (f y - f 0) - (f x - f 0) := by
    exact_mod_cast hcomplex
  linarith

/-! ### One-sided scalar limits from monotonicity -/

/-- Left scalar limit value supplied by monotonicity on `(-1,1)`. -/
def scalarLeftLimitValue (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  sSup (f '' Set.Ioo (-1 : ℝ) x)

/-- Right scalar limit value supplied by monotonicity on `(-1,1)`. -/
def scalarRightLimitValue (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  sInf (f '' Set.Ioo x (1 : ℝ))

/-- Finite matrix monotonicity gives the left scalar limit at each interior point. -/
theorem scalarLeftLimit_tendsto
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Filter.Tendsto f (𝓝[<] x) (𝓝 (scalarLeftLimitValue f x)) := by
  have hmono := scalarMonotoneOn_Ioo_of_finiteMatrixMonotone hfinite
  have hmono_left : MonotoneOn f (Set.Ioo (-1 : ℝ) x) := by
    intro a ha b hb hab
    exact hmono ⟨ha.1, lt_trans ha.2 hx.2⟩ ⟨hb.1, lt_trans hb.2 hx.2⟩ hab
  have hnonempty : (Set.Ioo (-1 : ℝ) x).Nonempty :=
    Set.nonempty_Ioo.mpr hx.1
  have hbdd : BddAbove (f '' Set.Ioo (-1 : ℝ) x) := by
    refine ⟨f x, ?_⟩
    intro z hz
    rcases hz with ⟨a, ha, rfl⟩
    exact hmono ⟨ha.1, lt_trans ha.2 hx.2⟩ hx (le_of_lt ha.2)
  simpa [scalarLeftLimitValue] using
    MonotoneOn.tendsto_nhdsWithin_Ioo_left hnonempty hmono_left hbdd

/-- Finite matrix monotonicity gives the right scalar limit at each interior point. -/
theorem scalarRightLimit_tendsto
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Filter.Tendsto f (𝓝[>] x) (𝓝 (scalarRightLimitValue f x)) := by
  have hmono := scalarMonotoneOn_Ioo_of_finiteMatrixMonotone hfinite
  have hmono_right : MonotoneOn f (Set.Ioo x (1 : ℝ)) := by
    intro a ha b hb hab
    exact hmono ⟨lt_trans hx.1 ha.1, ha.2⟩ ⟨lt_trans hx.1 hb.1, hb.2⟩ hab
  have hnonempty : (Set.Ioo x (1 : ℝ)).Nonempty :=
    Set.nonempty_Ioo.mpr hx.2
  have hbdd : BddBelow (f '' Set.Ioo x (1 : ℝ)) := by
    refine ⟨f x, ?_⟩
    intro z hz
    rcases hz with ⟨a, ha, rfl⟩
    exact hmono hx ⟨lt_trans hx.1 ha.1, ha.2⟩ (le_of_lt ha.1)
  simpa [scalarRightLimitValue] using
    MonotoneOn.tendsto_nhdsWithin_Ioo_right hnonempty hmono_right hbdd

/--
Full `2×2` CFC order comparison gives the left scalar limit at each interior
point.
-/
theorem scalarLeftLimit_tendsto_of_twoByTwo_cfc_order
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Filter.Tendsto f (𝓝[<] x) (𝓝 (scalarLeftLimitValue f x)) := by
  have hmono := scalarMonotoneOn_Ioo_of_twoByTwo_cfc_order h2
  have hmono_left : MonotoneOn f (Set.Ioo (-1 : ℝ) x) := by
    intro a ha b hb hab
    exact hmono ⟨ha.1, lt_trans ha.2 hx.2⟩ ⟨hb.1, lt_trans hb.2 hx.2⟩ hab
  have hnonempty : (Set.Ioo (-1 : ℝ) x).Nonempty :=
    Set.nonempty_Ioo.mpr hx.1
  have hbdd : BddAbove (f '' Set.Ioo (-1 : ℝ) x) := by
    refine ⟨f x, ?_⟩
    intro z hz
    rcases hz with ⟨a, ha, rfl⟩
    exact hmono ⟨ha.1, lt_trans ha.2 hx.2⟩ hx (le_of_lt ha.2)
  simpa [scalarLeftLimitValue] using
    MonotoneOn.tendsto_nhdsWithin_Ioo_left hnonempty hmono_left hbdd

/--
Full `2×2` CFC order comparison gives the right scalar limit at each interior
point.
-/
theorem scalarRightLimit_tendsto_of_twoByTwo_cfc_order
    {f : ℝ → ℝ}
    (h2 :
      ∀ {A B : CStarMatrix (Fin 2) (Fin 2) ℂ},
        A ∈ cStarFiniteMatrixDomain 2 →
        B ∈ cStarFiniteMatrixDomain 2 →
        A ≤ B →
          cfcₙ (fun t : ℝ => f t - f 0) A ≤
            cfcₙ (fun t : ℝ => f t - f 0) B)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Filter.Tendsto f (𝓝[>] x) (𝓝 (scalarRightLimitValue f x)) := by
  have hmono := scalarMonotoneOn_Ioo_of_twoByTwo_cfc_order h2
  have hmono_right : MonotoneOn f (Set.Ioo x (1 : ℝ)) := by
    intro a ha b hb hab
    exact hmono ⟨lt_trans hx.1 ha.1, ha.2⟩ ⟨lt_trans hx.1 hb.1, hb.2⟩ hab
  have hnonempty : (Set.Ioo x (1 : ℝ)).Nonempty :=
    Set.nonempty_Ioo.mpr hx.2
  have hbdd : BddBelow (f '' Set.Ioo x (1 : ℝ)) := by
    refine ⟨f x, ?_⟩
    intro z hz
    rcases hz with ⟨a, ha, rfl⟩
    exact hmono hx ⟨lt_trans hx.1 ha.1, ha.2⟩ (le_of_lt ha.1)
  simpa [scalarRightLimitValue] using
    MonotoneOn.tendsto_nhdsWithin_Ioo_right hnonempty hmono_right hbdd

/-- The left scalar limit supplied by monotonicity is below the point value. -/
theorem scalarLeftLimit_le_value
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    scalarLeftLimitValue f x ≤ f x := by
  have hmono := scalarMonotoneOn_Ioo_of_finiteMatrixMonotone hfinite
  refine csSup_le (Set.image_nonempty.mpr (Set.nonempty_Ioo.mpr hx.1)) ?_
  intro z hz
  rcases hz with ⟨a, ha, rfl⟩
  exact hmono ⟨ha.1, lt_trans ha.2 hx.2⟩ hx (le_of_lt ha.2)

/-- The right scalar limit supplied by monotonicity is above the point value. -/
theorem scalarValue_le_rightLimit
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    f x ≤ scalarRightLimitValue f x := by
  have hmono := scalarMonotoneOn_Ioo_of_finiteMatrixMonotone hfinite
  refine le_csInf (Set.image_nonempty.mpr (Set.nonempty_Ioo.mpr hx.2)) ?_
  intro z hz
  rcases hz with ⟨a, ha, rfl⟩
  exact hmono hx ⟨lt_trans hx.1 ha.1, ha.2⟩ (le_of_lt ha.1)

/-! ### Special left path spectral geometry -/

/-- Lower branch coefficient for the special left-hand two-point order ray. -/
def twoPointOrderRayLeftPathLowCoeff : ℝ :=
  (1 - Real.sqrt 5) / 2

/-- Upper branch coefficient for the special left-hand two-point order ray. -/
def twoPointOrderRayLeftPathHighCoeff : ℝ :=
  (1 + Real.sqrt 5) / 2

/--
On the special path `(x, x - δ, δ)`, the lower spectral branch has an explicit
linear form.
-/
lemma twoPointOrderRayEigenLow_leftPath_eq
    {x δ : ℝ} (hδ : 0 < δ) :
    twoPointOrderRayEigenLow x (x - δ) δ =
      x + δ * twoPointOrderRayLeftPathLowCoeff := by
  have hsqrt :
      Real.sqrt ((x - (x - δ)) ^ 2 + 4 * δ ^ 2) =
        δ * Real.sqrt 5 := by
    have hδ0 : 0 ≤ δ := le_of_lt hδ
    rw [show (x - (x - δ)) ^ 2 + 4 * δ ^ 2 = 5 * δ ^ 2 by ring]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5)]
    rw [show Real.sqrt (δ ^ 2) = δ by
      simpa [abs_of_nonneg hδ0] using Real.sqrt_sq_eq_abs δ]
    ring
  rw [twoPointOrderRayEigenLow, twoPointOrderRayTrace,
    twoPointOrderRayGap, hsqrt,
    twoPointOrderRayLeftPathLowCoeff]
  ring_nf

/--
On the special path `(x, x - δ, δ)`, the upper spectral branch has an explicit
linear form.
-/
lemma twoPointOrderRayEigenHigh_leftPath_eq
    {x δ : ℝ} (hδ : 0 < δ) :
    twoPointOrderRayEigenHigh x (x - δ) δ =
      x + δ * twoPointOrderRayLeftPathHighCoeff := by
  have hsqrt :
      Real.sqrt ((x - (x - δ)) ^ 2 + 4 * δ ^ 2) =
        δ * Real.sqrt 5 := by
    have hδ0 : 0 ≤ δ := le_of_lt hδ
    rw [show (x - (x - δ)) ^ 2 + 4 * δ ^ 2 = 5 * δ ^ 2 by ring]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5)]
    rw [show Real.sqrt (δ ^ 2) = δ by
      simpa [abs_of_nonneg hδ0] using Real.sqrt_sq_eq_abs δ]
    ring
  rw [twoPointOrderRayEigenHigh, twoPointOrderRayTrace,
    twoPointOrderRayGap, hsqrt,
    twoPointOrderRayLeftPathHighCoeff]
  ring_nf

/-- The lower branch on the left-hand special path approaches `x` from the left. -/
lemma twoPointOrderRayEigenLow_leftPath_tendsto_left
    (x : ℝ) :
    Filter.Tendsto
      (fun δ : ℝ => twoPointOrderRayEigenLow x (x - δ) δ)
      (𝓝[>] (0 : ℝ)) (𝓝[<] x) := by
  have hsqrt_gt_one : 1 < Real.sqrt 5 := by
    have hsq : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by
      rw [Real.sq_sqrt]
      norm_num
    have hnonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    nlinarith
  have hlow_neg : twoPointOrderRayLeftPathLowCoeff < 0 := by
    rw [twoPointOrderRayLeftPathLowCoeff]
    linarith
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hcont :
        ContinuousAt
          (fun δ : ℝ => x + δ * twoPointOrderRayLeftPathLowCoeff) 0 := by
      fun_prop
    have ht :
        Filter.Tendsto
          (fun δ : ℝ => x + δ * twoPointOrderRayLeftPathLowCoeff)
          (𝓝[>] (0 : ℝ)) (𝓝 x) := by
      simpa using hcont.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
    refine Filter.Tendsto.congr' ?_ ht
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (twoPointOrderRayEigenLow_leftPath_eq hδ).symm
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδpos : 0 < δ := by simpa using hδ
    rw [twoPointOrderRayEigenLow_leftPath_eq hδpos]
    have hmul : δ * twoPointOrderRayLeftPathLowCoeff < 0 :=
      mul_neg_of_pos_of_neg hδpos hlow_neg
    have : x + δ * twoPointOrderRayLeftPathLowCoeff < x := by
      linarith
    simpa [Set.mem_Iio] using this

/-- The upper branch on the left-hand special path approaches `x` from the right. -/
lemma twoPointOrderRayEigenHigh_leftPath_tendsto_right
    (x : ℝ) :
    Filter.Tendsto
      (fun δ : ℝ => twoPointOrderRayEigenHigh x (x - δ) δ)
      (𝓝[>] (0 : ℝ)) (𝓝[>] x) := by
  have hhigh_pos : 0 < twoPointOrderRayLeftPathHighCoeff := by
    rw [twoPointOrderRayLeftPathHighCoeff]
    have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    positivity
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hcont :
        ContinuousAt
          (fun δ : ℝ => x + δ * twoPointOrderRayLeftPathHighCoeff) 0 := by
      fun_prop
    have ht :
        Filter.Tendsto
          (fun δ : ℝ => x + δ * twoPointOrderRayLeftPathHighCoeff)
          (𝓝[>] (0 : ℝ)) (𝓝 x) := by
      simpa using hcont.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
    refine Filter.Tendsto.congr' ?_ ht
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (twoPointOrderRayEigenHigh_leftPath_eq hδ).symm
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδpos : 0 < δ := by simpa using hδ
    rw [twoPointOrderRayEigenHigh_leftPath_eq hδpos]
    have hmul : 0 < δ * twoPointOrderRayLeftPathHighCoeff :=
      mul_pos hδpos hhigh_pos
    simpa [Set.mem_Ioi] using (lt_add_of_pos_right x hmul :
      x < x + δ * twoPointOrderRayLeftPathHighCoeff)

/--
Along the left-hand special path, the lower spectral branch sees the scalar
left limit.
-/
theorem scalarLeftLimit_tendsto_twoPointEigenLow_leftPath
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Filter.Tendsto
      (fun δ : ℝ => f (twoPointOrderRayEigenLow x (x - δ) δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (scalarLeftLimitValue f x)) :=
  (scalarLeftLimit_tendsto hfinite hx).comp
    (twoPointOrderRayEigenLow_leftPath_tendsto_left x)

/--
Along the left-hand special path, the upper spectral branch sees the scalar
right limit.
-/
theorem scalarRightLimit_tendsto_twoPointEigenHigh_leftPath
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Filter.Tendsto
      (fun δ : ℝ => f (twoPointOrderRayEigenHigh x (x - δ) δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (scalarRightLimitValue f x)) :=
  (scalarRightLimit_tendsto hfinite hx).comp
    (twoPointOrderRayEigenHigh_leftPath_tendsto_right x)

/-- The moving node `x - δ` approaches `x` from the left as `δ ↓ 0`. -/
lemma x_sub_delta_tendsto_left (x : ℝ) :
    Filter.Tendsto (fun δ : ℝ => x - δ) (𝓝[>] (0 : ℝ)) (𝓝[<] x) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hcont : ContinuousAt (fun δ : ℝ => x - δ) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact sub_lt_self x hδ

/-- Along `x - δ`, the scalar function sees the left limit. -/
theorem scalarLeftLimit_tendsto_x_sub_delta
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Filter.Tendsto (fun δ : ℝ => f (x - δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (scalarLeftLimitValue f x)) :=
  (scalarLeftLimit_tendsto hfinite hx).comp
    (x_sub_delta_tendsto_left x)

/-! ### Left special path positivity substrate -/

/-!
The next few lemmas are the non-cyclic positivity substrate for the special
path `(x, x - δ, δ)`.  The earlier fixed-`y` order-ray comparison cannot be
used here because the second node varies with the ray parameter.
-/

/-- On the left special path, the moving diagonal base stays in the CFC domain. -/
lemma twoPointCStarDiagonal_leftPath_mem_domain_eventually
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      cStarDiagonalMatrix (twoPointNodes x (x - δ)) ∈
        cStarFiniteMatrixDomain 2 := by
  have hy_tendsto :
      Filter.Tendsto (fun δ : ℝ => x - δ) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    have hcont : ContinuousAt (fun δ : ℝ => x - δ) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hy_eventually :
      ∀ᶠ δ in 𝓝[>] (0 : ℝ), x - δ ∈ Set.Ioo (-1 : ℝ) 1 :=
    hy_tendsto.eventually (isOpen_Ioo.mem_nhds hx)
  filter_upwards [hy_eventually] with δ hy
  exact cStarDiagonalMatrix_mem_domain
    (twoPointNodes x (x - δ)) (twoPointNodes_mem_Ioo hx hy)

/-- On the left special path, the two-point order ray stays in the CFC domain. -/
lemma twoPointCStarOrderRay_leftPath_mem_domain_eventually
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      twoPointCStarOrderRayMatrix x (x - δ) δ ∈
        cStarFiniteMatrixDomain 2 := by
  have hlow_nhds :
      Filter.Tendsto
        (fun δ : ℝ => twoPointOrderRayEigenLow x (x - δ) δ)
        (𝓝[>] (0 : ℝ)) (𝓝 x) :=
    (twoPointOrderRayEigenLow_leftPath_tendsto_left x).mono_right
      nhdsWithin_le_nhds
  have hhigh_nhds :
      Filter.Tendsto
        (fun δ : ℝ => twoPointOrderRayEigenHigh x (x - δ) δ)
        (𝓝[>] (0 : ℝ)) (𝓝 x) :=
    (twoPointOrderRayEigenHigh_leftPath_tendsto_right x).mono_right
      nhdsWithin_le_nhds
  have hlow_eventually :
      ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        twoPointOrderRayEigenLow x (x - δ) δ ∈ Set.Ioo (-1 : ℝ) 1 :=
    hlow_nhds.eventually (isOpen_Ioo.mem_nhds hx)
  have hhigh_eventually :
      ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        twoPointOrderRayEigenHigh x (x - δ) δ ∈ Set.Ioo (-1 : ℝ) 1 :=
    hhigh_nhds.eventually (isOpen_Ioo.mem_nhds hx)
  filter_upwards [hlow_eventually, hhigh_eventually] with δ hlow hhigh
  refine ⟨?_, ?_⟩
  · simpa [twoPointCStarOrderRayMatrix] using
      cStarDiagonalPerturbation_isSelfAdjoint
        (twoPointNodes x (x - δ)) (fun _ : Fin 2 => (1 : ℂ)) δ
  · intro t ht
    have htq : t = 0 ∨
        t ∈ spectrum ℝ (twoPointCStarOrderRayMatrix x (x - δ) δ) :=
      (mem_quasispectrum_iff
        (a := twoPointCStarOrderRayMatrix x (x - δ) δ) (x := t)).mp ht
    rcases htq with hzero | hspectrum
    · have ht0 : t = 0 := by simpa using hzero
      simp [ht0]
    · have hspectral :=
        twoPointCStarOrderRayMatrix_spectrum_subset_eigenLowHigh
          x (x - δ) δ hspectrum
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hspectral
      rcases hspectral with htlow | hthigh
      · simpa [htlow] using hlow
      · simpa [hthigh] using hhigh

/--
Finite matrix monotonicity gives positivity of the CFC difference along the
left special path `(x, x - δ, δ)`.
-/
theorem twoPointCFCOrderRayDifference_nonneg_leftPath_eventually
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      0 ≤ twoPointCFCOrderRayDifference f x (x - δ) δ := by
  filter_upwards
    [twoPointCStarDiagonal_leftPath_mem_domain_eventually hx,
      twoPointCStarOrderRay_leftPath_mem_domain_eventually hx,
      self_mem_nhdsWithin] with δ hbase hray hδpos
  have hle_ray :
      cStarDiagonalMatrix (twoPointNodes x (x - δ)) ≤
        twoPointCStarOrderRayMatrix x (x - δ) δ :=
    twoPointCStarOrderRay_le_of_nonneg x (x - δ) (le_of_lt hδpos)
  haveI : StarOrderedRing (CStarMatrix (Fin 2) (Fin 2) ℂ) :=
    CStarMatrix.instStarOrderedRing
  haveI : FiniteDimensional ℂ (CStarMatrix (Fin 2) (Fin 2) ℂ) := by
    change FiniteDimensional ℂ (Matrix (Fin 2) (Fin 2) ℂ)
    infer_instance
  have hle :=
    hfinite.cfc_monotone_matrix 2 hbase hray hle_ray
  simpa [twoPointCFCOrderRayDifference] using sub_nonneg.mpr hle

/--
Positive CFC differences along the left special path give nonnegative named
quadratic tests.
-/
theorem twoPointCFCOrderRayDifference_testVector_nonneg_leftPath_eventually
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (c : Fin 2 → ℂ) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      0 ≤ twoPointCFCOrderRayDifferenceTest f x (x - δ) δ c := by
  filter_upwards
    [twoPointCFCOrderRayDifference_nonneg_leftPath_eventually
      hfinite hx] with δ hnonneg
  simpa [twoPointCFCOrderRayDifferenceTest] using
    cStarMatrix_quadratic_nonneg_of_nonneg hnonneg c

/-! ### Null-vector extraction of the left jump -/

/--
Test vector for the left special path.  With
`β = twoPointOrderRayLeftPathHighCoeff`, the vector `(1,-β)` cancels
the upper spectral branch in the quadratic CFC difference.
-/
def twoPointOrderRayLeftPathNullVector : Fin 2 → ℂ :=
  fun i => if i = 0 then 1 else
    -((twoPointOrderRayLeftPathHighCoeff : ℝ) : ℂ)

/-- The two left-path spectral coefficients add to one. -/
lemma twoPointOrderRayLeftPath_coeff_sum :
    twoPointOrderRayLeftPathLowCoeff +
      twoPointOrderRayLeftPathHighCoeff = 1 := by
  rw [twoPointOrderRayLeftPathLowCoeff,
    twoPointOrderRayLeftPathHighCoeff]
  ring

/-- The two left-path spectral coefficients multiply to `-1`. -/
lemma twoPointOrderRayLeftPath_coeff_mul :
    twoPointOrderRayLeftPathLowCoeff *
      twoPointOrderRayLeftPathHighCoeff = -1 := by
  rw [twoPointOrderRayLeftPathLowCoeff,
    twoPointOrderRayLeftPathHighCoeff]
  have hsqrt_sq : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  ring_nf
  rw [hsqrt_sq]
  ring

/--
Exact left-special-path quadratic test formula.  The null vector removes the
upper-branch singular contribution, leaving only the scalar left jump in the
limit.
-/
theorem twoPointCFCOrderRayDifference_leftPath_nullVector_formula
    (f : ℝ → ℝ) (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    twoPointCFCOrderRayDifferenceTest f x (x - δ) δ
      twoPointOrderRayLeftPathNullVector =
        (((1 + twoPointOrderRayLeftPathHighCoeff ^ 2) *
            f (twoPointOrderRayEigenLow x (x - δ) δ) -
          f x -
          twoPointOrderRayLeftPathHighCoeff ^ 2 * f (x - δ) : ℝ) : ℂ) := by
  let β : ℝ := twoPointOrderRayLeftPathHighCoeff
  let low : ℝ := twoPointOrderRayEigenLow x (x - δ) δ
  have hxy : x ≠ x - δ := by linarith
  have h00 :=
    twoPointCFCOrderRayDifference_entry_spectralFormula
      f x (x - δ) hδ (0 : Fin 2) (0 : Fin 2)
  have h01 :=
    twoPointCFCOrderRayDifference_entry_spectralFormula
      f x (x - δ) hδ (0 : Fin 2) (1 : Fin 2)
  have h10 :=
    twoPointCFCOrderRayDifference_entry_spectralFormula
      f x (x - δ) hδ (1 : Fin 2) (0 : Fin 2)
  have h11 :=
    twoPointCFCOrderRayDifference_entry_spectralFormula
      f x (x - δ) hδ (1 : Fin 2) (1 : Fin 2)
  have hbase00 :=
    twoPointCStarDiagonalMatrix_cfcₙ_entry_formula
      (f := f) hxy (0 : Fin 2) (0 : Fin 2)
  have hbase01 :=
    twoPointCStarDiagonalMatrix_cfcₙ_entry_formula
      (f := f) hxy (0 : Fin 2) (1 : Fin 2)
  have hbase10 :=
    twoPointCStarDiagonalMatrix_cfcₙ_entry_formula
      (f := f) hxy (1 : Fin 2) (0 : Fin 2)
  have hbase11 :=
    twoPointCStarDiagonalMatrix_cfcₙ_entry_formula
      (f := f) hxy (1 : Fin 2) (1 : Fin 2)
  have hM00 :
      (twoPointCStarOrderRayMatrix x (x - δ) δ) 0 0 =
        ((x + δ : ℝ) : ℂ) := by
    simp [twoPointCStarOrderRayMatrix, cStarDiagonalPerturbation,
      diagonalPerturbation, diagonalMatrix,
      rankOnePerturbation, twoPointNodes, Matrix.vecMulVec_apply]
  have hM01 :
      (twoPointCStarOrderRayMatrix x (x - δ) δ) 0 1 =
        (δ : ℂ) := by
    simp [twoPointCStarOrderRayMatrix, cStarDiagonalPerturbation,
      diagonalPerturbation, diagonalMatrix,
      rankOnePerturbation, twoPointNodes, Matrix.vecMulVec_apply]
  have hM10 :
      (twoPointCStarOrderRayMatrix x (x - δ) δ) 1 0 =
        (δ : ℂ) := by
    simp [twoPointCStarOrderRayMatrix, cStarDiagonalPerturbation,
      diagonalPerturbation, diagonalMatrix,
      rankOnePerturbation, twoPointNodes, Matrix.vecMulVec_apply]
  have hM11 :
      (twoPointCStarOrderRayMatrix x (x - δ) δ) 1 1 =
        (x : ℂ) := by
    simp [twoPointCStarOrderRayMatrix, cStarDiagonalPerturbation,
      diagonalPerturbation, diagonalMatrix,
      rankOnePerturbation, twoPointNodes, Matrix.vecMulVec_apply]
  have hlow_eq : low =
      x + δ * twoPointOrderRayLeftPathLowCoeff :=
    twoPointOrderRayEigenLow_leftPath_eq hδ
  have hcoeff_cancel :
      (1 - 2 * β) -
        twoPointOrderRayLeftPathLowCoeff * (1 + β ^ 2) = 0 := by
    have hsum := twoPointOrderRayLeftPath_coeff_sum
    have hmul := twoPointOrderRayLeftPath_coeff_mul
    dsimp [β]
    nlinarith
  simp only [twoPointCFCOrderRayDifferenceTest, dotProduct, Pi.star_apply,
    twoPointOrderRayLeftPathNullVector, Fin.isValue, RCLike.star_def, Matrix.mulVec,
    CStarMatrix.ofMatrix_symm_apply, mul_ite, mul_one, mul_neg, Fin.sum_univ_two,
    ↓reduceIte, one_ne_zero, map_one, one_mul, map_neg, Complex.conj_ofReal, neg_mul,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_pow]
  rw [twoPointCFCOrderRayDifference_entry_direct_formula
      (f := f) (x := x) (y := x - δ) (ε := δ) (i := 0) (j := 0),
    twoPointCFCOrderRayDifference_entry_direct_formula
      (f := f) (x := x) (y := x - δ) (ε := δ) (i := 0) (j := 1),
    twoPointCFCOrderRayDifference_entry_direct_formula
      (f := f) (x := x) (y := x - δ) (ε := δ) (i := 1) (j := 0),
    twoPointCFCOrderRayDifference_entry_direct_formula
      (f := f) (x := x) (y := x - δ) (ε := δ) (i := 1) (j := 1)]
  rw [h00, h01, h10, h11, hbase00, hbase01, hbase10, hbase11,
    hM00, hM01, hM10, hM11]
  simp [twoPointNodes,
    twoPointOrderRaySpectralIntercept, low, hlow_eq]
  ring_nf
  have hcoeffC :
      ((1 : ℂ) -
          2 * (twoPointOrderRayLeftPathHighCoeff : ℂ) -
          (twoPointOrderRayLeftPathLowCoeff : ℂ) *
            (1 + (twoPointOrderRayLeftPathHighCoeff : ℂ) ^ 2)) = 0 := by
    exact_mod_cast hcoeff_cancel
  linear_combination
    ((twoPointOrderRaySpectralSlope f x (x - δ) δ : ℂ) *
      (δ : ℂ)) * hcoeffC

/--
The left-special-path null-vector test converges to the scalar left jump
`leftLimit - f x`.
-/
theorem twoPointCFCOrderRayDifference_leftPath_nullVector_tendsto_leftGap
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Filter.Tendsto
      (fun δ : ℝ =>
        twoPointCFCOrderRayDifferenceTest f x (x - δ) δ
          twoPointOrderRayLeftPathNullVector)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((scalarLeftLimitValue f x - f x : ℝ) : ℂ)) := by
  let β : ℝ := twoPointOrderRayLeftPathHighCoeff
  let L : ℝ := scalarLeftLimitValue f x
  have hformula :
      (fun δ : ℝ =>
        twoPointCFCOrderRayDifferenceTest f x (x - δ) δ
          twoPointOrderRayLeftPathNullVector)
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun δ : ℝ =>
        (((1 + β ^ 2) *
            f (twoPointOrderRayEigenLow x (x - δ) δ) -
          f x - β ^ 2 * f (x - δ) : ℝ) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    simpa [β] using
      twoPointCFCOrderRayDifference_leftPath_nullVector_formula
        f x hδ
  have hlow :
      Filter.Tendsto
        (fun δ : ℝ => f (twoPointOrderRayEigenLow x (x - δ) δ))
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    simpa [L] using
      scalarLeftLimit_tendsto_twoPointEigenLow_leftPath hfinite hx
  have hnode :
      Filter.Tendsto (fun δ : ℝ => f (x - δ))
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    simpa [L] using scalarLeftLimit_tendsto_x_sub_delta hfinite hx
  have hlow_scaled :
      Filter.Tendsto
        (fun δ : ℝ =>
          (1 + β ^ 2) * f (twoPointOrderRayEigenLow x (x - δ) δ))
        (𝓝[>] (0 : ℝ)) (𝓝 ((1 + β ^ 2) * L)) :=
    hlow.const_mul (1 + β ^ 2)
  have hnode_scaled :
      Filter.Tendsto (fun δ : ℝ => β ^ 2 * f (x - δ))
        (𝓝[>] (0 : ℝ)) (𝓝 (β ^ 2 * L)) :=
    hnode.const_mul (β ^ 2)
  have hreal :
      Filter.Tendsto
        (fun δ : ℝ =>
          (1 + β ^ 2) *
              f (twoPointOrderRayEigenLow x (x - δ) δ) -
            f x - β ^ 2 * f (x - δ))
        (𝓝[>] (0 : ℝ))
        (𝓝 ((1 + β ^ 2) * L - f x - β ^ 2 * L)) :=
    (hlow_scaled.sub tendsto_const_nhds).sub hnode_scaled
  have htarget : (1 + β ^ 2) * L - f x - β ^ 2 * L = L - f x := by
    ring
  exact (Filter.tendsto_ofReal_iff.mpr (by simpa [htarget] using hreal)).congr'
    hformula.symm

/-! ### Closed left jump exclusion -/

/--
Left jump exclusion obtained from the special-path positivity test.

This is the first closed half of the two-point positivity jump-exclusion input.
-/
theorem scalarNoLeftJump_of_twoPointCFCPositivity_closed
    {f : ℝ → ℝ} (hfinite : UnitIntervalMatrixMonotone f)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    scalarLeftLimitValue f x = f x := by
  have hnonneg_eventually :
      ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        0 ≤ twoPointCFCOrderRayDifferenceTest f x (x - δ) δ
          twoPointOrderRayLeftPathNullVector :=
    twoPointCFCOrderRayDifference_testVector_nonneg_leftPath_eventually
      hfinite hx twoPointOrderRayLeftPathNullVector
  have hlim :=
    twoPointCFCOrderRayDifference_leftPath_nullVector_tendsto_leftGap
      hfinite hx
  have hnonnegC :
      0 ≤ ((scalarLeftLimitValue f x - f x : ℝ) : ℂ) :=
    ge_of_tendsto hlim hnonneg_eventually
  have hnonnegR : 0 ≤ scalarLeftLimitValue f x - f x := by
    exact_mod_cast hnonnegC
  have hle := scalarLeftLimit_le_value hfinite hx
  linarith


end

end Quantum.TraceInequality.Loewner
