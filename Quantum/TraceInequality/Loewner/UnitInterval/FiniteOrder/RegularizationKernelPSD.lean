import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.RegularizationKernelPSDCore

/-!
# Chapter 20 Hiai regularization kernel PSD public bridges

This file packages the diagonal lower-bound data and public Stieltjes /
domination inputs into positive semidefiniteness of the Hiai-regularized
Loewner kernel.  The shifted kernel formulas and quadratic-form integral core
are in `RegularizationKernelPSDCore`.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped Interval
open scoped ComplexOrder
open scoped MatrixOrder
open scoped NNReal
open scoped ENNReal
open scoped Convolution

noncomputable section

/--
Entry-term integrability for the finite quadratic form follows from
entrywise integrability; the coefficients `star (c i)` and `c j` are constants.
-/
theorem hiaiRegularization_loewnerKernel_entryTerm_integrable_of_entry_integrable
    {φ f : ℝ → ℝ} {ε : ℝ} {n : ℕ} {x : Fin n → ℝ}
    (hentry_int : ∀ i j : Fin n,
      Integrable
        (fun t : ℝ => (φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ))
        (volume.restrict (Ι (-1 : ℝ) 1))) :
    ∀ c : Fin n → ℂ, ∀ i j : Fin n,
      Integrable
        (fun t : ℝ => star (c i) * ((φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)) * c j)
        (volume.restrict (Ι (-1 : ℝ) 1)) := by
  intro c i j
  simpa [mul_assoc] using
    ((hentry_int i j).const_mul (star (c i))).mul_const (c j)

/--
Finite-node entry integrability with public off-diagonal entries and supplied
diagonal entries.  This isolates the diagonal singular contribution:
off the diagonal, public continuity already supplies integrability.  The diagonal
integrability follows from public Löwner positivity by
`hiaiRegularization_loewnerKernel_diag_intervalIntegrable_of_loewnerPosOnUnitInterval`.
-/
theorem
    hiaiRegularization_loewnerKernel_entry_integrable_on_nodes_of_diag
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f)
    (hdiag_int : ∀ i : Fin n,
      Integrable
        (fun t : ℝ => (φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x i - ε * t) : ℂ))
        (volume.restrict (Ι (-1 : ℝ) 1))) :
    ∀ i j : Fin n,
      Integrable
        (fun t : ℝ => (φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ))
        (volume.restrict (Ι (-1 : ℝ) 1)) := by
  intro i j
  by_cases hij : x i = x j
  · simpa [hij] using hdiag_int i
  · exact
      hiaiRegularization_loewnerKernel_offdiag_uIoc_integrable_of_loewnerPosOnUnitInterval
        (φ := φ) (f := f) hφ hε (hx i) (hx j) hpos hij

/--
The full quadratic-form term integrability follows from public off-diagonal
integrability plus diagonal entry integrability on the selected nodes.
-/
theorem
    hiaiRegularization_entryTerm_integrable_of_publicOffdiag
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f)
    (hdiag_int : ∀ i : Fin n,
      Integrable
        (fun t : ℝ => (φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x i - ε * t) : ℂ))
        (volume.restrict (Ι (-1 : ℝ) 1))) :
    ∀ c : Fin n → ℂ, ∀ i j : Fin n,
      Integrable
        (fun t : ℝ => star (c i) * ((φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)) * c j)
        (volume.restrict (Ι (-1 : ℝ) 1)) :=
  hiaiRegularization_loewnerKernel_entryTerm_integrable_of_entry_integrable
    (φ := φ) (f := f) (ε := ε) (x := x)
    (hiaiRegularization_loewnerKernel_entry_integrable_on_nodes_of_diag
      (φ := φ) (f := f) hφ hε hx hpos hdiag_int)

/--
If a Hermitian matrix is obtained from a positive semidefinite matrix by
increasing only diagonal entries, then it is positive semidefinite.  This is the
algebraic bridge needed for the Hiai regularization route when the diagonal
entry is available only as a lower bound.
-/
theorem matrix_posSemidef_of_offdiag_eq_diag_ge
    {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hB : B.PosSemidef)
    (hoffdiag : ∀ i j : Fin n, i ≠ j → A i j = B i j)
    (hdiag : ∀ i : Fin n, B i i ≤ A i i) :
    A.PosSemidef := by
  let D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal fun i : Fin n => A i i - B i i
  have hD_nonneg : ∀ i : Fin n, 0 ≤ A i i - B i i := by
    intro i
    exact sub_nonneg.mpr (hdiag i)
  have hD : D.PosSemidef := Matrix.PosSemidef.diagonal hD_nonneg
  have hAeq : A = B + D := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D]
    · rw [hoffdiag i j hij]
      simp [D, Matrix.diagonal_apply_ne _ hij]
  simpa [hAeq] using hB.add hD

/--
The matrix whose entries are the mollifier averages of the shifted public
Löwner kernels is positive semidefinite.  This is independent of the diagonal
entry of the regularized function; it only integrates the PSD matrices already
available for the shifted node families.
-/
theorem regularization_integralKernelMatrix_psd
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hinj : Function.Injective x) (hpos : LoewnerPosOnUnitInterval f)
    (hentry_int : ∀ i j : Fin n,
      Integrable
        (fun t : ℝ => (φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ))
        (volume.restrict (Ι (-1 : ℝ) 1))) :
    (Matrix.of fun i j : Fin n =>
      ∫ t : ℝ, (φ t : ℂ) *
        (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)
        ∂(volume.restrict (Ι (-1 : ℝ) 1))).PosSemidef := by
  let μ : Measure ℝ := volume.restrict (Ι (-1 : ℝ) 1)
  let B : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j : Fin n =>
    ∫ t : ℝ, (φ t : ℂ) *
      (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ) ∂μ
  have hquad : ∀ c : Fin n → ℂ,
      star c ⬝ᵥ (B.mulVec c) =
        ∫ t : ℝ,
          (φ t : ℂ) *
            (star c ⬝ᵥ
              ((Matrix.of fun i j : Fin n =>
                (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)).mulVec c)) ∂μ := by
    intro c
    let term : Fin n → Fin n → ℝ → ℂ := fun i j t =>
      star (c i) * ((φ t : ℂ) *
        (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)) * c j
    have hterm_int :=
      hiaiRegularization_loewnerKernel_entryTerm_integrable_of_entry_integrable
        (φ := φ) (f := f) (ε := ε) (x := x) hentry_int c
    have hconst : ∀ i j : Fin n,
        star (c i) *
            (∫ t : ℝ, (φ t : ℂ) *
              (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ) ∂μ) * c j =
          ∫ t : ℝ, term i j t ∂μ := by
      intro i j
      calc
        star (c i) *
            (∫ t : ℝ, (φ t : ℂ) *
              (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ) ∂μ) * c j
            = (∫ t : ℝ, star (c i) * ((φ t : ℂ) *
              (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)) ∂μ) * c j := by
                exact congrArg (fun z : ℂ => z * c j)
                  (MeasureTheory.integral_const_mul (μ := μ) (star (c i))
                    (fun t : ℝ =>
                      (φ t : ℂ) *
                        (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ))).symm
        _ = ∫ t : ℝ, term i j t ∂μ := by
                exact (MeasureTheory.integral_mul_const (μ := μ) (c j)
                  (fun t : ℝ =>
                    star (c i) * ((φ t : ℂ) *
                      (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)))).symm
    calc
      star c ⬝ᵥ (B.mulVec c)
          = ∑ i : Fin n, ∑ j : Fin n,
              star (c i) * B i j * c j := by
            simpa using loewnerKernel_quadraticForm_entry_sum B c
      _ = ∑ i : Fin n, ∑ j : Fin n, ∫ t : ℝ, term i j t ∂μ := by
            apply Finset.sum_congr rfl
            intro i _hi
            apply Finset.sum_congr rfl
            intro j _hj
            exact hconst i j
      _ = ∑ i : Fin n, ∫ t : ℝ, ∑ j : Fin n, term i j t ∂μ := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [MeasureTheory.integral_finset_sum Finset.univ]
            intro j _hj
            exact hterm_int i j
      _ = ∫ t : ℝ, ∑ i : Fin n, ∑ j : Fin n, term i j t ∂μ := by
            rw [MeasureTheory.integral_finset_sum Finset.univ]
            intro i _hi
            exact MeasureTheory.integrable_finset_sum Finset.univ
              (fun j _hj => hterm_int i j)
      _ = ∫ t : ℝ,
          (φ t : ℂ) *
            (star c ⬝ᵥ
              ((Matrix.of fun i j : Fin n =>
                (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)).mulVec c)) ∂μ := by
            congr 1
            ext t
            rw [loewnerKernel_quadraticForm_entry_sum]
            simp [term, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
  have hnonneg : ∀ c : Fin n → ℂ, 0 ≤ star c ⬝ᵥ (B.mulVec c) := by
    intro c
    rw [hquad c]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have htIcc : t ∈ Set.Icc (-1 : ℝ) 1 := by
      have ht_uIcc : t ∈ [[(-1 : ℝ), 1]] := Set.uIoc_subset_uIcc ht
      simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht_uIcc
    have hpsd :=
      loewnerKernel_shifted_posSemidef_of_loewnerPosOnUnitInterval
        (f := f) hpos hε hx hinj htIcc
    exact mul_nonneg
      (by exact_mod_cast hφ.nonneg t)
      (hpsd.dotProduct_mulVec_nonneg c)
  have hherm : B.IsHermitian := by
    refine Matrix.IsHermitian.ext ?_
    intro i j
    dsimp [B]
    calc
      (starRingEnd ℂ)
          (∫ t : ℝ, (φ t : ℂ) *
            (loewnerKernel f (x j - ε * t) (x i - ε * t) : ℂ) ∂μ) =
          ∫ t : ℝ, (starRingEnd ℂ)
            ((φ t : ℂ) *
              (loewnerKernel f (x j - ε * t) (x i - ε * t) : ℂ)) ∂μ := by
        exact (integral_conj
          (f := fun t : ℝ =>
            (φ t : ℂ) *
              (loewnerKernel f (x j - ε * t) (x i - ε * t) : ℂ))).symm
      _ = ∫ t : ℝ, (φ t : ℂ) *
            (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards with t
        simp [loewnerKernel_swap]
  simpa [B, μ] using
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm hnonneg

/--
Diagonal-lower-bound version of the Hiai regularization PSD bridge.  The
off-diagonal entries are identified with the averaged shifted kernels, while
the diagonal entries only need to dominate those averages.
-/
theorem regularization_loewnerKernelPSD_of_offdiag_integral_formula_diag_ge
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hinj : Function.Injective x) (hpos : LoewnerPosOnUnitInterval f)
    (hentry_int : ∀ i j : Fin n,
      Integrable
        (fun t : ℝ => (φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ))
        (volume.restrict (Ι (-1 : ℝ) 1)))
    (hoffdiag : ∀ i j : Fin n, i ≠ j →
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ) =
        ∫ t : ℝ, (φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)
          ∂(volume.restrict (Ι (-1 : ℝ) 1)))
    (hdiag_ge : ∀ i : Fin n,
      (∫ t : ℝ, (φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x i - ε * t) : ℂ)
          ∂(volume.restrict (Ι (-1 : ℝ) 1))) ≤
        (loewnerKernel (hiaiRegularization φ ε f) (x i) (x i) : ℂ)) :
    (Matrix.of fun i j : Fin n =>
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)).PosSemidef := by
  let B : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j : Fin n =>
    ∫ t : ℝ, (φ t : ℂ) *
      (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ)
      ∂(volume.restrict (Ι (-1 : ℝ) 1))
  have hB : B.PosSemidef := by
    simpa [B] using
      regularization_integralKernelMatrix_psd
        (φ := φ) (f := f) hφ hε hx hinj hpos hentry_int
  exact
    matrix_posSemidef_of_offdiag_eq_diag_ge
      (A := Matrix.of fun i j : Fin n =>
        (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ))
      (B := B) hB
      (by
        intro i j hij
        simpa [B] using hoffdiag i j hij)
      (by
        intro i
        simpa [B] using hdiag_ge i)

/--
Public off-diagonal formulas plus diagonal lower-bound data are enough to
transport finite Löwner positivity to the Hiai regularization.  This is the
conditional bridge targeted by the Stieltjes/distributional diagonal argument:
the analytic inputs are exactly diagonal integrability and the diagonal lower
bound.  For Löwner-positive `f` the integrability is discharged in
`regularization_loewnerKernelPSD_of_publicDiagonalLowerBound` and the lower bound
in `regularization_loewnerKernelPSD`, both below.
-/
theorem regularization_loewnerKernelPSD_of_diagonalLowerBoundData
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hinj : Function.Injective x) (hpos : LoewnerPosOnUnitInterval f)
    (hdiag_int : ∀ i : Fin n,
      Integrable
        (fun t : ℝ => (φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x i - ε * t) : ℂ))
        (volume.restrict (Ι (-1 : ℝ) 1)))
    (hdiag_ge : ∀ i : Fin n,
      (∫ t : ℝ, (φ t : ℂ) *
          (loewnerKernel f (x i - ε * t) (x i - ε * t) : ℂ)
          ∂(volume.restrict (Ι (-1 : ℝ) 1))) ≤
        (loewnerKernel (hiaiRegularization φ ε f) (x i) (x i) : ℂ)) :
    (Matrix.of fun i j : Fin n =>
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)).PosSemidef := by
  have hentry_int :
      ∀ i j : Fin n,
        Integrable
          (fun t : ℝ => (φ t : ℂ) *
            (loewnerKernel f (x i - ε * t) (x j - ε * t) : ℂ))
          (volume.restrict (Ι (-1 : ℝ) 1)) :=
    hiaiRegularization_loewnerKernel_entry_integrable_on_nodes_of_diag
      (φ := φ) (f := f) hφ hε hx hpos hdiag_int
  exact
    regularization_loewnerKernelPSD_of_offdiag_integral_formula_diag_ge
      (φ := φ) (f := f) hφ hε hx hinj hpos hentry_int
      (by
        intro i j hij
        exact
          hiaiRegularization_loewnerKernel_offdiag_uIoc_formula_of_loewnerPosOnUnitInterval
            (φ := φ) (f := f) hφ hε (hx i) (hx j) hpos
            (fun hxy => hij (hinj hxy)))
      hdiag_ge

/--
Real interval-integrability of the diagonal averaged kernel is the same
diagonal integrability datum required by the complex `uIoc` PSD bridge.
-/
theorem hiaiRegularization_loewnerKernel_diag_uIoc_integrable_of_intervalIntegrable
    {φ f : ℝ → ℝ} {ε x : ℝ}
    (hdiag_int :
      IntervalIntegrable
        (fun t : ℝ => φ t * loewnerKernel f (x - ε * t) (x - ε * t))
        volume (-1 : ℝ) 1) :
    Integrable
      (fun t : ℝ => (φ t : ℂ) *
        (loewnerKernel f (x - ε * t) (x - ε * t) : ℂ))
      (volume.restrict (Ι (-1 : ℝ) 1)) := by
  have hreal :
      Integrable
        (fun t : ℝ => φ t * loewnerKernel f (x - ε * t) (x - ε * t))
        (volume.restrict (Ι (-1 : ℝ) 1)) :=
    hdiag_int.def'
  have hcomplex :
      Integrable
        (fun t : ℝ =>
          ((φ t * loewnerKernel f (x - ε * t) (x - ε * t) : ℝ) : ℂ))
        (volume.restrict (Ι (-1 : ℝ) 1)) :=
    hreal.ofReal
  simpa using hcomplex

/--
Public Löwner positivity supplies interval-integrability of the diagonal
averaged kernel.  This uses scalar monotonicity and Mathlib's theorem that the
derivative of a monotone function is interval integrable; it does not claim the
Stieltjes lower bound.
-/
theorem
    hiaiRegularization_loewnerKernel_diag_intervalIntegrable_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 ≤ ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    IntervalIntegrable
      (fun t : ℝ => φ t * loewnerKernel f (x - ε * t) (x - ε * t))
      volume (-1 : ℝ) 1 := by
  have hφcont : ContinuousOn φ [[(-1 : ℝ), 1]] :=
    hφ.smooth.continuous.continuousOn
  have hmono : MonotoneOn f (Set.Ioo (-1 : ℝ) 1) :=
    scalarMonotoneOn_Ioo_of_loewnerPosOnUnitInterval hpos
  by_cases hε0 : ε = 0
  · subst ε
    have hconst : ContinuousOn (fun _t : ℝ => deriv f x) [[(-1 : ℝ), 1]] :=
      continuousOn_const
    have hprod : ContinuousOn (fun t : ℝ => φ t * deriv f x) [[(-1 : ℝ), 1]] :=
      hφcont.mul hconst
    simpa [loewnerKernel_self] using hprod.intervalIntegrable
  · have hεpos : 0 < ε := lt_of_le_of_ne hε (Ne.symm hε0)
    have hleft : -1 < x - ε := by
      have hxleft : -1 + ε < x := hx.1
      linarith
    have hright : x + ε < 1 := by
      have hxright : x < 1 - ε := hx.2
      linarith
    have hsub : [[x - ε, x + ε]] ⊆ Set.Ioo (-1 : ℝ) 1 := by
      intro y hy
      have hyIcc : y ∈ Set.Icc (x - ε) (x + ε) := by
        simpa [Set.uIcc_of_le (by linarith : x - ε ≤ x + ε)] using hy
      exact ⟨by linarith [hyIcc.1], by linarith [hyIcc.2]⟩
    have hmono_local : MonotoneOn f [[x - ε, x + ε]] :=
      hmono.mono hsub
    have hderiv_local :
        IntervalIntegrable (deriv f) volume (x - ε) (x + ε) :=
      MonotoneOn.intervalIntegrable_deriv hmono_local
    have hcomp_sub :
        IntervalIntegrable (fun u : ℝ => deriv f (x - u)) volume ε (-ε) := by
      simpa [sub_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (hderiv_local.comp_sub_left x)
    have hcomp_mul :
        IntervalIntegrable (fun t : ℝ => deriv f (x - ε * t)) volume 1 (-1) := by
      have h :=
        hcomp_sub.comp_mul_left (c := ε)
      simpa [hεpos.ne', div_self hεpos.ne', neg_div] using h
    have hderiv_comp :
        IntervalIntegrable (fun t : ℝ => deriv f (x - ε * t)) volume (-1) 1 :=
      hcomp_mul.symm
    have hprod :
        IntervalIntegrable (fun t : ℝ => φ t * deriv f (x - ε * t))
          volume (-1 : ℝ) 1 :=
      hderiv_comp.continuousOn_mul hφcont
    simpa [loewnerKernel_self] using hprod

/--
Public Löwner positivity supplies the complex `uIoc` diagonal integrability
needed by the lower-bound PSD bridge.
-/
theorem
    hiaiRegularization_loewnerKernel_diag_uIoc_integrable_of_loewnerPosOnUnitInterval
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 ≤ ε)
    (hx : x ∈ hiaiRegularizedInterior ε)
    (hpos : LoewnerPosOnUnitInterval f) :
    Integrable
      (fun t : ℝ => (φ t : ℂ) *
        (loewnerKernel f (x - ε * t) (x - ε * t) : ℂ))
      (volume.restrict (Ι (-1 : ℝ) 1)) :=
  hiaiRegularization_loewnerKernel_diag_uIoc_integrable_of_intervalIntegrable
    (φ := φ) (f := f) (ε := ε) (x := x)
    (hiaiRegularization_loewnerKernel_diag_intervalIntegrable_of_loewnerPosOnUnitInterval
      (φ := φ) (f := f) hφ hε hx hpos)

/--
The diagonal-lower-bound PSD bridge in the real interval-integral form expected
from the Stieltjes/distributional derivative argument.  The only analytic data
left open are real diagonal integrability and the real diagonal lower bound.
-/
theorem regularization_loewnerKernelPSD_of_realDiagonalLowerBoundData
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hinj : Function.Injective x) (hpos : LoewnerPosOnUnitInterval f)
    (hdiag_int : ∀ i : Fin n,
      IntervalIntegrable
        (fun t : ℝ => φ t * loewnerKernel f (x i - ε * t) (x i - ε * t))
        volume (-1 : ℝ) 1)
    (hdiag_ge : ∀ i : Fin n,
      (∫ t in (-1 : ℝ)..1,
          φ t * loewnerKernel f (x i - ε * t) (x i - ε * t)) ≤
        loewnerKernel (hiaiRegularization φ ε f) (x i) (x i)) :
    (Matrix.of fun i j : Fin n =>
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)).PosSemidef := by
  refine
    regularization_loewnerKernelPSD_of_diagonalLowerBoundData
      (φ := φ) (f := f) hφ hε hx hinj hpos
      (fun i =>
        hiaiRegularization_loewnerKernel_diag_uIoc_integrable_of_intervalIntegrable
          (φ := φ) (f := f) (ε := ε) (x := x i) (hdiag_int i))
      ?_
  intro i
  calc
    (∫ t : ℝ, (φ t : ℂ) *
        (loewnerKernel f (x i - ε * t) (x i - ε * t) : ℂ)
        ∂(volume.restrict (Ι (-1 : ℝ) 1)))
        = ∫ t in (-1 : ℝ)..1,
            ((φ t * loewnerKernel f (x i - ε * t) (x i - ε * t) : ℝ) : ℂ) := by
          have hconv :
              (∫ t in (-1 : ℝ)..1,
                ((φ t * loewnerKernel f (x i - ε * t) (x i - ε * t) : ℝ) : ℂ)) =
                ∫ t : ℝ, (φ t : ℂ) *
                  (loewnerKernel f (x i - ε * t) (x i - ε * t) : ℂ)
                  ∂(volume.restrict (Ι (-1 : ℝ) 1)) := by
            simpa [Complex.ofReal_mul] using
              (intervalIntegral.intervalIntegral_eq_integral_uIoc
                (fun t : ℝ => (φ t : ℂ) *
                  (loewnerKernel f (x i - ε * t) (x i - ε * t) : ℂ))
                (-1) 1 volume)
          exact hconv.symm
    _ ≤ (loewnerKernel (hiaiRegularization φ ε f) (x i) (x i) : ℂ) := by
          rw [intervalIntegral.integral_ofReal]
          exact_mod_cast hdiag_ge i

/--
PSD transport for Hiai regularization with only the real diagonal lower bound
left as an analytic hypothesis.  Public Löwner positivity supplies all
diagonal/off-diagonal integrability required by the finite quadratic-form
bridge.
-/
theorem regularization_loewnerKernelPSD_of_publicDiagonalLowerBound
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hinj : Function.Injective x) (hpos : LoewnerPosOnUnitInterval f)
    (hdiag_ge : ∀ i : Fin n,
      (∫ t in (-1 : ℝ)..1,
          φ t * loewnerKernel f (x i - ε * t) (x i - ε * t)) ≤
        loewnerKernel (hiaiRegularization φ ε f) (x i) (x i)) :
    (Matrix.of fun i j : Fin n =>
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)).PosSemidef :=
  regularization_loewnerKernelPSD_of_realDiagonalLowerBoundData
    (φ := φ) (f := f) hφ hε hx hinj hpos
    (fun i =>
      hiaiRegularization_loewnerKernel_diag_intervalIntegrable_of_loewnerPosOnUnitInterval
        (φ := φ) (f := f) hφ hε (hx i) hpos)
    hdiag_ge

/--
The Stieltjes diagonal comparison in the single-node form.  Once the
clipped Stieltjes convolution is known to be bounded above by the diagonal
kernel of the regularization, the averaged diagonal kernel lower bound follows
from the closed a.c.-part domination layer.  That bound is
`regularization_clippedStieltjesConvolution_le_diagKernel_of_loewnerPos`
(`ClippedComparison.lean`).
-/
theorem hiaiRegularization_loewnerKernel_diag_ge_integral_of_clippedStieltjesConvolution
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε x : ℝ} (hε : 0 < ε)
    (hg : Monotone (hiaiLocalClip f (x - ε) (x + ε)))
    (hw_int :
      Integrable (hiaiScaledMollifierWeight φ ε x)
        hg.stieltjesFunction.measure)
    (hconv_le :
      (∫ y, hiaiScaledMollifierWeight φ ε x y
          ∂hg.stieltjesFunction.measure) ≤
        loewnerKernel (hiaiRegularization φ ε f) x x) :
    (∫ t in (-1 : ℝ)..1,
        φ t * loewnerKernel f (x - ε * t) (x - ε * t)) ≤
      loewnerKernel (hiaiRegularization φ ε f) x x :=
  (hiaiRegularization_diagIntegral_le_clippedStieltjesConvolution
    (φ := φ) (f := f) hφ hε hg hw_int).trans hconv_le

/--
PSD transport from public Löwner positivity once the clipped Stieltjes
convolution supplies the diagonal lower bound at every selected node.  This is
the exact finite-node handoff used by the broad theorem
`regularization_loewnerKernelPSD` below.
-/
theorem regularization_loewnerKernelPSD_of_clippedStieltjesConvolutionBound
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hinj : Function.Injective x) (hpos : LoewnerPosOnUnitInterval f)
    (hg : ∀ i : Fin n,
      Monotone (hiaiLocalClip f (x i - ε) (x i + ε)))
    (hw_int : ∀ i : Fin n,
      Integrable (hiaiScaledMollifierWeight φ ε (x i))
        (hg i).stieltjesFunction.measure)
    (hconv_le : ∀ i : Fin n,
      (∫ y, hiaiScaledMollifierWeight φ ε (x i) y
          ∂(hg i).stieltjesFunction.measure) ≤
        loewnerKernel (hiaiRegularization φ ε f) (x i) (x i)) :
    (Matrix.of fun i j : Fin n =>
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)).PosSemidef :=
  regularization_loewnerKernelPSD_of_publicDiagonalLowerBound
    (φ := φ) (f := f) hφ hε.le hx hinj hpos
    (fun i =>
      hiaiRegularization_loewnerKernel_diag_ge_integral_of_clippedStieltjesConvolution
        (φ := φ) (f := f) hφ hε (hg i) (hw_int i) (hconv_le i))

/--
Public version of
`regularization_loewnerKernelPSD_of_clippedStieltjesConvolutionBound`.
Public Löwner positivity supplies the monotone clipped extension; the other
inputs are the Stieltjes integrability of the scaled weight and the comparison
between the clipped Stieltjes convolution and the regularized diagonal kernel.
They are supplied by
`hiaiScaledMollifierWeight_integrable_stieltjes_of_loewnerPosOnUnitInterval` and
`regularization_clippedStieltjesConvolution_le_diagKernel_of_loewnerPos`.
-/
theorem
    regularization_loewnerKernelPSD_of_publicClippedStieltjesConvolutionBound
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hinj : Function.Injective x) (hpos : LoewnerPosOnUnitInterval f)
    (hw_int : ∀ i : Fin n,
      Integrable (hiaiScaledMollifierWeight φ ε (x i))
        (hiaiLocalClip_mono_of_loewnerPosOnUnitInterval
          (f := f) hε.le (hx i) hpos).stieltjesFunction.measure)
    (hconv_le : ∀ i : Fin n,
      (∫ y, hiaiScaledMollifierWeight φ ε (x i) y
          ∂(hiaiLocalClip_mono_of_loewnerPosOnUnitInterval
            (f := f) hε.le (hx i) hpos).stieltjesFunction.measure) ≤
        loewnerKernel (hiaiRegularization φ ε f) (x i) (x i)) :
    (Matrix.of fun i j : Fin n =>
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)).PosSemidef :=
  regularization_loewnerKernelPSD_of_clippedStieltjesConvolutionBound
    (φ := φ) (f := f) hφ hε hx hinj hpos
    (fun i => hiaiLocalClip_mono_of_loewnerPosOnUnitInterval
      (f := f) hε.le (hx i) hpos)
    hw_int hconv_le

/--
The previous handoff with the Stieltjes integrability input discharged from
public data.  The only analytic input is the comparison between the clipped
Stieltjes convolution and the regularized diagonal kernel, which is
`regularization_clippedStieltjesConvolution_le_diagKernel_of_loewnerPos`
(`ClippedComparison.lean`).
-/
theorem
    regularization_loewnerKernelPSD_of_publicClippedBound_autoInt
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hinj : Function.Injective x) (hpos : LoewnerPosOnUnitInterval f)
    (hconv_le : ∀ i : Fin n,
      (∫ y, hiaiScaledMollifierWeight φ ε (x i) y
          ∂(hiaiLocalClip_mono_of_loewnerPosOnUnitInterval
            (f := f) hε.le (hx i) hpos).stieltjesFunction.measure) ≤
        loewnerKernel (hiaiRegularization φ ε f) (x i) (x i)) :
    (Matrix.of fun i j : Fin n =>
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)).PosSemidef :=
  regularization_loewnerKernelPSD_of_publicClippedStieltjesConvolutionBound
    (φ := φ) (f := f) hφ hε hx hinj hpos
    (fun i =>
      hiaiScaledMollifierWeight_integrable_stieltjes_of_loewnerPosOnUnitInterval
        (φ := φ) (f := f) hφ hε (hx i) hpos)
    hconv_le

/--
Finite-node PSD handoff with the Stieltjes integration-by-parts and
dominated differentiation data displayed explicitly at each node.  This is a
closed bookkeeping bridge only; it does not itself prove the Stieltjes
integration-by-parts identity, which is
`hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_closed`
(`IocUniformStep.lean`).
-/
theorem regularization_loewnerKernelPSD_of_publicIBPAndDominationData
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hinj : Function.Injective x) (hpos : LoewnerPosOnUnitInterval f)
    (hibp : ∀ i : Fin n,
      (∫ y, hiaiScaledMollifierWeight φ ε (x i) y
          ∂(hiaiLocalClip_mono_of_loewnerPosOnUnitInterval
            (f := f) hε.le (hx i) hpos).stieltjesFunction.measure) =
        -∫ y in x i - ε..x i + ε,
          deriv (fun y : ℝ => hiaiScaledMollifierWeight φ ε (x i) y) y *
            hiaiLocalClip f (x i - ε) (x i + ε) y)
    {s : Fin n → Set ℝ} (hs : ∀ i : Fin n, s i ∈ 𝓝 (x i))
    {bound : Fin n → ℝ → ℝ}
    (hF_meas : ∀ i : Fin n, ∀ᶠ z in 𝓝 (x i),
      AEStronglyMeasurable
        (fun y : ℝ =>
          hiaiScaledMollifierWeight φ ε z y *
            hiaiLocalClip f (x i - ε) (x i + ε) y) volume)
    (hF_int : ∀ i : Fin n,
      Integrable
        (fun y : ℝ =>
          hiaiScaledMollifierWeight φ ε (x i) y *
            hiaiLocalClip f (x i - ε) (x i + ε) y) volume)
    (hF'_meas : ∀ i : Fin n,
      AEStronglyMeasurable
        (fun y : ℝ =>
          deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) (x i) *
            hiaiLocalClip f (x i - ε) (x i + ε) y) volume)
    (h_bound : ∀ i : Fin n,
      ∀ᵐ y ∂volume, ∀ z ∈ s i,
        ‖deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) z *
            hiaiLocalClip f (x i - ε) (x i + ε) y‖ ≤ bound i y)
    (bound_integrable : ∀ i : Fin n, Integrable (bound i) volume)
    (hdiag_le : ∀ i : Fin n,
      loewnerKernel
          (hiaiRegularization φ ε
            (hiaiLocalClip f (x i - ε) (x i + ε)))
          (x i) (x i) ≤
        loewnerKernel (hiaiRegularization φ ε f) (x i) (x i)) :
    (Matrix.of fun i j : Fin n =>
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)).PosSemidef :=
  regularization_loewnerKernelPSD_of_publicClippedBound_autoInt
    (φ := φ) (f := f) hφ hε hx hinj hpos
    (fun i =>
      hiaiRegularization_clippedStieltjesConvolution_le_diagKernel_of_publicData
        (φ := φ) (f := f) hφ hε (hx i) hpos (hibp i) (hs i)
        (hF_meas i) (hF_int i) (hF'_meas i) (h_bound i)
        (bound_integrable i) (hdiag_le i))

/--
Finite-node PSD handoff after the Stieltjes/BV integration-by-parts identity
has been closed by the uniform `Ioc` step approximation.  The other inputs
are exactly the nodewise dominated-differentiation data and the
clipped-to-original diagonal comparison; they are supplied from public Löwner
positivity in the next theorem and in `regularization_loewnerKernelPSD` below.
-/
theorem regularization_loewnerKernelPSD_of_iocUniformStepsAndDominationData
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hinj : Function.Injective x) (hpos : LoewnerPosOnUnitInterval f)
    {s : Fin n → Set ℝ} (hs : ∀ i : Fin n, s i ∈ 𝓝 (x i))
    {bound : Fin n → ℝ → ℝ}
    (hF_meas : ∀ i : Fin n, ∀ᶠ z in 𝓝 (x i),
      AEStronglyMeasurable
        (fun y : ℝ =>
          hiaiScaledMollifierWeight φ ε z y *
            hiaiLocalClip f (x i - ε) (x i + ε) y) volume)
    (hF_int : ∀ i : Fin n,
      Integrable
        (fun y : ℝ =>
          hiaiScaledMollifierWeight φ ε (x i) y *
            hiaiLocalClip f (x i - ε) (x i + ε) y) volume)
    (hF'_meas : ∀ i : Fin n,
      AEStronglyMeasurable
        (fun y : ℝ =>
          deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) (x i) *
            hiaiLocalClip f (x i - ε) (x i + ε) y) volume)
    (h_bound : ∀ i : Fin n,
      ∀ᵐ y ∂volume, ∀ z ∈ s i,
        ‖deriv (fun z : ℝ => hiaiScaledMollifierWeight φ ε z y) z *
            hiaiLocalClip f (x i - ε) (x i + ε) y‖ ≤ bound i y)
    (bound_integrable : ∀ i : Fin n, Integrable (bound i) volume)
    (hdiag_le : ∀ i : Fin n,
      loewnerKernel
          (hiaiRegularization φ ε
            (hiaiLocalClip f (x i - ε) (x i + ε)))
          (x i) (x i) ≤
        loewnerKernel (hiaiRegularization φ ε f) (x i) (x i)) :
    (Matrix.of fun i j : Fin n =>
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)).PosSemidef :=
  regularization_loewnerKernelPSD_of_publicIBPAndDominationData
    (φ := φ) (f := f) hφ hε hx hinj hpos
    (fun i =>
      hiaiScaledMollifierWeight_IBP_identity_of_iocUniformSteps_closed
        (φ := φ)
        (g := hiaiLocalClip f (x i - ε) (x i + ε))
        hφ hε
        (hiaiLocalClip_mono_of_loewnerPosOnUnitInterval
          (f := f) hε.le (hx i) hpos))
    hs hF_meas hF_int hF'_meas h_bound bound_integrable hdiag_le

/--
Finite-node PSD handoff after the Stieltjes/BV integration-by-parts input and
the smooth scaled-weight dominated-differentiation data are both supplied from
public Löwner positivity.  The only nodewise input is the final
clipped-to-original diagonal derivative comparison, supplied by
`hiaiRegularization_localClip_deriv_eq_original` in `regularization_loewnerKernelPSD`
below.
-/
theorem regularization_loewnerKernelPSD_of_iocUniformStepsAndPublicDomination
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hinj : Function.Injective x) (hpos : LoewnerPosOnUnitInterval f)
    (hderiv_le : ∀ i : Fin n,
      deriv
          (fun z : ℝ =>
            hiaiRegularization φ ε
              (hiaiLocalClip f (x i - ε) (x i + ε)) z)
          (x i) ≤
        deriv (fun z : ℝ => hiaiRegularization φ ε f z) (x i)) :
    (Matrix.of fun i j : Fin n =>
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)).PosSemidef :=
  regularization_loewnerKernelPSD_of_publicClippedBound_autoInt
    (φ := φ) (f := f) hφ hε hx hinj hpos
    (fun i =>
      hiaiRegularization_clippedStieltjesConvolution_le_diagKernel_of_publicDomination
        (φ := φ) (f := f) hφ hε (hx i) hpos (hderiv_le i))

/--
Public PSD transport for Hiai regularization.  This is the regularized
kernel-PSD layer consumed by the smooth Hiai regularity argument and the
subsequent limit `ε ↓ 0`.
-/
theorem regularization_loewnerKernelPSD
    {φ f : ℝ → ℝ} (hφ : HiaiMollifier φ)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ∈ hiaiRegularizedInterior ε)
    (hinj : Function.Injective x) (hpos : LoewnerPosOnUnitInterval f) :
    (Matrix.of fun i j : Fin n =>
      (loewnerKernel (hiaiRegularization φ ε f) (x i) (x j) : ℂ)).PosSemidef :=
  regularization_loewnerKernelPSD_of_iocUniformStepsAndPublicDomination
    (φ := φ) (f := f) hφ hε hx hinj hpos
    (fun i =>
      le_of_eq
        (hiaiRegularization_localClip_deriv_eq_original
          (φ := φ) (f := f) hφ hε (hx i) hpos))

end

end Quantum.TraceInequality.Loewner
