import Quantum.TraceInequality.Loewner.Koranyi.SupportElimAlgebra

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable


namespace Quantum.TraceInequality.Loewner

open scoped BigOperators

noncomputable section

open MeasureTheory

section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Auxiliary spectral Dirac measure for a fixed finite-rank witness of the Hilbert space. -/
noncomputable def diracMeasure_of_isSymmetricAux
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (φ : E) (n : ℕ) (hn : Module.finrank ℂ E = n) :
    Measure ℝ := by
  classical
  let b : OrthonormalBasis (Fin n) ℂ E := hT.eigenvectorBasis (n := n) (hn := hn)
  let eig : Fin n → ℝ := hT.eigenvalues (n := n) (hn := hn)
  let cVec : EuclideanSpace ℂ (Fin n) := b.repr φ
  let c : Fin n → ℂ := fun i => cVec.ofLp i
  let μi : Fin n → Measure ℝ := fun i =>
    (ENNReal.ofReal (Complex.normSq (c i))) • Measure.dirac (eig i)
  exact ∑ i : Fin n, μi i

/-- The spectral Dirac measure attached to a symmetric finite-dimensional operator and vector. -/
noncomputable def diracMeasure_of_isSymmetric
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (φ : E) : Measure ℝ :=
  diracMeasure_of_isSymmetricAux (T := T) (hT := hT) (φ := φ)
    (n := Module.finrank ℂ E) (hn := rfl)

/-- Step 3 (finite-dimensional, `z`-uniform statement): the measure is `z`-independent.

For each `z` with `z.im ≠ 0`, we can solve `(T - zI) x = φ` and express
`⟪φ, x⟫` as the Stieltjes transform of a discrete measure that depends only on
`T` and `φ`. -/
theorem inner_solution_eq_integral_dirac_of_isSymmetric_forall
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (φ : E) :
    ∀ z : ℂ,
      z.im ≠ 0 →
        ∃ x : E,
          (T - z • (LinearMap.id : E →ₗ[ℂ] E)) x = φ ∧
            inner (𝕜 := ℂ) φ x =
              ∫ t, (1 / ((t : ℂ) - z))
                ∂(diracMeasure_of_isSymmetric (T := T) (hT := hT) φ) := by
  classical
  intro z hz
  -- Work in the eigenvector basis of `T`.
  let n : ℕ := Module.finrank ℂ E
  have hn : Module.finrank ℂ E = n := rfl
  let b : OrthonormalBasis (Fin n) ℂ E := hT.eigenvectorBasis (n := n) (hn := hn)
  let eig : Fin n → ℝ := hT.eigenvalues (n := n) (hn := hn)
  let cVec : EuclideanSpace ℂ (Fin n) := b.repr φ
  let c : Fin n → ℂ := fun i => cVec.ofLp i
  let aFun : Fin n → ℂ := fun i => c i / ((eig i : ℂ) - z)
  let a : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 aFun
  have hT_apply_basis : ∀ i : Fin n, T (b i) = (eig i : ℂ) • b i := by
    intro i
    simp [b, eig]
  -- Define the candidate solution by expanding in the eigenvector basis.
  let x : E := b.repr.symm a
  have hx_sum : x = ∑ i : Fin n, (a.ofLp i) • b i := by
    simpa [x] using (b.sum_repr_symm a).symm
  have ha_ne : ∀ i : Fin n, ((eig i : ℂ) - z) ≠ 0 := fun i =>
    complex_sub_ne_of_im_ne_zero (eig i) hz
  have hsol : (T - z • (LinearMap.id : E →ₗ[ℂ] E)) x = φ := by
    let s : Finset (Fin n) := Finset.univ
    have hx_sum' : x = s.sum (fun i => (a.ofLp i) • b i) := by
      simpa [s] using hx_sum
    rw [hx_sum']
    rw [map_sum (g := (T - z • (LinearMap.id : E →ₗ[ℂ] E))) (s := s)
      (f := fun i : Fin n => (a.ofLp i) • b i)]
    have hterm' :
        ∀ i : Fin n,
          (T - z • (LinearMap.id : E →ₗ[ℂ] E)) ((a.ofLp i) • b i) = (c i) • b i := by
      intro i
      have hSbi :
          (T - z • (LinearMap.id : E →ₗ[ℂ] E)) (b i) =
            ((eig i : ℂ) - z) • b i := by
        simp [LinearMap.smul_apply, hT_apply_basis, sub_eq_add_neg, add_smul]
      have hai : a.ofLp i = aFun i := by
        simp [a, aFun]
      have hcancel : aFun i * ((eig i : ℂ) - z) = c i := by
        have hne : ((eig i : ℂ) - z) ≠ 0 := ha_ne i
        simp [aFun, div_eq_mul_inv, hne, mul_comm]
      simp [hai, hSbi, hcancel, smul_smul]
    simp [hterm', s]
    simpa [s, cVec, c] using (b.sum_repr φ)
  -- Define the discrete measure supported on the eigenvalues, with weights `‖c i‖^2`.
  let μi : Fin n → Measure ℝ := fun i =>
    (ENNReal.ofReal (Complex.normSq (c i))) • Measure.dirac (eig i)
  let μ : Measure ℝ := ∑ i : Fin n, μi i
  have hμ_def :
      μ = diracMeasure_of_isSymmetric (T := T) (hT := hT) φ := by
    simp [diracMeasure_of_isSymmetric, diracMeasure_of_isSymmetricAux, μ, μi, c, cVec, eig, b, n]
  -- Compute the integral as a finite sum over atoms.
  have hμ_integral :
      (∫ t, ((t : ℂ) - z)⁻¹ ∂μ) =
        ∑ i : Fin n, ((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ) := by
    have h_int0 :
        ∫ t, ((t : ℂ) - z)⁻¹ ∂μ =
          ∑ i : Fin n, ∫ t, ((t : ℂ) - z)⁻¹ ∂(μi i) := by
      simpa [μ] using
        (MeasureTheory.integral_finset_sum_measure (μ := μi) (s := (Finset.univ : Finset (Fin n)))
          (f := fun t : ℝ => ((t : ℂ) - z)⁻¹)
          (by
            intro i hi
            have hdir : MeasureTheory.Integrable (fun t : ℝ => ((t : ℂ) - z)⁻¹)
                (Measure.dirac (eig i)) :=
              MeasureTheory.integrable_dirac (a := eig i) (f := fun t : ℝ => ((t : ℂ) - z)⁻¹)
                (by simp)
            simpa [μi] using hdir.smul_measure (by simp)))
    have hnonneg : ∀ i : Fin n, 0 ≤ Complex.normSq (c i) := fun i => Complex.normSq_nonneg (c i)
    rw [h_int0]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [μi, MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac,
      ENNReal.toReal_ofReal, hnonneg i]
    change (Complex.normSq (c i) : ℂ) * ((eig i : ℂ) - z)⁻¹ =
      ((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ)
    ring
  -- Compute `inner φ x` via the orthonormal basis.
  have h_inner :
      inner (𝕜 := ℂ) φ x =
        ∑ i : Fin n, ((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ) := by
    have hx_inner : ∀ i : Fin n, inner (𝕜 := ℂ) (b i) x = aFun i := by
      intro i
      have hrepr : b.repr x = a := by
        simp [x]
      have : (b.repr x).ofLp i = a.ofLp i := congrArg (fun v => v.ofLp i) hrepr
      simpa [b.repr_apply_apply, a, aFun] using this
    calc
      inner (𝕜 := ℂ) φ x
          = ∑ i : Fin n, inner (𝕜 := ℂ) φ (b i) * inner (𝕜 := ℂ) (b i) x := by
              symm
              simpa using (b.sum_inner_mul_inner φ x)
      _ = ∑ i : Fin n, ((starRingEnd ℂ) (c i)) * (aFun i) := by
            refine Fintype.sum_congr _ _ (fun i => ?_)
            have hc : inner (𝕜 := ℂ) (b i) φ = c i := by
              simpa [cVec, c] using (b.repr_apply_apply φ i).symm
            have hc' : inner (𝕜 := ℂ) φ (b i) = (starRingEnd ℂ) (c i) := by
              simpa [hc] using (inner_conj_symm (𝕜 := ℂ) (x := φ) (y := b i)).symm
            simp [hc', hx_inner i]
      _ = ∑ i : Fin n, ((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ) := by
            refine Fintype.sum_congr _ _ (fun i => ?_)
            have hmul : (starRingEnd ℂ) (c i) * c i = (Complex.normSq (c i) : ℂ) := by
              simpa using (Complex.normSq_eq_conj_mul_self (z := c i)).symm
            calc
              (starRingEnd ℂ) (c i) * (aFun i)
                  = (starRingEnd ℂ) (c i) * (c i * ((eig i : ℂ) - z)⁻¹) := by
                      simp [aFun, div_eq_mul_inv]
              _ = ((starRingEnd ℂ) (c i) * c i) * ((eig i : ℂ) - z)⁻¹ := by
                    simp [mul_assoc]
              _ = (Complex.normSq (c i) : ℂ) * ((eig i : ℂ) - z)⁻¹ := by
                    simp [hmul]
              _ = ((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ) := by
                    simp [mul_comm]
  have : inner (𝕜 := ℂ) φ x = ∫ t, ((t : ℂ) - z)⁻¹ ∂μ := by
    calc
      inner (𝕜 := ℂ) φ x =
          ∑ i : Fin n, ((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ) := h_inner
      _ = ∫ t, ((t : ℂ) - z)⁻¹ ∂μ := by simpa using hμ_integral.symm
  refine ⟨x, hsol, ?_⟩
  simpa [one_div, hμ_def] using this

/-- Step 3 (finite-dimensional): for a symmetric endomorphism `T` and a vector `φ`, the scalar
`⟪φ, x⟫` for the solution `x` to `(T - zI) x = φ` can be written as a finite sum, hence as an
integral against a discrete measure.

This statement is formulated with `z.im ≠ 0`, so that `T - zI` is automatically invertible. -/
theorem inner_solution_eq_integral_dirac_of_isSymmetric
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (φ : E) (z : ℂ) (hz : z.im ≠ 0) :
    ∃ μ : Measure ℝ,
      ∃ x : E,
        (T - z • (LinearMap.id : E →ₗ[ℂ] E)) x = φ ∧
          inner (𝕜 := ℂ) φ x = ∫ t, (1 / ((t : ℂ) - z)) ∂μ := by
  classical
  let μ : Measure ℝ := diracMeasure_of_isSymmetric (T := T) (hT := hT) φ
  rcases
      inner_solution_eq_integral_dirac_of_isSymmetric_forall (T := T) (hT := hT)
        (φ := φ) z hz with
    ⟨x, hsol, hx⟩
  exact ⟨μ, x, hsol, hx⟩

end

section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Strengthening of `inner_solution_eq_integral_dirac_of_isSymmetric`: if `z` lies in the upper
half-plane, then the imaginary part of `⟪φ, x⟫` is nonnegative. -/
theorem inner_solution_eq_integral_dirac_of_isSymmetric_im_nonneg_forall
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (φ : E) :
    ∀ z : ℂ,
      0 < z.im →
        ∃ x : E,
          (T - z • (LinearMap.id : E →ₗ[ℂ] E)) x = φ ∧
            inner (𝕜 := ℂ) φ x =
                ∫ t, (1 / ((t : ℂ) - z))
                  ∂(diracMeasure_of_isSymmetric (T := T) (hT := hT) φ) ∧
              0 ≤ (inner (𝕜 := ℂ) φ x).im := by
  intro z hz
  classical
  -- Work in the eigenvector basis of `T`.
  let n : ℕ := Module.finrank ℂ E
  have hn : Module.finrank ℂ E = n := rfl
  let b : OrthonormalBasis (Fin n) ℂ E := hT.eigenvectorBasis (n := n) (hn := hn)
  let eig : Fin n → ℝ := hT.eigenvalues (n := n) (hn := hn)
  let cVec : EuclideanSpace ℂ (Fin n) := b.repr φ
  let c : Fin n → ℂ := fun i => cVec.ofLp i
  let aFun : Fin n → ℂ := fun i => c i / ((eig i : ℂ) - z)
  let a : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 aFun
  have hT_apply_basis : ∀ i : Fin n, T (b i) = (eig i : ℂ) • b i := by
    intro i
    simp [b, eig]
  -- Define the candidate solution by expanding in the eigenvector basis.
  let x : E := b.repr.symm a
  have hx_sum : x = ∑ i : Fin n, (a.ofLp i) • b i := by
    simpa [x] using (b.sum_repr_symm a).symm
  have ha_ne : ∀ i : Fin n, ((eig i : ℂ) - z) ≠ 0 := fun i =>
    complex_sub_ne_of_im_ne_zero (eig i) (by exact hz.ne')
  have hsol : (T - z • (LinearMap.id : E →ₗ[ℂ] E)) x = φ := by
    -- Expand `x` as a sum in the eigenbasis and use the diagonal action.
    let s : Finset (Fin n) := Finset.univ
    have hx_sum' : x = s.sum (fun i => (a.ofLp i) • b i) := by
      simpa [s] using hx_sum
    rw [hx_sum']
    rw [map_sum (g := (T - z • (LinearMap.id : E →ₗ[ℂ] E))) (s := s)
      (f := fun i : Fin n => (a.ofLp i) • b i)]
    have hterm' :
        ∀ i : Fin n,
          (T - z • (LinearMap.id : E →ₗ[ℂ] E)) ((a.ofLp i) • b i) = (c i) • b i := by
      intro i
      have hSbi :
          (T - z • (LinearMap.id : E →ₗ[ℂ] E)) (b i) =
            ((eig i : ℂ) - z) • b i := by
        simp [LinearMap.smul_apply, hT_apply_basis, sub_eq_add_neg, add_smul]
      have hai : a.ofLp i = aFun i := by
        simp [a, aFun]
      have hcancel : aFun i * ((eig i : ℂ) - z) = c i := by
        have hne : ((eig i : ℂ) - z) ≠ 0 := ha_ne i
        simp [aFun, div_eq_mul_inv, hne, mul_comm]
      simp [hai, hSbi, hcancel, smul_smul]
    simp [hterm', s]
    simpa [s, cVec, c] using (b.sum_repr φ)
  -- Define the discrete measure supported on the eigenvalues, with weights `‖c i‖^2`.
  let μi : Fin n → Measure ℝ := fun i =>
    (ENNReal.ofReal (Complex.normSq (c i))) • Measure.dirac (eig i)
  let μ : Measure ℝ := ∑ i : Fin n, μi i
  have hμ_def :
      μ = diracMeasure_of_isSymmetric (T := T) (hT := hT) φ := by
    simp [diracMeasure_of_isSymmetric, diracMeasure_of_isSymmetricAux, μ, μi, c, cVec, eig, b, n]
  -- Compute the integral as a finite sum over atoms.
  have hμ_integral :
      (∫ t, ((t : ℂ) - z)⁻¹ ∂μ) =
        ∑ i : Fin n, ((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ) := by
    have h_int0 :
        ∫ t, ((t : ℂ) - z)⁻¹ ∂μ =
          ∑ i : Fin n, ∫ t, ((t : ℂ) - z)⁻¹ ∂(μi i) := by
      simpa [μ] using
        (MeasureTheory.integral_finset_sum_measure (μ := μi) (s := (Finset.univ : Finset (Fin n)))
          (f := fun t : ℝ => ((t : ℂ) - z)⁻¹)
          (by
            intro i hi
            have hdir : MeasureTheory.Integrable (fun t : ℝ => ((t : ℂ) - z)⁻¹)
                (Measure.dirac (eig i)) :=
              MeasureTheory.integrable_dirac (a := eig i) (f := fun t : ℝ => ((t : ℂ) - z)⁻¹)
                (by simp)
            simpa [μi] using hdir.smul_measure (by simp)))
    have hnonneg : ∀ i : Fin n, 0 ≤ Complex.normSq (c i) := fun i => Complex.normSq_nonneg (c i)
    rw [h_int0]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [μi, MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac,
      ENNReal.toReal_ofReal, hnonneg i]
    change (Complex.normSq (c i) : ℂ) * ((eig i : ℂ) - z)⁻¹ =
      ((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ)
    ring
  -- Compute `inner φ x` via the orthonormal basis.
  have h_inner :
      inner (𝕜 := ℂ) φ x =
        ∑ i : Fin n, ((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ) := by
    have hx_inner : ∀ i : Fin n, inner (𝕜 := ℂ) (b i) x = aFun i := by
      intro i
      have hrepr : b.repr x = a := by
        simp [x]
      have : (b.repr x).ofLp i = a.ofLp i := congrArg (fun v => v.ofLp i) hrepr
      simpa [b.repr_apply_apply, a, aFun] using this
    calc
      inner (𝕜 := ℂ) φ x
          = ∑ i : Fin n, inner (𝕜 := ℂ) φ (b i) * inner (𝕜 := ℂ) (b i) x := by
              symm
              simpa using (b.sum_inner_mul_inner φ x)
      _ = ∑ i : Fin n, ((starRingEnd ℂ) (c i)) * (aFun i) := by
            refine Fintype.sum_congr _ _ (fun i => ?_)
            have hc : inner (𝕜 := ℂ) (b i) φ = c i := by
              simpa [cVec, c] using (b.repr_apply_apply φ i).symm
            have hc' : inner (𝕜 := ℂ) φ (b i) = (starRingEnd ℂ) (c i) := by
              simpa [hc] using (inner_conj_symm (𝕜 := ℂ) (x := φ) (y := b i)).symm
            simp [hc', hx_inner i]
      _ = ∑ i : Fin n, ((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ) := by
            refine Fintype.sum_congr _ _ (fun i => ?_)
            have hmul : (starRingEnd ℂ) (c i) * c i = (Complex.normSq (c i) : ℂ) := by
              simpa using (Complex.normSq_eq_conj_mul_self (z := c i)).symm
            calc
              (starRingEnd ℂ) (c i) * (aFun i)
                  = (starRingEnd ℂ) (c i) * (c i * ((eig i : ℂ) - z)⁻¹) := by
                      simp [aFun, div_eq_mul_inv]
              _ = ((starRingEnd ℂ) (c i) * c i) * ((eig i : ℂ) - z)⁻¹ := by
                    simp [mul_assoc]
              _ = (Complex.normSq (c i) : ℂ) * ((eig i : ℂ) - z)⁻¹ := by
                    simp [hmul]
              _ = ((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ) := by
                    simp [mul_comm]
  -- Imaginary part is nonnegative on the upper half-plane.
  have him_nonneg : 0 ≤ (inner (𝕜 := ℂ) φ x).im := by
    rw [h_inner]
    have h_im_term :
        ∀ i : Fin n,
          0 ≤ (((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ)).im := by
      intro i
      set w : ℂ := ((eig i : ℂ) - z)⁻¹
      have hw_im : 0 ≤ w.im := by
        have hne : ((eig i : ℂ) - z) ≠ 0 := ha_ne i
        have hn : 0 < Complex.normSq ((eig i : ℂ) - z) := (Complex.normSq_pos).2 hne
        have : w.im = z.im / Complex.normSq ((eig i : ℂ) - z) := by
          simp [w, Complex.inv_im, sub_eq_add_neg]
        rw [this]
        exact div_nonneg hz.le (le_of_lt hn)
      have : (w * (Complex.normSq (c i) : ℂ)).im = w.im * Complex.normSq (c i) := by
        simp [w]
      -- both factors are nonnegative
      rw [this]
      exact mul_nonneg hw_im (Complex.normSq_nonneg (c i))
    have h_im_sum :
        (∑ i : Fin n, ((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ)).im =
          ∑ i : Fin n, (((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ)).im := by
      exact
        (Complex.im_sum (s := (Finset.univ : Finset (Fin n)))
          (f := fun i : Fin n => ((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ)))
    rw [h_im_sum]
    simpa using (Finset.sum_nonneg (fun i _hi => h_im_term i))
  refine ⟨x, hsol, ?_, him_nonneg⟩
  -- Combine the two computations for the integral representation.
  have : inner (𝕜 := ℂ) φ x = ∫ t, ((t : ℂ) - z)⁻¹ ∂μ := by
    calc
      inner (𝕜 := ℂ) φ x =
          ∑ i : Fin n, ((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ) := h_inner
      _ = ∫ t, ((t : ℂ) - z)⁻¹ ∂μ := by simpa using hμ_integral.symm
  have : inner (𝕜 := ℂ) φ x =
      ∫ t, ((t : ℂ) - z)⁻¹ ∂(diracMeasure_of_isSymmetric (T := T) (hT := hT) φ) := by
    simpa [hμ_def] using this
  simpa [one_div] using this

/-- Upper-half-plane Step 3 as an existential discrete measure and resolvent solution. -/
theorem inner_solution_eq_integral_dirac_of_isSymmetric_im_nonneg
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (φ : E) (z : ℂ) (hz : 0 < z.im) :
    ∃ μ : Measure ℝ,
      ∃ x : E,
        (T - z • (LinearMap.id : E →ₗ[ℂ] E)) x = φ ∧
          inner (𝕜 := ℂ) φ x = ∫ t, (1 / ((t : ℂ) - z)) ∂μ ∧
            0 ≤ (inner (𝕜 := ℂ) φ x).im := by
  let μ : Measure ℝ := diracMeasure_of_isSymmetric (T := T) (hT := hT) φ
  rcases
      inner_solution_eq_integral_dirac_of_isSymmetric_im_nonneg_forall (T := T)
        (hT := hT) (φ := φ) z hz
    with ⟨x, hsol, hx, him⟩
  exact ⟨μ, x, hsol, hx, him⟩

end

end

end Quantum.TraceInequality.Loewner
