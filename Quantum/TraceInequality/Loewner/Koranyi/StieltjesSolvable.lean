import Quantum.TraceInequality.Loewner.Koranyi.FinitePickData


namespace Quantum.TraceInequality.Loewner

open scoped BigOperators
open scoped ComplexOrder
open scoped MatrixOrder

open MeasureTheory

noncomputable section

section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Step 65 (utility): if the linear equation `(T - zI) x = φ` is solvable, then the scalar
`⟪φ, x⟫` is uniquely determined (independent of the choice of solution), and equals the
discrete Stieltjes integral provided by `diracMeasure_of_isSymmetric`.

This removes the hypothesis `z.im ≠ 0` from Step 3 at the cost of assuming solvability. -/
theorem inner_solution_eq_integral_dirac_of_isSymmetric_of_exists
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (φ : E) (z : ℂ)
    (hex : ∃ x : E, (T - z • (LinearMap.id : E →ₗ[ℂ] E)) x = φ) :
    ∀ x : E,
      (T - z • (LinearMap.id : E →ₗ[ℂ] E)) x = φ →
        inner (𝕜 := ℂ) φ x =
          ∫ t, (1 / ((t : ℂ) - z)) ∂(diracMeasure_of_isSymmetric (T := T) (hT := hT) φ) := by
  classical
  -- Work in the eigenvector basis of `T`.
  let n : ℕ := Module.finrank ℂ E
  have hn : Module.finrank ℂ E = n := rfl
  let b : OrthonormalBasis (Fin n) ℂ E := hT.eigenvectorBasis (n := n) (hn := hn)
  let eig : Fin n → ℝ := hT.eigenvalues (n := n) (hn := hn)
  let cVec : EuclideanSpace ℂ (Fin n) := b.repr φ
  let c : Fin n → ℂ := fun i => cVec.ofLp i
  have hT_apply_basis : ∀ i : Fin n, T (b i) = (eig i : ℂ) • b i := by
    intro i
    simp [b, eig]
  -- Any eigenvalue equal to `z` must have coefficient `0` in the expansion of `φ` (otherwise the
  -- equation would not be solvable).
  rcases hex with ⟨x₁, hx₁⟩
  have hc_eq : ∀ i : Fin n, ((eig i : ℂ) - z) * inner (𝕜 := ℂ) (b i) x₁ = c i := by
    intro i
    have hcφ : inner (𝕜 := ℂ) (b i) φ = c i := by
      simpa [cVec, c] using (b.repr_apply_apply φ i).symm
    have hsymm : inner (𝕜 := ℂ) (b i) (T x₁) = inner (𝕜 := ℂ) (T (b i)) x₁ := by
      simpa using (hT (b i) x₁).symm
    have hTi :
        inner (𝕜 := ℂ) (b i) (T x₁) = (eig i : ℂ) * inner (𝕜 := ℂ) (b i) x₁ := by
      -- Use symmetry and the diagonal action on the basis vector.
      calc
        inner (𝕜 := ℂ) (b i) (T x₁) = inner (𝕜 := ℂ) (T (b i)) x₁ := hsymm
        _ = inner (𝕜 := ℂ) ((eig i : ℂ) • b i) x₁ := by
              -- Avoid coercion to an `ℝ`-scalar smul.
              simpa using congrArg (fun v => inner (𝕜 := ℂ) v x₁) (hT_apply_basis i)
        _ = (eig i : ℂ) * inner (𝕜 := ℂ) (b i) x₁ := by
              simpa [Complex.conj_ofReal] using
                (inner_smul_left (𝕜 := ℂ) (r := (eig i : ℂ)) (x := b i) (y := x₁))
    have hinner :
        inner (𝕜 := ℂ) (b i) ((T - z • (LinearMap.id : E →ₗ[ℂ] E)) x₁) =
          ((eig i : ℂ) - z) * inner (𝕜 := ℂ) (b i) x₁ := by
      -- Expand and use linearity in the second argument.
      calc
        inner (𝕜 := ℂ) (b i) ((T - z • (LinearMap.id : E →ₗ[ℂ] E)) x₁)
            = inner (𝕜 := ℂ) (b i) (T x₁) - inner (𝕜 := ℂ) (b i) (z • x₁) := by
                simp [sub_eq_add_neg, inner_add_right]
        _ =
            (eig i : ℂ) * inner (𝕜 := ℂ) (b i) x₁ -
              z * inner (𝕜 := ℂ) (b i) x₁ := by
              simp [hTi, inner_smul_right]
        _ = ((eig i : ℂ) - z) * inner (𝕜 := ℂ) (b i) x₁ := by ring
    -- Take `inner (b i) ·` on the solvability equation.
    have hx_inner := congrArg (fun v => inner (𝕜 := ℂ) (b i) v) hx₁
    have hinner' :
        inner (𝕜 := ℂ) (b i) (T x₁ - z • x₁) =
          ((eig i : ℂ) - z) * inner (𝕜 := ℂ) (b i) x₁ := by
      simpa [LinearMap.sub_apply, LinearMap.smul_apply] using hinner
    simpa [hcφ, hinner'] using hx_inner
  have hc_zero : ∀ i : Fin n, ((eig i : ℂ) - z) = 0 → c i = 0 := by
    intro i hiz
    -- If the scalar factor vanishes, the right-hand side must be `0`.
    have := hc_eq i
    simpa [hiz] using this.symm
  -- Canonical solution with coefficients `c i / (eig i - z)` in the eigenbasis.
  let aFun : Fin n → ℂ := fun i => c i / ((eig i : ℂ) - z)
  let a : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 aFun
  let x0 : E := b.repr.symm a
  have hx0_sum : x0 = ∑ i : Fin n, (a.ofLp i) • b i := by
    simpa [x0] using (b.sum_repr_symm a).symm
  have hcancel : ∀ i : Fin n, aFun i * ((eig i : ℂ) - z) = c i := by
    intro i
    by_cases hne : ((eig i : ℂ) - z) = 0
    · have hc : c i = 0 := hc_zero i hne
      simp [aFun, hne, hc]
    · -- Standard cancellation in a field.
      have hne' : ((eig i : ℂ) - z) ≠ 0 := hne
      simp [aFun, div_eq_mul_inv, hne', mul_comm]
  have hx0_sol : (T - z • (LinearMap.id : E →ₗ[ℂ] E)) x0 = φ := by
    let s : Finset (Fin n) := Finset.univ
    have hx0_sum' : x0 = s.sum (fun i => (a.ofLp i) • b i) := by
      simpa [s] using hx0_sum
    rw [hx0_sum']
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
      have hcancel' : aFun i * ((eig i : ℂ) - z) = c i := hcancel i
      -- Expand and use the cancellation identity.
      simp [hai, hSbi, hcancel', smul_smul]
    simp [hterm', s]
    simpa [s, cVec, c] using (b.sum_repr φ)
  -- Define the discrete measure supported on the eigenvalues, with weights `‖c i‖^2`.
  let μ : Measure ℝ := diracMeasure_of_isSymmetric (T := T) (hT := hT) φ
  -- Compute the integral as a finite sum over atoms.
  have hμ_integral :
      (∫ t, ((t : ℂ) - z)⁻¹ ∂μ) =
        ∑ i : Fin n, ((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ) := by
    -- Unfold the Dirac-sum definition and compute directly.
    classical
    let μi : Fin n → Measure ℝ := fun i =>
      (ENNReal.ofReal (Complex.normSq (c i))) • Measure.dirac (eig i)
    have hμ :
        μ = ∑ i : Fin n, μi i := by
      simp [μ, diracMeasure_of_isSymmetric,
        _root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetricAux, μi, c, cVec,
        eig, b, n]
    -- Evaluate the integral on each atom and sum.
    have h_int0 :
        ∫ t, ((t : ℂ) - z)⁻¹ ∂μ =
          ∑ i : Fin n, ∫ t, ((t : ℂ) - z)⁻¹ ∂(μi i) := by
      -- `integral_finset_sum_measure` needs integrability on each summand; this is automatic
      -- for Dirac measures.
      simpa [hμ] using
        (MeasureTheory.integral_finset_sum_measure (μ := μi) (s := (Finset.univ : Finset (Fin n)))
          (f := fun t : ℝ => ((t : ℂ) - z)⁻¹)
          (by
            intro i _hi
            have hdir :
                MeasureTheory.Integrable
                  (fun t : ℝ => ((t : ℂ) - z)⁻¹) (Measure.dirac (eig i)) :=
              MeasureTheory.integrable_dirac (a := eig i)
                (f := fun t : ℝ => ((t : ℂ) - z)⁻¹) (by simp)
            simpa [μi] using hdir.smul_measure (by simp)))
    -- Now simplify each Dirac integral.
    have h_int1 :
        (∑ i : Fin n, ∫ t, ((t : ℂ) - z)⁻¹ ∂(μi i)) =
          ∑ i : Fin n, ((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ) := by
      have hnonneg : ∀ i : Fin n, 0 ≤ Complex.normSq (c i) :=
        fun i => Complex.normSq_nonneg (c i)
      refine Fintype.sum_congr _ _ (fun i => ?_)
      -- Scale the Dirac mass.
      simp only [μi, MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac,
        ENNReal.toReal_ofReal, hnonneg i]
      change (Complex.normSq (c i) : ℂ) * ((eig i : ℂ) - z)⁻¹ =
        ((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ)
      ring
    exact (h_int0.trans h_int1)
  -- Compute `inner φ x0` as a finite sum.
  have hx0_inner : inner (𝕜 := ℂ) φ x0 =
      ∑ i : Fin n, ((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ) := by
    have hx_inner : ∀ i : Fin n, inner (𝕜 := ℂ) (b i) x0 = aFun i := by
      intro i
      have hrepr : b.repr x0 = a := by
        simp [x0]
      have : (b.repr x0).ofLp i = a.ofLp i := congrArg (fun v => v.ofLp i) hrepr
      simpa [b.repr_apply_apply, a, aFun] using this
    calc
      inner (𝕜 := ℂ) φ x0
          = ∑ i : Fin n, inner (𝕜 := ℂ) φ (b i) * inner (𝕜 := ℂ) (b i) x0 := by
              symm
              simpa using (b.sum_inner_mul_inner φ x0)
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
  -- Compute the integral as a finite sum over atoms (reuse the existing Step 3 lemma).
  have hx0_integral :
      inner (𝕜 := ℂ) φ x0 = ∫ t, (1 / ((t : ℂ) - z)) ∂μ := by
    calc
      inner (𝕜 := ℂ) φ x0
          = ∑ i : Fin n, ((eig i : ℂ) - z)⁻¹ * (Complex.normSq (c i) : ℂ) := hx0_inner
      _ = ∫ t, ((t : ℂ) - z)⁻¹ ∂μ := by
            simpa using hμ_integral.symm
      _ = ∫ t, (1 / ((t : ℂ) - z)) ∂μ := by
            simp [one_div]
  -- Kernel orthogonality: any vector in `ker (T - zI)` is orthogonal to `φ`.
  have hker_orth : ∀ w : E,
      (T - z • (LinearMap.id : E →ₗ[ℂ] E)) w = 0 → inner (𝕜 := ℂ) φ w = 0 := by
    intro w hw
    have hw_eq : ∀ i : Fin n, ((eig i : ℂ) - z) * inner (𝕜 := ℂ) (b i) w = 0 := by
      intro i
      have hsymm : inner (𝕜 := ℂ) (b i) (T w) = inner (𝕜 := ℂ) (T (b i)) w := by
        simpa using (hT (b i) w).symm
      have hTi :
          inner (𝕜 := ℂ) (b i) (T w) = (eig i : ℂ) * inner (𝕜 := ℂ) (b i) w := by
        calc
          inner (𝕜 := ℂ) (b i) (T w) = inner (𝕜 := ℂ) (T (b i)) w := hsymm
          _ = inner (𝕜 := ℂ) ((eig i : ℂ) • b i) w := by simp [hT_apply_basis]
          _ = (eig i : ℂ) * inner (𝕜 := ℂ) (b i) w := by
                simpa [Complex.conj_ofReal] using
                  (inner_smul_left (𝕜 := ℂ) (r := (eig i : ℂ)) (x := b i) (y := w))
      have hinner :
          inner (𝕜 := ℂ) (b i) ((T - z • (LinearMap.id : E →ₗ[ℂ] E)) w) =
            ((eig i : ℂ) - z) * inner (𝕜 := ℂ) (b i) w := by
        calc
          inner (𝕜 := ℂ) (b i) ((T - z • (LinearMap.id : E →ₗ[ℂ] E)) w)
              = inner (𝕜 := ℂ) (b i) (T w) - inner (𝕜 := ℂ) (b i) (z • w) := by
                  simp [sub_eq_add_neg, inner_add_right]
          _ =
              (eig i : ℂ) * inner (𝕜 := ℂ) (b i) w -
                z * inner (𝕜 := ℂ) (b i) w := by
                simp [hTi, inner_smul_right]
          _ = ((eig i : ℂ) - z) * inner (𝕜 := ℂ) (b i) w := by ring
      have hw_inner := congrArg (fun v => inner (𝕜 := ℂ) (b i) v) hw
      have hinner' :
          inner (𝕜 := ℂ) (b i) (T w - z • w) =
            ((eig i : ℂ) - z) * inner (𝕜 := ℂ) (b i) w := by
        simpa [LinearMap.sub_apply, LinearMap.smul_apply] using hinner
      simpa [hinner'] using hw_inner
    -- Expand `w` in the eigenbasis and compute the inner product.
    calc
      inner (𝕜 := ℂ) φ w
          = ∑ i : Fin n, inner (𝕜 := ℂ) φ (b i) * inner (𝕜 := ℂ) (b i) w := by
              symm
              simpa using (b.sum_inner_mul_inner φ w)
      _ = ∑ i : Fin n, (starRingEnd ℂ) (c i) * inner (𝕜 := ℂ) (b i) w := by
            refine Fintype.sum_congr _ _ (fun i => ?_)
            have hc : inner (𝕜 := ℂ) (b i) φ = c i := by
              simpa [cVec, c] using (b.repr_apply_apply φ i).symm
            have hc' : inner (𝕜 := ℂ) φ (b i) = (starRingEnd ℂ) (c i) := by
              simpa [hc] using (inner_conj_symm (𝕜 := ℂ) (x := φ) (y := b i)).symm
            simp [hc']
      _ = 0 := by
            -- Each summand is zero: if `(eig i - z) ≠ 0` then the `w`-coefficient is
            -- zero; if it is zero, then `c i = 0` by solvability.
            apply Fintype.sum_eq_zero
            intro i
            by_cases hne : ((eig i : ℂ) - z) = 0
            · have hc : c i = 0 := hc_zero i hne
              simp [hc]
            · have hne' : ((eig i : ℂ) - z) ≠ 0 := hne
              have hwc : inner (𝕜 := ℂ) (b i) w = 0 := by
                have := hw_eq i
                -- Cancel the nonzero factor.
                exact (mul_eq_zero.mp this).resolve_left hne'
              simp [hwc]
  intro x hx
  -- Compare any solution to the canonical one.
  have hx_diff :
      (T - z • (LinearMap.id : E →ₗ[ℂ] E)) (x - x0) = 0 := by
    calc
      (T - z • (LinearMap.id : E →ₗ[ℂ] E)) (x - x0)
          =
            (T - z • (LinearMap.id : E →ₗ[ℂ] E)) x -
              (T - z • (LinearMap.id : E →ₗ[ℂ] E)) x0 := by
              simp [LinearMap.map_sub]
      _ = φ - φ := by simp [hx, hx0_sol]
      _ = 0 := by simp
  have hdiff_inner : inner (𝕜 := ℂ) φ (x - x0) = 0 := hker_orth (w := x - x0) hx_diff
  have : inner (𝕜 := ℂ) φ x = inner (𝕜 := ℂ) φ x0 := by
    -- Use linearity in the second argument.
    calc
      inner (𝕜 := ℂ) φ x = inner (𝕜 := ℂ) φ ((x - x0) + x0) := by
            simp
      _ = inner (𝕜 := ℂ) φ (x - x0) + inner (𝕜 := ℂ) φ x0 := by
            simpa using (inner_add_right (𝕜 := ℂ) (x := φ) (y := x - x0) (z := x0))
      _ = inner (𝕜 := ℂ) φ x0 := by
            simp [hdiff_inner]
  -- Conclude using the canonical integral identity.
  simpa [hx0_integral] using this

end

section

variable {n : ℕ} {f : ℝ → ℝ} {y : Fin (n + 1) → ℝ}

/-- Step 65 (finite case): in the Korányi finite-point construction, the distinguished vectors
`v i` satisfy a real-parameter Stieltjes identity at `z = 1 / y i` (for `i ≠ 0`). -/
theorem koranyi_finite_construct_inner_v_eq_integral_at_inv
    (hy : pointsHyp (n := n) y) (hL : (loewnerMatrix (n := n) f y).PosDef) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : FiniteDimensional ℂ H),
      ∃ (v : Fin (n + 1) → H) (φ : H) (A : H →ₗ[ℂ] H) (μ : Measure ℝ),
        (∀ i j : Fin (n + 1),
          inner (𝕜 := ℂ) (v i) (v j) = (loewnerKernel f (y i) (y j) : ℂ)) ∧
        φ = v 0 ∧
        IsSelfAdjoint A ∧
        (∀ i, i ≠ 0 → (v i - (y i : ℂ) • A (v i)) = φ) ∧
        (∀ i, i ≠ 0 →
          inner (𝕜 := ℂ) φ ((-(y i : ℂ)) • v i) =
            ∫ t, (1 / ((t : ℂ) - (1 / (y i : ℂ)))) ∂μ) := by
  classical
  rcases koranyi_finite_construct (n := n) (f := f) (y := y) hy hL with
    ⟨H, instH, instI, instFD, v, φ, A, hGram, hφ, hA, _hAv, hEq, _hInterp⟩
  letI : NormedAddCommGroup H := instH
  letI : InnerProductSpace ℂ H := instI
  letI : FiniteDimensional ℂ H := instFD
  have hSym : A.IsSymmetric := (LinearMap.isSymmetric_iff_isSelfAdjoint A).2 hA
  let μ : Measure ℝ := diracMeasure_of_isSymmetric (T := A) (hT := hSym) φ
  refine ⟨H, instH, instI, instFD, v, φ, A, μ, hGram, hφ, hA, hEq, ?_⟩
  intro i hi0
  have hyi : y i ≠ 0 := hy.2.2.2 i hi0
  have hyiC : (y i : ℂ) ≠ 0 := by exact_mod_cast hyi
  -- Provide a concrete solvable point `z = 1 / y i`.
  let z : ℂ := 1 / (y i : ℂ)
  have hz_solvable :
      (A - z • (LinearMap.id : H →ₗ[ℂ] H)) ((-(y i : ℂ)) • v i) = φ := by
    have hEq' : (v i - (y i : ℂ) • A (v i)) = φ := hEq i hi0
    have hz_mul : (y i : ℂ) * z = 1 := by
      simp [z, hyiC]
    -- Expand `(A - zI) (-(y)v)`.
    calc
      (A - z • (LinearMap.id : H →ₗ[ℂ] H)) ((-(y i : ℂ)) • v i)
          = (-(y i : ℂ)) • A (v i) - z • ((-(y i : ℂ)) • v i) := by
              simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
              rw [A.map_smul]
      _ = (-(y i : ℂ)) • A (v i) + ((y i : ℂ) * z) • v i := by
            have hz' : -(z • ((-(y i : ℂ)) • v i)) = ((y i : ℂ) * z) • v i := by
              calc
                -(z • ((-(y i : ℂ)) • v i)) = -((z * (-(y i : ℂ))) • v i) := by
                      simpa using congrArg Neg.neg (smul_smul z (-(y i : ℂ)) (v i))
                _ = (- (z * (-(y i : ℂ)))) • v i := by
                      simp
                _ = (z * (y i : ℂ)) • v i := by simp
                _ = ((y i : ℂ) * z) • v i := by simp [mul_comm]
            -- Use `rw` to avoid rewriting `-(z • _)` into `(-z) • _`.
            rw [sub_eq_add_neg]
            rw [hz']
      _ = v i - (y i : ℂ) • A (v i) := by
            simp [hz_mul, sub_eq_add_neg, add_comm]
      _ = φ := by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hEq'
  have hz_eval :
      inner (𝕜 := ℂ) φ ((-(y i : ℂ)) • v i) =
        ∫ t, (1 / ((t : ℂ) - z)) ∂(diracMeasure_of_isSymmetric (T := A) (hT := hSym) φ) := by
    -- Apply the solvable-`z` Step 65 lemma.
    have :=
      inner_solution_eq_integral_dirac_of_isSymmetric_of_exists
        (T := A) (hT := hSym) (φ := φ) (z := z)
        (hex := ⟨(-(y i : ℂ)) • v i,
          by
            simpa [LinearMap.sub_apply, LinearMap.smul_apply, z] using hz_solvable⟩)
        ((-(y i : ℂ)) • v i)
        (by
          simpa [LinearMap.sub_apply, LinearMap.smul_apply, z] using hz_solvable)
    simpa [one_div, z] using this
  -- Finish by rewriting `z` back to `1 / y i`.
  simpa [z] using hz_eval

/-!
The previous lemma returns the measure `μ` as an existential argument. For downstream packaging it
is often more convenient to fix `μ` *definitionally* as the discrete measure
`diracMeasure_of_isSymmetric A hSym φ`.  The next lemma repackages Step 65 in this form.
-/

/-- Step 65 (finite case, dirac-fixed form): same as
`koranyi_finite_construct_inner_v_eq_integral_at_inv`, but with `μ` definitionally fixed to
`diracMeasure_of_isSymmetric`. -/
theorem koranyi_finite_construct_inner_v_eq_integral_at_inv_dirac
    (hy : pointsHyp (n := n) y) (hL : (loewnerMatrix (n := n) f y).PosDef) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : FiniteDimensional ℂ H),
      ∃ (v : Fin (n + 1) → H) (φ : H) (A : H →ₗ[ℂ] H) (hA : IsSelfAdjoint A),
        (∀ i j : Fin (n + 1),
          inner (𝕜 := ℂ) (v i) (v j) = (loewnerKernel f (y i) (y j) : ℂ)) ∧
        φ = v 0 ∧
        (∀ i, i ≠ 0 → (v i - (y i : ℂ) • A (v i)) = φ) ∧
        let hSym : A.IsSymmetric := (LinearMap.isSymmetric_iff_isSelfAdjoint A).2 hA
        let μ : Measure ℝ := diracMeasure_of_isSymmetric (T := A) (hT := hSym) φ
        (∀ i, i ≠ 0 →
          inner (𝕜 := ℂ) φ ((-(y i : ℂ)) • v i) =
            ∫ t, (1 / ((t : ℂ) - (1 / (y i : ℂ)))) ∂μ) := by
  classical
  rcases koranyi_finite_construct (n := n) (f := f) (y := y) hy hL with
    ⟨H, instH, instI, instFD, v, φ, A, hGram, hφ, hA, _hAv, hEq, _hInterp⟩
  letI : NormedAddCommGroup H := instH
  letI : InnerProductSpace ℂ H := instI
  letI : FiniteDimensional ℂ H := instFD
  have hSym : A.IsSymmetric := (LinearMap.isSymmetric_iff_isSelfAdjoint A).2 hA
  let μ : Measure ℝ := diracMeasure_of_isSymmetric (T := A) (hT := hSym) φ
  refine ⟨H, instH, instI, instFD, v, φ, A, hA, hGram, hφ, hEq, ?_⟩
  dsimp [hSym, μ]
  intro i hi0
  have hyi : y i ≠ 0 := hy.2.2.2 i hi0
  have hyiC : (y i : ℂ) ≠ 0 := by exact_mod_cast hyi
  -- Provide a concrete solvable point `z = 1 / y i`.
  let z : ℂ := 1 / (y i : ℂ)
  have hz_solvable :
      (A - z • (LinearMap.id : H →ₗ[ℂ] H)) ((-(y i : ℂ)) • v i) = φ := by
    have hEq' : (v i - (y i : ℂ) • A (v i)) = φ := hEq i hi0
    have hz_mul : (y i : ℂ) * z = 1 := by
      simp [z, hyiC]
    -- Expand `(A - zI) (-(y)v)`.
    calc
      (A - z • (LinearMap.id : H →ₗ[ℂ] H)) ((-(y i : ℂ)) • v i)
          = (-(y i : ℂ)) • A (v i) - z • ((-(y i : ℂ)) • v i) := by
              simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
              rw [A.map_smul]
      _ = (-(y i : ℂ)) • A (v i) + ((y i : ℂ) * z) • v i := by
            have hz' : -(z • ((-(y i : ℂ)) • v i)) = ((y i : ℂ) * z) • v i := by
              calc
                -(z • ((-(y i : ℂ)) • v i)) = -((z * (-(y i : ℂ))) • v i) := by
                      simpa using congrArg Neg.neg (smul_smul z (-(y i : ℂ)) (v i))
                _ = (- (z * (-(y i : ℂ)))) • v i := by
                      simp
                _ = (z * (y i : ℂ)) • v i := by simp
                _ = ((y i : ℂ) * z) • v i := by simp [mul_comm]
            -- Use `rw` to avoid rewriting `-(z • _)` into `(-z) • _`.
            rw [sub_eq_add_neg]
            rw [hz']
      _ = v i - (y i : ℂ) • A (v i) := by
            simp [hz_mul, sub_eq_add_neg, add_comm]
      _ = φ := by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hEq'
  have hz_eval :
      inner (𝕜 := ℂ) φ ((-(y i : ℂ)) • v i) =
        ∫ t, (1 / ((t : ℂ) - z)) ∂(diracMeasure_of_isSymmetric (T := A) (hT := hSym) φ) := by
    -- Apply the solvable-`z` Step 65 lemma.
    have :=
      inner_solution_eq_integral_dirac_of_isSymmetric_of_exists
        (T := A) (hT := hSym) (φ := φ) (z := z)
        (hex := ⟨(-(y i : ℂ)) • v i,
          by
            simpa [LinearMap.sub_apply, LinearMap.smul_apply, z] using hz_solvable⟩)
        ((-(y i : ℂ)) • v i)
        (by
          simpa [LinearMap.sub_apply, LinearMap.smul_apply, z] using hz_solvable)
    simpa [one_div, z] using this
  -- Finish by rewriting `z` back to `1 / y i`.
  simpa [μ, z] using hz_eval

/-! ### Consequence: recovering `loewnerKernel f (y i) 0` from the discrete measure -/

/-- In the Korányi finite-point construction, the divided difference at `(y i, 0)` (encoded as
`loewnerKernel f (y i) 0`) can be expressed using the same discrete measure. -/
theorem koranyi_finite_construct_loewnerKernel_zero_eq_integral_at_inv
    (hy : pointsHyp (n := n) y) (hL : (loewnerMatrix (n := n) f y).PosDef) :
    ∃ (μ : Measure ℝ),
      ∀ i : Fin (n + 1),
        i ≠ 0 →
          (loewnerKernel f (y i) 0 : ℂ) =
            (-(1 / (y i : ℂ))) *
              ∫ t, (1 / ((t : ℂ) - (1 / (y i : ℂ)))) ∂μ := by
  classical
  rcases koranyi_finite_construct_inner_v_eq_integral_at_inv (n := n) (f := f) (y := y) hy hL with
    ⟨H, instH, instI, instFD, v, φ, A, μ, hGram, hφ, _hA, hEq, hI⟩
  refine ⟨μ, ?_⟩
  intro i hi0
  have hy0 : y 0 = 0 := hy.1
  have hyi : y i ≠ 0 := hy.2.2.2 i hi0
  have hyiC : (y i : ℂ) ≠ 0 := by exact_mod_cast hyi
  have hinner_i0 : inner (𝕜 := ℂ) (v i) φ = (loewnerKernel f (y i) 0 : ℂ) := by
    simpa [hφ, hy0] using (hGram i 0)
  have hinner0_i : inner (𝕜 := ℂ) φ (v i) = (loewnerKernel f (y i) 0 : ℂ) := by
    -- The right-hand side is real, so conjugation does nothing.
    have hconj : star (inner (𝕜 := ℂ) (v i) φ) = inner (𝕜 := ℂ) φ (v i) := by
      simp
    calc
      inner (𝕜 := ℂ) φ (v i) = star (inner (𝕜 := ℂ) (v i) φ) := by
        simp
      _ = (loewnerKernel f (y i) 0 : ℂ) := by
        simp [hinner_i0]
  have hI' : inner (𝕜 := ℂ) φ ((-(y i : ℂ)) • v i) =
      ∫ t, (1 / ((t : ℂ) - (1 / (y i : ℂ)))) ∂μ := hI i hi0
  -- Solve for `inner φ (v i)` in the scalar equation.
  have hsolve :
      inner (𝕜 := ℂ) φ (v i) =
        (-(1 / (y i : ℂ))) *
          ∫ t, (1 / ((t : ℂ) - (1 / (y i : ℂ)))) ∂μ := by
    have hyneg : (-(y i : ℂ)) ≠ 0 := neg_ne_zero.mpr hyiC
    have htmp :
        inner (𝕜 := ℂ) φ (v i) =
          (-(y i : ℂ))⁻¹ *
            ∫ t, (1 / ((t : ℂ) - (1 / (y i : ℂ)))) ∂μ := by
      have hlin' := hI'
      -- Keep the scalar as a complex number to use `inner_smul_right` directly.
      rw [inner_smul_right] at hlin'
      have hmul :
          (-(y i : ℂ))⁻¹ * (-(y i : ℂ) * inner (𝕜 := ℂ) φ (v i)) =
            (-(y i : ℂ))⁻¹ *
              ∫ t, (1 / ((t : ℂ) - (1 / (y i : ℂ)))) ∂μ := by
        simpa [mul_assoc] using congrArg (fun w => (-(y i : ℂ))⁻¹ * w) hlin'
      have hcancel :
          (-(y i : ℂ))⁻¹ * (-(y i : ℂ) * inner (𝕜 := ℂ) φ (v i)) =
            inner (𝕜 := ℂ) φ (v i) := by
        simpa [mul_assoc] using
          (inv_mul_cancel_left₀ hyneg (inner (𝕜 := ℂ) φ (v i)))
      exact hcancel.symm.trans hmul
    -- Rewrite `(-(y i))⁻¹` as `-(1 / (y i))`.
    simpa [div_eq_mul_inv, inv_neg, mul_assoc] using htmp
  -- Combine with the Gram identity at `(i,0)`.
  simpa [hinner0_i] using hsolve


end

end

end Quantum.TraceInequality.Loewner
