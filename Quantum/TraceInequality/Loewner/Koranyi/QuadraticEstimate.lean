import Quantum.TraceInequality.Loewner.Koranyi.DyadicCover
import Quantum.TraceInequality.Loewner.Koranyi.FiniteSpectralMeasure

import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension


namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set

noncomputable section

open scoped BigOperators

/-!
Step 45 (utility): a "quadratic estimate" for the discrete measure from Step 3.

Let `μ` be the discrete measure built from a symmetric endomorphism `T` and a vector `φ`
(Step 3).  If `δ` is any solution of `(T - x0 I) δ = φ` at a real point `x0`,
then the inverse-square `lintegral` at `x0` is bounded by `‖δ‖^2`.

This is the finite-dimensional core behind inequalities of the form
`∫ (x - x0)^{-2} dμ(x) ≤ ‖δ‖^2`, and is proved by expanding in an eigenbasis.
-/

section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/--
If `(T - x0 I) δ = φ`, the inverse-square lintegral is bounded by `‖δ‖ ^ 2`.
-/
theorem lintegral_sqInvDist_diracMeasure_le_of_solution
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (φ δ : E) (x0 : ℝ)
    (hsol : (T - (x0 : ℂ) • (LinearMap.id : E →ₗ[ℂ] E)) δ = φ) :
    (∫⁻ y, sqInvDist x0 y ∂(diracMeasure_of_isSymmetric (T := T) (hT := hT) φ)) ≤
      ENNReal.ofReal (‖δ‖ ^ 2) := by
  classical
  -- Work in the eigenvector basis of `T`.
  let n : ℕ := Module.finrank ℂ E
  have hn : Module.finrank ℂ E = n := rfl
  let b : OrthonormalBasis (Fin n) ℂ E := hT.eigenvectorBasis (n := n) (hn := hn)
  let eig : Fin n → ℝ := hT.eigenvalues (n := n) (hn := hn)
  let cVec : EuclideanSpace ℂ (Fin n) := b.repr φ
  let dVec : EuclideanSpace ℂ (Fin n) := b.repr δ
  let c : Fin n → ℂ := fun i => cVec.ofLp i
  let d : Fin n → ℂ := fun i => dVec.ofLp i
  have hT_apply_basis : ∀ i : Fin n, T (b i) = (eig i : ℂ) • b i := by
    intro i
    simp [b, eig]
  have hc_inner : ∀ i : Fin n, inner (𝕜 := ℂ) (b i) φ = c i := by
    intro i
    simpa [cVec, c] using (b.repr_apply_apply φ i).symm
  have hd_inner : ∀ i : Fin n, inner (𝕜 := ℂ) (b i) δ = d i := by
    intro i
    simpa [dVec, d] using (b.repr_apply_apply δ i).symm
  -- Coordinate-wise equation `(eig i - x0) * d i = c i`.
  have hcoord : ∀ i : Fin n, ((eig i : ℂ) - x0) * d i = c i := by
    intro i
    -- Freeze the scalar as a complex number to avoid rewriting to real scalar multiplication.
    let x0C : ℂ := x0
    have hsol' : (T - x0C • (LinearMap.id : E →ₗ[ℂ] E)) δ = φ := by
      simpa [x0C] using hsol
    have hinner :=
      congrArg (fun x => inner (𝕜 := ℂ) (b i) x) hsol'
    -- Expand the left-hand side and use symmetry to move `T` across the inner product.
    have hsymm : inner (𝕜 := ℂ) (b i) (T δ) = inner (𝕜 := ℂ) (T (b i)) δ := by
      simpa using (hT (b i) δ).symm
    -- Now compute.
    -- We keep the final expression in terms of `c i` and `d i` via `hc_inner`/`hd_inner`.
    -- The simplifications are all scalar-field computations.
    have :
        inner (𝕜 := ℂ) (b i) (T δ) - x0C * inner (𝕜 := ℂ) (b i) δ =
          inner (𝕜 := ℂ) (b i) φ := by
      -- Unfold `T - x0•id` and use linearity in the second argument.
      simpa [LinearMap.sub_apply, LinearMap.smul_apply, inner_sub_right,
        inner_smul_right, mul_assoc] using hinner
    -- Substitute `inner (b i) (T δ)` and `T (b i) = eig i • b i`.
    -- Finally rewrite `inner (b i) δ`/`inner (b i) φ` as `d i`/`c i`.
    -- Note: `eig i` is real, so `conj (eig i : ℂ) = eig i`.
    have hTb :
        inner (𝕜 := ℂ) (b i) (T δ) = (eig i : ℂ) * inner (𝕜 := ℂ) (b i) δ := by
      calc
        inner (𝕜 := ℂ) (b i) (T δ) = inner (𝕜 := ℂ) (T (b i)) δ := hsymm
        _ = inner (𝕜 := ℂ) ((eig i : ℂ) • b i) δ := by simp [hT_apply_basis]
        _ = (eig i : ℂ) * inner (𝕜 := ℂ) (b i) δ := by
              -- `inner_smul_left` introduces `starRingEnd`; for a real scalar this is harmless.
              calc
                inner (𝕜 := ℂ) ((eig i : ℂ) • b i) δ
                    = (starRingEnd ℂ) (eig i : ℂ) * inner (𝕜 := ℂ) (b i) δ := by
                        simpa using
                          (inner_smul_left (𝕜 := ℂ) (x := b i) (y := δ)
                            (r := (eig i : ℂ)))
                _ = (eig i : ℂ) * inner (𝕜 := ℂ) (b i) δ := by simp
    -- Put things together.
    -- Start from `hTb` and the expanded equality `this`.
    have :
        ((eig i : ℂ) - x0C) * inner (𝕜 := ℂ) (b i) δ = inner (𝕜 := ℂ) (b i) φ := by
      -- Replace `inner (b i) (T δ)` in `this`.
      -- Then regroup.
      calc
        ((eig i : ℂ) - x0C) * inner (𝕜 := ℂ) (b i) δ
            = (eig i : ℂ) * inner (𝕜 := ℂ) (b i) δ -
                x0C * inner (𝕜 := ℂ) (b i) δ := by
              ring
        _ = inner (𝕜 := ℂ) (b i) (T δ) - x0C * inner (𝕜 := ℂ) (b i) δ := by
              simp [hTb]
        _ = inner (𝕜 := ℂ) (b i) φ := this
    -- Rewrite inner products as coordinates.
    simpa [x0C, hc_inner, hd_inner, d] using this
  -- Unfold the discrete measure as a finite sum of Dirac atoms.
  let μi : Fin n → Measure ℝ := fun i =>
    (ENNReal.ofReal (Complex.normSq (c i))) • Measure.dirac (eig i)
  let μ : Measure ℝ := ∑ i : Fin n, μi i
  have hμ_def :
      μ = diracMeasure_of_isSymmetric (T := T) (hT := hT) φ := by
    simp [diracMeasure_of_isSymmetric, diracMeasure_of_isSymmetricAux, μ, μi, c, cVec, eig, b, n]
  have hlin :
      (∫⁻ y, sqInvDist x0 y ∂μ) =
        ∑ i : Fin n, ENNReal.ofReal (Complex.normSq (c i)) * sqInvDist x0 (eig i) := by
    simp [μ, μi, sqInvDist]
  -- Pointwise bound for each atom: the inverse-square term is controlled by the corresponding
  -- coordinate of `δ`.
  have hterm :
      ∀ i : Fin n,
        ENNReal.ofReal (Complex.normSq (c i)) * sqInvDist x0 (eig i) ≤
          ENNReal.ofReal (Complex.normSq (d i)) := by
    intro i
    by_cases hxe : eig i = x0
    · -- Then `c i = 0`, so the weight is zero and the term vanishes.
      have hc0 : c i = 0 := by
        have : ((eig i : ℂ) - x0) * d i = c i := hcoord i
        simp [hxe] at this
        simpa using this.symm
      simp [sqInvDist, hc0]
    · -- Otherwise we can cancel the distance factor and get equality.
      have habs_pos : 0 < abs (eig i - x0) := by
        have : eig i - x0 ≠ 0 := sub_ne_zero.mpr (by
          intro h
          exact hxe h)
        simpa using (abs_pos.mpr this)
      have habs_ne0 : ENNReal.ofReal (abs (eig i - x0)) ≠ 0 := by
        exact (ENNReal.ofReal_ne_zero_iff).2 habs_pos
      have habs_ne_top : ENNReal.ofReal (abs (eig i - x0)) ≠ ⊤ := ENNReal.ofReal_ne_top
      -- Rewrite the weight using `hcoord`.
      have hc_mul : c i = ((eig i : ℂ) - x0) * d i := by
        simpa [mul_comm] using (hcoord i).symm
      have hnorm :
          Complex.normSq (c i) = (abs (eig i - x0)) ^ (2 : ℕ) * Complex.normSq (d i) := by
        -- Use multiplicativity of `normSq` and `normSq (ofReal r) = r^2 = |r|^2`.
        calc
          Complex.normSq (c i)
              = Complex.normSq ((↑(eig i) - (x0 : ℂ)) * d i) := by
                    simp [hc_mul]
          _ = Complex.normSq (↑(eig i) - (x0 : ℂ)) * Complex.normSq (d i) := by
                    simp [Complex.normSq_mul]
          _ = (abs (eig i - x0)) ^ (2 : ℕ) * Complex.normSq (d i) := by
                    have hnormSq :
                        Complex.normSq (↑(eig i) - (x0 : ℂ)) =
                          (abs (eig i - x0)) ^ (2 : ℕ) := by
                      calc
                        Complex.normSq (↑(eig i) - (x0 : ℂ))
                            = Complex.normSq ((eig i - x0 : ℝ) : ℂ) := by simp
                        _ = (eig i - x0) ^ (2 : ℕ) := by
                              simpa [pow_two] using (Complex.normSq_ofReal (eig i - x0))
                        _ = (abs (eig i - x0)) ^ (2 : ℕ) := by
                              simp
                    simp [hnormSq]
      -- Convert to `ENNReal` and cancel.
      have habs_nonneg : 0 ≤ abs (eig i - x0) := abs_nonneg _
      -- Convert to `ENNReal` and cancel the distance factor.
      have hcancel :
          (ENNReal.ofReal (abs (eig i - x0)) ^ (2 : ℕ)) *
              ((ENNReal.ofReal (abs (eig i - x0)))⁻¹) ^ (2 : ℕ) = 1 := by
        -- Set `a := ofReal |eig i - x0|` and cancel explicitly.
        set a : ENNReal := ENNReal.ofReal (abs (eig i - x0))
        have ha0 : a ≠ 0 := by simpa [a] using habs_ne0
        have hat : a ≠ ⊤ := by simp [a]
        calc
          a ^ (2 : ℕ) * a⁻¹ ^ (2 : ℕ) = (a * a) * (a⁻¹ * a⁻¹) := by
                simp [pow_two, mul_assoc]
          _ = (a * a⁻¹) * (a * a⁻¹) := by
                simp [mul_assoc, mul_left_comm, mul_comm]
          _ = 1 := by
                simp [ENNReal.mul_inv_cancel ha0 hat]
      have hEq :
          ENNReal.ofReal (Complex.normSq (c i)) * sqInvDist x0 (eig i) =
            ENNReal.ofReal (Complex.normSq (d i)) := by
        calc
          ENNReal.ofReal (Complex.normSq (c i)) * sqInvDist x0 (eig i)
              = ENNReal.ofReal ((abs (eig i - x0)) ^ (2 : ℕ) * Complex.normSq (d i)) *
                    ((ENNReal.ofReal (abs (eig i - x0)))⁻¹) ^ (2 : ℕ) := by
                    -- Rewrite the weight via `hnorm` and unfold the kernel `sqInvDist`.
                    rw [sqInvDist, hnorm]
          _ =
              ((ENNReal.ofReal (abs (eig i - x0))) ^ (2 : ℕ) *
                ENNReal.ofReal (Complex.normSq (d i))) *
                  ((ENNReal.ofReal (abs (eig i - x0)))⁻¹) ^ (2 : ℕ) := by
                have habs_nonneg : 0 ≤ abs (eig i - x0) := abs_nonneg _
                have hpow_nonneg : 0 ≤ (abs (eig i - x0)) ^ (2 : ℕ) := by positivity
                have hmul :
                    ENNReal.ofReal ((abs (eig i - x0)) ^ (2 : ℕ) * Complex.normSq (d i)) =
                      ENNReal.ofReal ((abs (eig i - x0)) ^ (2 : ℕ)) *
                        ENNReal.ofReal (Complex.normSq (d i)) := by
                  simpa using
                    (ENNReal.ofReal_mul
                      (p := (abs (eig i - x0)) ^ (2 : ℕ))
                      (q := Complex.normSq (d i)) hpow_nonneg)
                have hpow :
                    ENNReal.ofReal ((abs (eig i - x0)) ^ (2 : ℕ)) =
                      (ENNReal.ofReal (abs (eig i - x0))) ^ (2 : ℕ) := by
                  simpa using (ENNReal.ofReal_pow habs_nonneg (2 : ℕ))
                -- Apply `hmul` and then `hpow`.
                calc
                  ENNReal.ofReal ((abs (eig i - x0)) ^ (2 : ℕ) * Complex.normSq (d i)) *
                      ((ENNReal.ofReal (abs (eig i - x0)))⁻¹) ^ (2 : ℕ)
                      =
                      (ENNReal.ofReal ((abs (eig i - x0)) ^ (2 : ℕ)) *
                        ENNReal.ofReal (Complex.normSq (d i))) *
                        ((ENNReal.ofReal (abs (eig i - x0)))⁻¹) ^ (2 : ℕ) := by
                        -- Avoid `simp` rewriting `|r|^2` into `r^2`; use `congrArg` directly.
                        simpa using
                          congrArg (fun x =>
                            x * ((ENNReal.ofReal (abs (eig i - x0)))⁻¹) ^ (2 : ℕ)) hmul
                  _ =
                      ((ENNReal.ofReal (abs (eig i - x0))) ^ (2 : ℕ) *
                        ENNReal.ofReal (Complex.normSq (d i))) *
                        ((ENNReal.ofReal (abs (eig i - x0)))⁻¹) ^ (2 : ℕ) := by
                        simpa [mul_assoc] using
                          congrArg (fun x =>
                            (x * ENNReal.ofReal (Complex.normSq (d i))) *
                              ((ENNReal.ofReal (abs (eig i - x0)))⁻¹) ^ (2 : ℕ)) hpow
          _ = ENNReal.ofReal (Complex.normSq (d i)) := by
                -- Associate as `(a^2 * (a⁻¹)^2) * ofReal(normSq d)` and use `hcancel`.
                calc
                  ((ENNReal.ofReal (abs (eig i - x0))) ^ (2 : ℕ) *
                    ENNReal.ofReal (Complex.normSq (d i))) *
                      ((ENNReal.ofReal (abs (eig i - x0)))⁻¹) ^ (2 : ℕ)
                      = ENNReal.ofReal (Complex.normSq (d i)) *
                          (((ENNReal.ofReal (abs (eig i - x0))) ^ (2 : ℕ)) *
                            ((ENNReal.ofReal (abs (eig i - x0)))⁻¹) ^ (2 : ℕ)) := by
                          simp [mul_assoc, mul_left_comm, mul_comm]
                  _ = ENNReal.ofReal (Complex.normSq (d i)) * 1 := by
                        simp [hcancel, mul_comm]
                  _ = ENNReal.ofReal (Complex.normSq (d i)) := by simp
      exact le_of_eq hEq
  -- Sum the pointwise bounds and compare to `‖δ‖^2`.
  have hsum :
      (∑ i : Fin n, ENNReal.ofReal (Complex.normSq (c i)) * sqInvDist x0 (eig i)) ≤
        ∑ i : Fin n, ENNReal.ofReal (Complex.normSq (d i)) := by
    simpa using (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun i _ => hterm i))
  have hsum_ofReal :
      (∑ i : Fin n, ENNReal.ofReal (Complex.normSq (d i))) =
        ENNReal.ofReal (∑ i : Fin n, Complex.normSq (d i)) := by
    have hnonneg :
        ∀ i : Fin n, i ∈ (Finset.univ : Finset (Fin n)) →
          0 ≤ Complex.normSq (d i) := by
      intro i _hi
      exact Complex.normSq_nonneg (d i)
    simpa using
      (ENNReal.ofReal_sum_of_nonneg (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => Complex.normSq (d i))
        hnonneg).symm
  have hnorm_repr : ‖dVec‖ = ‖δ‖ := by
    simp [dVec]
  have hsum_normsq :
      (∑ i : Fin n, Complex.normSq (d i)) = ‖dVec‖ ^ (2 : ℕ) := by
    -- `EuclideanSpace` is `PiLp 2`, so the squared norm is the sum of squared norms of entries.
    have hnorm_sq :
        ‖dVec‖ ^ 2 = ∑ i : Fin n, ‖dVec.ofLp i‖ ^ 2 := by
      simpa [EuclideanSpace] using
        (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin n => ℂ)
          (x := (dVec : PiLp 2 fun _ : Fin n => ℂ)))
    have hterm' :
        (∑ i : Fin n, Complex.normSq (d i)) = ∑ i : Fin n, ‖dVec.ofLp i‖ ^ 2 := by
      simp [d, Complex.normSq_eq_norm_sq]
    simpa [pow_two, hterm'] using hnorm_sq.symm
  -- Put everything together.
  have :
      (∫⁻ y, sqInvDist x0 y ∂(diracMeasure_of_isSymmetric (T := T) (hT := hT) φ)) ≤
        ENNReal.ofReal (‖δ‖ ^ 2) := by
    -- Rewrite to the unfolded measure `μ`.
    have :
        (∫⁻ y, sqInvDist x0 y ∂μ) ≤ ENNReal.ofReal (‖δ‖ ^ 2) := by
      calc
        (∫⁻ y, sqInvDist x0 y ∂μ)
            = ∑ i : Fin n, ENNReal.ofReal (Complex.normSq (c i)) * sqInvDist x0 (eig i) := hlin
        _ ≤ ∑ i : Fin n, ENNReal.ofReal (Complex.normSq (d i)) := hsum
        _ = ENNReal.ofReal (∑ i : Fin n, Complex.normSq (d i)) := hsum_ofReal
        _ = ENNReal.ofReal (‖dVec‖ ^ (2 : ℕ)) := by simp [hsum_normsq]
        _ = ENNReal.ofReal (‖δ‖ ^ (2 : ℕ)) := by simp [hnorm_repr]
        _ = ENNReal.ofReal (‖δ‖ ^ 2) := by simp [pow_two]
    simpa [hμ_def] using this
  exact this

end

end

end Quantum.TraceInequality.Loewner
