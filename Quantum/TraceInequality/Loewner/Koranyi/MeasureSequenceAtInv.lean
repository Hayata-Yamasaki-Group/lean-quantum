import Quantum.TraceInequality.Loewner.Koranyi.StieltjesSolvable
import Quantum.TraceInequality.Loewner.Koranyi.StieltjesTransform
import Quantum.TraceInequality.Loewner.Koranyi.DiracMeasureMass
import Quantum.TraceInequality.Loewner.Koranyi.FiniteConstruction
import Quantum.TraceInequality.Loewner.Koranyi.OneSubMulKernel
import Quantum.TraceInequality.Loewner.Koranyi.SupportElimAlgebra
import Quantum.TraceInequality.Loewner.Koranyi.PackageStructures


namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set Filter

open scoped UpperHalfPlane
open scoped ComplexOrder
open scoped MatrixOrder

noncomputable section

/-!
Step 57' (bridge, with extra finite-point data):

Starting from a family of finite-point Löwner matrices (`PosDef`), we produce a sequence of
discrete measures with a uniform mass bound and Pick property, together with an explicit
finite-point evaluation formula:

for each `n` and `i ≠ 0`, the value `f (y n i)` is recovered from the same discrete measure by
evaluating the Stieltjes transform at the real point `1 / y n i`.

This strengthens `exists_measureSeq_of_loewnerMatrix_posDef` by retaining a small portion of the
finite-point interpolation data in a form that will be useful for later boundary-value arguments.
-/

private theorem exists_measureSeq_core_of_loewnerMatrix_posDef_with_eval_at_inv
    (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hy : ∀ n : ℕ, pointsHyp (n := n) (y n))
    (hL : ∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef) :
    Nonempty (Loewner.RawEvalInvKernelIntegrablePackage f y) := by
  classical
  have hex :
      ∀ n : ℕ,
        ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
          (_ : FiniteDimensional ℂ H),
          ∃ (v : Fin (n + 1) → H) (φ : H) (A : H →ₗ[ℂ] H) (hA : IsSelfAdjoint A),
            (∀ i j : Fin (n + 1),
                inner (𝕜 := ℂ) (v i) (v j) = (loewnerKernel f (y n i) (y n j) : ℂ)) ∧
              φ = v 0 ∧
                (∀ i, i ≠ 0 → (v i - (y n i : ℂ) • A (v i)) = φ) ∧
                    let hSym : A.IsSymmetric := (LinearMap.isSymmetric_iff_isSelfAdjoint A).2 hA
                    let μ : Measure ℝ := diracMeasure_of_isSymmetric (T := A) (hT := hSym) φ
                    (∀ i, i ≠ 0 →
                      inner (𝕜 := ℂ) φ ((-(y n i : ℂ)) • v i) =
                        ∫ t, (1 / ((t : ℂ) - (1 / (y n i : ℂ)))) ∂μ) :=
    fun n =>
      koranyi_finite_construct_inner_v_eq_integral_at_inv_dirac (n := n) (f := f) (y := y n)
        (hy := hy n) (hL := hL n)
  choose H instH instI instFD v φ A hA hGram hφ hEq hI using hex
  let hSym : ∀ n : ℕ, (A n).IsSymmetric :=
    fun n => (LinearMap.isSymmetric_iff_isSelfAdjoint (A n)).2 (hA n)
  let μn : ℕ → Measure ℝ :=
    fun n => diracMeasure_of_isSymmetric (T := A n) (hT := hSym n) (φ n)
  have hμ_univ : ∀ n : ℕ, μn n Set.univ = ENNReal.ofReal (loewnerKernel f 0 0) := by
    intro n
    have hy0 : y n 0 = 0 := (hy n).1
    have hmass :
        μn n Set.univ = ENNReal.ofReal (‖φ n‖ ^ 2) := by
      simpa [μn] using diracMeasure_of_isSymmetric_univ (T := A n) (hT := hSym n) (φ := φ n)
    have hnorm_sq : ‖φ n‖ ^ 2 = loewnerKernel f 0 0 := by
      -- From the Gram identity at `(0,0)`, together with `φ = v 0`.
      have hinner :
          inner (𝕜 := ℂ) (φ n) (φ n) = (loewnerKernel f 0 0 : ℂ) := by
        simpa [hφ n, hy0] using (hGram n 0 0)
      -- Take real parts and use `re ⟪φ,φ⟫ = ‖φ‖^2`.
      have hre : (inner (𝕜 := ℂ) (φ n) (φ n)).re = loewnerKernel f 0 0 := by
        simpa using congrArg Complex.re hinner
      have hnorm : (inner (𝕜 := ℂ) (φ n) (φ n)).re = ‖φ n‖ ^ 2 := by
        simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (x := φ n))
      exact hnorm.symm.trans hre
    simpa [hnorm_sq] using hmass
  have hmass_bound : ∃ M0 : ENNReal, M0 < ⊤ ∧ ∀ n : ℕ, μn n Set.univ ≤ M0 := by
    refine ⟨ENNReal.ofReal (loewnerKernel f 0 0), by simp, ?_⟩
    intro n
    simp [hμ_univ n]
  have hPick : ∀ n : ℕ, ∀ z : ℍ, 0 ≤ (stieltjes (μn n) z).im := by
    intro n z
    have hStep3 :
        ∀ z : ℂ,
          0 < z.im →
            ∃ x : H n,
              (A n - z • (LinearMap.id : H n →ₗ[ℂ] H n)) x = φ n ∧
                inner (𝕜 := ℂ) (φ n) x = ∫ t, (1 / ((t : ℂ) - z)) ∂(μn n) ∧
                  0 ≤ (inner (𝕜 := ℂ) (φ n) x).im := by
      intro z hz
      simpa [μn] using
        inner_solution_eq_integral_dirac_of_isSymmetric_im_nonneg_forall (T := A n) (hT := hSym n)
          (φ := φ n) z hz
    exact stieltjes_im_nonneg_of_pick_data (A := A n) (φ := φ n) (μ := μn n) hStep3 z
  have hEval :
      ∀ n : ℕ,
        ∀ i : Fin (n + 1),
          i ≠ 0 →
            (f (y n i) : ℂ) =
              (f 0 : ℂ) -
                ∫ t, (1 / ((t : ℂ) - (1 / (y n i : ℂ)))) ∂(μn n) := by
    intro n i hi0
    have hy0 : y n 0 = 0 := (hy n).1
    have hyi : y n i ≠ 0 := (hy n).2.2.2 i hi0
    have hyiC : (y n i : ℂ) ≠ 0 := by exact_mod_cast hyi
    -- First, recover `loewnerKernel f (y i) 0` from the Stieltjes integral at `1 / y i`.
    have hinner_i0 :
        inner (𝕜 := ℂ) (v n i) (φ n) = (loewnerKernel f (y n i) 0 : ℂ) := by
      simpa [hφ n, hy0] using (hGram n i 0)
    have hinner0_i :
        inner (𝕜 := ℂ) (φ n) (v n i) = (loewnerKernel f (y n i) 0 : ℂ) := by
      have hconj :
          star (inner (𝕜 := ℂ) (v n i) (φ n)) = inner (𝕜 := ℂ) (φ n) (v n i) := by
        simp
      calc
        inner (𝕜 := ℂ) (φ n) (v n i) = star (inner (𝕜 := ℂ) (v n i) (φ n)) := by
          simp
        _ = (loewnerKernel f (y n i) 0 : ℂ) := by
          simp [hinner_i0]
    have hI' :
        inner (𝕜 := ℂ) (φ n) ((-(y n i : ℂ)) • v n i) =
          ∫ t, (1 / ((t : ℂ) - (1 / (y n i : ℂ)))) ∂(μn n) := by
      simpa [μn, hSym] using (hI n i hi0)
    have hk_int :
        (loewnerKernel f (y n i) 0 : ℂ) =
          (-(1 / (y n i : ℂ))) *
            ∫ t, (1 / ((t : ℂ) - (1 / (y n i : ℂ)))) ∂(μn n) := by
      have hyneg : (-(y n i : ℂ)) ≠ 0 := neg_ne_zero.mpr hyiC
      have htmp :
          inner (𝕜 := ℂ) (φ n) (v n i) =
            (-(y n i : ℂ))⁻¹ *
              ∫ t, (1 / ((t : ℂ) - (1 / (y n i : ℂ)))) ∂(μn n) := by
        have hlin' := hI'
        rw [inner_smul_right] at hlin'
        have hmul :
            (-(y n i : ℂ))⁻¹ * (-(y n i : ℂ) * inner (𝕜 := ℂ) (φ n) (v n i)) =
              (-(y n i : ℂ))⁻¹ *
                ∫ t, (1 / ((t : ℂ) - (1 / (y n i : ℂ)))) ∂(μn n) := by
          simpa [mul_assoc] using congrArg (fun w => (-(y n i : ℂ))⁻¹ * w) hlin'
        have hcancel :
            (-(y n i : ℂ))⁻¹ * (-(y n i : ℂ) * inner (𝕜 := ℂ) (φ n) (v n i)) =
              inner (𝕜 := ℂ) (φ n) (v n i) := by
          simpa [mul_assoc] using
            (inv_mul_cancel_left₀ hyneg (inner (𝕜 := ℂ) (φ n) (v n i)))
        exact hcancel.symm.trans hmul
      have hsolve :
          inner (𝕜 := ℂ) (φ n) (v n i) =
            (-(1 / (y n i : ℂ))) *
              ∫ t, (1 / ((t : ℂ) - (1 / (y n i : ℂ)))) ∂(μn n) := by
        simpa [div_eq_mul_inv, inv_neg, mul_assoc] using htmp
      simpa [hinner0_i] using hsolve
    have hk_real :
        (loewnerKernel f (y n i) 0 : ℂ) = ((f (y n i) - f 0) / (y n i) : ℂ) := by
      have hk : loewnerKernel f (y n i) 0 = (f (y n i) - f 0) / (y n i) :=
        loewnerKernel_zero_right (f := f) (x := y n i) hyi
      simpa using congrArg (fun r : ℝ => (r : ℂ)) hk
    -- Now solve for `f (y i)` using the scalar identity.
    have hdiff :
        (f (y n i) - f 0 : ℂ) =
          -∫ t, (1 / ((t : ℂ) - (1 / (y n i : ℂ)))) ∂(μn n) := by
      have hk_int' : ((f (y n i) - f 0) / (y n i) : ℂ) =
          (-(1 / (y n i : ℂ))) *
            ∫ t, (1 / ((t : ℂ) - (1 / (y n i : ℂ)))) ∂(μn n) := by
        simpa [hk_real] using hk_int
      have := congrArg (fun w : ℂ => (y n i : ℂ) * w) hk_int'
      simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv, hyiC] using this
    have hsub :
        (f (y n i) : ℂ) - (f 0 : ℂ) =
          -∫ t, (1 / ((t : ℂ) - (1 / (y n i : ℂ)))) ∂(μn n) := by
      simpa [sub_eq_add_neg] using hdiff
    have := congrArg (fun w : ℂ => (f 0 : ℂ) + w) hsub
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  have hIntAll :
      ∀ n : ℕ, ∀ x : ℝ, Integrable (fun t : ℝ => oneSubMulKernelC x t) (μn n) := by
    intro n x
    simpa [μn] using
      integrable_oneSubMulKernelC_diracMeasure_of_isSymmetric (T := A n) (hT := hSym n) (φ := φ n)
        (x := x)
  rcases hmass_bound with ⟨M0, hM0, hμle⟩
  exact ⟨⟨⟨⟨μn, M0, hM0, hμle, hμ_univ, hPick⟩, hEval⟩, hIntAll⟩⟩

theorem chk_priv_1 :
    ∀ (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ),
      (∀ n : ℕ, pointsHyp (n := n) (y n)) →
        (∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef) →
          Nonempty (Loewner.RawEvalInvKernelIntegrablePackage f y) :=
  exists_measureSeq_core_of_loewnerMatrix_posDef_with_eval_at_inv

/-- Add inverse-point finite evaluation identities to the finite-measure sequence package. -/
theorem exists_measureSeq_of_loewnerMatrix_posDef_with_eval_at_inv
    (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hy : ∀ n : ℕ, pointsHyp (n := n) (y n))
    (hL : ∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef) :
    Nonempty (Loewner.RawEvalInvPackage f y) := by
  classical
  rcases
      exists_measureSeq_core_of_loewnerMatrix_posDef_with_eval_at_inv (f := f) (y := y) hy hL with
    ⟨p⟩
  exact ⟨p.toRawEvalInvPackage⟩

end

end Quantum.TraceInequality.Loewner

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set Filter

open scoped UpperHalfPlane
open scoped ComplexOrder
open scoped MatrixOrder

noncomputable section

/-!
Step 57'' (convenience): rewrite the real-point evaluation formula into a `(1 - y * t)`-kernel
form.

This is a purely algebraic rearrangement of the integrand, using Lean's convention `inv 0 = 0`.
-/


private lemma neg_one_div_sub_inv_eq_mul_one_div_one_sub_mul (x t : ℂ) (hx : x ≠ 0) :
    -(1 / (t - (1 / x))) = x * (1 / (1 - x * t)) := by
  have h :=
    neg_inv_mul_one_div_sub_eq_one_div_one_sub_mul (x := x) (t := t) hx
  have : x * ((-(1 / x)) * (1 / (t - (1 / x)))) = x * (1 / (1 - x * t)) := by
    simpa [h] using congrArg (fun z : ℂ => x * z) h
  simpa [mul_assoc, div_eq_mul_inv, hx] using this

private theorem exists_measureSeq_core_of_loewnerMatrix_posDef_with_eval_at_inv_one_sub_mul
    (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hy : ∀ n : ℕ, pointsHyp (n := n) (y n))
    (hL : ∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef) :
    Nonempty (Loewner.RawOneSubMulKernelIntegrablePackage f y) := by
  classical
  rcases
      exists_measureSeq_core_of_loewnerMatrix_posDef_with_eval_at_inv (f := f) (y := y) hy hL with
    ⟨p⟩
  refine ⟨⟨⟨p.toRawEvalInvPackage.toRawMeasureSeqPackage, ?_⟩, p.hKernelIntegrable⟩⟩
  intro n i hi0
  have hyi0 : y n i ≠ 0 := (hy n).2.2.2 i hi0
  have hyiC : (y n i : ℂ) ≠ 0 := by exact_mod_cast hyi0
  have h0 := p.toRawEvalInvPackage.hEvalInv n i hi0
  calc
    (f (y n i) : ℂ) =
        (f 0 : ℂ) + ∫ t, -(1 / ((t : ℂ) - (1 / (y n i : ℂ))))
          ∂(p.toRawEvalInvPackage.toRawMeasureSeqPackage.μn n) := by
          have : (f (y n i) : ℂ) =
              (f 0 : ℂ) +
                -(∫ t, (1 / ((t : ℂ) - (1 / (y n i : ℂ))))
                  ∂(p.toRawEvalInvPackage.toRawMeasureSeqPackage.μn n)) := by
            simpa [sub_eq_add_neg] using h0
          simpa [MeasureTheory.integral_neg] using this
    _ =
        (f 0 : ℂ) +
          ∫ t, (y n i : ℂ) * (1 / (1 - (y n i : ℂ) * (t : ℂ)))
            ∂(p.toRawEvalInvPackage.toRawMeasureSeqPackage.μn n) := by
          refine congrArg (fun z => (f 0 : ℂ) + z) ?_
          refine MeasureTheory.integral_congr_ae ?_
          refine Filter.Eventually.of_forall (fun t => ?_)
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
            neg_one_div_sub_inv_eq_mul_one_div_one_sub_mul (x := (y n i : ℂ))
              (t := (t : ℂ)) hyiC
    _ =
        (f 0 : ℂ) + (y n i : ℂ) *
          ∫ t, (1 / (1 - (y n i : ℂ) * (t : ℂ)))
            ∂(p.toRawEvalInvPackage.toRawMeasureSeqPackage.μn n) := by
          exact congrArg (fun z => (f 0 : ℂ) + z)
            (MeasureTheory.integral_const_mul
              (μ := p.toRawEvalInvPackage.toRawMeasureSeqPackage.μn n) (r := (y n i : ℂ))
              (f := fun t : ℝ => 1 / (1 - (y n i : ℂ) * (t : ℂ))))

theorem chk_priv_2 :
    ∀ (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ),
      (∀ n : ℕ, pointsHyp (n := n) (y n)) →
        (∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef) →
          Nonempty (Loewner.RawOneSubMulKernelIntegrablePackage f y) :=
  exists_measureSeq_core_of_loewnerMatrix_posDef_with_eval_at_inv_one_sub_mul

/-- Rewrite the finite evaluation identities in the `1 - y * t` kernel form. -/
theorem exists_measureSeq_of_loewnerMatrix_posDef_with_eval_at_inv_one_sub_mul
    (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hy : ∀ n : ℕ, pointsHyp (n := n) (y n))
    (hL : ∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef) :
    Nonempty (Loewner.RawOneSubMulPackage f y) := by
  classical
  rcases
      exists_measureSeq_core_of_loewnerMatrix_posDef_with_eval_at_inv_one_sub_mul
        (f := f) (y := y) hy hL with
    ⟨p⟩
  exact ⟨p.toRawOneSubMulPackage⟩

/-- The `1 - y * t` finite-measure package also records kernel integrability. -/
theorem exists_measureSeq_of_loewnerMatrix_posDef_with_eval_at_inv_one_sub_mul_and_kernelIntegrable
    (f : ℝ → ℝ) (y : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hy : ∀ n : ℕ, pointsHyp (n := n) (y n))
    (hL : ∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef) :
    Nonempty (Loewner.RawOneSubMulKernelIntegrablePackage f y) := by
  classical
  simpa using
    exists_measureSeq_core_of_loewnerMatrix_posDef_with_eval_at_inv_one_sub_mul
      (f := f) (y := y) hy hL

end

end Quantum.TraceInequality.Loewner
