import Quantum.TraceInequality.Loewner.Koranyi.InsideMassPackage
import Quantum.TraceInequality.Loewner.Koranyi.FiniteKoranyiInsideMass
import Quantum.TraceInequality.Loewner.Koranyi.SupportElimSubseq
import Quantum.TraceInequality.Loewner.Koranyi.SupportElimAlgebra


namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set Filter

open scoped ComplexOrder
open scoped MatrixOrder
open scoped NNReal
open scoped Topology
open scoped UpperHalfPlane

noncomputable section

/-!
# Producer-side contracts for Chapter 27 Proposition 27.3 packages

This file contains only the first producer-side split for theorem 50.  It does
not construct either package from `GlobalStrictPosDef`; those analytic
producers remain separate frontiers.
-/

/--
Same-witness package without the Chapter 27 Proposition 27.3 inverse-square
input.

This intermediate package separates the witness-retention problem from the
analytic problem of producing the `K, C` bounds in
`SignedAxisSqInvDistInput`.

Proposition 27.3 of [simon2019].
-/
structure StrictApproxSameWitnessPackage (f : ℝ → ℝ)
    extends StrictApproxSignedEvalPackage f where
  stageWitness : ∀ n : ℕ, FiniteResolventWitness f (φ n)
  hμ_eq : ∀ n : ℕ, μn (φ n) = (stageWitness n).diracMeasure

/-- Forget the Prop. 27.3 input field from a full same-witness package.
Proposition 27.3 of [simon2019]. -/
def strictApproxSameWitnessPackage_of_sqInvDistPackage
    {f : ℝ → ℝ} (pkg : StrictApproxSameWitnessSqInvDistPackage f) :
    StrictApproxSameWitnessPackage f where
  toStrictApproxSignedEvalPackage := pkg.toStrictApproxSignedEvalPackage
  stageWitness := pkg.stageWitness
  hμ_eq := pkg.hμ_eq

/--
Assemble the full same-witness Prop. 27.3 package from witness-retention data
and a Chapter 27 Proposition 27.3 input on the same signed-evaluation
projection.

Proposition 27.3 of [simon2019].
-/
def strictApproxSameWitnessSqInvDistPackage_of_witnessPackage_and_input
    {f : ℝ → ℝ} (wpkg : StrictApproxSameWitnessPackage f)
    (hinput :
      SignedAxisSqInvDistInput wpkg.toStrictApproxSignedEvalPackage) :
    StrictApproxSameWitnessSqInvDistPackage f where
  toStrictApproxSignedEvalPackage := wpkg.toStrictApproxSignedEvalPackage
  stageWitness := wpkg.stageWitness
  hμ_eq := wpkg.hμ_eq
  hProp273Input := hinput

/--
Chapter 27 Proposition 27.3-type uniform dyadic-center solution input on the
same witness package.

This is the Lean-side contract for the theorem 51 frontier.  It asks for actual
solutions at the dyadic centers of the same `wpkg.stageWitness`; in Chapter 27
these solutions may come from the range-projection/generalized-inverse argument,
not necessarily from literal spectral separation.  Producing this input from
`GlobalStrictPosDef` while keeping the signed-evaluation witness fixed is the
remaining analytic work.

The radius sequence is recorded as `ℝ≥0` so that the eventual bound has exactly
the shape required by `SignedAxisSqInvDistInput`.

Proposition 27.3 of [simon2019].
-/
structure UniformDyadicSolutionInput {f : ℝ → ℝ}
    (wpkg : StrictApproxSameWitnessPackage f) where
  R : ℕ → ℝ≥0
  C : ℝ≥0
  hR_bound : ∀ᶠ n in atTop, R n ^ (2 : ℕ) ≤ C
  hsol :
    ∀ n : ℕ, ∀ i : Fin (nonzeroInteriorDyadicPointCount (wpkg.φ n) + 1),
      ∃ δ : (wpkg.stageWitness n).H,
        ((wpkg.stageWitness n).T -
            (zeroAnchoredDyadicPointFamily (wpkg.φ n) i : ℂ) •
              (LinearMap.id :
                (wpkg.stageWitness n).H →ₗ[ℂ] (wpkg.stageWitness n).H)) δ =
          (wpkg.stageWitness n).φ ∧
            ‖δ‖ ≤ (R n : ℝ)

/--
The uniform dyadic-center solution input gives the Prop. 27.3 inverse-square
input on the same signed-evaluation backbone.

Proposition 27.3 of [simon2019].
-/
def signedAxisSqInvDistInput_of_uniformDyadicSolutionInput
    {f : ℝ → ℝ} {wpkg : StrictApproxSameWitnessPackage f}
    (hinput : UniformDyadicSolutionInput wpkg) :
    SignedAxisSqInvDistInput wpkg.toStrictApproxSignedEvalPackage := by
  classical
  refine
    { K := fun n => hinput.R n ^ (2 : ℕ)
      C := hinput.C
      hK_bound := ?_
      hK_le := hinput.hR_bound }
  intro n i
  let W := wpkg.stageWitness n
  have hR_nonneg : 0 ≤ (hinput.R n : ℝ) := by
    exact_mod_cast (hinput.R n).2
  have hstage :
      ∀ i : Fin (nonzeroInteriorDyadicPointCount (wpkg.φ n) + 1),
        (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist
              (zeroAnchoredDyadicPointFamily (wpkg.φ n) i) y
            ∂(_root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric
              (T := W.T) (hT := W.hT) W.φ)) ≤
          ENNReal.ofReal ((hinput.R n : ℝ) ^ (2 : ℕ)) :=
    finiteKoranyi_stagewiseSqInvDistBound_standalone
      (T := W.T) (hT := W.hT) (φ := W.φ) (m := wpkg.φ n)
      (R := (hinput.R n : ℝ)) hR_nonneg (hinput.hsol n)
  rw [wpkg.hμ_eq n]
  simpa [W, FiniteResolventWitness.diracMeasure] using hstage i


/--
Build a signed-evaluation package together with same-witness Chapter 27
finite-stage witnesses.

This is the witness-retention part of theorem 50.  It deliberately replays the
finite Koranyi construction instead of recovering witnesses from an already
chosen `StrictApproxSignedEvalPackage`.

Proposition 27.3 of [simon2019].
-/
theorem exists_strictApproxSignedEvalPackage_with_sameWitness_of_globalStrictPosDef
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) :
    ∃ pkg : StrictApproxSignedEvalPackage f,
      ∃ stageWitness : ∀ n : ℕ, FiniteResolventWitness f (pkg.φ n),
        ∀ n : ℕ, pkg.μn (pkg.φ n) = (stageWitness n).diracMeasure := by
  classical
  let y : ∀ n : ℕ, Fin (n + 1) → ℝ := signedPoints
  have hy : ∀ n : ℕ, pointsHyp (n := n) (y n) := by
    intro n
    simpa [y] using pointsHyp_signedPoints (n := n)
  have hL : ∀ n : ℕ, (loewnerMatrix (n := n) f (y n)).PosDef := by
    intro n
    exact h n (y n) (hy n)
  have hex :
      ∀ n : ℕ,
        ∃ (H : Type) (_ : NormedAddCommGroup H)
          (_ : InnerProductSpace ℂ H) (_ : FiniteDimensional ℂ H),
          ∃ (v : Fin (n + 1) → H) (φ : H) (A : H →ₗ[ℂ] H)
            (hA : IsSelfAdjoint A),
            (∀ i j : Fin (n + 1),
                inner (𝕜 := ℂ) (v i) (v j) =
                  (loewnerKernel f (y n i) (y n j) : ℂ)) ∧
              φ = v 0 ∧
                (∀ i, i ≠ 0 → (v i - (y n i : ℂ) • A (v i)) = φ) ∧
                  let hSym : A.IsSymmetric :=
                    (LinearMap.isSymmetric_iff_isSelfAdjoint A).2 hA
                  let μ : Measure ℝ :=
                    _root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric
                      (T := A) (hT := hSym) φ
                  (∀ i, i ≠ 0 →
                    inner (𝕜 := ℂ) φ ((-(y n i : ℂ)) • v i) =
                      ∫ t, (1 / ((t : ℂ) - (1 / (y n i : ℂ)))) ∂μ) := fun n =>
    _root_.Quantum.TraceInequality.Loewner.koranyi_finite_construct_inner_v_eq_integral_at_inv_dirac
        (n := n) (f := f) (y := y n) (hy := hy n) (hL := hL n)
  choose H instH instI instFD v φ A hA hGram hφ hEq hI using hex
  let hSym : ∀ n : ℕ, (A n).IsSymmetric :=
    fun n => (LinearMap.isSymmetric_iff_isSelfAdjoint (A n)).2 (hA n)
  let W : ∀ n : ℕ, FiniteResolventWitness f n :=
    fun n =>
      { H := H n
        instNormedAddCommGroup := instH n
        instInnerProductSpace := instI n
        instFiniteDimensional := instFD n
        T := A n
        hT := hSym n
        φ := φ n }
  let μn : ℕ → Measure ℝ := fun n => (W n).diracMeasure
  have hμ_eq_raw : ∀ n : ℕ, μn n = (W n).diracMeasure := by
    intro n
    rfl
  have hMass : ∀ n : ℕ, μn n Set.univ = ENNReal.ofReal (loewnerKernel f 0 0) := by
    intro n
    have hy0 : y n 0 = 0 := (hy n).1
    have hmass :
        μn n Set.univ = ENNReal.ofReal (‖φ n‖ ^ 2) := by
      simpa [μn, W, FiniteResolventWitness.diracMeasure] using
        _root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric_univ
          (T := A n) (hT := hSym n) (φ := φ n)
    have hnorm_sq : ‖φ n‖ ^ 2 = loewnerKernel f 0 0 := by
      have hinner :
          inner (𝕜 := ℂ) (φ n) (φ n) = (loewnerKernel f 0 0 : ℂ) := by
        simpa [hφ n, hy0] using (hGram n 0 0)
      have hre : (inner (𝕜 := ℂ) (φ n) (φ n)).re = loewnerKernel f 0 0 := by
        simpa using congrArg Complex.re hinner
      have hnorm : (inner (𝕜 := ℂ) (φ n) (φ n)).re = ‖φ n‖ ^ 2 := by
        simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (x := φ n))
      exact hnorm.symm.trans hre
    simpa [hnorm_sq] using hmass
  let M0 : ENNReal := ENNReal.ofReal (loewnerKernel f 0 0)
  have hM0 : M0 < ⊤ := by
    simp [M0]
  have hμle : ∀ n : ℕ, μn n Set.univ ≤ M0 := by
    intro n
    simp [M0, hMass n]
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
      simpa [μn, W, FiniteResolventWitness.diracMeasure] using
        inner_solution_eq_integral_dirac_of_isSymmetric_im_nonneg_forall
          (T := A n) (hT := hSym n) (φ := φ n) z hz
    exact
      _root_.Quantum.TraceInequality.Loewner.stieltjes_im_nonneg_of_pick_data
        (A := A n) (φ := φ n) (μ := μn n) hStep3 z
  have hEvalRaw :
      ∀ n : ℕ,
        ∀ i : Fin (n + 1),
          i ≠ 0 →
            (loewnerKernel f (y n i) 0 : ℂ) =
              ∫ t, (1 / (1 - (y n i : ℂ) * (t : ℂ))) ∂(μn n) := by
    intro n i hi0
    have hy0 : y n 0 = 0 := (hy n).1
    have hyi : y n i ≠ 0 := (hy n).2.2.2 i hi0
    have hyiC : (y n i : ℂ) ≠ 0 := by exact_mod_cast hyi
    have hinner_i0 :
        inner (𝕜 := ℂ) (v n i) (φ n) =
          (loewnerKernel f (y n i) 0 : ℂ) := by
      simpa [hφ n, hy0] using (hGram n i 0)
    have hinner0_i :
        inner (𝕜 := ℂ) (φ n) (v n i) =
          (loewnerKernel f (y n i) 0 : ℂ) := by
      have hconj :
          star (inner (𝕜 := ℂ) (v n i) (φ n)) =
            inner (𝕜 := ℂ) (φ n) (v n i) := by
        simp
      calc
        inner (𝕜 := ℂ) (φ n) (v n i) =
            star (inner (𝕜 := ℂ) (v n i) (φ n)) := by
          simp
        _ = (loewnerKernel f (y n i) 0 : ℂ) := by
          simp [hinner_i0]
    have hI' :
        inner (𝕜 := ℂ) (φ n) ((-(y n i : ℂ)) • v n i) =
          ∫ t, (1 / ((t : ℂ) - (1 / (y n i : ℂ)))) ∂(μn n) := by
      simpa [μn, W, FiniteResolventWitness.diracMeasure] using (hI n i hi0)
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
            (-(y n i : ℂ))⁻¹ *
                (-(y n i : ℂ) * inner (𝕜 := ℂ) (φ n) (v n i)) =
              (-(y n i : ℂ))⁻¹ *
                ∫ t, (1 / ((t : ℂ) - (1 / (y n i : ℂ)))) ∂(μn n) := by
          simpa [mul_assoc] using congrArg (fun w => (-(y n i : ℂ))⁻¹ * w) hlin'
        have hcancel :
            (-(y n i : ℂ))⁻¹ *
                (-(y n i : ℂ) * inner (𝕜 := ℂ) (φ n) (v n i)) =
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
    calc
      (loewnerKernel f (y n i) 0 : ℂ) =
          (-(1 / (y n i : ℂ))) *
            ∫ t, (1 / ((t : ℂ) - (1 / (y n i : ℂ)))) ∂(μn n) := hk_int
      _ = ∫ t, (-(1 / (y n i : ℂ))) *
            (1 / ((t : ℂ) - (1 / (y n i : ℂ)))) ∂(μn n) := by
          simpa using
            (MeasureTheory.integral_const_mul (μ := μn n) (r := (-(1 / (y n i : ℂ))))
              (f := fun t : ℝ => (1 / ((t : ℂ) - (1 / (y n i : ℂ)))))).symm
      _ = ∫ t, (1 / (1 - (y n i : ℂ) * (t : ℂ))) ∂(μn n) := by
          refine MeasureTheory.integral_congr_ae ?_
          refine MeasureTheory.ae_of_all _ (fun t => ?_)
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            neg_inv_mul_one_div_sub_eq_one_div_one_sub_mul
              (x := (y n i : ℂ)) (t := (t : ℂ)) hyiC
  have hIntAll :
      ∀ n : ℕ, ∀ x : ℝ, Integrable (fun t : ℝ => oneSubMulKernelC x t) (μn n) := by
    intro n x
    simpa [μn, W, FiniteResolventWitness.diracMeasure] using
      _root_.Quantum.TraceInequality.Loewner.integrable_oneSubMulKernelC_diracMeasure_of_isSymmetric
        (T := A n) (hT := hSym n) (φ := φ n) (x := x)
  rcases
    _root_.Quantum.TraceInequality.Loewner.exists_subseq_supportElim_stieltjesDiff_full_with_tendsto
        (μn := μn) (M0 := M0) hM0 hμle with
    ⟨φsub, F, ν, hφsub, hconvSt, hconvDiff, hst, hdiff, hFpick, ht, hKoranyi⟩
  let pkg : StrictApproxSignedEvalPackage f :=
    { μn := μn
      M0 := M0
      hM0 := hM0
      hμle := hμle
      hMass := hMass
      φ := φsub
      hφ := hφsub
      F := F
      ν := ν
      hStieltjes := hconvSt
      hPick := hFpick
      hCayleyWeak := ht
      hKoranyi := hKoranyi
      hKernelIntegrableSubseq := fun n x => hIntAll (φsub n) x
      hEvalSigned := by
        intro n i hi0
        simpa [y] using hEvalRaw (φsub n) i hi0 }
  refine ⟨pkg, ?_⟩
  refine ⟨fun n => W (φsub n), ?_⟩
  intro n
  exact hμ_eq_raw (φsub n)

/--
Producer for theorem 50: retain the finite-stage Prop. 27.3 witness along the
canonical signed-evaluation backbone.

Proposition 27.3 of [simon2019].
-/
noncomputable def strictApproxSameWitnessPackage_of_globalStrictPosDef
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f) :
    StrictApproxSameWitnessPackage f := by
  classical
  let hex := exists_strictApproxSignedEvalPackage_with_sameWitness_of_globalStrictPosDef h
  let pkg := Classical.choose hex
  let h1 := Classical.choose_spec hex
  let stageWitness := Classical.choose h1
  let hμ_eq := Classical.choose_spec h1
  exact
    { toStrictApproxSignedEvalPackage := pkg
      stageWitness := stageWitness
      hμ_eq := hμ_eq }

end

end Quantum.TraceInequality.Loewner
