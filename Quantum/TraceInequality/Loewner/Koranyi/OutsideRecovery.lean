import Quantum.TraceInequality.Loewner.Koranyi.FiniteResolventWitness
import Quantum.TraceInequality.Loewner.Koranyi.InsideMass
import Quantum.TraceInequality.Loewner.Koranyi.DiracMeasureMass
import Quantum.TraceInequality.Loewner.Koranyi.StieltjesSolvable
import Quantum.TraceInequality.Loewner.Koranyi.SupportElimAlgebra
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Restrict

namespace Quantum.TraceInequality.Loewner

open Filter MeasureTheory

open scoped Topology
open scoped NNReal
open scoped ComplexOrder
open scoped MatrixOrder

noncomputable section

/-!
# Book-route outside recovery setup for Chapter 27 Proposition 27.4

This file starts the Chapter 27 Proposition 27.4 book route.  It fixes the
outside restriction of the Prop. 27.3 measure and the associated Stieltjes
transforms, and proves the two entry estimates needed before the later
Schwarz-error bound and derivative-identification layer.
-/

namespace FiniteResolventWitness

variable {f : ℝ → ℝ} {m : ℕ}

private theorem integrable_bookStieltjesKernel
    (W : FiniteResolventWitness f m) (x : ℝ) :
    Integrable (fun y : ℝ => 1 / ((y : ℂ) - (x : ℂ))) W.diracMeasure := by
  classical
  let n : ℕ := Module.finrank ℂ W.H
  have hn : Module.finrank ℂ W.H = n := rfl
  let b : OrthonormalBasis (Fin n) ℂ W.H := W.hT.eigenvectorBasis (n := n) (hn := hn)
  let eig : Fin n → ℝ := W.hT.eigenvalues (n := n) (hn := hn)
  let cVec : EuclideanSpace ℂ (Fin n) := b.repr W.φ
  let c : Fin n → ℂ := fun i => cVec.ofLp i
  let μi : Fin n → Measure ℝ :=
    fun i => (ENNReal.ofReal (Complex.normSq (c i))) • Measure.dirac (eig i)
  have hμ :
      W.diracMeasure = ∑ i : Fin n, μi i := by
    simp [FiniteResolventWitness.diracMeasure,
      _root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric,
      _root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetricAux,
      μi, c, cVec, eig, b, n]
  rw [hμ]
  exact
    (MeasureTheory.integrable_finset_sum_measure
      (μ := μi) (s := (Finset.univ : Finset (Fin n)))
      (f := fun y : ℝ => 1 / ((y : ℂ) - (x : ℂ)))).2
      (by
        intro i _hi
        have hdir :
            Integrable (fun y : ℝ => 1 / ((y : ℂ) - (x : ℂ)))
              (Measure.dirac (eig i)) :=
          MeasureTheory.integrable_dirac (a := eig i)
            (f := fun y : ℝ => 1 / ((y : ℂ) - (x : ℂ))) (by simp)
        simpa [μi] using hdir.smul_measure ENNReal.ofReal_ne_top)

private theorem diracMeasure_isFiniteMeasure
    (W : FiniteResolventWitness f m) :
    IsFiniteMeasure W.diracMeasure := by
  constructor
  have hmass :=
    _root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric_univ
      (T := W.T) (hT := W.hT) (φ := W.φ)
  have hlt : ENNReal.ofReal (‖W.φ‖ ^ 2) < ⊤ := ENNReal.ofReal_lt_top
  simpa [FiniteResolventWitness.diracMeasure] using hmass.trans_lt hlt

end FiniteResolventWitness

namespace AugmentedLoewnerLocalConstruction

variable {f : ℝ → ℝ} {m : ℕ}

/-- The Chapter 27 outside restriction `μ_m | (ℝ \ [-1,1])`. -/
def bookOutsideMeasure (C : AugmentedLoewnerLocalConstruction f m) : Measure ℝ :=
  C.toFiniteWitness.diracMeasure.restrict (Set.Icc (-1 : ℝ) 1)ᶜ

/-- The Chapter 27 inside restriction `μ_m | [-1,1]`. -/
def bookInsideMeasure (C : AugmentedLoewnerLocalConstruction f m) : Measure ℝ :=
  C.toFiniteWitness.diracMeasure.restrict (Set.Icc (-1 : ℝ) 1)

/-- The full Stieltjes transform attached to the Chapter 27 finite measure. -/
def bookStieltjes (C : AugmentedLoewnerLocalConstruction f m) (x : ℝ) : ℂ :=
  ∫ y, (1 / ((y : ℂ) - (x : ℂ))) ∂(C.toFiniteWitness.diracMeasure)

/-- The outside Stieltjes transform from Proposition 27.4. -/
def bookOutsideStieltjes (C : AugmentedLoewnerLocalConstruction f m) (x : ℝ) : ℂ :=
  ∫ y, (1 / ((y : ℂ) - (x : ℂ))) ∂(C.bookOutsideMeasure)

/-- The real-valued outside Stieltjes transform from Proposition 27.4. -/
def bookOutsideStieltjesReal (C : AugmentedLoewnerLocalConstruction f m) (x : ℝ) : ℝ :=
  ∫ y, (1 / (y - x)) ∂(C.bookOutsideMeasure)

/-- The inside Stieltjes contribution removed in Proposition 27.4. -/
def bookInsideStieltjes (C : AugmentedLoewnerLocalConstruction f m) (x : ℝ) : ℂ :=
  ∫ y, (1 / ((y : ℂ) - (x : ℂ))) ∂(C.bookInsideMeasure)

private theorem realKernel_ofReal_eq_complexKernel (x y : ℝ) :
    ((1 / (y - x) : ℝ) : ℂ) = 1 / ((y : ℂ) - (x : ℂ)) := by
  simp [one_div, Complex.ofReal_inv, Complex.ofReal_sub]

private theorem complexKernel_re_eq_realKernel (x y : ℝ) :
    (((1 / ((y : ℂ) - (x : ℂ))) : ℂ).re) = 1 / (y - x) := by
  exact (congrArg Complex.re (realKernel_ofReal_eq_complexKernel x y)).symm

/-- The real outside Stieltjes kernel is integrable against the outside restriction. -/
theorem integrable_bookOutsideStieltjesKernelReal
    (C : AugmentedLoewnerLocalConstruction f m) (x : ℝ) :
    Integrable (fun y : ℝ => 1 / (y - x)) C.bookOutsideMeasure := by
  have hFull :
      Integrable (fun y : ℝ => 1 / ((y : ℂ) - (x : ℂ)))
        C.toFiniteWitness.diracMeasure :=
    C.toFiniteWitness.integrable_bookStieltjesKernel x
  have hComplex :
      Integrable (fun y : ℝ => 1 / ((y : ℂ) - (x : ℂ))) C.bookOutsideMeasure := by
    simpa [bookOutsideMeasure] using
      hFull.mono_measure Measure.restrict_le_self
  convert hComplex.re using 1
  ext y
  exact (complexKernel_re_eq_realKernel x y).symm

private theorem bookOutsideMeasure_isFiniteMeasure
    (C : AugmentedLoewnerLocalConstruction f m) :
    IsFiniteMeasure C.bookOutsideMeasure := by
  haveI : IsFiniteMeasure C.toFiniteWitness.diracMeasure :=
    C.toFiniteWitness.diracMeasure_isFiniteMeasure
  exact isFiniteMeasure_of_le C.toFiniteWitness.diracMeasure (by
    simpa [bookOutsideMeasure] using
      (Measure.restrict_le_self (μ := C.toFiniteWitness.diracMeasure)
        (s := (Set.Icc (-1 : ℝ) 1)ᶜ)))

/-- The outside restriction is supported on the complement of `[-1,1]`. -/
theorem ae_bookOutsideMeasure_mem_Icc_compl
    (C : AugmentedLoewnerLocalConstruction f m) :
    ∀ᵐ y ∂C.bookOutsideMeasure, y ∈ (Set.Icc (-1 : ℝ) 1)ᶜ := by
  simpa [bookOutsideMeasure] using
    (ae_restrict_mem (μ := C.toFiniteWitness.diracMeasure)
      (s := (Set.Icc (-1 : ℝ) 1)ᶜ) isClosed_Icc.measurableSet.compl)

/-- The real Stieltjes transform is the real form of the complex one. -/
theorem bookOutsideStieltjesReal_ofReal_eq_bookOutsideStieltjes
    (C : AugmentedLoewnerLocalConstruction f m) (x : ℝ) :
    (C.bookOutsideStieltjesReal x : ℂ) = C.bookOutsideStieltjes x := by
  calc
    (C.bookOutsideStieltjesReal x : ℂ) =
        ∫ y, ((1 / (y - x) : ℝ) : ℂ) ∂(C.bookOutsideMeasure) := by
          simpa [bookOutsideStieltjesReal] using
            (integral_complex_ofReal
              (μ := C.bookOutsideMeasure) (f := fun y : ℝ => 1 / (y - x))).symm
    _ = C.bookOutsideStieltjes x := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun y => by
            exact realKernel_ofReal_eq_complexKernel x y

/-- The outside and inside restrictions split the full Chapter 27 measure. -/
theorem bookOutside_add_insideMeasure
    (C : AugmentedLoewnerLocalConstruction f m) :
    C.bookOutsideMeasure + C.bookInsideMeasure =
      C.toFiniteWitness.diracMeasure := by
  simp [bookOutsideMeasure, bookInsideMeasure,
    MeasureTheory.Measure.restrict_compl_add_restrict
      (μ := C.toFiniteWitness.diracMeasure) (s := Set.Icc (-1 : ℝ) 1)
      isClosed_Icc.measurableSet]

/-- The inside restriction has total mass equal to the full measure of `[-1,1]`. -/
theorem bookInsideMeasure_univ_eq
    (C : AugmentedLoewnerLocalConstruction f m) :
    C.bookInsideMeasure Set.univ =
      C.toFiniteWitness.diracMeasure (Set.Icc (-1 : ℝ) 1) := by
  simp [bookInsideMeasure]

/-- The full Chapter 27 Stieltjes transform recovers `f` on the dyadic grid. -/
theorem bookStieltjes_eq_f_on_dyadic
    (C : AugmentedLoewnerLocalConstruction f m)
    (i : Fin (nonzeroInteriorDyadicPointCount m + 1)) :
    C.bookStieltjes (zeroAnchoredDyadicPointFamily m i) =
      (f (zeroAnchoredDyadicPointFamily m i) : ℂ) := by
  let idx := augmentedBackboneDyadicIndex m i
  have hpoint :
      augmentedBackbonePointFamily m idx = zeroAnchoredDyadicPointFamily m i :=
    augmentedBackbonePointFamily_dyadicIndex m i
  have hsol :
      (C.A - (zeroAnchoredDyadicPointFamily m i : ℂ) •
          (LinearMap.id : C.H →ₗ[ℂ] C.H)) (C.v idx) = C.φ := by
    simpa [idx, hpoint] using C.hSolution idx
  have hIntegral :
      inner (𝕜 := ℂ) C.φ (C.v idx) =
        ∫ y, (1 / ((y : ℂ) - (zeroAnchoredDyadicPointFamily m i : ℂ)))
          ∂(C.toFiniteWitness.diracMeasure) := by
    have hstep :=
      Quantum.TraceInequality.Loewner.inner_solution_eq_integral_dirac_of_isSymmetric_of_exists
        (T := C.A) (hT := C.hA_symm) (φ := C.φ)
        (z := (zeroAnchoredDyadicPointFamily m i : ℂ))
        (hex := ⟨C.v idx, hsol⟩) (C.v idx) hsol
    simpa [FiniteResolventWitness.diracMeasure, AugmentedLoewnerLocalConstruction.toFiniteWitness]
      using hstep
  have hinner :
      inner (𝕜 := ℂ) C.φ (C.v idx) = (f (zeroAnchoredDyadicPointFamily m i) : ℂ) := by
    have hconj :
        star (inner (𝕜 := ℂ) (C.v idx) C.φ) =
          inner (𝕜 := ℂ) C.φ (C.v idx) := by
      simp
    calc
      inner (𝕜 := ℂ) C.φ (C.v idx) =
          star (inner (𝕜 := ℂ) (C.v idx) C.φ) := hconj.symm
      _ = (f (zeroAnchoredDyadicPointFamily m i) : ℂ) := by
            simp [C.hPhi idx, hpoint]
  exact hIntegral.symm.trans hinner

/-- The inside restriction inherits the dyadic inverse-square estimate. -/
theorem bookInside_sqInvDist_le_deriv
    (C : AugmentedLoewnerLocalConstruction f m)
    (i : Fin (nonzeroInteriorDyadicPointCount m + 1)) :
    (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist (zeroAnchoredDyadicPointFamily m i) y
        ∂(C.bookInsideMeasure)) ≤
      ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) := by
  have hmono :
      (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist (zeroAnchoredDyadicPointFamily m i) y
          ∂(C.bookInsideMeasure)) ≤
        ∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist (zeroAnchoredDyadicPointFamily m i) y
          ∂(C.toFiniteWitness.diracMeasure) := by
    simpa [bookInsideMeasure] using
      (lintegral_mono' (μ := C.bookInsideMeasure)
        (ν := C.toFiniteWitness.diracMeasure) Measure.restrict_le_self
        (fun _ => le_rfl))
  exact hmono.trans (C.dyadic_sqInvDist_le_deriv i)

/--
On the dyadic grid, the full Stieltjes transform is the sum of its outside and
inside restrictions.
-/
theorem bookStieltjes_eq_outside_add_inside_on_dyadic
    (C : AugmentedLoewnerLocalConstruction f m)
    (i : Fin (nonzeroInteriorDyadicPointCount m + 1)) :
    C.bookStieltjes (zeroAnchoredDyadicPointFamily m i) =
      C.bookOutsideStieltjes (zeroAnchoredDyadicPointFamily m i) +
        C.bookInsideStieltjes (zeroAnchoredDyadicPointFamily m i) := by
  let x := zeroAnchoredDyadicPointFamily m i
  have hFull :
      Integrable (fun y : ℝ => 1 / ((y : ℂ) - (x : ℂ)))
        C.toFiniteWitness.diracMeasure :=
    C.toFiniteWitness.integrable_bookStieltjesKernel x
  have hOutside :
      Integrable (fun y : ℝ => 1 / ((y : ℂ) - (x : ℂ))) C.bookOutsideMeasure := by
    simpa [bookOutsideMeasure] using
      hFull.mono_measure Measure.restrict_le_self
  have hInside :
      Integrable (fun y : ℝ => 1 / ((y : ℂ) - (x : ℂ))) C.bookInsideMeasure := by
    simpa [bookInsideMeasure] using
      hFull.mono_measure Measure.restrict_le_self
  calc
    C.bookStieltjes x =
        ∫ y, (1 / ((y : ℂ) - (x : ℂ))) ∂(C.toFiniteWitness.diracMeasure) := by
          rfl
    _ = ∫ y, (1 / ((y : ℂ) - (x : ℂ))) ∂(C.bookOutsideMeasure + C.bookInsideMeasure) := by
          rw [C.bookOutside_add_insideMeasure]
    _ = C.bookOutsideStieltjes x + C.bookInsideStieltjes x := by
          simpa [bookOutsideStieltjes, bookInsideStieltjes] using
            (MeasureTheory.integral_add_measure
              (μ := C.bookOutsideMeasure) (ν := C.bookInsideMeasure)
              (f := fun y : ℝ => 1 / ((y : ℂ) - (x : ℂ))) hOutside hInside)

/--
On the dyadic grid, replacing the full Stieltjes transform by the outside
restriction leaves exactly the negative inside contribution.
-/
theorem bookOutsideStieltjes_sub_f_eq_neg_inside_on_dyadic
    (C : AugmentedLoewnerLocalConstruction f m)
    (i : Fin (nonzeroInteriorDyadicPointCount m + 1)) :
    C.bookOutsideStieltjes (zeroAnchoredDyadicPointFamily m i) -
        (f (zeroAnchoredDyadicPointFamily m i) : ℂ) =
      -C.bookInsideStieltjes (zeroAnchoredDyadicPointFamily m i) := by
  let x := zeroAnchoredDyadicPointFamily m i
  have hsplit := C.bookStieltjes_eq_outside_add_inside_on_dyadic i
  have hfull := C.bookStieltjes_eq_f_on_dyadic i
  calc
    C.bookOutsideStieltjes x - (f x : ℂ) =
        C.bookOutsideStieltjes x - C.bookStieltjes x := by rw [hfull]
    _ = -C.bookInsideStieltjes x := by
          rw [hsplit]
          abel

private theorem stieltjesKernel_enorm_le_sqInvDist_rpow (x y : ℝ) :
    ‖(1 / ((y : ℂ) - (x : ℂ)))‖ₑ ≤
      (Quantum.TraceInequality.Loewner.sqInvDist x y) ^ (1 / 2 : ℝ) := by
  by_cases hxy : y = x
  · subst y
    simp [Quantum.TraceInequality.Loewner.sqInvDist]
  · have hnonzero : (y : ℂ) - (x : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr hxy
    have hnorm :
        ‖(y : ℂ) - (x : ℂ)‖ₑ = ENNReal.ofReal (abs (y - x)) := by
      have hnormReal : ‖(y : ℂ) - (x : ℂ)‖ = abs (y - x) := by
        simpa [Complex.ofReal_sub, Real.norm_eq_abs] using (Complex.norm_real (y - x))
      rw [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq]
      simp [coe_nnnorm, hnormReal]
    exact le_of_eq (by
      have hSqRoot :
          (ENNReal.ofReal (abs (y - x)))⁻¹ =
            (((ENNReal.ofReal (abs (y - x)))⁻¹) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
      have hSqDef :
          Quantum.TraceInequality.Loewner.sqInvDist x y =
            ((ENNReal.ofReal (abs (y - x)))⁻¹) ^ (2 : ℕ) := by
        simp only [Quantum.TraceInequality.Loewner.sqInvDist]
      calc
        ‖(1 / ((y : ℂ) - (x : ℂ)))‖ₑ =
            (ENNReal.ofReal (abs (y - x)))⁻¹ := by
              rw [one_div, enorm_inv hnonzero, hnorm]
        _ = (((ENNReal.ofReal (abs (y - x)))⁻¹) ^ (2 : ℕ)) ^
              (1 / 2 : ℝ) := hSqRoot
        _ = (Quantum.TraceInequality.Loewner.sqInvDist x y) ^ (1 / 2 : ℝ) := by
              rw [hSqDef])

/--
Cauchy-Schwarz core for the inside Stieltjes contribution, in the `ENNReal`
form used by the dyadic Proposition 27.4 error estimate.
-/
theorem bookInsideStieltjes_norm_le_sqrt_sqInvDist_mul_mass
    (C : AugmentedLoewnerLocalConstruction f m)
    (i : Fin (nonzeroInteriorDyadicPointCount m + 1)) :
    ‖C.bookInsideStieltjes (zeroAnchoredDyadicPointFamily m i)‖ₑ ≤
      ((∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist (zeroAnchoredDyadicPointFamily m i) y
          ∂(C.bookInsideMeasure)) * C.bookInsideMeasure Set.univ) ^ (1 / 2 : ℝ) := by
  let x := zeroAnchoredDyadicPointFamily m i
  have hIntegral :=
    MeasureTheory.enorm_integral_le_lintegral_enorm
      (μ := C.bookInsideMeasure) (fun y : ℝ => (1 / ((y : ℂ) - (x : ℂ))))
  have hPoint :
      (∫⁻ y, ‖(1 / ((y : ℂ) - (x : ℂ)))‖ₑ ∂(C.bookInsideMeasure)) ≤
        ∫⁻ y, (Quantum.TraceInequality.Loewner.sqInvDist x y) ^ (1 / 2 : ℝ)
          ∂(C.bookInsideMeasure) :=
    lintegral_mono (fun y => stieltjesKernel_enorm_le_sqInvDist_rpow x y)
  have hMeas :
      Measurable (fun y : ℝ => Quantum.TraceInequality.Loewner.sqInvDist x y) := by
    unfold Quantum.TraceInequality.Loewner.sqInvDist
    measurability
  have hHolder :
      (∫⁻ y, (Quantum.TraceInequality.Loewner.sqInvDist x y) ^ (1 / 2 : ℝ)
          ∂(C.bookInsideMeasure)) ≤
        (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist x y ∂(C.bookInsideMeasure)) ^
            (1 / 2 : ℝ) *
          (C.bookInsideMeasure Set.univ) ^ (1 / 2 : ℝ) := by
    have h := ENNReal.lintegral_mul_norm_pow_le
      (μ := C.bookInsideMeasure)
      (f := fun y : ℝ => Quantum.TraceInequality.Loewner.sqInvDist x y)
      (g := fun _y : ℝ => (1 : ENNReal))
      hMeas.aemeasurable measurable_const.aemeasurable
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1)
    simpa [ENNReal.one_rpow] using h
  calc
    ‖C.bookInsideStieltjes x‖ₑ =
        ‖∫ y, (1 / ((y : ℂ) - (x : ℂ))) ∂(C.bookInsideMeasure)‖ₑ := by
          rfl
    _ ≤ ∫⁻ y, ‖(1 / ((y : ℂ) - (x : ℂ)))‖ₑ ∂(C.bookInsideMeasure) :=
          hIntegral
    _ ≤ ∫⁻ y, (Quantum.TraceInequality.Loewner.sqInvDist x y) ^ (1 / 2 : ℝ)
          ∂(C.bookInsideMeasure) := hPoint
    _ ≤ (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist x y ∂(C.bookInsideMeasure)) ^
          (1 / 2 : ℝ) *
          (C.bookInsideMeasure Set.univ) ^ (1 / 2 : ℝ) := hHolder
    _ = ((∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist x y ∂(C.bookInsideMeasure)) *
          C.bookInsideMeasure Set.univ) ^ (1 / 2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg]
          norm_num

/--
Dyadic Proposition 27.4 error estimate before the real-derivative
identification layer.
-/
theorem bookOutsideStieltjes_dyadicErrorBound
    (C : AugmentedLoewnerLocalConstruction f m) (K : ℝ≥0)
    (hK :
      ∀ i : Fin (nonzeroInteriorDyadicPointCount m + 1),
        ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) ≤ (K : ENNReal))
    (i : Fin (nonzeroInteriorDyadicPointCount m + 1)) :
    ‖C.bookOutsideStieltjes (zeroAnchoredDyadicPointFamily m i) -
        (f (zeroAnchoredDyadicPointFamily m i) : ℂ)‖ₑ ≤
      ((K : ENNReal) *
          (((nonzeroInteriorDyadicPointCount m + 1 : ℕ) : ENNReal) *
            (ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ) *
            (K : ENNReal))) ^ (1 / 2 : ℝ) := by
  let x := zeroAnchoredDyadicPointFamily m i
  have hError :
      ‖C.bookOutsideStieltjes x - (f x : ℂ)‖ₑ = ‖C.bookInsideStieltjes x‖ₑ := by
    simpa [x] using
      congrArg (fun z : ℂ => ‖z‖ₑ)
        (C.bookOutsideStieltjes_sub_f_eq_neg_inside_on_dyadic i)
  have hCS := C.bookInsideStieltjes_norm_le_sqrt_sqInvDist_mul_mass i
  have hSq :
      (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist x y ∂(C.bookInsideMeasure)) ≤
        (K : ENNReal) := by
    simpa [x] using (C.bookInside_sqInvDist_le_deriv i).trans (hK i)
  have hMass :
      C.bookInsideMeasure Set.univ ≤
        ((nonzeroInteriorDyadicPointCount m + 1 : ℕ) : ENNReal) *
          (ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ) * (K : ENNReal) := by
    rw [C.bookInsideMeasure_univ_eq]
    exact C.insideMass_le_of_uniform_deriv_bound (K := (K : ENNReal)) hK
  have hProd :
      (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist x y ∂(C.bookInsideMeasure)) *
          C.bookInsideMeasure Set.univ ≤
        (K : ENNReal) *
          (((nonzeroInteriorDyadicPointCount m + 1 : ℕ) : ENNReal) *
            (ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ) * (K : ENNReal)) :=
    mul_le_mul' hSq hMass
  calc
    ‖C.bookOutsideStieltjes x - (f x : ℂ)‖ₑ ≤
        ((∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist x y ∂(C.bookInsideMeasure)) *
          C.bookInsideMeasure Set.univ) ^ (1 / 2 : ℝ) := by
          rw [hError]
          simpa [x] using hCS
    _ ≤ ((K : ENNReal) *
          (((nonzeroInteriorDyadicPointCount m + 1 : ℕ) : ENNReal) *
            (ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ) *
            (K : ENNReal))) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hProd (by norm_num)

/-- The dyadic error estimate with the book-route prefactor simplified. -/
theorem bookOutsideStieltjes_dyadicErrorBound_prefactor
    (C : AugmentedLoewnerLocalConstruction f m) (K : ℝ≥0)
    (hK :
      ∀ i : Fin (nonzeroInteriorDyadicPointCount m + 1),
        ENNReal.ofReal (deriv f (zeroAnchoredDyadicPointFamily m i)) ≤ (K : ENNReal))
    (i : Fin (nonzeroInteriorDyadicPointCount m + 1)) :
    ‖C.bookOutsideStieltjes (zeroAnchoredDyadicPointFamily m i) -
        (f (zeroAnchoredDyadicPointFamily m i) : ℂ)‖ₑ ≤
      ((K : ENNReal) *
          (ENNReal.ofReal (8 * dyadicGridRadius m) * (K : ENNReal))) ^
        (1 / 2 : ℝ) := by
  have hBase := C.bookOutsideStieltjes_dyadicErrorBound K hK i
  have hPref :
      ((nonzeroInteriorDyadicPointCount m + 1 : ℕ) : ENNReal) *
          (ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ) * (K : ENNReal) ≤
        ENNReal.ofReal (8 * dyadicGridRadius m) * (K : ENNReal) :=
    mul_le_mul' (bookDyadicInsideMassPrefactor_le m) le_rfl
  have hProd :
      (K : ENNReal) *
          (((nonzeroInteriorDyadicPointCount m + 1 : ℕ) : ENNReal) *
            (ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ) * (K : ENNReal)) ≤
        (K : ENNReal) *
          (ENNReal.ofReal (8 * dyadicGridRadius m) * (K : ENNReal)) :=
    mul_le_mul' le_rfl hPref
  exact hBase.trans (ENNReal.rpow_le_rpow hProd (by norm_num))

/--
The outside restriction inherits the inverse-square estimate at the dyadic
center `0`.
-/
theorem bookOutside_sqInvDist_zero_le_deriv
    (C : AugmentedLoewnerLocalConstruction f m) :
    (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist (0 : ℝ) y ∂(C.bookOutsideMeasure)) ≤
      ENNReal.ofReal (deriv f 0) := by
  have hmono :
      (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist (0 : ℝ) y ∂(C.bookOutsideMeasure)) ≤
        ∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist (0 : ℝ) y
          ∂(C.toFiniteWitness.diracMeasure) := by
    simpa [bookOutsideMeasure] using
      (lintegral_mono' (μ := C.bookOutsideMeasure)
        (ν := C.toFiniteWitness.diracMeasure) Measure.restrict_le_self
        (fun _ => le_rfl))
  have hfull := C.dyadic_sqInvDist_le_deriv (0 : Fin (nonzeroInteriorDyadicPointCount m + 1))
  exact hmono.trans (by simpa using hfull)

private theorem abs_sub_ge_half_of_mem_Icc_compl_of_mem_half {x y : ℝ}
    (hy : y ∈ (Set.Icc (-1 : ℝ) 1)ᶜ)
    (hx : x ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    (1 / 2 : ℝ) ≤ |y - x| := by
  have hy_abs : (1 : ℝ) ≤ |y| := one_le_abs_of_mem_Icc_compl hy
  have hx_abs : |x| < (1 / 2 : ℝ) := by
    rwa [abs_lt]
  have hrev : |y| - |x| ≤ |y - x| := abs_sub_abs_le_abs_sub y x
  have hhalf : (1 / 2 : ℝ) < |y| - |x| := by linarith
  exact (le_of_lt hhalf).trans hrev

private theorem inv_sq_norm_le_four_of_mem_Icc_compl_of_mem_half {x y : ℝ}
    (hy : y ∈ (Set.Icc (-1 : ℝ) 1)ᶜ)
    (hx : x ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    ‖(1 / (y - x) ^ 2 : ℝ)‖ ≤ (4 : ℝ) := by
  have hdist : (1 / 2 : ℝ) ≤ |y - x| :=
    abs_sub_ge_half_of_mem_Icc_compl_of_mem_half hy hx
  have hpos : 0 < |y - x| := lt_of_lt_of_le (by norm_num) hdist
  have hsq : (1 / 2 : ℝ) ^ 2 ≤ |y - x| ^ 2 := by
    nlinarith [sq_nonneg (|y - x| - (1 / 2 : ℝ))]
  have hsqpos : 0 < |y - x| ^ 2 := by positivity
  have hinv : (|y - x| ^ 2)⁻¹ ≤ (((1 / 2 : ℝ) ^ 2)⁻¹) := by
    exact (inv_le_inv₀ hsqpos (by norm_num)).2 hsq
  have hnorm : ‖(1 / (y - x) ^ 2 : ℝ)‖ = (|y - x| ^ 2)⁻¹ := by
    rw [one_div, Real.norm_eq_abs, abs_inv, abs_pow]
  rw [hnorm]
  norm_num at hinv ⊢
  exact hinv

private theorem integrable_bookOutside_inv_sq_zero
    (C : AugmentedLoewnerLocalConstruction f m) :
    Integrable (fun y : ℝ => 1 / y ^ 2) C.bookOutsideMeasure := by
  haveI : IsFiniteMeasure C.bookOutsideMeasure := C.bookOutsideMeasure_isFiniteMeasure
  refine Integrable.of_bound ?_ (4 : ℝ) ?_
  · have hmeas : Measurable (fun y : ℝ => (y ^ 2)⁻¹) :=
      (measurable_id.pow_const (2 : ℕ)).inv
    simpa [one_div] using hmeas.aestronglyMeasurable
  · filter_upwards [C.ae_bookOutsideMeasure_mem_Icc_compl] with y hy
    have hx : (0 : ℝ) ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by norm_num
    simpa using inv_sq_norm_le_four_of_mem_Icc_compl_of_mem_half (x := 0) hy hx

/--
At `0`, the real outside Stieltjes transform has derivative equal to the
outside inverse-square integral.
-/
theorem bookOutsideStieltjesReal_hasDerivAt_zero
    (C : AugmentedLoewnerLocalConstruction f m) :
    HasDerivAt (fun x : ℝ => C.bookOutsideStieltjesReal x)
      (∫ y, (1 / y ^ 2) ∂C.bookOutsideMeasure) 0 := by
  let μ := C.bookOutsideMeasure
  haveI : IsFiniteMeasure μ := C.bookOutsideMeasure_isFiniteMeasure
  let s : Set ℝ := Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)
  have hs : s ∈ 𝓝 (0 : ℝ) := by
    exact Ioo_mem_nhds (by norm_num) (by norm_num)
  have hF_meas :
      ∀ᶠ x in 𝓝 (0 : ℝ),
        AEStronglyMeasurable (fun y : ℝ => 1 / (y - x)) μ := by
    exact Filter.Eventually.of_forall fun x => by
      have hmeas : Measurable (fun y : ℝ => (y - x)⁻¹) :=
        (measurable_id.sub measurable_const).inv
      simpa [one_div] using hmeas.aestronglyMeasurable
  have hF_int : Integrable (fun y : ℝ => 1 / (y - 0)) μ := by
    simpa [μ] using C.integrable_bookOutsideStieltjesKernelReal 0
  have hF'_meas :
      AEStronglyMeasurable (fun y : ℝ => 1 / (y - 0) ^ 2) μ := by
    have hmeas : Measurable (fun y : ℝ => ((y - 0) ^ 2)⁻¹) :=
      ((measurable_id.sub measurable_const).pow_const (2 : ℕ)).inv
    simpa [one_div] using hmeas.aestronglyMeasurable
  have hBound :
      ∀ᵐ y ∂μ, ∀ x ∈ s, ‖(1 / (y - x) ^ 2 : ℝ)‖ ≤ (fun _ : ℝ => (4 : ℝ)) y := by
    filter_upwards [C.ae_bookOutsideMeasure_mem_Icc_compl] with y hy x hx
    exact inv_sq_norm_le_four_of_mem_Icc_compl_of_mem_half hy hx
  have hBoundInt : Integrable (fun _ : ℝ => (4 : ℝ)) μ := integrable_const (4 : ℝ)
  have hDiff :
      ∀ᵐ y ∂μ, ∀ x ∈ s,
        HasDerivAt (fun x : ℝ => 1 / (y - x)) (1 / (y - x) ^ 2) x := by
    filter_upwards [C.ae_bookOutsideMeasure_mem_Icc_compl] with y hy x hx
    have hdist : (1 / 2 : ℝ) ≤ |y - x| :=
      abs_sub_ge_half_of_mem_Icc_compl_of_mem_half hy hx
    have hne : y - x ≠ 0 :=
      abs_pos.mp (lt_of_lt_of_le (by norm_num) hdist)
    have hlin : HasDerivAt (fun x : ℝ => y - x) (-1 : ℝ) x := by
      simpa using (hasDerivAt_const (x := x) (c := y)).sub (hasDerivAt_id x)
    have hinv := hlin.inv hne
    simpa [one_div, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]
      using hinv
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := fun x y : ℝ => 1 / (y - x))
      (F' := fun x y : ℝ => 1 / (y - x) ^ 2)
      (bound := fun _ : ℝ => (4 : ℝ))
      (x₀ := (0 : ℝ)) (s := s)
      hs hF_meas hF_int hF'_meas hBound hBoundInt hDiff
  simpa [bookOutsideStieltjesReal, μ] using h.2

/-- The derivative at `0` is the outside inverse-square integral in `ENNReal` form. -/
theorem bookOutsideStieltjesReal_deriv_zero_eq_sqInvDist
    (C : AugmentedLoewnerLocalConstruction f m) :
    ENNReal.ofReal (deriv (fun x : ℝ => C.bookOutsideStieltjesReal x) 0) =
      ∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist (0 : ℝ) y ∂C.bookOutsideMeasure := by
  have hderiv :
      deriv (fun x : ℝ => C.bookOutsideStieltjesReal x) 0 =
        ∫ y, (1 / y ^ 2) ∂C.bookOutsideMeasure :=
    C.bookOutsideStieltjesReal_hasDerivAt_zero.deriv
  rw [hderiv]
  have hInt := C.integrable_bookOutside_inv_sq_zero
  have hNonneg : 0 ≤ᵐ[C.bookOutsideMeasure] fun y : ℝ => 1 / y ^ 2 := by
    exact Filter.Eventually.of_forall fun _ => by positivity
  rw [ofReal_integral_eq_lintegral_ofReal hInt hNonneg]
  apply lintegral_congr_ae
  filter_upwards [C.ae_bookOutsideMeasure_mem_Icc_compl] with y hy
  have hy_ne : y ≠ 0 := by
    have hy_abs : (1 : ℝ) ≤ |y| := one_le_abs_of_mem_Icc_compl hy
    exact abs_pos.mp (lt_of_lt_of_le zero_lt_one hy_abs)
  simpa [one_div] using ofReal_inv_sq_eq_sqInvDist_zero hy_ne

/-- Proposition 27.4(ii) derivative bound for the outside Stieltjes approximant. -/
theorem bookOutsideStieltjes_deriv_zero_le
    (C : AugmentedLoewnerLocalConstruction f m) :
    deriv (fun x : ℝ => C.bookOutsideStieltjesReal x) 0 ≤ deriv f 0 := by
  have hNonneg : 0 ≤ deriv f 0 := by
    have hnorm :=
      C.norm_sq_dyadicIndex_eq_deriv (0 : Fin (nonzeroInteriorDyadicPointCount m + 1))
    have hderiv :
        deriv f 0 =
          ‖C.v (augmentedBackboneDyadicIndex m
            (0 : Fin (nonzeroInteriorDyadicPointCount m + 1)))‖ ^ 2 := by
      simpa using hnorm.symm
    rw [hderiv]
    positivity
  have hENN :
      ENNReal.ofReal (deriv (fun x : ℝ => C.bookOutsideStieltjesReal x) 0) ≤
        ENNReal.ofReal (deriv f 0) := by
    rw [C.bookOutsideStieltjesReal_deriv_zero_eq_sqInvDist]
    exact C.bookOutside_sqInvDist_zero_le_deriv
  exact (ENNReal.ofReal_le_ofReal_iff hNonneg).mp hENN

end AugmentedLoewnerLocalConstruction

end

end Quantum.TraceInequality.Loewner
