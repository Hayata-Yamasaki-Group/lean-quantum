/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.MatrixFunctionalCalculus.Transport
import Quantum.TraceInequality.HansenPedersen.MatrixPosDef
import Quantum.TraceInequality.HiaiPetz.Support.MatrixSupport
import Mathlib.LinearAlgebra.Lagrange
import Quantum.TraceInequality.HansenPedersen.AmbientSubmodule.JOperator
import Quantum.TraceInequality.LownerHeinz.Defs
import Quantum.TraceInequality.TraceFunctionMonotonicity.PowerTrace
import Quantum.TraceInequality.TraceFunctionMonotonicity.Sandwiched.PowerTrace

/-!
# Power trace expressions

Matrix powers and trace expressions used in the Hiai--Petz power-specialized
quasi-entropy arguments.  The file provides both the ordinary real-functional-
calculus powers and the book-facing support convention at zero eigenvalues,
then relates them to spectral sums, support projections, `J`-quadratic forms,
and semidefinite regularization limits.

## Main results

* `supportMatrixPower_eq_matrixCfcR_supportPowerCoeff_nonneg`: the
  support-convention power is real CFC with the support coefficient on
  nonnegative matrices.
* `supportLiebTracePower_eq_liebTracePower_of_nonneg_Ioo`: on the open
  parameter interval, support and ordinary trace powers agree for semidefinite
  inputs.
* `matrixPower_tendsto_of_tendsto_nonneg`: nonnegative matrix powers are
  continuous along filters for nonnegative exponents.

## References

* Hiai, Theorem 6.3.
-/

namespace HiaiPetz

open scoped ComplexOrder MatrixOrder

noncomputable section MatrixScopedInstances

variable {n : ℕ}

/-- The inverse `J_f^{-1}` quadratic form specialized to `f x = x^p`, written in
the trace-shifted form used by Theorem 6.3(2). -/
theorem jOperatorInv_powerFn_qform_eq_jInversePowerTrace (p : ℝ) {A B X : Mₙ n}
    (hB : Matrix.PosDef B) :
    Complex.re (Matrix.trace (Matrix.conjTranspose X * (jOperatorInv (powerFn p) A B X))) =
      jInversePowerTrace p A B X := by
  simpa [jInversePowerTrace] using
    hsQForm_jOperatorInv_of_posDef (f := powerFn p) (A := A) (B := B) hB X X

/-- Rewriting orientation from the Theorem 6.3 inverse `J`-form back to the
`jOperatorInv` quadratic form. -/
theorem jInversePowerTrace_eq_jOperatorInv_powerFn_qform (p : ℝ) {A B X : Mₙ n}
    (hB : Matrix.PosDef B) :
    jInversePowerTrace p A B X =
      Complex.re (Matrix.trace (Matrix.conjTranspose X * (jOperatorInv (powerFn p) A B X))) :=
  (jOperatorInv_powerFn_qform_eq_jInversePowerTrace (p := p) (A := A) (B := B) (X := X) hB).symm

end MatrixScopedInstances

noncomputable section MatrixPowerLimits

open scoped Topology

variable {n : ℕ}

/-- Spectrum containment for a nonnegative CLM with a norm bound: the real
spectrum of `0 ≤ T` with `‖T‖ ≤ β` lies in `[0, β]`.  Factored out of the
regularization-continuity proof so that the deep `NonnegSpectrumClass` /
isometric-CFC instance searches run once, in a small context. -/
private lemma clm_spectrum_subset_Icc_of_nonneg_of_norm_le
    {T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)} {β : ℝ}
    (hT : 0 ≤ T) (hβ : ‖T‖ ≤ β) :
    spectrum ℝ T ⊆ Set.Icc (0 : ℝ) β := by
  intro x hx
  have hT_sa : IsSelfAdjoint T := IsSelfAdjoint.of_nonneg hT
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg (𝕜 := ℝ) hT hx
  have hxnorm : ‖x‖ ≤ ‖T‖ :=
    IsometricContinuousFunctionalCalculus.norm_spectrum_le (a := T) hx hT_sa
  have hxle : x ≤ ‖T‖ := by
    simpa [Real.norm_of_nonneg hx0] using hxnorm
  exact ⟨hx0, le_trans hxle hβ⟩

/-- Operator-side regularization continuity: on nonnegative CLMs, the real
functional calculus of the power function `x ^ p` (`0 ≤ p`) is continuous along
filters.  This is the `Filter.Tendsto.cfc` core of the matrix-side lemma
`matrixPower_tendsto_of_tendsto_nonneg` below, stated on atoms so the heavy
CFC elaboration happens once here. -/
private lemma cfcR_powerFn_tendsto_of_tendsto_nonneg {p : ℝ} (hp : 0 ≤ p)
    {l : Filter ℝ}
    {Tε : ℝ → EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)}
    {T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)}
    (hTlim : Filter.Tendsto Tε l (𝓝 T))
    (hT_nonneg : 0 ≤ T)
    (hTε_nonneg : ∀ᶠ ε in l, 0 ≤ Tε ε) :
    Filter.Tendsto
      (fun ε : ℝ =>
        LownerHeinzTheorem.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) (powerFn p) (Tε ε))
      l
      (𝓝 (LownerHeinzTheorem.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) (powerFn p) T)) := by
  have hT_sa : IsSelfAdjoint T := IsSelfAdjoint.of_nonneg hT_nonneg
  have hTε_sa : ∀ᶠ ε in l, IsSelfAdjoint (Tε ε) :=
    hTε_nonneg.mono fun ε hε => IsSelfAdjoint.of_nonneg hε
  have hnorm_event : ∀ᶠ ε in l, ‖Tε ε‖ ≤ ‖T‖ + 1 := by
    have hnorm_tendsto : Filter.Tendsto (fun ε : ℝ => ‖Tε ε‖) l (𝓝 ‖T‖) :=
      hTlim.norm
    have hlt : ∀ᶠ r : ℝ in 𝓝 ‖T‖, r < ‖T‖ + 1 := Iio_mem_nhds (by linarith)
    exact (hnorm_tendsto.eventually hlt).mono fun ε hε => le_of_lt hε
  have hTε_spectrum :
      ∀ᶠ ε in l, spectrum ℝ (Tε ε) ⊆ Set.Icc (0 : ℝ) (‖T‖ + 1) := by
    filter_upwards [hTε_nonneg, hnorm_event] with ε hε_nonneg hε_norm
    exact clm_spectrum_subset_Icc_of_nonneg_of_norm_le hε_nonneg hε_norm
  have hT_spectrum : spectrum ℝ T ⊆ Set.Icc (0 : ℝ) (‖T‖ + 1) :=
    clm_spectrum_subset_Icc_of_nonneg_of_norm_le hT_nonneg (by linarith)
  simpa [LownerHeinzTheorem.cfcR] using
    Filter.Tendsto.cfc
      (A := EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
      (hs := isCompact_Icc) (f := powerFn p)
      hTlim hTε_spectrum hTε_sa hT_spectrum hT_sa
      ((Real.continuous_rpow_const hp).continuousOn)

/-- Continuity of the matrix-to-operator transport `Matrix.toEuclideanCLM`
(finite-dimensional linear map). -/
@[fun_prop] private lemma toEuclideanCLM_continuous :
    Continuous (fun D : Mₙ n =>
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) D :
        EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) := by
  let L : Mₙ n →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    { toFun := fun D => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) D
      map_add' := by
        intro D E
        exact map_add _ D E
      map_smul' := by
        intro c D
        exact map_smul _ c D }
  simpa [L] using LinearMap.continuous_of_finiteDimensional L

/-- Continuity of the operator-to-matrix transport `Matrix.toEuclideanCLM.symm`
(finite-dimensional linear map). -/
@[fun_prop] private lemma toEuclideanCLM_symm_continuous :
    Continuous (fun S : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) =>
      ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm S : Mₙ n)) := by
  letI : FiniteDimensional ℂ
    (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := inferInstance
  exact LinearMap.continuous_of_finiteDimensional
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).symm.toAlgEquiv.toLinearMap

/-- Positivity transport: a Loewner-nonnegative matrix maps to a nonnegative
operator under `Matrix.toEuclideanCLM`. -/
private lemma toEuclideanCLM_nonneg_of_nonneg {C : Mₙ n} (hC : 0 ≤ C) :
    (0 : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) ≤
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) C := by
  have hCpsd : C.PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hC
  have hpos : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) C :
      EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).IsPositive := by
    change ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) C :
      EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
      EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)).IsPositive
    simpa [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
      (Matrix.isPositive_toEuclideanLin_iff (A := C)).2 hCpsd
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).2 hpos

/-- Regularization continuity for the matrix power: if `Cε → C` with all terms
Loewner-nonnegative and `0 ≤ p`, then `matrixPower p (Cε ε) → matrixPower p C`.
Shared by the Hiai--Petz 6.3/6.4 semidefinite-boundary arguments. -/
theorem matrixPower_tendsto_of_tendsto_nonneg {n : ℕ} {p : ℝ} (hp : 0 ≤ p)
    {l : Filter ℝ} {Cε : ℝ → Mₙ n} {C : Mₙ n}
    (hlim : Filter.Tendsto Cε l (𝓝 C))
    (hC : 0 ≤ C)
    (hCε : ∀ᶠ ε in l, 0 ≤ Cε ε) :
    Filter.Tendsto (fun ε : ℝ => matrixPower p (Cε ε)) l (𝓝 (matrixPower p C)) := by
  have hTlim :
      Filter.Tendsto (fun ε : ℝ => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (Cε ε)) l
        (𝓝 (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) C)) :=
    (toEuclideanCLM_continuous (n := n)).continuousAt.tendsto.comp hlim
  have hT_nonneg := toEuclideanCLM_nonneg_of_nonneg hC
  have hTε_nonneg : ∀ᶠ ε in l,
      (0 : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) ≤
        Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (Cε ε) :=
    hCε.mono fun ε hε => toEuclideanCLM_nonneg_of_nonneg hε
  have hcfc := cfcR_powerFn_tendsto_of_tendsto_nonneg hp hTlim hT_nonneg hTε_nonneg
  simpa [matrixPower, HansenPedersen.matrixCfcR, LownerHeinzTheorem.cfcR] using
    (toEuclideanCLM_symm_continuous (n := n)).continuousAt.tendsto.comp hcfc

/-- `matrixPower (g a) C → matrixPower p₀ C` for positive-definite `C` as the exponent converges. -/
theorem matrixPower_tendsto_exponent_of_posDef {α : Type*} {n : ℕ}
    {C : Mₙ n} (hC : Matrix.PosDef C) {l : Filter α} {g : α → ℝ} {p₀ : ℝ}
    (hg : Filter.Tendsto g l (𝓝 p₀)) :
    Filter.Tendsto (fun a : α => matrixPower (g a) C) l (𝓝 (matrixPower p₀ C)) := by
  let φ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  let T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) := φ C
  have hfin : Set.Finite (spectrum ℝ T) := finite_real_spectrum_clm T
  have hσ : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ) := by
    simpa [T, φ] using toEuclideanCLM_spectrum_Ioi_of_matrix_posDef (C := C) hC
  have hunif :
      TendstoUniformlyOn (fun a : α => powerFn (g a)) (powerFn p₀) l (spectrum ℝ T) :=
    powerFn_tendstoUniformlyOn_of_finite_pos hfin hσ hg
  have hcont : ∀ᶠ a : α in l, ContinuousOn (powerFn (g a)) (spectrum ℝ T) :=
    Filter.Eventually.of_forall fun a => hfin.continuousOn _
  have hcfc :
      Filter.Tendsto
        (fun a : α =>
          LownerHeinzTheorem.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) (powerFn (g a)) T)
        l
        (𝓝 (LownerHeinzTheorem.cfcR (ℋ := EuclideanSpace ℂ (Fin n)) (powerFn p₀) T)) := by
    dsimp [LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR]
    exact tendsto_cfc_fun hunif hcont
  have hφsymm_cont :
      Continuous fun S : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) =>
        (φ.symm S : Mₙ n) := by
    letI : FiniteDimensional ℂ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
      inferInstance
    exact LinearMap.continuous_of_finiteDimensional φ.symm.toAlgEquiv.toLinearMap
  simpa [matrixPower, HansenPedersen.matrixCfcR, T, φ] using
    hφsymm_cont.continuousAt.tendsto.comp hcfc

/-- `liebTracePower p` is continuous along limits of nonnegative matrix pairs (`p ∈ (0,1)`). -/
theorem liebTracePower_tendsto_of_tendsto_nonneg {n : ℕ} {p : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    {l : Filter ℝ} {Aε Bε : ℝ → Mₙ n} {A B X : Mₙ n}
    (hAlim : Filter.Tendsto Aε l (𝓝 A))
    (hBlim : Filter.Tendsto Bε l (𝓝 B))
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAε : ∀ᶠ ε in l, 0 ≤ Aε ε)
    (hBε : ∀ᶠ ε in l, 0 ≤ Bε ε) :
    Filter.Tendsto (fun ε : ℝ => liebTracePower p (Aε ε) (Bε ε) X) l
      (𝓝 (liebTracePower p A B X)) := by
  have hp_nonneg : 0 ≤ p := le_of_lt hp.1
  have h1mp_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp.2.le
  have hApow :
      Filter.Tendsto (fun ε : ℝ => matrixPower p (Aε ε)) l (𝓝 (matrixPower p A)) :=
    matrixPower_tendsto_of_tendsto_nonneg hp_nonneg hAlim hA hAε
  have hBpow :
      Filter.Tendsto (fun ε : ℝ => matrixPower (1 - p) (Bε ε)) l
        (𝓝 (matrixPower (1 - p) B)) :=
    matrixPower_tendsto_of_tendsto_nonneg h1mp_nonneg hBlim hB hBε
  have hprod :
      Filter.Tendsto
        (fun ε : ℝ =>
          Matrix.conjTranspose X * matrixPower p (Aε ε) * X *
            matrixPower (1 - p) (Bε ε))
        l
        (𝓝 (Matrix.conjTranspose X * matrixPower p A * X * matrixPower (1 - p) B)) := by
    simpa [Matrix.mul_assoc] using
      (((tendsto_const_nhds.mul hApow).mul tendsto_const_nhds).mul hBpow)
  have htrace :
      Filter.Tendsto
        (fun ε : ℝ =>
          Matrix.trace
            (Matrix.conjTranspose X * matrixPower p (Aε ε) * X *
              matrixPower (1 - p) (Bε ε)))
        l
        (𝓝 (Matrix.trace
          (Matrix.conjTranspose X * matrixPower p A * X * matrixPower (1 - p) B))) := by
    have hcont : Continuous (fun M : Mₙ n => Matrix.trace M) := by
      dsimp [Matrix.trace]
      fun_prop
    exact hcont.continuousAt.tendsto.comp hprod
  simpa [liebTracePower, powerTrace] using Complex.continuous_re.continuousAt.tendsto.comp htrace

end MatrixPowerLimits

end HiaiPetz
