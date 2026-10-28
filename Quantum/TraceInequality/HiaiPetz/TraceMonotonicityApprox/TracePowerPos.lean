/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.TraceMonotonicityApprox.ScalarApprox
import Quantum.TraceInequality.HiaiPetz.TraceMonotonicityApprox.PsiOperatorMonotone
import Quantum.TraceInequality.HiaiPetz.TraceMonotonicity.Basic
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.Main
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.OutputSupport.Reduction
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.SharedStages

/-!
# Theorem 6.3(3) on the positive exponent range

Quasi-entropy convergence along the truncated approximations, the concrete
`J`-form and trace-power forms of Hiai--Petz Theorem 6.3(3) on `1 < p < 2`,
the endpoint cases `p = 1, 2`, and the closed range `1 ≤ p ≤ 2`
(`liebTracePower_map_le_strictlyPositive_posIcc` and its output-support form).
-/

namespace HiaiPetz

namespace TraceMonotonicity

open scoped ComplexOrder MatrixOrder Topology Interval
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

private theorem finite_real_spectrum_hsOp {n : ℕ} (T : HSOp n) :
    Set.Finite (spectrum ℝ T) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  have hspecCfin : Set.Finite (spectrum ℂ T) := by
    rw [@ContinuousLinearMap.spectrum_eq ℂ _ (Mₙ n)
      (instMatrixNormedAddCommGroup (n := n)) (instMatrixNormedSpace (n := n))
      (instMatrixCompleteSpace (n := n)) (f := T)]
    simpa using Module.End.finite_spectrum (K := ℂ) (V := Mₙ n) T.toLinearMap
  rw [← spectrum.preimage_algebraMap ℂ]
  exact hspecCfin.preimage (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

private theorem powerApprox_tendstoUniformlyOn_spectrum_jArg {n : ℕ}
    {p : ℝ} {A B : Mₙ n} (hp : p ∈ Set.Ioo (1 : ℝ) 2)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    TendstoUniformlyOn (fun k : ℕ => powerApprox p k) (powerFn p)
      Filter.atTop (spectrum ℝ (jArg A B)) := by
  let s : Set ℝ := spectrum ℝ (jArg A B)
  have hfin : Set.Finite s := by
    simpa [s] using finite_real_spectrum_hsOp (jArg A B)
  have hs : IsCompact s := hfin.isCompact
  refine Monotone.tendstoUniformlyOn_of_forall_tendsto
    (F := fun k : ℕ => powerApprox p k) (f := powerFn p) (s := s)
    hs ?hFcont ?hmono ?hfcont ?htend
  · intro k
    exact hfin.continuousOn _
  · intro x hx
    have hxpos : 0 < x := spectrum_jArg_subset_Ioi_of_posDef hA hB (by simpa [s] using hx)
    exact powerApprox_monotone_cutoff hp (le_of_lt hxpos)
  · exact hfin.continuousOn _
  · intro x hx
    have hxpos : 0 < x := spectrum_jArg_subset_Ioi_of_posDef hA hB (by simpa [s] using hx)
    simpa [powerFn] using powerApprox_tendsto_rpow hp (le_of_lt hxpos)

private theorem hsCfcR_powerApprox_tendsto_powerFn {n : ℕ}
    {p : ℝ} {A B : Mₙ n} (hp : p ∈ Set.Ioo (1 : ℝ) 2)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    Filter.Tendsto
      (fun k : ℕ => hsCfcR (powerApprox p k) (jArg A B))
      Filter.atTop
      (𝓝 (hsCfcR (powerFn p) (jArg A B))) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  have hunif := powerApprox_tendstoUniformlyOn_spectrum_jArg
    (n := n) (p := p) (A := A) (B := B) hp hA hB
  have hcont : ∀ᶠ k : ℕ in Filter.atTop,
      ContinuousOn (powerApprox p k) (spectrum ℝ (jArg A B)) := by
    have hfin : Set.Finite (spectrum ℝ (jArg A B)) := finite_real_spectrum_hsOp (jArg A B)
    exact Filter.Eventually.of_forall fun k => hfin.continuousOn _
  dsimp [hsCfcR, HansenPedersen.cfcR, LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR]
  exact tendsto_cfc_fun hunif hcont

private theorem quasiEntropy_powerApprox_tendsto_powerFn {n : ℕ}
    {p : ℝ} {A B X : Mₙ n} (hp : p ∈ Set.Ioo (1 : ℝ) 2)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) :
    Filter.Tendsto
      (fun k : ℕ => quasiEntropy (powerApprox p k) A B X)
      Filter.atTop
      (𝓝 (quasiEntropy (powerFn p) A B X)) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  have hCfc := hsCfcR_powerApprox_tendsto_powerFn
    (n := n) (p := p) (A := A) (B := B) hp hA hB
  have hJ :
      Filter.Tendsto
        (fun k : ℕ => hsCfcR (powerApprox p k) (jArg A B) * rightMul B)
        Filter.atTop
        (𝓝 (hsCfcR (powerFn p) (jArg A B) * rightMul B)) := by
    simpa using hCfc.mul tendsto_const_nhds
  have happly :
      Filter.Tendsto
        (fun k : ℕ => (hsCfcR (powerApprox p k) (jArg A B) * rightMul B) X)
        Filter.atTop
        (𝓝 ((hsCfcR (powerFn p) (jArg A B) * rightMul B) X)) := by
    exact (ContinuousLinearMap.apply ℂ (Mₙ n) X).continuous.continuousAt.tendsto.comp hJ
  have hprod :
      Filter.Tendsto
        (fun k : ℕ => Matrix.conjTranspose X *
          ((hsCfcR (powerApprox p k) (jArg A B) * rightMul B) X))
        Filter.atTop
        (𝓝 (Matrix.conjTranspose X *
          ((hsCfcR (powerFn p) (jArg A B) * rightMul B) X))) := by
    simpa using tendsto_const_nhds.mul happly
  have htrace :
      Filter.Tendsto
        (fun k : ℕ => Matrix.trace (Matrix.conjTranspose X *
          ((hsCfcR (powerApprox p k) (jArg A B) * rightMul B) X)))
        Filter.atTop
        (𝓝 (Matrix.trace (Matrix.conjTranspose X *
          ((hsCfcR (powerFn p) (jArg A B) * rightMul B) X)))) := by
    have hcont : Continuous (fun M : Mₙ n => Matrix.trace M) := by
      dsimp [Matrix.trace]
      fun_prop
    exact hcont.continuousAt.tendsto.comp hprod
  simpa [quasiEntropy, jOperator] using Complex.continuous_re.continuousAt.tendsto.comp htrace

/-- Concrete truncated approximation inequality for Theorem 6.3(3).
Source: Hiai, proof of Theorem 6.3. -/
def QuasiEntropyPowerApproxMapLe : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {k : ℕ} {A B : Mₙ n} {X : Mₙ m},
    p ∈ Set.Ioo (1 : ℝ) 2 →
    0 < k →
    IsPositiveMap Φ →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    Matrix.PosDef (Φ (1 : Mₙ n)) →
    Matrix.PosDef (Φ B) →
    InAdjointMultiplicativeDomain Φ X →
    quasiEntropy (powerApprox p k) (Φ A) (Φ B) X ≤
      quasiEntropy (powerApprox p k) A B ((hsAdjoint Φ) X)

/-- The concrete truncated function `f_n = a_n x - ψ_n(x)` satisfies the inequality
obtained by specializing `quasiEntropy_affineMinus_map_le_of_operatorMonotone`.
Source: Hiai, proof of Theorem 6.3. -/
theorem quasiEntropy_powerApprox_map_le :
    QuasiEntropyPowerApproxMapLe := by
  intro n m Φ p k A B X hp hk hPos hTrace hSch hA hB hΦ1 hΦB hmd
  have hineq :
      quasiEntropy
          (fun x : ℝ => approxCoeff p k * x - psiApprox p k x)
          (Φ A) (Φ B) X ≤
        quasiEntropy
          (fun x : ℝ => approxCoeff p k * x - psiApprox p k x)
          A B ((hsAdjoint Φ) X) :=
    quasiEntropy_affineMinus_map_le_of_operatorMonotone Φ
      (a := approxCoeff p k)
      (ψ := psiApprox p k)
      (A := A) (B := B) (X := X)
      (psiApprox_continuousOn_Ioi hp k)
      (psiApprox_pos_Ioi hp hk)
      (psiApprox_operatorMonotone hp k)
      hPos hTrace hSch hA hB hΦ1 hΦB hmd
  simpa [powerApprox] using hineq

/-- Strict-output positive-definite `1 < p < 2` `J`-form inequality for Theorem 6.3(3).
Source: Hiai, proof of Theorem 6.3. -/
def QuasiEntropyPowerFnMapLeIoo : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B : Mₙ n} {X : Mₙ m},
    p ∈ Set.Ioo (1 : ℝ) 2 →
    IsPositiveMap Φ →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    Matrix.PosDef (Φ (1 : Mₙ n)) →
    Matrix.PosDef (Φ B) →
    InAdjointMultiplicativeDomain Φ X →
    quasiEntropy (powerFn p) (Φ A) (Φ B) X ≤
      quasiEntropy (powerFn p) A B ((hsAdjoint Φ) X)

/-- The cutoff approximation inequalities pass to the scalar-power limit, giving the
strict-output positive-definite `J`-form part of Theorem 6.3(3) for `1 < p < 2`.
Source: Hiai, proof of Theorem 6.3. -/
theorem quasiEntropy_powerFn_map_le_Ioo :
    QuasiEntropyPowerFnMapLeIoo := by
  intro n m Φ p A B X hp hPos hTrace hSch hA hB hΦ1 hΦB hmd
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hlhs :
      Filter.Tendsto
        (fun k : ℕ => quasiEntropy (powerApprox p k) (Φ A) (Φ B) X)
        Filter.atTop
        (𝓝 (quasiEntropy (powerFn p) (Φ A) (Φ B) X)) :=
    quasiEntropy_powerApprox_tendsto_powerFn (n := m) (p := p)
      (A := Φ A) (B := Φ B) (X := X) hp hΦA hΦB
  have hrhs :
      Filter.Tendsto
        (fun k : ℕ => quasiEntropy (powerApprox p k) A B ((hsAdjoint Φ) X))
        Filter.atTop
        (𝓝 (quasiEntropy (powerFn p) A B ((hsAdjoint Φ) X))) :=
    quasiEntropy_powerApprox_tendsto_powerFn (n := n) (p := p)
      (A := A) (B := B) (X := (hsAdjoint Φ) X) hp hA hB
  have hle :
      (fun k : ℕ => quasiEntropy (powerApprox p k) (Φ A) (Φ B) X) ≤ᶠ[Filter.atTop]
        (fun k : ℕ => quasiEntropy (powerApprox p k) A B ((hsAdjoint Φ) X)) := by
    exact (Filter.eventually_ge_atTop 1).mono fun k hk => by
      have hkpos : 0 < k := by omega
      exact quasiEntropy_powerApprox_map_le Φ hp hkpos hPos hTrace hSch hA hB hΦ1 hΦB hmd
  exact le_of_tendsto_of_tendsto hlhs hrhs hle

/-- Strict-output positive-definite trace-power form of Theorem 6.3(3) for `1 < p < 2`.
Source: Hiai, Theorem 6.3. -/
def LiebTracePowerMapLeStrictlyPositiveIoo : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B : Mₙ n} {X : Mₙ m},
    p ∈ Set.Ioo (1 : ℝ) 2 →
    IsPositiveMap Φ →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    Matrix.PosDef (Φ (1 : Mₙ n)) →
    Matrix.PosDef (Φ B) →
    InAdjointMultiplicativeDomain Φ X →
    liebTracePower p (Φ A) (Φ B) X ≤
      liebTracePower p A B ((hsAdjoint Φ) X)

/-- The output-nondegenerate `J`-form part of Theorem 6.3(3) yields the closed
trace-power form for positive-definite inputs.
Source: Hiai, Theorem 6.3. -/
theorem liebTracePower_map_le_strictlyPositive_Ioo :
    LiebTracePowerMapLeStrictlyPositiveIoo := by
  intro n m Φ p A B X hp hPos hTrace hSch hA hB hΦ1 hΦB hmd
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hJ :=
    quasiEntropy_powerFn_map_le_Ioo Φ hp hPos hTrace hSch hA hB hΦ1 hΦB hmd
  have hleft :
      quasiEntropy (powerFn p) (Φ A) (Φ B) X =
        liebTracePower p (Φ A) (Φ B) X := by
    rw [← jPowerTrace_eq_quasiEntropy_powerFn (p := p) (A := Φ A) (B := Φ B)
      (X := X) hΦB]
    exact jPowerTrace_eq_liebTracePower_of_posDef (p := p) hΦA hΦB
  have hright :
      quasiEntropy (powerFn p) A B ((hsAdjoint Φ) X) =
        liebTracePower p A B ((hsAdjoint Φ) X) := by
    rw [← jPowerTrace_eq_quasiEntropy_powerFn (p := p) (A := A) (B := B)
      (X := (hsAdjoint Φ) X) hB]
    exact jPowerTrace_eq_liebTracePower_of_posDef (p := p) hA hB
  rwa [hleft, hright] at hJ

/-- Output-support trace-power form of the `1 < p < 2` part of Theorem 6.3(3).
This is stated on a fixed orthonormal matrix realization of the support corner,
matching the book-facing support-corner layer used for parts (1) and (2).
Source: Hiai, Theorem 6.3. -/
def LiebTracePowerMapLeOutputSupportIoo : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B : Mₙ n},
    p ∈ Set.Ioo (1 : ℝ) 2 →
    let P := outputSupportProj Φ
    let corner := matrixCornerSubmodule P
    (hPos : IsPositiveMap Φ) →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    let Φcorner : Mₙ n →L[ℂ] corner := outputSupportReducedMapToCorner Φ hPos
    let model : MatrixCornerModel P := outputSupportMatrixCornerModel Φ
    let Ψ : HSMap n model.dim :=
      (model.toMat.toContinuousLinearEquiv.toContinuousLinearMap).comp Φcorner
    ∀ {X : Mₙ model.dim},
      InAdjointMultiplicativeDomain Ψ X →
      liebTracePower p (Ψ A) (Ψ B) X ≤
        liebTracePower p A B ((hsAdjoint Ψ) X)

/-- Transport the strict-output positive-definite trace-power inequality for `1 < p < 2`
to the fixed orthonormal matrix realization of the output-support corner.
Source: Hiai, Theorem 6.3. -/
theorem liebTracePower_map_le_outputSupport_Ioo :
    LiebTracePowerMapLeOutputSupportIoo := by
  intro n m Φ p A B hp
  dsimp
  intro hPos hTrace hSch hA hB X hmd
  let Ψ := outputSupportReducedMap Φ hPos
  have hready := outputSupportReducedHSMap_strictlyPositive Φ hPos hTrace hSch
  have hΨpos : IsPositiveMap Ψ := hready.positiveMap
  have hΨtrace : TracePreserving Ψ := hready.tracePreserving
  have hΨsch : HSAdjointSchwarz Ψ := hready.adjointSchwarz
  have hΨ1 : Matrix.PosDef (Ψ (1 : Mₙ n)) := hready.outputPosDef
  have hΨB : Matrix.PosDef (Ψ B) :=
    Matrix.PosDef.image_of_isPositiveMap Ψ hΨpos (B := B) hB hΨ1
  simpa [Ψ, outputSupportReducedMap, outputSupportReducedMapToCorner,
    MatrixCornerModel.transportMap] using
    (liebTracePower_map_le_strictlyPositive_Ioo Ψ (p := p) (A := A) (B := B) (X := X)
      hp hΨpos hΨtrace hΨsch hA hB hΨ1 hΨB hmd)

private theorem liebTracePower_tendsto_exponent_of_posDef {α : Type*} {n : ℕ}
    {A B X : Mₙ n} (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    {l : Filter α} {g : α → ℝ} {p₀ : ℝ}
    (hg : Filter.Tendsto g l (𝓝 p₀)) :
    Filter.Tendsto (fun a : α => liebTracePower (g a) A B X) l
      (𝓝 (liebTracePower p₀ A B X)) := by
  have hApow :
      Filter.Tendsto (fun a : α => matrixPower (g a) A) l (𝓝 (matrixPower p₀ A)) :=
    _root_.HiaiPetz.matrixPower_tendsto_exponent_of_posDef hA hg
  have hBpow :
      Filter.Tendsto (fun a : α => matrixPower (1 - g a) B) l
        (𝓝 (matrixPower (1 - p₀) B)) :=
    _root_.HiaiPetz.matrixPower_tendsto_exponent_of_posDef hB (tendsto_const_nhds.sub hg)
  have hprod :
      Filter.Tendsto
        (fun a : α =>
          Matrix.conjTranspose X * matrixPower (g a) A * X * matrixPower (1 - g a) B)
        l
        (𝓝 (Matrix.conjTranspose X * matrixPower p₀ A * X * matrixPower (1 - p₀) B)) := by
    exact ((tendsto_const_nhds.mul hApow).mul tendsto_const_nhds).mul hBpow
  have htrace :
      Filter.Tendsto
        (fun a : α =>
          Matrix.trace
            (Matrix.conjTranspose X * matrixPower (g a) A * X * matrixPower (1 - g a) B))
        l
        (𝓝 (Matrix.trace
          (Matrix.conjTranspose X * matrixPower p₀ A * X * matrixPower (1 - p₀) B))) := by
    have hcont : Continuous (fun M : Mₙ n => Matrix.trace M) := by
      dsimp [Matrix.trace]
      fun_prop
    exact hcont.continuousAt.tendsto.comp hprod
  simpa [liebTracePower, powerTrace] using Complex.continuous_re.continuousAt.tendsto.comp htrace

/-- Endpoint `p = 1` helper for the positive closed range.
Source: Hiai, proof of Theorem 6.3. -/
private theorem liebTracePower_map_le_strictlyPositive_endpoint_one {n m : ℕ}
    (Φ : HSMap n m) {A B : Mₙ n} {X : Mₙ m}
    (hPos : IsPositiveMap Φ) (_hTrace : TracePreserving Φ) (_hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) (hΦB : Matrix.PosDef (Φ B))
    (hmd : InAdjointMultiplicativeDomain Φ X) :
    liebTracePower 1 (Φ A) (Φ B) X ≤
      liebTracePower 1 A B ((hsAdjoint Φ) X) := by
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hlin :=
    quasiEntropy_id_eq_of_multiplicativeDomain Φ (A := A) (B := B) (X := X)
      hPos hA hB hΦB hmd
  have hJ :
      quasiEntropy (powerFn 1) (Φ A) (Φ B) X =
        quasiEntropy (powerFn 1) A B ((hsAdjoint Φ) X) := by
    have hfun : powerFn 1 = fun x : ℝ => x := by
      funext x
      simp [powerFn]
    simpa [hfun] using hlin
  have hleft :
      quasiEntropy (powerFn 1) (Φ A) (Φ B) X =
        liebTracePower 1 (Φ A) (Φ B) X := by
    rw [← jPowerTrace_eq_quasiEntropy_powerFn (p := 1) (A := Φ A) (B := Φ B)
      (X := X) hΦB]
    exact jPowerTrace_eq_liebTracePower_of_posDef (p := 1) hΦA hΦB
  have hright :
      quasiEntropy (powerFn 1) A B ((hsAdjoint Φ) X) =
        liebTracePower 1 A B ((hsAdjoint Φ) X) := by
    rw [← jPowerTrace_eq_quasiEntropy_powerFn (p := 1) (A := A) (B := B)
      (X := (hsAdjoint Φ) X) hB]
    exact jPowerTrace_eq_liebTracePower_of_posDef (p := 1) hA hB
  exact le_of_eq (by simpa [hleft, hright] using hJ)

/-- Endpoint `p = 2` helper for the positive closed range.
Source: Hiai, proof of Theorem 6.3. -/
private theorem liebTracePower_map_le_strictlyPositive_endpoint_two {n m : ℕ}
    (Φ : HSMap n m) {A B : Mₙ n} {X : Mₙ m}
    (hPos : IsPositiveMap Φ) (hTrace : TracePreserving Φ) (hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) (hΦB : Matrix.PosDef (Φ B))
    (hmd : InAdjointMultiplicativeDomain Φ X) :
    liebTracePower 2 (Φ A) (Φ B) X ≤
      liebTracePower 2 A B ((hsAdjoint Φ) X) := by
  let l : Filter ℝ := 𝓝[Set.Ioo (1 : ℝ) 2] (2 : ℝ)
  haveI : Filter.NeBot l := by
    dsimp [l]
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (by norm_num : (1 : ℝ) ≠ 2)]
    exact ⟨by norm_num, le_rfl⟩
  have hΦA : Matrix.PosDef (Φ A) := Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hlhs :
      Filter.Tendsto (fun q : ℝ => liebTracePower q (Φ A) (Φ B) X) l
        (𝓝 (liebTracePower 2 (Φ A) (Φ B) X)) :=
    liebTracePower_tendsto_exponent_of_posDef hΦA hΦB
      (Filter.tendsto_id.mono_left (by exact nhdsWithin_le_nhds))
  have hrhs :
      Filter.Tendsto (fun q : ℝ => liebTracePower q A B ((hsAdjoint Φ) X)) l
        (𝓝 (liebTracePower 2 A B ((hsAdjoint Φ) X))) :=
    liebTracePower_tendsto_exponent_of_posDef hA hB
      (Filter.tendsto_id.mono_left (by exact nhdsWithin_le_nhds))
  have hle :
      (fun q : ℝ => liebTracePower q (Φ A) (Φ B) X) ≤ᶠ[l]
        fun q : ℝ => liebTracePower q A B ((hsAdjoint Φ) X) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact liebTracePower_map_le_strictlyPositive_Ioo Φ (p := q) (A := A) (B := B) (X := X)
      hq hPos hTrace hSch hA hB hΦ1 hΦB hmd
  exact le_of_tendsto_of_tendsto hlhs hrhs hle

/-- Strict-output positive-definite trace-power form of Theorem 6.3(3) on
the positive closed range `1 ≤ p ≤ 2`.
Source: Hiai, Theorem 6.3. -/
def LiebTracePowerMapLeStrictlyPositivePosIcc : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B : Mₙ n} {X : Mₙ m},
    p ∈ Set.Icc (1 : ℝ) 2 →
    IsPositiveMap Φ →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    Matrix.PosDef (Φ (1 : Mₙ n)) →
    Matrix.PosDef (Φ B) →
    InAdjointMultiplicativeDomain Φ X →
    liebTracePower p (Φ A) (Φ B) X ≤
      liebTracePower p A B ((hsAdjoint Φ) X)

/-- Extend the already proved `1 < p < 2` trace-power inequality to the endpoints
`p = 1` and `p = 2`.
Source: Hiai, Theorem 6.3. -/
theorem liebTracePower_map_le_strictlyPositive_posIcc :
    LiebTracePowerMapLeStrictlyPositivePosIcc := by
  intro n m Φ p A B X hp hPos hTrace hSch hA hB hΦ1 hΦB hmd
  rcases lt_or_eq_of_le hp.1 with hp_gt_one | hp_eq_one
  · rcases lt_or_eq_of_le hp.2 with hp_lt_two | hp_eq_two
    · exact liebTracePower_map_le_strictlyPositive_Ioo Φ ⟨hp_gt_one, hp_lt_two⟩
        hPos hTrace hSch hA hB hΦ1 hΦB hmd
    · subst p
      exact liebTracePower_map_le_strictlyPositive_endpoint_two Φ
        hPos hTrace hSch hA hB hΦ1 hΦB hmd
  · subst p
    exact liebTracePower_map_le_strictlyPositive_endpoint_one Φ
      hPos hTrace hSch hA hB hΦ1 hΦB hmd

/-- Output-support trace-power form of Theorem 6.3(3) on the positive closed range.
The statement remains on a fixed orthonormal matrix realization of the support corner.
Source: Hiai, Theorem 6.3. -/
def LiebTracePowerMapLeOutputSupportPosIcc : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m) {p : ℝ} {A B : Mₙ n},
    p ∈ Set.Icc (1 : ℝ) 2 →
    let P := outputSupportProj Φ
    let corner := matrixCornerSubmodule P
    (hPos : IsPositiveMap Φ) →
    TracePreserving Φ →
    HSAdjointSchwarz Φ →
    Matrix.PosDef A →
    Matrix.PosDef B →
    let Φcorner : Mₙ n →L[ℂ] corner := outputSupportReducedMapToCorner Φ hPos
    let model : MatrixCornerModel P := outputSupportMatrixCornerModel Φ
    let Ψ : HSMap n model.dim :=
      (model.toMat.toContinuousLinearEquiv.toContinuousLinearMap).comp Φcorner
    ∀ {X : Mₙ model.dim},
      InAdjointMultiplicativeDomain Ψ X →
      liebTracePower p (Ψ A) (Ψ B) X ≤
        liebTracePower p A B ((hsAdjoint Ψ) X)

/-- Transport the positive closed range of Theorem 6.3(3) to the fixed orthonormal matrix
realization of the output-support corner.
Source: Hiai, Theorem 6.3. -/
theorem liebTracePower_map_le_outputSupport_posIcc :
    LiebTracePowerMapLeOutputSupportPosIcc := by
  intro n m Φ p A B hp
  dsimp
  intro hPos hTrace hSch hA hB X hmd
  let Ψ := outputSupportReducedMap Φ hPos
  have hready := outputSupportReducedHSMap_strictlyPositive Φ hPos hTrace hSch
  have hΨpos : IsPositiveMap Ψ := hready.positiveMap
  have hΨtrace : TracePreserving Ψ := hready.tracePreserving
  have hΨsch : HSAdjointSchwarz Ψ := hready.adjointSchwarz
  have hΨ1 : Matrix.PosDef (Ψ (1 : Mₙ n)) := hready.outputPosDef
  have hΨB : Matrix.PosDef (Ψ B) :=
    Matrix.PosDef.image_of_isPositiveMap Ψ hΨpos (B := B) hB hΨ1
  simpa [Ψ, outputSupportReducedMap, outputSupportReducedMapToCorner,
    MatrixCornerModel.transportMap] using
    (liebTracePower_map_le_strictlyPositive_posIcc Ψ (p := p) (A := A) (B := B)
      (X := X) hp hΨpos hΨtrace hΨsch hA hB hΨ1 hΨB hmd)

end MatrixScopedInstances

end TraceMonotonicity

end HiaiPetz
