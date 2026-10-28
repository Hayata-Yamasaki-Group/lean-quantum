/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
import Quantum.TraceInequality.TraceFunctionMonotonicity.Sandwiched.PowerTrace
import Quantum.TraceInequality.TraceFunctionMonotonicity.PowerTrace
import Quantum.TraceInequality.HiaiPetz.PowerTraceRetained
import Quantum.TraceInequality.HiaiPetz.Support.MatrixSupport
import Quantum.TraceInequality.HiaiPetz.SelectedProvider
import Quantum.TraceInequality.HansenPedersen.Reduction.ReducedMap
import Quantum.TraceInequality.HiaiPetzTheorem.Reduction.ReducedMap
import Quantum.TraceInequality.TraceFunctionMonotonicity.SharedVocabulary

/-!
# Trace-power monotonicity: base layer

Foundational definitions and lemmas for Hiai–Petz Theorem 6.3 (data-processing
monotonicity of the quasi-entropy / trace-power functional), stated in the
positive-definite input regime that the formalized Theorem 6.2 layer provides.

`InAdjointMultiplicativeDomain` records the multiplicative-domain condition
`X ∈ M_{Φ*}` of Theorem 6.3(3).  The unproved positive-definite statement
packages live separately under `HiaiPetz.Frontier`, so importing this completed
chapter layer does not expose statement-only theorem surfaces.  The lemmas
relate the `J`-operator and
quasi-entropy of affine functions on the multiplicative domain and derive the
map inequality from matrix monotonicity.  The book extends these statements to
semidefinite inputs by continuity; the semidefinite support-power forms are
`supportTracePowerMonotonicity` (`TraceMonotonicityApprox/SupportTracePower.lean`).

## Main definitions

* `InAdjointMultiplicativeDomain`: the multiplicative-domain condition for the
  Hilbert–Schmidt adjoint of `Φ` (Theorem 6.3(3)).
The statement-only positive-definite formulation is isolated in
`Quantum.TraceInequality.HansenPedersen.Frontier.TraceMonotonicity`.

## References

* Hiai, Theorem 6.3 (and Theorem 6.2 for the positive-definite layer).
-/

namespace HiaiPetz

namespace TraceMonotonicity

open scoped ComplexOrder MatrixOrder Topology
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- The shared real CFC witness must be fixed locally because the CFC predicate
is an output parameter of typeclass search. -/
noncomputable local instance instTraceMonotonicityHSOpRealCFC {n : ℕ} :
    ContinuousFunctionalCalculus ℝ (HSOp n) IsSelfAdjoint :=
  hsOpRealCFC

/-- Multiplicative-domain condition for the Hilbert--Schmidt adjoint of `Φ`.

This is the current Lean surface for the book's notation `X ∈ M_{Φ*}` in Theorem 6.3(3).
It records both quadratic equalities usually associated with the multiplicative domain of a
Schwarz map. -/
def InAdjointMultiplicativeDomain {n m : ℕ} (Φ : HSMap n m) (X : Mₙ m) : Prop :=
  hsAdjoint Φ (X * Matrix.conjTranspose X) =
      (hsAdjoint Φ X) * Matrix.conjTranspose (hsAdjoint Φ X) ∧
    hsAdjoint Φ (Matrix.conjTranspose X * X) =
      Matrix.conjTranspose (hsAdjoint Φ X) * (hsAdjoint Φ X)

/-- The multiplicative-domain hypothesis identifies the linear `J_x` trace term on
the output side with the corresponding trace term after applying `Φ*` to `X`.
Source: Hiai, proof of Theorem 6.3. -/
theorem linear_trace_identity_of_multiplicativeDomain :
    ∀ {n m : ℕ} (Φ : HSMap n m) {A : Mₙ n} {X : Mₙ m},
      IsPositiveMap Φ →
      Matrix.PosDef A →
      InAdjointMultiplicativeDomain Φ X →
      Complex.re (Matrix.trace (Matrix.conjTranspose X * (Φ A) * X)) =
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose ((hsAdjoint Φ) X) * A * ((hsAdjoint Φ) X))) := by
  intro n m Φ A X hPos hA hmd
  have hΦA_sa : IsSelfAdjoint (Φ A) := by
    have hΦA_nonneg : 0 ≤ Φ A := hPos (Matrix.PosDef.nonneg hA)
    simpa [Matrix.IsHermitian, IsSelfAdjoint] using
      (Matrix.nonneg_iff_posSemidef.mp hΦA_nonneg).1
  calc
    Complex.re (Matrix.trace (Matrix.conjTranspose X * (Φ A) * X))
        = Complex.re (Matrix.trace ((Φ A) * (X * Matrix.conjTranspose X))) := by
            calc
              Complex.re (Matrix.trace (Matrix.conjTranspose X * (Φ A) * X))
                  = Complex.re (Matrix.trace ((Matrix.conjTranspose X * (Φ A)) * X)) := by
                      simp [Matrix.mul_assoc]
              _ = Complex.re (Matrix.trace (X * (Matrix.conjTranspose X * (Φ A)))) := by
                    rw [Matrix.trace_mul_comm]
              _ = Complex.re (Matrix.trace ((X * Matrix.conjTranspose X) * (Φ A))) := by
                    simp [Matrix.mul_assoc]
              _ = Complex.re (Matrix.trace ((Φ A) * (X * Matrix.conjTranspose X))) := by
                    rw [Matrix.trace_mul_comm]
    _ = Complex.re (Matrix.trace (A * ((hsAdjoint Φ) (X * Matrix.conjTranspose X)))) := by
          exact (ProofNet.re_trace_mul_hsAdjoint_eq Φ hA.1 hΦA_sa).symm
    _ = Complex.re
          (Matrix.trace
            (A * (((hsAdjoint Φ) X) * Matrix.conjTranspose ((hsAdjoint Φ) X)))) := by
          rw [hmd.1]
    _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose ((hsAdjoint Φ) X) * A * ((hsAdjoint Φ) X))) := by
          calc
            Complex.re
                (Matrix.trace
                  (A * (((hsAdjoint Φ) X) * Matrix.conjTranspose ((hsAdjoint Φ) X))))
                =
              Complex.re
                (Matrix.trace
                  ((((hsAdjoint Φ) X) * Matrix.conjTranspose ((hsAdjoint Φ) X)) * A)) := by
                  rw [Matrix.trace_mul_comm]
            _ = Complex.re
                  (Matrix.trace
                    (((hsAdjoint Φ) X) * (Matrix.conjTranspose ((hsAdjoint Φ) X) * A))) := by
                  simp [Matrix.mul_assoc]
            _ = Complex.re
                  (Matrix.trace
                    ((Matrix.conjTranspose ((hsAdjoint Φ) X) * A) * ((hsAdjoint Φ) X))) := by
                  rw [Matrix.trace_mul_comm]
            _ = Complex.re
                  (Matrix.trace
                    (Matrix.conjTranspose ((hsAdjoint Φ) X) * A * ((hsAdjoint Φ) X))) := by
                  simp [Matrix.mul_assoc]

private theorem hsCfcR_id_jArg {n : ℕ} {A B : Mₙ n}
    (hA : IsSelfAdjoint A) (hB : Matrix.PosDef B) :
    hsCfcR (fun x : ℝ => x) (jArg A B) = jArg A B := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  have hjArg_sa : IsSelfAdjoint (jArg A B) := by
    simpa [hsAdjoint] using jArg_isSelfAdjoint (A := A) (B := B) hA hB
  dsimp [hsCfcR, HansenPedersen.cfcR, LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR]
  simpa using (cfc_id' (R := ℝ) (a := jArg A B) (ha := hjArg_sa))

/-- For the identity function, `J_id(A,B)` reduces to left multiplication by `A`.
Sanity lemma: `J_id(A,B)` for `f(x)=x`; terminology from Hiai,
Definition 6.1. -/
theorem jOperator_id {n : ℕ} {A B : Mₙ n}
    (hA : IsSelfAdjoint A) (hB : Matrix.PosDef B) :
    jOperator (fun x : ℝ => x) A B = leftMul A := by
  have hcfc := hsCfcR_id_jArg (A := A) (B := B) hA hB
  have hBinv : B * B⁻¹ = 1 := by
    rcases Matrix.PosDef.isUnit hB with ⟨u, rfl⟩
    simp
  apply ContinuousLinearMap.ext
  intro X
  calc
    jOperator (fun x : ℝ => x) A B X
        = (jArg A B * rightMul B) X := by
            rw [jOperator, hcfc]
    _ = A * X := by
          simp [ContinuousLinearMap.mul_apply, jArg_apply, Matrix.mul_assoc, hBinv]

/-- The raw multiplicative-domain trace identity, rewritten as equality of the
linear-function `J_x` quadratic forms.
Source: Hiai, proof of Theorem 6.3. -/
theorem quasiEntropy_id_eq_of_multiplicativeDomain :
    ∀ {n m : ℕ} (Φ : HSMap n m) {A B : Mₙ n} {X : Mₙ m},
      IsPositiveMap Φ →
      Matrix.PosDef A →
      Matrix.PosDef B →
      Matrix.PosDef (Φ B) →
      InAdjointMultiplicativeDomain Φ X →
      quasiEntropy (fun x : ℝ => x) (Φ A) (Φ B) X =
        quasiEntropy (fun x : ℝ => x) A B ((hsAdjoint Φ) X) := by
  intro n m Φ A B X hPos hA hB hΦB hmd
  have hΦA_sa : IsSelfAdjoint (Φ A) := by
    have hΦA_nonneg : 0 ≤ Φ A := hPos (Matrix.PosDef.nonneg hA)
    simpa [Matrix.IsHermitian, IsSelfAdjoint] using
      (Matrix.nonneg_iff_posSemidef.mp hΦA_nonneg).1
  have hraw :=
    linear_trace_identity_of_multiplicativeDomain Φ (A := A) (X := X) hPos hA hmd
  calc
    quasiEntropy (fun x : ℝ => x) (Φ A) (Φ B) X
        = Complex.re (Matrix.trace (Matrix.conjTranspose X * (Φ A) * X)) := by
            rw [quasiEntropy, jOperator_id hΦA_sa hΦB]
            simp [Matrix.mul_assoc]
    _ = Complex.re
          (Matrix.trace
            (Matrix.conjTranspose ((hsAdjoint Φ) X) * A * ((hsAdjoint Φ) X))) := hraw
    _ = quasiEntropy (fun x : ℝ => x) A B ((hsAdjoint Φ) X) := by
          rw [quasiEntropy, jOperator_id hA.1 hB]
          simp [Matrix.mul_assoc]

private theorem hsCfcR_affineMinus {n : ℕ} {A B : Mₙ n} {a : ℝ} {ψ : ℝ → ℝ}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    (hψcont : ContinuousOn ψ (Set.Ioi (0 : ℝ))) :
    hsCfcR (fun x : ℝ => a * x - ψ x) (jArg A B) =
      a • hsCfcR (fun x : ℝ => x) (jArg A B) - hsCfcR ψ (jArg A B) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  have hlinear_cont : ContinuousOn (fun x : ℝ => a * x) (spectrum ℝ (jArg A B)) := by
    exact (continuous_const.mul continuous_id).continuousOn
  have hψ_cont_spec : ContinuousOn ψ (spectrum ℝ (jArg A B)) := by
    exact hψcont.mono (spectrum_jArg_subset_Ioi_of_posDef hA hB)
  dsimp [hsCfcR, HansenPedersen.cfcR, LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR]
  calc
    cfc (fun x : ℝ => a * x - ψ x) (jArg A B)
        = cfc (fun x : ℝ => a * x) (jArg A B) - cfc ψ (jArg A B) := by
            simpa using (cfc_sub (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
              (f := fun x : ℝ => a * x) (g := ψ) (a := jArg A B)
              hlinear_cont hψ_cont_spec)
    _ = a • cfc (fun x : ℝ => x) (jArg A B) - cfc ψ (jArg A B) := by
          rw [cfc_const_mul (R := ℝ) (A := HSOp n) (p := IsSelfAdjoint)
            (r := a) (f := fun x : ℝ => x) (a := jArg A B)]

private theorem jOperator_affineMinus {n : ℕ} {A B : Mₙ n} {a : ℝ} {ψ : ℝ → ℝ}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    (hψcont : ContinuousOn ψ (Set.Ioi (0 : ℝ))) :
    jOperator (fun x : ℝ => a * x - ψ x) A B =
      a • jOperator (fun x : ℝ => x) A B - jOperator ψ A B := by
  rw [jOperator, jOperator, jOperator, hsCfcR_affineMinus (A := A) (B := B)
    hA hB hψcont]
  ext X
  simp [ContinuousLinearMap.sub_apply, sub_mul]

private theorem quasiEntropy_affineMinus {n : ℕ} {A B X : Mₙ n} {a : ℝ}
    {ψ : ℝ → ℝ}
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
    (hψcont : ContinuousOn ψ (Set.Ioi (0 : ℝ))) :
    quasiEntropy (fun x : ℝ => a * x - ψ x) A B X =
      a * quasiEntropy (fun x : ℝ => x) A B X - quasiEntropy ψ A B X := by
  rw [quasiEntropy, quasiEntropy, quasiEntropy, jOperator_affineMinus (A := A) (B := B)
    hA hB hψcont]
  have hscale :
      (Matrix.trace
          (Matrix.conjTranspose X * ((a • jOperator (fun x : ℝ => x) A B) X))).re =
        a * (Matrix.trace
          (Matrix.conjTranspose X * ((jOperator (fun x : ℝ => x) A B) X))).re := by
    let J : HSOp n := jOperator (fun x : ℝ => x) A B
    let M : Mₙ n := Matrix.conjTranspose X * (J X)
    have hmul : Matrix.conjTranspose X * ((a • J) X) = (a : ℝ) • M := by
      change Matrix.conjTranspose X * ((a : ℝ) • (J X)) = (a : ℝ) • M
      ext i j
      simp only [M, Matrix.mul_apply, Matrix.smul_apply]
      change (∑ k, Matrix.conjTranspose X i k * ((a : ℂ) * J X k j)) =
        (a : ℂ) * (∑ k, Matrix.conjTranspose X i k * J X k j)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have htrace : Matrix.trace ((a : ℝ) • M) = (a : ℂ) * Matrix.trace M := by
      change (∑ i, Matrix.diag ((a : ℝ) • M) i) =
        (a : ℂ) * (∑ i, Matrix.diag M i)
      change (∑ i, (a : ℂ) * Matrix.diag M i) =
        (a : ℂ) * (∑ i, Matrix.diag M i)
      rw [Finset.mul_sum]
    calc
      (Matrix.trace
          (Matrix.conjTranspose X * ((a • jOperator (fun x : ℝ => x) A B) X))).re =
          (Matrix.trace ((a : ℝ) • M)).re := by
            rw [hmul]
      _ = ((a : ℂ) * Matrix.trace M).re := by
            rw [htrace]
      _ = a * (Matrix.trace
          (Matrix.conjTranspose X * ((jOperator (fun x : ℝ => x) A B) X))).re := by
            simp [M, J]
  rw [ContinuousLinearMap.sub_apply, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hscale]

private theorem quasiEntropy_direct_of_operatorMonotone {n m : ℕ} (Φ : HSMap n m)
    {ψ : ℝ → ℝ} {A B : Mₙ n} {X : Mₙ m}
    (hψcont : ContinuousOn ψ (Set.Ioi (0 : ℝ)))
    (hψpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < ψ x)
    (hψI : QuasiEntropyDataProcessing.AllHOperatorMonotoneOnIoi ψ)
    (hPos : IsPositiveMap Φ) (hTrace : TracePreserving Φ) (hSch : HSAdjointSchwarz Φ)
    (hA : Matrix.PosDef A) (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ (1 : Mₙ n))) :
    quasiEntropy ψ A B ((hsAdjoint Φ) X) ≤ quasiEntropy ψ (Φ A) (Φ B) X := by
  have hImat : ProofNet.MatrixMonotone ψ :=
    ProofNet.matrixMonotoneCondition_of_allHOperatorMonotoneOnIoi hψI
  have hEquivalences := ProofNet.strictDPIEquivalences (f := ψ) hψcont hψpos
  have hIII : ProofNet.StrictDirectDPI ψ :=
    hEquivalences.strictInverseDPI_iff_strictDirectDPI.mp
      (hEquivalences.matrixMonotone_iff_strictInverseDPI.mp hImat)
  have hHS :
      (show HSOp m from Φ.comp ((jOperator ψ A B).comp (hsAdjoint Φ))) ≤
        (jOperator ψ (Φ A) (Φ B)) :=
    hIII Φ (A := A) (B := B) hPos hTrace hSch hA hB hΦ1
  have hq :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((Φ.comp ((jOperator ψ A B).comp (hsAdjoint Φ))) X))) ≤
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((jOperator ψ (Φ A) (Φ B)) X))) := by
    exact hsQForm_le_of_le hHS X
  have hsource :
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((Φ.comp ((jOperator ψ A B).comp (hsAdjoint Φ))) X))) =
        quasiEntropy ψ A B ((hsAdjoint Φ) X) := by
    calc
      Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((Φ.comp ((jOperator ψ A B).comp (hsAdjoint Φ))) X)))
          =
        Complex.re
          (Matrix.trace
            (Matrix.conjTranspose ((hsAdjoint Φ) X) *
              ((jOperator ψ A B) ((hsAdjoint Φ) X)))) := by
            simpa using hsQForm_comp_hsAdjoint Φ (jOperator ψ A B) X
      _ = quasiEntropy ψ A B ((hsAdjoint Φ) X) := by
            rfl
  calc
    quasiEntropy ψ A B ((hsAdjoint Φ) X)
        = Complex.re
            (Matrix.trace
              (Matrix.conjTranspose X *
                ((Φ.comp ((jOperator ψ A B).comp (hsAdjoint Φ))) X))) := hsource.symm
    _ ≤ Complex.re
          (Matrix.trace
            (Matrix.conjTranspose X *
              ((jOperator ψ (Φ A) (Φ B)) X))) := hq
    _ = quasiEntropy ψ (Φ A) (Φ B) X := by
          rfl

/-- The direct inequality for `a x - ψ(x)` follows by combining the linear `J_x`
identity with the direct Hiai--Petz inequality for the operator-monotone positive
function `ψ`.
Source: Hiai, proof of Theorem 6.3. -/
theorem quasiEntropy_affineMinus_map_le_of_operatorMonotone :
    ∀ {n m : ℕ} (Φ : HSMap n m) {a : ℝ} {ψ : ℝ → ℝ} {A B : Mₙ n} {X : Mₙ m},
      ContinuousOn ψ (Set.Ioi (0 : ℝ)) →
      (∀ x ∈ Set.Ioi (0 : ℝ), 0 < ψ x) →
      QuasiEntropyDataProcessing.AllHOperatorMonotoneOnIoi ψ →
      IsPositiveMap Φ →
      TracePreserving Φ →
      HSAdjointSchwarz Φ →
      Matrix.PosDef A →
      Matrix.PosDef B →
      Matrix.PosDef (Φ (1 : Mₙ n)) →
      Matrix.PosDef (Φ B) →
      InAdjointMultiplicativeDomain Φ X →
      quasiEntropy (fun x : ℝ => a * x - ψ x) (Φ A) (Φ B) X ≤
        quasiEntropy (fun x : ℝ => a * x - ψ x) A B ((hsAdjoint Φ) X) := by
  intro n m Φ a ψ A B X hψcont hψpos hψI hPos hTrace hSch hA hB hΦ1 hΦB hmd
  have hΦA : Matrix.PosDef (Φ A) :=
    Matrix.PosDef.image_of_isPositiveMap Φ hPos hA hΦ1
  have hψineq :
      quasiEntropy ψ A B ((hsAdjoint Φ) X) ≤ quasiEntropy ψ (Φ A) (Φ B) X :=
    quasiEntropy_direct_of_operatorMonotone Φ (ψ := ψ) (A := A) (B := B) (X := X)
      hψcont hψpos hψI hPos hTrace hSch hA hB hΦ1
  have hlin :
      quasiEntropy (fun x : ℝ => x) (Φ A) (Φ B) X =
        quasiEntropy (fun x : ℝ => x) A B ((hsAdjoint Φ) X) :=
    quasiEntropy_id_eq_of_multiplicativeDomain Φ (A := A) (B := B) (X := X)
      hPos hA hB hΦB hmd
  rw [quasiEntropy_affineMinus (A := Φ A) (B := Φ B) (X := X)
      (a := a) (ψ := ψ) hΦA hΦB hψcont,
    quasiEntropy_affineMinus (A := A) (B := B) (X := (hsAdjoint Φ) X)
      (a := a) (ψ := ψ) hA hB hψcont]
  have hlinmul :
      a * quasiEntropy (fun x : ℝ => x) (Φ A) (Φ B) X =
        a * quasiEntropy (fun x : ℝ => x) A B ((hsAdjoint Φ) X) := by
    exact congrArg (fun t : ℝ => a * t) hlin
  linarith


end MatrixScopedInstances

end TraceMonotonicity

end HiaiPetz
