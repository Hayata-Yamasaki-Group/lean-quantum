/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.ConditionVocabulary
import Quantum.TraceInequality.HansenPedersen.QuasiEntropyDataProcessing.OutputSupport.Bridge
-- Provides `List.TFAE`, `tfae_have`, and `tfae_finish` for the book-facing surfaces.
import Mathlib.Tactic.TFAE
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Model.MatrixCorner
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Reduction.Basic
import Quantum.TraceInequality.HiaiPetz.QuasiEntropyDataProcessing.OutputSupport.Reduction.Map
import Quantum.TraceInequality.HiaiPetz.Support
import Quantum.TraceInequality.HiaiPetz.Support.Corner
import Quantum.TraceInequality.HiaiPetzTheorem.Reduction.ReducedMap

/-!
# Book-facing output-support surface for Theorem 6.2

Public support-corner formulation of conditions `(ii)` and `(iii)` of Hiai--Petz Theorem 6.2,
proved equivalent to the internal reduced-map formulations built from a fixed orthonormal
matrix realization of the support corner, together with the general-output main characterization
theorem `outputSupport_characterizations`.
-/

namespace HiaiPetz

namespace QuasiEntropyDataProcessing

open scoped MatrixOrder ComplexOrder
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/-- General `(ii)` in the internal reduced-map formulation, quantified over all maps.
Source: Hiai, Theorem 6.2, condition (ii) = (6.3). -/
def ReducedMapInverseInequality (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m), ReducedMapInverseInequalityAt f Φ

namespace ReducedMapInverseInequality

/-- Specialize the all-map inverse inequality to a fixed Hilbert--Schmidt map.
Source: Hiai, Theorem 6.2, condition (ii) = (6.3). -/
theorem apply {f : ℝ → ℝ} (h : ReducedMapInverseInequality f)
    {n m : ℕ} (Φ : HSMap n m) :
    ReducedMapInverseInequalityAt f Φ :=
  h Φ

end ReducedMapInverseInequality

/-- Build the all-map inverse inequality from its fixed-map form.
Local API: one-line wrapper; terminology from Hiai, Theorem 6.2,
condition (ii) = (6.3). -/
theorem reducedMapInverseInequality_of_at {f : ℝ → ℝ}
    (h : ∀ {n m : ℕ} (Φ : HSMap n m), ReducedMapInverseInequalityAt f Φ) :
    ReducedMapInverseInequality f :=
  h

/-- General `(iii)` in the internal reduced-map formulation, quantified over all maps.
Source: Hiai, Theorem 6.2, condition (iii) = (6.4). -/
def ReducedMapDirectInequality (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m), ReducedMapDirectInequalityAt f Φ

namespace ReducedMapDirectInequality

/-- Specialize the all-map direct inequality to a fixed Hilbert--Schmidt map.
Source: Hiai, Theorem 6.2, condition (iii) = (6.4). -/
theorem apply {f : ℝ → ℝ} (h : ReducedMapDirectInequality f)
    {n m : ℕ} (Φ : HSMap n m) :
    ReducedMapDirectInequalityAt f Φ :=
  h Φ

end ReducedMapDirectInequality

/-- Build the all-map direct inequality from its fixed-map form.
Local API: one-line wrapper; terminology from Hiai, Theorem 6.2,
condition (iii) = (6.4). -/
theorem reducedMapDirectInequality_of_at {f : ℝ → ℝ}
    (h : ∀ {n m : ℕ} (Φ : HSMap n m), ReducedMapDirectInequalityAt f Φ) :
    ReducedMapDirectInequality f :=
  h

/-- Book-facing general condition `(ii)`: the inverse inequality for an arbitrary positive
trace-preserving map whose Hilbert--Schmidt adjoint is a Schwarz map, with the output read
through the reduced map on a fixed orthonormal matrix realization of the support corner.
Source: Hiai, Theorem 6.2, condition (ii) = (6.3). -/
def OutputSupportInverseInequality (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m),
    ∀ {A B : Mₙ n},
      (hPos : IsPositiveMap Φ) →
      TracePreserving Φ →
      HSAdjointSchwarz Φ →
      Matrix.PosDef A →
      Matrix.PosDef B →
      let Ψ := outputSupportReducedHSMap Φ hPos
      (show HSOp n from
        (hsAdjoint Ψ).comp ((jOperatorInv f (Ψ A) (Ψ B)).comp Ψ)) ≤
        (jOperatorInv f A B)

/-- Book-facing general condition `(iii)`: the direct inequality for an arbitrary positive
trace-preserving map whose Hilbert--Schmidt adjoint is a Schwarz map, with the output read
through the reduced map on a fixed orthonormal matrix realization of the support corner.
Source: Hiai, Theorem 6.2, condition (iii) = (6.4). -/
def OutputSupportDirectInequality (f : ℝ → ℝ) : Prop :=
  ∀ {n m : ℕ} (Φ : HSMap n m),
    ∀ {A B : Mₙ n},
      (hPos : IsPositiveMap Φ) →
      TracePreserving Φ →
      HSAdjointSchwarz Φ →
      Matrix.PosDef A →
      Matrix.PosDef B →
      let Ψ := outputSupportReducedHSMap Φ hPos
      (show HSOp (outputSupportMatrixCornerModel Φ).dim from
        Ψ.comp ((jOperator f A B).comp (hsAdjoint Ψ))) ≤
        (jOperator f (Ψ A) (Ψ B))

/-- The book-facing support-corner formulation of general `(ii)` is equivalent to its
internal reduced-map formulation. -/
theorem outputSupportInverseInequality_iff_reducedMap (f : ℝ → ℝ) :
    OutputSupportInverseInequality f ↔ ReducedMapInverseInequality f := by
  constructor
  · intro hII
    refine reducedMapInverseInequality_of_at ?_
    intro n m Φ A B hPos hTrace hSch hA hB
    simpa [ReducedMapInverseInequalityAt, outputSupportReducedHSMap] using
      (hII Φ (A := A) (B := B) hPos hTrace hSch hA hB)
  · intro hII n m Φ A B hPos hTrace hSch hA hB
    simpa [ReducedMapInverseInequalityAt, outputSupportReducedHSMap] using
      (hII.apply Φ (A := A) (B := B) hPos hTrace hSch hA hB)

/-- The book-facing support-corner formulation of general `(iii)` is equivalent to its
internal reduced-map formulation. -/
theorem outputSupportDirectInequality_iff_reducedMap (f : ℝ → ℝ) :
    OutputSupportDirectInequality f ↔ ReducedMapDirectInequality f := by
  constructor
  · intro hIII
    refine reducedMapDirectInequality_of_at ?_
    intro n m Φ A B hPos hTrace hSch hA hB
    simpa [ReducedMapDirectInequalityAt, outputSupportReducedHSMap] using
      (hIII Φ (A := A) (B := B) hPos hTrace hSch hA hB)
  · intro hIII n m Φ A B hPos hTrace hSch hA hB
    simpa [ReducedMapDirectInequalityAt, outputSupportReducedHSMap] using
      (hIII.apply Φ (A := A) (B := B) hPos hTrace hSch hA hB)

/-- Internal proof package for the general-output route. This bundles the reduced-map
theorem head for a fixed orthonormal matrix realization of the support corner by combining the
bridge lemmas with the remaining strict-output steps.
Source: Hiai, Theorem 6.2. -/
theorem reducedMap_characterizations {f : ℝ → ℝ} :
    ContinuousOn f (Set.Ioi (0 : ℝ)) →
    (∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) →
      (AllHOperatorMonotoneOnIoi f → ReducedMapDirectInequality f) ∧
      (ReducedMapInverseInequality f ↔ ReducedMapDirectInequality f) ∧
      (ReducedMapDirectInequality f → JointConcavity f) ∧
      (JointConcavity f → MatrixMonotoneCondition f) ∧
      (MatrixMonotoneCondition f → AllHOperatorMonotoneOnIoi f) := by
  intro hf hposf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hI
    exact reducedMapDirectInequality_of_at fun Φ =>
      reducedMapDirectInequalityAt_of_operatorMonotone f hf hposf hI Φ
  · constructor
    · intro hII
      exact reducedMapDirectInequality_of_at fun Φ =>
        (reducedMapInverseInequalityAt_iff_directInequalityAt f hf hposf Φ).1 (hII.apply Φ)
    · intro hIII
      exact reducedMapInverseInequality_of_at fun Φ =>
        (reducedMapInverseInequalityAt_iff_directInequalityAt f hf hposf Φ).2 (hIII.apply Φ)
  · intro hIII
    exact jointConcavity_of_reducedMapDirectInequality f hf hIII
  · exact matrixMonotone_of_jointConcavity f hf hposf
  · exact HiaiPetz.MatrixFunctionalCalculus.allHOperatorMonotoneOnIoi_of_matrixMonotoneCondition hf


/-- Public-facing main theorem for the general-output layer of Theorem 6.2. Readers should use
this book-facing statement, whose conditions `(ii)` and `(iii)` are phrased with the support-corner
notation. The proof still reuses the internal reduced-map package and only
transports `(ii)` / `(iii)` through the established equivalences with
`OutputSupportInverseInequality` / `OutputSupportDirectInequality`.
The public entry points are the `ProofNet.*` declarations; `outputSupport_characterizations_tfae`
is an auxiliary TFAE form of this statement.
Source: Hiai, Theorem 6.2. -/
theorem outputSupport_characterizations {f : ℝ → ℝ} :
    ContinuousOn f (Set.Ioi (0 : ℝ)) →
    (∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) →
      (AllHOperatorMonotoneOnIoi f → OutputSupportDirectInequality f) ∧
      (OutputSupportInverseInequality f ↔ OutputSupportDirectInequality f) ∧
      (OutputSupportDirectInequality f → JointConcavity f) ∧
      (JointConcavity f → MatrixMonotoneCondition f) ∧
      (MatrixMonotoneCondition f → AllHOperatorMonotoneOnIoi f) := by
  intro hf hposf
  rcases reducedMap_characterizations (f := f) hf hposf with
    ⟨hItoIII, hIIiffIII, hIIItoIV, hIVtoI_matrix, hI_matrix_toI⟩
  refine ⟨?_, ?_, ?_, hIVtoI_matrix, hI_matrix_toI⟩
  · intro hI
    exact (outputSupportDirectInequality_iff_reducedMap f).2 (hItoIII hI)
  · constructor
    · intro hIIbook
      exact (outputSupportDirectInequality_iff_reducedMap f).2
        (hIIiffIII.1 ((outputSupportInverseInequality_iff_reducedMap f).1 hIIbook))
    · intro hIIIbook
      exact (outputSupportInverseInequality_iff_reducedMap f).2
        (hIIiffIII.2 ((outputSupportDirectInequality_iff_reducedMap f).1 hIIIbook))
  · intro hIIIbook
    exact hIIItoIV ((outputSupportDirectInequality_iff_reducedMap f).1 hIIIbook)

/-- The four unprimed book-facing conditions of Hiai Theorem 6.2 are equivalent on the
output-support surface.

The source theorem does not assume continuity; this implementation through the continuous
functional calculus assumes `hf`. -/
theorem outputSupport_characterizations_tfae {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    List.TFAE [
      AllHOperatorMonotoneOnIoi f,
      OutputSupportInverseInequality f,
      OutputSupportDirectInequality f,
      JointConcavity f
    ] := by
  rcases outputSupport_characterizations (f := f) hf hpos with
    ⟨hItoIII, hIIiffIII, hIIItoIV, hIVtoImat, hImatToI⟩
  tfae_have 1 → 3 := hItoIII
  tfae_have 2 ↔ 3 := hIIiffIII
  tfae_have 3 → 4 := hIIItoIV
  tfae_have 4 → 1 := fun hIV => hImatToI (hIVtoImat hIV)
  tfae_finish

/-- Extended general-output characterization adding the matrix-monotone bridge condition
to the four unprimed book-facing conditions.

The source theorem does not assume continuity; this implementation through the continuous
functional calculus assumes `hf`. -/
theorem outputSupport_characterizations_tfae_with_matrix {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < f x) :
    List.TFAE [
      AllHOperatorMonotoneOnIoi f,
      OutputSupportInverseInequality f,
      OutputSupportDirectInequality f,
      JointConcavity f,
      MatrixMonotoneCondition f
    ] := by
  rcases outputSupport_characterizations (f := f) hf hpos with
    ⟨hItoIII, hIIiffIII, hIIItoIV, hIVtoImat, hImatToI⟩
  tfae_have 1 → 3 := hItoIII
  tfae_have 2 ↔ 3 := hIIiffIII
  tfae_have 3 → 4 := hIIItoIV
  tfae_have 4 → 5 := hIVtoImat
  tfae_have 5 → 1 := hImatToI
  tfae_finish

end MatrixScopedInstances

end QuasiEntropyDataProcessing

end HiaiPetz
