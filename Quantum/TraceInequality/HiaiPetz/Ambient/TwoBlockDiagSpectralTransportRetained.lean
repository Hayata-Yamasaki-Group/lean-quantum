/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagJOperator
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Operator.CompleteCodomain
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Quantum.TraceInequality.HansenPedersen.AmbientSubmodule.JOperatorInequalities
import Quantum.TraceInequality.HiaiPetz.Ambient.TwoBlockDiagSpectralTransport

/-!
# Spectral transport for two-block restricted operators

This file transports spectral and self-adjointness facts for the restricted
two-block diagonal and off-diagonal `J` arguments through the block-submodule
equivalences.  These facts supply the continuity hypotheses needed by the
orthogonal CFC transport layer.

## Main results

* `finite_real_spectrum_of_selfAdjoint`: finite-dimensional self-adjoint
  endomorphisms have finite real spectrum.
* `twoBlockDiagRestrictedJArg_isSelfAdjoint` and
  `offDiagRestrictedJArg_isSelfAdjoint`: self-adjointness of the restricted
  `J` arguments.
* `twoBlockDiagSubmoduleIsometry_rightMul` and
  `offDiagSubmoduleIsometry_rightMul`: right multiplication transported to the
  `WithLp` pair model.

## References

* Hiai, spectral-control step for the blockwise `J`-operator CFC
  reduction.
-/

namespace HiaiPetz

open scoped MatrixOrder Matrix.Norms.Frobenius

open scoped ComplexOrder

open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

/- Instance caches: `spectrum ℝ` / `AlgEquiv.spectrum_eq` on the transported
operator algebras below repeatedly trigger the deep `Algebra ℝ _` derivation
through `NormedAlgebra.complexToReal`, re-run at every use site. Section-level
reducible local instances turn each search into
a head-match; `@[reducible]` keeps the aliases transparent so statements stay
syntactically compatible with Mathlib lemmas.

For the continuous-linear-map endomorphism algebras the raw `Algebra ℝ _`
search dead-ends through the large population of non-matching candidates
before reaching the restriction-of-scalars route (times out even at 20x the
default budget); naming the head (`Algebra.complexToReal`, resp. its normed
refinement) leaves only cheap subgoals found within the default budget. -/

/-- Local reducible real algebra cache for endomorphisms of the two-block
diagonal submodule. -/
@[reducible, local instance]
private noncomputable def instAlgebraRealTwoBlockDiagCLMScoped {n : ℕ} :
    Algebra ℝ (↥(twoBlockDiagSubmodule n) →L[ℂ] ↥(twoBlockDiagSubmodule n)) :=
  Algebra.complexToReal

/-- Local reducible real algebra cache for endomorphisms of the off-diagonal
submodule. -/
@[reducible, local instance]
private noncomputable def instAlgebraRealOffDiagCLMScoped {n : ℕ} :
    Algebra ℝ (↥(offDiagSubmodule n) →L[ℂ] ↥(offDiagSubmodule n)) :=
  Algebra.complexToReal

-- One-time search for the cache itself; every later use is a head-match.
/-- Local reducible real algebra cache for Hilbert-Schmidt operators. -/
@[reducible, local instance]
private noncomputable def instAlgebraRealHSOpScoped {n : ℕ} :
    Algebra ℝ (HSOp n) :=
  inferInstance

private theorem spectrum_twoBlockDiagRestrictedJArg_subset_union {n : ℕ}
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    spectrum ℝ
        (twoBlockDiagRestrictedJArg
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) ⊆
      spectrum ℝ (jArg A₁ B₁) ∪ spectrum ℝ (jArg A₂ B₂) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  letI : CompleteSpace ↥(twoBlockDiagSubmodule n) := instTwoBlockDiagSubtypeCompleteSpace (n := n)
  let Ψ₀ :
      (HSOp n × HSOp n) →⋆ₐ[ℂ]
        ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) :=
    @HansenPedersen.Internal.diagStarAlgHom (Mₙ n)
      (instMatrixNormedAddCommGroup (n := n))
      (instMatrixInnerProductSpace (n := n))
      (instMatrixCompleteSpace (n := n))
      (Mₙ n)
      (instMatrixNormedAddCommGroup (n := n))
      (instMatrixInnerProductSpace (n := n))
      (instMatrixCompleteSpace (n := n))
  have h : twoBlockDiagSubmoduleConjStarAlgEquiv n
      (twoBlockDiagRestrictedJArg
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) =
      Ψ₀ (jArg A₁ B₁, jArg A₂ B₂) := by
    rw [twoBlockDiagSubmoduleIsometry_jArg (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁)
      (B₂ := B₂) hB₁ hB₂]
    rfl
  exact spectrum_real_subset_union_of_eq_pairHom (twoBlockDiagSubmoduleConjStarAlgEquiv n) Ψ₀ h

@[fun_prop] private theorem continuousOn_twoBlockDiagRestrictedJArg {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    ContinuousOn f
      (spectrum ℝ
        (twoBlockDiagRestrictedJArg
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)) := by
  exact (continuousOn_jArg_union (f := f) hf hA₁ hA₂ hB₁ hB₂).mono
    (spectrum_twoBlockDiagRestrictedJArg_subset_union (A₁ := A₁) (A₂ := A₂)
      (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)

@[fun_prop] theorem continuousOn_offDiagRestrictedJArg {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    ContinuousOn f
      (spectrum ℝ
        (offDiagRestrictedJArg
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)) := by
  exact (continuousOn_jArg_union (f := f) hf hA₁ hA₂ hB₂ hB₁).mono
    (spectrum_offDiagRestrictedJArg_subset_union (A₁ := A₁) (A₂ := A₂)
      (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)

end MatrixScopedInstances

end HiaiPetz
