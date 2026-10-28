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
import Quantum.TraceInequality.HiaiPetz.Core.JOperatorPositivity

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

/-- Local reducible real algebra cache for endomorphisms of the orthogonal
complement of the two-block diagonal submodule. -/
@[reducible, local instance]
private noncomputable def instAlgebraRealTwoBlockDiagOrthCLMScoped {n : ℕ} :
    Algebra ℝ
      (↥(twoBlockDiagOrthogonalSubmodule n) →L[ℂ] ↥(twoBlockDiagOrthogonalSubmodule n)) :=
  Algebra.complexToReal

-- One-time search for the cache itself; every later use is a head-match.
/-- Local reducible real algebra cache for Hilbert-Schmidt operators. -/
@[reducible, local instance]
private noncomputable def instAlgebraRealHSOpScoped {n : ℕ} :
    Algebra ℝ (HSOp n) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Local reducible real algebra cache for pairs of Hilbert-Schmidt operators. -/
@[reducible, local instance]
private noncomputable def instAlgebraRealHSOpProdScoped {n : ℕ} :
    Algebra ℝ (HSOp n × HSOp n) :=
  inferInstance

/-- Local reducible real algebra cache for endomorphisms of the `WithLp`
matrix-pair model. -/
@[reducible, local instance]
private noncomputable def instAlgebraRealWithLpPairCLMScoped {n : ℕ} :
    Algebra ℝ
      ((WithLp 2 (Mₙ n × Mₙ n)) →L[ℂ] (WithLp 2 (Mₙ n × Mₙ n))) :=
  NormedAlgebra.complexToReal.toAlgebra

/-- Real spectrum of the image of a pair under a star-algebra homomorphism out of a
product of C⋆-algebras (abstract form, so that the instance search stays cheap). -/
private theorem spectrum_real_pairHom_subset_union
    {A B Y : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra Y]
    (Ψ : (A × B) →⋆ₐ[ℂ] Y) (a : A) (b : B) :
    spectrum ℝ (Ψ (a, b)) ⊆ spectrum ℝ a ∪ spectrum ℝ b := by
  letI : IsScalarTower ℝ ℂ A := RestrictScalars.isScalarTower ℝ ℂ A
  letI : IsScalarTower ℝ ℂ B := RestrictScalars.isScalarTower ℝ ℂ B
  letI : IsScalarTower ℝ ℂ Y := RestrictScalars.isScalarTower ℝ ℂ Y
  letI : IsScalarTower ℝ ℂ (A × B) := Prod.isScalarTower
  rw [← Prod.spectrum_eq]
  exact AlgHom.spectrum_apply_subset (Ψ.restrictScalars ℝ) (a, b)

/-- If a star-algebra equivalence sends `T` to the image of a pair `(a, b)`, the real
spectrum of `T` lies in the union of the real spectra of `a` and `b`. -/
theorem spectrum_real_subset_union_of_eq_pairHom
    {X : Type*} [Ring X] [Algebra ℂ X] [Star X]
    {A B Y : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra Y]
    (Φ : X ≃⋆ₐ[ℂ] Y) (Ψ : (A × B) →⋆ₐ[ℂ] Y) {T : X} {a : A} {b : B}
    (h : Φ T = Ψ (a, b)) :
    spectrum ℝ T ⊆ spectrum ℝ a ∪ spectrum ℝ b := by
  letI : IsScalarTower ℝ ℂ X := RestrictScalars.isScalarTower ℝ ℂ X
  letI : IsScalarTower ℝ ℂ Y := RestrictScalars.isScalarTower ℝ ℂ Y
  have hs : spectrum ℝ (Φ T) = spectrum ℝ T :=
    AlgEquiv.spectrum_eq ((Φ : X ≃ₐ[ℂ] Y).restrictScalars ℝ) T
  rw [← hs, h]
  exact spectrum_real_pairHom_subset_union Ψ a b

/-- If a star-algebra equivalence sends `T` to the image of a pair of self-adjoint
elements with positive real spectra, the complex spectrum of `T` lies on the positive
real axis. -/
private theorem spectrum_complex_subset_ofReal_Ioi_of_eq_pairHom
    {X : Type*} [Ring X] [Algebra ℂ X] [Star X]
    {A B Y : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra Y]
    (Φ : X ≃⋆ₐ[ℂ] Y) (Ψ : (A × B) →⋆ₐ[ℂ] Y) {T : X} {a : A} {b : B}
    (h : Φ T = Ψ (a, b)) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hσa : spectrum ℝ a ⊆ Set.Ioi 0) (hσb : spectrum ℝ b ⊆ Set.Ioi 0) :
    spectrum ℂ T ⊆ Complex.ofReal '' Set.Ioi (0 : ℝ) := by
  have hsa : IsSelfAdjoint (Ψ (a, b)) := (show IsSelfAdjoint (a, b) from Prod.ext ha hb).map Ψ
  have hreal : spectrum ℝ (Ψ (a, b)) ⊆ Set.Ioi 0 := fun x hx =>
    (spectrum_real_pairHom_subset_union Ψ a b hx).elim (fun h => hσa h) (fun h => hσb h)
  have hs : spectrum ℂ (Φ T) = spectrum ℂ T := AlgEquiv.spectrum_eq (Φ : X ≃ₐ[ℂ] Y) T
  rw [← hs, h]
  letI : IsScalarTower ℝ ℂ Y := RestrictScalars.isScalarTower ℝ ℂ Y
  intro z hz
  rw [← hsa.spectrumRestricts.algebraMap_image] at hz
  rcases hz with ⟨x, hx, rfl⟩
  exact ⟨x, hreal hx, rfl⟩

theorem spectrum_offDiagRestrictedJArg_subset_union {n : ℕ}
    {A₁ A₂ B₁ B₂ : Mₙ n} (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    spectrum ℝ
        (offDiagRestrictedJArg
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) ⊆
      spectrum ℝ (jArg A₁ B₂) ∪ spectrum ℝ (jArg A₂ B₁) := by
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  letI : CompleteSpace ↥(offDiagSubmodule n) := instOffDiagSubtypeCompleteSpace (n := n)
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
  have h : offDiagSubmoduleConjStarAlgEquiv n
      (offDiagRestrictedJArg
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) =
      Ψ₀ (jArg A₁ B₂, jArg A₂ B₁) := by
    rw [offDiagSubmoduleIsometry_jArg (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁)
      (B₂ := B₂) hB₁ hB₂]
    rfl
  exact spectrum_real_subset_union_of_eq_pairHom (offDiagSubmoduleConjStarAlgEquiv n) Ψ₀ h

private theorem complex_spectrum_subset_of_real_Ioi
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [ContinuousFunctionalCalculus ℝ (K →L[ℂ] K) IsSelfAdjoint]
    {T : K →L[ℂ] K} (hT : IsSelfAdjoint T)
    (hσ : spectrum ℝ T ⊆ Set.Ioi (0 : ℝ)) :
    spectrum ℂ T ⊆ Complex.ofReal '' Set.Ioi (0 : ℝ) := by
  intro z hz
  by_cases hnt : Nontrivial (K →L[ℂ] K)
  · letI : Nontrivial (K →L[ℂ] K) := hnt
    rw [← hT.spectrumRestricts.algebraMap_image] at hz
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨x, hσ hx, rfl⟩
  · have hsub : Subsingleton (K →L[ℂ] K) := not_nontrivial_iff_subsingleton.mp hnt
    have hs : spectrum ℂ T = ∅ := spectrum.of_subsingleton (R := ℂ) T
    simp at hz

private theorem finite_spectrum_clm
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] (T : E →L[𝕜] E) :
    Set.Finite (spectrum 𝕜 T) := by
  let e : (E →ₗ[𝕜] E) ≃ₐ[𝕜] (E →L[𝕜] E) := Module.End.toContinuousLinearMap E
  have hspec : spectrum 𝕜 T = spectrum 𝕜 (e.symm T) := by
    simp
  rw [hspec]
  exact Module.End.finite_spectrum (e.symm T)

@[fun_prop] private theorem continuousOn_spectrum_clm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : ℝ → ℝ) (T : E →L[ℝ] E) :
    ContinuousOn f (spectrum ℝ T) :=
  (finite_spectrum_clm (𝕜 := ℝ) T).continuousOn f

@[fun_prop] private theorem continuousOn_complex_ofReal_Ioi {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ))) :
    ContinuousOn (fun z : ℂ => ((f z.re : ℝ) : ℂ)) (Complex.ofReal '' Set.Ioi (0 : ℝ)) := by
  have hreal :
      ContinuousOn (fun z : ℂ => f z.re) (Complex.ofReal '' Set.Ioi (0 : ℝ)) := by
    refine hf.comp Complex.continuous_re.continuousOn ?_
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    simpa using hx
  have hof :
      ContinuousOn (fun x : ℝ => ((x : ℝ) : ℂ)) (Set.univ : Set ℝ) :=
    Complex.continuous_ofReal.continuousOn
  simpa using hof.comp hreal (by
    intro z hz
    simp)

/-- In finite complex dimension, a self-adjoint continuous linear endomorphism
has finite real spectrum. -/
theorem finite_real_spectrum_of_selfAdjoint
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [FiniteDimensional ℂ K]
    [ContinuousFunctionalCalculus ℂ (K →L[ℂ] K) IsStarNormal]
    {T : K →L[ℂ] K} (hT : IsSelfAdjoint T) :
    Set.Finite (spectrum ℝ T) := by
  have hσc : Set.Finite (spectrum ℂ T) :=
    finite_spectrum_clm (𝕜 := ℂ) T
  have himage : Set.Finite (((fun x : ℝ => (x : ℂ)) '' spectrum ℝ T)) := by
    simpa only [show (fun x : ℝ => (x : ℂ)) = algebraMap ℝ ℂ by rfl] using
      (hT.spectrumRestricts.algebraMap_image.symm ▸ hσc)
  simpa [Set.preimage_image_eq _ Complex.ofReal_injective] using
    himage.preimage (Set.injOn_of_injective Complex.ofReal_injective)

/-- Transporting right multiplication on the diagonal submodule to the
`WithLp` pair model gives the diagonal map with entries `rightMul B₁` and
`rightMul B₂`. -/
theorem twoBlockDiagSubmoduleIsometry_rightMul {n : ℕ} {B₁ B₂ : Mₙ n} :
    twoBlockDiagSubmoduleConjStarAlgEquiv n
        (twoBlockDiagRestrictedRightMul (n := n) (B₁ := B₁) (B₂ := B₂)) =
      @HansenPedersen.Internal.diagMapCLM (Mₙ n)
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixInnerProductSpace (n := n))
        (Mₙ n)
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixInnerProductSpace (n := n))
        (rightMul B₁) (rightMul B₂) := by
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  simpa [LinearIsometryEquiv.conjStarAlgEquiv_apply] using
    twoBlockDiagSubmoduleEquiv_rightMul (n := n) (B₁ := B₁) (B₂ := B₂)

/-- Transporting right multiplication on the off-diagonal submodule to the
`WithLp` pair model gives the diagonal map with mixed entries `rightMul B₂` and
`rightMul B₁`. -/
theorem offDiagSubmoduleIsometry_rightMul {n : ℕ} {B₁ B₂ : Mₙ n} :
    offDiagSubmoduleConjStarAlgEquiv n
        (offDiagRestrictedRightMul (n := n) (B₁ := B₁) (B₂ := B₂)) =
      @HansenPedersen.Internal.diagMapCLM (Mₙ n)
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixInnerProductSpace (n := n))
        (Mₙ n)
        (instMatrixNormedAddCommGroup (n := n))
        (instMatrixInnerProductSpace (n := n))
        (rightMul B₂) (rightMul B₁) := by
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  simpa [LinearIsometryEquiv.conjStarAlgEquiv_apply] using
    offDiagSubmoduleEquiv_rightMul (n := n) (B₁ := B₁) (B₂ := B₂)

/-- The diagonal restriction of the two-block `J` argument is self-adjoint when
the two `A` blocks are self-adjoint and the two `B` blocks are positive
definite. -/
theorem twoBlockDiagRestrictedJArg_isSelfAdjoint {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    IsSelfAdjoint
      (twoBlockDiagRestrictedJArg
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) := by
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  letI : NormedAddCommGroup (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : NormedSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : CompleteSpace (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : InnerProductSpace ℂ ↥(twoBlockDiagSubmodule n) := inferInstance
  letI : CompleteSpace ↥(twoBlockDiagSubmodule n) := instTwoBlockDiagSubtypeCompleteSpace (n := n)
  let Φ := twoBlockDiagSubmoduleConjStarAlgEquiv n
  have hJ₁ : IsSelfAdjoint (jArg A₁ B₁) := by
    change hsAdjoint (jArg A₁ B₁) = jArg A₁ B₁
    exact jArg_isSelfAdjoint hA₁ hB₁
  have hJ₂ : IsSelfAdjoint (jArg A₂ B₂) := by
    change hsAdjoint (jArg A₂ B₂) = jArg A₂ B₂
    exact jArg_isSelfAdjoint hA₂ hB₂
  have hdiagHs :
      IsSelfAdjoint (matrixDiagMapCLM (n := n) (jArg A₁ B₁) (jArg A₂ B₂)) :=
    isSelfAdjoint_matrixDiagMapCLM (n := n) hJ₁ hJ₂
  have hdiag :
      IsSelfAdjoint (matrixDiagMapCLM (n := n) (jArg A₁ B₁) (jArg A₂ B₂)) := by
    exact hdiagHs
  have hmap :
      IsSelfAdjoint
        (Φ (twoBlockDiagRestrictedJArg
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)) := by
    rw [twoBlockDiagSubmoduleIsometry_jArg (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁)
      (B₂ := B₂) hB₁ hB₂]
    exact hdiag
  change star (twoBlockDiagRestrictedJArg
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) =
      twoBlockDiagRestrictedJArg
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂
  apply Φ.injective
  calc
    Φ (star (twoBlockDiagRestrictedJArg
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)) =
        star
          (Φ (twoBlockDiagRestrictedJArg
            (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)) := by
            simpa [Φ] using
              (Φ.map_star'
                (twoBlockDiagRestrictedJArg
                  (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
    _ = Φ (twoBlockDiagRestrictedJArg
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) :=
          hmap.star_eq

-- The diagonal/off-diagonal transport produces a large `diagMapCLM` term under `star`.
/-- The off-diagonal restriction of the two-block `J` argument is self-adjoint
under the same self-adjointness and positive-definiteness hypotheses. -/
theorem offDiagRestrictedJArg_isSelfAdjoint {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    IsSelfAdjoint
      (offDiagRestrictedJArg
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) := by
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  letI : NormedAddCommGroup (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : NormedSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : InnerProductSpace ℂ (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : CompleteSpace (WithLp 2 (Mₙ n × Mₙ n)) := inferInstance
  letI : InnerProductSpace ℂ ↥(offDiagSubmodule n) := inferInstance
  letI : CompleteSpace ↥(offDiagSubmodule n) := instOffDiagSubtypeCompleteSpace (n := n)
  let Ψ := offDiagSubmoduleConjStarAlgEquiv n
  have hJ₁₂ : IsSelfAdjoint (jArg A₁ B₂) := by
    change hsAdjoint (jArg A₁ B₂) = jArg A₁ B₂
    exact jArg_isSelfAdjoint hA₁ hB₂
  have hJ₂₁ : IsSelfAdjoint (jArg A₂ B₁) := by
    change hsAdjoint (jArg A₂ B₁) = jArg A₂ B₁
    exact jArg_isSelfAdjoint hA₂ hB₁
  have hdiagHs :
      IsSelfAdjoint (matrixDiagMapCLM (n := n) (jArg A₁ B₂) (jArg A₂ B₁)) :=
    isSelfAdjoint_matrixDiagMapCLM (n := n) hJ₁₂ hJ₂₁
  have hdiag :
      IsSelfAdjoint (matrixDiagMapCLM (n := n) (jArg A₁ B₂) (jArg A₂ B₁)) := by
    exact hdiagHs
  change star (offDiagRestrictedJArg
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) =
      offDiagRestrictedJArg
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂
  apply Ψ.injective
  calc
    Ψ (star (offDiagRestrictedJArg
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)) =
        star
          (Ψ (offDiagRestrictedJArg
            (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)) := by
            simpa [Ψ] using
              (Ψ.map_star'
                (offDiagRestrictedJArg
                  (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂))
    _ = Ψ (offDiagRestrictedJArg
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) := by
          rw [offDiagSubmoduleIsometry_jArg (n := n)
            (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂]
          exact hdiag.star_eq

-- Self-adjointness is transported through the off-diagonal orthogonal equivalence.
private theorem offDiagRestrictedJArgOrth_isSelfAdjoint {n : ℕ} {A₁ A₂ B₁ B₂ : Mₙ n}
    (hA₁ : IsSelfAdjoint A₁) (hA₂ : IsSelfAdjoint A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    IsSelfAdjoint
      (offDiagRestrictedJArgOrth (n := n)
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) := by
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  letI : NormedAddCommGroup (offDiagSubmodule n) := inferInstance
  letI : NormedSpace ℂ (offDiagSubmodule n) := inferInstance
  letI : InnerProductSpace ℂ (offDiagSubmodule n) := inferInstance
  letI : CompleteSpace (offDiagSubmodule n) := instOffDiagSubmoduleCompleteSpace (n := n)
  letI : NormedAddCommGroup ↥(offDiagSubmodule n) := inferInstance
  letI : NormedSpace ℂ ↥(offDiagSubmodule n) := inferInstance
  letI : InnerProductSpace ℂ ↥(offDiagSubmodule n) := inferInstance
  letI : CompleteSpace ↥(offDiagSubmodule n) := instOffDiagSubtypeCompleteSpace (n := n)
  letI : NormedAddCommGroup (twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : NormedSpace ℂ (twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : InnerProductSpace ℂ (twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : CompleteSpace (twoBlockDiagOrthogonalSubmodule n) :=
    instTwoBlockDiagOrthogonalSubmoduleCompleteSpace (n := n)
  letI : NormedAddCommGroup ↥(twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : NormedSpace ℂ ↥(twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : InnerProductSpace ℂ ↥(twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : CompleteSpace ↥(twoBlockDiagOrthogonalSubmodule n) :=
    instTwoBlockDiagOrthogonalSubtypeCompleteSpace (n := n)
  let e : offDiagSubmodule n ≃ₗᵢ[ℂ] twoBlockDiagOrthogonalSubmodule n :=
    offDiagOrthogonalEquiv n
  let Ψ :
      (offDiagSubmodule n →L[ℂ] offDiagSubmodule n) ≃⋆ₐ[ℂ]
        (twoBlockDiagOrthogonalSubmodule n →L[ℂ] twoBlockDiagOrthogonalSubmodule n) :=
    @LinearIsometryEquiv.conjStarAlgEquiv ℂ
      (inferInstance : RCLike ℂ)
      (offDiagSubmodule n)
      (inferInstance : NormedAddCommGroup (offDiagSubmodule n))
      (inferInstance : InnerProductSpace ℂ (offDiagSubmodule n))
      (instOffDiagSubtypeCompleteSpace (n := n))
      (twoBlockDiagOrthogonalSubmodule n)
      (inferInstance : NormedAddCommGroup (twoBlockDiagOrthogonalSubmodule n))
      (inferInstance : InnerProductSpace ℂ (twoBlockDiagOrthogonalSubmodule n))
      (instTwoBlockDiagOrthogonalSubtypeCompleteSpace (n := n))
      e
  have hsrc :
      IsSelfAdjoint
        (offDiagRestrictedJArg
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) :=
    offDiagRestrictedJArg_isSelfAdjoint (n := n) hA₁ hA₂ hB₁ hB₂
  simpa [e, Ψ, offDiagRestrictedJArgOrth, LinearIsometryEquiv.conjStarAlgEquiv_apply,
      ContinuousLinearMap.comp_assoc] using hsrc.map Ψ

private theorem spectrum_offDiagRestrictedJArgOrth_subset_Ioi {n : ℕ}
    {A₁ A₂ B₁ B₂ : Mₙ n}
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    spectrum ℝ
        (offDiagRestrictedJArgOrth (n := n)
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) ⊆
      Set.Ioi (0 : ℝ) := by
  letI : InnerProductSpace ℂ (Mₙ (2 * n)) := instMatrixInnerProductSpace (n := 2 * n)
  letI : CompleteSpace (Mₙ (2 * n)) := instMatrixCompleteSpace (n := 2 * n)
  let od : ↥(offDiagSubmodule n) ≃ₗᵢ[ℂ] ↥(twoBlockDiagOrthogonalSubmodule n) :=
    offDiagOrthogonalEquiv n
  letI : NormedAddCommGroup (offDiagSubmodule n) := inferInstance
  letI : NormedSpace ℂ (offDiagSubmodule n) := inferInstance
  letI : InnerProductSpace ℂ (offDiagSubmodule n) := inferInstance
  letI : CompleteSpace (offDiagSubmodule n) := instOffDiagSubmoduleCompleteSpace (n := n)
  letI : NormedAddCommGroup ↥(offDiagSubmodule n) := inferInstance
  letI : NormedSpace ℂ ↥(offDiagSubmodule n) := inferInstance
  letI : InnerProductSpace ℂ ↥(offDiagSubmodule n) := inferInstance
  letI : CompleteSpace ↥(offDiagSubmodule n) := instOffDiagSubtypeCompleteSpace (n := n)
  letI : NormedAddCommGroup (twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : NormedSpace ℂ (twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : InnerProductSpace ℂ (twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : CompleteSpace (twoBlockDiagOrthogonalSubmodule n) :=
    instTwoBlockDiagOrthogonalSubmoduleCompleteSpace (n := n)
  letI : NormedAddCommGroup ↥(twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : NormedSpace ℂ ↥(twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : InnerProductSpace ℂ ↥(twoBlockDiagOrthogonalSubmodule n) := inferInstance
  letI : CompleteSpace ↥(twoBlockDiagOrthogonalSubmodule n) :=
    instTwoBlockDiagOrthogonalSubtypeCompleteSpace (n := n)
  let Ψ :
      (offDiagSubmodule n →L[ℂ] offDiagSubmodule n) ≃⋆ₐ[ℂ]
        (twoBlockDiagOrthogonalSubmodule n →L[ℂ] twoBlockDiagOrthogonalSubmodule n) :=
    @LinearIsometryEquiv.conjStarAlgEquiv ℂ
      (inferInstance : RCLike ℂ)
      (offDiagSubmodule n)
      (inferInstance : NormedAddCommGroup (offDiagSubmodule n))
      (inferInstance : InnerProductSpace ℂ (offDiagSubmodule n))
      (instOffDiagSubtypeCompleteSpace (n := n))
      (twoBlockDiagOrthogonalSubmodule n)
      (inferInstance : NormedAddCommGroup (twoBlockDiagOrthogonalSubmodule n))
      (inferInstance : InnerProductSpace ℂ (twoBlockDiagOrthogonalSubmodule n))
      (instTwoBlockDiagOrthogonalSubtypeCompleteSpace (n := n))
      od
  let ΨR :
      (offDiagSubmodule n →L[ℂ] offDiagSubmodule n) ≃ₐ[ℝ]
        (twoBlockDiagOrthogonalSubmodule n →L[ℂ] twoBlockDiagOrthogonalSubmodule n) :=
    { toFun := Ψ
      invFun := Ψ.symm
      left_inv := Ψ.left_inv
      right_inv := Ψ.right_inv
      map_mul' := Ψ.map_mul'
      map_add' := Ψ.map_add'
      commutes' := by
        intro r
        apply ContinuousLinearMap.ext
        intro X
        change
          od (((algebraMap ℝ (offDiagSubmodule n →L[ℂ] offDiagSubmodule n)) r)
              (od.symm X)) =
            ((algebraMap ℝ (twoBlockDiagOrthogonalSubmodule n →L[ℂ]
              twoBlockDiagOrthogonalSubmodule n)) r) X
        simpa [ContinuousLinearMap.algebraMap_apply] using od.map_smul r (od.symm X) }
  intro x hx
  have horth :
      offDiagRestrictedJArgOrth (n := n)
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ =
        ΨR (offDiagRestrictedJArg
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) := by
    apply ContinuousLinearMap.ext
    intro X
    apply Subtype.ext
    rfl
  have hx' : x ∈ spectrum ℝ
      (offDiagRestrictedJArg
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) := by
    rw [horth] at hx
    rw [AlgEquiv.spectrum_eq ΨR
      (offDiagRestrictedJArg
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)] at hx
    exact hx
  rcases spectrum_offDiagRestrictedJArg_subset_union
      (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ hx' with hx | hx
  · exact spectrum_jArg_subset_Ioi hA₁ hB₂ hx
  · exact spectrum_jArg_subset_Ioi hA₂ hB₁ hx

-- Complex-spectrum continuity unfolds the off-diagonal transport and product CFC instances.
@[fun_prop] private theorem continuousOn_complex_offDiagRestrictedJArgOrth
    {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    ContinuousOn (fun z : ℂ => ((f z.re : ℝ) : ℂ))
      (spectrum ℂ
        (offDiagRestrictedJArgOrth (n := n)
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)) := by
  /- Step 1: Fix the matrix Hilbert-space instances. -/
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  /- Step 2: Relate orthogonal and ordinary restrictions by algebra equivalence. -/
  let od : offDiagSubmodule n ≃ₗᵢ[ℂ] twoBlockDiagOrthogonalSubmodule n :=
    offDiagOrthogonalEquiv n
  let Θ :
      (offDiagSubmodule n →L[ℂ] offDiagSubmodule n) ≃⋆ₐ[ℂ]
        (twoBlockDiagOrthogonalSubmodule n →L[ℂ] twoBlockDiagOrthogonalSubmodule n) :=
    @LinearIsometryEquiv.conjStarAlgEquiv ℂ
      (inferInstance : RCLike ℂ)
      (offDiagSubmodule n)
      (inferInstance : NormedAddCommGroup (offDiagSubmodule n))
      (inferInstance : InnerProductSpace ℂ (offDiagSubmodule n))
      (instOffDiagSubtypeCompleteSpace (n := n))
      (twoBlockDiagOrthogonalSubmodule n)
      (inferInstance : NormedAddCommGroup (twoBlockDiagOrthogonalSubmodule n))
      (inferInstance : InnerProductSpace ℂ (twoBlockDiagOrthogonalSubmodule n))
      (instTwoBlockDiagOrthogonalSubtypeCompleteSpace (n := n))
      od
  have horth :
      offDiagRestrictedJArgOrth (n := n)
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂ =
        Θ (offDiagRestrictedJArg
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) := by
    rfl
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
  have h : offDiagSubmoduleConjStarAlgEquiv n
      (offDiagRestrictedJArg
        (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂) =
      Ψ₀ (jArg A₁ B₂, jArg A₂ B₁) := by
    rw [offDiagSubmoduleIsometry_jArg (n := n) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁)
      (B₂ := B₂) hB₁ hB₂]
    rfl
  have hsub := spectrum_complex_subset_ofReal_Ioi_of_eq_pairHom
    (offDiagSubmoduleConjStarAlgEquiv n) Ψ₀ h
    (by
      change hsAdjoint (jArg A₁ B₂) = jArg A₁ B₂
      exact jArg_isSelfAdjoint hA₁.1 hB₂)
    (by
      change hsAdjoint (jArg A₂ B₁) = jArg A₂ B₁
      exact jArg_isSelfAdjoint hA₂.1 hB₁)
    (spectrum_jArg_subset_Ioi hA₁ hB₂) (spectrum_jArg_subset_Ioi hA₂ hB₁)
  /- Step 3: Pull orthogonal spectral points back along `Θ` to the off-diagonal restriction. -/
  refine (continuousOn_complex_ofReal_Ioi hf).mono ?_
  rw [horth, AlgEquiv.spectrum_eq Θ]
  exact hsub

-- Complex-spectrum continuity unfolds the diagonal transport and product CFC instances.
@[fun_prop] private theorem continuousOn_complex_twoBlockDiagRestrictedJArg
    {n : ℕ} {f : ℝ → ℝ}
    {A₁ A₂ B₁ B₂ : Mₙ n}
    (hf : ContinuousOn f (Set.Ioi (0 : ℝ)))
    (hA₁ : Matrix.PosDef A₁) (hA₂ : Matrix.PosDef A₂)
    (hB₁ : Matrix.PosDef B₁) (hB₂ : Matrix.PosDef B₂) :
    ContinuousOn (fun z : ℂ => ((f z.re : ℝ) : ℂ))
      (spectrum ℂ
        (twoBlockDiagRestrictedJArg
          (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) hB₁ hB₂)) := by
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
  exact (continuousOn_complex_ofReal_Ioi hf).mono
    (spectrum_complex_subset_ofReal_Ioi_of_eq_pairHom
      (twoBlockDiagSubmoduleConjStarAlgEquiv n) Ψ₀ h
      (by
        change hsAdjoint (jArg A₁ B₁) = jArg A₁ B₁
        exact jArg_isSelfAdjoint hA₁.1 hB₁)
      (by
        change hsAdjoint (jArg A₂ B₂) = jArg A₂ B₂
        exact jArg_isSelfAdjoint hA₂.1 hB₂)
      (spectrum_jArg_subset_Ioi hA₁ hB₁) (spectrum_jArg_subset_Ioi hA₂ hB₂))

end MatrixScopedInstances

end HiaiPetz
