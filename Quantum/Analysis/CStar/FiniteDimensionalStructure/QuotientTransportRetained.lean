/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
-- Projections identify normal idempotents with self-adjoint idempotents in C*-algebras.
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Algebra.Order.Star.Pi
-- Matrix-block algebra automorphisms are inner after identifying matrices with endomorphisms.
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Artinian.Ring
-- Complete orthogonal idempotent families package the coordinate block projections.
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Topology.Order.Basic
import Quantum.TraceInequality.LownerHeinzTheorem
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Primitives
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Transport
import Quantum.Analysis.CStar.FiniteDimensionalStructure.EndpointOrder
import Quantum.Analysis.CStar.FiniteDimensionalStructure.EndpointOrderRetained
import Quantum.Analysis.CStar.FiniteDimensionalStructure.QuotientTransport
-- An instance name below is an indivisible token longer than the style limit.
set_option linter.style.longLine false

-- Part of the finite-dimensional infrastructure for the AH1 matrix-order bridge.

/-!
# Positive-ray AH1 quotient transport

Carlen 2022 Theorem 1.45 (AH1): finite-dimensional C*-algebra
classification infrastructure stage for transporting the endpoint quotient
through matrix and finite product models.
-/

namespace Quantum.TraceInequality.Loewner

open scoped MatrixOrder ComplexOrder CStarAlgebra
open scoped Topology
open Filter
open Matrix

-- Keep the complex-to-real algebra local to the endpoint quotient CFC identities.
attribute [local instance] instAH1QuotientCStarMatrixRealAlgebra

section PositiveRayEndpointQuotientCFC

attribute [local instance]
    instContinuousFunctionalCalculusRealContinuousLinearMapComplexIdEuclideanSpaceFinIsSelfAdjointOfNontrivial_quantum

attribute [local instance]
    instNonnegSpectrumClassRealContinuousLinearMapComplexIdEuclideanSpaceFinOfNontrivial_quantum

/-! ### Matrix and product transport of endpoint quotient -/
/--
Transport the concrete finite-dimensional Hilbert-space endpoint-quotient CFC
monotonicity to the corresponding `CStarMatrix` algebra.

This is the matrix-algebra copy of the concrete theorem. The extension to arbitrary
finite-dimensional non-unital C*-algebras, normalized to `cfcₙ`, is completed in
`Classification.lean`: `exists_starAlgEquiv_pi_cstarMatrix` classifies such algebras by finite
products of `CStarMatrix` blocks, and `positiveRay_cfcₙ_sub_endpoint_le` is the resulting
general theorem.
-/
theorem cstarMatrix_endpointQuotient_positiveCayleyPullback_cfc_le_of_order
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))]
    {A B : CStarMatrix (Fin n) (Fin n) ℂ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAq : quasispectrum ℝ A ⊆ Set.Ioo (-1 : ℝ) 1)
    (hBq : quasispectrum ℝ B ⊆ Set.Ioo (-1 : ℝ) 1)
    (hAB : A ≤ B) :
    LownerHeinzCore.cfcR
        (𝓐 := CStarMatrix (Fin n) (Fin n) ℂ)
        (positiveCayleyPullback (positiveRayEndpointQuotient h d)) A ≤
      LownerHeinzCore.cfcR
        (𝓐 := CStarMatrix (Fin n) (Fin n) ℂ)
        (positiveCayleyPullback (positiveRayEndpointQuotient h d)) B := by
  let e := positiveRayOperatorCStarMatrixEquiv n
  let ψ : CStarMatrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    starAlgEquivToStarAlgHom e.symm
  let φ : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) →⋆ₐ[ℂ]
      CStarMatrix (Fin n) (Fin n) ℂ :=
    starAlgEquivToStarAlgHom e
  have hψA : IsSelfAdjoint (ψ A) := hA.map ψ
  have hψB : IsSelfAdjoint (ψ B) := hB.map ψ
  have hφcont : Continuous φ := by
    simpa [φ, starAlgEquivToStarAlgHom] using (StarAlgEquiv.isometry e).continuous
  have hψAspec : spectrum ℝ (ψ A) ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro x hx
    have hxq : x ∈ quasispectrum ℝ (ψ A) :=
      spectrum_subset_quasispectrum ℝ (ψ A) hx
    have hsubset : quasispectrum ℝ (ψ A) ⊆ quasispectrum ℝ A := by
      exact NonUnitalAlgHom.quasispectrum_apply_subset' (R := ℝ) ℂ ψ A
    exact hAq (hsubset hxq)
  have hψBspec : spectrum ℝ (ψ B) ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro x hx
    have hxq : x ∈ quasispectrum ℝ (ψ B) :=
      spectrum_subset_quasispectrum ℝ (ψ B) hx
    have hsubset : quasispectrum ℝ (ψ B) ⊆ quasispectrum ℝ B := by
      exact NonUnitalAlgHom.quasispectrum_apply_subset' (R := ℝ) ℂ ψ B
    exact hBq (hsubset hxq)
  have hψAB : ψ A ≤ ψ B := by
    letI : OrderIsoClass
        (CStarMatrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℂ]
          (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
        (CStarMatrix (Fin n) (Fin n) ℂ)
        (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
      StarRingEquivClass.instOrderIsoClass
    exact OrderHomClass.mono e.symm hAB
  have hmonoψ :=
    positiveRayEuclidean_endpointQuotient_positiveCayleyPullback_cfc_le_of_order
      (h := h) (d := d) hclosed hlin (n := n)
      hψA hψB hψAspec hψBspec hψAB
  have hmapped :
      φ (LownerHeinzTheorem.cfcR
            (ℋ := EuclideanSpace ℂ (Fin n))
            (positiveCayleyPullback (positiveRayEndpointQuotient h d)) (ψ A)) ≤
        φ (LownerHeinzTheorem.cfcR
            (ℋ := EuclideanSpace ℂ (Fin n))
            (positiveCayleyPullback (positiveRayEndpointQuotient h d)) (ψ B)) := by
    letI : OrderIsoClass
        ((EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) ≃⋆ₐ[ℂ]
          CStarMatrix (Fin n) (Fin n) ℂ)
        (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
        (CStarMatrix (Fin n) (Fin n) ℂ) :=
      StarRingEquivClass.instOrderIsoClass
    exact OrderHomClass.mono e hmonoψ
  have hfinA : (spectrum ℝ (ψ A)).Finite :=
    positiveRayEndpointQuotientCFC_spectrum_real_finite_of_finiteDimensional_complex
      (B := (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) (ψ A)
  have hfinB : (spectrum ℝ (ψ B)).Finite :=
    positiveRayEndpointQuotientCFC_spectrum_real_finite_of_finiteDimensional_complex
      (B := (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) (ψ B)
  have hmapA :
      φ (LownerHeinzTheorem.cfcR
            (ℋ := EuclideanSpace ℂ (Fin n))
            (positiveCayleyPullback (positiveRayEndpointQuotient h d)) (ψ A)) =
        LownerHeinzCore.cfcR
          (𝓐 := CStarMatrix (Fin n) (Fin n) ℂ)
          (positiveCayleyPullback (positiveRayEndpointQuotient h d)) A := by
    dsimp [LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR]
    have hcf := cstarMatrix_starAlgHom_map_cfc
      (h := positiveCayleyPullback (positiveRayEndpointQuotient h d))
      (φ := φ) hψA (hfinA.continuousOn _) hφcont (hψA.map φ)
    have hround : φ (ψ A) = A := by
      change e (e.symm A) = A
      exact e.apply_symm_apply A
    rw [hround] at hcf
    simpa [φ, ψ, starAlgEquivToStarAlgHom] using hcf
  have hmapB :
      φ (LownerHeinzTheorem.cfcR
            (ℋ := EuclideanSpace ℂ (Fin n))
            (positiveCayleyPullback (positiveRayEndpointQuotient h d)) (ψ B)) =
        LownerHeinzCore.cfcR
          (𝓐 := CStarMatrix (Fin n) (Fin n) ℂ)
          (positiveCayleyPullback (positiveRayEndpointQuotient h d)) B := by
    dsimp [LownerHeinzTheorem.cfcR, LownerHeinzCore.cfcR]
    have hcf := cstarMatrix_starAlgHom_map_cfc
      (h := positiveCayleyPullback (positiveRayEndpointQuotient h d))
      (φ := φ) hψB (hfinB.continuousOn _) hφcont (hψB.map φ)
    have hround : φ (ψ B) = B := by
      change e (e.symm B) = B
      exact e.apply_symm_apply B
    rw [hround] at hcf
    simpa [φ, ψ, starAlgEquivToStarAlgHom] using hcf
  simpa [hmapA, hmapB] using hmapped

/--
The normalized non-unital CFC form of the `CStarMatrix` transport theorem.

This is still a matrix-algebra statement; its transport to arbitrary
finite-dimensional non-unital C*-algebras is `positiveRay_cfcₙ_sub_endpoint_le` in
`Classification.lean`.
-/
theorem cstarMatrix_endpointQuotient_positiveCayleyPullback_cfcₙ_sub_endpoint_le_of_order
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))]
    {A B : CStarMatrix (Fin n) (Fin n) ℂ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAq : quasispectrum ℝ A ⊆ Set.Ioo (-1 : ℝ) 1)
    (hBq : quasispectrum ℝ B ⊆ Set.Ioo (-1 : ℝ) 1)
    (hAB : A ≤ B) :
    cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) A ≤
      cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) B := by
  let F : ℝ → ℝ := positiveCayleyPullback (positiveRayEndpointQuotient h d)
  let c0 : CStarMatrix (Fin n) (Fin n) ℂ := algebraMap ℝ _ (F 0)
  have hmono :
      LownerHeinzCore.cfcR (𝓐 := CStarMatrix (Fin n) (Fin n) ℂ) F A ≤
        LownerHeinzCore.cfcR (𝓐 := CStarMatrix (Fin n) (Fin n) ℂ) F B := by
    simpa [F] using
      cstarMatrix_endpointQuotient_positiveCayleyPullback_cfc_le_of_order
        (h := h) (d := d) hclosed hlin hA hB hAq hBq hAB
  have hqfinA : (quasispectrum ℝ A).Finite :=
    positiveRayEndpointQuotientCFC_quasispectrum_real_finite_of_finiteDimensional_complex A
  have hqfinB : (quasispectrum ℝ B).Finite :=
    positiveRayEndpointQuotientCFC_quasispectrum_real_finite_of_finiteDimensional_complex B
  have hAeq :
      cfcₙ (fun x : ℝ => F x - F 0) A =
        LownerHeinzCore.cfcR (𝓐 := CStarMatrix (Fin n) (Fin n) ℂ) F A - c0 := by
    have hcn :
        cfcₙ (fun x : ℝ => F x - F 0) A =
          cfc (fun x : ℝ => F x - F 0) A := by
      exact cfcₙ_eq_cfc
        (R := ℝ) (A := CStarMatrix (Fin n) (Fin n) ℂ) (p := IsSelfAdjoint)
        (f := fun x : ℝ => F x - F 0) (a := A)
        (hf := hqfinA.continuousOn _) (hf0 := by simp)
    have hsub :
        cfc (fun x : ℝ => F x - F 0) A =
          cfc F A - cfc (fun _ : ℝ => F 0) A := by
      exact cfc_sub (f := F) (g := fun _ : ℝ => F 0) (a := A)
        (hf := (hqfinA.continuousOn F).mono (spectrum_subset_quasispectrum ℝ A))
        (hg := continuousOn_const)
    have hconst :
        cfc (fun _ : ℝ => F 0) A = c0 := by
      simpa [c0] using
        cfc_const (R := ℝ)
          (A := CStarMatrix (Fin n) (Fin n) ℂ) (p := IsSelfAdjoint)
          (r := F 0) (a := A) (ha := hA)
    calc
      cfcₙ (fun x : ℝ => F x - F 0) A =
          cfc (fun x : ℝ => F x - F 0) A := hcn
      _ = cfc F A - cfc (fun _ : ℝ => F 0) A := hsub
      _ = LownerHeinzCore.cfcR (𝓐 := CStarMatrix (Fin n) (Fin n) ℂ) F A - c0 := by
          simp [LownerHeinzCore.cfcR, hconst]
  have hBeq :
      cfcₙ (fun x : ℝ => F x - F 0) B =
        LownerHeinzCore.cfcR (𝓐 := CStarMatrix (Fin n) (Fin n) ℂ) F B - c0 := by
    have hcn :
        cfcₙ (fun x : ℝ => F x - F 0) B =
          cfc (fun x : ℝ => F x - F 0) B := by
      exact cfcₙ_eq_cfc
        (R := ℝ) (A := CStarMatrix (Fin n) (Fin n) ℂ) (p := IsSelfAdjoint)
        (f := fun x : ℝ => F x - F 0) (a := B)
        (hf := hqfinB.continuousOn _) (hf0 := by simp)
    have hsub :
        cfc (fun x : ℝ => F x - F 0) B =
          cfc F B - cfc (fun _ : ℝ => F 0) B := by
      exact cfc_sub (f := F) (g := fun _ : ℝ => F 0) (a := B)
        (hf := (hqfinB.continuousOn F).mono (spectrum_subset_quasispectrum ℝ B))
        (hg := continuousOn_const)
    have hconst :
        cfc (fun _ : ℝ => F 0) B = c0 := by
      simpa [c0] using
        cfc_const (R := ℝ)
          (A := CStarMatrix (Fin n) (Fin n) ℂ) (p := IsSelfAdjoint)
          (r := F 0) (a := B) (ha := hB)
    calc
      cfcₙ (fun x : ℝ => F x - F 0) B =
          cfc (fun x : ℝ => F x - F 0) B := hcn
      _ = cfc F B - cfc (fun _ : ℝ => F 0) B := hsub
      _ = LownerHeinzCore.cfcR (𝓐 := CStarMatrix (Fin n) (Fin n) ℂ) F B - c0 := by
          simp [LownerHeinzCore.cfcR, hconst]
  simpa [F, hAeq, hBeq] using sub_le_sub_right hmono c0

/--
The normalized non-unital CFC monotonicity extends componentwise to finite
products of `CStarMatrix` blocks.

This closes the product-of-matrix-block part of the finite-dimensional
C*-algebra transport.  The classification step that identifies an arbitrary
finite-dimensional non-unital C*-algebra with such a finite product of matrix blocks is
`exists_starAlgEquiv_pi_cstarMatrix` in `Classification.lean`, and the extension to arbitrary
finite-dimensional non-unital C*-algebras is `positiveRay_cfcₙ_sub_endpoint_le` there.
-/
theorem piCStarMatrix_endpointQuotient_positiveCayleyPullback_cfcₙ_sub_endpoint_le_of_order
    {ι : Type*} [Finite ι] {n : ι → ℕ}
    {h : ℝ → ℝ} {d : ℝ}
    (hclosed :
      PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0))
    [∀ i, Nontrivial (EuclideanSpace ℂ (Fin (n i)))]
    {A B : ∀ i, CStarMatrix (Fin (n i)) (Fin (n i)) ℂ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAq : quasispectrum ℝ A ⊆ Set.Ioo (-1 : ℝ) 1)
    (hBq : quasispectrum ℝ B ⊆ Set.Ioo (-1 : ℝ) 1)
    (hAB : A ≤ B) :
    letI := Fintype.ofFinite ι
    cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) A ≤
      cfcₙ
        (fun x : ℝ =>
          positiveCayleyPullback (positiveRayEndpointQuotient h d) x -
            positiveCayleyPullback (positiveRayEndpointQuotient h d) 0) B := by
  letI : Fintype ι := Fintype.ofFinite ι
  haveI : ∀ i, StarOrderedRing (CStarMatrix (Fin (n i)) (Fin (n i)) ℂ) :=
    fun _ => CStarMatrix.instStarOrderedRing
  let F : ℝ → ℝ := positiveCayleyPullback (positiveRayEndpointQuotient h d)
  let f : ℝ → ℝ := fun x : ℝ => F x - F 0
  have hfinA : (⋃ i, quasispectrum ℝ (A i)).Finite := by
    exact Set.Finite.iUnion Set.finite_univ
      (by
        intro i _
        exact positiveRayEndpointQuotientCFC_quasispectrum_real_finite_of_finiteDimensional_complex
          (A i))
      (by intro i hi; simp at hi)
  have hfinB : (⋃ i, quasispectrum ℝ (B i)).Finite := by
    exact Set.Finite.iUnion Set.finite_univ
      (by
        intro i _
        exact positiveRayEndpointQuotientCFC_quasispectrum_real_finite_of_finiteDimensional_complex
          (B i))
      (by intro i hi; simp at hi)
  have hmapA :
      cfcₙ f A = fun i => cfcₙ f (A i) := by
    exact cfcₙ_map_pi (R := ℝ) (S := ℂ) f A
      (hf := hfinA.continuousOn f)
      (ha := hA)
      (ha' := by
        intro i
        change star (A i) = A i
        exact congrFun hA.star_eq i)
  have hmapB :
      cfcₙ f B = fun i => cfcₙ f (B i) := by
    exact cfcₙ_map_pi (R := ℝ) (S := ℂ) f B
      (hf := hfinB.continuousOn f)
      (ha := hB)
      (ha' := by
        intro i
        change star (B i) = B i
        exact congrFun hB.star_eq i)
  rw [hmapA, hmapB]
  intro i
  have hAi : IsSelfAdjoint (A i) := by
    change star (A i) = A i
    exact congrFun hA.star_eq i
  have hBi : IsSelfAdjoint (B i) := by
    change star (B i) = B i
    exact congrFun hB.star_eq i
  have hAqi : quasispectrum ℝ (A i) ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro x hx
    haveI : Nonempty ι := ⟨i⟩
    have hq :
        quasispectrum ℝ A =
          ⋃ j, quasispectrum ℝ (A j) := by
      exact Pi.quasispectrum_eq (R := ℝ) (a := A)
    exact hAq (hq.symm ▸ Set.mem_iUnion.mpr ⟨i, hx⟩)
  have hBqi : quasispectrum ℝ (B i) ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro x hx
    haveI : Nonempty ι := ⟨i⟩
    have hq :
        quasispectrum ℝ B =
          ⋃ j, quasispectrum ℝ (B j) := by
      exact Pi.quasispectrum_eq (R := ℝ) (a := B)
    exact hBq (hq.symm ▸ Set.mem_iUnion.mpr ⟨i, hx⟩)
  have hABi : A i ≤ B i := hAB i
  simpa [F, f] using
    cstarMatrix_endpointQuotient_positiveCayleyPullback_cfcₙ_sub_endpoint_le_of_order
      (h := h) (d := d) hclosed hlin hAi hBi hAqi hBqi hABi

end PositiveRayEndpointQuotientCFC

end Quantum.TraceInequality.Loewner
