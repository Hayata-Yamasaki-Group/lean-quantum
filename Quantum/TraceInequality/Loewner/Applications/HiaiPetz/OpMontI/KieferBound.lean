/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.Loewner.Applications.HiaiPetz.OpMontI.WeightedAction

/-!
# Carlen's `opmontI` conditions: Kiefer bound and reciprocal target

This module contains the projection-invariance, Kiefer quadratic-form bound,
and condition (4) specialization stage of Carlen 2022 Theorem 1.46.
-/

namespace Quantum.TraceInequality.Loewner.HiaiPetz

open scoped MatrixOrder CStarAlgebra ComplexOrder

attribute [local instance]
  _root_.HiaiPetz.instMatrixNormedAddCommGroup
  _root_.HiaiPetz.instMatrixNormedSpace
  _root_.HiaiPetz.instMatrixInnerProductSpace
  _root_.HiaiPetz.instMatrixCompleteSpace
  instOpMontIBaseHSOpCStarAlgebra
  instOpMontIBaseHSOpComplexAlgebra
  instOpMontIBaseMatrixRealModule
  instOpMontIBaseMatrixRealScalarTower
  instOpMontIBaseMatrixRealNormedSpace
  instOpMontIBaseMatrixRealFiniteDimensional
  instOpMontIBaseHSOpRealAlgebra
  instOpMontIBaseHSOpStarRing
  instOpMontIBaseHSOpPartialOrder
  instOpMontIBaseHSOpStarOrderedRing
  instOpMontIBaseHSOpNonnegSpectrumClass
  instOpMontIBaseHSOpRealCFC
  instOpMontIBaseMatrixOppRealCFC
  instOpMontIBaseHSOpProdCStarAlgebra
  instOpMontIBaseHSOpProdRealCFC
  instOpMontIBaseHSOpProdProdCStarAlgebra
  instOpMontIBaseHSOpProdProdRealCFC

noncomputable section

/-! ### Projection invariance and weighted CFC -/
private theorem twoBlockReindex_inner_offDiag_diag_zero {n : ℕ}
    (B C U V : Mₙ n) :
    @inner ℂ (Mₙ (n + n)) inferInstance
      (twoBlockReindex (n := n) (Matrix.fromBlocks 0 B C 0))
      (twoBlockReindex (n := n) (Matrix.fromBlocks U 0 0 V)) = 0 := by
  change
    Matrix.trace
        (twoBlockReindex (n := n) (Matrix.fromBlocks U 0 0 V) *
          Matrix.conjTranspose
            (twoBlockReindex (n := n) (Matrix.fromBlocks 0 B C 0))) = 0
  rw [trace_twoBlockReindex_mul_conjTranspose]
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    trace_fromBlocks_diagonal]

private theorem twoBlockDiagonalProjection_eq_zero_of_inner_diagonal_zero {n : ℕ}
    {M : Mₙ (n + n)}
    (hM : ∀ U V : Mₙ n,
      @inner ℂ (Mₙ (n + n)) inferInstance M
        (twoBlockReindex (n := n) (Matrix.fromBlocks U 0 0 V)) = 0) :
    (twoBlockDiagonalProjection (n := n) : HSOp (n + n)) M = 0 := by
  let F : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    (twoBlockReindex (n := n)).symm M
  have hM_blocks :
      M =
        twoBlockReindex (n := n)
          (Matrix.fromBlocks F.toBlocks₁₁ F.toBlocks₁₂ F.toBlocks₂₁ F.toBlocks₂₂) := by
    calc
      M = twoBlockReindex (n := n) ((twoBlockReindex (n := n)).symm M) := by
          simp
      _ =
        twoBlockReindex (n := n)
          (Matrix.fromBlocks F.toBlocks₁₁ F.toBlocks₁₂ F.toBlocks₂₁ F.toBlocks₂₂) := by
          simp [F, Matrix.fromBlocks_toBlocks]
  have h₁₁_trace :
      Matrix.trace (F.toBlocks₁₁ * Matrix.conjTranspose F.toBlocks₁₁) = 0 := by
    have h := hM F.toBlocks₁₁ 0
    rw [hM_blocks] at h
    change
      Matrix.trace
          (twoBlockReindex (n := n) (Matrix.fromBlocks F.toBlocks₁₁ 0 0 0) *
            Matrix.conjTranspose
              (twoBlockReindex (n := n)
                (Matrix.fromBlocks F.toBlocks₁₁ F.toBlocks₁₂ F.toBlocks₂₁ F.toBlocks₂₂))) = 0 at h
    rw [trace_twoBlockReindex_mul_conjTranspose] at h
    simpa [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      trace_fromBlocks_diagonal] using h
  have h₂₂_trace :
      Matrix.trace (F.toBlocks₂₂ * Matrix.conjTranspose F.toBlocks₂₂) = 0 := by
    have h := hM 0 F.toBlocks₂₂
    rw [hM_blocks] at h
    change
      Matrix.trace
          (twoBlockReindex (n := n) (Matrix.fromBlocks 0 0 0 F.toBlocks₂₂) *
            Matrix.conjTranspose
              (twoBlockReindex (n := n)
                (Matrix.fromBlocks F.toBlocks₁₁ F.toBlocks₁₂ F.toBlocks₂₁ F.toBlocks₂₂))) = 0 at h
    rw [trace_twoBlockReindex_mul_conjTranspose] at h
    simpa [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      trace_fromBlocks_diagonal] using h
  have h₁₁ : F.toBlocks₁₁ = 0 :=
    Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp h₁₁_trace
  have h₂₂ : F.toBlocks₂₂ = 0 :=
    Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp h₂₂_trace
  calc
    (twoBlockDiagonalProjection (n := n) : HSOp (n + n)) M =
        (twoBlockDiagonalProjection (n := n) : HSOp (n + n))
          (twoBlockReindex (n := n)
            (Matrix.fromBlocks F.toBlocks₁₁ F.toBlocks₁₂ F.toBlocks₂₁ F.toBlocks₂₂)) := by
          rw [hM_blocks]
    _ = twoBlockReindex (n := n) (Matrix.fromBlocks F.toBlocks₁₁ 0 0 F.toBlocks₂₂) := by
          simp
    _ = 0 := by
          simp [h₁₁, h₂₂]

/--
If a self-adjoint Hilbert--Schmidt operator acts on the diagonal block
subspace as the direct sum of two smaller operators, then it commutes with the
orthogonal projection onto that diagonal block subspace.
-/
theorem twoBlockDiagonalProjection_commute_of_selfadjoint_direct_sum_action {n : ℕ}
    {T : HSOp (n + n)} {T₀ T₁ : HSOp n}
    (hT : IsSelfAdjoint T)
    (hdiag :
      ∀ W₀ W₁ : Mₙ n,
        T (twoBlockReindex (n := n) (Matrix.fromBlocks W₀ 0 0 W₁)) =
          twoBlockReindex (n := n)
            (Matrix.fromBlocks (T₀ W₀) 0 0 (T₁ W₁))) :
    Commute (twoBlockDiagonalProjection (n := n) : HSOp (n + n)) T := by
  rw [Commute]
  apply ContinuousLinearMap.ext
  intro V
  let F : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    (twoBlockReindex (n := n)).symm V
  let Vdiag : Mₙ (n + n) :=
    twoBlockReindex (n := n) (Matrix.fromBlocks F.toBlocks₁₁ 0 0 F.toBlocks₂₂)
  let Voff : Mₙ (n + n) :=
    twoBlockReindex (n := n) (Matrix.fromBlocks 0 F.toBlocks₁₂ F.toBlocks₂₁ 0)
  have hV :
      V = Vdiag + Voff := by
    calc
      V = twoBlockReindex (n := n) ((twoBlockReindex (n := n)).symm V) := by
          simp
      _ =
        twoBlockReindex (n := n)
          (Matrix.fromBlocks F.toBlocks₁₁ F.toBlocks₁₂ F.toBlocks₂₁ F.toBlocks₂₂) := by
          simp [F, Matrix.fromBlocks_toBlocks]
      _ = Vdiag + Voff := by
          change
            (twoBlockReindex (n := n))
                (Matrix.fromBlocks F.toBlocks₁₁ F.toBlocks₁₂ F.toBlocks₂₁ F.toBlocks₂₂) =
              (twoBlockReindex (n := n)) (Matrix.fromBlocks F.toBlocks₁₁ 0 0 F.toBlocks₂₂) +
                (twoBlockReindex (n := n)) (Matrix.fromBlocks 0 F.toBlocks₁₂ F.toBlocks₂₁ 0)
          rw [← map_add]
          congr 1
          simp [Matrix.fromBlocks_add]
  have hP_V :
      (twoBlockDiagonalProjection (n := n) : HSOp (n + n)) V = Vdiag := by
    rw [hV]
    simp [Vdiag, Voff]
  have hP_TVoff :
      (twoBlockDiagonalProjection (n := n) : HSOp (n + n)) (T Voff) = 0 := by
    apply twoBlockDiagonalProjection_eq_zero_of_inner_diagonal_zero
    intro U W
    have hsym :=
      (@IsSelfAdjoint.isSymmetric ℂ (Mₙ (n + n)) inferInstance
          (instMatrixNormedAddCommGroup (n := n + n))
          (instMatrixInnerProductSpace (n := n + n))
          (instMatrixCompleteSpace (n := n + n))
          (A := T) hT) Voff
        (twoBlockReindex (n := n) (Matrix.fromBlocks U 0 0 W))
    calc
      @inner ℂ (Mₙ (n + n)) inferInstance (T Voff)
          (twoBlockReindex (n := n) (Matrix.fromBlocks U 0 0 W)) =
          @inner ℂ (Mₙ (n + n)) inferInstance Voff
            (T (twoBlockReindex (n := n) (Matrix.fromBlocks U 0 0 W))) := hsym
      _ =
          @inner ℂ (Mₙ (n + n)) inferInstance Voff
            (twoBlockReindex (n := n)
              (Matrix.fromBlocks (T₀ U) 0 0 (T₁ W))) := by
            rw [hdiag U W]
      _ = 0 := by
            simpa [Voff] using
              twoBlockReindex_inner_offDiag_diag_zero
                (n := n) F.toBlocks₁₂ F.toBlocks₂₁ (T₀ U) (T₁ W)
  have hT_Vdiag :
      T Vdiag =
        twoBlockReindex (n := n)
          (Matrix.fromBlocks (T₀ F.toBlocks₁₁) 0 0 (T₁ F.toBlocks₂₂)) := by
    simpa [Vdiag] using hdiag F.toBlocks₁₁ F.toBlocks₂₂
  calc
    (twoBlockDiagonalProjection (n := n) : HSOp (n + n)) (T V) =
        (twoBlockDiagonalProjection (n := n) : HSOp (n + n)) (T (Vdiag + Voff)) := by
          rw [hV]
    _ =
        (twoBlockDiagonalProjection (n := n) : HSOp (n + n)) (T Vdiag + T Voff) := by
          simp
    _ =
        (twoBlockDiagonalProjection (n := n) : HSOp (n + n)) (T Vdiag) +
          (twoBlockDiagonalProjection (n := n) : HSOp (n + n)) (T Voff) := by
          simp
    _ =
        (twoBlockDiagonalProjection (n := n) : HSOp (n + n)) (T Vdiag) := by
          rw [hP_TVoff, add_zero]
    _ = T Vdiag := by
          rw [hT_Vdiag]
          simp
    _ = T ((twoBlockDiagonalProjection (n := n) : HSOp (n + n)) V) := by
          rw [hP_V]

/--
If a self-adjoint Hilbert--Schmidt operator acts as a direct sum on the
diagonal block subspace, then every real continuous functional calculus of it
preserves that subspace.
-/
theorem twoBlockDiagonalProjection_hsCfcR_of_selfadjoint_direct_sum_action_apply_fromBlocks
    {n : ℕ} {T : HSOp (n + n)} {T₀ T₁ : HSOp n} (k : ℝ → ℝ)
    (hT : IsSelfAdjoint T)
    (hdiag :
      ∀ W₀ W₁ : Mₙ n,
        T (twoBlockReindex (n := n) (Matrix.fromBlocks W₀ 0 0 W₁)) =
          twoBlockReindex (n := n)
            (Matrix.fromBlocks (T₀ W₀) 0 0 (T₁ W₁)))
    (V₀ V₁ : Mₙ n) :
    (twoBlockDiagonalProjection (n := n) : HSOp (n + n))
        (hsCfcR k T (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁))) =
      hsCfcR k T (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)) := by
  let P : HSOp (n + n) := twoBlockDiagonalProjection (n := n)
  let V : Mₙ (n + n) := twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)
  have hcomm : Commute (hsCfcR k T) P := by
    simpa [hsCfcR, P] using
      (twoBlockDiagonalProjection_commute_of_selfadjoint_direct_sum_action
        (n := n) (T := T) (T₀ := T₀) (T₁ := T₁) hT hdiag).symm.cfc_real k
  have hPV : P V = V := by
    simp [P, V]
  rw [Commute] at hcomm
  have happly : (hsCfcR k T) (P V) = P ((hsCfcR k T) V) := by
    have hmul := congrArg (fun S : HSOp (n + n) => S V) hcomm
    simpa [ContinuousLinearMap.mul_apply] using hmul
  calc
    P ((hsCfcR k T) V) = (hsCfcR k T) (P V) := happly.symm
    _ = (hsCfcR k T) V := by
          rw [hPV]

/--
On a full four-block input, the weighted-block `gArg` commutes with the
diagonal-block projection. This is the algebraic invariance needed before
lifting the block decomposition through continuous functional calculus.
-/
theorem twoBlockDiagonalProjection_weightedBlockDiag_gArg_apply_fromBlocks {n : ℕ}
    {θ : ℝ} {X₀ X₁ Y₀ Y₁ V₀₀ V₀₁ V₁₀ V₁₁ : Mₙ n}
    (hY₀ : MatrixPosDef Y₀) (hY₁ : MatrixPosDef Y₁)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (twoBlockDiagonalProjection (n := n) : HSOp (n + n))
        ((gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁) : HSOp (n + n))
          (twoBlockReindex (n := n) (Matrix.fromBlocks V₀₀ V₀₁ V₁₀ V₁₁))) =
      (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁) : HSOp (n + n))
        ((twoBlockDiagonalProjection (n := n) : HSOp (n + n))
          (twoBlockReindex (n := n) (Matrix.fromBlocks V₀₀ V₀₁ V₁₀ V₁₁))) := by
  rw [weightedBlockDiag_gArg_apply_twoBlockReindex_fromBlocks_all
      (n := n) (θ := θ) hY₀ hY₁ hθ0 hθ1]
  rw [twoBlockDiagonalProjection_apply_fromBlocks]
  rw [twoBlockDiagonalProjection_apply_fromBlocks]
  rw [weightedBlockDiag_gArg_apply_twoBlockReindex_fromBlocks_all
      (n := n) (θ := θ) hY₀ hY₁ hθ0 hθ1]
  simp

/--
The diagonal-block projection commutes with the weighted-block `gArg` as an
operator on the Hilbert--Schmidt space.
-/
theorem twoBlockDiagonalProjection_commute_weightedBlockDiag_gArg {n : ℕ}
    {θ : ℝ} {X₀ X₁ Y₀ Y₁ : Mₙ n}
    (hY₀ : MatrixPosDef Y₀) (hY₁ : MatrixPosDef Y₁)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    Commute
      (twoBlockDiagonalProjection (n := n) : HSOp (n + n))
      (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁) : HSOp (n + n)) := by
  rw [Commute]
  apply ContinuousLinearMap.ext
  intro V
  change
    (twoBlockDiagonalProjection (n := n) : HSOp (n + n))
        ((gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁) : HSOp (n + n)) V) =
      (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁) : HSOp (n + n))
        ((twoBlockDiagonalProjection (n := n) : HSOp (n + n)) V)
  let F := (twoBlockReindex (n := n)).symm V
  have hV :
      V =
        twoBlockReindex (n := n)
          (Matrix.fromBlocks F.toBlocks₁₁ F.toBlocks₁₂ F.toBlocks₂₁ F.toBlocks₂₂) := by
    calc
      V = twoBlockReindex (n := n) ((twoBlockReindex (n := n)).symm V) := by
          simp
      _ =
        twoBlockReindex (n := n)
          (Matrix.fromBlocks F.toBlocks₁₁ F.toBlocks₁₂ F.toBlocks₂₁ F.toBlocks₂₂) := by
          simp [F, Matrix.fromBlocks_toBlocks]
  rw [hV]
  exact
    twoBlockDiagonalProjection_weightedBlockDiag_gArg_apply_fromBlocks
      (n := n) (θ := θ) hY₀ hY₁ hθ0 hθ1

/--
The real CFC of the weighted-block `gArg` preserves the diagonal-block
subspace. Equivalently, applying the diagonal-block projection after this CFC
does not change the result on diagonal-block inputs.
-/
theorem twoBlockDiagonalProjection_hsCfcR_weightedBlockDiag_gArg_apply_fromBlocks
    {n : ℕ} {θ : ℝ} {X₀ X₁ Y₀ Y₁ V₀ V₁ : Mₙ n} (k : ℝ → ℝ)
    (hY₀ : MatrixPosDef Y₀) (hY₁ : MatrixPosDef Y₁)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (twoBlockDiagonalProjection (n := n) : HSOp (n + n))
        (hsCfcR k
          (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
          (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁))) =
      hsCfcR k
        (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
        (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)) := by
  let P : HSOp (n + n) := twoBlockDiagonalProjection (n := n)
  let T : HSOp (n + n) :=
    gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁)
  let V : Mₙ (n + n) := twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)
  have hcomm : Commute (hsCfcR k T) P := by
    simpa [hsCfcR, P, T] using
      (twoBlockDiagonalProjection_commute_weightedBlockDiag_gArg
        (n := n) (θ := θ) (X₀ := X₀) (X₁ := X₁)
        hY₀ hY₁ hθ0 hθ1).symm.cfc_real k
  have hPV : P V = V := by
    simp [P, V]
  rw [Commute] at hcomm
  have happly : (hsCfcR k T) (P V) = P ((hsCfcR k T) V) := by
    have hmul := congrArg (fun S : HSOp (n + n) => S V) hcomm
    simpa [ContinuousLinearMap.mul_apply] using hmul
  calc
    P ((hsCfcR k T) V) = (hsCfcR k T) (P V) := happly.symm
    _ = (hsCfcR k T) V := by rw [hPV]

/--
Once the CFC output is known to stay in the diagonal-block subspace, the two
diagonal block identities determine the whole blockwise CFC action.
-/
theorem hsCfcR_weightedBlockDiag_gArg_apply_fromBlocks_of_diagonal_blocks
    {n : ℕ} {θ : ℝ} {X₀ X₁ Y₀ Y₁ V₀ V₁ : Mₙ n} (k : ℝ → ℝ)
    (hY₀ : MatrixPosDef Y₀) (hY₁ : MatrixPosDef Y₁)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (h₀ :
      ((twoBlockReindex (n := n)).symm
        (hsCfcR k
          (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
          (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)))).toBlocks₁₁ =
        hsCfcR k (gArg X₀ Y₀) V₀)
    (h₁ :
      ((twoBlockReindex (n := n)).symm
        (hsCfcR k
          (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
          (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)))).toBlocks₂₂ =
        hsCfcR k (gArg X₁ Y₁) V₁) :
    hsCfcR k
        (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
        (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁)) =
      twoBlockReindex (n := n)
        (Matrix.fromBlocks
          (hsCfcR k (gArg X₀ Y₀) V₀) 0 0
          (hsCfcR k (gArg X₁ Y₁) V₁)) := by
  let W : Mₙ (n + n) :=
    hsCfcR k
      (gArg (weightedBlockDiag θ X₀ X₁) (weightedBlockDiag θ Y₀ Y₁))
      (twoBlockReindex (n := n) (Matrix.fromBlocks V₀ 0 0 V₁))
  let F : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    (twoBlockReindex (n := n)).symm W
  have hdiag : (twoBlockDiagonalProjection (n := n) : HSOp (n + n)) W = W := by
    simpa [W] using
      twoBlockDiagonalProjection_hsCfcR_weightedBlockDiag_gArg_apply_fromBlocks
        (n := n) (θ := θ) (X₀ := X₀) (X₁ := X₁) (Y₀ := Y₀) (Y₁ := Y₁)
        (V₀ := V₀) (V₁ := V₁) k hY₀ hY₁ hθ0 hθ1
  have hW :
      W =
        twoBlockReindex (n := n)
          (Matrix.fromBlocks F.toBlocks₁₁ F.toBlocks₁₂ F.toBlocks₂₁ F.toBlocks₂₂) := by
    calc
      W = twoBlockReindex (n := n) ((twoBlockReindex (n := n)).symm W) := by
          simp
      _ =
        twoBlockReindex (n := n)
          (Matrix.fromBlocks F.toBlocks₁₁ F.toBlocks₁₂ F.toBlocks₂₁ F.toBlocks₂₂) := by
          simp [F, Matrix.fromBlocks_toBlocks]
  have hproj :
      (twoBlockDiagonalProjection (n := n) : HSOp (n + n)) W =
        twoBlockReindex (n := n) (Matrix.fromBlocks F.toBlocks₁₁ 0 0 F.toBlocks₂₂) := by
    rw [hW]
    simp [F]
  calc
    W = (twoBlockDiagonalProjection (n := n) : HSOp (n + n)) W := hdiag.symm
    _ = twoBlockReindex (n := n) (Matrix.fromBlocks F.toBlocks₁₁ 0 0 F.toBlocks₂₂) :=
        hproj
    _ =
      twoBlockReindex (n := n)
        (Matrix.fromBlocks
          (hsCfcR k (gArg X₀ Y₀) V₀) 0 0
          (hsCfcR k (gArg X₁ Y₁) V₁)) := by
        simp [F, W, h₀, h₁]

/-! ### Kiefer quadratic-form bound -/
/--
The theorem-facing positive-definite predicate is stable under real convex
combinations of matrices.
-/
theorem matrixPosDef_matrixConvexCombo {n : ℕ} {θ : ℝ} {A B : Mₙ n}
    (hA : MatrixPosDef A) (hB : MatrixPosDef B) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    MatrixPosDef (matrixConvexCombo θ A B) := by
  by_cases hθzero : θ = 0
  · subst θ
    simpa [matrixConvexCombo] using hB
  by_cases hθone : θ = 1
  · subst θ
    simpa [matrixConvexCombo] using hA
  have hθpos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθzero)
  have h1θpos : 0 < 1 - θ := sub_pos.mpr (lt_of_le_of_ne hθ1 hθone)
  apply matrixPosDef_of_posDef
  have hθA : (((θ : ℂ) • A) : Mₙ n).PosDef := by
    have hr : (((θ : ℂ) • A) : Mₙ n) = (θ • A : Mₙ n) := by
      ext i j
      simp [Complex.real_smul]
    rw [hr]
    exact (matrixPosDef_posDef hA).smul hθpos
  have h1B : ((((1 - θ : ℝ) : ℂ) • B) : Mₙ n).PosDef := by
    have hr : ((((1 - θ : ℝ) : ℂ) • B) : Mₙ n) = ((1 - θ : ℝ) • B : Mₙ n) := by
      ext i j
      simp [Complex.real_smul]
    rw [hr]
    exact (matrixPosDef_posDef hB).smul h1θpos
  simpa [matrixConvexCombo] using hθA.add h1B

/-- Evaluating a Hilbert--Schmidt operator inequality on a vector gives a
quadratic-form inequality. -/
theorem hsQF_le_of_HSLE {n : ℕ} {S T : HSOp n} (h : HSLE S T) (Z : Mₙ n) :
    hsQF S Z ≤ hsQF T Z := by
  rw [HSLE, HSNonneg] at h
  have hZ := h Z
  change 0 ≤ Complex.re (Matrix.trace (Matrix.conjTranspose Z * (T Z - S Z))) at hZ
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at hZ
  change Complex.re (Matrix.trace (Matrix.conjTranspose Z * S Z)) ≤
    Complex.re (Matrix.trace (Matrix.conjTranspose Z * T Z))
  exact sub_nonneg.mp hZ

/-- The trace pairing for `hsAdjoint` agrees with the pushed-forward pairing. -/
theorem trace_hsAdjoint_eq_opmontI {n m : ℕ} (Φ : HSMap n m) (X : Mₙ n)
    (Y : Mₙ m) :
    Matrix.trace (Matrix.conjTranspose X * hsAdjoint Φ Y) =
      Matrix.trace (Matrix.conjTranspose (Φ X) * Y) := by
  calc
    Matrix.trace (Matrix.conjTranspose X * hsAdjoint Φ Y)
        = Matrix.trace (hsAdjoint Φ Y * Matrix.conjTranspose X) := by
          rw [Matrix.trace_mul_comm]
    _ = @inner ℂ (Mₙ n) inferInstance X (hsAdjoint Φ Y) := rfl
    _ = @inner ℂ (Mₙ m) inferInstance (Φ X) Y := by
          have hadj :=
            @ContinuousLinearMap.adjoint_inner_right ℂ (Mₙ n) (Mₙ m)
              (inferInstance : RCLike ℂ)
              (instMatrixNormedAddCommGroup (n := n))
              (instMatrixNormedAddCommGroup (n := m))
              (instMatrixInnerProductSpace (n := n))
              (instMatrixInnerProductSpace (n := m))
              (instMatrixCompleteSpace (n := n))
              (instMatrixCompleteSpace (n := m))
              Φ X Y
          simpa [hsAdjoint] using hadj
    _ = Matrix.trace (Y * Matrix.conjTranspose (Φ X)) := rfl
    _ = Matrix.trace (Matrix.conjTranspose (Φ X) * Y) := by
          rw [Matrix.trace_mul_comm]

/--
The trace pairing can move an `hsAdjoint` from the second factor to the first
after taking conjugate transposes.
-/
theorem trace_mul_hsAdjoint_conjTranspose' {n m : ℕ} (Φ : HSMap n m)
    (X : Mₙ n) (Y : Mₙ m) :
    Matrix.trace (X * Matrix.conjTranspose (hsAdjoint Φ Y)) =
      Matrix.trace (Φ X * Matrix.conjTranspose Y) := by
  calc
    Matrix.trace (X * Matrix.conjTranspose (hsAdjoint Φ Y)) =
        Matrix.trace (Matrix.conjTranspose
          (Matrix.conjTranspose (X * Matrix.conjTranspose (hsAdjoint Φ Y)))) := by
      simp
    _ = star (Matrix.trace
        (Matrix.conjTranspose (X * Matrix.conjTranspose (hsAdjoint Φ Y)))) := by
      rw [Matrix.trace_conjTranspose]
    _ = star (Matrix.trace (hsAdjoint Φ Y * Matrix.conjTranspose X)) := by
      simp [Matrix.conjTranspose_mul]
    _ = star (Matrix.trace (Matrix.conjTranspose X * hsAdjoint Φ Y)) := by
      rw [Matrix.trace_mul_comm]
    _ = star (Matrix.trace (Matrix.conjTranspose (Φ X) * Y)) := by
      rw [trace_hsAdjoint_eq_opmontI Φ X Y]
    _ = Matrix.trace (Matrix.conjTranspose (Matrix.conjTranspose (Φ X) * Y)) := by
      rw [Matrix.trace_conjTranspose]
    _ = Matrix.trace (Matrix.conjTranspose Y * Φ X) := by
      simp [Matrix.conjTranspose_mul]
    _ = Matrix.trace (Φ X * Matrix.conjTranspose Y) := by
      rw [Matrix.trace_mul_comm]

/-- Quadratic form of a compressed operator, expressed through the adjoint. -/
theorem hsQF_comp_adjoint {n m : ℕ} (Φ : HSMap n m) (T : HSOp n) (Z : Mₙ m) :
    hsQF (Φ.comp (T.comp (hsAdjoint Φ))) Z =
      hsQF T (hsAdjoint Φ Z) := by
  change Complex.re
      (Matrix.trace (Matrix.conjTranspose Z * Φ (T (hsAdjoint Φ Z)))) =
    Complex.re
      (Matrix.trace (Matrix.conjTranspose (hsAdjoint Φ Z) * T (hsAdjoint Φ Z)))
  calc
    Complex.re (Matrix.trace (Matrix.conjTranspose Z * Φ (T (hsAdjoint Φ Z)))) =
        Complex.re (Matrix.trace (Φ (T (hsAdjoint Φ Z)) * Matrix.conjTranspose Z)) := by
      rw [Matrix.trace_mul_comm]
    _ = Complex.re
        (Matrix.trace (T (hsAdjoint Φ Z) * Matrix.conjTranspose (hsAdjoint Φ Z))) := by
      rw [(trace_mul_hsAdjoint_conjTranspose' Φ (T (hsAdjoint Φ Z)) Z).symm]
    _ = Complex.re
        (Matrix.trace (Matrix.conjTranspose (hsAdjoint Φ Z) * T (hsAdjoint Φ Z))) := by
      rw [Matrix.trace_mul_comm]

/--
The Hilbert--Schmidt quadratic form of a block-diagonal output evaluated on a
weighted block-diagonal input is the corresponding weighted sum of the two
diagonal quadratic forms.
-/
theorem hsQF_weightedBlockDiag_fromBlocks {n : ℕ} (θ : ℝ)
    (W₀ W₁ Z₀ Z₁ : Mₙ n) :
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose (weightedBlockDiag θ Z₀ Z₁) *
            twoBlockReindex (n := n) (Matrix.fromBlocks W₀ 0 0 W₁))) =
      θ * Complex.re (Matrix.trace (Matrix.conjTranspose Z₀ * W₀)) +
        (1 - θ) * Complex.re (Matrix.trace (Matrix.conjTranspose Z₁ * W₁)) := by
  calc
    Complex.re
        (Matrix.trace
          (Matrix.conjTranspose (weightedBlockDiag θ Z₀ Z₁) *
            twoBlockReindex (n := n) (Matrix.fromBlocks W₀ 0 0 W₁))) =
        Complex.re
          (Matrix.trace
            (twoBlockReindex (n := n) (Matrix.fromBlocks W₀ 0 0 W₁) *
              Matrix.conjTranspose (weightedBlockDiag θ Z₀ Z₁))) := by
          rw [Matrix.trace_mul_comm]
    _ =
        Complex.re
          (Matrix.trace
            (Matrix.fromBlocks W₀ 0 0 W₁ *
              Matrix.conjTranspose
                (Matrix.fromBlocks ((θ : ℂ) • Z₀) 0 0 (((1 - θ : ℝ) : ℂ) • Z₁)))) := by
          rw [weightedBlockDiag, trace_twoBlockReindex_mul_conjTranspose]
    _ = Complex.re (Matrix.trace (W₀ * Matrix.conjTranspose ((θ : ℂ) • Z₀))) +
          Complex.re
            (Matrix.trace
              (W₁ * Matrix.conjTranspose (((1 - θ : ℝ) : ℂ) • Z₁))) := by
          simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
            trace_fromBlocks_diagonal]
    _ = θ * Complex.re (Matrix.trace (W₀ * Matrix.conjTranspose Z₀)) +
          (1 - θ) * Complex.re (Matrix.trace (W₁ * Matrix.conjTranspose Z₁)) := by
          have hleft :
              Complex.re (Matrix.trace (W₀ * Matrix.conjTranspose ((θ : ℂ) • Z₀))) =
                θ * Complex.re (Matrix.trace (W₀ * Matrix.conjTranspose Z₀)) := by
            rw [Matrix.conjTranspose_smul]
            have hstar : star (θ : ℂ) = (θ : ℂ) := by simp
            rw [hstar, Matrix.mul_smul, Matrix.trace_smul]
            simp
          have hright :
              Complex.re
                  (Matrix.trace
                    (W₁ * Matrix.conjTranspose (((1 - θ : ℝ) : ℂ) • Z₁))) =
                (1 - θ) * Complex.re (Matrix.trace (W₁ * Matrix.conjTranspose Z₁)) := by
            rw [Matrix.conjTranspose_smul]
            have hstar : star (((1 - θ : ℝ) : ℂ)) = (((1 - θ : ℝ) : ℂ)) := by simp
            rw [hstar, Matrix.mul_smul, Matrix.trace_smul]
            simp
          rw [hleft, hright]
    _ = θ * Complex.re (Matrix.trace (Matrix.conjTranspose Z₀ * W₀)) +
          (1 - θ) * Complex.re (Matrix.trace (Matrix.conjTranspose Z₁ * W₁)) := by
          rw [Matrix.trace_mul_comm W₀ (Matrix.conjTranspose Z₀),
            Matrix.trace_mul_comm W₁ (Matrix.conjTranspose Z₁)]

/-- Condition (4): joint convexity of the quadratic form of `G_f⁻¹`. -/
def CarlenOpMontICondition4 (f : ℝ → ℝ) : Prop :=
  ∀ {n : ℕ} {X₀ X₁ Y₀ Y₁ Z₀ Z₁ : Mₙ n} {θ : ℝ},
    MatrixPosDef X₀ →
    MatrixPosDef X₁ →
    MatrixPosDef Y₀ →
    MatrixPosDef Y₁ →
    0 ≤ θ →
    θ ≤ 1 →
    gInvQF f
        (matrixConvexCombo θ X₀ X₁)
        (matrixConvexCombo θ Y₀ Y₁)
        (matrixConvexCombo θ Z₀ Z₁)
      ≤
      θ * gInvQF f X₀ Y₀ Z₀ + (1 - θ) * gInvQF f X₁ Y₁ Z₁

/-! ### Condition (4) specialization and reciprocal target -/
/-- The convex combination of the identity matrix with itself is the identity. -/
theorem matrixConvexCombo_one_one {n : ℕ} (θ : ℝ) :
    matrixConvexCombo θ (1 : Mₙ n) (1 : Mₙ n) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    unfold matrixConvexCombo
    rw [Matrix.add_apply]
    rw [Matrix.smul_apply]
    rw [Matrix.smul_apply]
    simp
  · unfold matrixConvexCombo
    rw [Matrix.add_apply]
    rw [Matrix.smul_apply]
    rw [Matrix.smul_apply]
    simp [hij]

/--
The `Y = I` specialization of condition (4). Since `Z` is arbitrary, this
includes the rank-one choices used to read the quadratic form as a vector
quadratic form.
-/
def CarlenOpMontICondition4YOne (f : ℝ → ℝ) : Prop :=
  ∀ {n : ℕ} {X₀ X₁ Z₀ Z₁ : Mₙ n} {θ : ℝ},
    MatrixPosDef X₀ →
    MatrixPosDef X₁ →
    0 ≤ θ →
    θ ≤ 1 →
    gInvQF f
        (matrixConvexCombo θ X₀ X₁)
        (1 : Mₙ n)
        (matrixConvexCombo θ Z₀ Z₁)
      ≤
      θ * gInvQF f X₀ (1 : Mₙ n) Z₀ +
        (1 - θ) * gInvQF f X₁ (1 : Mₙ n) Z₁

/--
Condition (4) implies its `Y = I` specialization; rank-one matrix choices for
`Z` are then a special case.
-/
theorem condition4_rank_one_specialization {f : ℝ → ℝ}
    (h4 : CarlenOpMontICondition4 f) :
    CarlenOpMontICondition4YOne f := by
  intro n X₀ X₁ Z₀ Z₁ θ hX₀ hX₁ hθ0 hθ1
  have hI : MatrixPosDef (1 : Mₙ n) :=
    matrixPosDef_of_posDef Matrix.PosDef.one
  have h := h4 (n := n) (X₀ := X₀) (X₁ := X₁)
    (Y₀ := (1 : Mₙ n)) (Y₁ := (1 : Mₙ n))
    (Z₀ := Z₀) (Z₁ := Z₁) (θ := θ) hX₀ hX₁ hI hI hθ0 hθ1
  rwa [matrixConvexCombo_one_one] at h

/--
The AH1 quadratic-form convexity conclusion for the reciprocal function
`x ↦ (f x)⁻¹`.

This is the precise bridge output needed after specializing condition (4) to
`Y = I` and rank-one matrix variables.
-/
def CarlenOpMontIReciprocalQFormJointConvex (f : ℝ → ℝ) : Prop :=
  PositiveRayMatrixQFormJointConvex
    (positiveRayMatrixCfc (fun x : ℝ => (f x)⁻¹))

/--
Rank-one realization needed to read the `Y = I` specialization of condition
(4) as the AH1 vector quadratic form for `1/f`.

For each matrix size this gives a linear choice of square matrix `Z v`; the
second field says that Carlen's Hilbert--Schmidt quadratic form at `Y = I`
agrees with the AH1 vector quadratic form.
-/
def CarlenOpMontIReciprocalRankOneModel (f : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∃ R : (Fin n → ℂ) → Mₙ n,
    (∀ (θ : ℝ) (v w : Fin n → ℂ),
      R (positiveRayVectorConvexCombo θ v w) =
        matrixConvexCombo θ (R v) (R w)) ∧
    ∀ {X : Mₙ n}, MatrixPosDef X → ∀ v : Fin n → ℂ,
      gInvQF f X (1 : Mₙ n) (R v) =
        positiveRayQForm
          (positiveRayMatrixCfc (fun x : ℝ => (f x)⁻¹) n X) v

/--
The CFC naturality component of the `Y = I` bridge: reciprocal CFC of right
multiplication by `X` is right multiplication by the reciprocal matrix CFC.
-/
def CarlenOpMontIRightMulCfcModel (f : ℝ → ℝ) : Prop :=
  ∀ {n : ℕ} {X : Mₙ n}, MatrixPosDef X →
    hsCfcR (fun x : ℝ => (f x)⁻¹) (rightMul X) =
      rightMul (positiveRayMatrixCfc (fun x : ℝ => (f x)⁻¹) n X)

end

end Quantum.TraceInequality.Loewner.HiaiPetz
