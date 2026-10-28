/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.HiaiPetz.Ambient.MatrixInstances
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

namespace Matrix.PosDef

open HiaiPetz Matrix Unitary
open scoped MatrixOrder ComplexOrder
open scoped Matrix.Norms.Frobenius
open scoped HiaiPetz.AmbientInstances

noncomputable section MatrixScopedInstances

-- Finite-dimensional spectral lower bounds still elaborate through the eigenvalue model.
/-- Every positive definite matrix dominates `r • 1` for some real `r > 0`.
The proof chooses the minimum eigenvalue in finite dimension. -/
theorem exists_pos_algebraMap_le {n : ℕ} {B : Mₙ n}
    (hB : Matrix.PosDef B) :
    ∃ r > 0, algebraMap ℝ (Mₙ n) r ≤ B := by
  classical
  letI : NormedAddCommGroup (Mₙ n) := instMatrixNormedAddCommGroup (n := n)
  letI : NormedSpace ℂ (Mₙ n) := instMatrixNormedSpace (n := n)
  letI : InnerProductSpace ℂ (Mₙ n) := instMatrixInnerProductSpace (n := n)
  letI : CompleteSpace (Mₙ n) := instMatrixCompleteSpace (n := n)
  by_cases hn : Nonempty (Fin n)
  · letI := hn
    let hBpos : B.PosDef := hB
    /- Step 1: Choose the minimum eigenvalue as a positive scalar lower bound candidate. -/
    let σ : Finset ℝ := Finset.univ.image (fun i : Fin n => hBpos.1.eigenvalues i)
    have hσne : σ.Nonempty := by
      rcases hn with ⟨i⟩
      exact ⟨hBpos.1.eigenvalues i, by simp [σ]⟩
    let r : ℝ := σ.min' hσne
    have hr : 0 < r := by
      rcases Finset.mem_image.mp (Finset.min'_mem σ hσne) with ⟨i, _, hi⟩
      have hri : r = hBpos.1.eigenvalues i := by
        simpa [r] using hi.symm
      simpa [hri] using hBpos.eigenvalues_pos i
    have hr_le : ∀ i : Fin n, r ≤ hBpos.1.eigenvalues i := by
      intro i
      simpa [r] using
        (Finset.min'_le (s := σ) (x := hBpos.1.eigenvalues i) (by simp [σ]))
    let U : Mₙ n := ↑hBpos.1.eigenvectorUnitary
    let D : Mₙ n := Matrix.diagonal (fun i => ((hBpos.1.eigenvalues i - r : ℝ) : ℂ))
    /- Step 2: Show the diagonal spectral remainder B_diag - rI is positive semidefinite. -/
    have hD_psd : D.PosSemidef := by
      rw [show D = Matrix.diagonal (fun i => ((hBpos.1.eigenvalues i - r : ℝ) : ℂ)) by rfl]
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      exact_mod_cast sub_nonneg.mpr (hr_le i)
    have hone :
        Unitary.conjStarAlgAut ℂ _ hBpos.1.eigenvectorUnitary ((r : ℂ) • (1 : Mₙ n)) =
          (r : ℂ) • (1 : Mₙ n) := by
      calc
        Unitary.conjStarAlgAut ℂ _ hBpos.1.eigenvectorUnitary ((r : ℂ) • (1 : Mₙ n))
            = (r : ℂ) •
                (Unitary.conjStarAlgAut ℂ _ hBpos.1.eigenvectorUnitary (1 : Mₙ n)) := by
              exact map_smul
                (Unitary.conjStarAlgAut ℂ _ hBpos.1.eigenvectorUnitary) (r : ℂ) (1 : Mₙ n)
        _ = (r : ℂ) • (1 : Mₙ n) := by
              rw [map_one]
    have hspec :
        B =
          Unitary.conjStarAlgAut ℂ _ hBpos.1.eigenvectorUnitary
            (Matrix.diagonal (Complex.ofReal ∘ hBpos.1.eigenvalues)) := by
      simpa [U, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc, Function.comp_def] using
        hBpos.1.spectral_theorem
    have hdiag_sub :
        Matrix.diagonal (Complex.ofReal ∘ hBpos.1.eigenvalues) -
          ((r : ℂ) • (1 : Mₙ n)) = D := by
      ext i j
      change (Matrix.diagonal (Complex.ofReal ∘ hBpos.1.eigenvalues)) i j -
          (r : ℂ) * (1 : Mₙ n) i j =
        (Matrix.diagonal fun k => ((hBpos.1.eigenvalues k - r : ℝ) : ℂ)) i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.diagonal]
      · simp [Matrix.diagonal, hij]
    have hinside_psd :
        (Matrix.diagonal (Complex.ofReal ∘ hBpos.1.eigenvalues) -
          ((r : ℂ) • (1 : Mₙ n))).PosSemidef := by
      rw [hdiag_sub]
      exact hD_psd
    have halg :
        algebraMap ℝ (Mₙ n) r = ((r : ℂ) • (1 : Mₙ n)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]
      · simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, hij]
    /- Step 3: Transport the positive diagonal remainder back through the spectral unitary. -/
    have hstep :
        B - algebraMap ℝ (Mₙ n) r =
          Unitary.conjStarAlgAut ℂ _ hBpos.1.eigenvectorUnitary
            (Matrix.diagonal (Complex.ofReal ∘ hBpos.1.eigenvalues) -
              ((r : ℂ) • (1 : Mₙ n))) := by
      calc
        B - algebraMap ℝ (Mₙ n) r
            = B - ((r : ℂ) • (1 : Mₙ n)) := by
                rw [halg]
        _ = Unitary.conjStarAlgAut ℂ _ hBpos.1.eigenvectorUnitary
              (Matrix.diagonal (Complex.ofReal ∘ hBpos.1.eigenvalues)) -
              ((r : ℂ) • (1 : Mₙ n)) := by
                exact congrArg (fun M : Mₙ n => M - ((r : ℂ) • (1 : Mₙ n))) hspec
        _ = Unitary.conjStarAlgAut ℂ _ hBpos.1.eigenvectorUnitary
              (Matrix.diagonal (Complex.ofReal ∘ hBpos.1.eigenvalues)) -
              Unitary.conjStarAlgAut ℂ _ hBpos.1.eigenvectorUnitary
                ((r : ℂ) • (1 : Mₙ n)) := by
                  exact congrArg
                    (fun M : Mₙ n =>
                      Unitary.conjStarAlgAut ℂ _ hBpos.1.eigenvectorUnitary
                        (Matrix.diagonal (Complex.ofReal ∘ hBpos.1.eigenvalues)) - M)
                    hone.symm
        _ = Unitary.conjStarAlgAut ℂ _ hBpos.1.eigenvectorUnitary
              (Matrix.diagonal (Complex.ofReal ∘ hBpos.1.eigenvalues) -
                ((r : ℂ) • (1 : Mₙ n))) := by
                  rw [← map_sub]
    have hnonneg : 0 ≤ B - algebraMap ℝ (Mₙ n) r := by
      rw [hstep]
      exact (Matrix.nonneg_iff_posSemidef).mpr <|
        (Matrix.IsUnit.posSemidef_star_right_conjugate_iff
          (hU := Unitary.isUnit_coe (U := hBpos.1.eigenvectorUnitary))).2 hinside_psd
    exact ⟨r, hr, by simpa [sub_nonneg] using hnonneg⟩
  · haveI : IsEmpty (Fin n) := not_nonempty_iff.mp hn
    /- Step 4: In the empty matrix case, subsingleton order makes r = 1 sufficient. -/
    have hB1 : B = (1 : Mₙ n) := Subsingleton.elim _ _
    refine ⟨1, zero_lt_one, ?_⟩
    simp [hB1]

/-- A positive Hilbert--Schmidt map preserves positive definiteness from `B`
to `Φ B` provided the image of the identity, `Φ 1`, is positive definite. -/
theorem image_of_isPositiveMap {n m : ℕ} (Φ : HSMap n m)
    (hPos : IsPositiveMap Φ) {B : Mₙ n}
    (hB : Matrix.PosDef B) (hΦ1 : Matrix.PosDef (Φ 1)) :
    Matrix.PosDef (Φ B) := by
  rcases Matrix.PosDef.exists_pos_algebraMap_le hB with ⟨r, hr, hr_le⟩
  have hΦB_nonneg : 0 ≤ Φ B := hPos (Matrix.PosDef.nonneg hB)
  have hΦdiff_nonneg : 0 ≤ Φ (B - algebraMap ℝ (Mₙ n) r) := by
    exact hPos (sub_nonneg.mpr hr_le)
  have halgebraMap :
      algebraMap ℝ (Mₙ n) r = (r : ℂ) • (1 : Mₙ n) := by
    ext i j
    simp [Algebra.algebraMap_eq_smul_one]
  have hΦlower : (r : ℂ) • (Φ (1 : Mₙ n)) ≤ Φ B := by
    rw [halgebraMap, Φ.map_sub, Φ.map_smul] at hΦdiff_nonneg
    exact sub_nonneg.mp hΦdiff_nonneg
  have hΦB_psd : (Φ B).PosSemidef := (Matrix.nonneg_iff_posSemidef).mp hΦB_nonneg
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hΦB_psd.isHermitian ?_
  intro x hx
  have hlower_nonneg : 0 ≤ Φ B - (r : ℂ) • (Φ (1 : Mₙ n)) :=
    sub_nonneg.mpr hΦlower
  have hlower_psd :
      (Φ B - (r : ℂ) • (Φ (1 : Mₙ n))).PosSemidef :=
    (Matrix.nonneg_iff_posSemidef).mp hlower_nonneg
  have hrest :
      0 ≤ Complex.re
        (dotProduct (star x)
          (Matrix.mulVec (Φ B - (r : ℂ) • (Φ (1 : Mₙ n))) x)) :=
    hlower_psd.re_dotProduct_nonneg x
  have hunit := hΦ1.re_dotProduct_pos hx
  have hscalar :
      Complex.re
        (dotProduct (star x) (Matrix.mulVec ((r : ℂ) • Φ (1 : Mₙ n)) x)) =
      r * Complex.re (dotProduct (star x) (Matrix.mulVec (Φ (1 : Mₙ n)) x)) := by
    have hdot :
        dotProduct (star x) (Matrix.mulVec ((r : ℂ) • Φ (1 : Mₙ n)) x) =
          (r : ℂ) * dotProduct (star x) (Matrix.mulVec (Φ (1 : Mₙ n)) x) := by
      rw [Matrix.smul_mulVec, dotProduct_smul]
      simp [smul_eq_mul]
    rw [hdot]
    simp
  have hunit_pos :
      0 < Complex.re
        (dotProduct (star x) (Matrix.mulVec ((r : ℂ) • Φ (1 : Mₙ n)) x)) := by
    rw [hscalar]
    exact mul_pos hr hunit
  have hdecomp :
      dotProduct (star x) (Matrix.mulVec (Φ B) x) =
        dotProduct (star x)
          (Matrix.mulVec (Φ B - (r : ℂ) • Φ (1 : Mₙ n)) x) +
        dotProduct (star x)
          (Matrix.mulVec ((r : ℂ) • Φ (1 : Mₙ n)) x) := by
    calc
      dotProduct (star x) (Matrix.mulVec (Φ B) x)
          = dotProduct (star x)
              (Matrix.mulVec ((Φ B - (r : ℂ) • Φ (1 : Mₙ n)) +
                (r : ℂ) • Φ (1 : Mₙ n)) x) := by
                congr 1
                simp
      _ = dotProduct (star x)
            (Matrix.mulVec (Φ B - (r : ℂ) • Φ (1 : Mₙ n)) x +
              Matrix.mulVec ((r : ℂ) • Φ (1 : Mₙ n)) x) := by
              simpa using congrArg (dotProduct (star x))
                (Matrix.add_mulVec
                  (Φ B - (r : ℂ) • Φ (1 : Mₙ n))
                  ((r : ℂ) • Φ (1 : Mₙ n)) x)
      _ = dotProduct (star x) (Matrix.mulVec (Φ B - (r : ℂ) • Φ (1 : Mₙ n)) x) +
            dotProduct (star x) (Matrix.mulVec ((r : ℂ) • Φ (1 : Mₙ n)) x) := by
              simp [dotProduct_add]
  refine RCLike.pos_iff.mpr ⟨?_, ?_⟩
  · rw [hdecomp]
    exact add_pos_of_nonneg_of_pos hrest hunit_pos
  · simpa using hΦB_psd.isHermitian.im_star_dotProduct_mulVec_self x

end MatrixScopedInstances

end Matrix.PosDef
