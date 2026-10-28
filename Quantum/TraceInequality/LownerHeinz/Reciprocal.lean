/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LownerHeinz.Defs

/-!
# Reciprocal inequalities and shifted reciprocals


-/

namespace LownerHeinzCore

universe u

open CFC

section Spectrum

variable {𝓐 : Type u}
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
variable [Nontrivial 𝓐]
variable [NonnegSpectrumClass ℝ 𝓐]

/-! ### Reciprocal inequalities and Schur complements -/

omit [Nontrivial (𝓐)] [NonnegSpectrumClass ℝ 𝓐] in
/-- A self-adjoint element with spectrum in `[0, ∞)` is nonnegative. -/
lemma nonneg_of_spectrum_subset_Ici {X : 𝓐} (hX : IsSelfAdjoint X)
    (Xs : spectrum ℝ X ⊆ Set.Ici (0 : ℝ)) : 0 ≤ X := by
  have h0 : 0 ≤ cfcR (fun x : ℝ ↦ x) X := by
    dsimp [cfcR]
    exact cfc_nonneg fun x hx ↦ Set.mem_Ici.mp (Xs hx)
  simpa [cfcR, cfc_id' (R := ℝ) (a := X) (ha := hX)] using h0

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
lemma isSelfAdjoint_convexCombo (t : ℝ) {A B : 𝓐}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint ((1 - t) • A + t • B) :=
  ((IsSelfAdjoint.all (1 - t)).smul hA).add ((IsSelfAdjoint.all t).smul hB)

lemma spectrum_convexCombo_Ioi {A B : 𝓐} {t : ℝ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (As : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)) (Bs : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    spectrum ℝ ((1 - t) • A + t • B) ⊆ Set.Ioi (0 : ℝ) := by
  set C : 𝓐 := (1 - t) • A + t • B
  have hC : IsSelfAdjoint C := by simpa [C] using isSelfAdjoint_convexCombo t hA hB
  have hApos : ∃ r > 0, algebraMap ℝ (𝓐) r ≤ A := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := 𝓐) (a := A) (ha := hA)).2 ?_
    intro x hx
    exact As hx
  have hBpos : ∃ r > 0, algebraMap ℝ (𝓐) r ≤ B := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := 𝓐) (a := B) (ha := hB)).2 ?_
    intro x hx
    exact Bs hx
  rcases hApos with ⟨rA, hrA, hrA_le⟩
  rcases hBpos with ⟨rB, hrB, hrB_le⟩
  set rC : ℝ := (1 - t) * rA + t * rB
  have hrC : 0 < rC := by
    have h := (lt_min hrA hrB).trans_le
      (Convex.min_le_combo rA rB (sub_nonneg.mpr ht1) ht0 (by ring))
    simpa [rC, smul_eq_mul] using h
  have hrC_le : algebraMap ℝ (𝓐) rC ≤ C := by
    have hsum : (1 - t) • algebraMap ℝ (𝓐) rA + t • algebraMap ℝ (𝓐) rB ≤ C := by
      simpa [C] using add_le_add (smul_le_smul_of_nonneg_left hrA_le (sub_nonneg.mpr ht1))
        (smul_le_smul_of_nonneg_left hrB_le ht0)
    have hLHS :
        (1 - t) • algebraMap ℝ (𝓐) rA + t • algebraMap ℝ (𝓐) rB =
          algebraMap ℝ (𝓐) rC := by
      simp [rC, Algebra.smul_def]
    simpa [hLHS] using hsum
  intro x hx
  simpa [C] using
    (CFC.exists_pos_algebraMap_le_iff (A := 𝓐) (a := C) (ha := hC)).1 ⟨rC, hrC, hrC_le⟩ x hx

omit [Nontrivial (𝓐)] in
omit [NonnegSpectrumClass ℝ 𝓐] in
private lemma posSemidef_block_one_inv {A : 𝓐} (hA : IsSelfAdjoint A)
    (As : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)) :
    Matrix.PosSemidef
      (!![A, 1; 1, cfcR (fun x : ℝ ↦ x⁻¹) A] : Matrix (Fin 2) (Fin 2) 𝓐) := by
  -- Gram matrix construction using `A^{1/2}` and `A^{-1/2}`
  set sqrtA : 𝓐 := cfcR (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) A
  set invSqrtA : 𝓐 := cfcR (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) A
  set v : Fin 2 → 𝓐 := fun i => if i = 0 then sqrtA else invSqrtA
  have posV : Matrix.PosSemidef (Matrix.vecMulVec v (star v)) := by
    simpa using (Matrix.posSemidef_vecMulVec_self_star (R := 𝓐) v)
  have hsqrtA : IsSelfAdjoint sqrtA := by
    dsimp [sqrtA, cfcR]
    exact cfc_predicate _ _
  have hinvSqrtA : IsSelfAdjoint invSqrtA := by
    dsimp [invSqrtA, cfcR]
    exact cfc_predicate _ _
  have hcont_sqrt : ContinuousOn (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) (spectrum ℝ A) :=
    fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt (As hx)))).continuousWithinAt
  have hcont_invSqrt : ContinuousOn (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (spectrum ℝ A) :=
    fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt (As hx)))).continuousWithinAt
  have sqrtA_mul_invSqrtA : sqrtA * invSqrtA = (1 : 𝓐) := by
    dsimp [sqrtA, invSqrtA, cfcR]
    rw [← cfc_mul _ _ A hcont_sqrt hcont_invSqrt, ← cfc_const_one ℝ A]
    apply cfc_congr
    intro x hx
    dsimp only
    rw [← Real.rpow_add (As hx), show ((1 : ℝ) / 2 + (-1) / 2 : ℝ) = 0 from by ring, Real.rpow_zero]
  have invSqrtA_mul_sqrtA : invSqrtA * sqrtA = (1 : 𝓐) := by
    dsimp [sqrtA, invSqrtA, cfcR]
    rw [← cfc_mul _ _ A hcont_invSqrt hcont_sqrt, ← cfc_const_one ℝ A]
    apply cfc_congr
    intro x hx
    dsimp only
    rw [← Real.rpow_add (As hx), show ((-1 : ℝ) / 2 + (1 : ℝ) / 2 : ℝ) = 0 from by ring,
      Real.rpow_zero]
  have invSqrtA_mul_invSqrtA : invSqrtA * invSqrtA = cfcR (fun x : ℝ ↦ x ^ (-1 : ℝ)) A := by
    dsimp [invSqrtA, cfcR]
    rw [← cfc_mul _ _ A hcont_invSqrt hcont_invSqrt]
    apply cfc_congr
    intro x hx
    dsimp only
    rw [← Real.rpow_add (As hx), show ((-1 : ℝ) / 2 + (-1 : ℝ) / 2 : ℝ) = -1 from by ring]
  have sqrtA_mul_sqrtA : sqrtA * sqrtA = A := by
    dsimp [sqrtA, cfcR]
    rw [← cfc_mul _ _ A hcont_sqrt hcont_sqrt]
    calc
      cfcR (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2)) A =
          cfcR (fun x : ℝ ↦ x) A := by
            apply cfc_congr
            intro x hx
            dsimp only
            rw [← Real.rpow_add (As hx),
              show ((1 : ℝ) / 2 + (1 : ℝ) / 2 : ℝ) = 1 from by ring, Real.rpow_one]
      _ = A := cfc_id' (R := ℝ) (a := A) (ha := hA)
  have invA_eq : cfcR (fun x : ℝ ↦ x ^ (-1 : ℝ)) A = cfcR (fun x : ℝ ↦ x⁻¹) A := by
    dsimp [cfcR]
    apply cfc_congr
    intro x hx
    have hxne : x ≠ 0 := ne_of_gt (As hx)
    simpa [hxne] using (Real.rpow_neg_one x)
  have hEq : Matrix.vecMulVec v (star v) = (!![A, 1; 1, cfcR (fun x : ℝ ↦ x⁻¹) A] :
      Matrix (Fin 2) (Fin 2) (𝓐)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecMulVec_apply, v, hsqrtA.star_eq, hinvSqrtA.star_eq, sqrtA_mul_sqrtA,
        sqrtA_mul_invSqrtA, invSqrtA_mul_sqrtA, invSqrtA_mul_invSqrtA, invA_eq]
  simpa [hEq] using posV

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
private lemma schur_conj_eq_diagonal {C D invC : 𝓐} (hInvC_sa : IsSelfAdjoint invC)
    (invC_mul_C : invC * C = (1 : 𝓐)) (C_mul_invC : C * invC = (1 : 𝓐)) :
    star (!![(1 : 𝓐), -invC; 0, 1] : Matrix (Fin 2) (Fin 2) (𝓐))
        * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) (𝓐))
        * (!![(1 : 𝓐), -invC; 0, 1] : Matrix (Fin 2) (Fin 2) (𝓐))
      = Matrix.diagonal (fun i : Fin 2 => if i = 0 then C else D - invC) := by
  set U : Matrix (Fin 2) (Fin 2) (𝓐) := !![(1 : 𝓐), -invC; 0, 1]
  have hstarU : star U = !![(1 : 𝓐), 0; -invC, 1] := by
    dsimp [U]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hInvC_sa.star_eq]
  have hP :
      star U * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) (𝓐)) =
        !![C, 1; -invC * C + 1, -invC + D] := by
    simp [hstarU, U]
  have hQ :
      star U * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) (𝓐)) * U =
        !![C, 0; 0, D - invC] := by
    have hstep :
        star U * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) (𝓐)) * U =
          (!![C, 1; -invC * C + 1, -invC + D] : Matrix (Fin 2) (Fin 2) (𝓐)) * U := by
      simpa [mul_assoc] using congrArg (fun X => X * U) hP
    dsimp [U] at hstep ⊢
    simp [hstep, C_mul_invC, invC_mul_C, sub_eq_add_neg, add_comm]
  have hdiag :
      (Matrix.diagonal (fun i : Fin 2 => if i = 0 then C else D - invC)) =
        (!![C, 0; 0, D - invC] : Matrix (Fin 2) (Fin 2) (𝓐)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  simpa [hdiag] using hQ

/-- `x ↦ 1 / x` is operator convex on `(0, ∞)`, via a Schur-complement argument.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Lemma 2.7. Correspondence restricted to the exponent
range and domain of this declaration. -/
/- Reciprocal operator convexity
    (Carlen 2009, Lemma 2.7, operator-convexity part) -/
/- (Carlen 2009, Lemma 2.7, operator-convexity part) The function $f(t)=t^{-1}$ is operator convex,
    and the function $f(t)=-t^{-1}$ is operator monotone.
    *Lean deviation*: this node records the convexity part as $x \mapsto 1/x$ operator
    convex on $(0,\infty)$ in the sense of the definition of `OperatorConvexOn`, over a unital
    $C^*$-algebra rather than matrices. -/
/- Carlen09 (proof of Lemma 2.7): after the same conjugation
    $C=A^{-1/2}BA^{-1/2}$, midpoint convexity is reduced to
    \[
      \frac12 A^{-1}+\frac12 B^{-1}
        - \left(\frac{A+B}{2}\right)^{-1}
      =
      A^{-1/2}\left[
        \frac12 I+\frac12 C^{-1}-\left(\frac{I+C}{2}\right)^{-1}
      \right]A^{-1/2}.
    \]
    The bracket is positive by applying the scalar arithmetic--harmonic mean inequality with
    $a = 1$ and $c$ any eigenvalue of $C^{-1}$; continuity upgrades midpoint convexity to
    full convexity.
    *Lean deviation*: the formal proof uses a $2 \times 2$ block-matrix positivity
    argument and a Schur-complement calculation, rather than the scalar
    arithmetic-harmonic-mean reduction. -/
theorem one_div_operatorConvexOn_Ioi :
    OperatorConvexOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x) := by
  dsimp [OperatorConvexOn]
  intro A B t hA hB ht0 ht1 As Bs
  -- rewrite `1/x` as `x⁻¹`
  simp only [one_div]
  set C : 𝓐 := (1 - t) • A + t • B
  have hC : IsSelfAdjoint C := by simpa [C] using isSelfAdjoint_convexCombo t hA hB
  have specC : spectrum ℝ C ⊆ Set.Ioi (0 : ℝ) := by
    simpa [C] using
      spectrum_convexCombo_Ioi  (A := A) (B := B) (t := t) hA hB ht0 ht1 As Bs
  set invA : 𝓐 := cfcR (fun x : ℝ ↦ x⁻¹) A
  set invB : 𝓐 := cfcR (fun x : ℝ ↦ x⁻¹) B
  set invC : 𝓐 := cfcR (fun x : ℝ ↦ x⁻¹) C
  set D : 𝓐 := (1 - t) • invA + t • invB
  let M_A : Matrix (Fin 2) (Fin 2) (𝓐) := !![A, 1; 1, invA]
  let M_B : Matrix (Fin 2) (Fin 2) (𝓐) := !![B, 1; 1, invB]
  let M : Matrix (Fin 2) (Fin 2) (𝓐) := (1 - t) • M_A + t • M_B
  have posA : Matrix.PosSemidef M_A := by
    simpa [M_A, invA] using posSemidef_block_one_inv  (A := A) hA As
  have posB : Matrix.PosSemidef M_B := by
    simpa [M_B, invB] using posSemidef_block_one_inv  (A := B) hB Bs
  have posM : Matrix.PosSemidef M := by
    simpa [M] using Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul (x := M_A) (a := (1 - t)) posA (sub_nonneg.mpr ht1))
      (Matrix.PosSemidef.smul (x := M_B) (a := t) posB ht0)
  have hM : M = !![C, 1; 1, D] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M, M_A, M_B, C, D] <;> module
  let U : Matrix (Fin 2) (Fin 2) (𝓐) := !![(1 : 𝓐), -invC; 0, 1]
  have hU : IsUnit U := by
    refine ⟨⟨U, !![(1 : 𝓐), invC; 0, 1], ?_, ?_⟩, rfl⟩ <;>
      simp [U, Matrix.one_fin_two]
  have hconj :
      star U * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) (𝓐)) * U
        = Matrix.diagonal (fun i : Fin 2 => if i = 0 then C else D - invC) := by
    have hInvC_sa : IsSelfAdjoint invC := by
      dsimp [invC, cfcR]
      exact cfc_predicate _ _
    let uC : 𝓐ˣ := cfcUnits (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
      (fun x : ℝ ↦ x) C (fun x hx ↦ ne_of_gt (specC hx)) (ha := hC)
    have huC : (uC : 𝓐) = C := by
      simpa [uC, cfcUnits] using cfc_id' (R := ℝ) (a := C) (ha := hC)
    have huCinv : (↑uC⁻¹ : 𝓐) = invC := rfl
    have invC_mul_C : invC * C = (1 : 𝓐) := by
      rw [← huCinv, ← huC]
      exact Units.inv_mul uC
    have C_mul_invC : C * invC = (1 : 𝓐) := by
      rw [← huC, ← huCinv]
      exact Units.mul_inv uC
    simpa [U] using
      schur_conj_eq_diagonal  (C := C) (D := D) (invC := invC)
        hInvC_sa invC_mul_C C_mul_invC
  have posDiag :
      Matrix.PosSemidef (Matrix.diagonal (fun i : Fin 2 => if i = 0 then C else D - invC)) := by
    rw [← hconj, ← hM]
    simpa [Matrix.star_eq_conjTranspose] using posM.conjTranspose_mul_mul_same U
  exact le_of_sub_nonneg (by simpa using
    (Matrix.posSemidef_diagonal_iff (R := 𝓐)
      (d := fun i : Fin 2 => if i = 0 then C else D - invC)).1 posDiag (1 : Fin 2))

end Spectrum

end LownerHeinzCore
