/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LownerHeinz.Defs

/-!
# Reciprocal inequalities and shifted reciprocals

This file is part of the split `LownerHeinzCore` development.
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

omit [Nontrivial 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
/-- Reciprocal antitonicity
(Carlen 2010, Lemma 2.7, equivalent antitone form of its monotonicity part)

The function $f(t)=t^{-1}$ is operator convex,
and the function $f(t)=-t^{-1}$ is operator monotone.
\emph{Lean deviation}: this node records the equivalent decreasing form: $x \mapsto 1/x$
is operator antitone on $(0,\infty)$ in the sense of `OperatorAntitoneOn`,
over a unital $C^*$-algebra rather than matrices.

Proof: Carlen (2010), proof of Lemma 2.7: for monotonicity, take
$A,B \in \mathbf{H}_n^+$ and set $C=A^{-1/2}BA^{-1/2}$. Then
\[
  A^{-1}-(A+B)^{-1}
    = A^{-1/2}\bigl[I-(I+C)^{-1}\bigr]A^{-1/2}.
\]
Since $C \in \mathbf{H}_n^+$, also $I-(I+C)^{-1} \in \mathbf{H}_n^+$, so the displayed
difference is positive; this proves that $-t^{-1}$ is operator monotone, equivalently that
$t^{-1}$ is decreasing.
\emph{Lean deviation}: the formal proof works directly in the fixed $C^*$-algebra using
\texttt{cfcUnits} to identify the functional calculus inverse and
\texttt{CStarAlgebra.inv\_le\_inv} to obtain the inverse-order inequality.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Lemma 2.7. Correspondence restricted to the exponent
range and domain of this declaration. -/
theorem one_div_operatorAntitoneOn_Ioi :
    OperatorAntitoneOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x) := by
  dsimp [OperatorAntitoneOn]
  intro A B hA_sa hB_sa BA As Bs
  let f : ℝ → ℝ := fun x ↦ x
  have B_nonneg : 0 ≤ B :=
    nonneg_of_spectrum_subset_Ici hB_sa (Bs.trans Set.Ioi_subset_Ici_self)
  have hA_ne0 : ∀ x ∈ spectrum ℝ A, f x ≠ 0 := by
    intro x hx
    exact ne_of_gt (As hx)
  have hB_ne0 : ∀ x ∈ spectrum ℝ B, f x ≠ 0 := by
    intro x hx
    exact ne_of_gt (Bs hx)
  let uA : (𝓐)ˣ :=
    cfcUnits (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) f A hA_ne0 (ha := hA_sa)
  let uB : (𝓐)ˣ :=
    cfcUnits (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) f B hB_ne0 (ha := hB_sa)
  have huA_val : (uA : 𝓐) = A := by
    simp [uA, cfcUnits, f, cfc_id' (R := ℝ) (a := A) (ha := hA_sa)]
  have huB_val : (uB : 𝓐) = B := by
    simp [uB, cfcUnits, f, cfc_id' (R := ℝ) (a := B) (ha := hB_sa)]
  have huB_nonneg : 0 ≤ (uB : 𝓐) := by
    simpa [huB_val] using B_nonneg
  have hub_le_hua : (uB : 𝓐) ≤ (uA : 𝓐) := by
    simpa [huA_val, huB_val] using BA
  have hinv : (↑uA⁻¹ : 𝓐) ≤ (↑uB⁻¹ : 𝓐) := by
    simpa using
      (CStarAlgebra.inv_le_inv (A := 𝓐) (a := uB) (b := uA) huB_nonneg hub_le_hua)
  -- convert the inverse inequality back to the desired `cfcR` inequality
  simpa [uA, uB, cfcUnits, cfcR, f, one_div] using hinv

omit [Nontrivial 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
/-- The reciprocal functional calculus is antitone on the positive spectrum. -/
@[gcongr]
theorem cfcR_one_div_le_cfcR_one_div_of_le {A B : 𝓐}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hBA : B ≤ A)
    (hspA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hspB : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    cfcR (fun x : ℝ ↦ 1 / x) A ≤ cfcR (fun x : ℝ ↦ 1 / x) B :=
  one_div_operatorAntitoneOn_Ioi hA hB hBA hspA hspB

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

/-- Reciprocal operator convexity
(Carlen 2010, Lemma 2.7, operator-convexity part)

The function $f(t)=t^{-1}$ is operator convex,
and the function $f(t)=-t^{-1}$ is operator monotone.
\emph{Lean deviation}: this node records the convexity part as $x \mapsto 1/x$ operator
convex on $(0,\infty)$ in the sense of `OperatorConvexOn`, over a unital
$C^*$-algebra rather than matrices.

Proof: Carlen (2010), proof of Lemma 2.7: after the same conjugation
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
\emph{Lean deviation}: the formal proof uses a $2 \times 2$ block-matrix positivity
argument and a Schur-complement calculation, rather than the scalar
arithmetic-harmonic-mean reduction.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Lemma 2.7. Correspondence restricted to the exponent
range and domain of this declaration. -/
theorem operatorConvexOn_one_div_Ioi :
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

/-! ### Positive-cone restrictions and shifted reciprocals -/

omit [Nontrivial 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
/-- On a set `s ⊆ [0, ∞)` the self-adjointness hypotheses in `OperatorMonotoneOn` are
equivalent to the previous nonnegativity-based formulation, since for self-adjoint elements
`spectrum ℝ A ⊆ s ⊆ [0, ∞)` already forces `0 ≤ A`. -/
theorem operatorMonotoneOn_iff_of_subset_Ici {s : Set ℝ} (hs : s ⊆ Set.Ici (0 : ℝ))
    (f : ℝ → ℝ) :
    OperatorMonotoneOn (𝓐 := 𝓐) s f ↔
      ∀ ⦃A B : 𝓐⦄, 0 ≤ A → 0 ≤ B → B ≤ A →
        spectrum ℝ A ⊆ s → spectrum ℝ B ⊆ s → cfcR f B ≤ cfcR f A := by
  constructor
  · intro h A B hA0 hB0 hBA hsA hsB
    exact h (IsSelfAdjoint.of_nonneg hA0) (IsSelfAdjoint.of_nonneg hB0) hBA hsA hsB
  · intro h A B hA hB hBA hsA hsB
    exact h (nonneg_of_spectrum_subset_Ici hA (hsA.trans hs))
      (nonneg_of_spectrum_subset_Ici hB (hsB.trans hs)) hBA hsA hsB

omit [Nontrivial 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
/-- On a set `s ⊆ [0, ∞)` the self-adjointness hypotheses in `OperatorAntitoneOn` are
equivalent to the previous nonnegativity-based formulation. -/
theorem operatorAntitoneOn_iff_of_subset_Ici {s : Set ℝ} (hs : s ⊆ Set.Ici (0 : ℝ))
    (f : ℝ → ℝ) :
    OperatorAntitoneOn (𝓐 := 𝓐) s f ↔
      ∀ ⦃A B : 𝓐⦄, 0 ≤ A → 0 ≤ B → B ≤ A →
        spectrum ℝ A ⊆ s → spectrum ℝ B ⊆ s → cfcR f A ≤ cfcR f B := by
  constructor
  · intro h A B hA0 hB0 hBA hsA hsB
    exact h (IsSelfAdjoint.of_nonneg hA0) (IsSelfAdjoint.of_nonneg hB0) hBA hsA hsB
  · intro h A B hA hB hBA hsA hsB
    exact h (nonneg_of_spectrum_subset_Ici hA (hsA.trans hs))
      (nonneg_of_spectrum_subset_Ici hB (hsB.trans hs)) hBA hsA hsB

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
/-- Functional calculus of the shift `x ↦ x + t` is the algebraic shift by `t`. -/
private lemma cfcR_shift_eq {t : ℝ} {X : 𝓐} (hX : IsSelfAdjoint X) :
    cfcR (fun x : ℝ ↦ x + t) X = X + algebraMap ℝ 𝓐 t := by
  dsimp [cfcR]
  simpa [cfc_id' (R := ℝ) (a := X) (ha := hX)] using
    (cfc_add_const (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := t)
      (f := fun x : ℝ ↦ x) (a := X) (ha := hX))

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
/-- Shifting by `t > 0` moves a spectrum inside `[0, ∞)` into `(0, ∞)`. -/
private lemma spectrum_cfcR_shift_subset_Ioi {t : ℝ} (ht : 0 < t) {X : 𝓐}
    (hX : IsSelfAdjoint X) (Xs : spectrum ℝ X ⊆ Set.Ici (0 : ℝ)) :
    spectrum ℝ (cfcR (fun x : ℝ ↦ x + t) X) ⊆ Set.Ioi (0 : ℝ) := by
  have hs : spectrum ℝ (cfcR (fun x : ℝ ↦ x + t) X) = (fun x : ℝ ↦ x + t) '' spectrum ℝ X := by
    dsimp [cfcR]
    simpa using
      (cfc_map_spectrum (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (a := X)
        (f := fun x : ℝ ↦ x + t) (ha := hX))
  intro x hx
  rw [hs] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using add_pos_of_nonneg_of_pos (Set.mem_Ici.mp (Xs hy)) ht

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
/-- For spectra in `[0, ∞)` and `t > 0`, `cfc (x ↦ (x + t)⁻¹)` is the ring inverse of the shift. -/
private lemma cfcR_one_div_shift_eq_ringInverse {t : ℝ} (ht : 0 < t) {X : 𝓐}
    (hX : IsSelfAdjoint X) (Xs : spectrum ℝ X ⊆ Set.Ici (0 : ℝ)) :
    cfcR (fun x : ℝ ↦ (x + t)⁻¹) X = Ring.inverse (X + algebraMap ℝ 𝓐 t) := by
  have hne : ∀ x ∈ spectrum ℝ X, x + t ≠ 0 := fun x hx ↦
    (add_pos_of_nonneg_of_pos (Set.mem_Ici.mp (Xs hx)) ht).ne'
  have h' : cfc (fun x : ℝ ↦ (x + t)⁻¹) X = Ring.inverse (cfc (fun x : ℝ ↦ x + t) X) := by
    simpa using (cfc_inv (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
      (f := fun x : ℝ ↦ x + t) (a := X) hne (ha := hX))
  simpa [cfcR_shift_eq hX] using h'

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
/-- For spectra in `(0, ∞)`, `cfc (x ↦ x⁻¹)` agrees with `Ring.inverse`. -/
private lemma cfcR_inv_eq_ringInverse {X : 𝓐} (hX : IsSelfAdjoint X)
    (Xs : spectrum ℝ X ⊆ Set.Ioi (0 : ℝ)) :
    cfcR (fun x : ℝ ↦ x⁻¹) X = Ring.inverse X := by
  dsimp [cfcR]
  simpa [cfc_id' (R := ℝ) (a := X) (ha := hX)] using
    (cfc_inv (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (f := fun x : ℝ ↦ x)
      (a := X) (fun x hx ↦ (Set.mem_Ioi.mp (Xs hx)).ne') (ha := hX))

omit [Nontrivial (𝓐)] [NonnegSpectrumClass ℝ 𝓐] in
/-- Shifted reciprocal antitonicity
(Carlen 2010, proof of Theorem 2.6, shifted form of Lemma 2.7; integrand of Lemma 2.8, formula
(2.5))

By Lemma 2.7, the map
$A \mapsto -(t+A)^{-1}$ is operator monotone; this is the shifted reciprocal appearing in
the integrand of (2.5).
\emph{Lean deviation}: this node records the equivalent decreasing form:
for every $t>0$, $x \mapsto 1/(x+t)$ is operator antitone on $[0,\infty)$ in the sense of
`OperatorAntitoneOn`.

Proof: Carlen (2010): the assertion is Lemma 2.7 applied after translating the positive
matrix variable by $tI$; adding $tI$ puts $t+A$ in the strictly positive cone.
\emph{Lean deviation}: the formal proof performs the shift in continuous functional
calculus and then applies \texttt{CStarAlgebra.inv\_le\_inv} through \texttt{cfcUnits},
instead of appealing to a separate translated matrix lemma.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6 / Lemma 2.7. Correspondence restricted to
the exponent range and domain of this declaration. -/
theorem one_div_add_t_operatorAntitoneOn_Ici :
  ∀ t : ℝ, 0 < t →
    OperatorAntitoneOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ 1 / (x + t)) := by
  intro t ht
  dsimp [OperatorAntitoneOn]
  intro A B hA_sa hB_sa BA As Bs
  let f : ℝ → ℝ := fun x => x + t
  have hne {X : 𝓐} (Xs : spectrum ℝ X ⊆ Set.Ici (0 : ℝ)) :
      ∀ x ∈ spectrum ℝ X, f x ≠ 0 := by
    intro x hx
    exact ne_of_gt (add_pos_of_nonneg_of_pos (by simpa [Set.Ici] using Xs hx) ht)
  let uA : (𝓐)ˣ :=
    cfcUnits (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) f A (hne As) (ha := hA_sa)
  let uB : (𝓐)ˣ :=
    cfcUnits (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) f B (hne Bs) (ha := hB_sa)
  have huA_val : (uA : 𝓐) = A + algebraMap ℝ (𝓐) t := by
    simp [uA, cfcUnits, f]
    simpa using cfcR_shift_eq (t := t) hA_sa
  have huB_val : (uB : 𝓐) = B + algebraMap ℝ (𝓐) t := by
    simp [uB, cfcUnits, f]
    simpa using cfcR_shift_eq (t := t) hB_sa
  have huB_nonneg : 0 ≤ (uB : 𝓐) := by
    simp only [uB, cfcUnits, f]
    refine cfc_nonneg (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (a := B) ?_
    intro x hx
    exact le_of_lt (add_pos_of_nonneg_of_pos (by simpa [Set.Ici] using Bs hx) ht)
  have hub_le_hua : (uB : 𝓐) ≤ (uA : 𝓐) := by
    simpa [huA_val, huB_val, add_assoc, add_left_comm, add_comm] using
      add_le_add_right BA (algebraMap ℝ (𝓐) t)
  simpa [uA, uB, cfcUnits, cfcR, f, one_div] using
    (CStarAlgebra.inv_le_inv (A := 𝓐) (a := uB) (b := uA) huB_nonneg hub_le_hua)

omit [Nontrivial 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
/-- The shifted reciprocal functional calculus is antitone on the positive cone. -/
@[gcongr]
theorem cfcR_one_div_add_le_cfcR_one_div_add_of_le {t : ℝ} (ht : 0 < t)
    {A B : 𝓐} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hBA : B ≤ A)
    (hspA : spectrum ℝ A ⊆ Set.Ici (0 : ℝ))
    (hspB : spectrum ℝ B ⊆ Set.Ici (0 : ℝ)) :
    cfcR (fun x : ℝ ↦ 1 / (x + t)) A ≤ cfcR (fun x : ℝ ↦ 1 / (x + t)) B :=
  one_div_add_t_operatorAntitoneOn_Ici t ht hA hB hBA hspA hspB

/-- Shifted reciprocal operator convexity
(Carlen 2010, proof of Theorem 2.6, shifted form of Lemma 2.7; integrand of Lemma 2.8, formula
(2.5))

By Lemma 2.7, the map
$A \mapsto -(t+A)^{-1}$ is operator concave; equivalently,
$A \mapsto (t+A)^{-1}$ is operator convex. This is the shifted reciprocal used in the
integrands (2.5) and (2.6).
\emph{Lean deviation}: this node states the translated form as
$x \mapsto 1/(x+t)$ operator convex on $[0,\infty)$ in the sense of
`OperatorConvexOn`.

This reduces to
`operatorConvexOn_one_div_Ioi` by shifting.

Proof: Carlen (2010): translate Lemma 2.7 by replacing $A$ with $tI+A$, so that the
operator convexity of $u \mapsto u^{-1}$ gives the operator convexity of
$A \mapsto (t+A)^{-1}$.
\emph{Lean deviation}: the formal proof reduces to `operatorConvexOn_one_div_Ioi` after proving
that the spectral shift by $t>0$ moves $[0,\infty)$ into $(0,\infty)$, then rewrites the
shifted functional calculus to the inverse on the shifted element.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6 / Lemma 2.7. Correspondence restricted to
the exponent range and domain of this declaration. -/
theorem operatorConvexOn_one_div_add_t_Ici :
  ∀ t : ℝ, 0 < t →
    OperatorConvexOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ 1 / (x + t)) := by
  intro t ht
  dsimp [OperatorConvexOn]
  intro A B θ hA hB hθ0 hθ1 As Bs
  -- rewrite `1 / (x + t)` as `(x + t)⁻¹` for `simp`/`cfc` lemmas
  simp only [one_div]
  -- Reduce to operator convexity of `x ↦ x⁻¹` on `Ioi 0` by shifting by `t`.
  set C : 𝓐 := (1 - θ) • A + θ • B
  have hC : IsSelfAdjoint C := by simpa [C] using isSelfAdjoint_convexCombo θ hA hB
  set shift : ℝ → ℝ := fun x ↦ x + t
  set T : 𝓐 := algebraMap ℝ (𝓐) t
  have hT : IsSelfAdjoint T := by
    simpa [T] using (IsSelfAdjoint.algebraMap (A := 𝓐) (r := t)
      (hr := IsSelfAdjoint.all (t : ℝ)))
  have A_nonneg : 0 ≤ A := nonneg_of_spectrum_subset_Ici hA As
  have B_nonneg : 0 ≤ B := nonneg_of_spectrum_subset_Ici hB Bs
  have C_nonneg : 0 ≤ C := by
    simpa [C] using
      add_nonneg (smul_nonneg (sub_nonneg.mpr hθ1) A_nonneg) (smul_nonneg hθ0 B_nonneg)
  have hA_shift : cfcR shift A = A + T := by simpa [shift, T] using cfcR_shift_eq (t := t) hA
  have hB_shift : cfcR shift B = B + T := by simpa [shift, T] using cfcR_shift_eq (t := t) hB
  have hC_shift : cfcR shift C = C + T := by simpa [shift, T] using cfcR_shift_eq (t := t) hC
  set A1 : 𝓐 := A + T
  set B1 : 𝓐 := B + T
  set C1 : 𝓐 := (1 - θ) • A1 + θ • B1
  have hA1_sa : IsSelfAdjoint A1 := by
    subst A1
    exact hA.add hT
  have hB1_sa : IsSelfAdjoint B1 := by
    subst B1
    exact hB.add hT
  have specA1 : spectrum ℝ A1 ⊆ Set.Ioi (0 : ℝ) := by
    have hval : cfcR shift A = A1 := by simpa [A1] using hA_shift
    rw [← hval]
    simpa [shift] using spectrum_cfcR_shift_subset_Ioi ht hA As
  have specB1 : spectrum ℝ B1 ⊆ Set.Ioi (0 : ℝ) := by
    have hval : cfcR shift B = B1 := by simpa [B1] using hB_shift
    rw [← hval]
    simpa [shift] using spectrum_cfcR_shift_subset_Ioi ht hB Bs
  have hC1 : C1 = C + T := by
    subst A1 B1 C1
    simp [C, add_assoc, add_left_comm, add_comm, smul_add]
  have hA_inv : cfcR (fun x : ℝ ↦ (x + t)⁻¹) A = Ring.inverse A1 := by
    simpa [A1, T] using cfcR_one_div_shift_eq_ringInverse ht hA As
  have hB_inv : cfcR (fun x : ℝ ↦ (x + t)⁻¹) B = Ring.inverse B1 := by
    simpa [B1, T] using cfcR_one_div_shift_eq_ringInverse ht hB Bs
  have hC_inv : cfcR (fun x : ℝ ↦ (x + t)⁻¹) C = Ring.inverse (C + T) := by
    have hCs : spectrum ℝ C ⊆ Set.Ici (0 : ℝ) := fun x hx ↦
      Set.mem_Ici.mpr (spectrum_nonneg_of_nonneg C_nonneg hx)
    simpa [T] using cfcR_one_div_shift_eq_ringInverse ht hC hCs
  have hA1_inv : cfcR (fun x : ℝ ↦ x⁻¹) A1 = Ring.inverse A1 :=
    cfcR_inv_eq_ringInverse hA1_sa specA1
  have hB1_inv : cfcR (fun x : ℝ ↦ x⁻¹) B1 = Ring.inverse B1 :=
    cfcR_inv_eq_ringInverse hB1_sa specB1
  have hA_eq : cfcR (fun x : ℝ ↦ (x + t)⁻¹) A = cfcR (fun x : ℝ ↦ x⁻¹) A1 := by
    simp [hA_inv, hA1_inv]
  have hB_eq : cfcR (fun x : ℝ ↦ (x + t)⁻¹) B = cfcR (fun x : ℝ ↦ x⁻¹) B1 := by
    simp [hB_inv, hB1_inv]
  have specC1 : spectrum ℝ C1 ⊆ Set.Ioi (0 : ℝ) := by
    have hCs : spectrum ℝ C ⊆ Set.Ici (0 : ℝ) := fun x hx ↦
      Set.mem_Ici.mpr (spectrum_nonneg_of_nonneg C_nonneg hx)
    have hval : cfcR shift C = C1 := by simpa [hC1] using hC_shift
    rw [← hval]
    simpa [shift] using spectrum_cfcR_shift_subset_Ioi ht hC hCs
  have hC1_sa : IsSelfAdjoint C1 := by
    simpa [hC1] using (hC.add hT)
  have hC1_inv : cfcR (fun x : ℝ ↦ x⁻¹) C1 = Ring.inverse C1 :=
    cfcR_inv_eq_ringInverse hC1_sa specC1
  have hC_eq : cfcR (fun x : ℝ ↦ (x + t)⁻¹) C = cfcR (fun x : ℝ ↦ x⁻¹) C1 := by
    calc
      cfcR (fun x : ℝ ↦ (x + t)⁻¹) C
          = Ring.inverse (C + T) := hC_inv
      _ = Ring.inverse C1 := by simp [hC1]
      _ = cfcR (fun x : ℝ ↦ x⁻¹) C1 := by simpa using hC1_inv.symm
  have hconv :
      cfcR (fun x : ℝ ↦ x⁻¹) C1
        ≤ (1 - θ) • cfcR (fun x : ℝ ↦ x⁻¹) A1
          + θ • cfcR (fun x : ℝ ↦ x⁻¹) B1 := by
    simpa [one_div] using
      (operatorConvexOn_one_div_Ioi  (A := A1) (B := B1) (t := θ)
        hA1_sa hB1_sa hθ0 hθ1 specA1 specB1)
  -- conclude by rewriting everything to the shifted `1/x` convexity statement
  simpa [C, hC_eq, hA_eq, hB_eq] using hconv

end Spectrum

end LownerHeinzCore
