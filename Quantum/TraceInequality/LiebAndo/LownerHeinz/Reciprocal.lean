/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LiebAndo.LownerHeinz.Defs
import Quantum.TraceInequality.LownerHeinz.Defs
import Quantum.TraceInequality.LownerHeinz.Reciprocal

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

omit [Nontrivial 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
/-- `x ↦ 1 / x` is operator antitone on `(0, ∞)`.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Lemma 2.7. Correspondence restricted to the exponent
range and domain of this declaration. -/
/- Reciprocal antitonicity
    (Carlen 2009, Lemma 2.7, equivalent antitone form of its monotonicity part) -/
/- (Carlen 2009, Lemma 2.7, equivalent antitone form of its monotonicity part) The function
    $f(t)=t^{-1}$ is operator convex, and the function $f(t)=-t^{-1}$ is operator monotone.
    *Lean deviation*: this node records the equivalent decreasing form: $x \mapsto 1/x$
    is operator antitone on $(0,\infty)$ in the sense of the definition of `OperatorAntitoneOn`,
    over a unital $C^*$-algebra rather than matrices. -/
/- Carlen09 (proof of Lemma 2.7): for monotonicity, take
    $A,B \in \mathbf{H}_n^+$ and set $C=A^{-1/2}BA^{-1/2}$. Then
    \[
      A^{-1}-(A+B)^{-1}
        = A^{-1/2}\bigl[I-(I+C)^{-1}\bigr]A^{-1/2}.
    \]
    Since $C \in \mathbf{H}_n^+$, also $I-(I+C)^{-1} \in \mathbf{H}_n^+$, so the displayed
    difference is positive; this proves that $-t^{-1}$ is operator monotone, equivalently that
    $t^{-1}$ is decreasing.
    *Lean deviation*: the formal proof works directly in the fixed $C^*$-algebra using
    `cfcUnits` to identify the functional calculus inverse and
    `CStarAlgebra.inv_le_inv` to obtain the inverse-order inequality. -/
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
/-- `x ↦ 1 / (x + t)` is operator antitone on `[0, ∞)` for `t > 0`.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6 / Lemma 2.7. Correspondence restricted to
the exponent range and domain of this declaration. -/
/- Shifted reciprocal antitonicity
    (Carlen 2009, proof of Theorem 2.6, shifted form of Lemma 2.7; integrand of Lemma 2.8,
    formula (2.5)) -/
/- (Carlen 2009, proof of Theorem 2.6, shifted form of Lemma 2.7; integrand of Lemma 2.8,
    formula (2.5)) By Lemma 2.7, the map $A \mapsto -(t+A)^{-1}$ is operator monotone; this is the
    shifted reciprocal appearing in the integrand of (2.5).
    *Lean deviation*: this node records the equivalent decreasing form:
    for every $t>0$, $x \mapsto 1/(x+t)$ is operator antitone on $[0,\infty)$ in the sense of
    the definition of `OperatorAntitoneOn`. -/
/- Carlen09: the assertion is Lemma 2.7 applied after translating the positive
    matrix variable by $tI$; adding $tI$ puts $t+A$ in the strictly positive cone.
    *Lean deviation*: the formal proof performs the shift in continuous functional
    calculus and then applies `CStarAlgebra.inv_le_inv` through `cfcUnits`,
    instead of appealing to a separate translated matrix lemma. -/
theorem one_div_add_t_operatorAntitoneOn_Ici (t : ℝ) (ht : 0 < t) :
    OperatorAntitoneOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ 1 / (x + t)) := by
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

/-- `x ↦ 1 / (x + t)` is operator convex on `[0, ∞)` for `t > 0`; this reduces to
`one_div_operatorConvexOn_Ioi` by shifting.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6 / Lemma 2.7. Correspondence restricted to
the exponent range and domain of this declaration. -/
/- Shifted reciprocal operator convexity
    (Carlen 2009, proof of Theorem 2.6, shifted form of Lemma 2.7; integrand of Lemma 2.8,
    formula (2.5)) -/
/- (Carlen 2009, proof of Theorem 2.6, shifted form of Lemma 2.7; integrand of Lemma 2.8,
    formula (2.5)) By Lemma 2.7, the map $A \mapsto -(t+A)^{-1}$ is operator concave; equivalently,
    $A \mapsto (t+A)^{-1}$ is operator convex. This is the shifted reciprocal used in the
    integrands (2.5) and (2.6).
    *Lean deviation*: this node states the translated form as
    $x \mapsto 1/(x+t)$ operator convex on $[0,\infty)$ in the sense of
    the definition of `OperatorConvexOn`. -/
/- Carlen09: translate Lemma 2.7 by replacing $A$ with $tI+A$, so that the
    operator convexity of $u \mapsto u^{-1}$ gives the operator convexity of
    $A \mapsto (t+A)^{-1}$.
    *Lean deviation*: the formal proof reduces to reciprocal convexity
    (`one_div_operatorConvexOn_Ioi`) after proving that the spectral shift by $t>0$ moves
    $[0,\infty)$ into $(0,\infty)$, then rewrites the shifted functional calculus to the inverse on
    the shifted element. -/
theorem one_div_add_t_operatorConvexOn_Ici (t : ℝ) (ht : 0 < t) :
    OperatorConvexOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ 1 / (x + t)) := by
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
      (one_div_operatorConvexOn_Ioi  (A := A1) (B := B1) (t := θ)
        hA1_sa hB1_sa hθ0 hθ1 specA1 specB1)
  -- conclude by rewriting everything to the shifted `1/x` convexity statement
  simpa [C, hC_eq, hA_eq, hB_eq] using hconv

end Spectrum

end LownerHeinzCore
