/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LownerHeinz.RpowOneTwo

/-!
# Negative powers on the positive spectrum

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

/-! ### Negative powers on the positive spectrum -/

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
/-- The spectrum of `X ^ r` (via `cfc`) stays in `(0, ∞)` when the spectrum of `X` does. -/
private lemma spectrum_cfcR_rpow_subset_Ioi {X : 𝓐} (hX : IsSelfAdjoint X)
    (Xs : spectrum ℝ X ⊆ Set.Ioi (0 : ℝ)) (r : ℝ) :
    spectrum ℝ (cfcR (fun x : ℝ ↦ x ^ r) X) ⊆ Set.Ioi (0 : ℝ) := by
  have hcont : ContinuousOn (fun x : ℝ ↦ x ^ r) (spectrum ℝ X) := fun x hx ↦
    (Real.continuousAt_rpow_const x r (Or.inl (Set.mem_Ioi.mp (Xs hx)).ne')).continuousWithinAt
  have hspec : spectrum ℝ (cfcR (fun x : ℝ ↦ x ^ r) X) = (fun x : ℝ ↦ x ^ r) '' spectrum ℝ X := by
    dsimp [cfcR]
    simpa using
      (cfc_map_spectrum (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (f := fun x : ℝ ↦ x ^ r)
        (a := X) (ha := hX) (hf := hcont))
  intro y hy
  rw [hspec] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  simpa using Real.rpow_pos_of_pos (Set.mem_Ioi.mp (Xs hx)) r

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
/-- Composing the functional calculi: `(X ^ r)⁻¹ = X ^ (-r)` for spectra in `(0, ∞)`. -/
private lemma cfcR_one_div_cfcR_rpow {X : 𝓐} (hX : IsSelfAdjoint X)
    (Xs : spectrum ℝ X ⊆ Set.Ioi (0 : ℝ)) (r : ℝ) :
    cfcR (fun x : ℝ ↦ 1 / x) (cfcR (fun x : ℝ ↦ x ^ r) X) = cfcR (fun x : ℝ ↦ x ^ (-r)) X := by
  have hcont : ContinuousOn (fun x : ℝ ↦ x ^ r) (spectrum ℝ X) := fun x hx ↦
    (Real.continuousAt_rpow_const x r (Or.inl (Set.mem_Ioi.mp (Xs hx)).ne')).continuousWithinAt
  have hs : (fun x : ℝ ↦ x ^ r) '' spectrum ℝ X ⊆ ({0}ᶜ : Set ℝ) := by
    rintro y ⟨x, hx, rfl⟩
    simpa [Set.mem_compl_singleton_iff] using
      (Real.rpow_pos_of_pos (Set.mem_Ioi.mp (Xs hx)) r).ne'
  have hg : ContinuousOn (fun y : ℝ ↦ 1 / y) ((fun x : ℝ ↦ x ^ r) '' spectrum ℝ X) := by
    simpa [one_div] using (continuousOn_inv₀.mono hs)
  have hcomp :
      cfcR (fun y : ℝ ↦ 1 / y) (cfcR (fun x : ℝ ↦ x ^ r) X) =
        cfcR (fun x : ℝ ↦ 1 / (x ^ r)) X := by
    dsimp [cfcR]
    simpa [Function.comp] using
      (cfc_comp' (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (g := fun y : ℝ ↦ 1 / y)
        (f := fun x : ℝ ↦ x ^ r) (a := X) (hg := hg) (hf := hcont) (ha := hX)).symm
  rw [hcomp]
  dsimp [cfcR]
  apply cfc_congr
  intro x hx
  dsimp only
  simpa [one_div] using (Real.rpow_neg (Set.mem_Ioi.mp (Xs hx)).le r).symm

-- Paper statement (Löwner–Heinz): for `p ∈ [-1,0]`, `f(t) = -t^p` is operator monotone and concave
-- on `(0,∞)`.
omit [Nontrivial 𝓐] in
/-- Monotonicity of sign-reversed negative powers
(Carlen 2010, Theorem 2.6, first clause; proof using Lemma 2.8, formula (2.5))

For $-1 \leq p \leq 0$, the
function $f(t)=-t^p$ is operator monotone.
\emph{Lean deviation}: stated as $x \mapsto -x^p$ operator monotone on $(0,\infty)$ in the
sense of `OperatorMonotoneOn`, over a unital $C^*$-algebra rather than matrices.

Proof: Carlen (2010), proof of Theorem 2.6: for $-1<p<0$, Lemma 2.8 gives
\[
  A^p = \frac{\sin(\pi(p+1))}{\pi}
    \int_0^\infty t^p\frac1{t+A}\,\mathrm{d}t .
\]
Since Lemma 2.7 makes $A \mapsto -(t+A)^{-1}$ operator monotone and the weights are
positive, $A \mapsto -A^p$ is operator monotone; the endpoint cases $p=-1,0$ are covered
by Lemma 2.7 and triviality.
\emph{Lean deviation}: the formal proof derives the result from the already-formalized
$0 \leq q \leq 1$ monotonicity for $x^q$ with $q=-p$ from
`power_Icc_zero_one_operatorMonotoneOn_Ici`, then composes with the reciprocal and uses
`one_div_operatorAntitoneOn_Ioi`, rather than using the integral representation (2.5) directly.

Source: this paper, arXiv:2607.05492v1, formalization of the main results in §3 (no individual paper
theorem number is assigned).
Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6. Correspondence restricted to the exponent
range and domain of this declaration. -/
theorem power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi : ∀ p ∈ Set.Icc (-1 : ℝ) 0,
    OperatorMonotoneOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x ↦ -(x ^ p)) := by
  intro p hp
  dsimp [OperatorMonotoneOn]
  intro A B hA_sa hB_sa hBA hspA hspB
  let q : ℝ := -p
  have hq : q ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨neg_nonneg.mpr hp.2, by simpa [q] using neg_le_neg hp.1⟩
  have hBAq : cfcR (fun x : ℝ ↦ x ^ q) B ≤ cfcR (fun x : ℝ ↦ x ^ q) A :=
    power_Icc_zero_one_operatorMonotoneOn_Ici q hq (A := A) (B := B) hA_sa hB_sa hBA
      (hspA.trans Set.Ioi_subset_Ici_self) (hspB.trans Set.Ioi_subset_Ici_self)
  let Aq : 𝓐 := cfcR (fun x : ℝ ↦ x ^ q) A
  let Bq : 𝓐 := cfcR (fun x : ℝ ↦ x ^ q) B
  have hAq_sa : IsSelfAdjoint Aq := by
    dsimp [Aq, cfcR]
    exact cfc_predicate _ _
  have hBq_sa : IsSelfAdjoint Bq := by
    dsimp [Bq, cfcR]
    exact cfc_predicate _ _
  have h_inv : cfcR (fun x : ℝ ↦ 1 / x) Aq ≤ cfcR (fun x : ℝ ↦ 1 / x) Bq :=
    one_div_operatorAntitoneOn_Ioi hAq_sa hBq_sa hBAq
      (spectrum_cfcR_rpow_subset_Ioi hA_sa hspA q) (spectrum_cfcR_rpow_subset_Ioi hB_sa hspB q)
  rw [show cfcR (fun x : ℝ ↦ 1 / x) Aq = cfcR (fun x : ℝ ↦ x ^ p) A by
        simpa [Aq, q, neg_neg] using cfcR_one_div_cfcR_rpow hA_sa hspA q,
      show cfcR (fun x : ℝ ↦ 1 / x) Bq = cfcR (fun x : ℝ ↦ x ^ p) B by
        simpa [Bq, q, neg_neg] using cfcR_one_div_cfcR_rpow hB_sa hspB q] at h_inv
  simpa [cfcR, cfc_neg] using neg_le_neg h_inv

omit [Nontrivial 𝓐] in
/-- The negative real-power functional calculus is monotone after negation. -/
@[gcongr]
theorem cfcR_neg_rpow_le_cfcR_neg_rpow_of_le {p : ℝ}
    (hp : p ∈ Set.Icc (-1 : ℝ) 0) {A B : 𝓐}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hBA : B ≤ A)
    (hspA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hspB : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    cfcR (fun x : ℝ ↦ -(x ^ p)) B ≤ cfcR (fun x : ℝ ↦ -(x ^ p)) A :=
  power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi p hp hA hB hBA hspA hspB

omit [Nontrivial 𝓐] in
/-- Antitonicity of negative powers
(Carlen 2010, equivalent antitone form of Theorem 2.6, first clause; proof using Lemma 2.8, formula
(2.5))

For
$-1 \leq p \leq 0$, the function $x \mapsto x^p$ is operator monotone decreasing on
$(0,\infty)$.
\emph{Lean deviation}: stated as operator antitonicity on $(0,\infty)$ in the sense of
`OperatorAntitoneOn`, over a unital $C^*$-algebra rather than matrices.

This is the antitone
restatement of `power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi`.

Proof: Carlen (2010): this is just the decreasing-language reformulation of the first
clause of Theorem 2.6, whose proof uses (2.5) and Lemma 2.7 to show that $-A^p$ is a
positive weighted sum of shifted monotone reciprocals.
\emph{Lean deviation}: the formal proof is the wrapper
\texttt{operatorAntitoneOn\_iff\_operatorMonotoneOn\_neg} applied to
`power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi`; it introduces no new analytic argument.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6. Correspondence restricted to the exponent
range and domain of this declaration. -/
theorem power_Icc_neg_one_zero_operatorAntitoneOn_Ioi (p : ℝ)
    (hp : p ∈ Set.Icc (-1 : ℝ) 0) :
    OperatorAntitoneOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x ↦ x ^ p) :=
  (operatorAntitoneOn_iff_operatorMonotoneOn_neg _ _).mpr
    (power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi p hp)

/-- Concavity of sign-reversed negative powers
(Carlen 2010, Theorem 2.6, first clause; proof using Lemma 2.8, formula (2.5))

For $-1 \leq p \leq 0$, the
function $f(t)=-t^p$ is operator concave.
\emph{Lean deviation}: stated as $x \mapsto -x^p$ operator concave on $(0,\infty)$ in the
sense of `OperatorConcaveOn`, over a unital $C^*$-algebra rather than matrices.

Proof: Carlen (2010), proof of Theorem 2.6: for $-1<p<0$, formula (2.5) writes $A^p$ as
a positive weighted integral of $(t+A)^{-1}$. Since Lemma 2.7 gives
$A \mapsto -(t+A)^{-1}$ operator concave, positive weighted sums show that
$A \mapsto -A^p$ is operator concave; the endpoint cases are supplied by Lemma 2.7 and
triviality.
\emph{Lean deviation}: the formal proof shows the equivalent convexity of $x^p$ for
negative $p$ by setting $r=-p$, using the $0 \leq r \leq 1$ concavity theorem
`operatorConcaveOn_rpow_Ici` for $x^r$, then applying reciprocal antitonicity and convexity
from `one_div_operatorAntitoneOn_Ioi` and `operatorConvexOn_one_div_Ioi`.

Source: this paper, arXiv:2607.05492v1, formalization of the main results in §3 (no individual paper
theorem number is assigned).
Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6. Correspondence restricted to the exponent
range and domain of this declaration. -/
theorem operatorConcaveOn_neg_rpow_Ioi : ∀ p ∈ Set.Icc (-1 : ℝ) 0,
    OperatorConcaveOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x ↦ -(x ^ p)) := by
  intro p hp
  dsimp [OperatorConcaveOn, OperatorConvexOn]
  intro A B t hA hB ht0 ht1 As Bs
  let r : ℝ := -p
  have hr : r ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨neg_nonneg.mpr hp.2, by simpa [r] using neg_le_neg hp.1⟩
  set C : 𝓐 := (1 - t) • A + t • B
  have hC : IsSelfAdjoint C := by simpa [C] using isSelfAdjoint_convexCombo t hA hB
  have Cs : spectrum ℝ C ⊆ Set.Ioi (0 : ℝ) := by
    simpa [C] using
      spectrum_convexCombo_Ioi  (A := A) (B := B) (t := t) hA hB ht0 ht1 As Bs
  let Ar : 𝓐 := cfcR  (fun x : ℝ ↦ x ^ r) A
  let Br : 𝓐 := cfcR  (fun x : ℝ ↦ x ^ r) B
  let Cr : 𝓐 := cfcR  (fun x : ℝ ↦ x ^ r) C
  let Dr : 𝓐 := (1 - t) • Ar + t • Br
  have h_conc : Dr ≤ Cr := neg_le_neg_iff.mp (by
    simpa [C, Ar, Br, Cr, Dr, cfcR, cfc_neg, smul_neg, add_comm] using
      (operatorConcaveOn_rpow_Ici (𝓐 := 𝓐) r hr)
        hA hB ht0 ht1 (As.trans Set.Ioi_subset_Ici_self)
          (Bs.trans Set.Ioi_subset_Ici_self))
  have hAr_sa : IsSelfAdjoint Ar := by dsimp [Ar, cfcR]; exact cfc_predicate _ _
  have hBr_sa : IsSelfAdjoint Br := by dsimp [Br, cfcR]; exact cfc_predicate _ _
  have hCr_sa : IsSelfAdjoint Cr := by dsimp [Cr, cfcR]; exact cfc_predicate _ _
  have hDr_sa : IsSelfAdjoint Dr := by
    exact isSelfAdjoint_convexCombo t hAr_sa hBr_sa
  have hspAr : spectrum ℝ Ar ⊆ Set.Ioi (0 : ℝ) := spectrum_cfcR_rpow_subset_Ioi hA As r
  have hspBr : spectrum ℝ Br ⊆ Set.Ioi (0 : ℝ) := spectrum_cfcR_rpow_subset_Ioi hB Bs r
  have hspCr : spectrum ℝ Cr ⊆ Set.Ioi (0 : ℝ) := spectrum_cfcR_rpow_subset_Ioi hC Cs r
  have hspDr : spectrum ℝ Dr ⊆ Set.Ioi (0 : ℝ) := by
    simpa [Dr] using
      spectrum_convexCombo_Ioi (A := Ar) (B := Br) (t := t) hAr_sa hBr_sa ht0 ht1 hspAr hspBr
  have h_inv1 : cfcR (fun x : ℝ ↦ 1 / x) Cr ≤ cfcR (fun x : ℝ ↦ 1 / x) Dr :=
    one_div_operatorAntitoneOn_Ioi hCr_sa hDr_sa h_conc hspCr hspDr
  have h_inv2 :
      cfcR (fun x : ℝ ↦ 1 / x) Dr
        ≤ (1 - t) • cfcR (fun x : ℝ ↦ 1 / x) Ar
          + t • cfcR (fun x : ℝ ↦ 1 / x) Br := by
    simpa [Dr] using
      (operatorConvexOn_one_div_Ioi (𝓐 := 𝓐))
        (A := Ar) (B := Br) (t := t) hAr_sa hBr_sa ht0 ht1 hspAr hspBr
  have hcompA : cfcR (fun x : ℝ ↦ 1 / x) Ar = cfcR (fun x : ℝ ↦ x ^ p) A := by
    simpa [Ar, r, neg_neg] using cfcR_one_div_cfcR_rpow hA As r
  have hcompB : cfcR (fun x : ℝ ↦ 1 / x) Br = cfcR (fun x : ℝ ↦ x ^ p) B := by
    simpa [Br, r, neg_neg] using cfcR_one_div_cfcR_rpow hB Bs r
  have hcompC : cfcR (fun x : ℝ ↦ 1 / x) Cr = cfcR (fun x : ℝ ↦ x ^ p) C := by
    simpa [Cr, r, neg_neg] using cfcR_one_div_cfcR_rpow hC Cs r
  have hmain :
      cfcR  (fun x : ℝ ↦ x ^ p) C
        ≤ (1 - t) • cfcR  (fun x : ℝ ↦ x ^ p) A
          + t • cfcR  (fun x : ℝ ↦ x ^ p) B := by
    calc
      cfcR (fun x : ℝ ↦ x ^ p) C = cfcR (fun x : ℝ ↦ 1 / x) Cr := hcompC.symm
      _ ≤ cfcR (fun x : ℝ ↦ 1 / x) Dr := h_inv1
      _ ≤ (1 - t) • cfcR (fun x : ℝ ↦ 1 / x) Ar
          + t • cfcR (fun x : ℝ ↦ 1 / x) Br := h_inv2
      _ = (1 - t) • cfcR (fun x : ℝ ↦ x ^ p) A
          + t • cfcR (fun x : ℝ ↦ x ^ p) B := by rw [hcompA, hcompB]
  simpa [C] using hmain

end Spectrum

end LownerHeinzCore
