/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LownerHeinz.Reciprocal
import Quantum.TraceInequality.TraceFunctionMonotonicity.LownerHeinz.Defs

/-!
# Ratio functions and powers between zero and one


-/

namespace LownerHeinzCore

universe u

open CFC

section Spectrum

variable {𝓐 : Type u}
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
variable [Nontrivial 𝓐]
variable [NonnegSpectrumClass ℝ 𝓐]

/-! ### Powers between zero and one -/

omit [Nontrivial (𝓐)] in
/-- **Löwner–Heinz**: `x ↦ x ^ p` is operator monotone on `[0, ∞)` for `p ∈ [0, 1]`.

Source: arXiv:2607.05492v1, §3.
Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6 / Lemma 2.8. Correspondence restricted to
the exponent range and domain of this declaration. -/
/- Löwner–Heinz power monotonicity
    (Carlen 2009, Theorem 2.6, second clause; proof using Lemma 2.8, formula (2.6)) -/
/- (Carlen 2009, Theorem 2.6, second clause; proof using Lemma 2.8, formula (2.6)) For
    $0 \leq p \leq 1$, the function $f(t) = t^p$ is operator monotone.
    *Lean deviation*: stated as — $x \mapsto x^p$ is operator monotone on $[0, \infty)$
    in the sense of the definition of `OperatorMonotoneOn`, over a unital $C^*$-algebra rather than
    matrices. -/
/- Carlen09 (proof of Theorem 2.6): by the integral formula (2.6) of Lemma 2.8,
    $A^p = \frac{\sin(\pi p)}{\pi} \int_0^\infty t^p \bigl(\tfrac{1}{t} -
    \tfrac{1}{t+A}\bigr)\,\mathrm{d}t$ for $0 < p < 1$; each integrand
    $A \mapsto \tfrac{1}{t} - \tfrac{1}{t+A}$ is operator monotone by (the shifted form of)
    Lemma 2.7, and weighted sums with positive weights preserve operator monotonicity.
    *Lean deviation*: the formal proof obtains this clause directly from Mathlib's
    `CFC.rpow_le_rpow`; Carlen09's integral route is instead followed for the
    companion concavity clause. -/
theorem power_Icc_zero_one_operatorMonotoneOn_Ici (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    OperatorMonotoneOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  dsimp [OperatorMonotoneOn]
  intro A B hA_sa hB_sa hBA hspA hspB
  have hA0 : 0 ≤ A := nonneg_of_spectrum_subset_Ici hA_sa hspA
  have hB0 : 0 ≤ B := nonneg_of_spectrum_subset_Ici hB_sa hspB
  have hA : cfcR (fun x : ℝ ↦ x ^ p) A = A ^ p := by
    simpa [cfcR] using
      (CFC.rpow_eq_cfc_real (A := 𝓐) (a := A) (y := p) (ha := hA0)).symm
  have hB : cfcR (fun x : ℝ ↦ x ^ p) B = B ^ p := by
    simpa [cfcR] using
      (CFC.rpow_eq_cfc_real (A := 𝓐) (a := B) (y := p) (ha := hB0)).symm
  simpa [hA, hB] using (CFC.rpow_le_rpow (A := 𝓐) hp hBA)

omit [Nontrivial 𝓐] in
/-- The real-power functional calculus is monotone for exponents in `[0, 1]`. -/
@[gcongr]
theorem cfcR_rpow_le_cfcR_rpow_of_le {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    {A B : 𝓐} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hBA : B ≤ A)
    (hspA : spectrum ℝ A ⊆ Set.Ici (0 : ℝ))
    (hspB : spectrum ℝ B ⊆ Set.Ici (0 : ℝ)) :
    cfcR (fun x : ℝ ↦ x ^ p) B ≤ cfcR (fun x : ℝ ↦ x ^ p) A :=
  power_Icc_zero_one_operatorMonotoneOn_Ici p hp hA hB hBA hspA hspB

end Spectrum

end LownerHeinzCore
