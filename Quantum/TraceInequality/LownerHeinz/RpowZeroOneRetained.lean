/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LiebAndo.LownerHeinz.Reciprocal
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

/-! ### Ratio functions from shifted reciprocals -/

omit [Nontrivial (𝓐)] [NonnegSpectrumClass ℝ 𝓐] in
/-- `x ↦ x / (x + t)` is operator monotone on `[0, ∞)` for `t > 0`.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6 / Lemma 2.7. Correspondence restricted to
the exponent range and domain of this declaration. -/
/- Monotonicity of the shifted ratio
    (Carlen 2009, proof of Theorem 2.6, Lemma 2.7 and the integrand of Lemma 2.8, formula (2.6)) -/
/- (Carlen 2009, proof of Theorem 2.6, Lemma 2.7 and the integrand of Lemma 2.8, formula (2.6)) The
    integrand $A \mapsto \frac{1}{t}-\frac{1}{t+A}$ is operator monotone, by Lemma 2.7 applied to
    the shifted reciprocal. Equivalently, up to the positive scalar factor $1/t$, this is the map
    $A \mapsto A/(t+A)=I-t(t+A)^{-1}$.
    The ratio function itself is not stated as an independent proposition in the source.
    *Lean deviation*: this node states the equivalent ratio form:
    for every $t>0$, $x \mapsto x/(x+t)$ is operator monotone on $[0,\infty)$ in the sense of
    the definition of `OperatorMonotoneOn`. -/
/- Carlen09: since $A \mapsto -(t+A)^{-1}$ is operator monotone by Lemma 2.7
    after shifting, adding the constant $1/t$ and multiplying by the positive scalar $t$ gives
    the monotonicity of $A \mapsto A/(t+A)$.
    *Lean deviation*: the formal proof rewrites the functional calculus identity
    $x/(x+t)=1-t/(x+t)$ and combines scalar order with
    shifted reciprocal antitonicity (`one_div_add_t_operatorAntitoneOn_Ici`); it does not use the
    integral formula itself. -/
theorem ratio_add_t_operatorMonotoneOn_Ici (t : ℝ) (ht : 0 < t) :
    OperatorMonotoneOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x / (x + t)) := by
  dsimp [OperatorMonotoneOn]
  intro A B hA_sa hB_sa hBA hspA hspB
  let g : ℝ → ℝ := fun x ↦ 1 / (x + t)
  have hrepr (T : 𝓐) (hT_sa : IsSelfAdjoint T)
      (hspT : spectrum ℝ T ⊆ Set.Ici (0 : ℝ)) :
      cfcR (fun x : ℝ ↦ x / (x + t)) T = (1 : 𝓐) - t • cfcR g T := by
    have hne : ∀ x ∈ spectrum ℝ T, x + t ≠ 0 := fun x hx ↦
      ne_of_gt (add_pos_of_nonneg_of_pos (hspT hx) ht)
    have hg : ContinuousOn g (spectrum ℝ T) := by
      simpa [g, one_div] using (continuousOn_id.add continuousOn_const).inv₀ hne
    calc
      cfcR (fun x : ℝ ↦ x / (x + t)) T =
          cfcR (fun x : ℝ ↦ 1 - t * g x) T := by
        apply cfc_congr
        intro x hx
        simp only [g]
        field_simp [hne x hx]
        ring
      _ = (1 : 𝓐) - t • cfcR g T := by
        dsimp [cfcR]
        rw [cfc_sub (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
            (f := fun _ : ℝ ↦ (1 : ℝ)) (g := fun x : ℝ ↦ t * g x) (a := T)
            (hf := continuousOn_const) (hg := continuousOn_const.mul hg),
          cfc_const_one (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
            (a := T) (ha := hT_sa),
          cfc_const_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
            (r := t) (f := g) (a := T) (hf := hg)]
  rw [hrepr B hB_sa hspB, hrepr A hA_sa hspA]
  exact sub_le_sub_left (smul_le_smul_of_nonneg_left (by
    simpa [g] using
      (one_div_add_t_operatorAntitoneOn_Ici (𝓐 := 𝓐) t ht)
        hA_sa hB_sa hBA hspA hspB) ht.le) 1

omit [Nontrivial 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
/-- The ratio functional calculus `x / (x + t)` is monotone on the positive cone. -/
@[gcongr]
theorem cfcR_ratio_add_le_cfcR_ratio_add_of_le {t : ℝ} (ht : 0 < t)
    {A B : 𝓐} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hBA : B ≤ A)
    (hspA : spectrum ℝ A ⊆ Set.Ici (0 : ℝ))
    (hspB : spectrum ℝ B ⊆ Set.Ici (0 : ℝ)) :
    cfcR (fun x : ℝ ↦ x / (x + t)) B ≤ cfcR (fun x : ℝ ↦ x / (x + t)) A :=
  ratio_add_t_operatorMonotoneOn_Ici t ht hA hB hBA hspA hspB

end Spectrum

end LownerHeinzCore
