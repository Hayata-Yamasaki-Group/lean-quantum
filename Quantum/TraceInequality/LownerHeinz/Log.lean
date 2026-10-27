/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LownerHeinz.NegPow

/-!
# Logarithm limits and convexity

This file is part of the split `LownerHeinzCore` development.
-/

namespace LownerHeinzCore

universe u

open CFC

section LogLimit

variable {𝓐 : Type u}
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
variable [Nontrivial 𝓐]
variable [NonnegSpectrumClass ℝ 𝓐]

/-! ### Logarithm as a limit of normalized powers -/

open scoped Topology in
open Real Filter in
open Set in
/-- Locally uniform normalized-power approximation of the logarithm
(Carlen 2010, proof of Theorem 2.6, first limit in formula (2.8))

On the positive half-line, the scalar functions
$(p,x)\mapsto p^{-1}(x^p-1)$ converge locally uniformly to $\log x$ as $p\downarrow 0$.
The locally uniform strengthening is on the Lean side; the source gives only the matrix limit.

Proof: For a compact set $K\subset(0,\infty)$, the quantities
$\lVert\log x\rVert$ and $\lVert\log x\rVert^2$ are bounded on $K$.  Choose $p>0$ small
enough that $p$ is below both the reciprocal logarithmic bound and the $\varepsilon$-scaled
quadratic bound.  The scalar estimate
\[
  \left|p^{-1}(x^p-1)-\log x\right|\le p\,|\log x|^2
\]
follows from $x^p=\exp(p\log x)$ and the second-order bound for $\exp(y)-1-y$ when
$|y|\le 1$.  The chosen bounds make the right-hand side uniformly at most
$\varepsilon$ on $K$, proving locally uniform convergence.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6. Correspondence as an auxiliary lemma used
in the proof of this result. -/
private lemma real_tendstoLocallyUniformlyOn_rpow_sub_one_log :
    TendstoLocallyUniformlyOn (fun (p : ℝ) (x : ℝ) => p⁻¹ * (x ^ p - 1)) log
      (𝓝[>] 0) (Ioi 0) := by
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioi).mpr ?_
  intro s hs hs'
  rw [Metric.uniformity_basis_dist_le.tendstoUniformlyOn_iff_of_uniformity]
  intro ε hε
  let pbound : ℝ := ε / (sSup ((fun x => ‖log x‖ ^ 2) '' s) + 1)
  have hxs : ∀ x ∈ s, x ≠ 0 := by grind
  have sSup_nonneg : 0 ≤ sSup ((fun x => ‖log x‖ ^ 2) '' s) := by
    refine Real.sSup_nonneg ?_
    grind [← sq_nonneg]
  have sSup_nonneg' : 0 ≤ sSup ((fun x => ‖log x‖) '' s) := by
    refine Real.sSup_nonneg ?_
    grind [← sq_nonneg]
  have pbound_pos : 0 < pbound := by positivity
  have h₁ : ∀ᶠ p : ℝ in 𝓝[>] 0, 0 < p ∧ p < pbound :=
    nhdsGT_basis 0 |>.mem_of_mem pbound_pos
  have h₂ : ∀ᶠ p : ℝ in 𝓝[>] 0, p ≤ 1 / (sSup ((fun x => ‖log x‖) '' s) + 1) :=
    Eventually.filter_mono nhdsWithin_le_nhds <| eventually_le_nhds (by positivity)
  have hcont : ContinuousOn (fun x => ‖log x‖ ^ 2) s := by
    fun_prop (disch := assumption)
  have hcont' : ContinuousOn (fun x => ‖log x‖) s := by
    fun_prop (disch := assumption)
  filter_upwards [h₁, h₂] with p ⟨hp₁, hp₂⟩ hp₃
  intro x hx
  have hx' : ‖p * log x‖ ≤ 1 := calc
    _ = p * ‖log x‖ := by grind [norm_mul, Real.norm_of_nonneg]
    _ ≤ 1 / (sSup ((fun y => ‖log y‖) '' s) + 1) * ‖log x‖ := by gcongr
    _ ≤ 1 / (‖log x‖ + 1) * ‖log x‖ := by
      gcongr
      refine le_csSup ?_ (by grind)
      grind [IsCompact.bddAbove, ← IsCompact.image_of_continuousOn]
    _ = ‖log x‖ / (‖log x‖ + 1) := by grind
    _ ≤ 1 := by rw [div_le_one₀] <;> grind [norm_nonneg]
  have hest : ‖p⁻¹ * (x ^ p - 1) - log x‖ ≤ p * ‖log x‖ ^ 2 := by
    have pinv_nonneg : 0 ≤ p⁻¹ := by grind [_root_.inv_nonneg]
    calc
      _ = ‖p⁻¹ * ((x ^ p - 1) - p * log x)‖ := by grind
      _ = p⁻¹ * ‖(rexp (p * log x) - 1) - p * log x‖ := by
        simp only [norm_mul, Real.norm_of_nonneg (r := p⁻¹) pinv_nonneg]
        congr
        rw [mul_comm, Real.exp_mul, Real.exp_log (by grind)]
      _ ≤ p⁻¹ * ‖p * log x‖ ^ 2 := by
        gcongr
        refine Real.norm_exp_sub_one_sub_id_le ?_
        simp only [hx']
      _ = p * ‖log x‖ ^ 2 := by
        simp only [norm_mul]
        grind [Real.norm_of_nonneg]
  rw [dist_eq_norm']
  calc
    _ ≤ p * ‖log x‖ ^ 2 := hest
    _ ≤ p * sSup ((fun x => ‖log x‖ ^ 2) '' s) := by
      gcongr
      refine le_csSup ?_ (by grind)
      grind [IsCompact.bddAbove, ← IsCompact.image_of_continuousOn]
    _ ≤ pbound * (sSup ((fun x => ‖log x‖ ^ 2) '' s) + 1) := by gcongr; grind
    _ = ε := by grind

omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
open scoped Topology in
open Filter in
open Set in
/-- Continuous-functional-calculus convergence of normalized powers to the logarithm
(Carlen 2010, proof of Theorem 2.6, first limit in formula (2.8))

If the real spectrum of $X$ is contained in $(0,\infty)$, then
$p^{-1}(X^p-I)$, interpreted by continuous functional calculus, converges to $\log X$ as
$p\downarrow 0$.

Proof: Apply the scalar locally uniform convergence of
`real_tendstoLocallyUniformlyOn_rpow_sub_one_log` to the compact spectrum of $X$, using the
assumed inclusion in $(0,\infty)$.  The continuous functional calculus is continuous under
uniform convergence on the spectrum, and for all sufficiently small positive $p$ the scalar
approximants are continuous there.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6. Correspondence as an auxiliary lemma used
in the proof of this result. -/
private lemma tendsto_cfcR_rpow_sub_one_log {X : 𝓐}
    (Xs : spectrum ℝ X ⊆ Set.Ioi (0 : ℝ)) :
    Tendsto (fun p : ℝ => cfcR (fun x : ℝ => p⁻¹ * (x ^ p - 1)) X) (𝓝[>] 0)
      (𝓝 (cfcR (fun x : ℝ => Real.log x) X)) := by
  dsimp [cfcR]
  refine tendsto_cfc_fun ?tendsto ?cont
  · have hmain := real_tendstoLocallyUniformlyOn_rpow_sub_one_log
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioi] at hmain
    exact hmain (spectrum ℝ X) Xs (isCompact_iff_compactSpace.mpr inferInstance)
  · have hsmall : ∀ᶠ p : ℝ in 𝓝[>] 0, 0 < p ∧ p < 1 :=
      nhdsGT_basis 0 |>.mem_of_mem zero_lt_one
    filter_upwards [hsmall] with p hp
    fun_prop (disch := grind)

/-- Logarithm operator monotonicity
(Carlen 2010, Theorem 2.6, final clause; proof using the first limit in formula (2.8))

The function
$f(t)=\log(t)$ is operator monotone on $(0,\infty)$.
\emph{Lean deviation}: stated as $x \mapsto \log x$ operator monotone on
$(0,\infty)$ in the sense of `OperatorMonotoneOn`, over a fixed unital
$C^*$-algebra rather than matrices.

Proof: Let $B\le A$ be self-adjoint elements whose spectra are contained in
$(0,\infty)$.  For every $0<p<1$, `power_Icc_zero_one_operatorMonotoneOn_Ici` applies on
$[0,\infty)$ after restricting the two spectra from $(0,\infty)$ to $[0,\infty)$, giving
$B^p\le A^p$ by continuous functional calculus.  Subtracting $I$ and multiplying by the
positive scalar $p^{-1}$ preserves the order, so
\[
  p^{-1}(B^p-I)\le p^{-1}(A^p-I).
\]
The algebraic form of these two sides is exactly the continuous functional calculus of
$x\mapsto p^{-1}(x^p-1)$.  By `tendsto_cfcR_rpow_sub_one_log`, these two approximants converge
respectively to $\log(B)$ and $\log(A)$ as $p\downarrow0$.  Since the order relation in a
$C^*$-algebra is closed, passing to the limit gives $\log(B)\le\log(A)$, which is precisely
operator monotonicity on $(0,\infty)$.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6. Correspondence to the logarithm result
using the normalized limit of powers. -/
theorem log_operatorMonotoneOn_Ioi :
    OperatorMonotoneOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ Real.log x) := by
  dsimp [OperatorMonotoneOn]
  intro A B hA_sa hB_sa hBA hspA hspB
  have _ : (spectrum ℝ A).Nonempty := ContinuousFunctionalCalculus.spectrum_nonempty A hA_sa
  have hlimA := tendsto_cfcR_rpow_sub_one_log (𝓐 := 𝓐) (X := A) hspA
  have hlimB := tendsto_cfcR_rpow_sub_one_log (𝓐 := 𝓐) (X := B) hspB
  refine le_of_tendsto_of_tendsto hlimB hlimA ?_
  have hsmall : ∀ᶠ p : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < p ∧ p < 1 :=
    nhdsGT_basis 0 |>.mem_of_mem zero_lt_one
  filter_upwards [hsmall] with p hp
  have hpIcc : p ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hp.1, le_of_lt hp.2⟩
  have hpow : cfcR (fun x : ℝ ↦ x ^ p) B ≤ cfcR (fun x : ℝ ↦ x ^ p) A := by
    have hmono := power_Icc_zero_one_operatorMonotoneOn_Ici (𝓐 := 𝓐) p hpIcc
    exact hmono hA_sa hB_sa hBA (hspA.trans Set.Ioi_subset_Ici_self)
      (hspB.trans Set.Ioi_subset_Ici_self)
  have hscaled :
      p⁻¹ • (cfcR (fun x : ℝ ↦ x ^ p) B - 1) ≤
        p⁻¹ • (cfcR (fun x : ℝ ↦ x ^ p) A - 1) := by
    exact smul_le_smul_of_nonneg_left (sub_le_sub_right hpow 1) (inv_nonneg.mpr (le_of_lt hp.1))
  have hBexpr :
      cfcR (fun x : ℝ ↦ p⁻¹ * (x ^ p - 1)) B =
        p⁻¹ • (cfcR (fun x : ℝ ↦ x ^ p) B - 1) := by
    dsimp [cfcR]
    calc
      cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (fun x : ℝ ↦ p⁻¹ * (x ^ p - 1)) B
          = p⁻¹ • cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
              (fun x : ℝ ↦ x ^ p - 1) B := by
            rw [cfc_const_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
              (r := p⁻¹) (f := fun x : ℝ ↦ x ^ p - 1) (a := B)
              (hf := by fun_prop (disch := grind))]
      _ = p⁻¹ • (cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
              (fun x : ℝ ↦ x ^ p) B - 1) := by
            rw [cfc_sub (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
              (f := fun x : ℝ ↦ x ^ p) (g := fun _ : ℝ ↦ 1) (a := B)
              (hf := by fun_prop (disch := grind))
              (hg := by fun_prop)]
            rw [cfc_const_one (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) B hB_sa]
  have hAexpr :
      cfcR (fun x : ℝ ↦ p⁻¹ * (x ^ p - 1)) A =
        p⁻¹ • (cfcR (fun x : ℝ ↦ x ^ p) A - 1) := by
    dsimp [cfcR]
    calc
      cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (fun x : ℝ ↦ p⁻¹ * (x ^ p - 1)) A
          = p⁻¹ • cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
              (fun x : ℝ ↦ x ^ p - 1) A := by
            rw [cfc_const_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
              (r := p⁻¹) (f := fun x : ℝ ↦ x ^ p - 1) (a := A)
              (hf := by fun_prop (disch := grind))]
      _ = p⁻¹ • (cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
              (fun x : ℝ ↦ x ^ p) A - 1) := by
            rw [cfc_sub (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
              (f := fun x : ℝ ↦ x ^ p) (g := fun _ : ℝ ↦ 1) (a := A)
              (hf := by fun_prop (disch := grind))
              (hg := by fun_prop)]
            rw [cfc_const_one (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) A hA_sa]
  simpa [hBexpr, hAexpr] using hscaled

/-- The logarithm functional calculus is monotone on the positive spectrum. -/
@[gcongr]
theorem cfcR_log_le_cfcR_log_of_le {A B : 𝓐}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hBA : B ≤ A)
    (hspA : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ))
    (hspB : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    cfcR (fun x : ℝ ↦ Real.log x) B ≤ cfcR (fun x : ℝ ↦ Real.log x) A :=
  log_operatorMonotoneOn_Ioi hA hB hBA hspA hspB

/-! ### Concavity of the logarithm -/

omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
/-- Continuous-functional-calculus identity for normalized powers

For a self-adjoint element $X$ and $0<p$, the continuous functional
calculus of $x\mapsto p^{-1}(x^p-1)$ is
$p^{-1}$ times the difference between the functional calculus of $x\mapsto x^p$ and the
identity element.

Proof: The continuous functional calculus is compatible with multiplication by a
real scalar and with subtraction.  Pull the scalar $p^{-1}$ outside the calculus, split
$x^p-1$ as the difference of $x^p$ and the constant function $1$, and evaluate the latter
by the constant-one rule.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6. Correspondence as an auxiliary lemma used
in the proof of this result. -/
private lemma cfcR_rpow_sub_one_scaled {X : 𝓐} {p : ℝ} (hp : 0 < p)
    (hX : IsSelfAdjoint X) :
    cfcR (fun x : ℝ ↦ p⁻¹ * (x ^ p - 1)) X =
      p⁻¹ • (cfcR (fun x : ℝ ↦ x ^ p) X - 1) := by
  dsimp [cfcR]
  calc
    cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (fun x : ℝ ↦ p⁻¹ * (x ^ p - 1)) X
        = p⁻¹ • cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
            (fun x : ℝ ↦ x ^ p - 1) X := by
          rw [cfc_const_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
            (r := p⁻¹) (f := fun x : ℝ ↦ x ^ p - 1) (a := X)
            (hf := by fun_prop (disch := grind))]
    _ = p⁻¹ • (cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
            (fun x : ℝ ↦ x ^ p) X - 1) := by
          rw [cfc_sub (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
            (f := fun x : ℝ ↦ x ^ p) (g := fun _ : ℝ ↦ 1) (a := X)
            (hf := by fun_prop (disch := grind))
            (hg := by fun_prop)]
          rw [cfc_const_one (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) X hX]

/-- Operator concavity of normalized-power approximants
(Carlen 2010, proof of Theorem 2.6, immediately after formula (2.8))

For every $0<p<1$, the function
$x\mapsto p^{-1}(x^p-1)$ is operator concave on $(0,\infty)$.

Proof: Restrict the concavity of $x\mapsto x^p$ from
`operatorConcaveOn_rpow_Ici` to the positive interval.  For a fixed convex-combination
comparison, this gives
$(1-u)A^p+uB^p\le ((1-u)A+uB)^p$ in continuous functional calculus.  Subtracting the
identity from both sides and multiplying by the nonnegative scalar $p^{-1}$ preserves the
order; `cfcR_rpow_sub_one_scaled` identifies these three terms with the functional
calculus of $x\mapsto p^{-1}(x^p-1)$.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6. Correspondence as an auxiliary lemma used
in the proof of this result. -/
private lemma rpow_sub_one_scaled_operatorConcaveOn_Ioi (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    OperatorConcaveOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ))
      (fun x : ℝ ↦ p⁻¹ * (x ^ p - 1)) := by
  dsimp [OperatorConcaveOn, OperatorConvexOn]
  intro A B u hA hB hu0 hu1 As Bs
  set C : 𝓐 := (1 - u) • A + u • B
  have hC : IsSelfAdjoint C := by simpa [C] using isSelfAdjoint_convexCombo u hA hB
  have hpow :
      (1 - u) • cfcR (fun x : ℝ ↦ x ^ p) A +
          u • cfcR (fun x : ℝ ↦ x ^ p) B ≤
        cfcR (fun x : ℝ ↦ x ^ p) C := by
    have hpIcc : p ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hp.1, le_of_lt hp.2⟩
    have hconc := operatorConcaveOn_rpow_Ici (𝓐 := 𝓐) p hpIcc
    dsimp [OperatorConcaveOn, OperatorConvexOn] at hconc
    have hneg := hconc (A := A) (B := B) (t := u) hA hB hu0 hu1
      (As.trans Set.Ioi_subset_Ici_self) (Bs.trans Set.Ioi_subset_Ici_self)
    have hneg' :
        -cfcR (fun x : ℝ ↦ x ^ p) C ≤
          -((1 - u) • cfcR (fun x : ℝ ↦ x ^ p) A +
            u • cfcR (fun x : ℝ ↦ x ^ p) B) := by
      simpa [C, cfcR, cfc_neg, smul_neg, neg_add, add_assoc, add_left_comm, add_comm]
        using hneg
    exact (neg_le_neg_iff).1 hneg'
  have hpos :
      (1 - u) • cfcR (fun x : ℝ ↦ p⁻¹ * (x ^ p - 1)) A +
          u • cfcR (fun x : ℝ ↦ p⁻¹ * (x ^ p - 1)) B ≤
        cfcR (fun x : ℝ ↦ p⁻¹ * (x ^ p - 1)) C := by
    rw [cfcR_rpow_sub_one_scaled hp.1 hA, cfcR_rpow_sub_one_scaled hp.1 hB,
      cfcR_rpow_sub_one_scaled hp.1 hC]
    calc
      (1 - u) • (p⁻¹ • (cfcR (fun x : ℝ ↦ x ^ p) A - 1)) +
          u • (p⁻¹ • (cfcR (fun x : ℝ ↦ x ^ p) B - 1)) =
        p⁻¹ • ((1 - u) • cfcR (fun x : ℝ ↦ x ^ p) A +
          u • cfcR (fun x : ℝ ↦ x ^ p) B - 1) := by module
      _ ≤ p⁻¹ • (cfcR (fun x : ℝ ↦ x ^ p) C - 1) :=
        smul_le_smul_of_nonneg_left (sub_le_sub_right hpow 1)
          (inv_nonneg.mpr hp.1.le)
  have hneg :
      -cfcR (fun x : ℝ ↦ p⁻¹ * (x ^ p - 1)) C ≤
        -((1 - u) • cfcR (fun x : ℝ ↦ p⁻¹ * (x ^ p - 1)) A +
          u • cfcR (fun x : ℝ ↦ p⁻¹ * (x ^ p - 1)) B) :=
    neg_le_neg hpos
  simpa [C, cfcR, cfc_neg, smul_neg, neg_add, add_assoc, add_left_comm, add_comm]
    using hneg

/-- Logarithm operator concavity
(Carlen 2010, Theorem 2.6, final clause; proof using the first limit in formula (2.8))

The function
$f(t)=\log(t)$ is operator concave on $(0,\infty)$.
\emph{Lean deviation}: stated as $x \mapsto \log x$ operator concave on
$(0,\infty)$ in the sense of `OperatorConcaveOn`, over a fixed unital
$C^*$-algebra rather than matrices.

Proof: Fix self-adjoint $A,B$ with spectra in $(0,\infty)$ and $0\le u\le1$.
The convex combination $C=(1-u)A+uB$ again has spectrum in $(0,\infty)$.  For every
$0<p<1$, `rpow_sub_one_scaled_operatorConcaveOn_Ioi` gives
\[
  (1-u)p^{-1}(A^p-I)+u p^{-1}(B^p-I)
    \le p^{-1}(C^p-I).
\]
By `tendsto_cfcR_rpow_sub_one_log`, the three normalized power terms converge through
continuous functional calculus to $\log(A)$, $\log(B)$, and $\log(C)$ as
$p\downarrow0$.  The order relation is closed under such limits, hence
\[
  (1-u)\log(A)+u\log(B)\le \log(C),
\]
which is the defining operator-concavity inequality after unfolding
`OperatorConcaveOn`.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6. Correspondence to the logarithm result
using the normalized limit of powers. -/
theorem operatorConcaveOn_log_Ioi :
    OperatorConcaveOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ Real.log x) := by
  dsimp [OperatorConcaveOn, OperatorConvexOn]
  intro A B u hA hB hu0 hu1 As Bs
  set C : 𝓐 := (1 - u) • A + u • B
  have hC : IsSelfAdjoint C := by simpa [C] using isSelfAdjoint_convexCombo u hA hB
  have Cs : spectrum ℝ C ⊆ Set.Ioi (0 : ℝ) := by
    simpa [C] using
      spectrum_convexCombo_Ioi (A := A) (B := B) (t := u) hA hB hu0 hu1 As Bs
  have hlimAB := Filter.Tendsto.add
    (Filter.Tendsto.const_smul (tendsto_cfcR_rpow_sub_one_log (X := A) As) (1 - u))
    (Filter.Tendsto.const_smul (tendsto_cfcR_rpow_sub_one_log (X := B) Bs) u)
  have hlog :
      (1 - u) • cfcR (fun x : ℝ ↦ Real.log x) A +
          u • cfcR (fun x : ℝ ↦ Real.log x) B ≤
        cfcR (fun x : ℝ ↦ Real.log x) C := by
    refine le_of_tendsto_of_tendsto hlimAB
      (tendsto_cfcR_rpow_sub_one_log (X := C) Cs) ?_
    filter_upwards [nhdsGT_basis 0 |>.mem_of_mem zero_lt_one] with p hp
    have hconc := rpow_sub_one_scaled_operatorConcaveOn_Ioi (𝓐 := 𝓐) p hp
    dsimp [OperatorConcaveOn, OperatorConvexOn] at hconc
    exact (neg_le_neg_iff).1 (by
      simpa [C, cfcR, cfc_neg, smul_neg, neg_add, add_assoc, add_left_comm, add_comm]
        using hconc (A := A) (B := B) (t := u) hA hB hu0 hu1 As Bs)
  simpa [C, cfcR, cfc_neg, smul_neg, neg_add, add_assoc, add_left_comm, add_comm]
    using neg_le_neg hlog

/-! ### Convexity of x log x -/

/-- Operator convexity of normalized power differences
(Carlen 2010, proof of Theorem 2.6, immediately after formula (2.8), with p=1+q)

For $-1<q<1$ and $q\ne0$, the normalized difference
\[
  x\mapsto q^{-1}(x^{1+q}-x)
\]
is operator convex on $(0,\infty)$.

Proof: Put $p=1+q$.  If $q>0$, then $1<p<2$, so
`operatorConvexOn_rpow_Ici` gives operator convexity of $x\mapsto x^p$ on
$[0,\infty)$.  Subtracting the affine map $x\mapsto x$ and multiplying by the positive
scalar $q^{-1}$ preserves the convexity inequality.  If $q<0$, then $0<p<1$, and
`operatorConcaveOn_rpow_Ici` gives the opposite inequality for the powers; after subtracting
the same affine term, multiplication by the negative scalar $q^{-1}$ reverses the order and
again gives convexity.  The continuous-functional-calculus identities used here are just
compatibility with scalar multiplication, subtraction, and the identity function.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6. Correspondence as an auxiliary lemma used
in the proof of this result. -/
private lemma rpow_one_add_sub_id_scaled_operatorConvexOn_Ioi (q : ℝ)
    (hq : q ∈ Set.Ioo (-1 : ℝ) 1) (hq0 : q ≠ 0) :
    OperatorConvexOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ))
      (fun x : ℝ ↦ q⁻¹ * (x ^ ((1 : ℝ) + q) - x)) := by
  dsimp [OperatorConvexOn]
  intro A B u hA hB hu0 hu1 As Bs
  let p : ℝ := 1 + q
  have hp_pos : 0 < p := by dsimp [p]; linarith [hq.1]
  set C : 𝓐 := (1 - u) • A + u • B
  have hC : IsSelfAdjoint C := by simpa [C] using isSelfAdjoint_convexCombo u hA hB
  have hcalc (T : 𝓐) (hT : IsSelfAdjoint T) :
      cfcR (fun x : ℝ ↦ q⁻¹ * (x ^ p - x)) T =
        q⁻¹ • (cfcR (fun x : ℝ ↦ x ^ p) T - T) := by
    dsimp [cfcR]
    rw [cfc_const_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
      (r := q⁻¹) (f := fun x : ℝ ↦ x ^ p - x) (a := T)
      (hf := by fun_prop (disch := positivity))]
    rw [cfc_sub (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
      (f := fun x : ℝ ↦ x ^ p) (g := fun x : ℝ ↦ x) (a := T)
      (hf := by fun_prop (disch := positivity)) (hg := continuousOn_id)]
    rw [cfc_id' (R := ℝ) (a := T) (ha := hT)]
  have hscaled :
      q⁻¹ • (cfcR (fun x : ℝ ↦ x ^ p) C - C) ≤
        q⁻¹ • ((1 - u) • (cfcR (fun x : ℝ ↦ x ^ p) A - A) +
          u • (cfcR (fun x : ℝ ↦ x ^ p) B - B)) := by
    by_cases hqpos : 0 < q
    · apply smul_le_smul_of_nonneg_left _ (inv_nonneg.mpr hqpos.le)
      calc
        cfcR (fun x : ℝ ↦ x ^ p) C - C ≤
            ((1 - u) • cfcR (fun x : ℝ ↦ x ^ p) A +
              u • cfcR (fun x : ℝ ↦ x ^ p) B) - C :=
          sub_le_sub_right
            ((operatorConvexOn_rpow_Ici (𝓐 := 𝓐) p
              ⟨by dsimp [p]; linarith, by dsimp [p]; linarith [hq.2]⟩)
              hA hB hu0 hu1 (As.trans Set.Ioi_subset_Ici_self)
                (Bs.trans Set.Ioi_subset_Ici_self)) C
        _ = (1 - u) • (cfcR (fun x : ℝ ↦ x ^ p) A - A) +
            u • (cfcR (fun x : ℝ ↦ x ^ p) B - B) := by subst C; module
    · have hqneg : q < 0 := lt_of_le_of_ne (le_of_not_gt hqpos) hq0
      apply smul_le_smul_of_nonpos_left _ (inv_nonpos.mpr hqneg.le)
      calc
        (1 - u) • (cfcR (fun x : ℝ ↦ x ^ p) A - A) +
            u • (cfcR (fun x : ℝ ↦ x ^ p) B - B) =
          ((1 - u) • cfcR (fun x : ℝ ↦ x ^ p) A +
            u • cfcR (fun x : ℝ ↦ x ^ p) B) - C := by subst C; module
        _ ≤ cfcR (fun x : ℝ ↦ x ^ p) C - C := sub_le_sub_right (by
          exact neg_le_neg_iff.mp (by
            simpa [C, cfcR, cfc_neg, smul_neg, neg_add, add_assoc, add_left_comm, add_comm] using
              (operatorConcaveOn_rpow_Ici (𝓐 := 𝓐) p
                ⟨by dsimp [p]; linarith [hq.1], by dsimp [p]; linarith⟩)
                hA hB hu0 hu1 (As.trans Set.Ioi_subset_Ici_self)
                  (Bs.trans Set.Ioi_subset_Ici_self))) C
  calc
    cfcR (fun x : ℝ ↦ q⁻¹ * (x ^ (1 + q) - x)) ((1 - u) • A + u • B) =
        q⁻¹ • (cfcR (fun x : ℝ ↦ x ^ p) C - C) := by simpa [p, C] using hcalc C hC
    _ ≤ q⁻¹ • ((1 - u) • (cfcR (fun x : ℝ ↦ x ^ p) A - A) +
          u • (cfcR (fun x : ℝ ↦ x ^ p) B - B)) := hscaled
    _ = (1 - u) • (q⁻¹ • (cfcR (fun x : ℝ ↦ x ^ p) A - A)) +
          u • (q⁻¹ • (cfcR (fun x : ℝ ↦ x ^ p) B - B)) := by module
    _ = (1 - u) • cfcR (fun x : ℝ ↦ q⁻¹ * (x ^ (1 + q) - x)) A +
          u • cfcR (fun x : ℝ ↦ q⁻¹ * (x ^ (1 + q) - x)) B := by
      rw [hcalc A hA, hcalc B hB]

omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
/-- Continuous-functional-calculus convergence to $x\log x$
(Carlen 2010, proof of Theorem 2.6, second limit in formula (2.8), with q=p-1)

If $X$ is self-adjoint and its real spectrum is contained in
$(0,\infty)$, then the continuous functional calculus of
$x\mapsto q^{-1}(x^{1+q}-x)$ converges to the continuous functional calculus of
$x\mapsto x\log x$ as $q\downarrow0$.

Proof: On the spectrum of $X$ one has
$q^{-1}(x^{1+q}-x)=x\,q^{-1}(x^q-1)$ for $q>0$.  The continuous functional calculus turns
this product into $X$ times the calculus of $q^{-1}(x^q-1)$.  The latter converges to
$\log X$ by `tendsto_cfcR_rpow_sub_one_log`; continuity of left multiplication and the CFC
product rule identify the limit with the calculus of $x\mapsto x\log x$.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6. Correspondence as an auxiliary lemma used
in the proof of this result. -/
private lemma tendsto_cfcR_rpow_one_add_sub_id_scaled_mul_log {X : 𝓐}
    (hX : IsSelfAdjoint X) (Xs : spectrum ℝ X ⊆ Set.Ioi (0 : ℝ)) :
    Filter.Tendsto
      (fun q : ℝ => cfcR (fun x : ℝ ↦ q⁻¹ * (x ^ ((1 : ℝ) + q) - x)) X)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (cfcR (fun x : ℝ ↦ x * Real.log x) X)) := by
  have hlim := tendsto_cfcR_rpow_sub_one_log (𝓐 := 𝓐) (X := X) Xs
  have hscaled_cont (q : ℝ) :
      ContinuousOn (fun x : ℝ ↦ q⁻¹ * (x ^ q - 1)) (spectrum ℝ X) := by
    have hpow : ContinuousOn (fun x : ℝ ↦ x ^ q) (spectrum ℝ X) := by
      intro x hx
      exact (Real.continuousAt_rpow_const x q
        (Or.inl (Set.mem_Ioi.mp (Xs hx)).ne')).continuousWithinAt
    exact continuousOn_const.mul (hpow.sub continuousOn_const)
  have hlog_cont : ContinuousOn (fun x : ℝ ↦ Real.log x) (spectrum ℝ X) :=
    Real.continuousOn_log.mono (by
      intro x hx
      simpa [Set.mem_compl_iff] using (Set.mem_Ioi.mp (Xs hx)).ne')
  have hmul_eq (q : ℝ) (hq : 0 < q) :
      cfcR (fun x : ℝ ↦ q⁻¹ * (x ^ ((1 : ℝ) + q) - x)) X =
        X * cfcR (fun x : ℝ ↦ q⁻¹ * (x ^ q - 1)) X := by
    dsimp [cfcR]
    rw [show cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (fun x : ℝ ↦ q⁻¹ * (x ^ ((1 : ℝ) + q) - x)) X =
        cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
          (fun x : ℝ ↦ x * (q⁻¹ * (x ^ q - 1))) X by
      apply cfc_congr
      intro x hx
      change q⁻¹ * (x ^ ((1 : ℝ) + q) - x) = x * (q⁻¹ * (x ^ q - 1))
      rw [show x ^ ((1 : ℝ) + q) = x * x ^ q by
        simpa [Real.rpow_one] using Real.rpow_add (Set.mem_Ioi.mp (Xs hx)) (1 : ℝ) q]
      ring, cfc_mul (f := fun x : ℝ ↦ x) (g := fun x : ℝ ↦ q⁻¹ * (x ^ q - 1))
        (a := X) (hf := continuousOn_id) (hg := hscaled_cont q),
      cfc_id' (R := ℝ) (a := X) (ha := hX)]
  have htarget :
      X * cfcR (fun x : ℝ ↦ Real.log x) X =
        cfcR (fun x : ℝ ↦ x * Real.log x) X := by
    dsimp [cfcR]
    rw [cfc_mul (f := fun x : ℝ ↦ x) (g := fun x : ℝ ↦ Real.log x) (a := X)
        (hf := continuousOn_id) (hg := hlog_cont),
      cfc_id' (R := ℝ) (a := X) (ha := hX)]
  rw [← htarget]
  refine Filter.Tendsto.congr' ?_ (by
    simpa [ContinuousLinearMap.mul_apply'] using
      ((ContinuousLinearMap.mul ℝ (𝓐) X).continuous.tendsto
        (cfcR (fun x : ℝ ↦ Real.log x) X)).comp hlim)
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (hmul_eq q (Set.mem_Ioi.mp hq)).symm

/-- $x\log x$ operator convexity
(Carlen 2010, Theorem 2.6, final clause; proof using the second limit in formula (2.8))

The function
$f(t)=t\log(t)$ is operator convex on $(0,\infty)$.
\emph{Lean deviation}: stated as $x \mapsto x\log x$ operator convex on
$(0,\infty)$ in the sense of `OperatorConvexOn`, over a fixed unital
$C^*$-algebra rather than matrices.

Proof: Carlen (2010), proof of Theorem 2.6: for $p\ne 1$ with $0\le p\le 2$ consider
\[
  A \mapsto (p-1)^{-1}(A^p-A).
\]
If $1<p\le 2$, then $A\mapsto A^p$ is operator convex, so subtracting the affine map
$A\mapsto A$ and multiplying by the positive scalar $(p-1)^{-1}$ preserves operator
convexity.  If $0\le p<1$, then $A\mapsto A^p$ is operator concave, hence $A\mapsto A^p-A$ is
operator concave, and multiplication by the negative scalar $(p-1)^{-1}$ reverses the
concavity inequality into operator convexity.  For each positive definite $A$, the spectral
theorem reduces the limiting assertion to the scalar identity
\[
  \lim_{p\to 1}\frac{t^p-t}{p-1}=t\log t
\]
on the spectrum of $A$; uniformly on the spectra involved in a fixed convexity
comparison, continuous functional calculus permits passage to the limit.  Since
operator convexity inequalities are closed under such limits, the limit map
$A\mapsto A\log(A)$ is operator convex.
\emph{Lean deviation}: the local convexity node `rpow_one_add_sub_id_scaled_operatorConvexOn_Ioi`
formalizes the two Carlen branches for the normalized functions
$q^{-1}(x^{1+q}-x)$, $-1<q<1$, $q\ne0$.  The final limit passage uses the right-hand
subfamily $q\downarrow0$: `tendsto_cfcR_rpow_one_add_sub_id_scaled_mul_log` rewrites the CFC
approximant as $X\,q^{-1}(X^q-I)$ and identifies its limit with $X\log X$.
Applying the closedness of
the order relation to the convexity inequalities for these approximants yields the displayed
operator-convexity inequality for $x\mapsto x\log x$.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6. Correspondence to the logarithm result
using the normalized limit of powers. -/
theorem operatorConvexOn_mul_log_Ioi :
    OperatorConvexOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ x * Real.log x) := by
  dsimp [OperatorConvexOn]
  intro A B u hA hB hu0 hu1 As Bs
  set C : 𝓐 := (1 - u) • A + u • B
  have hC : IsSelfAdjoint C := by simpa [C] using isSelfAdjoint_convexCombo u hA hB
  have Cs : spectrum ℝ C ⊆ Set.Ioi (0 : ℝ) := by
    simpa [C] using
      spectrum_convexCombo_Ioi (A := A) (B := B) (t := u) hA hB hu0 hu1 As Bs
  have hlimAB := Filter.Tendsto.add
    (Filter.Tendsto.const_smul
      (tendsto_cfcR_rpow_one_add_sub_id_scaled_mul_log (X := A) hA As) (1 - u))
    (Filter.Tendsto.const_smul
      (tendsto_cfcR_rpow_one_add_sub_id_scaled_mul_log (X := B) hB Bs) u)
  have hmain :
      cfcR (fun x : ℝ ↦ x * Real.log x) C ≤
        (1 - u) • cfcR (fun x : ℝ ↦ x * Real.log x) A +
          u • cfcR (fun x : ℝ ↦ x * Real.log x) B := by
    refine le_of_tendsto_of_tendsto
      (tendsto_cfcR_rpow_one_add_sub_id_scaled_mul_log (X := C) hC Cs) hlimAB ?_
    filter_upwards [nhdsGT_basis 0 |>.mem_of_mem zero_lt_one] with q hq
    have hconv :=
      rpow_one_add_sub_id_scaled_operatorConvexOn_Ioi
        (𝓐 := 𝓐) q ⟨by linarith [hq.1], hq.2⟩ hq.1.ne'
    dsimp [OperatorConvexOn] at hconv
    exact hconv (A := A) (B := B) (t := u) hA hB hu0 hu1 As Bs
  simpa [C] using hmain

end LogLimit

end LownerHeinzCore
