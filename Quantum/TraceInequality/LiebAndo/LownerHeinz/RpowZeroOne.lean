/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LiebAndo.LownerHeinz.Reciprocal
import Quantum.TraceInequality.LownerHeinz.Reciprocal

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

/-- `x ↦ x / (x + t)` is operator concave on `[0, ∞)` for `t > 0`.

Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6. Correspondence restricted to the exponent
range and domain of this declaration. -/
/- Concavity of the shifted ratio
    (Carlen 2009, proof of Theorem 2.6, Lemma 2.7 and the integrand of Lemma 2.8, formula (2.6)) -/
/- (Carlen 2009, proof of Theorem 2.6, Lemma 2.7 and the integrand of Lemma 2.8, formula (2.6)) The
    integrand $A \mapsto \frac{1}{t}-\frac{1}{t+A}$ is operator concave, by Lemma 2.7 applied to the
    shifted reciprocal. Equivalently, up to the positive scalar factor $1/t$, this is the map
    $A \mapsto A/(t+A)=I-t(t+A)^{-1}$.
    The ratio function itself is not stated as an independent proposition in the source.
    *Lean deviation*: this node states the equivalent ratio form:
    for every $t>0$, $x \mapsto x/(x+t)$ is operator concave on $[0,\infty)$ in the sense of
    the definition of `OperatorConcaveOn`. -/
/- Carlen09: Lemma 2.7 says $A \mapsto (t+A)^{-1}$ is operator convex after
    translation, hence $A \mapsto -t(t+A)^{-1}$ is operator concave for $t>0$; adding the
    constant $I$ gives the concavity of $A \mapsto A/(t+A)$.
    *Lean deviation*: the formal proof expands the definition of `OperatorConcaveOn`, rewrites
    $-x/(x+t)$ as a constant plus a positive multiple of $1/(x+t)$ under continuous functional
    calculus, and uses shifted reciprocal convexity (`one_div_add_t_operatorConvexOn_Ici`). -/
theorem ratio_add_t_operatorConcaveOn_Ici (t : ℝ) (ht : 0 < t) :
    OperatorConcaveOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x / (x + t)) := by
  dsimp [OperatorConcaveOn, OperatorConvexOn]
  intro A B u hA hB hu0 hu1 As Bs
  let g : ℝ → ℝ := fun x ↦ 1 / (x + t)
  set C : 𝓐 := (1 - u) • A + u • B
  have hC : IsSelfAdjoint C := by simpa [C] using isSelfAdjoint_convexCombo u hA hB
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg
      (smul_nonneg (sub_nonneg.mpr hu1) (nonneg_of_spectrum_subset_Ici hA As))
      (smul_nonneg hu0 (nonneg_of_spectrum_subset_Ici hB Bs))
  have Cs : spectrum ℝ C ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    exact spectrum_nonneg_of_nonneg (𝕜 := ℝ) (A := 𝓐) (a := C) hC0 hx
  have hcalc (T : 𝓐) (hT : IsSelfAdjoint T) (Ts : spectrum ℝ T ⊆ Set.Ici (0 : ℝ)) :
      cfcR (fun x : ℝ ↦ -(x / (x + t))) T =
        algebraMap ℝ 𝓐 (-1 : ℝ) + t • cfcR g T := by
    have hne : ∀ x ∈ spectrum ℝ T, x + t ≠ 0 := fun x hx ↦
      ne_of_gt (add_pos_of_nonneg_of_pos (Ts hx) ht)
    have hg : ContinuousOn g (spectrum ℝ T) := by
      simpa [g, one_div] using (continuousOn_id.add continuousOn_const).inv₀ hne
    dsimp [cfcR]
    calc
      cfcR (fun x : ℝ ↦ -(x / (x + t))) T =
          cfcR (fun x : ℝ ↦ (-1 : ℝ) + t * g x) T := by
        apply cfc_congr
        intro x hx
        simp only [g]
        field_simp [hne x hx]
        ring
      _ = algebraMap ℝ 𝓐 (-1 : ℝ) + cfcR (fun x : ℝ ↦ t * g x) T := by
        simpa using cfc_const_add (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
          (r := (-1 : ℝ)) (f := fun x : ℝ ↦ t * g x) (a := T)
          (hf := continuousOn_const.mul hg) (ha := hT)
      _ = algebraMap ℝ 𝓐 (-1 : ℝ) + t • cfcR g T := by
        simp [cfc_const_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
          (r := t) (f := g) (a := T) (hf := hg)]
  have hscale :
      t • cfcR g C ≤
        t • ((1 - u) • cfcR g A + u • cfcR g B) :=
    smul_le_smul_of_nonneg_left (by
      simpa [g, C] using
        (one_div_add_t_operatorConvexOn_Ici (𝓐 := 𝓐) t ht)
          (A := A) (B := B) (t := u) hA hB hu0 hu1 As Bs) ht.le
  rw [hcalc C hC Cs, hcalc A hA As, hcalc B hB Bs]
  calc
    algebraMap ℝ 𝓐 (-1 : ℝ) + t • cfcR g C ≤
        algebraMap ℝ 𝓐 (-1 : ℝ) +
          t • ((1 - u) • cfcR g A + u • cfcR g B) := add_le_add_right hscale _
    _ = (1 - u) • (algebraMap ℝ 𝓐 (-1 : ℝ) + t • cfcR g A) +
        u • (algebraMap ℝ 𝓐 (-1 : ℝ) + t • cfcR g B) := by module

omit [Nontrivial (𝓐)] in
omit [StarOrderedRing 𝓐] in
private lemma cfcₙ_rpowIntegrand₀₁_eq_smul_cfcR_ratio {q : NNReal} (hq : q ∈ Set.Ioo (0 : NNReal) 1)
    {t : ℝ} (htpos : 0 < t) (X : 𝓐) (hX0 : 0 ≤ X) :
    cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) X =
      (t ^ ((q : ℝ) - 1)) • cfcR (fun x : ℝ => x / (x + t)) X := by
  have hq_real : ((q : ℝ) : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨(NNReal.coe_pos).2 hq.1, (NNReal.coe_lt_coe).2 hq.2⟩
  let ratio : ℝ → ℝ := fun x => x / (x + t)
  let r : ℝ := t ^ ((q : ℝ) - 1)
  have hcont_ratio : ContinuousOn ratio (spectrum ℝ X) :=
    continuousOn_id.div (continuousOn_id.add continuousOn_const) fun x hx ↦
      ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hX0 hx) htpos)
  have hcfcₙ : cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) X =
      cfcR (Real.rpowIntegrand₀₁ (q : ℝ) t) X := by
    simpa using
      (cfcₙ_eq_cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (f := Real.rpowIntegrand₀₁ (q : ℝ) t) (a := X)
        (hf := (Real.continuousOn_rpowIntegrand₀₁_Ici hq_real htpos).mono fun x hx ↦
          Set.mem_Ici.mpr (quasispectrum_nonneg_of_nonneg X hX0 x hx)) (hf0 := by simp))
  have hEq :
      (spectrum ℝ X).EqOn (Real.rpowIntegrand₀₁ (q : ℝ) t) (fun x : ℝ ↦ r * ratio x) := by
    intro x hx
    simp [r, ratio, add_comm, mul_div_assoc,
      Real.rpowIntegrand₀₁_eq_pow_div hq_real htpos.le (spectrum_nonneg_of_nonneg hX0 hx)]
  calc
    cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) X =
        cfcR (Real.rpowIntegrand₀₁ (q : ℝ) t) X := hcfcₙ
    _ = cfcR (fun x : ℝ ↦ r * ratio x) X := cfc_congr hEq
    _ = r • cfcR ratio X := by
      simpa using
        (cfc_const_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := r) (f := ratio)
          (a := X) (hf := hcont_ratio))
    _ = (t ^ ((q : ℝ) - 1)) • cfcR (fun x : ℝ => x / (x + t)) X := by
      rfl

private lemma cfcR_ratio_weighted_le {t : ℝ} (htpos : 0 < t) {A B : 𝓐} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • cfcR (fun x : ℝ => x / (x + t)) A + b • cfcR (fun x : ℝ => x / (x + t)) B
      ≤ cfcR (fun x : ℝ => x / (x + t)) (a • A + b • B) := by
  have ha1 : a = 1 - b := by linarith [hab]
  have hb1 : b ≤ 1 := by linarith [ha, hab]
  have hspec (X : 𝓐) (hX0 : 0 ≤ X) : spectrum ℝ X ⊆ Set.Ici (0 : ℝ) := fun _ hx ↦
    Set.mem_Ici.mpr (spectrum_nonneg_of_nonneg hX0 hx)
  have hOp := ratio_add_t_operatorConcaveOn_Ici (𝓐 := 𝓐) t htpos
  have hneg' :
      cfcR (fun x : ℝ ↦ - (x / (x + t))) ((1 - b) • A + b • B)
        ≤ (1 - b) • cfcR (fun x : ℝ ↦ - (x / (x + t))) A
          + b • cfcR (fun x : ℝ ↦ - (x / (x + t))) B := by
    dsimp [OperatorConcaveOn, OperatorConvexOn] at hOp
    exact hOp (A := A) (B := B) (t := b) (IsSelfAdjoint.of_nonneg hA0)
      (IsSelfAdjoint.of_nonneg hB0) hb hb1 (hspec A hA0) (hspec B hB0)
  have hneg'' :
      -cfcR (fun x : ℝ => x / (x + t)) ((1 - b) • A + b • B)
        ≤ -((1 - b) • cfcR (fun x : ℝ => x / (x + t)) A
            + b • cfcR (fun x : ℝ => x / (x + t)) B) := by
    have h' :
        -cfcR (fun x : ℝ => x / (x + t)) ((1 - b) • A + b • B)
          ≤ -(b • cfcR (fun x : ℝ => x / (x + t)) B
              + (1 - b) • cfcR (fun x : ℝ => x / (x + t)) A) := by
      simpa [cfcR, cfc_neg, smul_neg, neg_add] using hneg'
    simpa [add_comm, add_left_comm, add_assoc] using h'
  simpa [ha1, add_comm, add_left_comm, add_assoc] using neg_le_neg_iff.mp hneg''

private lemma concaveOn_cfcₙ_rpowIntegrand₀₁ {q : NNReal} (hq : q ∈ Set.Ioo (0 : NNReal) 1)
    {t : ℝ} (htpos : 0 < t) :
    ConcaveOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 => cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A) := by
  have hq_real : ((q : ℝ) : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨(NNReal.coe_pos).2 hq.1, (NNReal.coe_lt_coe).2 hq.2⟩
  refine ⟨convex_Ici (𝕜 := ℝ) (0 : 𝓐), ?_⟩
  intro A hA B hB a b ha hb hab
  have hA0 : 0 ≤ A := by simpa [Set.Ici] using hA
  have hB0 : 0 ≤ B := by simpa [Set.Ici] using hB
  have hAB0 : 0 ≤ a • A + b • B := add_nonneg (smul_nonneg ha hA0) (smul_nonneg hb hB0)
  let ratio : ℝ → ℝ := fun x => x / (x + t)
  let r : ℝ := t ^ ((q : ℝ) - 1)
  have hr_nonneg : 0 ≤ r := Real.rpow_nonneg (le_of_lt htpos) _
  have hrepr (X : 𝓐) (hX0 : 0 ≤ X) :
      cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) X = r • cfcR ratio X := by
    simpa [r, ratio] using cfcₙ_rpowIntegrand₀₁_eq_smul_cfcR_ratio  (q := q) hq htpos X hX0
  have hratio :
      a • cfcR ratio A + b • cfcR ratio B ≤ cfcR ratio (a • A + b • B) := by
    -- use the separate lemma to keep heartbeats per-declaration small
    -- (`ratio` is a local abbreviation here)
    simpa [ratio] using cfcR_ratio_weighted_le  (t := t) htpos (A := A) (B := B) hA0 hB0 ha hb hab
  have hscaled : r • (a • cfcR ratio A + b • cfcR ratio B) ≤ r • cfcR ratio (a • A + b • B) :=
    smul_le_smul_of_nonneg_left hratio hr_nonneg
  have hL :
      a • cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A + b • cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) B =
        r • (a • cfcR ratio A + b • cfcR ratio B) := by
    simp [hrepr A hA0, hrepr B hB0, smul_add, smul_smul, mul_comm]
  have hR :
      cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) (a • A + b • B) = r • cfcR ratio (a • A + b • B) := by
    simp [hrepr (a • A + b • B) hAB0]
  calc
    a • cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A + b • cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) B
        = r • (a • cfcR ratio A + b • cfcR ratio B) := hL
    _ ≤ r • cfcR ratio (a • A + b • B) := hscaled
    _ = cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) (a • A + b • B) := hR.symm

private lemma concaveOn_nnrpow_Ioo {q : NNReal} (hq : q ∈ Set.Ioo (0 : NNReal) 1) :
    ConcaveOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ A ^ q) := by
  -- integral representation for `a ↦ a ^ q`
  obtain ⟨μ, hμ⟩ :=
    CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ (A := 𝓐) hq
  let ν : MeasureTheory.Measure ℝ := μ.restrict (Set.Ioi (0 : ℝ))
  let F : ℝ → 𝓐 → 𝓐 := fun t A => cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A
  have hF_int : ∀ A ∈ Set.Ici (0 : 𝓐), MeasureTheory.Integrable (fun t => F t A) ν := by
    intro A hA
    simpa [F, ν, MeasureTheory.IntegrableOn] using (hμ A hA).1
  have hF_conc :
      ∀ᵐ t ∂ν, ConcaveOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 => F t A) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    simpa [F] using (concaveOn_cfcₙ_rpowIntegrand₀₁  (q := q) hq ht)
  have hconc_int :
      ConcaveOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ ∫ t, F t A ∂ν) :=
    MeasureTheory.integral_concaveOn_of_integrand_ae
      (μ := ν) (s := Set.Ici (0 : 𝓐)) (f := fun t A => F t A)
      (convex_Ici (𝕜 := ℝ) (0 : 𝓐)) hF_conc hF_int
  -- identify the integral with `A ^ q` on `Ici 0`
  refine hconc_int.congr ?_
  intro A hA
  -- `A ^ q` is the set integral of the integrand on `Ioi 0`
  have hEq : A ^ q = ∫ t, F t A ∂ν := by
    simpa [F, ν] using (hμ A hA).2
  simp [hEq]

private lemma concaveOn_rpow_Ioo {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ConcaveOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ A ^ p) := by
  -- reduce to the `ℝ≥0` exponent case
  let q : NNReal := ⟨p, le_of_lt hp.1⟩
  have hq0 : (0 : NNReal) < q := by
    have : (0 : ℝ) < (q : ℝ) := by
      simpa [q] using hp.1
    exact (NNReal.coe_pos).1 this
  have hq1 : q < (1 : NNReal) := by
    have : (q : ℝ) < (1 : ℝ) := by
      simpa [q] using hp.2
    exact (NNReal.coe_lt_coe).1 (by simpa using this)
  have hq : q ∈ Set.Ioo (0 : NNReal) 1 := ⟨hq0, hq1⟩
  -- main lemma: concavity for `a ↦ a ^ q`
  have hconc : ConcaveOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ A ^ q) :=
    concaveOn_nnrpow_Ioo  hq
  -- transport concavity from `A ^ q` to `A ^ p`
  refine hconc.congr ?_
  intro A hA
  -- `A ^ q = A ^ (q : ℝ)`, and `(q : ℝ) = p`
  simpa [q] using (CFC.nnrpow_eq_rpow (A := 𝓐) (a := A) (x := q) hq0)

/-- `x ↦ x ^ p` is operator concave on `[0, ∞)` for `p ∈ [0, 1]`.

Source: arXiv:2607.05492v1, §3.
Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6 / Lemma 2.8. Correspondence restricted to
the exponent range and domain of this declaration. -/
/- Concavity of powers between zero and one
    (Carlen 2009, Theorem 2.6, second clause; proof using Lemma 2.8, formula (2.6)) -/
/- (Carlen 2009, Theorem 2.6, second clause; proof using Lemma 2.8, formula (2.6)) For
    $0 \leq p \leq 1$, the function $f(t)=t^p$ is operator concave.
    *Lean deviation*: stated as $x \mapsto x^p$ operator concave on $[0,\infty)$ in the
    sense of the definition of `OperatorConcaveOn`, over a unital $C^*$-algebra rather than
    matrices. -/
/- Carlen09 (proof of Theorem 2.6): for $0<p<1$, Lemma 2.8 gives
    \[
      A^p = \frac{\sin(\pi p)}{\pi}
        \int_0^\infty t^p\left(\frac1t-\frac1{t+A}\right)\,\mathrm{d}t .
    \]
    By Lemma 2.7 the shifted reciprocal makes each integrand operator concave, and positive
    weighted sums of operator-concave functions are operator concave; the endpoint cases are
    trivial.
    *Lean deviation*: the formal proof uses Mathlib's integral representation for real
    powers, proves concavity of the ratio integrand through operator concavity of the ratio
    (`ratio_add_t_operatorConcaveOn_Ici`), and integrates concave functions with
    `MeasureTheory.integral_concaveOn_of_integrand_ae`, and handles $p=0,1$ separately. -/
theorem power_Icc_zero_one_operatorConcaveOn_Ici (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    OperatorConcaveOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  by_cases hp0 : p = 0
  · subst hp0
    dsimp [OperatorConcaveOn, OperatorConvexOn]
    intro A B u hA hB hu0 hu1 As Bs
    have hC : IsSelfAdjoint ((1 - u) • A + u • B) := isSelfAdjoint_convexCombo u hA hB
    have hfun : (fun x : ℝ ↦ - (x ^ (0 : ℝ))) = (fun _ : ℝ ↦ (-1 : ℝ)) := by
      funext x
      simp
    have hconst (T : 𝓐) (hT : IsSelfAdjoint T) :
        cfcR (fun _ : ℝ ↦ (-1 : ℝ)) T = (-1 : 𝓐) := by
      simpa [cfcR] using
        (cfc_const (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (-1 : ℝ) T hT)
    rw [hfun]
    rw [hconst _ hC, hconst _ hA, hconst _ hB]
    simp
  by_cases hp1 : p = 1
  · subst hp1
    dsimp [OperatorConcaveOn, OperatorConvexOn]
    intro A B u hA hB hu0 hu1 As Bs
    have hC : IsSelfAdjoint ((1 - u) • A + u • B) := isSelfAdjoint_convexCombo u hA hB
    have hfun : (fun x : ℝ ↦ - (x ^ (1 : ℝ))) = (fun x : ℝ ↦ -x) := by
      funext x
      simp
    have hneg (T : 𝓐) (hT : IsSelfAdjoint T) :
        cfcR (fun x : ℝ ↦ -x) T = -T := by
      simpa [cfcR] using (cfc_neg_id (R := ℝ) (p := IsSelfAdjoint) (a := T) hT)
    rw [hfun]
    rw [hneg _ hC, hneg _ hA, hneg _ hB]
    -- both sides are `-((1-u)•A + u•B)`
    simp [add_comm, sub_eq_add_neg]
  have hp01 : p ∈ Set.Ioo (0 : ℝ) 1 := ⟨hp.1.lt_of_ne' hp0, hp.2.lt_of_ne hp1⟩
  dsimp [OperatorConcaveOn, OperatorConvexOn]
  intro A B u hA hB hu0 hu1 As Bs
  have hA0 : 0 ≤ A := nonneg_of_spectrum_subset_Ici hA As
  have hB0 : 0 ≤ B := nonneg_of_spectrum_subset_Ici hB Bs
  have hu0' : 0 ≤ (1 - u) := sub_nonneg.mpr hu1
  have hC0 : 0 ≤ (1 - u) • A + u • B :=
    add_nonneg (smul_nonneg hu0' hA0) (smul_nonneg hu0 hB0)
  set C : 𝓐 := (1 - u) • A + u • B
  have hC_mem : C ∈ Set.Ici (0 : 𝓐) := by
    simpa [C, Set.Ici] using hC0
  have hA_mem : A ∈ Set.Ici (0 : 𝓐) := by simpa [Set.Ici] using hA0
  have hB_mem : B ∈ Set.Ici (0 : 𝓐) := by simpa [Set.Ici] using hB0
  have hconcC : (1 - u) • (A ^ p) + u • (B ^ p) ≤ C ^ p := by
    have hab : (1 - u) + u = (1 : ℝ) := by ring
    simpa [C] using (concaveOn_rpow_Ioo  hp01).2 hA_mem hB_mem hu0' hu0 hab
  have hcalc (T : 𝓐) (hT0 : 0 ≤ T) :
      cfcR (fun x : ℝ ↦ x ^ p) T = T ^ p := by
    simpa [cfcR] using
      (CFC.rpow_eq_cfc_real (A := 𝓐) (a := T) (y := p) (ha := hT0)).symm
  have hconcC' :
      (1 - u) • cfcR (fun x : ℝ ↦ x ^ p) A + u • cfcR (fun x : ℝ ↦ x ^ p) B
        ≤ cfcR (fun x : ℝ ↦ x ^ p) C := by
    simpa [hcalc A hA0, hcalc B hB0, hcalc C hC0, C] using hconcC
  -- convert concavity into convexity of `x ↦ -x^p`
  simpa [cfcR, cfc_neg, smul_neg, neg_add, add_assoc, add_left_comm, add_comm] using
    neg_le_neg hconcC'

end Spectrum

end LownerHeinzCore
