/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LiebAndo.LownerHeinz.RpowZeroOne

/-!
# Powers between one and two


-/

namespace LownerHeinzCore

universe u

open CFC

section Spectrum

variable {𝓐 : Type u}
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
variable [Nontrivial 𝓐]
variable [NonnegSpectrumClass ℝ 𝓐]

/-! ### Integral convexity setup for powers between one and two -/

private lemma convexOn_cfcR_one_div_add_t (t : ℝ) (htpos : 0 < t) :
    ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun X : 𝓐 ↦ cfcR (fun x : ℝ ↦ 1 / (x + t)) X) := by
  have hs : Convex ℝ (Set.Ici (0 : 𝓐)) := convex_Ici (𝕜 := ℝ) (0 : 𝓐)
  refine ⟨hs, ?_⟩
  intro A hA B hB a b ha hb hab
  have ha1 : a = 1 - b := by linarith [hab]
  have hb1 : b ≤ 1 := by linarith [ha, hab]
  have hA0 : 0 ≤ A := by simpa [Set.Ici] using hA
  have hB0 : 0 ≤ B := by simpa [Set.Ici] using hB
  have hspec (X : 𝓐) (hX0 : 0 ≤ X) : spectrum ℝ X ⊆ Set.Ici (0 : ℝ) := fun _ hx ↦
    Set.mem_Ici.mpr (spectrum_nonneg_of_nonneg hX0 hx)
  have hOp := one_div_add_t_operatorConvexOn_Ici (𝓐 := 𝓐) t htpos
  dsimp [OperatorConvexOn] at hOp
  simpa [one_div, ha1] using
    hOp (A := A) (B := B) (t := b) (IsSelfAdjoint.of_nonneg hA0)
      (IsSelfAdjoint.of_nonneg hB0) hb hb1 (hspec A hA0) (hspec B hB0)

omit [Nontrivial (𝓐)] in
private lemma G_eqOn_rpowIntegrand₀₁_mul {q : NNReal} (hq_real : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    (t : ℝ) (htpos : 0 < t) :
    (Set.Ici (0 : 𝓐)).EqOn
      (fun X : 𝓐 ↦ cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X)
      (fun X : 𝓐 ↦ (t ^ ((q : ℝ) - 1)) •
        (X - algebraMap ℝ (𝓐) t + (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X)) := by
  intro X hX
  have hX0 : 0 ≤ X := by simpa [Set.Ici] using hX
  have hX_sa : IsSelfAdjoint X := IsSelfAdjoint.of_nonneg hX0
  have hqs : quasispectrum ℝ X ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    simpa [Set.Ici] using quasispectrum_nonneg_of_nonneg X hX0 x hx
  have hf :
      ContinuousOn (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x)
        (quasispectrum ℝ X) :=
    continuousOn_id.mul <| (Real.continuousOn_rpowIntegrand₀₁_Ici hq_real htpos).mono hqs
  have hcfcₙ :
      cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X =
        cfcR (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X := by
    simpa using
      (cfcₙ_eq_cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (f := fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) (a := X)
        (hf := hf) (hf0 := by simp))
  have hne : ∀ x ∈ spectrum ℝ X, x + t ≠ 0 :=
    fun x hx ↦ ne_of_gt <|
      add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hX0 hx) htpos
  have hEq :
      (spectrum ℝ X).EqOn
        (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x)
        (fun x : ℝ ↦ (t ^ ((q : ℝ) - 1)) *
          (x - t + (t ^ (2 : ℕ)) * (1 / (x + t)))) := by
    intro x hx
    dsimp
    rw [Real.rpowIntegrand₀₁_eq_pow_div hq_real htpos.le
      (spectrum_nonneg_of_nonneg hX0 hx)]
    rw [add_comm t x]
    field_simp [hne x hx]; ring_nf
  have hcont : ContinuousOn (fun x : ℝ ↦ 1 / (x + t)) (spectrum ℝ X) :=
    continuousOn_const.div (continuousOn_id.add continuousOn_const) hne
  have hcont_inner :
      ContinuousOn (fun x : ℝ ↦ x - t + (t ^ (2 : ℕ)) * (1 / (x + t)))
        (spectrum ℝ X) :=
    (continuousOn_id.sub continuousOn_const).add (continuousOn_const.mul hcont)
  calc
    cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X =
        cfcR (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X := hcfcₙ
    _ = cfcR (fun x : ℝ ↦ (t ^ ((q : ℝ) - 1)) *
        (x - t + (t ^ (2 : ℕ)) * (1 / (x + t)))) X := cfc_congr hEq
    _ = (t ^ ((q : ℝ) - 1)) •
        cfcR (fun x : ℝ ↦ x - t + (t ^ (2 : ℕ)) * (1 / (x + t))) X := by
      simpa [cfcR] using
        (cfc_const_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
          (r := t ^ ((q : ℝ) - 1))
          (f := fun x : ℝ ↦ x - t + (t ^ (2 : ℕ)) * (1 / (x + t))) (a := X)
          (hf := hcont_inner))
    _ = (t ^ ((q : ℝ) - 1)) •
        (cfcR (fun x : ℝ ↦ x - t) X +
          cfcR (fun x : ℝ ↦ (t ^ (2 : ℕ)) * (1 / (x + t))) X) := by
      simp only [cfcR]
      rw [cfc_add (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (f := fun x : ℝ ↦ x - t)
        (g := fun x : ℝ ↦ (t ^ (2 : ℕ)) * (1 / (x + t))) (a := X)
        (hf := continuousOn_id.sub continuousOn_const)
        (hg := continuousOn_const.mul hcont)]
    _ = (t ^ ((q : ℝ) - 1)) •
        ((cfcR (fun x : ℝ ↦ x) X - cfcR (fun _ : ℝ ↦ t) X) +
          (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X) := by
      simp only [cfcR]
      rw [cfc_sub (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
          (f := fun x : ℝ ↦ x) (g := fun _ : ℝ ↦ t) (a := X)
          (hf := continuousOn_id) (hg := continuousOn_const),
        cfc_const_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
          (r := t ^ (2 : ℕ)) (f := fun x : ℝ ↦ 1 / (x + t)) (a := X)
          (hf := hcont)]
    _ = (t ^ ((q : ℝ) - 1)) •
        (X - algebraMap ℝ (𝓐) t +
          (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X) := by
      simp only [cfcR]
      rw [cfc_id' (R := ℝ) (ha := hX_sa), cfc_const (ha := hX_sa)]

private lemma convexOn_G_rpowIntegrand₀₁_mul {q : NNReal} (hq_real : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    (t : ℝ) (htpos : 0 < t) :
    ConvexOn ℝ (Set.Ici (0 : 𝓐))
      (fun X : 𝓐 ↦ cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X) := by
  -- use `EqOn` to replace the integrand by a structured convex expression
  let r : ℝ := t ^ ((q : ℝ) - 1)
  have hr_nonneg : 0 ≤ r :=
    Real.rpow_nonneg (le_of_lt htpos) _
  have hs : Convex ℝ (Set.Ici (0 : 𝓐)) := convex_Ici (𝕜 := ℝ) (0 : 𝓐)
  have h_aff : ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun X : 𝓐 ↦ X - algebraMap ℝ (𝓐) t) := by
    have hid : ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun X : 𝓐 ↦ X) := by
      simpa using (convexOn_id (𝕜 := ℝ) (s := Set.Ici (0 : 𝓐)) hs)
    have hconst : ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun _ : 𝓐 ↦ -algebraMap ℝ (𝓐) t) :=
      convexOn_const (-algebraMap ℝ (𝓐) t) hs
    simpa [sub_eq_add_neg] using hid.add hconst
  have h_one_div : ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun X : 𝓐 ↦ cfcR (fun x : ℝ ↦ 1 / (x + t)) X) :=
    convexOn_cfcR_one_div_add_t  t htpos
  have h_inner :
      ConvexOn ℝ (Set.Ici (0 : 𝓐))
        (fun X : 𝓐 ↦
          X - algebraMap ℝ (𝓐) t + (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X) := by
    have hterm :
        ConvexOn ℝ (Set.Ici (0 : 𝓐))
          (fun X : 𝓐 ↦ (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X) :=
      (h_one_div.smul (sq_nonneg t))
    exact h_aff.add hterm
  have h_rhs :
      ConvexOn ℝ (Set.Ici (0 : 𝓐))
        (fun X : 𝓐 ↦ r •
          (X - algebraMap ℝ (𝓐) t + (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X)) :=
    h_inner.smul hr_nonneg
  -- transfer convexity back to the `cfcₙ` expression
  refine h_rhs.congr ?_
  intro X hX
  have : (fun X : 𝓐 ↦ cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X) X
      =
      (fun X : 𝓐 ↦ r •
        (X - algebraMap ℝ (𝓐) t + (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X)) X := by
    simpa [r] using G_eqOn_rpowIntegrand₀₁_mul  hq_real t htpos hX
  simpa using this.symm

omit [Nontrivial (𝓐)] in
private lemma ae_cfcₙ_mul_id_rpowIntegrand₀₁_restrict_Ioi {q : NNReal}
    (hq_real : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    (μ : MeasureTheory.Measure ℝ) (A : 𝓐) (hA0 : 0 ≤ A) :
    ∀ᵐ t ∂(μ.restrict (Set.Ioi (0 : ℝ))),
      cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) A =
        A * cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A := by
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have hqs : quasispectrum ℝ A ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := quasispectrum_nonneg_of_nonneg A hA0 x hx
    simpa [Set.Ici] using hx0
  have hg : ContinuousOn (Real.rpowIntegrand₀₁ (q : ℝ) t) (quasispectrum ℝ A) :=
    (Real.continuousOn_rpowIntegrand₀₁_Ici hq_real ht).mono hqs
  have hG_mul :
      cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) A
        =
        cfcₙ (fun x : ℝ ↦ x) A * cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A := by
    simpa using
      (cfcₙ_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (f := fun x : ℝ ↦ x) (g := Real.rpowIntegrand₀₁ (q : ℝ) t) (a := A)
        (hf := continuousOn_id) (hf0 := by simp) (hg := hg) (hg0 := by simp))
  have hA_id : cfcₙ (fun x : ℝ ↦ x) A = A := by
    simpa using (cfcₙ_id' (R := ℝ) (a := A) (ha := IsSelfAdjoint.of_nonneg hA0))
  simp [hA_id, hG_mul]

/-! ### Convexity of powers between one and two -/

private lemma convexOn_nnrpow_Ioo_one_add {q : NNReal} (hq : q ∈ Set.Ioo (0 : NNReal) 1) :
    ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ A ^ ((1 : NNReal) + q)) := by
  -- real exponent in `(0,1)`
  have hq_real : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨(NNReal.coe_pos).2 hq.1, (NNReal.coe_lt_coe).2 hq.2⟩
  -- integral representation for `a ↦ a ^ q`
  obtain ⟨μ, hμ⟩ :=
    CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ (A := 𝓐) hq
  let ν : MeasureTheory.Measure ℝ := μ.restrict (Set.Ioi (0 : ℝ))
  let F0 : ℝ → 𝓐 → 𝓐 := fun t A => cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A
  let G : ℝ → 𝓐 → 𝓐 := fun t A =>
    cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) A
  have hF0_int : ∀ A ∈ Set.Ici (0 : 𝓐), MeasureTheory.Integrable (fun t => F0 t A) ν := by
    intro A hA
    simpa [F0, ν, MeasureTheory.IntegrableOn] using (hμ A hA).1
  have hG_int : ∀ A ∈ Set.Ici (0 : 𝓐), MeasureTheory.Integrable (fun t => G t A) ν := by
    intro A hA
    have hA0 : 0 ≤ A := by simpa [Set.Ici] using hA
    have hAF : MeasureTheory.Integrable (fun t => A * F0 t A) ν := by
      -- left multiplication by a constant is a continuous linear map
      have hF : MeasureTheory.Integrable (fun t => F0 t A) ν := hF0_int A hA
      simpa [ContinuousLinearMap.mul_apply'] using
        (ContinuousLinearMap.mul ℝ (𝓐) A).integrable_comp hF
    have hG_mul_ae : ∀ᵐ t ∂ν, G t A = A * F0 t A := by
      simpa [ν, G, F0] using
        ae_cfcₙ_mul_id_rpowIntegrand₀₁_restrict_Ioi  (q := q) hq_real μ A hA0
    exact hAF.congr (hG_mul_ae.mono fun _ ht => ht.symm)
  have hG_conv :
      ∀ᵐ t ∂ν, ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 => G t A) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hconv :
        ConvexOn ℝ (Set.Ici (0 : 𝓐))
          (fun X : 𝓐 ↦ cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X) :=
      convexOn_G_rpowIntegrand₀₁_mul  hq_real t ht
    simpa [G] using hconv
  have hconv_int :
      ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ ∫ t, G t A ∂ν) :=
    MeasureTheory.integral_convexOn_of_integrand_ae
      (μ := ν) (s := Set.Ici (0 : 𝓐)) (f := fun t A => G t A)
      (convex_Ici (𝕜 := ℝ) (0 : 𝓐)) hG_conv hG_int
  -- identify the integral with `A ^ (1 + q)` on `Ici 0`
  refine hconv_int.congr ?_
  intro A hA
  have hA0 : 0 ≤ A := by simpa [Set.Ici] using hA
  have hq0 : (0 : NNReal) < q := hq.1
  have hpow :
      A ^ ((1 : NNReal) + q) = A * (A ^ q) := by
    have h1 : A ^ ((1 : NNReal) + q) = A ^ (1 : NNReal) * A ^ q := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (CFC.nnrpow_add (A := 𝓐) (a := A) (x := (1 : NNReal)) (y := q) zero_lt_one hq0)
    simpa [CFC.nnrpow_one (A := 𝓐) A hA0] using h1
  have hEq_q : A ^ q = ∫ t, F0 t A ∂ν := by
    simpa [F0, ν] using (hμ A hA).2
  have hEq_mul :
      A * (∫ t, F0 t A ∂ν) = ∫ t, A * F0 t A ∂ν := by
    have h :
        (∫ t, (ContinuousLinearMap.mul ℝ (𝓐) A) (F0 t A) ∂ν)
          =
          (ContinuousLinearMap.mul ℝ (𝓐) A) (∫ t, F0 t A ∂ν) :=
      (ContinuousLinearMap.mul ℝ (𝓐) A).integral_comp_comm (μ := ν) (φ_int := hF0_int A hA)
    exact h.symm
  have hEq :
      A ^ ((1 : NNReal) + q) = ∫ t, G t A ∂ν := by
    calc
      A ^ ((1 : NNReal) + q) = A * (A ^ q) := hpow
      _ = A * (∫ t, F0 t A ∂ν) := by simp [hEq_q]
      _ = ∫ t, A * F0 t A ∂ν := hEq_mul
      _ = ∫ t, G t A ∂ν := by
        have hG_mul_ae : ∀ᵐ t ∂ν, A * F0 t A = G t A := by
          have h' : ∀ᵐ t ∂ν, G t A = A * F0 t A := by
            simpa [ν, G, F0] using
              ae_cfcₙ_mul_id_rpowIntegrand₀₁_restrict_Ioi  (q := q) hq_real μ A hA0
          exact h'.mono (fun _ ht => ht.symm)
        simpa using (MeasureTheory.integral_congr_ae hG_mul_ae)
  simp [hEq]

private lemma convexOn_rpow_Ioo_one_two {p : ℝ} (hp : p ∈ Set.Ioo (1 : ℝ) 2) :
    ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ A ^ p) := by
  -- reduce to the `ℝ≥0` exponent case with `p = 1 + q`, `q ∈ (0,1)`
  let q : NNReal := ⟨p - 1, sub_nonneg.mpr (le_of_lt hp.1)⟩
  have hq0 : (0 : NNReal) < q := by
    have : (0 : ℝ) < (q : ℝ) := by
      simpa [q] using (sub_pos.mpr hp.1)
    exact (NNReal.coe_pos).1 this
  have hq1 : q < (1 : NNReal) := by
    have : (q : ℝ) < (1 : ℝ) := by
      have : p - 1 < (1 : ℝ) := by linarith [hp.2]
      simpa [q] using this
    exact (NNReal.coe_lt_coe).1 (by simpa using this)
  have hq : q ∈ Set.Ioo (0 : NNReal) 1 := ⟨hq0, hq1⟩
  have hconv :
      ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ A ^ ((1 : NNReal) + q)) :=
    convexOn_nnrpow_Ioo_one_add  hq
  refine hconv.congr ?_
  intro A hA
  have hA0 : 0 ≤ A := by simpa [Set.Ici] using hA
  have hq0' : (0 : NNReal) < (1 : NNReal) + q :=
    add_pos_of_pos_of_nonneg zero_lt_one (le_of_lt hq0)
  -- `A ^ (1 + q) = A ^ p`
  have hEq :
      A ^ ((1 : NNReal) + q) = A ^ (((1 : NNReal) + q : NNReal) : ℝ) := by
    simpa using (CFC.nnrpow_eq_rpow (A := 𝓐) (a := A) (x := (1 : NNReal) + q) hq0')
  -- simplify the real exponent `(1 + q : ℝ)` into `p`
  have hreal : (((1 : NNReal) + q : NNReal) : ℝ) = p := by
    have : (1 : ℝ) + (p - 1) = p := by ring
    simp [q, this]
  simp [hEq, hreal]

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
private lemma cfcR_mul_self (T : 𝓐) (hT : IsSelfAdjoint T) :
    cfcR (fun x : ℝ ↦ x * x) T = T * T := by
  dsimp [cfcR]
  calc
    cfcR (fun x : ℝ ↦ x * x) T =
        cfcR (fun x : ℝ ↦ x) T * cfcR (fun x : ℝ ↦ x) T := by
      simpa using
        (cfc_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
          (f := fun x : ℝ ↦ x) (g := fun x : ℝ ↦ x) (a := T))
    _ = T * T := by
      simp [cfc_id' (R := ℝ) (a := T) (ha := hT)]

-- This lemma is purely algebraic, so we drop analytical/finite-dimensional assumptions here.
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] [Nontrivial (𝓐)] in
private lemma square_convexity_diff (A B : 𝓐) (u : ℝ) :
    (1 - u) • (A * A) + u • (B * B)
        - ((1 - u) • A + u • B) * ((1 - u) • A + u • B)
      =
      (u * (1 - u)) • ((A - B) * (A - B)) := by
  simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
  module

omit [Nontrivial (𝓐)] [NonnegSpectrumClass ℝ 𝓐] in
private lemma operatorConvexOn_pow_two_Ici :
    OperatorConvexOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x ^ (2 : ℝ)) := by
  dsimp [OperatorConvexOn]
  intro A B u hA hB hu0 hu1 As Bs
  have hA0 : 0 ≤ A := nonneg_of_spectrum_subset_Ici hA As
  have hB0 : 0 ≤ B := nonneg_of_spectrum_subset_Ici hB Bs
  have hu0' : 0 ≤ (1 - u) := sub_nonneg.mpr hu1
  set C : 𝓐 := (1 - u) • A + u • B
  have hC0 : 0 ≤ C :=
    add_nonneg (smul_nonneg hu0' hA0) (smul_nonneg hu0 hB0)
  have hsq : 0 ≤ (A - B) * (A - B) := by
    have hT : IsSelfAdjoint (A - B) := hA.sub hB
    simpa [mul_assoc] using hT.conjugate_nonneg (zero_le_one : (0 : 𝓐) ≤ 1)
  have hub : 0 ≤ u * (1 - u) := mul_nonneg hu0 hu0'
  have hdiff :
      (1 - u) • (A * A) + u • (B * B) - C * C
        = (u * (1 - u)) • ((A - B) * (A - B)) := by
    simpa [C] using (square_convexity_diff  A B u)
  have hnonneg : 0 ≤ (1 - u) • (A * A) + u • (B * B) - C * C := by
    have hscale : 0 ≤ (u * (1 - u)) • ((A - B) * (A - B)) := smul_nonneg hub hsq
    simpa [hdiff] using hscale
  have hmain : C * C ≤ (1 - u) • (A * A) + u • (B * B) :=
    (sub_nonneg).1 hnonneg
  have hC : IsSelfAdjoint C := by simpa [C] using isSelfAdjoint_convexCombo u hA hB
  -- rewrite the goal via `cfcR (x ↦ x^2) T = T*T`
  have hfun : (fun x : ℝ ↦ x ^ (2 : ℝ)) = (fun x : ℝ ↦ x * x) := by
    funext x
    simp [pow_two]
  rw [hfun]
  simpa [C, cfcR_mul_self  C hC, cfcR_mul_self  A hA, cfcR_mul_self  B hB] using hmain

/-- `x ↦ x ^ p` is operator convex on `[0, ∞)` for `p ∈ [1, 2]`.

Source: arXiv:2607.05492v1, §3.
Source: Eric Carlen, "Trace Inequalities and Quantum Entropy: An Introductory Course",
Contemporary Mathematics 529 (2010), 73–140, Theorem 2.6 / Lemma 2.8 / Lemma 2.7.
Correspondence restricted to the exponent range and domain of this declaration. -/
/- Convexity of powers between one and two (Carlen 2009, Theorem 2.6, third clause; proof
    using Lemma 2.8, formula (2.7)): for 1 ≤ p ≤ 2, the function t ↦ t^p is operator convex.
    Lean deviation: stated as operator convexity of x ↦ x^p on [0, ∞) in the sense of
    `OperatorConvexOn`, over a unital C*-algebra rather than matrices. -/
/- Proof (Carlen 2009, proof of Theorem 2.6): for 1 < p < 2, Lemma 2.8 gives the integral
    formula (2.7) with integrand A ↦ A/t + t/(t + A) − I. By Lemma 2.7, in the shifted
    reciprocal form (`one_div_add_t_operatorConvexOn_Ici`), this is a sum of operator-convex
    functions, hence operator convex; it is only a difference of operator-monotone functions,
    so no monotonicity is claimed. Positive weighted sums then give operator convexity of A^p,
    with endpoint cases treated separately.
    Lean deviation: the formal proof handles the endpoints p = 1 (identity) and p = 2 (square
    convexity, `operatorConvexOn_pow_two_Ici`) directly. For 1 < p < 2 it reduces to the local
    lemma `convexOn_rpow_Ioo_one_two` of this file (not a Mathlib theorem): writing p = 1 + q
    with 0 < q < 1, it uses the continuous-functional-calculus integral representation of A^q
    and rewrites the integrand into an affine term plus a positive multiple of the shifted
    reciprocal x ↦ 1/(x + t), whose operator convexity is `one_div_add_t_operatorConvexOn_Ici`.
    This formalizes Carlen's integral formula (2.7) rather than avoiding it. -/
theorem power_Icc_one_two_operatorConvexOn_Ici (p : ℝ) (hp : p ∈ Set.Icc (1 : ℝ) 2) :
    OperatorConvexOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  by_cases hp1 : p = 1
  · subst hp1
    dsimp [OperatorConvexOn]
    intro A B u hA hB hu0 hu1 As Bs
    have hC : IsSelfAdjoint ((1 - u) • A + u • B) := isSelfAdjoint_convexCombo u hA hB
    have hfun : (fun x : ℝ ↦ x ^ (1 : ℝ)) = (fun x : ℝ ↦ x) := by
      funext x
      simp
    rw [hfun]
    simp [cfcR, cfc_id' (R := ℝ) (a := ((1 - u) • A + u • B)) (ha := hC),
      cfc_id' (R := ℝ) (a := A) (ha := hA), cfc_id' (R := ℝ) (a := B) (ha := hB)]
  by_cases hp2 : p = 2
  · subst hp2
    simpa using operatorConvexOn_pow_two_Ici
  have hp12 : p ∈ Set.Ioo (1 : ℝ) 2 := ⟨hp.1.lt_of_ne' hp1, hp.2.lt_of_ne hp2⟩
  dsimp [OperatorConvexOn]
  intro A B u hA hB hu0 hu1 As Bs
  have hA0 : 0 ≤ A := nonneg_of_spectrum_subset_Ici hA As
  have hB0 : 0 ≤ B := nonneg_of_spectrum_subset_Ici hB Bs
  have hu0' : 0 ≤ (1 - u) := sub_nonneg.mpr hu1
  set C : 𝓐 := (1 - u) • A + u • B
  have hC0 : 0 ≤ C :=
    add_nonneg (smul_nonneg hu0' hA0) (smul_nonneg hu0 hB0)
  have hC_mem : C ∈ Set.Ici (0 : 𝓐) := by
    simpa [C, Set.Ici] using hC0
  have hA_mem : A ∈ Set.Ici (0 : 𝓐) := by simpa [Set.Ici] using hA0
  have hB_mem : B ∈ Set.Ici (0 : 𝓐) := by simpa [Set.Ici] using hB0
  have hab : (1 - u) + u = (1 : ℝ) := by ring
  have hconvC : (C ^ p) ≤ (1 - u) • (A ^ p) + u • (B ^ p) := by
    simpa [C] using
      (convexOn_rpow_Ioo_one_two  hp12).2 hA_mem hB_mem hu0' hu0 hab
  have hcalc (T : 𝓐) (hT0 : 0 ≤ T) :
      cfcR (fun x : ℝ ↦ x ^ p) T = T ^ p := by
    simpa [cfcR] using
      (CFC.rpow_eq_cfc_real (A := 𝓐) (a := T) (y := p) (ha := hT0)).symm
  -- rewrite the convexity inequality through `cfcR`
  simpa [hcalc A hA0, hcalc B hB0, hcalc C hC0, C] using hconvC

end Spectrum

end LownerHeinzCore
