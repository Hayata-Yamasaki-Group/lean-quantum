/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.JensenOperatorInequality

/-!
# Generalized operator perspectives

The generalized perspective combines continuous functional calculus with conjugation
by a positive square root. This module establishes its joint convexity and concavity
on the positive cones under the corresponding hypotheses on the scalar functions.
-/

namespace GeneralizedPerspectiveFunction

universe u

open LownerHeinzTheorem
open JensenOperatorInequality

section Convexity

variable {E F G : Type*}
variable [AddCommMonoid E] [Module ℝ E]
variable [AddCommMonoid F] [Module ℝ F]
variable [Preorder G] [AddCommMonoid G] [Module ℝ G]

/-- Joint convexity of a two-variable map on prescribed domains in each argument. -/
def JointlyConvexOn (s : Set E) (t : Set F) (Φ : E → F → G) : Prop :=
  ∀ ⦃A₁ A₂ : E⦄ ⦃B₁ B₂ : F⦄ ⦃θ : ℝ⦄,
    A₁ ∈ s → A₂ ∈ s → B₁ ∈ t → B₂ ∈ t →
    0 ≤ θ → θ ≤ 1 →
    Φ ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂)
      ≤ (1 - θ) • Φ A₁ B₁ + θ • Φ A₂ B₂

/-- Joint convexity of a two-variable map without domain restrictions. -/
def JointlyConvex (Φ : E → F → G) : Prop :=
  JointlyConvexOn (Set.univ : Set E) (Set.univ : Set F) Φ

/-- Joint concavity of a two-variable map on prescribed domains in each argument. -/
def JointlyConcaveOn (s : Set E) (t : Set F) (Φ : E → F → G) : Prop :=
  ∀ ⦃A₁ A₂ : E⦄ ⦃B₁ B₂ : F⦄ ⦃θ : ℝ⦄,
    A₁ ∈ s → A₂ ∈ s → B₁ ∈ t → B₂ ∈ t →
    0 ≤ θ → θ ≤ 1 →
    (1 - θ) • Φ A₁ B₁ + θ • Φ A₂ B₂
      ≤ Φ ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂)

/-- Joint concavity of a two-variable map without domain restrictions. -/
def JointlyConcave (Φ : E → F → G) : Prop :=
  JointlyConcaveOn (Set.univ : Set E) (Set.univ : Set F) Φ

end Convexity

section Definition

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

/-- The operator `h(B)^(1/2)` defined by real continuous functional calculus. -/
noncomputable def hSqrt (h : ℝ → ℝ) (B : QuantumState.B ℋ) : QuantumState.B ℋ :=
  cfcR (fun x : ℝ ↦ (h x) ^ ((1 : ℝ) / 2)) B

/-- The operator `h(B)^(-1/2)` defined by real continuous functional calculus. -/
noncomputable def hInvSqrt (h : ℝ → ℝ) (B : QuantumState.B ℋ) : QuantumState.B ℋ :=
  cfcR (fun x : ℝ ↦ (h x) ^ ((-1 : ℝ) / 2)) B

/--
The generalized perspective function
`(fΔh)(A, B) = h(B)^(1/2) f(h(B)^(-1/2) A h(B)^(-1/2)) h(B)^(1/2)`.

This definition is intended to be used when `A` is Hermitian and `h(B)` is positive/invertible.

Source: A. Ebadian, I. Nikoufar, M. Eshaghi Gordji, "Perspectives of matrix convex functions",
PNAS 108(18) (2011), 7313--7314, Page 1, DOI 10.1073/pnas.1102518108. Defined everywhere via CFC;
positivity and invertibility are assumed in subsequent theorems.
-/
noncomputable def generalizedPerspective (f h : ℝ → ℝ) (A B : QuantumState.B ℋ)
    : QuantumState.B ℋ :=
  hSqrt h B * cfcR f (hInvSqrt h B * A * hInvSqrt h B) * hSqrt h B

/-- Infix notation for generalized perspective: `(f Δ h) A B = generalizedPerspective f h A B`. -/
scoped infixl:70 " Δ " => generalizedPerspective

end Definition

section Theorem25Forward

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

/-- Positive semidefinite operators. -/
def psdSet : Set (QuantumState.B ℋ) :=
  {A | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ Set.Ici (0 : ℝ)}

/-- Strictly positive operators. -/
def pdSet : Set (QuantumState.B ℋ) :=
  {A | IsSelfAdjoint A ∧ spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)}

omit [Nontrivial ℋ] in
private lemma cfcR_sq_eq {g k : ℝ → ℝ} {A : (ℋ →L[ℂ] ℋ)}
    (hA : IsSelfAdjoint A)
    (hg : ContinuousOn g (spectrum ℝ A))
    (hk : ContinuousOn k (spectrum ℝ A))
    (hmul : ∀ x ∈ spectrum ℝ A, g x * k x = 1) :
    cfcR (ℋ := ℋ) g A * cfcR (ℋ := ℋ) k A = (1 : (ℋ →L[ℂ] ℋ)) := by
  rw [← cfc_mul (R := ℝ) (A := (ℋ →L[ℂ] ℋ)) (p := IsSelfAdjoint)
      (f := g) (g := k) (a := A) hg hk, ← cfc_const_one ℝ A]
  apply cfc_congr
  intro x hx
  simpa using hmul x hx

omit [Nontrivial ℋ] in
private lemma cfcR_mul_eq {g k m : ℝ → ℝ} {A : (ℋ →L[ℂ] ℋ)}
    (hg : ContinuousOn g (spectrum ℝ A))
    (hk : ContinuousOn k (spectrum ℝ A))
    (hmul : ∀ x ∈ spectrum ℝ A, g x * k x = m x) :
    cfcR (ℋ := ℋ) g A * cfcR (ℋ := ℋ) k A = cfcR (ℋ := ℋ) m A := by
  rw [← cfc_mul (R := ℝ) (A := (ℋ →L[ℂ] ℋ)) (p := IsSelfAdjoint)
      (f := g) (g := k) (a := A) hg hk]
  apply cfc_congr
  intro x hx
  simpa using hmul x hx

private lemma hpow_continuousOn
    (h : ℝ → ℝ) (p : ℝ)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    ContinuousOn (fun x : ℝ ↦ (h x) ^ p) (Set.Ioi (0 : ℝ)) := by
  intro x hx
  have hg : ContinuousWithinAt (fun y : ℝ ↦ y ^ p) (Set.Ioi (0 : ℝ)) (h x) :=
    (Real.continuousAt_rpow_const (h x) p (Or.inl (ne_of_gt (hpos x hx)))).continuousWithinAt
  exact hg.comp (hcont x hx) (by
    intro y hy
    exact hpos y hy)

omit [Nontrivial ℋ] in
private lemma hSqrt_selfAdjoint (h : ℝ → ℝ) (B : (ℋ →L[ℂ] ℋ)) :
    IsSelfAdjoint (hSqrt (ℋ := ℋ) h B) := by
  dsimp [hSqrt, cfcR]
  exact cfc_predicate _ _

omit [Nontrivial ℋ] in
private lemma hInvSqrt_selfAdjoint (h : ℝ → ℝ) (B : (ℋ →L[ℂ] ℋ)) :
    IsSelfAdjoint (hInvSqrt (ℋ := ℋ) h B) := by
  dsimp [hInvSqrt, cfcR]
  exact cfc_predicate _ _

omit [Nontrivial ℋ] in
private lemma hSqrt_mul_hInvSqrt_eq_one
    {h : ℝ → ℝ} {B : (ℋ →L[ℂ] ℋ)}
    (hB : IsSelfAdjoint B) (Bs : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ))
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    hSqrt (ℋ := ℋ) h B * hInvSqrt (ℋ := ℋ) h B = (1 : (ℋ →L[ℂ] ℋ)) := by
  have hsqrt :
      ContinuousOn (fun x : ℝ ↦ (h x) ^ ((1 : ℝ) / 2)) (spectrum ℝ B) :=
    (hpow_continuousOn h ((1 : ℝ) / 2) hcont hpos).mono (by intro x hx; exact Bs hx)
  have hinv :
      ContinuousOn (fun x : ℝ ↦ (h x) ^ ((-1 : ℝ) / 2)) (spectrum ℝ B) :=
    (hpow_continuousOn h ((-1 : ℝ) / 2) hcont hpos).mono (by intro x hx; exact Bs hx)
  have hmul :
      ∀ x ∈ spectrum ℝ B,
        (h x) ^ ((1 : ℝ) / 2) * (h x) ^ ((-1 : ℝ) / 2) = 1 := by
    intro x hx
    have hxpos : 0 < h x := hpos x (Bs hx)
    rw [← Real.rpow_add hxpos]
    norm_num
  simpa [hSqrt, hInvSqrt] using cfcR_sq_eq (ℋ := ℋ) (A := B) hB hsqrt hinv hmul

omit [Nontrivial ℋ] in
private lemma hInvSqrt_mul_hSqrt_eq_one
    {h : ℝ → ℝ} {B : (ℋ →L[ℂ] ℋ)}
    (hB : IsSelfAdjoint B) (Bs : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ))
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    hInvSqrt (ℋ := ℋ) h B * hSqrt (ℋ := ℋ) h B = (1 : (ℋ →L[ℂ] ℋ)) := by
  have hsqrt :
      ContinuousOn (fun x : ℝ ↦ (h x) ^ ((1 : ℝ) / 2)) (spectrum ℝ B) :=
    (hpow_continuousOn h ((1 : ℝ) / 2) hcont hpos).mono (by intro x hx; exact Bs hx)
  have hinv :
      ContinuousOn (fun x : ℝ ↦ (h x) ^ ((-1 : ℝ) / 2)) (spectrum ℝ B) :=
    (hpow_continuousOn h ((-1 : ℝ) / 2) hcont hpos).mono (by intro x hx; exact Bs hx)
  have hmul :
      ∀ x ∈ spectrum ℝ B,
        (h x) ^ ((-1 : ℝ) / 2) * (h x) ^ ((1 : ℝ) / 2) = 1 := by
    intro x hx
    have hxpos : 0 < h x := hpos x (Bs hx)
    rw [← Real.rpow_add hxpos]
    norm_num
  simpa [hSqrt, hInvSqrt] using cfcR_sq_eq (ℋ := ℋ) (A := B) hB hinv hsqrt hmul

omit [Nontrivial ℋ] in
private lemma hSqrt_mul_hSqrt_eq
    {h : ℝ → ℝ} {B : (ℋ →L[ℂ] ℋ)}
    (Bs : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ))
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    hSqrt (ℋ := ℋ) h B * hSqrt (ℋ := ℋ) h B = cfcR (ℋ := ℋ) h B := by
  have hsqrt :
      ContinuousOn (fun x : ℝ ↦ (h x) ^ ((1 : ℝ) / 2)) (spectrum ℝ B) :=
    (hpow_continuousOn h ((1 : ℝ) / 2) hcont hpos).mono (by intro x hx; exact Bs hx)
  have hmul :
      ∀ x ∈ spectrum ℝ B,
        (h x) ^ ((1 : ℝ) / 2) * (h x) ^ ((1 : ℝ) / 2) = h x := by
    intro x hx
    have hxpos : 0 < h x := hpos x (Bs hx)
    rw [← Real.rpow_add hxpos]
    norm_num
  simpa [hSqrt] using cfcR_mul_eq (ℋ := ℋ) (A := B) hsqrt hsqrt hmul

omit [Nontrivial ℋ] in
private lemma conj_le_conj {X Y T : (ℋ →L[ℂ] ℋ)} (hXY : X ≤ Y) (hT : IsSelfAdjoint T) :
    T * X * T ≤ T * Y * T := by
  have hnonneg : 0 ≤ Y - X := sub_nonneg.mpr hXY
  have hconj : 0 ≤ T * (Y - X) * T := by
    simpa using hT.conjugate_nonneg hnonneg
  have hsub : T * (Y - X) * T = T * Y * T - T * X * T := by
    simp [sub_eq_add_neg, mul_add, add_mul, mul_assoc]
  exact sub_nonneg.mp (by simpa [hsub] using hconj)

section CondVCore
-- The normalization proof below expands several nested CFC products, and every tactic
-- step re-derives the real-scalar structure of `L ℋ` (obtained from the complex one by
-- restriction of scalars) from scratch: the searches for derived classes such as
-- `NonnegSpectrumClass ℝ (ℋ →L[ℂ] ℋ)`, `StarModule ℝ (ℋ →L[ℂ] ℋ)`,
-- `PosSMulMono ℝ (ℋ →L[ℂ] ℋ)` all
-- repeatedly re-solve the `Module ℝ (ℋ →L[ℂ] ℋ)` / `Algebra ℝ (ℋ →L[ℂ] ℋ)`
-- subgoals, which are not
-- cached across tactic steps and cost hundreds of milliseconds per occurrence.  Caching
-- the two root instances at section level keeps the declaration within the default
-- heartbeat budget.
noncomputable local instance : Module ℝ (ℋ →L[ℂ] ℋ) := inferInstance
noncomputable local instance : Algebra ℝ (ℋ →L[ℂ] ℋ) := inferInstance

private theorem jointlyConvexOn_generalizedPerspective_psdSet_pdSet_of_jensenColumn
    {f h : ℝ → ℝ}
    (hcoreV : JensenContractiveColumnCondition (ℋ := ℋ) f)
    (hconc : OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) h)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    JointlyConvexOn (psdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ)) (fun A B ↦ (f Δ h) A B) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  rcases hA₁ with ⟨hA₁_sa, hA₁_spec⟩
  rcases hA₂ with ⟨hA₂_sa, hA₂_spec⟩
  rcases hB₁ with ⟨hB₁_sa, hB₁_spec⟩
  rcases hB₂ with ⟨hB₂_sa, hB₂_spec⟩
  let A : (ℋ →L[ℂ] ℋ) := (1 - θ) • A₁ + θ • A₂
  let B : (ℋ →L[ℂ] ℋ) := (1 - θ) • B₁ + θ • B₂
  have hA₁_nonneg : (0 : (ℋ →L[ℂ] ℋ)) ≤ A₁ := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A₁ (ha := hA₁_sa)).2 ?_
    intro x hx
    simpa [Set.Ici] using hA₁_spec hx
  have hA₂_nonneg : (0 : (ℋ →L[ℂ] ℋ)) ≤ A₂ := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A₂ (ha := hA₂_sa)).2 ?_
    intro x hx
    simpa [Set.Ici] using hA₂_spec hx
  have hB_sa : IsSelfAdjoint B := by
    dsimp [B]
    simpa using (IsSelfAdjoint.all (1 - θ)).smul hB₁_sa |>.add ((IsSelfAdjoint.all θ).smul hB₂_sa)
  have hB_spec : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ) :=
    LownerHeinzCore.spectrum_convexCombo_Ioi (𝓐 := (ℋ →L[ℂ] ℋ))
      hB₁_sa hB₂_sa hθ0 hθ1 hB₁_spec hB₂_spec
  have hB_conc :
      (1 - θ) • cfcR (ℋ := ℋ) h B₁ + θ • cfcR (ℋ := ℋ) h B₂ ≤ cfcR (ℋ := ℋ) h B := by
    have hconc' := hconc
    dsimp [OperatorConcaveOn, OperatorConvexOn] at hconc'
    have hneg :
        cfcR (ℋ := ℋ) (fun x : ℝ ↦ -h x) B ≤
          (1 - θ) • cfcR (ℋ := ℋ) (fun x : ℝ ↦ -h x) B₁ +
            θ • cfcR (ℋ := ℋ) (fun x : ℝ ↦ -h x) B₂ := by
      simpa [B] using
        hconc' (A := B₁) (B := B₂) (t := θ) hB₁_sa hB₂_sa hθ0 hθ1 hB₁_spec hB₂_spec
    simpa [cfcR, cfc_neg, smul_neg, neg_add, add_comm, add_left_comm, add_assoc] using
      neg_le_neg hneg
  let S : (ℋ →L[ℂ] ℋ) := hSqrt (ℋ := ℋ) h B
  let IR : (ℋ →L[ℂ] ℋ) := hInvSqrt (ℋ := ℋ) h B
  let S₁ : (ℋ →L[ℂ] ℋ) := hSqrt (ℋ := ℋ) h B₁
  let S₂ : (ℋ →L[ℂ] ℋ) := hSqrt (ℋ := ℋ) h B₂
  let IR₁ : (ℋ →L[ℂ] ℋ) := hInvSqrt (ℋ := ℋ) h B₁
  let IR₂ : (ℋ →L[ℂ] ℋ) := hInvSqrt (ℋ := ℋ) h B₂
  let T₁ : (ℋ →L[ℂ] ℋ) := Real.sqrt (1 - θ) • (S₁ * IR)
  let T₂ : (ℋ →L[ℂ] ℋ) := Real.sqrt θ • (S₂ * IR)
  let M₁ : (ℋ →L[ℂ] ℋ) := IR₁ * A₁ * IR₁
  let M₂ : (ℋ →L[ℂ] ℋ) := IR₂ * A₂ * IR₂
  have hS_sa : IsSelfAdjoint S := hSqrt_selfAdjoint (ℋ := ℋ) h B
  have hIR_sa : IsSelfAdjoint IR := hInvSqrt_selfAdjoint (ℋ := ℋ) h B
  have hS₁_sa : IsSelfAdjoint S₁ := hSqrt_selfAdjoint (ℋ := ℋ) h B₁
  have hS₂_sa : IsSelfAdjoint S₂ := hSqrt_selfAdjoint (ℋ := ℋ) h B₂
  have hIR₁_sa : IsSelfAdjoint IR₁ := hInvSqrt_selfAdjoint (ℋ := ℋ) h B₁
  have hIR₂_sa : IsSelfAdjoint IR₂ := hInvSqrt_selfAdjoint (ℋ := ℋ) h B₂
  have hSIR : S * IR = (1 : (ℋ →L[ℂ] ℋ)) :=
    hSqrt_mul_hInvSqrt_eq_one (ℋ := ℋ) hB_sa hB_spec hcont hpos
  have hIRS : IR * S = (1 : (ℋ →L[ℂ] ℋ)) :=
    hInvSqrt_mul_hSqrt_eq_one (ℋ := ℋ) hB_sa hB_spec hcont hpos
  have hS₁IR₁ : S₁ * IR₁ = (1 : (ℋ →L[ℂ] ℋ)) :=
    hSqrt_mul_hInvSqrt_eq_one (ℋ := ℋ) hB₁_sa hB₁_spec hcont hpos
  have hIR₁S₁ : IR₁ * S₁ = (1 : (ℋ →L[ℂ] ℋ)) :=
    hInvSqrt_mul_hSqrt_eq_one (ℋ := ℋ) hB₁_sa hB₁_spec hcont hpos
  have hS₂IR₂ : S₂ * IR₂ = (1 : (ℋ →L[ℂ] ℋ)) :=
    hSqrt_mul_hInvSqrt_eq_one (ℋ := ℋ) hB₂_sa hB₂_spec hcont hpos
  have hIR₂S₂ : IR₂ * S₂ = (1 : (ℋ →L[ℂ] ℋ)) :=
    hInvSqrt_mul_hSqrt_eq_one (ℋ := ℋ) hB₂_sa hB₂_spec hcont hpos
  have hM₁_nonneg : (0 : (ℋ →L[ℂ] ℋ)) ≤ M₁ := by
    dsimp [M₁]
    simpa [mul_assoc] using hIR₁_sa.conjugate_nonneg hA₁_nonneg
  have hM₂_nonneg : (0 : (ℋ →L[ℂ] ℋ)) ≤ M₂ := by
    dsimp [M₂]
    simpa [mul_assoc] using hIR₂_sa.conjugate_nonneg hA₂_nonneg
  have hM₁_sa : IsSelfAdjoint M₁ := IsSelfAdjoint.of_nonneg hM₁_nonneg
  have hM₂_sa : IsSelfAdjoint M₂ := IsSelfAdjoint.of_nonneg hM₂_nonneg
  have hM₁_spec : spectrum ℝ M₁ ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    simpa [Set.Ici] using spectrum_nonneg_of_nonneg hM₁_nonneg hx
  have hM₂_spec : spectrum ℝ M₂ ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    simpa [Set.Ici] using spectrum_nonneg_of_nonneg hM₂_nonneg hx
  have hT₁ :
      star T₁ * T₁ = (1 - θ) • (IR * cfcR (ℋ := ℋ) h B₁ * IR) := by
    calc
      star T₁ * T₁
          = (Real.sqrt (1 - θ) * Real.sqrt (1 - θ)) • (IR * (S₁ * S₁) * IR) := by
              simp [T₁, hS₁_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
      _ = (1 - θ) • (IR * (S₁ * S₁) * IR) := by
              rw [Real.mul_self_sqrt (sub_nonneg.mpr hθ1)]
      _ = (1 - θ) • (IR * cfcR (ℋ := ℋ) h B₁ * IR) := by
              rw [hSqrt_mul_hSqrt_eq (ℋ := ℋ) (B := B₁) hB₁_spec hcont hpos]
  have hT₂ :
      star T₂ * T₂ = θ • (IR * cfcR (ℋ := ℋ) h B₂ * IR) := by
    calc
      star T₂ * T₂
          = (Real.sqrt θ * Real.sqrt θ) • (IR * (S₂ * S₂) * IR) := by
              simp [T₂, hS₂_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
      _ = θ • (IR * (S₂ * S₂) * IR) := by
              rw [Real.mul_self_sqrt hθ0]
      _ = θ • (IR * cfcR (ℋ := ℋ) h B₂ * IR) := by
              rw [hSqrt_mul_hSqrt_eq (ℋ := ℋ) (B := B₂) hB₂_spec hcont hpos]
  have hTsum : star T₁ * T₁ + star T₂ * T₂ ≤ (1 : (ℋ →L[ℂ] ℋ)) := by
    rw [hT₁, hT₂]
    have hmid :
        (1 - θ) • (IR * cfcR (ℋ := ℋ) h B₁ * IR) + θ • (IR * cfcR (ℋ := ℋ) h B₂ * IR)
          ≤ IR * cfcR (ℋ := ℋ) h B * IR := by
      calc
        (1 - θ) • (IR * cfcR (ℋ := ℋ) h B₁ * IR) + θ • (IR * cfcR (ℋ := ℋ) h B₂ * IR)
            = IR * ((1 - θ) • cfcR (ℋ := ℋ) h B₁ + θ • cfcR (ℋ := ℋ) h B₂) * IR := by
                simp [mul_add, add_mul, mul_assoc]
        _ ≤ IR * cfcR (ℋ := ℋ) h B * IR := conj_le_conj (ℋ := ℋ) hB_conc hIR_sa
    have hunit : IR * cfcR (ℋ := ℋ) h B * IR = (1 : (ℋ →L[ℂ] ℋ)) := by
      calc
        IR * cfcR (ℋ := ℋ) h B * IR = IR * (S * S) * IR := by
          rw [hSqrt_mul_hSqrt_eq (ℋ := ℋ) (B := B) hB_spec hcont hpos]
        _ = (IR * S) * (S * IR) := by simp [mul_assoc]
        _ = 1 := by simp [hIRS, hSIR]
    exact hmid.trans_eq hunit
  have hterm₁ :
      star T₁ * M₁ * T₁ = (1 - θ) • (IR * A₁ * IR) := by
    calc
      star T₁ * M₁ * T₁
          = (Real.sqrt (1 - θ) * Real.sqrt (1 - θ)) •
              (IR * (S₁ * (IR₁ * A₁ * IR₁) * S₁) * IR) := by
                simp [T₁, M₁, hS₁_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
      _ = (1 - θ) • (IR * (S₁ * (IR₁ * A₁ * IR₁) * S₁) * IR) := by
            rw [Real.mul_self_sqrt (sub_nonneg.mpr hθ1)]
      _ = (1 - θ) • (IR * A₁ * IR) := by
            rw [show IR * (S₁ * (IR₁ * A₁ * IR₁) * S₁) * IR =
                IR * (((S₁ * IR₁) * A₁) * (IR₁ * S₁)) * IR by simp [mul_assoc]]
            rw [hS₁IR₁, hIR₁S₁]
            simp [mul_assoc]
  have hterm₂ :
      star T₂ * M₂ * T₂ = θ • (IR * A₂ * IR) := by
    calc
      star T₂ * M₂ * T₂
          = (Real.sqrt θ * Real.sqrt θ) •
              (IR * (S₂ * (IR₂ * A₂ * IR₂) * S₂) * IR) := by
                simp [T₂, M₂, hS₂_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
      _ = θ • (IR * (S₂ * (IR₂ * A₂ * IR₂) * S₂) * IR) := by
            rw [Real.mul_self_sqrt hθ0]
      _ = θ • (IR * A₂ * IR) := by
            rw [show IR * (S₂ * (IR₂ * A₂ * IR₂) * S₂) * IR =
                IR * (((S₂ * IR₂) * A₂) * (IR₂ * S₂)) * IR by simp [mul_assoc]]
            rw [hS₂IR₂, hIR₂S₂]
            simp [mul_assoc]
  have hleft_inner :
      star T₁ * M₁ * T₁ + star T₂ * M₂ * T₂ = IR * A * IR := by
    rw [hterm₁, hterm₂]
    simp [A, mul_add, add_mul, mul_assoc]
  have hcore :=
    hcoreV (A := M₁) (B := M₂) (X := T₁) (Y := T₂) hM₁_sa hM₂_sa hM₁_spec hM₂_spec hTsum
  have houter := conj_le_conj (ℋ := ℋ) hcore hS_sa
  rw [hleft_inner] at houter
  have hright₁ :
      S * (star T₁ * cfcR (ℋ := ℋ) f M₁ * T₁) * S =
        (1 - θ) • ((f Δ h) A₁ B₁) := by
    calc
      S * (star T₁ * cfcR (ℋ := ℋ) f M₁ * T₁) * S
          = (Real.sqrt (1 - θ) * Real.sqrt (1 - θ)) •
              (S * IR * (S₁ * cfcR (ℋ := ℋ) f M₁ * S₁) * IR * S) := by
                simp [T₁, hS₁_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
      _ = (1 - θ) • (S * IR * (S₁ * cfcR (ℋ := ℋ) f M₁ * S₁) * IR * S) := by
            rw [Real.mul_self_sqrt (sub_nonneg.mpr hθ1)]
      _ = (1 - θ) • (S₁ * cfcR (ℋ := ℋ) f M₁ * S₁) := by
            simp [mul_assoc, hSIR, hIRS]
      _ = (1 - θ) • ((f Δ h) A₁ B₁) := by
            rfl
  have hright₂ :
      S * (star T₂ * cfcR (ℋ := ℋ) f M₂ * T₂) * S =
        θ • ((f Δ h) A₂ B₂) := by
    calc
      S * (star T₂ * cfcR (ℋ := ℋ) f M₂ * T₂) * S
          = (Real.sqrt θ * Real.sqrt θ) •
              (S * IR * (S₂ * cfcR (ℋ := ℋ) f M₂ * S₂) * IR * S) := by
                simp [T₂, hS₂_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
      _ = θ • (S * IR * (S₂ * cfcR (ℋ := ℋ) f M₂ * S₂) * IR * S) := by
            rw [Real.mul_self_sqrt hθ0]
      _ = θ • (S₂ * cfcR (ℋ := ℋ) f M₂ * S₂) := by
            simp [mul_assoc, hSIR, hIRS]
      _ = θ • ((f Δ h) A₂ B₂) := by
            rfl
  have hright :
      S * (star T₁ * cfcR (ℋ := ℋ) f M₁ * T₁ + star T₂ * cfcR (ℋ := ℋ) f M₂ * T₂) * S =
        (1 - θ) • ((f Δ h) A₁ B₁) + θ • ((f Δ h) A₂ B₂) := by
    rw [mul_add, add_mul, hright₁, hright₂]
  have hleft :
      S * cfcR (ℋ := ℋ) f (IR * A * IR) * S = (f Δ h) A B := by
    rfl
  simpa [hleft, hright] using houter

end CondVCore




-- Restricted localized forward form of Theorem 2.5 on the positive cone.
/--
Source: A. Ebadian, I. Nikoufar, M. Eshaghi Gordji, "Perspectives of matrix convex functions",
PNAS 108(18) (2011), 7313--7314, Theorem 2.5. Only the forward direction of the necessary and
sufficient condition. Localized to psdSet × pdSet under f(0)≤0.
-/
theorem jointlyConvexOn_generalizedPerspective_psdSet_pdSet
    {f h : ℝ → ℝ}
    (hf : OperatorConvexIciAllContNonposAtZero.{u} f)
    (hconc : OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) h)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    JointlyConvexOn (psdSet (ℋ := ℋ)) pdSet (fun A B ↦ (f Δ h) A B) := by
  have hcoreV : JensenContractiveColumnCondition (ℋ := ℋ) f :=
    jensenColumn_of_opConvexIciAll (ℋ := ℋ) (f := f) hf
  exact jointlyConvexOn_generalizedPerspective_psdSet_pdSet_of_jensenColumn
    (ℋ := ℋ) (f := f) (h := h) hcoreV hconc hcont hpos

omit [Nontrivial ℋ] in
private lemma generalizedPerspective_neg
    (f h : ℝ → ℝ) (A B : (ℋ →L[ℂ] ℋ)) :
    ((fun x : ℝ ↦ -f x) Δ h) A B = -((f Δ h) A B) := by
  simp [generalizedPerspective, cfcR, cfc_neg, mul_assoc]

omit [Nontrivial ℋ] in
private lemma jointlyConcaveOn_of_jointlyConvexOn_neg
    {s : Set (ℋ →L[ℂ] ℋ)} {t : Set (ℋ →L[ℂ] ℋ)} {Φ : (ℋ →L[ℂ] ℋ) →
        (ℋ →L[ℂ] ℋ) → (ℋ →L[ℂ] ℋ)}
    (hΦ : JointlyConvexOn s t (fun A B ↦ -Φ A B)) :
    JointlyConcaveOn s t Φ := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hneg := hΦ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hneg' :
      -Φ ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂) ≤
        -((1 - θ) • Φ A₁ B₁ + θ • Φ A₂ B₂) := by
    simpa [smul_neg, neg_add, add_comm, add_left_comm, add_assoc] using hneg
  exact (neg_le_neg_iff.mp hneg')

/-- Restricted localized forward form of Corollary 2.6 on the positive cone.

Source: A. Ebadian, I. Nikoufar, M. Eshaghi Gordji, "Perspectives of matrix convex functions",
PNAS 108(18) (2011), 7313--7314, Corollary 2.6. The forward direction of the original proposition is
localized to psdSet × pdSet.
The condition at the origin follows the correction source given separately. Correction source:
Nikoufar (2016), Theorem 1(i) (the corrected version with $f(0)\geq 0$). -/
theorem jointlyConcaveOn_generalizedPerspective_psdSet_pdSet
    {f h : ℝ → ℝ}
    (hfconc : OperatorConcaveOnAll.{u} (Set.Ici (0 : ℝ)) f)
    (hfcont : ContinuousOn f (Set.Ici (0 : ℝ)))
    (hf0 : 0 ≤ f 0)
    (hconc : OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) h)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    JointlyConcaveOn (psdSet (ℋ := ℋ)) pdSet (fun A B ↦ (f Δ h) A B) := by
  have hfneg : OperatorConvexIciAllContNonposAtZero.{u} (fun x : ℝ ↦ -f x) := by
    refine ⟨?_, ?_, ?_⟩
    · intro K _ _ _ _
      simpa [OperatorConcaveOn, OperatorConvexOn] using (hfconc (K := K))
    · simpa using hfcont.neg
    · simpa using (neg_nonpos.mpr hf0)
  have hconv_neg :
      JointlyConvexOn (psdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
        (fun A B ↦ -((f Δ h) A B)) := by
    simpa [generalizedPerspective_neg] using
      (jointlyConvexOn_generalizedPerspective_psdSet_pdSet
        (ℋ := ℋ) (f := fun x : ℝ ↦ -f x) (h := h) hfneg hconc hcont hpos)
  exact jointlyConcaveOn_of_jointlyConvexOn_neg (ℋ := ℋ) hconv_neg

end Theorem25Forward

-- Ebadian--Nikoufar--Eshaghi Gordji (2011), Perspectives of matrix convex functions,
-- page 1, DOI https://www.pnas.org/doi/10.1073/pnas.1102518108
-- For any qudit ℋ, any A ∈ Herm(ℋ), any B ∈ Pd(ℋ),
-- any real-valued continuous function f, any positive-valued continuous function h>0,
-- (fΔh)(A,B) := h(B)^{1/2} f(h(B)^{-1/2} A h(B)^{-1/2}) h(B)^{1/2}

-- Ebadian--Nikoufar--Eshaghi Gordji (2011), Theorem 2.5,
-- DOI https://www.pnas.org/doi/10.1073/pnas.1102518108
-- Suppose that f is a continuous function with f(0) ≤ 0, and h is a continuous function with h > 0.
-- If f is operator convex and h is operator concave,
-- then fΔh is jointly convex

end GeneralizedPerspectiveFunction

-- Ebadian--Nikoufar--Eshaghi Gordji (2011), Corollary 2.6(i),
-- corrected by Nikoufar (2016), Theorem 1(i).
-- Suppose that f is a continuous function with f(0) ≥ 0, and h is a continuous function with h > 0.
-- If f is operator concave and h is operator concave,
-- then fΔh is jointly concave
