import Quantum.TraceInequality.JensenOperatorInequality

/-!
Finite contractive-column Jensen on the nonnegative half-line.

Source: arXiv:2607.05492v1, main.tex:945–955, Eq. `eq:jensen-finite`;
Hansen–Pedersen, *Jensen's Operator Inequality*, Bull. London Math. Soc. 35
(2003), 553–564, DOI: 10.1112/S0024609303002200.

Only `[0, ∞)` is covered: uniform operator convexity on this set, continuity
on this set, and `f 0 ≤ 0` are explicit hypotheses. No general-interval
version is asserted. The Hilbert space may be infinite dimensional.
-/

namespace JensenOperatorInequality

open LownerHeinzTheorem

universe u v

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

noncomputable local instance : Algebra ℝ (HSum ℋ →L[ℂ] HSum ℋ) := inferInstance
noncomputable local instance : NormedSpace ℝ (HSum ℋ →L[ℂ] HSum ℋ) := inferInstance
noncomputable local instance : Module ℝ (HSum ℋ →L[ℂ] HSum ℋ) := inferInstance
noncomputable local instance : NonnegSpectrumClass ℝ (HSum ℋ →L[ℂ] HSum ℋ) :=
  inferInstance

omit [Nontrivial ℋ] in
private lemma finite_block_compression (A B X Y : ℋ →L[ℂ] ℋ) :
    star (blockOp X 0 Y 0) * blockDiagonal A B * blockOp X 0 Y 0 =
      blockDiagonal (star X * A * X + star Y * B * Y) 0 := by
  rw [blockOp_star, blockDiagonal_eq_blockOp, blockOp_mul, blockOp_mul,
    blockDiagonal_eq_blockOp]
  congr 1 <;> simp [mul_assoc]

omit [Nontrivial ℋ] in
private lemma finite_block_gram (X Y : ℋ →L[ℂ] ℋ) :
    star (blockOp X 0 Y 0) * blockOp X 0 Y 0 =
      blockDiagonal (star X * X + star Y * Y) 0 := by
  have hone : blockDiagonal (1 : ℋ →L[ℂ] ℋ) 1 = 1 :=
    map_one (blockDiagonalHom (ℋ := ℋ))
  simpa [hone] using finite_block_compression (1 : ℋ →L[ℂ] ℋ) 1 X Y

omit [Nontrivial ℋ] in
private lemma finite_block_add (A B : ℋ →L[ℂ] ℋ) :
    blockDiagonal A 0 + blockDiagonal B 0 = blockDiagonal (A + B) 0 := by
  simpa only [blockDiagonalHom_apply, Prod.fst_add, Prod.snd_add, add_zero] using
    (map_add (blockDiagonalHom (ℋ := ℋ)) (A, 0) (B, 0)).symm

omit [Nontrivial ℋ] in
private lemma finite_block_sum {ι : Type v} [Fintype ι] (A : ι → ℋ →L[ℂ] ℋ) :
    ∑ i, blockDiagonal (A i) 0 = blockDiagonal (∑ i, A i) 0 := by
  simpa only [blockDiagonalHom_apply, Prod.fst_sum, Prod.snd_sum,
    Finset.sum_const_zero] using (map_sum (blockDiagonalHom (ℋ := ℋ))
    (fun i ↦ (A i, (0 : ℋ →L[ℂ] ℋ))) Finset.univ).symm

/-- Induction uniformly in the Hilbert space. In the step, two entries are
packed into one block diagonal and its block column on `HSum ℋ`. The new
Gram sum is exactly `diag (∑ i, Xᵢ* Xᵢ) 0`, hence remains at most the identity.
This avoids requiring an inverse of a possibly singular partial Gram sum. -/
private lemma jensen_fin_of_opConvexIciAll {f : ℝ → ℝ}
    (hf : OperatorConvexIciAllContNonposAtZero.{u} f) (n : ℕ) :
    ∀ {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] [Nontrivial K]
      (A X : Fin n → K →L[ℂ] K),
      (∀ i, 0 ≤ A i) → (∑ i, star (X i) * X i ≤ 1) →
      cfcR f (∑ i, star (X i) * A i * X i) ≤
        ∑ i, star (X i) * cfcR f (A i) * X i := by
  induction n using Nat.twoStepInduction with
  | zero =>
      intro K _ _ _ _ A X _ _
      simp only [Fin.sum_univ_zero]
      simpa [cfcR, Algebra.algebraMap_eq_smul_one] using
        smul_nonpos_of_nonpos_of_nonneg hf.2.2 (show (0 : K →L[ℂ] K) ≤ 1 from zero_le_one)
  | one =>
      intro K _ _ _ _ A X hA hX
      simpa using (jensenColumn_of_opConvexIciAll (ℋ := K) hf)
        (A := A 0) (B := 0) (X := X 0) (Y := 0)
        (IsSelfAdjoint.of_nonneg (hA 0)) (by simp)
        (spectrum_Ici_of_nonneg (hA 0)) spectrum_zero_subset_Ici
        (by simpa using hX)
  | more n _ ih =>
      intro K _ _ _ _ A X hA hX
      let P : Fin (n + 1) → HSum K →L[ℂ] HSum K :=
        Fin.cons (blockDiagonal (A 0) (A 1))
          (fun i ↦ blockDiagonal (A i.succ.succ) 0)
      let V : Fin (n + 1) → HSum K →L[ℂ] HSum K :=
        Fin.cons (blockOp (X 0) 0 (X 1) 0)
          (fun i ↦ blockOp (X i.succ.succ) 0 0 0)
      have hP : ∀ i, 0 ≤ P i := by
        intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact blockDiagonal_nonneg (hA 0) (hA 1)
        · exact blockDiagonal_nonneg (hA j.succ.succ) le_rfl
      have hgram : ∑ i, star (V i) * V i =
          blockDiagonal (∑ i, star (X i) * X i) 0 := by
        simp only [Fin.sum_univ_succ, V, Fin.cons_zero, Fin.cons_succ,
          finite_block_gram, star_zero, mul_zero, add_zero]
        rw [finite_block_sum, finite_block_add]
        congr 1
        simp only [add_assoc, Fin.succ_zero_eq_one]
      have hV : ∑ i, star (V i) * V i ≤ 1 := by
        rw [hgram]
        have hone : blockDiagonal (1 : K →L[ℂ] K) 1 = 1 :=
          map_one (blockDiagonalHom (ℋ := K))
        rw [← hone]
        exact blockDiagonal_le_blockDiagonal hX zero_le_one
      have hcompress : ∑ i, star (V i) * P i * V i =
          blockDiagonal (∑ i, star (X i) * A i * X i) 0 := by
        simp only [Fin.sum_univ_succ, P, V, Fin.cons_zero, Fin.cons_succ,
          finite_block_compression, star_zero, mul_zero, add_zero]
        rw [finite_block_sum, finite_block_add]
        congr 1
        simp only [add_assoc, Fin.succ_zero_eq_one]
      have hcfc (C D : K →L[ℂ] K) (hC : 0 ≤ C) (hD : 0 ≤ D) :
          cfcR f (blockDiagonal C D) = blockDiagonal (cfcR f C) (cfcR f D) :=
        cfcR_blockDiagonal f C D (IsSelfAdjoint.of_nonneg hC)
          (IsSelfAdjoint.of_nonneg hD)
          (continuousOn_union_of_subset_Ici hf.2.1
            (spectrum_Ici_of_nonneg hC) (spectrum_Ici_of_nonneg hD))
      have hright : ∑ i, star (V i) * cfcR f (P i) * V i =
          blockDiagonal (∑ i, star (X i) * cfcR f (A i) * X i) 0 := by
        simp only [Fin.sum_univ_succ, P, V, Fin.cons_zero, Fin.cons_succ]
        rw [hcfc _ _ (hA 0) (hA 1), finite_block_compression]
        simp_rw [hcfc _ _ (hA _) le_rfl, finite_block_compression]
        simp only [star_zero, zero_mul, mul_zero, add_zero]
        rw [finite_block_sum, finite_block_add]
        congr 1
        simp only [add_assoc, Fin.succ_zero_eq_one]
      have hsum : 0 ≤ ∑ i, star (X i) * A i * X i :=
        Finset.sum_nonneg fun i _ ↦ by
          simpa [mul_assoc] using star_left_conjugate_nonneg (hA i) (X i)
      have h := ih P V hP hV
      rw [hcompress, hright, hcfc _ _ hsum le_rfl] at h
      exact blockDiagonal_le_left h

/-- Finite contraction Jensen, including the empty index type.

Source: arXiv:2607.05492v1, main.tex:945–955, Eq. `eq:jensen-finite`;
Hansen–Pedersen (2003), *Jensen's Operator Inequality*, 553–564,
DOI: 10.1112/S0024609303002200. This is the continuous `[0, ∞)` version,
with uniform operator convexity on Hilbert spaces in universe `u`.
The finite index type has an independent universe `v`.
-/
theorem jensenFinite_of_opConvexIciAll {ι : Type v} [Fintype ι]
    {f : ℝ → ℝ} (hf : OperatorConvexIciAllContNonposAtZero.{u} f)
    (A X : ι → QuantumState.B ℋ)
    (hA : ∀ i, IsSelfAdjoint (A i))
    (hAs : ∀ i, spectrum ℝ (A i) ⊆ Set.Ici (0 : ℝ))
    (hX : ∑ i, star (X i) * X i ≤ 1) :
    cfcR f (∑ i, star (X i) * A i * X i) ≤
      ∑ i, star (X i) * cfcR f (A i) * X i := by
  classical
  let e := (Fintype.equivFin ι).symm
  have hpos (i : ι) : 0 ≤ A i :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) (A i) (ha := hA i)).2
      fun x hx ↦ hAs i hx
  have h := jensen_fin_of_opConvexIciAll hf (Fintype.card ι)
    (fun i ↦ A (e i)) (fun i ↦ X (e i)) (fun i ↦ hpos (e i))
    (by simpa only [e.sum_comp (fun i ↦ star (X i) * X i)] using hX)
  simpa only [e.sum_comp (fun i ↦ star (X i) * A i * X i),
    e.sum_comp (fun i ↦ star (X i) * cfcR f (A i) * X i)] using h

end JensenOperatorInequality
