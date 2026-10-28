/-
Shows cBits>0 and cBits/n→0 for λ∈(0,1].
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
/-
The ceil lattice is at least log₂x and less than log₂x+cBits.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
/-
The rounded image of [λ^n/3,1] is finite with at most n+1 elements.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
import Quantum.QuantumEntropy.GourResource.Definitions

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_y14 :
∀ lam : ℝ, lam ∈ Set.Ioc 0 1 →
  (∀ n : ℕ, 0 < cBits lam n) ∧
  Tendsto (fun n : ℕ => cBits lam n / (n : ℝ)) atTop (𝓝 0)
:= by
  intro lam hlam
  constructor
  · intro n
    have hlog : 0 ≤ Real.logb 2 (1 / lam) :=
      Real.logb_nonneg (by norm_num) ((one_le_div hlam.1).2 hlam.2)
    have hthree : 0 < Real.logb 2 3 := Real.logb_pos (by norm_num) (by norm_num)
    have hn : (0 : ℝ) < (max n 1 : ℕ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_right n 1))
    exact add_pos_of_nonneg_of_pos hlog (div_pos hthree hn)
  · have hdiv := tendsto_const_div_atTop_nhds_zero_nat (Real.logb 2 3)
    have hlim : Tendsto
        (fun n : ℕ => (Real.logb 2 (1 / lam) + Real.logb 2 3 / (n : ℝ)) / (n : ℝ))
        atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, one_mul, add_zero, mul_zero] using
        (tendsto_const_nhds.add hdiv).mul
          (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    simp only [cBits, max_eq_left hn]

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_y15 :
∀ (lam x : ℝ) (n : ℕ), lam ∈ Set.Ioc 0 1 → 0 < x →
  Real.logb 2 x ≤ grid lam n x ∧ grid lam n x < Real.logb 2 x + cBits lam n
:= by
  intro lam x n hlam _hx
  have hc : 0 < cBits lam n := (GourResource.gsl_y14 lam hlam).1 n
  constructor
  · change Real.logb 2 x ≤ (⌈Real.logb 2 x / cBits lam n⌉ : ℝ) * cBits lam n
    exact (div_le_iff₀ hc).mp (Int.le_ceil (Real.logb 2 x / cBits lam n))
  · change (⌈Real.logb 2 x / cBits lam n⌉ : ℝ) * cBits lam n < Real.logb 2 x + cBits lam n
    calc
      _ < (Real.logb 2 x / cBits lam n + 1) * cBits lam n :=
        mul_lt_mul_of_pos_right (Int.ceil_lt_add_one _) hc
      _ = _ := by rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hc), one_mul]

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_y16 :
∀ (lam : ℝ) (n : ℕ), lam ∈ Set.Ioc 0 1 → 0 < n →
  let S := (fun x : ℝ => Real.rpow 2 (grid lam n x)) '' Set.Icc (lam^n/3) 1
  S.Finite ∧ S.ncard ≤ n+1
:= by
  intro lam n hlam hn
  have hc : 0 < cBits lam n := (GourResource.gsl_y14 lam hlam).1 n
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hbase : 0 < lam ^ n / 3 := div_pos (pow_pos hlam.1 n) (by norm_num)
  have hlog : Real.logb 2 (lam ^ n / 3) = -(n : ℝ) * cBits lam n := by
    rw [Real.logb_div (ne_of_gt (pow_pos hlam.1 n)) (by norm_num), Real.logb_pow]
    simp only [cBits, max_eq_left (Nat.succ_le_iff.mpr hn), one_div, Real.logb_inv]
    field_simp [hn0]
    ring
  let f : ℤ → ℝ := fun k => Real.rpow 2 ((k : ℝ) * cBits lam n)
  have hsub : (fun x : ℝ => Real.rpow 2 (grid lam n x)) '' Set.Icc (lam^n/3) 1 ⊆
      f '' Set.Icc (-(n : ℤ)) 0 := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⌈Real.logb 2 x / cBits lam n⌉, ⟨?_, ?_⟩, rfl⟩
    · have hl : -(n : ℝ) ≤ Real.logb 2 x / cBits lam n := by
        apply (le_div_iff₀ hc).mpr
        rw [← hlog]
        exact Real.logb_le_logb_of_le (by norm_num) hbase hx.1
      have hceil := hl.trans (Int.le_ceil (Real.logb 2 x / cBits lam n))
      exact_mod_cast hceil
    · apply Int.ceil_le.mpr
      simp only [Int.cast_zero]
      apply div_nonpos_of_nonpos_of_nonneg _ hc.le
      exact Real.logb_nonpos (by norm_num) (hbase.trans_le hx.1).le hx.2
  have hfin : (Set.Icc (-(n : ℤ)) 0).Finite := Set.finite_Icc _ _
  have hcard : (Set.Icc (-(n : ℤ)) 0).ncard = n + 1 := by
    rw [← Finset.coe_Icc, Set.ncard_coe_finset, Int.card_Icc]
    omega
  exact ⟨(hfin.image f).subset hsub,
    (Set.ncard_le_ncard hsub (hfin.image f)).trans
      ((Set.ncard_image_le hfin).trans_eq hcard)⟩

end GourResource

