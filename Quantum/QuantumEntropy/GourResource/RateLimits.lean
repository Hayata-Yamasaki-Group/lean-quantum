/-
Evaluates the liminf of an EReal sequence z using p with small liminf and q converging to 0 along every tail.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
/-
For cBits and δ∈(0,1), bounds the tail of cap by a nonnegative finite C independent of δ.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
import Quantum.OperationalProbabilistic.Framework.TestingRegionDecisionDefinitions.GSLCore
import Quantum.QuantumEntropy.GourResource.SpectralGrid


namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_y39 :
∀ (z : ℕ → EReal) (p q : ℕ → ℝ) (a b C h : ℝ),
  0 ≤ b → 0 ≤ C →
  (∀ᶠ n in atTop, p n ∈ Set.Icc 0 1 ∧ q n ∈ Set.Icc 0 1) →
  Filter.liminf p atTop ≤ h → Tendsto q atTop (𝓝 0) →
  (∀ᶠ n in atTop, z n ≤ ((a+b*p n+C*q n : ℝ) : EReal)) →
    Filter.liminf z atTop ≤ ((a+b*h : ℝ) : EReal)
:= by
  intro z p q a b C h hb _hC hpq hp hq hz
  have hp_lower : IsBoundedUnder (· ≥ ·) atTop p :=
    isBoundedUnder_of_eventually_ge (hpq.mono fun _ hn => hn.1.1)
  have hp_upper : IsBoundedUnder (· ≤ ·) atTop p :=
    isBoundedUnder_of_eventually_le (hpq.mono fun _ hn => hn.1.2)
  have hmono : Monotone (fun x : ℝ => ((a + b * x : ℝ) : EReal)) := by
    intro x y hxy
    exact EReal.coe_le_coe (add_le_add le_rfl (mul_le_mul_of_nonneg_left hxy hb))
  have hcont : Continuous (fun x : ℝ => ((a + b * x : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp
      (continuous_const.add (continuous_const.mul continuous_id))
  have hplim :
      liminf (fun n => ((a + b * p n : ℝ) : EReal)) atTop =
        ((a + b * liminf p atTop : ℝ) : EReal) := by
    simpa only [Function.comp_def] using
      (hmono.map_liminf_of_continuousAt p hcont.continuousAt
        hp_upper.isCoboundedUnder_ge hp_lower).symm
  have hq_real : Tendsto (fun n => C * q n) atTop (𝓝 (0 : ℝ)) := by
    simpa using hq.const_mul C
  have hq_ereal :
      Tendsto (fun n => ((C * q n : ℝ) : EReal)) atTop (𝓝 (0 : EReal)) := by
    simpa only [EReal.coe_zero] using EReal.tendsto_coe.mpr hq_real
  have hsum :
      liminf (fun n => ((C * q n : ℝ) : EReal) + ((a + b * p n : ℝ) : EReal))
        atTop ≤ ((a + b * liminf p atTop : ℝ) : EReal) := by
    have hadd := EReal.liminf_add_le
      (u := fun n => ((C * q n : ℝ) : EReal))
      (v := fun n => ((a + b * p n : ℝ) : EReal)) (f := atTop)
      (Or.inr (by rw [hplim]; exact EReal.coe_ne_top _))
      (Or.inr (by rw [hplim]; exact EReal.coe_ne_bot _))
    simpa only [Pi.add_apply, hq_ereal.limsup_eq, hplim, zero_add] using hadd
  calc
    liminf z atTop ≤
        liminf (fun n => ((C * q n : ℝ) : EReal) + ((a + b * p n : ℝ) : EReal))
          atTop := by
      refine Filter.liminf_le_liminf ?_ (by isBoundedDefault) (by isBoundedDefault)
      filter_upwards [hz] with n hn
      simpa only [← EReal.coe_add, add_comm (C * q n)] using hn
    _ ≤ ((a + b * liminf p atTop : ℝ) : EReal) := hsum
    _ ≤ ((a + b * h : ℝ) : EReal) :=
      EReal.coe_le_coe (add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hb))

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_y40 :
∀ (lam b : ℝ), lam ∈ Set.Ioc 0 1 →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, δ ∈ Set.Ioo 0 1 →
    ∀ᶠ n in atTop, cap lam b δ n ≤ C
:= by
  intro lam b hlam
  let B := Real.logb 2 (1 / lam) + Real.logb 2 3
  refine ⟨max 0 (max (B + 1) (b + 1)), le_max_left _ _, ?_⟩
  intro δ hδ
  have htail : ∀ᶠ n : ℕ in atTop, cBits lam n / (n : ℝ) < 1 :=
    (GourResource.gsl_y14 lam hlam).2.eventually_lt_const zero_lt_one
  filter_upwards [htail] with n hn
  have hden : (1 : ℝ) ≤ (max n 1 : ℕ) := by
    exact_mod_cast le_max_right n 1
  have hlog : 0 ≤ Real.logb 2 3 :=
    (Real.logb_pos (by norm_num) (by norm_num)).le
  have hbits : cBits lam n ≤ B := by
    exact add_le_add (le_refl (Real.logb 2 (1 / lam))) (div_le_self hlog hden)
  apply max_le
  · exact (add_le_add hbits hn.le).trans
      ((le_max_left (B + 1) (b + 1)).trans (le_max_right 0 _))
  · exact (add_le_add (le_refl b) hδ.2.le).trans
      ((le_max_right (B + 1) (b + 1)).trans (le_max_right 0 _))

end GourResource

