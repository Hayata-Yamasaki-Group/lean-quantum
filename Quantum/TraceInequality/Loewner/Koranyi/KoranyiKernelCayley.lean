import Quantum.TraceInequality.Loewner.Koranyi.CayleyRatioIdentity
import Quantum.TraceInequality.Loewner.Koranyi.RatioKernel


namespace Quantum.TraceInequality.Loewner

open Set

noncomputable section

/-!
Step 16 (bridge): relate the ratio kernel on `(0,∞)` (encoded as `ENNReal`) to the Korányi-type
kernel on `(-1,1)` via the Cayley transform.

This file only provides pointwise algebraic identities (and basic positivity facts), intended to
be used when transporting measures between `(-1,1)` and `[0,∞]`.
-/

/-- The Korányi-type kernel on `(-1,1)`. -/
def koranyiKernel (x t : ℝ) : ℝ :=
  ((1 + x) * (1 - t)) / (2 * (1 - x * t))

/-- Definitional form of the Koranyi kernel. -/
lemma koranyiKernel_def (x t : ℝ) :
    koranyiKernel x t = ((1 + x) * (1 - t)) / (2 * (1 - x * t)) := rfl

/-- The Koranyi kernel is nonnegative on the open square `(-1,1) × (-1,1)`. -/
lemma koranyiKernel_nonneg {x t : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    0 ≤ koranyiKernel x t := by
  have hx1 : -1 < x := hx.1
  have hx2 : x < 1 := hx.2
  have ht1 : -1 < t := ht.1
  have ht2 : t < 1 := ht.2
  have hpos1 : 0 < 1 + x := by linarith
  have hpos2 : 0 < 1 - t := by linarith
  have hpos3 : 0 < 1 - x * t := by
    have hxabs : |x| < 1 := by
      have : (-1 : ℝ) < x ∧ x < 1 := ⟨hx1, hx2⟩
      simpa [abs_lt] using this
    have htabs : |t| < 1 := by
      have : (-1 : ℝ) < t ∧ t < 1 := ⟨ht1, ht2⟩
      simpa [abs_lt] using this
    have hmulabs : |x| * |t| < 1 := by
      -- `mul_lt_mul''` yields `|x|*|t| < 1*1`.
      have h := mul_lt_mul'' hxabs htabs (abs_nonneg x) (abs_nonneg t)
      simpa using h
    have hxtabs : |x * t| < 1 := by
      simpa [abs_mul] using hmulabs
    have hxt : x * t < 1 := lt_of_le_of_lt (le_abs_self _) hxtabs
    exact sub_pos.mpr hxt
  have hpos_den : 0 < 2 * (1 - x * t) := mul_pos two_pos hpos3
  have hpos_num : 0 ≤ (1 + x) * (1 - t) := by
    exact mul_nonneg (le_of_lt hpos1) (le_of_lt hpos2)
  have : 0 ≤ ((1 + x) * (1 - t)) / (2 * (1 - x * t)) := by
    exact div_nonneg hpos_num (le_of_lt hpos_den)
  simpa [koranyiKernel] using this

/-- Under Cayley, the `ENNReal` ratio kernel is the Koranyi kernel on `(-1,1)`. -/
lemma ratioKernel_ofReal_cayley_eq_ofReal_koranyiKernel
    {x t : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    ratioKernel (ENNReal.ofReal (cayley x)) (ENNReal.ofReal (cayley t)) =
      ENNReal.ofReal (koranyiKernel x t) := by
  have hxpos : 0 < cayley x := cayley_pos_of_mem_Ioo (x := x) hx
  have htpos : 0 < cayley t := cayley_pos_of_mem_Ioo (x := t) ht
  have hdenpos : 0 < cayley x + cayley t := by linarith
  have hnonneg : 0 ≤ koranyiKernel x t := koranyiKernel_nonneg (x := x) (t := t) hx ht
  -- Reduce to the real identity, then transfer to `ENNReal.ofReal`.
  have hid :
      cayley x / (cayley x + cayley t) = koranyiKernel x t := by
    simpa [koranyiKernel] using cayley_div_cayley_add_cayley_eq (x := x) (t := t) hx ht
  have hx0 : 0 ≤ cayley x := le_of_lt hxpos
  have ht0 : 0 ≤ cayley t := le_of_lt htpos
  have hden :
      ENNReal.ofReal (cayley x + cayley t) =
        ENNReal.ofReal (cayley x) + ENNReal.ofReal (cayley t) :=
    ENNReal.ofReal_add hx0 ht0
  calc
    ratioKernel (ENNReal.ofReal (cayley x)) (ENNReal.ofReal (cayley t))
        = ENNReal.ofReal (cayley x) / (ENNReal.ofReal (cayley x) + ENNReal.ofReal (cayley t)) := by
            simp [ratioKernel]
    _ = ENNReal.ofReal (cayley x) / ENNReal.ofReal (cayley x + cayley t) := by
          have hsum :
              ENNReal.ofReal (cayley x) + ENNReal.ofReal (cayley t) =
                ENNReal.ofReal (cayley x + cayley t) := by
            simpa using hden.symm
          have hsum' :
              ENNReal.ofReal ((1 + x) / (1 - x)) + ENNReal.ofReal ((1 + t) / (1 - t)) =
                ENNReal.ofReal (((1 + x) / (1 - x)) + ((1 + t) / (1 - t))) := by
            simpa [cayley] using hsum
          simp [cayley, hsum']
    _ = ENNReal.ofReal (cayley x / (cayley x + cayley t)) := by
          simpa using
            (ENNReal.ofReal_div_of_pos (x := cayley x) (y := cayley x + cayley t) hdenpos).symm
    _ = ENNReal.ofReal (koranyiKernel x t) := by
          -- Use the real identity directly, avoiding rewriting issues with definitional
          -- unfolding.
          simpa [koranyiKernel] using
            congrArg ENNReal.ofReal (cayley_div_cayley_add_cayley_eq (x := x) (t := t) hx ht)

/-- The bounded-continuous ratio kernel evaluates to the nonnegative Koranyi kernel. -/
lemma ratioKernelBCNN_ofReal_cayley_apply
    {x t : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    ratioKernelBCNN (ENNReal.ofReal (cayley x)) (by simp) (ENNReal.ofReal (cayley t)) =
      Real.toNNReal (koranyiKernel x t) := by
  -- Avoid unfolding `ratioKernel` (which introduces `toNNReal` divisions); rewrite it first.
  change
      (ratioKernel (ENNReal.ofReal (cayley x)) (ENNReal.ofReal (cayley t))).toNNReal =
        Real.toNNReal (koranyiKernel x t)
  simpa [ENNReal.ofReal] using
    congrArg ENNReal.toNNReal
      (ratioKernel_ofReal_cayley_eq_ofReal_koranyiKernel (x := x) (t := t) hx ht)

end

end Quantum.TraceInequality.Loewner
