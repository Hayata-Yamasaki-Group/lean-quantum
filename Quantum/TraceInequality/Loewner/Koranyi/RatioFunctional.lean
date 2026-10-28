import Quantum.TraceInequality.Loewner.Koranyi.RatioKernelSubseq

import Mathlib.Data.ENNReal.Real


namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped NNReal
open scoped BoundedContinuousFunction

noncomputable section

/-!
Step 13 (utility): the ratio-kernel functional induced by a finite measure on `ENNReal`.

For a finite measure `μ` on `ENNReal = [0,∞]`, we package the map
`x ↦ ∫ x/(x+λ) dμ(λ)` in the `testAgainstNN` formalism.
-/

/-- Ratio-kernel functional `x ↦ ∫ x / (x + λ) dμ(λ)` as an `ℝ≥0` value. -/
def ratioFunctional (μ : FiniteMeasure ENNReal) (x : ℝ≥0) : ℝ≥0 :=
  μ.testAgainstNN (ratioKernelBCNN (x : ENNReal) (by simp))

/-- Definition rule for `ratioFunctional` through `FiniteMeasure.testAgainstNN`. -/
lemma ratioFunctional_def (μ : FiniteMeasure ENNReal) (x : ℝ≥0) :
    ratioFunctional μ x = μ.testAgainstNN (ratioKernelBCNN (x : ENNReal) (by simp)) := rfl


/-- For fixed `λ`, the ratio kernel is monotone in the nonnegative parameter `x`. -/
lemma ratioKernel_mono_left (l : ENNReal) :
    Monotone fun x : ℝ≥0 => ratioKernel (x : ENNReal) l := by
  intro x y hxy
  by_cases hl : l = ⊤
  · subst hl
    simp [ratioKernel]
  · have hx_top : (x : ENNReal) ≠ ⊤ := by simp
    have hy_top : (y : ENNReal) ≠ ⊤ := by simp
    have hxrl_top : ratioKernel (x : ENNReal) l ≠ ⊤ := ratioKernel_ne_top (x : ENNReal) l
    have hyrl_top : ratioKernel (y : ENNReal) l ≠ ⊤ := ratioKernel_ne_top (y : ENNReal) l
    -- Reduce the inequality in `ENNReal` to one in `ℝ` via `toReal`.
    have hre : (ratioKernel (x : ENNReal) l).toReal ≤ (ratioKernel (y : ENNReal) l).toReal := by
      -- Compute `toReal` and prove the inequality in `ℝ`.
      have hx_le : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast hxy
      have hc0 : 0 ≤ l.toReal := ENNReal.toReal_nonneg
      by_cases hc : l.toReal = 0
      · -- Then `l` is `0`, so the ratio is `x/x` and monotonicity is trivial.
        have hl0 : l = 0 := by
          -- `l ≠ ⊤` and `l.toReal = 0` implies `l = 0`.
          have h0 : ENNReal.ofReal l.toReal = l := ENNReal.ofReal_toReal (by simpa using hl)
          have : (0 : ENNReal) = l := by simpa [hc] using h0
          simpa [eq_comm] using this
        subst hl0
        by_cases hx0 : x = 0
        · subst hx0
          have hy0 : 0 ≤ (y : ℝ) := by positivity
          have : (0 : ℝ) ≤ (y : ℝ) / (y : ℝ) := div_nonneg hy0 hy0
          simpa [ratioKernel] using this
        · have hy0 : y ≠ 0 := by
            intro hy0
            have hx_le_zero : x ≤ 0 := by
              simpa [hy0] using hxy
            exact hx0 (le_antisymm hx_le_zero (zero_le x))
          have hx0' : (x : ℝ) ≠ 0 := by exact_mod_cast hx0
          have hy0' : (y : ℝ) ≠ 0 := by exact_mod_cast hy0
          simp [ratioKernel, hx0', hy0']
      · have hcpos : 0 < l.toReal := lt_of_le_of_ne hc0 (Ne.symm hc)
        have hx0' : 0 ≤ (x : ℝ) := by positivity
        have hy0' : 0 ≤ (y : ℝ) := by positivity
        have hxden : 0 < (x : ℝ) + l.toReal := by linarith
        have hyden : 0 < (y : ℝ) + l.toReal := by linarith
        -- Use `div_le_div_iff₀` to clear denominators.
        have hmul :
            ((x : ℝ) / ((x : ℝ) + l.toReal)) ≤ ((y : ℝ) / ((y : ℝ) + l.toReal)) := by
          have hxden' : 0 < (x : ℝ) + l.toReal := hxden
          have hyden' : 0 < (y : ℝ) + l.toReal := hyden
          -- It suffices to show `x*(y+c) ≤ y*(x+c)`.
          have : (x : ℝ) * ((y : ℝ) + l.toReal) ≤ (y : ℝ) * ((x : ℝ) + l.toReal) := by
            -- Expand and compare the `l.toReal` terms.
            have hmulc : (x : ℝ) * l.toReal ≤ (y : ℝ) * l.toReal :=
              mul_le_mul_of_nonneg_right hx_le hc0
            have hadd :
                (x : ℝ) * (y : ℝ) + (x : ℝ) * l.toReal ≤
                  (x : ℝ) * (y : ℝ) + (y : ℝ) * l.toReal := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left hmulc ((x : ℝ) * (y : ℝ))
            calc
              (x : ℝ) * ((y : ℝ) + l.toReal) =
                  (x : ℝ) * (y : ℝ) + (x : ℝ) * l.toReal := by
                ring
              _ ≤ (x : ℝ) * (y : ℝ) + (y : ℝ) * l.toReal := hadd
              _ = (y : ℝ) * ((x : ℝ) + l.toReal) := by ring
          exact (div_le_div_iff₀ hxden' hyden').2 this
        -- Put back the `toReal` computations.
        -- We use `toReal_add` since `l ≠ ⊤` and `x,y` are finite.
        simpa [ratioKernel, ENNReal.toReal_div, ENNReal.toReal_add hx_top (by simpa using hl),
          ENNReal.toReal_add hy_top (by simpa using hl)] using hmul
    exact (ENNReal.toReal_le_toReal hxrl_top hyrl_top).1 hre

/-- The ratio functional is monotone in its nonnegative parameter. -/
theorem monotone_ratioFunctional (μ : FiniteMeasure ENNReal) :
    Monotone fun x : ℝ≥0 => ratioFunctional μ x := by
  intro x y hxy
  -- Pointwise monotonicity of the kernel.
  have hle :
      (fun l : ENNReal => ratioKernelBCNN (x : ENNReal) (by simp) l) ≤
        (fun l : ENNReal => ratioKernelBCNN (y : ENNReal) (by simp) l) := by
    intro l
    have hker : ratioKernel (x : ENNReal) l ≤ ratioKernel (y : ENNReal) l :=
      ratioKernel_mono_left (l := l) hxy
    have hker' :
        (ratioKernel (x : ENNReal) l).toNNReal ≤ (ratioKernel (y : ENNReal) l).toNNReal :=
      ENNReal.toNNReal_mono (ratioKernel_ne_top (y : ENNReal) l) hker
    simpa [ratioKernelBCNN_apply] using hker'
  have hmono :=
    MeasureTheory.FiniteMeasure.testAgainstNN_mono μ
      (f := ratioKernelBCNN (x : ENNReal) (by simp))
      (g := ratioKernelBCNN (y : ENNReal) (by simp)) hle
  simpa [ratioFunctional] using hmono


end

end Quantum.TraceInequality.Loewner
