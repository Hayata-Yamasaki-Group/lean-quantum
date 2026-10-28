import Quantum.TraceInequality.Loewner.Koranyi.SupportElimination
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Quantum.TraceInequality.Loewner.Koranyi.SupportElimAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Quantum.TraceInequality.Loewner.Koranyi.StieltjesTransform
import Quantum.TraceInequality.Loewner.Koranyi.CayleyPushforward

/-!
# Kernel identities for the support-elimination transform

Steps of the Korányi construction for `supportElimMeasure`: it gives no mass to `{0}`, the
kernel `x/(t(t - x))` splits almost everywhere, the Stieltjes transform of the transformed
measure is an explicit difference of integrals, and the ratio functional of its Cayley
pushforward is a Korányi-kernel integral.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set Filter

open scoped UpperHalfPlane

noncomputable section



/-- The inversion map's preimage of `{0}` is `{0}`. -/
lemma supportElimInv_preimage_singleton_zero :
    supportElimInv ⁻¹' ({0} : Set ℝ) = {0} := by
  ext y
  simp [supportElimInv]

/-- The support-elimination transform assigns measure `0` to the singleton `{0}`. -/
lemma supportElimMeasure_singleton_zero (μ : Measure ℝ) :
    supportElimMeasure μ ({0} : Set ℝ) = 0 := by
  -- Unfold the definition and compute using the map formula.
  have hmeas : MeasurableSet ({0} : Set ℝ) := isClosed_singleton.measurableSet
  have hmap :
      supportElimMeasure μ {0} =
        ((μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ).withDensity supportElimWeight)
          (supportElimInv ⁻¹' ({0} : Set ℝ)) := by
    simp [supportElimMeasure, Measure.map_apply, measurable_supportElimInv, hmeas]
  -- The preimage is `{0}`, which lies inside `[-1,1]` and hence is null for the restricting set.
  have hpre :
      (supportElimInv ⁻¹' ({0} : Set ℝ)) ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro y hy
    have : y = 0 := by
      simpa [supportElimInv_preimage_singleton_zero] using hy
    subst this
    constructor <;> linarith
  have hrestrict :
      (μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) (supportElimInv ⁻¹' ({0} : Set ℝ)) = 0 := by
    -- The set is disjoint from the restricting set.
    calc
      (μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) (supportElimInv ⁻¹' ({0} : Set ℝ))
          = μ ((supportElimInv ⁻¹' ({0} : Set ℝ)) ∩ (Set.Icc (-1 : ℝ) 1)ᶜ) := by
              simp
      _ = μ ∅ := by
            have : (supportElimInv ⁻¹' ({0} : Set ℝ)) ∩ (Set.Icc (-1 : ℝ) 1)ᶜ = ∅ := by
              ext y
              constructor
              · intro hy
                exact hy.2 (hpre hy.1)
              · intro hy
                simp at hy
            simp [this]
      _ = 0 := by simp
  have hac :
      ((μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ).withDensity supportElimWeight) ≪
        (μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) :=
    MeasureTheory.withDensity_absolutelyContinuous _ _
  have hwd :
      ((μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ).withDensity supportElimWeight)
          (supportElimInv ⁻¹' ({0} : Set ℝ)) = 0 :=
    hac hrestrict
  simpa [hmap] using hwd

/-- Almost every point is nonzero under the support-elimination transform. -/
lemma ae_supportElimMeasure_ne_zero (μ : Measure ℝ) :
    (∀ᵐ t ∂(supportElimMeasure μ), t ≠ 0) := by
  -- `t = 0` is a null set under `supportElimMeasure μ`.
  have h0 : supportElimMeasure μ ({0} : Set ℝ) = 0 := supportElimMeasure_singleton_zero (μ := μ)
  have h0' : (supportElimMeasure μ) {t : ℝ | ¬ t ≠ 0} = 0 := by
    simpa [Set.setOf_eq_eq_singleton] using h0
  exact (MeasureTheory.ae_iff.2 h0')

/-- Almost everywhere under the support-elimination transform, the kernel `x/(t(t - x))` equals
the difference of Stieltjes kernels `1/(t - x) - 1/t`, the rewrite being valid away from `t = 0`. -/
lemma supportElimMeasure_kernel_split_ae (μ : Measure ℝ) (x : ℂ) (hx : x.im ≠ 0) :
    (fun t : ℝ => x / ((t : ℂ) * ((t : ℂ) - x))) =ᵐ[supportElimMeasure μ]
      fun t : ℝ => (1 / ((t : ℂ) - x)) - (1 / (t : ℂ)) := by
  -- The identity holds pointwise for `t ≠ 0` since then we can clear denominators.
  have hne0 : ∀ᵐ t : ℝ ∂(supportElimMeasure μ), (t : ℂ) ≠ 0 := by
    filter_upwards [ae_supportElimMeasure_ne_zero (μ := μ)] with t ht
    exact_mod_cast ht
  filter_upwards [hne0] with t ht
  have htx : (t : ℂ) - x ≠ 0 := by
    -- `x` is not real, so it cannot equal `(t : ℂ)`.
    intro h
    have : ((t : ℂ) - x).im = 0 := congrArg Complex.im h
    have h_im : -x.im = 0 := by
      simpa using this
    exact hx (neg_eq_zero.mp h_im)
  field_simp [ht, htx]
  ring

/-- The integral of `x/(t(t - x))` against the support-elimination transform equals the integral of
`1/(t - x) - 1/t`. -/
theorem integral_supportElimMeasure_kernel_split (μ : Measure ℝ) (x : ℂ) (hx : x.im ≠ 0) :
    (∫ t : ℝ, x / ((t : ℂ) * ((t : ℂ) - x)) ∂(supportElimMeasure μ)) =
      ∫ t : ℝ, ((1 / ((t : ℂ) - x)) - (1 / (t : ℂ))) ∂(supportElimMeasure μ) := by
  refine MeasureTheory.integral_congr_ae ?_
  exact supportElimMeasure_kernel_split_ae (μ := μ) (x := x) hx

end

end Quantum.TraceInequality.Loewner

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set

noncomputable section



section

variable (μ : Measure ℝ) {z : ℂ}

private lemma inv_im_ne_zero (hz : z.im ≠ 0) : (z⁻¹).im ≠ 0 := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  have hn : 0 < Complex.normSq z := (Complex.normSq_pos).2 hz0
  have h_im : (z⁻¹).im = -z.im / Complex.normSq z := by
    simp [Complex.inv_im]
  intro h
  have hdiv : (-z.im / Complex.normSq z) = 0 := by
    simpa [h_im] using h
  have hn0 : (Complex.normSq z) ≠ 0 := ne_of_gt hn
  have hnum : (-z.im) = 0 := by
    rcases (div_eq_zero_iff).1 hdiv with hnum | hden
    · exact hnum
    · exact (hn0 hden).elim
  have : z.im = 0 := by linarith
  exact hz this

private lemma supportElimWeight_toReal (y : ℝ) :
    (supportElimWeight y).toReal = (y ^ (2 : ℕ))⁻¹ := by
  have h0 : 0 ≤ (y ^ (2 : ℕ))⁻¹ := by
    have : 0 ≤ y ^ (2 : ℕ) := by simpa using (pow_two_nonneg y)
    exact inv_nonneg.2 this
  simpa [supportElimWeight] using (ENNReal.toReal_ofReal h0)

/-- For `z` with nonzero imaginary part, the Stieltjes kernel integral against the
support-elimination transform of `μ` equals the integral of `1/y - 1/(y - z⁻¹)` over `[-1, 1]ᶜ`. -/
theorem integral_supportElimMeasure_stieltjesKernel_eq_integral_diff
    (hz : z.im ≠ 0) :
    (∫ t, (1 / ((t : ℂ) - z)) ∂(supportElimMeasure μ)) =
      ∫ y,
        ((1 / (y : ℂ)) - (1 / ((y : ℂ) - z⁻¹)))
          ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) := by
  classical
  have hS : MeasurableSet (Set.Icc (-1 : ℝ) 1)ᶜ :=
    (isClosed_Icc.measurableSet).compl
  have hmeas_inv : Measurable supportElimInv := measurable_supportElimInv
  have hmeas_w : Measurable supportElimWeight := measurable_supportElimWeight
  -- Pull back the integral along inversion.
  have hmap :
      (∫ t, (1 / ((t : ℂ) - z)) ∂(supportElimMeasure μ)) =
        ∫ y, (1 / (((supportElimInv y : ℝ) : ℂ) - z))
          ∂((μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ).withDensity supportElimWeight) := by
    set μ0 : Measure ℝ := (μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ).withDensity supportElimWeight
    have hφ : AEMeasurable supportElimInv μ0 := hmeas_inv.aemeasurable
    have hf :
        AEStronglyMeasurable (fun t : ℝ => (1 / ((t : ℂ) - z)))
          (Measure.map supportElimInv μ0) :=
      (measurable_const.div (Complex.measurable_ofReal.sub measurable_const)).aestronglyMeasurable
    have h :=
      (MeasureTheory.integral_map (μ := μ0) (φ := supportElimInv) hφ
        (f := fun t : ℝ => (1 / ((t : ℂ) - z))) hf)
    simpa [supportElimMeasure, μ0] using h
  -- Rewrite the `withDensity` integral.
  have hwd :
      (∫ y, (1 / (((supportElimInv y : ℝ) : ℂ) - z))
          ∂((μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ).withDensity supportElimWeight)) =
        ∫ y,
          (supportElimWeight y).toReal • (1 / (((supportElimInv y : ℝ) : ℂ) - z))
          ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) := by
    have htop :
        (∀ᵐ y ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ),
          supportElimWeight y < (⊤ : ENNReal)) := by
      exact MeasureTheory.ae_of_all
        (μ := μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ)
        (fun y => by
          simp [supportElimWeight])
    simpa using
      (integral_withDensity_eq_integral_toReal_smul
        (μ := μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) (f := supportElimWeight) hmeas_w htop
        (g := fun y : ℝ => (1 / (((supportElimInv y : ℝ) : ℂ) - z))))
  -- Replace the integrand a.e. on `[-1,1]ᶜ` by a purely algebraic identity.
  have hEq :
      (fun y : ℝ =>
          (supportElimWeight y).toReal • (1 / (((supportElimInv y : ℝ) : ℂ) - z))) =ᵐ[
          μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ]
        fun y : ℝ => ((1 / (y : ℂ)) - (1 / ((y : ℂ) - z⁻¹))) := by
    filter_upwards [ae_restrict_mem hS] with y hy
    have hy0 : y ≠ 0 := by
      -- `y ∉ [-1,1]` implies `y ≠ 0`.
      have hyIcc : ¬ y ∈ Set.Icc (-1 : ℝ) 1 := by
        simpa [Set.mem_compl_iff] using hy
      intro h
      apply hyIcc
      simp [h]
    have hz0 : z ≠ 0 := by
      intro h
      simp [h] at hz
    have hinv_im : (z⁻¹).im ≠ 0 := inv_im_ne_zero (z := z) hz
    have hsub1 : ((y⁻¹ : ℝ) : ℂ) - z ≠ 0 :=
      complex_sub_ne_of_im_ne_zero (r := (y⁻¹ : ℝ)) (z := z) hz
    have hsub2 : (y : ℂ) - z⁻¹ ≠ 0 :=
      complex_sub_ne_of_im_ne_zero (r := y) (z := z⁻¹) hinv_im
    -- Convert the scalar multiplication to multiplication in `ℂ`.
    -- Then clear denominators.
    have :
        ((supportElimWeight y).toReal : ℂ) * (1 / (((supportElimInv y : ℝ) : ℂ) - z)) =
          (1 / (y : ℂ)) - (1 / ((y : ℂ) - z⁻¹)) := by
      have hwt : (supportElimWeight y).toReal = (y ^ (2 : ℕ))⁻¹ :=
        supportElimWeight_toReal (y := y)
      have hy0C : (y : ℂ) ≠ 0 := by exact_mod_cast hy0
      have hne1 : (1 - (y : ℂ) * z) ≠ 0 := by
        intro h
        have hyz : (y : ℂ) * z = (1 : ℂ) := by
          simpa using (sub_eq_zero.mp h).symm
        have hz_eq : z = (y : ℂ)⁻¹ := by
          calc
            z = (y : ℂ)⁻¹ * ((y : ℂ) * z) := by
              simp [mul_comm, hy0C]
            _ = (y : ℂ)⁻¹ := by simp [hyz]
        have hz_eq' : z = ((y⁻¹ : ℝ) : ℂ) := by
          simpa [Complex.ofReal_inv] using hz_eq
        exact hz (by simp [hz_eq'] )
      -- We rewrite both sides to the common expression
      -- `(y : ℂ)⁻¹ * (1 - (y : ℂ) * z)⁻¹`.
      have hL :
          ((supportElimWeight y).toReal : ℂ) * (1 / (((supportElimInv y : ℝ) : ℂ) - z)) =
            (y : ℂ)⁻¹ * (1 - (y : ℂ) * z)⁻¹ := by
        -- Expand `supportElimInv` and rewrite the inverse difference.
        have hfactor :
            (((supportElimInv y : ℝ) : ℂ) - z) = (1 - (y : ℂ) * z) * (y : ℂ)⁻¹ := by
          -- `(1 - y*z) * y⁻¹ = y⁻¹ - z`, using commutativity.
          have hmul :
              ((y : ℂ) * z) * (y : ℂ)⁻¹ = z := by
            calc
              ((y : ℂ) * z) * (y : ℂ)⁻¹ = z * ((y : ℂ) * (y : ℂ)⁻¹) := by
                simp [mul_assoc, mul_comm]
              _ = z := by simp [hy0C]
          -- Reduce to a direct computation in `ℂ`.
          have :
              ((y : ℂ)⁻¹ - z) = (1 - (y : ℂ) * z) * (y : ℂ)⁻¹ := by
            calc
              (y : ℂ)⁻¹ - z = (y : ℂ)⁻¹ - ((y : ℂ) * z) * (y : ℂ)⁻¹ := by
                simp [hmul]
              _ = (1 - (y : ℂ) * z) * (y : ℂ)⁻¹ := by
                simp [sub_mul, one_mul]
          simpa [supportElimInv, Complex.ofReal_inv, hy0C] using this
        calc
          ((supportElimWeight y).toReal : ℂ) * (1 / (((supportElimInv y : ℝ) : ℂ) - z))
              = ((y ^ (2 : ℕ))⁻¹ : ℂ) * (1 / (((supportElimInv y : ℝ) : ℂ) - z)) := by
                  simp [hwt]
          _ = ((y : ℂ) ^ (2 : ℕ))⁻¹ * (1 / (((supportElimInv y : ℝ) : ℂ) - z)) := by
                  simp
          _ = ((y : ℂ) ^ (2 : ℕ))⁻¹ * (((((supportElimInv y : ℝ) : ℂ) - z))⁻¹) := by
                  simp [div_eq_mul_inv]
          _ = ((y : ℂ) ^ (2 : ℕ))⁻¹ * (((1 - (y : ℂ) * z) * (y : ℂ)⁻¹)⁻¹) := by
                  simp [hfactor]
          _ = ((y : ℂ) ^ (2 : ℕ))⁻¹ * ((y : ℂ) * (1 - (y : ℂ) * z)⁻¹) := by
                  simp [mul_assoc, mul_comm]
          _ = (y : ℂ)⁻¹ * (1 - (y : ℂ) * z)⁻¹ := by
                  -- `y⁻² * y = y⁻¹`.
                  simp [pow_two, mul_assoc, mul_comm, mul_left_comm, hy0C]
      have hR :
          (1 / (y : ℂ)) - (1 / ((y : ℂ) - z⁻¹)) =
            (y : ℂ)⁻¹ * (1 - (y : ℂ) * z)⁻¹ := by
        -- Clear denominators; `hne1` prevents `1 - y*z` from vanishing.
        have hd : (-1 + (y : ℂ) * z) ≠ 0 := by
          intro h
          apply hne1
          have : -(-1 + (y : ℂ) * z) = 0 := by
            simpa using congrArg Neg.neg h
          simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
            mul_left_comm] using this
        field_simp [hy0C, hz0, hsub2, hne1]
        have hden : (y : ℂ) * z - 1 ≠ 0 := by
          -- `y * z - 1 = -1 + y * z`.
          simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
            mul_left_comm] using hd
        field_simp [hden]
        ring_nf
      exact hL.trans hR.symm
    simpa [Complex.real_smul, this]
  -- Put everything together.
  calc
    (∫ t, (1 / ((t : ℂ) - z)) ∂(supportElimMeasure μ)) =
        ∫ y, (1 / (((supportElimInv y : ℝ) : ℂ) - z))
          ∂((μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ).withDensity supportElimWeight) := hmap
    _ =
        ∫ y,
          (supportElimWeight y).toReal • (1 / (((supportElimInv y : ℝ) : ℂ) - z))
          ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) := hwd
    _ =
        ∫ y,
          ((1 / (y : ℂ)) - (1 / ((y : ℂ) - z⁻¹)))
            ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) := by
          exact MeasureTheory.integral_congr_ae hEq

end

end

end Quantum.TraceInequality.Loewner

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set

open scoped UpperHalfPlane

noncomputable section



/-- The Stieltjes transform of the support-elimination transform of `μ`, evaluated on the upper
half-plane, equals the integral of `1/y - 1/(y - z⁻¹)` over the outside part `[-1, 1]ᶜ`. -/
theorem stieltjes_supportElimMeasure_eq_integral_diff (μ : Measure ℝ) (z : ℍ) :
    stieltjes (supportElimMeasure μ) z =
      ∫ y, ((1 / (y : ℂ)) - (1 / ((y : ℂ) - (z : ℂ)⁻¹)))
        ∂(μ.restrict (Set.Icc (-1 : ℝ) 1)ᶜ) := by
  have hz : ((z : ℂ).im) ≠ 0 := ne_of_gt z.coe_im_pos
  -- Step 50 works with `z : ℂ`; we specialize at the coercion of `z : ℍ`.
  simpa [stieltjes] using
    (integral_supportElimMeasure_stieltjesKernel_eq_integral_diff (μ := μ) (z := (z : ℂ)) hz)

end

end Quantum.TraceInequality.Loewner

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set

noncomputable section

open scoped NNReal



/--
After support elimination, the Cayley push-forward ratio functional is the
Koranyi-kernel `lintegral`.
-/
theorem ratioFunctional_cayleyPushforward_supportElimMeasure_eq_lintegral_koranyiKernel
    (μ : FiniteMeasure ℝ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ((ratioFunctional
          (cayleyPushforward
            (⟨supportElimMeasure (μ : Measure ℝ),
                ⟨lt_of_le_of_lt (supportElimMeasure_univ_le (μ := (μ : Measure ℝ)))
                    (measure_lt_top (μ := (μ : Measure ℝ)) Set.univ)⟩⟩ : FiniteMeasure ℝ))
          (Real.toNNReal (cayley x))) : ENNReal) =
      ∫⁻ t, (Real.toNNReal (koranyiKernel x t) : ENNReal)
          ∂(supportElimMeasure (μ : Measure ℝ)) := by
  -- Apply Step 18 with the automatic support property (Step 26).
  have hsupp : (supportElimMeasure (μ : Measure ℝ)) (Set.Ioo (-1 : ℝ) 1)ᶜ = 0 :=
    supportElimMeasure_compl_Ioo (μ := (μ : Measure ℝ))
  simpa using
    (ratioFunctional_cayleyPushforward_eq_lintegral_koranyiKernel
        (μ := (⟨supportElimMeasure (μ : Measure ℝ),
          ⟨lt_of_le_of_lt (supportElimMeasure_univ_le (μ := (μ : Measure ℝ)))
              (measure_lt_top (μ := (μ : Measure ℝ)) Set.univ)⟩⟩ : FiniteMeasure ℝ))
        (hμ := hsupp) (x := x) hx)

end

end Quantum.TraceInequality.Loewner
