import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Quantum.Analysis.Real.PositiveCayley
import Quantum.Analysis.CStar.UnitIntervalKernel

namespace Quantum.TraceInequality.Loewner

open Set Filter

open scoped Topology

noncomputable section

instance instUnitizationFiniteDimensional
    {A : Type*} [NonUnitalCStarAlgebra A] [FiniteDimensional ℂ A] :
    FiniteDimensional ℂ (Unitization ℂ A) := by
  change FiniteDimensional ℂ (ℂ × A)
  infer_instance

theorem spectrum_lmul_eq {K A : Type*} [Field K] [Ring A] [Algebra K A]
    (a : A) : spectrum K ((Algebra.lmul K A) a : Module.End K A) = spectrum K a := by
  ext r
  rw [spectrum.mem_iff, spectrum.mem_iff]
  have hmap :
      algebraMap K (Module.End K A) r - (Algebra.lmul K A) a =
        (Algebra.lmul K A) (algebraMap K A r - a) := by
    ext x
    simp [Algebra.coe_lmul_eq_mul, Algebra.smul_def]
  rw [hmap, Algebra.lmul_isUnit_iff]

theorem spectrum_finite_of_finiteDimensional
    {K A : Type*} [Field K] [Ring A] [Algebra K A]
    [FiniteDimensional K A] (a : A) :
    (spectrum K a).Finite := by
  rw [← spectrum_lmul_eq (K := K) (A := A) a]
  exact Module.End.finite_spectrum ((Algebra.lmul K A) a : Module.End K A)

theorem spectrum_real_finite_of_finiteDimensional_complex
    {B : Type*} [Ring B] [Algebra ℂ B] [IsScalarTower ℝ ℂ B]
    [FiniteDimensional ℂ B] (b : B) :
    (spectrum ℝ b).Finite := by
  rw [← spectrum.preimage_algebraMap ℂ]
  exact (spectrum_finite_of_finiteDimensional (K := ℂ) (A := B) b).preimage
    (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

theorem continuousOn_unitToPositiveCayley_of_subset_Ioo {s : Set ℝ}
    (hs : s ⊆ Set.Ioo (-1 : ℝ) 1) :
    ContinuousOn unitToPositiveCayley s := by
  intro x hx
  have hxI : x ∈ Set.Ioo (-1 : ℝ) 1 := hs hx
  have hden : 1 - x ≠ 0 := by linarith [hxI.2]
  unfold unitToPositiveCayley
  exact ((continuousAt_const.add continuousAt_id).div
    (continuousAt_const.sub continuousAt_id) hden).continuousWithinAt

theorem unitToPositiveCayley_eq_one_add_two_kernel {y : ℝ}
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    unitToPositiveCayley y =
      1 + 2 * unitIntervalOperatorKernel (-1 : ℝ) y := by
  have hden : 1 - y ≠ 0 := by linarith [hy.2]
  unfold unitToPositiveCayley
  have hk : unitIntervalOperatorKernel (-1 : ℝ) y = y / (1 - y) := by
    unfold unitIntervalOperatorKernel
    ring_nf
  rw [hk]
  field_simp [hden]
  ring_nf

end

end Quantum.TraceInequality.Loewner
