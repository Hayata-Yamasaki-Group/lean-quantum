import Quantum.TraceInequality.LiebAndo.LownerHeinzTheorem
import Quantum.TraceInequality.TraceFunctionMonotonicity.LownerHeinzTheorem
import Quantum.TraceInequality.HansenPedersen.LownerHeinzTheorem
import Quantum.TraceInequality.HiaiPetz.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheoremRetained
import Mathlib.Analysis.InnerProductSpace.PiL2
import Quantum.TraceInequality.LownerHeinz.ReciprocalRetained

/-!
# Degeneracy of the unrestricted operator-convexity predicates

The pinned Mathlib real CFC returns zero on non-self-adjoint inputs. Requiring the
convexity inequality for every algebra element therefore forces the scalar function
itself to be zero. The localized predicates retain nonzero examples, such as `x²`.
-/

open CFC
namespace LownerHeinzCore
universe u
variable {𝓐 : Type u} [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
variable [Nontrivial 𝓐]
local instance : ContinuousSMul ℝ ℂ := ⟨by
  simpa only [Complex.real_smul] using
    (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd⟩
local instance : ContinuousSMul ℂ 𝓐 := by infer_instance
local instance : IsScalarTower ℝ ℂ 𝓐 := Real.isScalarTower (E := 𝓐) (A := ℂ)

omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] in
private lemma not_sa (z : ℂ) (hz : z.im ≠ 0) :
    ¬ IsSelfAdjoint (algebraMap ℂ 𝓐 z) := by
  intro h
  have hstar : star z = z := (FaithfulSMul.algebraMap_injective ℂ 𝓐) (by
    simpa only [Algebra.algebraMap_eq_smul_one, star_smul, star_one] using h.star_eq)
  have him := congrArg Complex.im hstar
  simp only [Complex.star_def, Complex.conj_im] at him
  exact hz (by linarith)

omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
private lemma combo (a b : ℂ) (t : ℝ) :
    (1 - t) • algebraMap ℂ 𝓐 a + t • algebraMap ℂ 𝓐 b =
      algebraMap ℂ 𝓐 ((1 - t) • a + t • b) := by
  simp only [Algebra.algebraMap_eq_smul_one, smul_assoc, add_smul]

/-- The unrestricted predicate forces `f = 0` on every nontrivial C*-algebra.
The two midpoint tests use scalar elements `(x ± i) • 1` and `x • 1`, `(x + 2i) • 1`.
No continuity assumption on `f` is needed: real scalar elements have singleton spectra. -/
theorem OperatorConvex.eq_zero_of_nontrivial {f : ℝ → ℝ}
    (hf : OperatorConvex (𝓐 := 𝓐) f) : ∀ x, f x = 0 := by
  intro x
  have hplus := not_sa (𝓐 := 𝓐) ((x : ℂ) + Complex.I) (by simp)
  have hminus := not_sa (𝓐 := 𝓐) ((x : ℂ) - Complex.I) (by simp)
  have htwo := not_sa (𝓐 := 𝓐) ((x : ℂ) + 2 * Complex.I) (by simp)
  have havg : (1 - (1 / 2 : ℝ)) • ((x : ℂ) + Complex.I) +
      (1 / 2 : ℝ) • ((x : ℂ) - Complex.I) = (x : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  have havg' : (1 - (1 / 2 : ℝ)) • (x : ℂ) +
      (1 / 2 : ℝ) • ((x : ℂ) + 2 * Complex.I) = (x : ℂ) + Complex.I := by
    apply Complex.ext <;> simp; ring
  have hreal : algebraMap ℂ 𝓐 (x : ℂ) = algebraMap ℝ 𝓐 x := by
    exact IsScalarTower.algebraMap_apply ℝ ℂ 𝓐 x |>.symm
  have hupper := hf (A := algebraMap ℂ 𝓐 ((x : ℂ) + Complex.I))
    (B := algebraMap ℂ 𝓐 ((x : ℂ) - Complex.I)) (t := 1 / 2) (by norm_num) (by norm_num)
  dsimp only [cfcR] at hupper
  rw [combo, havg, hreal, cfc_algebraMap,
    cfc_apply_of_not_predicate _ hplus, cfc_apply_of_not_predicate _ hminus] at hupper
  simp only [smul_zero, add_zero] at hupper
  have hlower := hf (A := algebraMap ℂ 𝓐 (x : ℂ))
    (B := algebraMap ℂ 𝓐 ((x : ℂ) + 2 * Complex.I)) (t := 1 / 2) (by norm_num) (by norm_num)
  dsimp only [cfcR] at hlower
  rw [combo, havg', cfc_apply_of_not_predicate _ hplus,
    cfc_apply_of_not_predicate _ htwo, hreal, cfc_algebraMap] at hlower
  have hlower' : 0 ≤ algebraMap ℝ 𝓐 (f x) := by
    have := smul_le_smul_of_nonneg_left hlower (show (0 : ℝ) ≤ 2 by norm_num)
    norm_num [smul_smul] at this ⊢
    exact this
  exact (FaithfulSMul.algebraMap_injective ℝ 𝓐) (by
    simpa using le_antisymm hupper hlower')
end LownerHeinzCore

namespace LownerHeinzCore
universe u
open scoped ComplexOrder

/-- Uniform unrestricted operator convexity forces the zero function. -/
theorem OperatorConvexAll.eq_zero {f : ℝ → ℝ} (hf : OperatorConvexAll.{u} f) : f = 0 := by
  exact funext (OperatorConvex.eq_zero_of_nontrivial
    (𝓐 := EuclideanSpace ℂ (ULift.{u} Unit) →L[ℂ] EuclideanSpace ℂ (ULift.{u} Unit)) hf)

/-- The unrestricted concavity predicate also forces every value to vanish. -/
theorem OperatorConcave.eq_zero_of_nontrivial
    {𝓐 : Type u} [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐]
    {f : ℝ → ℝ} (hf : OperatorConcave (𝓐 := 𝓐) f) : ∀ x, f x = 0 := by
  intro x
  have h := OperatorConvex.eq_zero_of_nontrivial hf x
  exact neg_eq_zero.mp h

/-- Uniform unrestricted operator concavity forces the zero function. -/
theorem OperatorConcaveAll.eq_zero {f : ℝ → ℝ} (hf : OperatorConcaveAll.{u} f) : f = 0 := by
  exact funext (OperatorConcave.eq_zero_of_nontrivial
    (𝓐 := EuclideanSpace ℂ (ULift.{u} Unit) →L[ℂ] EuclideanSpace ℂ (ULift.{u} Unit)) hf)

/-- The zero function satisfies the unrestricted predicate. -/
theorem OperatorConvex.zero
    {𝓐 : Type u} [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] :
    OperatorConvex (𝓐 := 𝓐) (0 : ℝ → ℝ) := by
  intro A B t _ _
  simp [cfcR]
end LownerHeinzCore

namespace LownerHeinzTheorem
universe u

/-- Uniform unrestricted operator convexity forces the zero function. -/
theorem OperatorConvexAll.eq_zero {f : ℝ → ℝ} (hf : OperatorConvexAll.{u} f) : f = 0 := by
  exact funext (LownerHeinzCore.OperatorConvex.eq_zero_of_nontrivial
    (hf (K := EuclideanSpace ℂ (ULift.{u} Unit))))

/-- Uniform unrestricted operator concavity forces the zero function. -/
theorem OperatorConcaveAll.eq_zero {f : ℝ → ℝ} (hf : OperatorConcaveAll.{u} f) : f = 0 := by
  exact funext (LownerHeinzCore.OperatorConcave.eq_zero_of_nontrivial
    (hf (K := EuclideanSpace ℂ (ULift.{u} Unit))))

/-- Nonvacuity canary: the square function is operator convex on the nonnegative half-line. -/
theorem operatorConvexOnAll_Ici_sq :
    OperatorConvexOnAll.{u} (Set.Ici 0) (fun x : ℝ ↦ x ^ (2 : ℕ)) := by
  intro K _ _ _ _
  simpa only [Real.rpow_two] using
    (power_Icc_one_two_operatorConvexOn_Ici (ℋ := K) 2 (by constructor <;> norm_num))

/-- The localized canary is a nonzero function. -/
theorem sq_ne_zero : (fun x : ℝ ↦ x ^ (2 : ℕ)) ≠ 0 := by
  intro h
  have := congrFun h 1
  norm_num at this
end LownerHeinzTheorem
