/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.GeneralizedPerspectiveFunction
import Quantum.TraceInequality.HilbertSchmidtOperatorSpace
import Quantum.QuantumMechanics.QuantumState
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.LinearAlgebra.Lagrange

namespace LiebAndoTrace

universe u

open QuantumState LownerHeinzTheorem
open GeneralizedPerspectiveFunction
open HilbertSchmidtOperatorSpace
open Module.End Polynomial

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [FiniteDimensional ℂ ℋ] [Nontrivial ℋ]
/-! ### Trace maps and HS right-multiplication bridge -/

noncomputable instance instCFCRealSelfAdjointMop :
    ContinuousFunctionalCalculus ℝ ((B ℋ)ᵐᵒᵖ) IsSelfAdjoint :=
  (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
    (A := (B ℋ)ᵐᵒᵖ)).toContinuousFunctionalCalculus

omit [Nontrivial ℋ] in
lemma rightMulHS_nonneg {A : B ℋ} (hA0 : 0 ≤ A) :
    0 ≤ rightMulHS (ℋ := ℋ) A := by
  let sqrtA : B ℋ := A ^ ((1 : ℝ) / 2)
  have hsqrt_sq_pow : sqrtA ^ (2 : ℕ) = A := by
    calc
      sqrtA ^ (2 : ℕ) = sqrtA ^ (2 : ℝ) := by
            simpa using (CFC.rpow_natCast sqrtA 2).symm
      _ = A ^ (((1 : ℝ) / 2) * 2) := by
            simpa [sqrtA] using
              (CFC.rpow_rpow_of_exponent_nonneg A ((1 : ℝ) / 2) 2
                (by positivity) (by positivity) (ha₂ := hA0))
      _ = A ^ (1 : ℝ) := by ring_nf
      _ = A := by simpa using CFC.rpow_one A
  have hsqrt_sq : sqrtA * sqrtA = A := by
    simpa [pow_two] using hsqrt_sq_pow
  have hsqrt_sa : IsSelfAdjoint sqrtA := IsSelfAdjoint.of_nonneg (by
    simp [sqrtA])
  let S : B (HSOp ℋ) := rightMulHS (ℋ := ℋ) sqrtA
  have hSstar : star S = S := by
    change star (rightMulHS (ℋ := ℋ) sqrtA) = rightMulHS (ℋ := ℋ) sqrtA
    simp [hsqrt_sa.star_eq]
  have hSq : rightMulHS (ℋ := ℋ) A = star S * S := by
    calc
      rightMulHS (ℋ := ℋ) A = rightMulHS (ℋ := ℋ) (sqrtA * sqrtA) := by simp [hsqrt_sq]
      _ = S * S := by simp [S]
      _ = star S * S := by simp [hSstar]
  simp [hSq]

omit [Nontrivial ℋ] in
@[gcongr]
private lemma rightMulHS_le_rightMulHS {A B : (ℋ →L[ℂ] ℋ)} (hAB : A ≤ B) :
    rightMulHS (ℋ := ℋ) A ≤ rightMulHS (ℋ := ℋ) B := by
  have hnonneg : 0 ≤ rightMulHS (ℋ := ℋ) (B - A) :=
    rightMulHS_nonneg (ℋ := ℋ) (sub_nonneg.mpr hAB)
  have hsub :
      rightMulHS (ℋ := ℋ) B - rightMulHS (ℋ := ℋ) A =
        rightMulHS (ℋ := ℋ) (B - A) := by
    ext T
    simpa [sub_eq_add_neg] using (mul_add (toOp T) B (-A)).symm
  exact sub_nonneg.mp (by simpa [hsub] using hnonneg)

lemma rightMulHS_pdSet {A : B ℋ} (hA : A ∈ pdSet (ℋ := ℋ)) :
    rightMulHS (ℋ := ℋ) A ∈ pdSet (ℋ := HSOp ℋ) := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  have hright_sa : IsSelfAdjoint (rightMulHS (ℋ := ℋ) A) := by
    change star (rightMulHS (ℋ := ℋ) A) = rightMulHS (ℋ := ℋ) A
    simp [hA_sa.star_eq]
  letI : Nontrivial (HSOp ℋ) := by
    delta HSOp
    infer_instance
  letI : Nontrivial (B (HSOp ℋ)) := inferInstance
  refine ⟨hright_sa, ?_⟩
  rcases (CFC.exists_pos_algebraMap_le_iff (A := B ℋ) (a := A) (ha :=
      hA_sa)).2 hA_spec
    with ⟨r, hr, hrA⟩
  refine (CFC.exists_pos_algebraMap_le_iff
    (A := B (HSOp ℋ)) (a := rightMulHS (ℋ := ℋ) A) (ha := hright_sa)).1 ?_
  refine ⟨r, hr, ?_⟩
  simpa [Algebra.algebraMap_eq_smul_one, rightMulHS_real_smul_one (ℋ := ℋ) (r := r)] using
    rightMulHS_le_rightMulHS (ℋ := ℋ) hrA

/-! ### The `phiK` functional and CFC evaluation helpers -/
/-- The functional `T ↦ Re ⟪K*, T K*⟫` on operators on the Hilbert–Schmidt space, where `K*`
is regarded as a Hilbert–Schmidt vector (`ofOp (star K)`). -/
noncomputable def phiK (K : B ℋ) (T : B (HSOp ℋ)) : ℝ :=
  Complex.re (inner ℂ (ofOp (star K)) (T (ofOp (star K))))

omit [Nontrivial ℋ] in
lemma phiK_nonneg (K : B ℋ) {T : B (HSOp ℋ)} (hT : 0 ≤ T) :
    0 ≤ phiK (ℋ := ℋ) K T := by
  dsimp [phiK]
  have hpos : T.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive T).1 hT
  have hnonneg : 0 ≤ Complex.re (inner ℂ (T (ofOp (star K))) (ofOp (star K))) := by
    exact ((ContinuousLinearMap.isPositive_iff_complex T).1 hpos (ofOp (star K))).2
  have hre :
      Complex.re (inner ℂ (ofOp (star K)) (T (ofOp (star K)))) =
        Complex.re (inner ℂ (T (ofOp (star K))) (ofOp (star K))) := by
    simpa using
      (inner_re_symm (𝕜 := ℂ) (x := ofOp (star K)) (y := T (ofOp (star K))))
  rw [hre]
  exact hnonneg

omit [Nontrivial ℋ] in
lemma phiK_add (K : B ℋ) (T S : B (HSOp ℋ)) :
    phiK (ℋ := ℋ) K (T + S) = phiK (ℋ := ℋ) K T + phiK (ℋ := ℋ) K S := by
  simp [phiK, inner_add_right, Complex.add_re]

omit [Nontrivial ℋ] in
lemma phiK_smul (K : B ℋ) (r : ℝ) (T : B (HSOp ℋ)) :
    phiK (ℋ := ℋ) K (r • T) = r * phiK (ℋ := ℋ) K T := by
  rw [phiK]
  change Complex.re (inner ℂ (ofOp (star K)) (r • T (ofOp (star K)))) =
    r * Complex.re (inner ℂ (ofOp (star K)) (T (ofOp (star K))))
  rw [show inner ℂ (ofOp (star K)) (r • T (ofOp (star K))) =
      (r : ℂ) * inner ℂ (ofOp (star K)) (T (ofOp (star K))) by
        simpa using inner_smul_right (ofOp (star K)) (T (ofOp (star K))) (r : ℂ)]
  simp

omit [Nontrivial ℋ] in
lemma phiK_mono (K : B ℋ) {T S : B (HSOp ℋ)} (hTS : T ≤ S) :
    phiK (ℋ := ℋ) K T ≤ phiK (ℋ := ℋ) K S := by
  have hnonneg :
      0 ≤ S + (-1 : ℝ) • T := by
    simpa [sub_eq_add_neg] using (sub_nonneg.mpr hTS)
  have hphi_nonneg := phiK_nonneg (ℋ := ℋ) K hnonneg
  have hrewrite :
      phiK (ℋ := ℋ) K (S + (-1 : ℝ) • T) =
        phiK (ℋ := ℋ) K S - phiK (ℋ := ℋ) K T := by
    rw [phiK_add, phiK_smul]
    ring
  linarith [hrewrite ▸ hphi_nonneg]

attribute [gcongr] phiK_mono

lemma re_inner_nonneg_of_nonneg
    {𝓚 : Type*} [NormedAddCommGroup 𝓚] [InnerProductSpace ℂ 𝓚]
    {T : B 𝓚} (hT : 0 ≤ T) :
    ∀ x : 𝓚, 0 ≤ Complex.re (inner ℂ x (T x)) := by
  intro x
  have hpos : T.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive T).1 hT
  have hnonneg : 0 ≤ Complex.re (inner ℂ (T x) x) :=
    ((ContinuousLinearMap.isPositive_iff_complex T).1 hpos x).2
  have hre :
      Complex.re (inner ℂ x (T x)) = Complex.re (inner ℂ (T x) x) := by
    simpa using (inner_re_symm (𝕜 := ℂ) (x := x) (y := T x))
  rw [hre]
  exact hnonneg

private lemma aeval_apply_of_mem_eigenspace_realpoly
    {𝓚 : Type*} [NormedAddCommGroup 𝓚] [InnerProductSpace ℂ 𝓚]
    {T : B 𝓚} {r : ℝ} {x : 𝓚}
    (hx : T x = (r : ℂ) • x) (p : ℝ[X]) :
    Polynomial.aeval T (p.map (algebraMap ℝ ℂ)) x =
      ((p.map (algebraMap ℝ ℂ)).eval (r : ℂ)) • x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hmap :
      Polynomial.aeval T (p.map (algebraMap ℝ ℂ)) x =
        Polynomial.aeval (T : L 𝓚) (p.map (algebraMap ℝ ℂ)) x := by
    simpa using
      congrArg (fun F : L 𝓚 => F x)
        (Polynomial.map_aeval_eq_aeval_map
          (R := ℂ) (S := B 𝓚) (T := ℂ) (U := L 𝓚)
          (φ := RingHom.id ℂ) (ψ := ContinuousLinearMap.toLinearMapRingHom)
          (h := by ext z; rfl) (p := p.map (algebraMap ℝ ℂ)) (a := T))
  rw [hmap]
  simpa using
    (Module.End.aeval_apply_of_hasEigenvector
      (f := (T : L 𝓚)) (p := p.map (algebraMap ℝ ℂ)) (μ := (r : ℂ)) (x := x)
        ⟨Module.End.mem_eigenspace_iff.mpr hx, hx0⟩)

lemma cfcR_apply_of_mem_eigenspace_real
    {𝓚 : Type*} [NormedAddCommGroup 𝓚] [InnerProductSpace ℂ 𝓚] [CompleteSpace 𝓚]
    [FiniteDimensional ℂ 𝓚]
    [ContinuousFunctionalCalculus ℝ (B 𝓚) IsSelfAdjoint]
    (f : ℝ → ℝ) {T : B 𝓚} (hT : IsSelfAdjoint T) {r : ℝ} {x : 𝓚}
    (hx : T x = (r : ℂ) • x) :
    cfcR (ℋ := 𝓚) f T x = (f r : ℂ) • x := by
  haveI : IsScalarTower ℝ ℂ (B 𝓚) := RestrictScalars.isScalarTower ℝ ℂ
      (B 𝓚)
  classical
  by_cases hx0 : x = 0
  · simp [hx0]
  have hspecCfin : Set.Finite (spectrum ℂ T) := by
    change Set.Finite
      (spectrum ℂ ((Module.End.toContinuousLinearMap 𝓚) (T : L 𝓚)))
    simpa using Module.End.finite_spectrum (K := ℂ) (V := 𝓚) (T : L 𝓚)
  have hspecRfin : Set.Finite (spectrum ℝ T) := by
    rw [← spectrum.preimage_algebraMap ℂ]
    exact hspecCfin.preimage (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn
  let s : Finset ℝ := hspecRfin.toFinset
  let q : ℝ[X] := Lagrange.interpolate s id fun y ↦ f y
  have hq_spec : (spectrum ℝ T).EqOn f q.eval := by
    intro y hy
    symm
    simpa [q] using
      (Lagrange.eval_interpolate_at_node
        (s := s) (v := id) (r := fun z ↦ f z) (i := y)
        (hvs := fun _ _ _ _ h => h) (by simpa [s] using hy))
  have hr_spec : r ∈ spectrum ℝ T := spectrum.of_algebraMap_mem ℂ <| by
    change (r : ℂ) ∈
      spectrum ℂ ((Module.End.toContinuousLinearMap 𝓚) (T : L 𝓚))
    simpa using
      (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr hx, hx0⟩).mem_spectrum
  calc
    cfcR (ℋ := 𝓚) f T x = cfcR (ℋ := 𝓚) q.eval T x := by
      rw [show cfcR (ℋ := 𝓚) f T = cfcR (ℋ := 𝓚) q.eval T by
        simpa [cfcR] using (cfc_congr (a := T) (f := f) (g := q.eval) hq_spec)]
    _ = Polynomial.aeval T q x := by
      rw [show cfcR (ℋ := 𝓚) q.eval T = Polynomial.aeval T q by
        simpa [cfcR] using (cfc_polynomial (p := IsSelfAdjoint) (q := q) (a := T) hT)]
    _ = Polynomial.aeval T (q.map (algebraMap ℝ ℂ)) x := by
      symm
      simp
    _ = ((q.map (algebraMap ℝ ℂ)).eval (r : ℂ)) • x := by
      simpa using aeval_apply_of_mem_eigenspace_realpoly hx q
    _ = (f r : ℂ) • x := by
      congr 1
      rw [Polynomial.eval_map_algebraMap]
      calc
        Polynomial.aeval (algebraMap ℝ ℂ r) q = ((Polynomial.eval r q : ℝ) : ℂ) := by
          simpa using
            (Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) (x := r) (p := q))
        _ = (f r : ℂ) := by
          simpa using congrArg (fun t : ℝ => (t : ℂ)) (hq_spec hr_spec).symm

end LiebAndoTrace
