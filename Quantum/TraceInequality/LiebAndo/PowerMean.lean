/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.LiebAndo.LiebTrace.Bridge
import Quantum.TraceInequality.LiebTrace.Bridge
import Quantum.TraceInequality.LiebAndo.GeneralizedPerspectiveFunction

namespace LiebAndoTrace

universe u

open LownerHeinzTheorem
open GeneralizedPerspectiveFunction
open HilbertSchmidtOperatorSpace
open OperatorGeometricMean
open Module.End Polynomial

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [FiniteDimensional ℂ ℋ] [Nontrivial ℋ]

-- Under transparency-respecting defeq, synthesizing `NonnegSpectrumClass ℝ (ℋ →L[ℂ] ℋ)`
-- from scratch exceeds the default typeclass budget and is re-run at every
-- `nonneg_iff_spectrum_nonneg`-style step (it is not cached across tactic steps).
-- Register the C⋆-algebra instance once so each search is a direct hit.
local instance instNonnegSpectrumClassRealContinuousLinearMapComplexId_quantum :
    NonnegSpectrumClass ℝ (ℋ →L[ℂ] ℋ) := CStarAlgebra.instNonnegSpectrumClass

/-! ### HS middle operator real-power decomposition -/
/-- Real powers commute with left multiplication on `HSOp ℋ`. -/
private lemma leftMulHS_cfcR_rpow {p : ℝ} {A : (ℋ →L[ℂ] ℋ)} (hA0 : 0 ≤ A)
    (hne : ∀ x ∈ spectrum ℝ A, x ≠ 0) :
    cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ p) (leftMulHS (ℋ := ℋ) A) =
      leftMulHS (ℋ := ℋ) (A ^ p) := by
  rw [show leftMulHS (ℋ := ℋ) (A ^ p) =
      leftMulHS (ℋ := ℋ) (cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ p) A) by
    congr
    simpa [cfcR] using
      (CFC.rpow_eq_cfc_real (A := (ℋ →L[ℂ] ℋ)) (a := A) (y := p) (ha := hA0))]
  exact (leftMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ p) A (IsSelfAdjoint.of_nonneg hA0)
    (fun x hx => (Real.continuousAt_rpow_const x p
      (Or.inl (hne x hx))).continuousWithinAt)).symm

/-- Real powers commute with right multiplication on `HSOp ℋ`. -/
private lemma rightMulHS_cfcR_rpow {p : ℝ} {B : (ℋ →L[ℂ] ℋ)} (hB0 : 0 ≤ B)
    (hne : ∀ x ∈ spectrum ℝ B, x ≠ 0) :
    cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ p) (rightMulHS (ℋ := ℋ) B) =
      rightMulHS (ℋ := ℋ) (B ^ p) := by
  rw [show rightMulHS (ℋ := ℋ) (B ^ p) =
      rightMulHS (ℋ := ℋ) (cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ p) B) by
    congr
    simpa [cfcR] using
      (CFC.rpow_eq_cfc_real (A := (ℋ →L[ℂ] ℋ)) (a := B) (y := p) (ha := hB0))]
  exact (rightMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ p) B (IsSelfAdjoint.of_nonneg hB0)
    (fun x hx => (Real.continuousAt_rpow_const x p
      (Or.inl (hne x hx))).continuousWithinAt)).symm

omit [Nontrivial ℋ] in
/-- On a joint eigenvector of `leftMulHS A` and `rightMulHS C`, the real power of their product
acts as the product of their real powers. -/
private lemma cfcR_rpow_leftMul_rightMul_apply {s a b : ℝ} {A C : (ℋ →L[ℂ] ℋ)}
    (hA0 : 0 ≤ A) (hC0 : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) {x : HSOp ℋ}
    (hxa : leftMulHS (ℋ := ℋ) A x = (a : ℂ) • x)
    (hxb : rightMulHS (ℋ := ℋ) C x = (b : ℂ) • x) :
    cfcR (ℋ := HSOp ℋ) (fun t : ℝ ↦ t ^ s) (leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) C) x =
      (cfcR (ℋ := HSOp ℋ) (fun t : ℝ ↦ t ^ s) (leftMulHS (ℋ := ℋ) A) *
        cfcR (ℋ := HSOp ℋ) (fun t : ℝ ↦ t ^ s) (rightMulHS (ℋ := ℋ) C)) x := by
  have hleft_sa : IsSelfAdjoint (leftMulHS (ℋ := ℋ) A) :=
    IsSelfAdjoint.of_nonneg (leftMulHS_nonneg (ℋ := ℋ) hA0)
  have hright_sa : IsSelfAdjoint (rightMulHS (ℋ := ℋ) C) :=
    IsSelfAdjoint.of_nonneg (rightMulHS_nonneg (ℋ := ℋ) hC0)
  have hprod_sa : IsSelfAdjoint (leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) C) :=
    IsSelfAdjoint.of_nonneg ((leftMulHS_rightMulHS_commute (ℋ := ℋ) A C).mul_nonneg
      (leftMulHS_nonneg (ℋ := ℋ) hA0) (rightMulHS_nonneg (ℋ := ℋ) hC0))
  have hxprod :
      (leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) C) x = ((a * b : ℝ) : ℂ) • x := by
    rw [ContinuousLinearMap.mul_apply, hxb, ContinuousLinearMap.map_smul, hxa, smul_smul]
    congr 1
    push_cast
    ring
  rw [cfcR_apply_of_mem_eigenspace_real (𝓚 := HSOp ℋ) (fun t : ℝ ↦ t ^ s) hprod_sa hxprod,
    ContinuousLinearMap.mul_apply,
    cfcR_apply_of_mem_eigenspace_real (𝓚 := HSOp ℋ) (fun t : ℝ ↦ t ^ s) hright_sa hxb,
    ContinuousLinearMap.map_smul,
    cfcR_apply_of_mem_eigenspace_real (𝓚 := HSOp ℋ) (fun t : ℝ ↦ t ^ s) hleft_sa hxa,
    smul_smul, Real.mul_rpow ha hb]
  congr 1
  push_cast
  ring

omit [Nontrivial ℋ] in
/-- The real power of `leftMulHS A * rightMulHS C` is the product of the real powers. -/
private lemma cfcR_rpow_leftMul_rightMul {s : ℝ} {A C : (ℋ →L[ℂ] ℋ)}
    (hA0 : 0 ≤ A) (hC0 : 0 ≤ C) :
    cfcR (ℋ := HSOp ℋ) (fun t : ℝ ↦ t ^ s) (leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) C) =
      cfcR (ℋ := HSOp ℋ) (fun t : ℝ ↦ t ^ s) (leftMulHS (ℋ := ℋ) A) *
        cfcR (ℋ := HSOp ℋ) (fun t : ℝ ↦ t ^ s) (rightMulHS (ℋ := ℋ) C) := by
  let T0 : HSOp ℋ →ₗ[ℂ] HSOp ℋ :=
    (leftMulHS (ℋ := ℋ) A : HSOp ℋ →ₗ[ℂ] HSOp ℋ)
  let T1 : HSOp ℋ →ₗ[ℂ] HSOp ℋ :=
    (rightMulHS (ℋ := ℋ) C : HSOp ℋ →ₗ[ℂ] HSOp ℋ)
  let D : (HSOp ℋ →L[ℂ] HSOp ℋ) :=
    cfcR (ℋ := HSOp ℋ) (fun t : ℝ ↦ t ^ s) (leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) C) -
      cfcR (ℋ := HSOp ℋ) (fun t : ℝ ↦ t ^ s) (leftMulHS (ℋ := ℋ) A) *
        cfcR (ℋ := HSOp ℋ) (fun t : ℝ ↦ t ^ s) (rightMulHS (ℋ := ℋ) C)
  have hT0_symm : T0.IsSymmetric := by
    simpa [T0] using
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        (IsSelfAdjoint.of_nonneg (leftMulHS_nonneg (ℋ := ℋ) hA0)))
  have hT1_symm : T1.IsSymmetric := by
    simpa [T1] using
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        (IsSelfAdjoint.of_nonneg (rightMulHS_nonneg (ℋ := ℋ) hC0)))
  have hcomm : Commute T0 T1 := by
    change T0 * T1 = T1 * T0
    ext x
    simpa [T0, T1] using congrArg (fun F : (HSOp ℋ →L[ℂ] HSOp ℋ) => F x)
      (leftMulHS_rightMulHS_commute (ℋ := ℋ) A C).eq
  have htop :
      (⨆ α, ⨆ β, eigenspace T0 α ⊓ eigenspace T1 β) = ⊤ := by
    exact LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute
      hT0_symm hT1_symm hcomm
  have hjoint_ker :
      ∀ α β,
        eigenspace T0 α ⊓ eigenspace T1 β ≤
          LinearMap.ker (D : HSOp ℋ →ₗ[ℂ] HSOp ℋ) := by
    intro α β x hx
    rcases hx with ⟨hx0, hx1⟩
    rw [LinearMap.mem_ker]
    by_cases hxzero : x = 0
    · simp [D, hxzero]
    have hxv0 : Module.End.HasEigenvector T0 α x := ⟨hx0, hxzero⟩
    have hxv1 : Module.End.HasEigenvector T1 β x := ⟨hx1, hxzero⟩
    have hαeq : α = (α.re : ℂ) := by
      exact (RCLike.conj_eq_iff_re.mp
        (hT0_symm.conj_eigenvalue_eq_self (Module.End.hasEigenvalue_of_hasEigenvector hxv0))
        ).symm
    have hβeq : β = (β.re : ℂ) := by
      exact (RCLike.conj_eq_iff_re.mp
        (hT1_symm.conj_eigenvalue_eq_self (Module.End.hasEigenvalue_of_hasEigenvector hxv1))
        ).symm
    have hx0r : x ∈ eigenspace T0 (α.re : ℂ) := by
      rwa [hαeq] at hx0
    have hx1r : x ∈ eigenspace T1 (β.re : ℂ) := by
      rwa [hβeq] at hx1
    have hαnonneg : 0 ≤ α.re := by
      exact eigenvalue_nonneg_of_nonneg
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx0r, hxzero⟩)
        (fun y => by
          simpa [T0] using
            re_inner_nonneg_of_nonneg (T := leftMulHS (ℋ := ℋ) A)
              (leftMulHS_nonneg (ℋ := ℋ) hA0) y)
    have hβnonneg : 0 ≤ β.re := by
      exact eigenvalue_nonneg_of_nonneg
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx1r, hxzero⟩)
        (fun y => by
          simpa [T1] using
            re_inner_nonneg_of_nonneg (T := rightMulHS (ℋ := ℋ) C)
              (rightMulHS_nonneg (ℋ := ℋ) hC0) y)
    have hxa : leftMulHS (ℋ := ℋ) A x = (α.re : ℂ) • x := by
      simpa [T0] using Module.End.mem_eigenspace_iff.mp hx0r
    have hxb : rightMulHS (ℋ := ℋ) C x = (β.re : ℂ) • x := by
      simpa [T1] using Module.End.mem_eigenspace_iff.mp hx1r
    simpa [D] using
      sub_eq_zero.mpr (cfcR_rpow_leftMul_rightMul_apply hA0 hC0 hαnonneg hβnonneg hxa hxb)
  have hker_top : LinearMap.ker (D : HSOp ℋ →ₗ[ℂ] HSOp ℋ) = ⊤ := by
    apply top_unique
    rw [← htop]
    exact iSup_le fun α => iSup_le fun β => hjoint_ker α β
  have hDzero : D = 0 := by
    ext x
    exact LinearMap.congr_fun (LinearMap.ker_eq_top.mp hker_top) x
  exact sub_eq_zero.mp hDzero

private lemma hmiddle_leftMul_rightMul
    {s : ℝ} {A B : (ℋ →L[ℂ] ℋ)}
    (hA : A ∈ pdSet (ℋ := ℋ)) (hB : B ∈ pdSet (ℋ := ℋ)) :
    cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s)
        (cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) *
          leftMulHS (ℋ := ℋ) A *
          cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B)) =
      leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s)) := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  rcases hB with ⟨hB_sa, hB_spec⟩
  have hA0 : 0 ≤ A :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA_sa)).2
      fun _ hx => (hA_spec hx).le
  have hB0 : 0 ≤ B :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB_sa)).2
      fun _ hx => (hB_spec hx).le
  have hBunit : IsUnit B :=
    spectrum.isUnit_of_zero_notMem (R := ℝ) fun h0 =>
      (lt_irrefl (0 : ℝ)) (by simpa [Set.Ioi] using hB_spec h0)
  have hBnegOne :
      B ^ ((-1 : ℝ) / 2) * B ^ ((-1 : ℝ) / 2) = B ^ (-1 : ℝ) := by
    rw [← CFC.rpow_add hBunit]
    congr 1
    ring
  have hmid_prod :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) *
          leftMulHS (ℋ := ℋ) A *
          cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) =
        leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) := by
    rw [rightMulHS_cfcR_rpow hB0 fun x hx => ne_of_gt (hB_spec hx),
      (leftMulHS_rightMulHS_commute (ℋ := ℋ) A (B ^ ((-1 : ℝ) / 2))).eq.symm,
      mul_assoc,
      ← rightMulHS_mul (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) (B ^ ((-1 : ℝ) / 2)),
      hBnegOne]
  have hBinv0 : 0 ≤ B ^ (-1 : ℝ) := by
    simp
  have hBinv_unit : IsUnit (B ^ (-1 : ℝ)) := by
    rcases hBunit with ⟨u, rfl⟩
    simp [CFC.rpow_neg_one_eq_inv u (by simpa using hB0)]
  have hright_pow :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s)
          (rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))) =
        rightMulHS (ℋ := ℋ) (B ^ (-s)) := by
    rw [rightMulHS_cfcR_rpow hBinv0 fun x hx hx0 =>
      spectrum.zero_notMem (R := ℝ) hBinv_unit (by simpa [hx0] using hx)]
    congr 1
    simpa using (CFC.rpow_rpow (a := B) (-1 : ℝ) s hBunit (by norm_num) hB0)
  rw [hmid_prod, ← leftMulHS_cfcR_rpow hA0 fun x hx => ne_of_gt (hA_spec hx), ← hright_pow]
  exact cfcR_rpow_leftMul_rightMul hA0 hBinv0

/-! ### Operator power means rewritten as Lieb traces -/
-- The identification lemma expands a large `HSOp`-valued generalized perspective term.
lemma phiK_operatorPowerMean_eq_liebTraceMap
    {s : ℝ} (K A B : (ℋ →L[ℂ] ℋ)) (hA : A ∈ pdSet (ℋ := ℋ)) (hB : B ∈ pdSet (ℋ := ℋ)) :
    phiK (ℋ := ℋ) K
        (operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B)) =
      liebTraceMap (ℋ := ℋ) s K A B := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  rcases hB with ⟨hB_sa, hB_spec⟩
  have hB0 : 0 ≤ B := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB_sa)).2
      (by intro x hx; exact (hB_spec hx).le)
  have hright_half :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) =
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) := by
    rw [show rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) =
        rightMulHS (ℋ := ℋ) (cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) B) by
      congr
      simpa [cfcR] using
        (CFC.rpow_eq_cfc_real (A := (ℋ →L[ℂ] ℋ)) (a := B) (y := (1 : ℝ) / 2) (ha := hB0))]
    exact (rightMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) B hB_sa
        (by
          intro x hx
          exact (Real.continuousAt_rpow_const x ((1 : ℝ) / 2)
            (Or.inr (by positivity))).continuousWithinAt)).symm
  have hBunit : IsUnit B := by
    refine spectrum.isUnit_of_zero_notMem (R := ℝ) ?_
    intro h0
    exact (lt_irrefl (0 : ℝ)) (by simpa [Set.Ioi] using hB_spec h0)
  have hBpow :
      B ^ ((1 : ℝ) / 2) * B ^ (-s) * B ^ ((1 : ℝ) / 2) = B ^ (1 - s) := by
    calc
      B ^ ((1 : ℝ) / 2) * B ^ (-s) * B ^ ((1 : ℝ) / 2)
          = B ^ (((1 : ℝ) / 2) + (-s)) * B ^ ((1 : ℝ) / 2) := by
              rw [← CFC.rpow_add hBunit]
      _ = B ^ ((((1 : ℝ) / 2) + (-s)) + ((1 : ℝ) / 2)) := by
              rw [← CFC.rpow_add hBunit]
      _ = B ^ (1 - s) := by ring_nf
  have hmiddle :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s)
          (cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) *
            leftMulHS (ℋ := ℋ) A *
            cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B)) =
        leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s)) := by
    exact hmiddle_leftMul_rightMul (ℋ := ℋ) (s := s) ⟨hA_sa, hA_spec⟩ ⟨hB_sa, hB_spec⟩
  have happly :
      operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B) (ofOp (star K)) =
        ofOp (A ^ s * star K * B ^ (1 - s)) := by
    have hcomm_half :
        Commute (leftMulHS (ℋ := ℋ) (A ^ s)) (rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))) :=
      leftMulHS_rightMulHS_commute (ℋ := ℋ) (A ^ s) (B ^ ((1 : ℝ) / 2))
    have hright_pow :
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
            rightMulHS (ℋ := ℋ) (B ^ (-s)) *
            rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) =
          rightMulHS (ℋ := ℋ) (B ^ (1 - s)) := by
      calc
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
            rightMulHS (ℋ := ℋ) (B ^ (-s)) *
            rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))
            =
          rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2) * B ^ (-s) * B ^ ((1 : ℝ) / 2)) := by
            simp [mul_assoc]
        _ = rightMulHS (ℋ := ℋ) (B ^ (1 - s)) := by rw [hBpow]
    have hreorder :
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
            (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s))) *
            rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) =
          leftMulHS (ℋ := ℋ) (A ^ s) *
            (rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
              rightMulHS (ℋ := ℋ) (B ^ (-s)) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))) := by
      calc
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
            (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s))) *
            rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))
            =
          ((rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
              leftMulHS (ℋ := ℋ) (A ^ s)) *
            rightMulHS (ℋ := ℋ) (B ^ (-s))) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) := by
                simp [mul_assoc]
        _ =
          ((leftMulHS (ℋ := ℋ) (A ^ s) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))) *
            rightMulHS (ℋ := ℋ) (B ^ (-s))) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) := by
                rw [hcomm_half.eq]
        _ =
          leftMulHS (ℋ := ℋ) (A ^ s) *
            (rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
              rightMulHS (ℋ := ℋ) (B ^ (-s)) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))) := by
                simp [mul_assoc]
    calc
      operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B) (ofOp (star K))
        =
          (rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
              (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s))) *
              rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2))) (ofOp (star K)) := by
            rw [OperatorGeometricMean.operatorPowerMean, generalizedPerspective,
              GeneralizedPerspectiveFunction.hSqrt, GeneralizedPerspectiveFunction.hInvSqrt]
            simp only [Real.rpow_one]
            rw [hmiddle]
            rw [hright_half]
      _ =
          (leftMulHS (ℋ := ℋ) (A ^ s) *
              (rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) *
                rightMulHS (ℋ := ℋ) (B ^ (-s)) *
                rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)))) (ofOp (star K)) := by
            rw [hreorder]
      _ =
          (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (1 - s))) (ofOp (star K)) := by
            rw [hright_pow]
      _ = ofOp (A ^ s * star K * B ^ (1 - s)) := by
            simp [leftMulHS_apply, rightMulHS_apply, mul_assoc]
  calc
    phiK (ℋ := ℋ) K
        (operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B))
      = Complex.re
          (inner ℂ (ofOp (star K))
            (ofOp (A ^ s * star K * B ^ (1 - s)))) := by
            simp [phiK, happly]
    _ = traceRe (ℋ := ℋ) (A ^ s * star K * B ^ (1 - s) * K) := by
          rw [traceRe]
          set X : (ℋ →L[ℂ] ℋ) := A ^ s * star K * B ^ (1 - s)
          have htrace :=
            re_hsInner_eq_traceRe (ℋ := ℋ) (X := star K) (Y := X)
          have htrace' :
              Complex.re (inner ℂ (ofOp (star K)) (ofOp X)) =
                Complex.re (LinearMap.trace ℂ ℋ
                  ((K * X : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ)) := by
            simpa [X, mul_assoc] using htrace
          have hcycle :
              Complex.re (LinearMap.trace ℂ ℋ ((K * X : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ)) =
                Complex.re
                  (LinearMap.trace ℂ ℋ ((X * K : ℋ →L[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ)) := by
            simpa using
              congrArg Complex.re
                (LinearMap.trace_mul_comm (R := ℂ) (M := ℋ)
                  (K : ℋ →ₗ[ℂ] ℋ) (X : ℋ →ₗ[ℂ] ℋ))
          simpa [X, mul_assoc] using htrace'.trans hcycle
    _ = liebTraceMap (ℋ := ℋ) s K A B := by
          rfl

lemma phiK_weightedSum_operatorPowerMean_eq
    {s θ : ℝ} (K A₁ A₂ B₁ B₂ : (ℋ →L[ℂ] ℋ))
    (hA₁ : A₁ ∈ pdSet (ℋ := ℋ)) (hA₂ : A₂ ∈ pdSet (ℋ := ℋ))
    (hB₁ : B₁ ∈ pdSet (ℋ := ℋ)) (hB₂ : B₂ ∈ pdSet (ℋ := ℋ)) :
    phiK (ℋ := ℋ) K
        ((1 - θ) • operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁) +
          θ • operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂)) =
      (1 - θ) • liebTraceMap (ℋ := ℋ) s K A₁ B₁ +
        θ • liebTraceMap (ℋ := ℋ) s K A₂ B₂ := by
  rw [phiK_add, phiK_smul, phiK_smul]
  simpa [smul_eq_mul] using
    show (1 - θ) * phiK (ℋ := ℋ) K
        (operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁)) +
      θ * phiK (ℋ := ℋ) K
        (operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂)) =
      (1 - θ) * liebTraceMap (ℋ := ℋ) s K A₁ B₁ +
        θ * liebTraceMap (ℋ := ℋ) s K A₂ B₂ by
      simp only [phiK_operatorPowerMean_eq_liebTraceMap (ℋ := ℋ) (s := s) K A₁ B₁ hA₁ hB₁,
    phiK_operatorPowerMean_eq_liebTraceMap (ℋ := ℋ) (s := s) K A₂ B₂ hA₂ hB₂]


end LiebAndoTrace
