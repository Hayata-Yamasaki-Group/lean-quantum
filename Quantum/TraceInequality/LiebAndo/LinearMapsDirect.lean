/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumEntropy.Common.PositiveDefiniteSet
import Quantum.QuantumEntropy.CFCTransport
import Quantum.TraceInequality.LiebAndo.PositiveDefiniteGeometry
import Quantum.TraceInequality.LiebAndo.TraceMapLM

/-! # Hilbert–Schmidt power-mean identities for linear endomorphisms -/

open QuantumState LownerHeinzTheorem GeneralizedPerspectiveFunction
open HilbertSchmidtOperatorSpace OperatorGeometricMean Module.End Polynomial

namespace LiebAndoTrace

universe u

variable {ℋ : Type u} [Qudit ℋ]

local instance linearTraceNonnegSpectrumClass :
    NonnegSpectrumClass ℝ (ℋ →L[ℂ] ℋ) :=
  CStarAlgebra.instNonnegSpectrumClass

private lemma toCLM_rpow (A : L ℋ) (p : ℝ) :
    (A ^ p).toContinuousLinearMap = A.toContinuousLinearMap ^ p := by
  simpa only [CFC.rpow_eq_pow] using CFCTransport.cfc_rpow_toCLM A p

private lemma toCLM_star (A : L ℋ) :
    (star A).toContinuousLinearMap = star A.toContinuousLinearMap :=
  map_star (QuantumChannel.linearToContinuousEndStarAlgEquiv ℋ) A

private lemma toCLM_mul (A B : L ℋ) :
    (A * B).toContinuousLinearMap = A.toContinuousLinearMap * B.toContinuousLinearMap :=
  map_mul (QuantumChannel.linearToContinuousEndStarAlgEquiv ℋ) A B

private lemma trace_product_toCLM (s : ℝ) (K A B : L ℋ) :
    (LinearMap.trace ℂ ℋ
      ((A.toContinuousLinearMap ^ s * star K.toContinuousLinearMap *
        B.toContinuousLinearMap ^ (1 - s) * K.toContinuousLinearMap).toLinearMap)).re =
      liebTraceMap s K A B := by
  rw [← toCLM_rpow, ← toCLM_rpow, ← toCLM_star,
    ← toCLM_mul, ← toCLM_mul, ← toCLM_mul]
  rfl

/-- Real powers of commuting positive operators, proved on joint eigenspaces. -/
private lemma cfcR_mul_rpow_of_commute_nonneg
    {𝓚 : Type*} [NormedAddCommGroup 𝓚] [InnerProductSpace ℂ 𝓚] [CompleteSpace 𝓚]
    [FiniteDimensional ℂ 𝓚] {T S : 𝓚 →L[ℂ] 𝓚}
    (hTS : Commute T S) (hT0 : 0 ≤ T) (hS0 : 0 ≤ S) (s : ℝ) :
    cfcR (ℋ := 𝓚) (fun x : ℝ ↦ x ^ s) (T * S) =
      cfcR (ℋ := 𝓚) (fun x : ℝ ↦ x ^ s) T *
        cfcR (ℋ := 𝓚) (fun x : ℝ ↦ x ^ s) S := by
  let T0 : 𝓚 →ₗ[ℂ] 𝓚 := T.toLinearMap
  let T1 : 𝓚 →ₗ[ℂ] 𝓚 := S.toLinearMap
  let lhs := cfcR (ℋ := 𝓚) (fun x : ℝ ↦ x ^ s) (T * S)
  let rhs := cfcR (ℋ := 𝓚) (fun x : ℝ ↦ x ^ s) T *
    cfcR (ℋ := 𝓚) (fun x : ℝ ↦ x ^ s) S
  let D := lhs - rhs
  have hT_sa : IsSelfAdjoint T := IsSelfAdjoint.of_nonneg hT0
  have hS_sa : IsSelfAdjoint S := IsSelfAdjoint.of_nonneg hS0
  have hT0_symm : T0.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT_sa
  have hT1_symm : T1.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hS_sa
  have hcomm : Commute T0 T1 := by
    change T0 * T1 = T1 * T0
    ext x
    exact congrArg (fun F : 𝓚 →L[ℂ] 𝓚 => F x) hTS.eq
  have hprod_sa : IsSelfAdjoint (T * S) :=
    IsSelfAdjoint.of_nonneg (hTS.mul_nonneg hT0 hS0)
  have htop :
      (⨆ α, ⨆ β, eigenspace T0 α ⊓ eigenspace T1 β) = ⊤ := by
    exact LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute
      hT0_symm hT1_symm hcomm
  have hjoint_ker :
      ∀ α β,
        eigenspace T0 α ⊓ eigenspace T1 β ≤
          LinearMap.ker (D : 𝓚 →ₗ[ℂ] 𝓚) := by
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
    have hT0_nonneg_re :
        ∀ y : 𝓚, 0 ≤ Complex.re (inner ℂ y (T0 y)) := by
      intro y
      simpa [T0] using
        re_inner_nonneg_of_nonneg
          (T := T)
          (hT0) y
    have hT1_nonneg_re :
        ∀ y : 𝓚, 0 ≤ Complex.re (inner ℂ y (T1 y)) := by
      intro y
      simpa [T1] using
        re_inner_nonneg_of_nonneg
          (T := S)
          (hS0) y
    have hαnonneg : 0 ≤ α.re := by
      exact eigenvalue_nonneg_of_nonneg
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx0r, hxzero⟩)
        hT0_nonneg_re
    have hβnonneg : 0 ≤ β.re := by
      exact eigenvalue_nonneg_of_nonneg
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx1r, hxzero⟩)
        hT1_nonneg_re
    have hxprod :
        x ∈ eigenspace
          ((T * S :
            𝓚 →L[ℂ] 𝓚) : 𝓚 →ₗ[ℂ] 𝓚)
          (((α.re * β.re : ℝ) : ℂ)) := by
      rw [Module.End.mem_eigenspace_iff]
      have hx0apply : T0 x = (α.re : ℂ) • x := Module.End.mem_eigenspace_iff.mp hx0r
      have hx1apply : T1 x = (β.re : ℂ) • x := Module.End.mem_eigenspace_iff.mp hx1r
      have hx0apply' :
          T x = (α.re : ℂ) • x := by
        simpa [T0] using hx0apply
      have hx1apply' :
          S x = (β.re : ℂ) • x := by
        simpa [T1] using hx1apply
      change T (S x) =
        (((α.re * β.re : ℝ) : ℂ)) • x
      rw [hx1apply', ContinuousLinearMap.map_smul, hx0apply']
      rw [smul_smul]
      congr 1
      simp [mul_comm]
    have hlhsx :
        lhs x = ((((α.re * β.re : ℝ) ^ s : ℝ) : ℂ) • x) := by
      simpa [lhs] using
        cfcR_apply_of_mem_eigenspace_real
          (𝓚 := 𝓚) (f := fun t : ℝ ↦ t ^ s) hprod_sa
            (Module.End.mem_eigenspace_iff.mp hxprod)
    have hrhsx :
        rhs x = ((((α.re ^ s) * (β.re ^ s) : ℝ) : ℂ) • x) := by
      change (cfcR (ℋ := 𝓚) (fun t : ℝ ↦ t ^ s) T * cfcR (ℋ := 𝓚) (fun t : ℝ ↦ t ^ s) S) x =
        ((((α.re ^ s) * (β.re ^ s) : ℝ) : ℂ) • x)
      have hleftx :
          cfcR (ℋ := 𝓚) (fun t : ℝ ↦ t ^ s) (T) x =
            (((α.re ^ s : ℝ) : ℂ) • x) := by
        simpa using
          cfcR_apply_of_mem_eigenspace_real
            (𝓚 := 𝓚) (f := fun t : ℝ ↦ t ^ s) hT_sa
              (Module.End.mem_eigenspace_iff.mp hx0r)
      have hrightx :
          cfcR (ℋ := 𝓚) (fun t : ℝ ↦ t ^ s)
              (S) x =
            (((β.re ^ s : ℝ) : ℂ) • x) := by
        simpa using
          cfcR_apply_of_mem_eigenspace_real
            (𝓚 := 𝓚) (f := fun t : ℝ ↦ t ^ s) hS_sa
              (Module.End.mem_eigenspace_iff.mp hx1r)
      rw [ContinuousLinearMap.mul_def]
      change cfcR (ℋ := 𝓚) (fun t : ℝ ↦ t ^ s) (T)
          (cfcR (ℋ := 𝓚) (fun t : ℝ ↦ t ^ s)
            (S) x) =
        ((((α.re ^ s) * (β.re ^ s) : ℝ) : ℂ) • x)
      rw [hrightx, ContinuousLinearMap.map_smul, hleftx]
      rw [smul_smul]
      congr 1
      simp [mul_comm]
    have hscal :
        (((α.re * β.re : ℝ) ^ s : ℝ) : ℂ) =
          ((((α.re ^ s) * (β.re ^ s) : ℝ)) : ℂ) := by
      exact congrArg (fun t : ℝ => (t : ℂ)) (Real.mul_rpow hαnonneg hβnonneg)
    simpa [D] using
      sub_eq_zero.mpr (hlhsx.trans (hscal ▸ hrhsx.symm))
  have hker_top : LinearMap.ker (D : 𝓚 →ₗ[ℂ] 𝓚) = ⊤ := by
    apply top_unique
    rw [← htop]
    exact iSup_le fun α => iSup_le fun β => hjoint_ker α β
  have hDzero : D = 0 := by
    ext x
    exact LinearMap.congr_fun (LinearMap.ker_eq_top.mp hker_top) x
  simpa [lhs, rhs] using sub_eq_zero.mp hDzero

variable [Nontrivial ℋ]

omit [Nontrivial ℋ] in
/-- The middle power in the HS perspective for linear endomorphisms. -/
private lemma middlePower_leftMul_rightMul_lm {s : ℝ} {A₀ B₀ : L ℋ}
    (hA : A₀ ∈ SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ))
    (hB : B₀ ∈ SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ)) :
    cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s)
      (cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2))
          (rightMulHS B₀.toContinuousLinearMap) *
        leftMulHS A₀.toContinuousLinearMap *
        cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2))
          (rightMulHS B₀.toContinuousLinearMap)) =
      leftMulHS (A₀ ^ s).toContinuousLinearMap *
        rightMulHS (B₀ ^ (-s)).toContinuousLinearMap := by
  let A := A₀.toContinuousLinearMap
  let B := B₀.toContinuousLinearMap
  suffices h :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s)
        (cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS B) *
          leftMulHS A *
          cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS B)) =
        leftMulHS (A ^ s) * rightMulHS (B ^ (-s)) by
    simpa only [A, B, toCLM_rpow] using h
  change A ∈ pdSet (ℋ := ℋ) at hA
  change B ∈ pdSet (ℋ := ℋ) at hB
  rcases hA with ⟨hA_sa, hA_spec⟩
  rcases hB with ⟨hB_sa, hB_spec⟩
  have hA0 : 0 ≤ A :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA_sa)).2
      fun _ hx => (hA_spec hx).le
  have hB0 : 0 ≤ B :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB_sa)).2
      fun _ hx => (hB_spec hx).le
  have hright_negHalf :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) =
        rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) := by
    rw [show rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) =
        rightMulHS (ℋ := ℋ) (cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) B) by
      congr
      simpa [cfcR] using
        (CFC.rpow_eq_cfc_real (A := (ℋ →L[ℂ] ℋ)) (a := B) (y := (-1 : ℝ) / 2) (ha := hB0))]
    exact (rightMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) B hB_sa
      (by
        intro x hx
        exact (Real.continuousAt_rpow_const x ((-1 : ℝ) / 2)
          (Or.inl (ne_of_gt (hB_spec hx)))).continuousWithinAt)).symm
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
    rw [hright_negHalf,
      (leftMulHS_rightMulHS_commute (ℋ := ℋ) A (B ^ ((-1 : ℝ) / 2))).eq.symm,
      mul_assoc,
      ← rightMulHS_mul (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) (B ^ ((-1 : ℝ) / 2)),
      hBnegOne]
  rw [hmid_prod]
  have hBinv0 : 0 ≤ B ^ (-1 : ℝ) := by
    simp
  have hBinv_sa : IsSelfAdjoint (B ^ (-1 : ℝ)) := IsSelfAdjoint.of_nonneg hBinv0
  have hBinv_unit : IsUnit (B ^ (-1 : ℝ)) := hBunit.cfcRpow (-1 : ℝ) hB0
  have hleft_pow :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s) (leftMulHS (ℋ := ℋ) A) =
        leftMulHS (ℋ := ℋ) (A ^ s) := by
    rw [show leftMulHS (ℋ := ℋ) (A ^ s) =
        leftMulHS (ℋ := ℋ) (cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ s) A) by
      congr
      simpa [cfcR] using
        (CFC.rpow_eq_cfc_real (A := (ℋ →L[ℂ] ℋ)) (a := A) (y := s) (ha := hA0))]
    exact (leftMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ s) A hA_sa
      (by
        intro x hx
        exact (Real.continuousAt_rpow_const x s
          (Or.inl (ne_of_gt (hA_spec hx)))).continuousWithinAt)).symm
  have hright_pow :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s)
          (rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))) =
        rightMulHS (ℋ := ℋ) (B ^ (-s)) := by
    rw [show rightMulHS (ℋ := ℋ) (B ^ (-s)) =
        rightMulHS (ℋ := ℋ) (cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ s) (B ^ (-1 : ℝ))) by
      congr
      calc
        B ^ (-s) = (B ^ (-1 : ℝ)) ^ s := by
          symm
          simpa using (CFC.rpow_rpow (a := B) (-1 : ℝ) s hBunit (by norm_num) hB0)
        _ = cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ s) (B ^ (-1 : ℝ)) := by
          simpa [cfcR] using
            (CFC.rpow_eq_cfc_real (A := (ℋ →L[ℂ] ℋ)) (a := B ^ (-1 : ℝ)) (y := s)
                (ha := hBinv0))]
    exact (rightMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ s) (B ^ (-1 : ℝ)) hBinv_sa
      (by
        intro x hx
        have hx0 : x ≠ 0 := by
          intro hx0
          exact spectrum.zero_notMem (R := ℝ) hBinv_unit (by simpa [hx0] using hx)
        exact (Real.continuousAt_rpow_const x s (Or.inl hx0)).continuousWithinAt)).symm
  rw [← hleft_pow, ← hright_pow]
  exact cfcR_mul_rpow_of_commute_nonneg
    (leftMulHS_rightMulHS_commute A (B ^ (-1 : ℝ)))
    (leftMulHS_nonneg hA0) (rightMulHS_nonneg hBinv0) s

omit [Nontrivial ℋ] in
/-- Direct HS vector-state identification, stated with the LM trace map. -/
lemma phiK_operatorPowerMean_eq_liebTraceMap_lm
    {s : ℝ} (K₀ A₀ B₀ : L ℋ)
    (hA : A₀ ∈ SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ))
    (hB : B₀ ∈ SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ)) :
    phiK K₀.toContinuousLinearMap
      (operatorPowerMean (ℋ := HSOp ℋ) s 1
        (leftMulHS A₀.toContinuousLinearMap) (rightMulHS B₀.toContinuousLinearMap)) =
      liebTraceMap s K₀ A₀ B₀ := by
  let K := K₀.toContinuousLinearMap
  let A := A₀.toContinuousLinearMap
  let B := B₀.toContinuousLinearMap
  change A ∈ pdSet (ℋ := ℋ) at hA
  change B ∈ pdSet (ℋ := ℋ) at hB
  change phiK K (operatorPowerMean (ℋ := HSOp ℋ) s 1 (leftMulHS A) (rightMulHS B)) =
    liebTraceMap s K₀ A₀ B₀
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
    simpa only [A, B, toCLM_rpow] using
      middlePower_leftMul_rightMul_lm (ℋ := ℋ) (s := s) (A₀ := A₀) (B₀ := B₀)
        ⟨hA_sa, hA_spec⟩ ⟨hB_sa, hB_spec⟩
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
            change ofOp (A ^ s * (star K * B ^ (1 - s))) = _
            simp only [mul_assoc]
  calc
    phiK (ℋ := ℋ) K
        (operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B))
      = Complex.re
          (inner ℂ (ofOp (star K))
            (ofOp (A ^ s * star K * B ^ (1 - s)))) := by
            simp [phiK, happly]
    _ = (LinearMap.trace ℂ ℋ
          ((A ^ s * star K * B ^ (1 - s) * K).toLinearMap)).re := by
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
    _ = liebTraceMap s K₀ A₀ B₀ := by
          simpa only [K, A, B] using trace_product_toCLM s K₀ A₀ B₀

/-- Positive real powers stay in the LM positive-definite cone. -/
private lemma pdSetLM_rpow {β : ℝ} (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    {B : L ℋ} (hB : B ∈ SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ)) :
    B ^ β ∈ SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ) := by
  change (B ^ β).toContinuousLinearMap ∈ pdSet (ℋ := ℋ)
  rw [toCLM_rpow]
  exact pdSet_rpow_of_mem_Icc_zero_one_transport hβ hB

/-- Transport the composed scalar power through right multiplication. -/
private lemma rightMulHS_power_comp_lm {β : ℝ}
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) (B : L ℋ)
    (hB : B ∈ SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ)) :
    cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ (x ^ β) ^ t)
        (rightMulHS B.toContinuousLinearMap) =
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ t)
        (rightMulHS (B ^ β).toContinuousLinearMap) := by
  let C := B.toContinuousLinearMap
  have hC : C ∈ pdSet (ℋ := ℋ) := hB
  have hC0 : 0 ≤ C :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) C (ha := hC.1)).2
      fun _ hx => (hC.2 hx).le
  have hf : ContinuousOn (fun x : ℝ ↦ x ^ β) (spectrum ℝ C) := by
    intro x hx
    exact (Real.continuousAt_rpow_const x β
      (Or.inl (ne_of_gt (hC.2 hx)))).continuousWithinAt
  have hg : ContinuousOn (fun x : ℝ ↦ x ^ t)
      ((fun x : ℝ ↦ x ^ β) '' spectrum ℝ C) := by
    rintro x ⟨y, hy, rfl⟩
    exact (Real.continuousAt_rpow_const (y ^ β) t
      (Or.inl (ne_of_gt (Real.rpow_pos_of_pos (hC.2 hy) β)))).continuousWithinAt
  have hcomp : cfcR (fun x : ℝ ↦ (x ^ β) ^ t) C =
      cfcR (fun x : ℝ ↦ x ^ t) (C ^ β) := by
    rw [CFC.rpow_eq_cfc_real (a := C) (y := β) (ha := hC0)]
    exact cfc_comp (fun x : ℝ ↦ x ^ t) (fun x : ℝ ↦ x ^ β) C hC.1 hg hf
  have hpow := pdSet_rpow_of_mem_Icc_zero_one_transport hβ hC
  have hpcont : ContinuousOn (fun x : ℝ ↦ x ^ t) (spectrum ℝ (C ^ β)) := by
    intro x hx
    exact (Real.continuousAt_rpow_const x t
      (Or.inl (ne_of_gt (hpow.2 hx)))).continuousWithinAt
  rw [toCLM_rpow]
  change cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ (x ^ β) ^ t) (rightMulHS C) =
    cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ t) (rightMulHS (C ^ β))
  rw [← rightMulHS_cfcR (fun x : ℝ ↦ (x ^ β) ^ t) C hC.1
    (hg.comp hf (Set.mapsTo_image _ _)),
    hcomp, rightMulHS_cfcR _ (C ^ β) hpow.1 hpcont]

/-- The HS power mean with general β reduces to the β=1 identification. -/
lemma phiK_operatorPowerMean_eq_liebTraceMap_rpow_lm {q β : ℝ}
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (K A B : L ℋ)
    (hA : A ∈ SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ))
    (hB : B ∈ SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ)) :
    phiK K.toContinuousLinearMap
      (operatorPowerMean (ℋ := HSOp ℋ) q β
        (leftMulHS A.toContinuousLinearMap) (rightMulHS B.toContinuousLinearMap)) =
      liebTraceMap q K A (B ^ β) := by
  have hmean : operatorPowerMean (ℋ := HSOp ℋ) q β
      (leftMulHS A.toContinuousLinearMap) (rightMulHS B.toContinuousLinearMap) =
      operatorPowerMean (ℋ := HSOp ℋ) q 1
        (leftMulHS A.toContinuousLinearMap) (rightMulHS (B ^ β).toContinuousLinearMap) := by
    unfold operatorPowerMean generalizedPerspective hSqrt hInvSqrt
    simp only [Real.rpow_one]
    rw [rightMulHS_power_comp_lm hβ ((1 : ℝ) / 2) B hB,
      rightMulHS_power_comp_lm hβ ((-1 : ℝ) / 2) B hB]
  rw [hmean]
  exact phiK_operatorPowerMean_eq_liebTraceMap_lm K A (B ^ β) hA (pdSetLM_rpow hβ hB)

omit [Nontrivial ℋ] in
/-- Compose powers on positive LM inputs, including the β=0 endpoint. -/
lemma liebTraceMap_rpow_eq_andoTraceMap_lm {q r β : ℝ}
    (hβmul : β * (1 - q) = -r) (K A B : L ℋ)
    (hB : B ∈ SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ)) :
    liebTraceMap q K A (B ^ β) = andoTraceMap q r K A B := by
  have hB0 : 0 ≤ B.toContinuousLinearMap :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ)
      B.toContinuousLinearMap (ha := hB.1)).2 fun _ hx => (hB.2 hx).le
  have hunit : IsUnit B.toContinuousLinearMap :=
    spectrum.isUnit_of_zero_notMem (R := ℝ) fun h0 =>
      (lt_irrefl (0 : ℝ)) (by simpa [Set.Ioi] using hB.2 h0)
  have hpow : (B ^ β) ^ (1 - q) = B ^ (-r) := by
    suffices h : ((B ^ β) ^ (1 - q)).toContinuousLinearMap =
        (B ^ (-r)).toContinuousLinearMap from
      congrArg ContinuousLinearMap.toLinearMap h
    rw [toCLM_rpow, toCLM_rpow, toCLM_rpow]
    by_cases hβzero : β = 0
    · have hrzero : r = 0 := by
        rw [hβzero] at hβmul
        linarith
      simp only [hβzero, hrzero, neg_zero]
      rw [CFC.rpow_zero _ hB0]
      exact CFC.one_rpow
    · rw [CFC.rpow_rpow _ _ _ hunit hβzero hB0, hβmul]
  simp only [liebTraceMap, andoTraceMap, hpow]

private lemma phiK_operatorPowerMean_eq_andoTraceMap_lm {q r β : ℝ}
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hβmul : β * (1 - q) = -r)
    (K A B : L ℋ)
    (hA : A ∈ SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ))
    (hB : B ∈ SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ)) :
    phiK K.toContinuousLinearMap
      (operatorPowerMean (ℋ := HSOp ℋ) q β
        (leftMulHS A.toContinuousLinearMap) (rightMulHS B.toContinuousLinearMap)) =
      andoTraceMap q r K A B := by
  rw [phiK_operatorPowerMean_eq_liebTraceMap_rpow_lm hβ K A B hA hB]
  exact liebTraceMap_rpow_eq_andoTraceMap_lm hβmul K A B hB

end LiebAndoTrace
