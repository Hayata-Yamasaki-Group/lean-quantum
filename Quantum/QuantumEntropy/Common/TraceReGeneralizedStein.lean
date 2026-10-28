/-
Copyright (c) 2025-2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.QuantumMechanics.OperatorBridge

namespace QuantumEntropy

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u
variable {ℋ : Type u} [Qudit ℋ]

private lemma alphaInfty_trace_sub (A B : ℋ →L[ℂ] ℋ) :
    Tr ((A - B : ℋ →L[ℂ] ℋ) : L ℋ) =
      Tr (A : L ℋ) - Tr (B : L ℋ) := by
  change Tr ((A : L ℋ) - (B : L ℋ)) = Tr (A : L ℋ) - Tr (B : L ℋ)
  exact map_sub Tr (A : L ℋ) (B : L ℋ)

end

end QuantumEntropy

namespace QuantumEntropy

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u
variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

/-- For a non-negative operator, the operator norm (largest eigenvalue) is bounded
    by the (real) trace (the sum of the eigenvalues). -/
lemma norm_le_re_trace {C : B ℋ} (hC : 0 ≤ C) :
    ‖C‖ ≤ (Tr (C : L ℋ)).re := by
  classical
  have hpos : C.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive C).mp hC
  have hsym : C.IsSymmetric := hpos.isSymmetric
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  set b := hsym.eigenvectorBasis hn with hb
  set eig := hsym.eigenvalues hn with heig
  have h_eig_nn : ∀ i, 0 ≤ eig i := fun i => hpos.toLinearMap.nonneg_eigenvalues hn i
  have h_eig_apply : ∀ i, C (b i) = ((eig i : ℝ) : ℂ) • b i :=
    hsym.apply_eigenvectorBasis hn
  have htr : (Tr (C : L ℋ)).re = ∑ i, eig i := by
    simpa using hsym.re_trace_eq_sum_eigenvalues hn
  -- `‖C‖` is attained as an eigenvalue.
  have hmemℝ : ‖C‖ ∈ spectrum ℝ C := CStarAlgebra.norm_mem_spectrum_of_nonneg hC
  have hmemℂ : (‖C‖ : ℂ) ∈ spectrum ℂ C :=
    (IsSelfAdjoint.of_nonneg hC).coe_mem_spectrum_complex.mpr hmemℝ
  rw [ContinuousLinearMap.spectrum_eq] at hmemℂ
  have hev : Module.End.HasEigenvalue (C : L ℋ) (‖C‖ : ℂ) :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hmemℂ
  obtain ⟨w, hw⟩ := hev.exists_hasEigenvector
  have hCw : C w = (‖C‖ : ℂ) • w := Module.End.mem_eigenspace_iff.mp hw.1
  have hw_ne : w ≠ 0 := hw.2
  obtain ⟨j, hcj⟩ : ∃ j, inner ℂ (b j) w ≠ (0 : ℂ) := by
    by_contra h; push_neg at h
    apply hw_ne
    have hrep : w = ∑ i, inner ℂ (b i) w • b i := (b.sum_repr' w).symm
    rw [hrep]; simp [h]
  have hkey : (eig j : ℂ) * inner ℂ (b j) w = (‖C‖ : ℂ) * inner ℂ (b j) w := by
    have h1 : inner ℂ (b j) (C w) = (‖C‖ : ℂ) * inner ℂ (b j) w := by rw [hCw,
      inner_smul_right]
    have h2 : inner ℂ (b j) (C w) = (eig j : ℂ) * inner ℂ (b j) w := by
      rw [show inner ℂ (b j) (C w) = inner ℂ (C (b j)) w from (hsym (b j) w).symm,
        h_eig_apply j, inner_smul_left, Complex.conj_ofReal]
    rw [← h1, h2]
  have hej : eig j = ‖C‖ := by exact_mod_cast mul_right_cancel₀ hcj hkey
  rw [htr, ← hej]
  exact Finset.single_le_sum (fun i _ => h_eig_nn i) (Finset.mem_univ j)

end

end QuantumEntropy

namespace QuantumEntropy

section

open QuantumState
open scoped ComplexOrder NNReal Topology
universe u
variable {ℋ : Type u} [Qudit ℋ]

/-- For a non-negative operator, the (real) trace is bounded by `dim ℋ` times the
    operator norm. -/
lemma re_trace_le_finrank_norm {C : B ℋ} (hC : 0 ≤ C) :
    (Tr (C : L ℋ)).re ≤
      (Module.finrank ℂ ℋ : ℝ) * ‖C‖ := by
  have hle : C ≤ algebraMap ℝ (B ℋ) ‖C‖ :=
    IsSelfAdjoint.le_algebraMap_norm_self (IsSelfAdjoint.of_nonneg hC)
  have hdiff : (0 : B ℋ) ≤ algebraMap ℝ (B ℋ) ‖C‖ - C :=
    sub_nonneg.mpr hle
  have htr : 0 ≤ (Tr (((algebraMap ℝ (B ℋ) ‖C‖ - C :
      QuantumState.B ℋ) : L ℋ))).re := by
    have h := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hdiff).toLinearMap.trace_nonneg
    rw [Complex.le_def] at h
    exact h.1
  rw [alphaInfty_trace_sub, Complex.sub_re] at htr
  have htr1 : (Tr ((algebraMap ℝ (B ℋ) ‖C‖ :
      QuantumState.B ℋ) : L ℋ)).re =
      (Module.finrank ℂ ℋ : ℝ) * ‖C‖ := by
    rw [show (algebraMap ℝ (B ℋ)) ‖C‖ =
        ((‖C‖ : ℝ) : ℂ) • (1 : B ℋ) by
      rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]]
    change (Tr (((‖C‖ : ℝ) : ℂ) • (1 : L ℋ))).re =
      (Module.finrank ℂ ℋ : ℝ) * ‖C‖
    rw [map_smul, smul_eq_mul, LinearMap.trace_one, Complex.mul_re]
    simp [mul_comm]
  rw [htr1] at htr
  linarith

end

end QuantumEntropy
