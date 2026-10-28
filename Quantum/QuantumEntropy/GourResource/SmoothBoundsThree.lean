/-
Order and normalization of the noncommutative filter. Uses the inverse square root on the support projection, and concludes a nonzero trace.
Source context: Gour, Theorem 11.4.
-/
/-
Fidelity lower bound for the filtered state.
Source context: Gour, Theorem 11.4.
-/
/-
Upper bound of the smoothed max-relative entropy by the hypothesis-testing relative entropy: smoothMax(√(1−ε²)) + log₂(ε/(1−ε)) ≤ dh(ε) for ε ∈ (0,1) (gsl_c19).
Source context: Gour, Theorem 11.4.
-/
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesVonNeumann.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesDualMinCore.GSLCore
import Quantum.QuantumEntropy.GourResource.TestingSDP
import Quantum.QuantumEntropy.GourResource.KWMetricBridge
import Quantum.QuantumEntropy.PSDMoorePenroseCFC.GSLCore


namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem inverse_sandwich {A : Type u} [Qudit A] [Nontrivial A]
    (T : L A) (hT : 0 ≤ T) :
    CFC.rpow T (-1 / 2 : ℝ) * T * CFC.rpow T (-1 / 2 : ℝ) =
      OPT.petzSupportRpow T 0 ∧ OPT.petzSupportRpow T 0 ≤ 1 := by
  have hOne : OPT.petzSupportRpow T 1 = T := by
    rw [OPT.petzSupportRpow_of_ne_zero T (by norm_num), CFC.rpow_eq_pow,
      CFC.rpow_one T hT]
  constructor
  · calc
      _ = OPT.petzSupportRpow T (-1/2) * OPT.petzSupportRpow T 1 *
          OPT.petzSupportRpow T (-1/2) := by
        rw [hOne, OPT.petzSupportRpow_of_ne_zero T (by norm_num)]
      _ = OPT.petzSupportRpow T 0 := by
        rw [OPT.petzSupportRpow_add hT, OPT.petzSupportRpow_add hT]
        norm_num
  · rw [OPT.petzSupportRpow_zero]
    exact ((LinearMap.isStarProjection_iff_isSymmetricProjection).mpr
      (Submodule.isSymmetricProjection_starProjection (LinearMap.range T))).le_one

private theorem support_fixes {A : Type u} [Qudit A] [Nontrivial A]
    {B T : L A} (hT : 0 ≤ T) (hB : 0 ≤ B) (hBT : B ≤ T) :
    B * OPT.petzSupportRpow T 0 = B := by
  apply OPT.mul_petzSupportRpow_zero_eq_of_ker_le hT hB
  intro x hx
  exact LinearMap.mem_ker.mpr
    (QuantumChannel.nonneg_eq_zero_of_le_of_apply_eq_zero
      hB hBT (LinearMap.mem_ker.mp hx))

private theorem trace_mul_mono {A : Type u} [Qudit A] [Nontrivial A]
    {K X Y : L A} (hK : 0 ≤ K) (hXY : X ≤ Y) :
    (Tr (K * X)).re ≤ (Tr (K * Y)).re := by
  have h : 0 ≤ (Tr (K * (Y - X))).re := by
    by_cases hz : K * (Y - X) = 0
    · simp [hz]
    · exact (OPT.trace_re_pos_mul_of_nonneg_of_ne_zero
        hK (sub_nonneg.mpr hXY) hz).le
  simpa only [mul_sub, map_sub, Complex.sub_re, sub_nonneg] using h

private theorem trace_filter {A : Type u} [Qudit A] (G B : L A) :
    Tr (G * B * star G) = Tr (star G * G * B) := by
  rw [LinearMap.trace_mul_comm ℂ (G * B) (star G), mul_assoc]

private theorem normalize_density {A : Type u} [Qudit A]
    {X : L A} (hX : 0 ≤ X) (hq : 0 < (Tr X).re) :
    IsDensity ((Tr X).re⁻¹ • X) := by
  have hXp := (LinearMap.nonneg_iff_isPositive X).mp hX
  have hTr : Tr X = ((Tr X).re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp hXp.trace_nonneg).2.symm
  constructor
  · rw [← Complex.coe_smul]
    exact hXp.smul_of_nonneg (by exact_mod_cast (inv_nonneg.mpr hq.le))
  · rw [← Complex.coe_smul, map_smul, hTr, smul_eq_mul]
    norm_cast
    exact inv_mul_cancel₀ hq.ne'

private theorem filter_geometry {A : Type u} [Qudit A] [Nontrivial A]
    {B T : L A} (hB : 0 ≤ B) (hT : 0 ≤ T) (hBT : B ≤ T) :
    let G := CFC.sqrt B * CFC.rpow T (-1 / 2 : ℝ)
    star G * G ≤ 1 ∧ G * T * star G ≤ B ∧ Tr (star G * G * T) = Tr B := by
  let S := CFC.sqrt B
  let R := CFC.rpow T (-1 / 2 : ℝ)
  have hS : 0 ≤ S := CFC.sqrt_nonneg B
  have hR : 0 ≤ R := CFC.rpow_nonneg
  have hSstar : star S = S := (IsSelfAdjoint.of_nonneg hS).star_eq
  have hRstar : star R = R := (IsSelfAdjoint.of_nonneg hR).star_eq
  have hSS : S * S = B := CFC.sqrt_mul_sqrt_self B hB
  obtain ⟨hRTR, hP⟩ := inverse_sandwich T hT
  change R * T * R = OPT.petzSupportRpow T 0 at hRTR
  have hE : star (S * R) * (S * R) = R * B * R := by
    rw [star_mul, hSstar, hRstar]
    calc
      _ = R * (S * S) * R := by noncomm_ring
      _ = R * B * R := by rw [hSS]
  have hGT : (S * R) * T * star (S * R) = S * (R * T * R) * S := by
    rw [star_mul, hSstar, hRstar]
    noncomm_ring
  change star (S * R) * (S * R) ≤ 1 ∧
    (S * R) * T * star (S * R) ≤ B ∧
    Tr (star (S * R) * (S * R) * T) = Tr B
  refine ⟨?_, ?_, ?_⟩
  · rw [hE]
    exact ((conjugate_le_conjugate_of_nonneg hBT hR).trans_eq hRTR).trans hP
  · rw [hGT, hRTR]
    simpa only [mul_one, hSS] using conjugate_le_conjugate_of_nonneg hP hS
  · rw [hE]
    calc
      Tr (R * B * R * T) = Tr (R * (B * R * T)) := by
        simp only [mul_assoc]
      _ = Tr ((B * R * T) * R) := LinearMap.trace_mul_comm ℂ R (B * R * T)
      _ = Tr (B * (R * T * R)) := by simp only [mul_assoc]
      _ = Tr B := by rw [hRTR, support_fixes hT hB hBT]

private theorem c18a_smul_cancel {M : Type*} [AddCommGroup M] [Module ℝ M]
    (t q : ℝ) (X : M) (hq : q ≠ 0) : (t * q : ℝ) • (q⁻¹ • X) = t • X := by
  rw [smul_smul, mul_assoc, mul_inv_cancel₀ hq, mul_one]

private theorem c18a_conj_smul {R : Type*} [Ring R] [Module ℝ R] [SMulCommClass ℝ R R]
    [IsScalarTower ℝ R R] (G X H : R) (t : ℝ) : G * (t • X) * H = t • (G * X * H) := by
  rw [mul_smul_comm, smul_mul_assoc]

private theorem c18a_tr_mul_smul {A : Type u} [Qudit A] (K X : L A) (t : ℝ) :
    (Tr (K * (t • X))).re = t * (Tr (K * X)).re := by
  rw [mul_smul_comm, ← Complex.coe_smul, map_smul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem gsl_c18a :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (ε t : ℝ) (W : L.{u} A),
  ε ∈ Set.Ioo 0 1 → 0 < t → W.IsPositive →
  (σ.1 + W - t • ρ.1).IsPositive → (Tr.{u} W).re ≤ (1-ε)*t →
  let G := CFC.sqrt σ.1 * CFC.rpow (σ.1 + W) (-1 / 2 : ℝ)
  let X := G * ρ.1 * star G
  let q := (Tr.{u} X).re
  effect.{u} (star G * G) ∧ ε ≤ q ∧ q ≤ 1 ∧ 0 < q ∧
    IsDensity.{u} (q⁻¹ • X) ∧ (t*q : ℝ) • (q⁻¹ • X) ≤ σ.1
:= by
  intro A _ _ ρ σ ε t W hε ht hW hdom htrace
  let T := σ.1 + W
  let G := CFC.sqrt σ.1 * CFC.rpow T (-1 / 2 : ℝ)
  let X := G * ρ.1 * star G
  let q := (Tr X).re
  change effect (star G * G) ∧ ε ≤ q ∧ q ≤ 1 ∧ 0 < q ∧
    IsDensity (q⁻¹ • X) ∧ (t*q : ℝ) • (q⁻¹ • X) ≤ σ.1
  have hρ : 0 ≤ ρ.1 := (LinearMap.nonneg_iff_isPositive _).mpr ρ.2.1
  have hσ : 0 ≤ σ.1 := (LinearMap.nonneg_iff_isPositive _).mpr σ.2.1
  have hW0 : 0 ≤ W := (LinearMap.nonneg_iff_isPositive _).mpr hW
  have hT : 0 ≤ T := add_nonneg hσ hW0
  have hσT : σ.1 ≤ T := le_add_of_nonneg_right hW0
  have hρT : t • ρ.1 ≤ T :=
    sub_nonneg.mp ((LinearMap.nonneg_iff_isPositive _).mpr hdom)
  obtain ⟨hE, hGT, hET⟩ := filter_geometry hσ hT hσT
  change star G * G ≤ 1 at hE
  change G * T * star G ≤ σ.1 at hGT
  change Tr (star G * G * T) = Tr σ.1 at hET
  have hK : 0 ≤ 1 - star G * G := sub_nonneg.mpr hE
  have hX : 0 ≤ X := star_right_conjugate_nonneg hρ G
  have hqtrace : Tr (star G * G * ρ.1) = Tr X := (trace_filter G ρ.1).symm
  have hupper : q ≤ 1 := by
    have h := trace_mul_mono hρ hE
    rw [mul_one, ρ.2.2, Complex.one_re,
      LinearMap.trace_mul_comm ℂ ρ.1 (star G * G), hqtrace] at h
    exact h
  have hlossT : (Tr ((1 - star G * G) * T)).re = (Tr W).re := by
    rw [sub_mul, one_mul, map_sub, hET]
    simp only [T, map_add, Complex.add_re, Complex.sub_re]
    ring
  have hlossρ : (Tr ((1 - star G * G) * (t • ρ.1))).re = t * (1 - q) := by
    rw [c18a_tr_mul_smul, sub_mul, one_mul, map_sub, Complex.sub_re, ρ.2.2, Complex.one_re,
      hqtrace]
  have hloss := trace_mul_mono hK hρT
  rw [hlossρ, hlossT] at hloss
  have hlower : ε ≤ q := by nlinarith
  have hq : 0 < q := hε.1.trans_le hlower
  refine ⟨⟨(LinearMap.nonneg_iff_isPositive _).mp (star_mul_self_nonneg G),
    (LinearMap.nonneg_iff_isPositive _).mp hK⟩, hlower, hupper, hq,
    normalize_density hX hq, ?_⟩
  have htX : t • X ≤ σ.1 := by
    have h := (star_right_conjugate_le_conjugate hρT G).trans hGT
    rwa [c18a_conj_smul] at h
  calc
    (t*q : ℝ) • (q⁻¹ • X) = t • X := c18a_smul_cancel t q X hq.ne'
    _ ≤ σ.1 := htX

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem tr_nonneg {A : Type u} [Qudit A] {X : L A} (hX : 0 ≤ X) :
    0 ≤ (Tr X).re :=
  (RCLike.nonneg_iff.mp ((LinearMap.nonneg_iff_isPositive _).mp hX).trace_nonneg).1

private theorem tr_mono {A : Type u} [Qudit A] {X Y : L A} (h : X ≤ Y) :
    (Tr X).re ≤ (Tr Y).re := by
  have ht := tr_nonneg (sub_nonneg.mpr h)
  simpa only [map_sub, Complex.sub_re, sub_nonneg] using ht

private theorem tr_smul {A : Type u} [Qudit A] (c : ℝ) (X : L A) :
    (Tr (c • X)).re = c * (Tr X).re := by
  change (Tr ((c : ℂ) • X)).re = _
  simp only [map_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

private theorem tr_star {A : Type u} [Qudit A] (X : L A) :
    (Tr (star X)).re = (Tr X).re := by
  classical
  let b := stdOrthonormalBasis ℂ A
  change (LinearMap.trace ℂ A (star X)).re = (LinearMap.trace ℂ A X).re
  rw [(star X).trace_eq_sum_inner b, X.trace_eq_sum_inner b]
  simp only [Complex.re_sum, LinearMap.star_eq_adjoint, LinearMap.adjoint_inner_right]
  exact Finset.sum_congr rfl fun i _ => inner_re_symm (𝕜 := ℂ) _ _

private theorem tr_pair_nonneg {A : Type u} [Qudit A] {X Y : L A}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) : 0 ≤ (Tr (X * Y)).re := by
  have hs := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg X)).star_eq
  have hp : 0 ≤ CFC.sqrt X * Y * CFC.sqrt X := by
    simpa only [hs] using star_left_conjugate_nonneg hY (CFC.sqrt X)
  have ht := tr_nonneg hp
  rw [LinearMap.trace_mul_comm ℂ (CFC.sqrt X * Y),
    ← mul_assoc (CFC.sqrt X), CFC.sqrt_mul_sqrt_self X hX] at ht
  exact ht

private theorem conj_mono {A : Type u} [Qudit A] {X Y : L A}
    (h : X ≤ Y) (K : L A) : K * X * star K ≤ K * Y * star K := by
  have hp := star_right_conjugate_nonneg (sub_nonneg.mpr h) K
  simpa only [mul_sub, sub_mul, sub_nonneg] using hp

private theorem inv_sqrt_mul {A : Type u} [Qudit A] [Nontrivial A]
    {S : L A} (hS : 0 ≤ S) :
    CFC.rpow S (-1 / 2 : ℝ) * S = CFC.sqrt S := by
  have he := OPT.petzSupportRpow_add hS (-1 / 2 : ℝ) 1
  norm_num only at he
  rw [OPT.petzSupportRpow_of_ne_zero S (by norm_num : (-(1/2) : ℝ) ≠ 0),
    OPT.petzSupportRpow_of_ne_zero S (by norm_num : (1 : ℝ) ≠ 0),
    OPT.petzSupportRpow_of_ne_zero S (by norm_num : (1/2 : ℝ) ≠ 0)] at he
  simp only [CFC.rpow_eq_pow, CFC.rpow_one S hS] at he
  simpa only [CFC.sqrt_eq_rpow, CFC.rpow_eq_pow, neg_div] using he

private theorem inv_sqrt_sandwich {A : Type u} [Qudit A] [Nontrivial A]
    {S : L A} (hS : 0 ≤ S) :
    CFC.rpow S (-1 / 2 : ℝ) * S * CFC.rpow S (-1 / 2 : ℝ) ≤ 1 := by
  rw [inv_sqrt_mul hS]
  have he : CFC.sqrt S * CFC.rpow S (-1 / 2 : ℝ) =
      (LinearMap.range S).starProjection.toLinearMap := by
    simpa only [CFC.sqrt_eq_rpow, CFC.rpow_eq_pow, neg_div] using
      OPT.rpow_half_mul_invHalf hS
  rw [he]
  have hp := (Submodule.isSymmetricProjection_starProjection
    (LinearMap.range S).orthogonal).isPositive
  have heq := congrArg ContinuousLinearMap.toLinearMap
    (Submodule.starProjection_orthogonal (LinearMap.range S))
  rw [heq] at hp
  exact sub_nonneg.mp ((LinearMap.nonneg_iff_isPositive _).mpr hp)

private theorem tr_residual {A : Type u} [Qudit A] {R : L A}
    (hR : 0 ≤ R) (K : L A) :
    (Tr ((1 - K) * R * star (1 - K))).re =
      (Tr R).re + (Tr (K * R * star K)).re - 2 * (Tr (K * R)).re := by
  have hs := (IsSelfAdjoint.of_nonneg hR).star_eq
  have ht : (Tr (R * star K)).re = (Tr (K * R)).re := by
    simpa only [star_mul, hs] using tr_star (K * R)
  simp only [star_sub, star_one, mul_sub, sub_mul, one_mul, mul_one,
    map_sub, Complex.sub_re, ht]
  ring

-- The conjugation bound behind `filter_residual`, over an abstract C⋆-algebra.
private theorem filter_conj_le {R : Type*} [CStarAlgebra R] [PartialOrder R]
    [StarOrderedRing R] (s r S : R) (hs : star s = s) (hr : star r = r)
    (hrSr : r * S * r ≤ 1) : s * r * S * star (s * r) ≤ s * s := by
  have h := star_left_conjugate_le_conjugate hrSr s
  rw [hs] at h
  rw [star_mul, hs, hr]
  simpa only [mul_assoc, mul_one] using h

private theorem filter_residual {A : Type u} [Qudit A] [Nontrivial A]
    {σ W : L A} (hσ : 0 ≤ σ) (hW : 0 ≤ W) :
    let G := CFC.sqrt σ * CFC.rpow (σ + W) (-1 / 2 : ℝ)
    (Tr ((1 - G) * (σ + W) * star (1 - G))).re ≤ (Tr W).re := by
  let S := σ + W
  let G := CFC.sqrt σ * CFC.rpow S (-1 / 2 : ℝ)
  change (Tr ((1 - G) * S * star (1 - G))).re ≤ _
  have hS : 0 ≤ S := add_nonneg hσ hW
  have hs := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg σ)).star_eq
  have hi : star (CFC.rpow S (-1 / 2 : ℝ)) = CFC.rpow S (-1 / 2 : ℝ) :=
    (IsSelfAdjoint.of_nonneg CFC.rpow_nonneg).star_eq
  have hGS : G * S = CFC.sqrt σ * CFC.sqrt S := by
    dsimp only [G]
    rw [mul_assoc, inv_sqrt_mul hS]
  have hGSG : G * S * star G ≤ σ := by
    have h := filter_conj_le (CFC.sqrt σ) (CFC.rpow S (-1 / 2 : ℝ)) S hs hi
      (inv_sqrt_sandwich hS)
    rwa [CFC.sqrt_mul_sqrt_self σ hσ] at h
  have hp := tr_pair_nonneg (CFC.sqrt_nonneg σ)
    (sub_nonneg.mpr (CFC.sqrt_le_sqrt σ S (le_add_of_nonneg_right hW)))
  rw [mul_sub, map_sub, Complex.sub_re, CFC.sqrt_mul_sqrt_self σ hσ] at hp
  have ht := tr_mono hGSG
  rw [hGS] at ht
  rw [tr_residual hS, hGS]
  have htr : (Tr S).re = (Tr σ).re + (Tr W).re := by
    simp only [S, map_add, Complex.add_re]
  linarith

private theorem filter_overlap {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : State A) (ε t : ℝ) (W : L A)
    (ht : 0 < t) (hW : W.IsPositive)
    (hdom : (σ.1 + W - t • ρ.1).IsPositive)
    (htr : (Tr W).re ≤ (1 - ε) * t)
    (hq : ε ≤ (Tr ((CFC.sqrt σ.1 * CFC.rpow (σ.1 + W) (-1 / 2 : ℝ)) *
      ρ.1 * star (CFC.sqrt σ.1 * CFC.rpow (σ.1 + W) (-1 / 2 : ℝ)))).re) :
    ε ≤ (Tr ((CFC.sqrt σ.1 * CFC.rpow (σ.1 + W) (-1 / 2 : ℝ)) * ρ.1)).re := by
  let G := CFC.sqrt σ.1 * CFC.rpow (σ.1 + W) (-1 / 2 : ℝ)
  change ε ≤ (Tr (G * ρ.1)).re
  change ε ≤ (Tr (G * ρ.1 * star G)).re at hq
  have hρ := (LinearMap.nonneg_iff_isPositive _).mpr ρ.2.1
  have hσ := (LinearMap.nonneg_iff_isPositive _).mpr σ.2.1
  have hW' := (LinearMap.nonneg_iff_isPositive _).mpr hW
  have hd := sub_nonneg.mp ((LinearMap.nonneg_iff_isPositive _).mpr hdom)
  have hc := (tr_mono (conj_mono hd (1 - G))).trans (filter_residual hσ hW')
  rw [mul_smul_comm, smul_mul_assoc, tr_smul, tr_residual hρ,
    ρ.2.2, Complex.one_re] at hc
  nlinarith

private theorem vec_marginal {A : Type u} [Qudit A] (B : L A) :
    TrRight (outer_product (vec (stdOrthonormalBasis ℂ A).toBasis B)
      (vec (stdOrthonormalBasis ℂ A).toBasis B)) = B * star B := by
  classical
  let b := stdOrthonormalBasis ℂ A
  change traceOutRight (outer_product (vec b.toBasis B) (vec b.toBasis B)) = _
  rw [vec_apply, outer_product_sum]
  simp only [OrthonormalBasis.coe_toBasis, map_sum, TrRight_outer_product_tmul_basis,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ext x
  simp only [LinearMap.sum_apply, outer_product_apply, Module.End.mul_apply,
    LinearMap.star_eq_adjoint]
  conv_rhs => rw [← b.sum_repr' (B.adjoint x)]
  simp only [map_sum, map_smul, LinearMap.adjoint_inner_right]

private theorem factor_overlap {A : Type u} [Qudit A] [Nontrivial A]
    (B D : L A) (hB : B * star B ≠ 0) (hD : D * star D ≠ 0) :
    Complex.normSq (Tr (star B * D)) ≤
      rootFidelity (B * star B) (D * star D) ^ 2 := by
  have hp (K : L A) : (K * star K).IsPositive :=
    (LinearMap.nonneg_iff_isPositive _).mp (mul_star_self_nonneg K)
  have hd : max (Module.finrank ℂ (LinearMap.range (B * star B)))
      (Module.finrank ℂ (LinearMap.range (D * star D))) ≤ Module.finrank ℂ A :=
    max_le (LinearMap.finrank_range_le _) (LinearMap.finrank_range_le _)
  have h := (GourConditionalEntropy.w39_uhlmann_psd (E := A)
    (B * star B) (D * star D) (hp B) (hp D) hB hD hd).1.2
    ⟨vec (stdOrthonormalBasis ℂ A).toBasis B,
      vec (stdOrthonormalBasis ℂ A).toBasis D,
      vec_marginal B, vec_marginal D, rfl⟩
  simpa only [inner_vec_eq_trace, LinearMap.star_eq_adjoint,
    Module.End.mul_eq_comp] using h

private theorem fidelity_nonneg {A : Type u} [Qudit A] (X Y : L A) :
    0 ≤ rootFidelity X Y := tr_nonneg (CFC.sqrt_nonneg _)

private theorem sqrt_gram {A : Type u} [Qudit A] {R : L A} (hR : 0 ≤ R) :
    CFC.sqrt R * star (CFC.sqrt R) = R := by
  rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg R)).star_eq,
    CFC.sqrt_mul_sqrt_self R hR]

private theorem filter_gram {A : Type u} [Qudit A] {R : L A}
    (hR : 0 ≤ R) (G : L A) :
    (G * CFC.sqrt R) * star (G * CFC.sqrt R) = G * R * star G := by
  rw [star_mul]
  calc
    _ = G * (CFC.sqrt R * star (CFC.sqrt R)) * star G := by
      simp only [mul_assoc]
    _ = _ := by rw [sqrt_gram hR]

private theorem sqrt_cyclic {A : Type u} [Qudit A] {R : L A}
    (hR : 0 ≤ R) (G : L A) :
    Tr (star (CFC.sqrt R) * (G * CFC.sqrt R)) = Tr (G * R) := by
  rw [LinearMap.trace_mul_comm ℂ (star (CFC.sqrt R)), mul_assoc, sqrt_gram hR]

private theorem overlap_le_fidelity {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) (G : L A) (hX : G * ρ.1 * star G ≠ 0) :
    (Tr (G * ρ.1)).re ≤ rootFidelity ρ.1 (G * ρ.1 * star G) := by
  have hρ := (LinearMap.nonneg_iff_isPositive _).mpr ρ.2.1
  have h := factor_overlap (CFC.sqrt ρ.1) (G * CFC.sqrt ρ.1)
    (by rw [sqrt_gram hρ]; exact ρ.2.ne_zero) (by rwa [filter_gram hρ])
  rw [sqrt_gram hρ, filter_gram hρ, sqrt_cyclic hρ, Complex.normSq_apply] at h
  have hf := fidelity_nonneg ρ.1 (G * ρ.1 * star G)
  nlinarith [sq_nonneg (Tr (G * ρ.1)).im]

-- The two `CFC.sqrt` computations behind `fidelity_smul` and `fidelity_self`, over an abstract
-- C⋆-algebra so that `CFC.sqrt_unique` is elaborated without the costly `L A` instance searches.
private theorem fidelity_sqrt_smul {R : Type*} [CStarAlgebra R] [PartialOrder R]
    [StarOrderedRing R] (b a : R) (ha : 0 ≤ a) (c : ℝ) (hc : 0 ≤ c) :
    CFC.sqrt (CFC.sqrt b * (c • a) * CFC.sqrt b) =
      Real.sqrt c • CFC.sqrt (CFC.sqrt b * a * CFC.sqrt b) := by
  have hs : star (CFC.sqrt b) = CFC.sqrt b :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)).star_eq
  have hp : 0 ≤ CFC.sqrt b * a * CFC.sqrt b := by
    simpa only [hs] using star_left_conjugate_nonneg ha (CFC.sqrt b)
  rw [mul_smul_comm, smul_mul_assoc]
  apply CFC.sqrt_unique
  · rw [smul_mul_smul_comm, Real.mul_self_sqrt hc, CFC.sqrt_mul_sqrt_self _ hp]
  · exact smul_nonneg (Real.sqrt_nonneg c) (CFC.sqrt_nonneg _)

private theorem fidelity_sqrt_self {R : Type*} [CStarAlgebra R] [PartialOrder R]
    [StarOrderedRing R] (a : R) (ha : 0 ≤ a) :
    CFC.sqrt (CFC.sqrt a * a * CFC.sqrt a) = a := by
  have hs : CFC.sqrt a * a * CFC.sqrt a = a * a := by
    calc
      _ = CFC.sqrt a * (CFC.sqrt a * CFC.sqrt a) * CFC.sqrt a := by
        rw [CFC.sqrt_mul_sqrt_self _ ha]
      _ = (CFC.sqrt a * CFC.sqrt a) * (CFC.sqrt a * CFC.sqrt a) := by simp only [mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self _ ha]
  rw [hs]
  exact CFC.sqrt_unique rfl ha

private theorem fidelity_smul {A : Type u} [Qudit A] (ρ σ : L A)
    (hσ : 0 ≤ σ) (c : ℝ) (hc : 0 ≤ c) :
    rootFidelity ρ (c • σ) = Real.sqrt c * rootFidelity ρ σ := by
  unfold rootFidelity
  rw [fidelity_sqrt_smul ρ σ hσ c hc, tr_smul]

private theorem fidelity_self {A : Type u} [Qudit A] (ρ : State A) :
    rootFidelity ρ.1 ρ.1 = 1 := by
  have hρ := (LinearMap.nonneg_iff_isPositive _).mpr ρ.2.1
  unfold rootFidelity
  rw [fidelity_sqrt_self ρ.1 hρ, ρ.2.2, Complex.one_re]

private theorem normalized_fidelity {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) (G : L A) (ε : ℝ)
    (hq : 0 < (Tr (G * ρ.1 * star G)).re)
    (hq1 : (Tr (G * ρ.1 * star G)).re ≤ 1)
    (hov : ε ≤ (Tr (G * ρ.1)).re) :
    ε ≤ rootFidelity ρ.1 ((Tr (G * ρ.1 * star G)).re⁻¹ •
      (G * ρ.1 * star G)) := by
  let X := G * ρ.1 * star G
  have hX : 0 ≤ X := star_right_conjugate_nonneg
    ((LinearMap.nonneg_iff_isPositive _).mpr ρ.2.1) G
  have hX0 : X ≠ 0 := by
    intro hz
    change 0 < (Tr X).re at hq
    simp only [hz, map_zero, Complex.zero_re, lt_self_iff_false] at hq
  have hf := hov.trans (overlap_le_fidelity ρ G hX0)
  change ε ≤ rootFidelity ρ.1 ((Tr X).re⁻¹ • X)
  rw [fidelity_smul _ _ hX _ (inv_nonneg.mpr hq.le)]
  have hs : 1 ≤ Real.sqrt (Tr X).re⁻¹ :=
    Real.one_le_sqrt.mpr ((one_le_inv₀ hq).mpr hq1)
  exact hf.trans (le_mul_of_one_le_left (fidelity_nonneg _ _) hs)

private theorem log_bound {ε t q b : ℝ} (hε : ε ∈ Set.Ioo 0 1)
    (ht : 0 < t) (hq : ε ≤ q) (hb : 0 < b) (hbt : b ≤ (1 - ε) * t) :
    Real.logb 2 (t * q)⁻¹ + Real.logb 2 (ε / (1 - ε)) ≤ -Real.logb 2 b := by
  have hq0 := hε.1.trans_le hq
  have he0 := sub_pos.mpr hε.2
  have htq := mul_pos ht hq0
  have hm : b * ε ≤ (t * q) * (1 - ε) := by nlinarith
  have hl := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    (mul_pos hb hε.1) (mul_pos htq he0)).mpr hm
  rw [Real.logb_mul hb.ne' hε.1.ne', Real.logb_mul htq.ne' he0.ne'] at hl
  rw [Real.logb_inv, Real.logb_div hε.1.ne' he0.ne']
  linarith

private theorem entropy_bound {A : Type u} [Qudit A] (ρ σ τ : State A)
    (ε t q : ℝ) (hε : ε ∈ Set.Ioo 0 1) (ht : 0 < t) (hq : ε ≤ q)
    (hb : 0 < beta ρ.1 σ.1 ε) (hbt : beta ρ.1 σ.1 ε ≤ (1 - ε) * t)
    (hd : (t * q) • τ.1 ≤ σ.1) :
    dm τ.1 σ.1 + ((Real.logb 2 (ε / (1 - ε)) : ℝ) : EReal) ≤ dh ρ.1 σ.1 ε := by
  have htq := mul_pos ht (hε.1.trans_le hq)
  have hdom : τ.1 ≤ (t * q)⁻¹ • σ.1 := by
    have h := smul_le_smul_of_nonneg_left hd (inv_nonneg.mpr htq.le)
    rwa [inv_smul_smul₀ htq.ne'] at h
  have hdm : dm τ.1 σ.1 ≤ ((Real.logb 2 (t * q)⁻¹ : ℝ) : EReal) := by
    apply OPT.OrderedCone.maxRelEntropy_le_of_domination
    rwa [Real.rpow_logb (by norm_num) (by norm_num) (inv_pos.mpr htq)]
  have hdh : dh ρ.1 σ.1 ε = ((-Real.logb 2 (beta ρ.1 σ.1 ε) : ℝ) : EReal) := by
    rw [dh, OPT.binaryNegLog2, if_neg (ne_of_gt (Real.toNNReal_pos.mpr hb)),
      Real.coe_toNNReal _ hb.le]
  rw [hdh]
  calc
    _ ≤ ((Real.logb 2 (t * q)⁻¹ : ℝ) : EReal) +
        ((Real.logb 2 (ε / (1 - ε)) : ℝ) : EReal) := add_le_add hdm le_rfl
    _ ≤ _ := by
      rw [← EReal.coe_add, EReal.coe_le_coe_iff]
      exact log_bound hε ht hq hb hbt

theorem gsl_c18b :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (ε : ℝ), ε ∈ Set.Ioo 0 1 →
  ∃ τ : State.{u} A, ε ≤ rootFidelity.{u} ρ.1 τ.1 ∧ td.{u} ρ.1 τ.1 ≤ Real.sqrt (1-ε^2) ∧
    dm.{u} τ.1 σ.1 + ((Real.logb 2 (ε/(1-ε)) : ℝ) : EReal) ≤ dh.{u} ρ.1 σ.1 ε)
:= by
  intro A _ _ ρ σ ε hε
  by_cases hb : 0 < beta ρ.1 σ.1 ε
  · obtain ⟨t, W, ht, hW, hdom, heq⟩ := GourResource.gsl_c07b ρ σ ε hε
    have hWtr : 0 ≤ (Tr W).re :=
      tr_nonneg ((LinearMap.nonneg_iff_isPositive _).mpr hW)
    have ht0 : 0 < t := by nlinarith [hε.1, hε.2]
    have htr : (Tr W).re ≤ (1 - ε) * t := by linarith
    obtain ⟨_, hqε, hq1, hq0, hτ, horder⟩ := GourResource.gsl_c18a.{u} ρ σ ε t W hε ht0 hW hdom htr
    let G := CFC.sqrt σ.1 * CFC.rpow (σ.1 + W) (-1 / 2 : ℝ)
    let X := G * ρ.1 * star G
    let q := (Tr X).re
    let τ : State A := ⟨q⁻¹ • X, hτ⟩
    have hov : ε ≤ (Tr (G * ρ.1)).re :=
      filter_overlap ρ σ ε t W ht0 hW hdom htr hqε
    have hf : ε ≤ rootFidelity ρ.1 τ.1 :=
      normalized_fidelity ρ G ε hq0 hq1 hov
    refine ⟨τ, hf, ?_, ?_⟩
    · apply (GourResource.gsl_b04.{u}.2.2.2.2 ρ τ).trans
      apply Real.sqrt_le_sqrt
      nlinarith [hε.1]
    · exact entropy_bound ρ σ τ ε t q hε ht0 hqε hb (by linarith) horder
  · have hdh : dh ρ.1 σ.1 ε = ⊤ := by
      rw [dh, OPT.binaryNegLog2,
        if_pos (Real.toNNReal_eq_zero.mpr (le_of_not_gt hb))]
    refine ⟨ρ, ?_, ?_, ?_⟩
    · rw [fidelity_self]
      exact hε.2.le
    · apply (GourResource.gsl_b04.{u}.2.2.2.2 ρ ρ).trans
      rw [fidelity_self]
      apply Real.sqrt_le_sqrt
      nlinarith [hε.1, hε.2]
    · rw [hdh]
      exact le_top

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_c19 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (ε : ℝ), ε ∈ Set.Ioo 0 1 →
  smoothMax.{u} ρ.1 σ.1 (Real.sqrt (1-ε^2)) +
    ((Real.logb 2 (ε/(1-ε)) : ℝ) : EReal) ≤ dh.{u} ρ.1 σ.1 ε)
:= by
  intro A _ _ ρ σ ε hε
  obtain ⟨τ, _, hdist, hbound⟩ := GourResource.gsl_c18b.{u} ρ σ ε hε
  have hinf : smoothMax ρ.1 σ.1 (Real.sqrt (1-ε^2)) ≤ dm τ.1 σ.1 :=
    iInf_le_of_le τ.1 (iInf_le_of_le ⟨τ.2, hdist⟩ le_rfl)
  exact (add_le_add hinf le_rfl).trans hbound

end GourResource

