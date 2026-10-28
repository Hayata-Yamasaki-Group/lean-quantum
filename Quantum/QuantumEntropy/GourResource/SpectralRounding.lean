import Quantum.QuantumEntropy.SandwichedRenyiLMCompat.GSLCore
import Quantum.QuantumEntropy.GourResource.JordanTesting
import Quantum.QuantumEntropy.GourResource.KWTestingBridge
import Quantum.QuantumEntropy.GourResource.SpectralGrid
import Quantum.QuantumEntropy.GourResource.TestingSDP
/-
Sandwiches the unnormalized CFC rounding between X and 2^c X, and sandwiches the trace as well.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
/-
Obtains the density property and full support of the trace-normalized rounded operator.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
/-
Keeps 2^(−c)X≤rounded≤2^c X after normalization.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/
/-
Bounds the number of eigenvalues of rounded by n+1.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7.
-/


open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower ℝ ℂ (L H) :=
  RestrictScalars.isScalarTower ℝ ℂ (L H)

namespace GourResource


open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem spectrum_real_finite {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (X : L.{u} A) : (spectrum ℝ X).Finite := by
  rw [← spectrum.preimage_algebraMap ℂ]
  exact (Module.End.finite_spectrum X).preimage
    (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

private theorem scalar_round_bounds {x g c : ℝ} (hx : 0 < x)
    (hg : Real.logb 2 x ≤ g ∧ g < Real.logb 2 x + c) :
    x ≤ Real.rpow 2 g ∧ Real.rpow 2 g ≤ Real.rpow 2 c * x := by
  have hlog : Real.rpow 2 (Real.logb 2 x) = x :=
    Real.rpow_logb (by norm_num) (by norm_num) hx
  constructor
  · calc
      x = Real.rpow 2 (Real.logb 2 x) := hlog.symm
      _ ≤ Real.rpow 2 g := Real.rpow_le_rpow_of_exponent_le (by norm_num) hg.1
  · calc
      Real.rpow 2 g ≤ Real.rpow 2 (Real.logb 2 x + c) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hg.2.le
      _ = Real.rpow 2 (Real.logb 2 x) * Real.rpow 2 c :=
        Real.rpow_add (by norm_num) _ _
      _ = Real.rpow 2 c * x := by rw [hlog, mul_comm]

private theorem trace_re_mono {A : Type u} [Qudit.{u} A]
    {X Y : L.{u} A} (hXY : X ≤ Y) : (Tr X).re ≤ (Tr Y).re := by
  have hpos := (LinearMap.nonneg_iff_isPositive (Y - X)).mp (sub_nonneg.mpr hXY)
  have htrace := (Complex.nonneg_iff.mp hpos.trace_nonneg).1
  simpa only [map_sub, Complex.sub_re, sub_nonneg] using htrace

theorem gsl_y17 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (X : State.{u} A) (lam : ℝ) (n : ℕ),
  lam ∈ Set.Ioc 0 1 → 0 < n →
  (lam^n/3 : ℝ) • (1 : L.{u} A) ≤ X.1 →
  X.1 ≤ roundRaw.{u} lam n X.1 ∧
  roundRaw.{u} lam n X.1 ≤ (Real.rpow 2 (cBits lam n) : ℝ) • X.1 ∧
  1 ≤ (Tr.{u} (roundRaw.{u} lam n X.1)).re ∧
  (Tr.{u} (roundRaw.{u} lam n X.1)).re ≤ Real.rpow 2 (cBits lam n)
:= by
  intro A _ _ X lam n hlam _hn hfloor
  have _hc : 0 < cBits lam n := (GourResource.gsl_y14 lam hlam).1 n
  have hX : IsSelfAdjoint X.1 :=
    IsSelfAdjoint.of_nonneg ((LinearMap.nonneg_iff_isPositive X.1).mpr X.2.1)
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ X.1) :=
    fun f => (spectrum_real_finite X.1).continuousOn f
  have hspec : ∀ x ∈ spectrum ℝ X.1, 0 < x := by
    have hfloor' : algebraMap ℝ (L A) (lam ^ n / 3) ≤ X.1 := by
      simpa only [Algebra.algebraMap_eq_smul_one] using hfloor
    intro x hx
    exact (div_pos (pow_pos hlam.1 n) (by norm_num)).trans_le
      ((algebraMap_le_iff_le_spectrum hX).mp hfloor' x hx)
  have hscalar : ∀ x ∈ spectrum ℝ X.1,
      x ≤ Real.rpow 2 (grid lam n x) ∧
      Real.rpow 2 (grid lam n x) ≤ Real.rpow 2 (cBits lam n) * x := by
    intro x hx
    exact scalar_round_bounds (hspec x hx) (GourResource.gsl_y15 lam x n hlam (hspec x hx))
  have hlo : X.1 ≤ roundRaw lam n X.1 := by
    unfold roundRaw
    nth_rw 1 [← cfc_id' ℝ X.1 hX]
    exact (cfc_le_iff _ _ X.1 (hcont _) (hcont _) hX).mpr fun x hx => (hscalar x hx).1
  have hhi : roundRaw lam n X.1 ≤ Real.rpow 2 (cBits lam n) • X.1 := by
    rw [roundRaw, ← cfc_const_mul_id (Real.rpow 2 (cBits lam n)) X.1 hX]
    exact (cfc_le_iff _ _ X.1 (hcont _) (hcont _) hX).mpr fun x hx => (hscalar x hx).2
  refine ⟨hlo, hhi, ?_, ?_⟩
  · simpa only [X.2.2, Complex.one_re] using trace_re_mono hlo
  · simpa only [LinearMap.map_smul_of_tower, X.2.2, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      mul_one, mul_zero, sub_zero] using trace_re_mono hhi

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_y18 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (X : State.{u} A) (lam : ℝ) (n : ℕ),
  lam ∈ Set.Ioc 0 1 → 0 < n →
  (lam^n/3 : ℝ) • (1 : L.{u} A) ≤ X.1 →
  IsDensity.{u} (rounded.{u} lam n X.1) ∧
  IsPositiveDefinite.{u} (rounded.{u} lam n X.1)
:= by
  intro A _ _ X lam n hlam hn hbound
  obtain ⟨hXraw, _, htrace, _⟩ := GourResource.gsl_y17.{u} X lam n hlam hn hbound
  have ht : 0 < (Tr (roundRaw lam n X.1)).re := lt_of_lt_of_le zero_lt_one htrace
  have hraw : (0 : L A) ≤ roundRaw lam n X.1 :=
    le_trans ((LinearMap.nonneg_iff_isPositive _).mpr X.2.1) hXraw
  have hrawPos := (LinearMap.nonneg_iff_isPositive _).mp hraw
  have hreal : ((Tr (roundRaw lam n X.1)).re : ℂ) =
      Tr (roundRaw lam n X.1) := by
    exact Complex.ext rfl
      (by simpa using (Complex.nonneg_iff.mp hrawPos.trace_nonneg).2)
  have hpd : roundRaw lam n X.1 ∈ SandwichedRenyiRelativeEntropy.pdSetLM := by
    have hle : ((lam ^ n / 3 : ℝ) : ℂ) • (1 : L A) ≤ roundRaw lam n X.1 := by
      simpa only [Complex.coe_smul] using le_trans hbound hXraw
    have hpos : (0 : ℝ) < lam ^ n / 3 := div_pos (pow_pos hlam.1 n) (by norm_num)
    simpa only [sub_add_cancel] using
      SandwichedRenyiRelativeEntropy.pdSetLM_add_nonneg (sub_nonneg.mpr hle)
        (SandwichedRenyiRelativeEntropy.pos_smul_one_pdSetLM hpos)
  have hrounded : IsPositiveDefinite (rounded lam n X.1) := by
    apply (OPT.isPositiveDefinite_iff_mem_pdSetLM _).mpr
    simpa only [rounded, Complex.coe_smul] using
      SandwichedRenyiRelativeEntropy.pdSetLM_pos_smul hpd (inv_pos.mpr ht)
  refine ⟨⟨hrounded.1, ?_⟩, hrounded⟩
  unfold rounded
  rw [← Complex.coe_smul, map_smul, smul_eq_mul, Complex.ofReal_inv, hreal]
  exact inv_mul_cancel₀ (fun hz => ht.ne' (by simp [hz]))

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_y19 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (X : State.{u} A) (lam : ℝ) (n : ℕ),
  lam ∈ Set.Ioc 0 1 → 0 < n →
  (lam^n/3 : ℝ) • (1 : L.{u} A) ≤ X.1 →
  IsDensity.{u} (rounded.{u} lam n X.1) ∧ IsPositiveDefinite.{u} (rounded.{u} lam n X.1) ∧
  (Real.rpow 2 (-cBits lam n) : ℝ) • X.1 ≤ rounded.{u} lam n X.1 ∧
  rounded.{u} lam n X.1 ≤ (Real.rpow 2 (cBits lam n) : ℝ) • X.1
:= by
  intro A instQ instN X lam n hlam hn hfloor
  obtain ⟨hrawLower, hrawUpper, htraceLower, htraceUpper⟩ :=
    GourResource.gsl_y17.{u} X lam n hlam hn hfloor
  obtain ⟨hdensity, hdefinite⟩ := GourResource.gsl_y18.{u} X lam n hlam hn hfloor
  have hX : 0 ≤ X.1 := (LinearMap.nonneg_iff_isPositive _).mpr X.2.1
  have hraw : 0 ≤ roundRaw lam n X.1 := hX.trans hrawLower
  have htracePos : 0 < (Tr (roundRaw lam n X.1)).re :=
    lt_of_lt_of_le zero_lt_one htraceLower
  have hpowPos : 0 < Real.rpow 2 (cBits lam n) := Real.rpow_pos_of_pos (by norm_num) _
  have hinvLower : (Real.rpow 2 (cBits lam n))⁻¹ ≤
      ((Tr (roundRaw lam n X.1)).re)⁻¹ :=
    (inv_le_inv₀ hpowPos htracePos).mpr htraceUpper
  have hinvUpper : ((Tr (roundRaw lam n X.1)).re)⁻¹ ≤ (1 : ℝ) := by
    simpa only [inv_one] using (inv_le_inv₀ htracePos zero_lt_one).mpr htraceLower
  refine ⟨hdensity, hdefinite, ?_, ?_⟩
  · have hneg : Real.rpow 2 (-cBits lam n) = (Real.rpow 2 (cBits lam n))⁻¹ :=
      Real.rpow_neg (by norm_num) (cBits lam n)
    rw [hneg]
    exact (smul_le_smul_of_nonneg_right hinvLower hX).trans
      (smul_le_smul_of_nonneg_left hrawLower (inv_nonneg.mpr htracePos.le))
  · exact (show rounded lam n X.1 ≤ roundRaw lam n X.1 from
      (by simpa only [rounded, one_smul] using
        smul_le_smul_of_nonneg_right hinvUpper hraw)).trans hrawUpper

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem realSpectrumFinite {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (X : L.{u} A) : (spectrum ℝ X).Finite := by
  rw [← spectrum.preimage_algebraMap ℂ]
  exact (Module.End.finite_spectrum X).preimage
    (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

private theorem densitySpectrumSubset {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (X : State.{u} A) (a : ℝ) (hlo : a • (1 : L.{u} A) ≤ X.1) :
    spectrum ℝ X.1 ⊆ Set.Icc a 1 := by
  have hsa : IsSelfAdjoint X.1 := X.2.1.isSelfAdjoint
  have hnorm : ‖X.1‖ ≤ 1 := by
    simpa only [X.2.2, Complex.one_re] using
      SandwichedRenyiRelativeEntropy.norm_le_re_trace_lm
        ((LinearMap.nonneg_iff_isPositive _).mpr X.2.1)
  intro x hx
  refine ⟨?_, (Real.le_norm_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans hnorm)⟩
  exact (algebraMap_le_iff_le_spectrum hsa).mp
    (by simpa only [Algebra.algebraMap_eq_smul_one] using hlo) x hx

private theorem eigenvalueCard {A : Type u} [Qudit.{u} A] (X : L.{u} A) :
    Fintype.card (spectralEigenvalue X) = (spectrum ℂ X).ncard := by
  rw [← Nat.card_eq_fintype_card]
  change {z : ℂ | Module.End.HasEigenvalue X z}.ncard = (spectrum ℂ X).ncard
  congr 1
  ext z
  exact Module.End.hasEigenvalue_iff_mem_spectrum

theorem gsl_y20 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (X : State.{u} A) (lam : ℝ) (n : ℕ),
  lam ∈ Set.Ioc 0 1 → 0 < n →
  (lam^n/3 : ℝ) • (1 : L.{u} A) ≤ X.1 →
  IsDensity.{u} (rounded.{u} lam n X.1) ∧
  Fintype.card (spectralEigenvalue.{u} (rounded.{u} lam n X.1)) ≤ n+1
:= by
  intro A _ _ X lam n hlam hn hlo
  have hden := (GourResource.gsl_y18.{u} X lam n hlam hn hlo).1
  refine ⟨hden, ?_⟩
  let f : ℝ → ℝ := fun x => Real.rpow 2 (grid lam n x)
  let S : Set ℝ := f '' Set.Icc (lam^n/3) 1
  obtain ⟨hS, hcard⟩ := GourResource.gsl_y16 lam n hlam hn
  change S.Finite at hS
  change S.ncard ≤ n+1 at hcard
  let t : ℝ := (Tr (roundRaw lam n X.1)).re
  have ht : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one
    (GourResource.gsl_y17.{u} X lam n hlam hn hlo).2.2.1)
  have hraw : spectrum ℝ (roundRaw lam n X.1) = f '' spectrum ℝ X.1 :=
    cfc_map_spectrum f X.1 X.2.1.isSelfAdjoint ((realSpectrumFinite X.1).continuousOn f)
  have hrawSub : spectrum ℝ (roundRaw lam n X.1) ⊆ S := by
    rw [hraw]
    exact Set.image_mono (densitySpectrumSubset X (lam^n/3) hlo)
  let g : ℝ → ℝ := fun x => t⁻¹ * x
  have hrounded : spectrum ℝ (rounded lam n X.1) = g '' spectrum ℝ (roundRaw lam n X.1) := by
    simpa only [rounded, Units.smul_def, Units.val_mk0, ← Set.image_smul,
      smul_eq_mul] using
      (spectrum.unit_smul_eq_smul (roundRaw lam n X.1) (Units.mk0 t⁻¹ (inv_ne_zero ht)))
  have hsub : spectrum ℝ (rounded lam n X.1) ⊆ g '' S := by
    rw [hrounded]
    exact Set.image_mono hrawSub
  have hcomplex : spectrum ℂ (rounded lam n X.1) =
      (algebraMap ℝ ℂ) '' spectrum ℝ (rounded lam n X.1) :=
    hden.1.isSelfAdjoint.spectrumRestricts.algebraMap_image.symm
  rw [eigenvalueCard, hcomplex]
  exact (Set.ncard_image_le (realSpectrumFinite _)).trans
    ((Set.ncard_le_ncard hsub (hS.image g)).trans ((Set.ncard_image_le hS).trans hcard))

end GourResource

