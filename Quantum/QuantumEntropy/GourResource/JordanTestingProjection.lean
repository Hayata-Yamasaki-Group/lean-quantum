/-
The nonnegative threshold projection is an effect, with type-II≤2^(−a)×mass and mass∈[0,1].
Proof construction: keeps the fact that the complement of the strict-positive projection contains the zero eigenspace.
Proof construction: connects the public GourResource.gsl_y26 with the spectral orthogonality of posProj. Jordan decomposition. If the difference is 0, then testHi=I.
Lemma used:
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (X : L.{u} A), X.IsSymmetric →
  (positivePart.{u} X).IsPositive ∧ (positivePart.{u} (-X)).IsPositive ∧
  X = positivePart.{u} X - positivePart.{u} (-X) ∧
  positivePart.{u} X * positivePart.{u} (-X) = 0
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma S2.
-/
import Quantum.QuantumEntropy.GourResource.JordanTesting
import Quantum.QuantumEntropy.GourResource.KWTestingBridge

open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower ℝ ℂ (L H) :=
  RestrictScalars.isScalarTower ℝ ℂ (L H)

namespace GourResource


open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem positivePart_eq_cfc {A : Type u} [Qudit.{u} A]
    (X : L.{u} A) (hX : X.IsSymmetric) :
    positivePart X = cfc (fun x : ℝ => max x 0) X := by
  have hsa : IsSelfAdjoint X := (LinearMap.isSymmetric_iff_isSelfAdjoint X).mp hX
  have heq : positivePart X = X⁺ := by
    change (1 / 2 : ℝ) • (X + CFC.abs X) = X⁺
    rw [add_comm, CFC.abs_add_self X hsa, two_smul]
    module
  rw [heq, CFC.posPart_def, cfcₙ_eq_cfc]
  rfl

private theorem posProj_mul_positivePart {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (X : L.{u} A) (hX : X.IsSymmetric) :
    posProj X * positivePart X = positivePart X := by
  classical
  apply (hX.eigenvectorBasis rfl).toBasis.ext
  intro i
  let v := hX.eigenvectorBasis rfl i
  let μ := hX.eigenvalues rfl i
  have hev : X v = (μ : ℂ) • v := hX.apply_eigenvectorBasis rfl i
  have hspec : μ ∈ spectrum ℝ X :=
    SandwichedRenyiRelativeEntropy.mem_spectrum_real_of_eigenvector_lm
      ((hX.eigenvectorBasis rfl).toBasis.ne_zero i) hev
  have hpart : positivePart X v = ((max μ 0 : ℝ) : ℂ) • v := by
    rw [positivePart_eq_cfc X hX]
    exact SandwichedRenyiRelativeEntropy.cfc_real_apply_eigenvector_lm
      ((LinearMap.isSymmetric_iff_isSelfAdjoint X).mp hX) _ hev hspec
  change posProj X (positivePart X v) = positivePart X v
  rw [hpart, map_smul]
  by_cases hμ : 0 < μ
  · have hmem : v ∈ ⨆ (a : ℝ) (_ : 0 < a), Module.End.eigenspace X (a : ℂ) := by
      exact Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ
        (Module.End.mem_eigenspace_iff.mpr hev))
    have hproj : posProj X v = v := Submodule.starProjection_eq_self_iff.mpr hmem
    rw [hproj]
  · simp only [max_eq_right (le_of_not_gt hμ), Complex.ofReal_zero, zero_smul]

private theorem testHi_effect {A : Type u} [Qudit.{u} A]
    (X σ : L.{u} A) (a : ℝ) : effect (testHi X σ a) := by
  have hP : (posProj ((Real.rpow 2 a : ℝ) • σ - X)).IsSymmetricProjection :=
    Submodule.isSymmetricProjection_starProjection _
  have hQ : (testHi X σ a).IsSymmetricProjection :=
    ⟨hP.isIdempotentElem.one_sub, LinearMap.isPositive_one.isSymmetric.sub hP.isSymmetric⟩
  refine ⟨hQ.isPositive, ?_⟩
  simpa only [testHi, sub_sub_cancel] using hP.isPositive

private theorem pairing_nonneg {A : Type u} [Qudit.{u} A] {X Y : L.{u} A}
    (hX : X.IsPositive) (hY : Y.IsPositive) : 0 ≤ pairing X Y := by
  have hY0 := (LinearMap.nonneg_iff_isPositive _).mpr hY
  have hs : IsSelfAdjoint (CFC.sqrt Y) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg Y)
  have hp : 0 ≤ CFC.sqrt Y * X * CFC.sqrt Y := by
    simpa only [hs.star_eq] using
      star_left_conjugate_nonneg ((LinearMap.nonneg_iff_isPositive _).mpr hX) (CFC.sqrt Y)
  have ht := (Complex.nonneg_iff.mp
    ((LinearMap.nonneg_iff_isPositive _).mp hp).trace_nonneg).1
  have he : Tr (CFC.sqrt Y * X * CFC.sqrt Y) = Tr (X * Y) := by
    rw [mul_assoc, LinearMap.trace_mul_comm ℂ (CFC.sqrt Y), mul_assoc,
      CFC.sqrt_mul_sqrt_self Y hY0]
  change 0 ≤ (Tr (X * Y)).re
  rwa [he] at ht

private theorem pairing_complement_nonpos {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (X : L.{u} A) (hX : X.IsSymmetric) : pairing X (1 - posProj X) ≤ 0 := by
  obtain ⟨_, hN, hdec, _⟩ := GourResource.gsl_y26 X hX
  have hP : (posProj X).IsSymmetricProjection :=
    Submodule.isSymmetricProjection_starProjection _
  have hQ : (1 - posProj X).IsSymmetricProjection :=
    ⟨hP.isIdempotentElem.one_sub,
      LinearMap.isPositive_one.isSymmetric.sub hP.isSymmetric⟩
  have hz : Tr (positivePart X * (1 - posProj X)) = 0 := by
    rw [mul_sub, mul_one, map_sub,
      LinearMap.trace_mul_comm ℂ (positivePart X) (posProj X),
      posProj_mul_positivePart X hX, sub_self]
  have he : pairing X (1 - posProj X) = -pairing (positivePart (-X)) (1 - posProj X) := by
    conv_lhs => arg 1; rw [hdec]
    simp only [pairing, sub_mul, map_sub, hz, zero_sub, Complex.neg_re]
  rw [he]
  exact neg_nonpos.mpr (pairing_nonneg hN hQ.isPositive)

private theorem pairing_mem_Icc {A : Type u} [Qudit.{u} A]
    (ρ : State.{u} A) (M : L.{u} A) (hM : effect M) : pairing ρ.1 M ∈ Set.Icc 0 1 := by
  refine ⟨pairing_nonneg ρ.2.1 hM.1, ?_⟩
  have h := pairing_nonneg ρ.2.1 hM.2
  have he : pairing ρ.1 (1 - M) = 1 - pairing ρ.1 M := by
    simp [pairing, mul_sub, ρ.2.2]
  rw [he] at h
  linarith

theorem gsl_y27 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (a : ℝ),
  effect.{u} (testHi.{u} ρ.1 σ.1 a) ∧
  pairing.{u} σ.1 (testHi.{u} ρ.1 σ.1 a) ≤
    Real.rpow 2 (-a) * testMass.{u} ρ.1 σ.1 a ∧
  testMass.{u} ρ.1 σ.1 a ∈ Set.Icc 0 1
:= by
  intro A _ _ ρ σ a
  have hM := testHi_effect ρ.1 σ.1 a
  refine ⟨hM, ?_, pairing_mem_Icc ρ (testHi ρ.1 σ.1 a) hM⟩
  have hc : 0 < Real.rpow 2 a := Real.rpow_pos_of_pos (by norm_num) a
  have hσ : ((Real.rpow 2 a : ℝ) • σ.1).IsPositive :=
    σ.2.1.smul_of_nonneg ((RCLike.ofReal_nonneg (K := ℂ)).mpr hc.le)
  have hX := hσ.isSymmetric.sub ρ.2.1.isSymmetric
  have h := pairing_complement_nonpos ((Real.rpow 2 a : ℝ) • σ.1 - ρ.1) hX
  have hbound : Real.rpow 2 a * pairing σ.1 (testHi ρ.1 σ.1 a) ≤
      testMass ρ.1 σ.1 a := by
    have hd : Real.rpow 2 a * pairing σ.1 (testHi ρ.1 σ.1 a) -
        pairing ρ.1 (testHi ρ.1 σ.1 a) ≤ 0 := by
      simpa [testHi, pairing, sub_mul, smul_mul_assoc] using h
    exact sub_nonpos.mp hd
  have hpow : Real.rpow 2 (-a) = (Real.rpow 2 a)⁻¹ :=
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) a
  rw [hpow]
  calc
    pairing σ.1 (testHi ρ.1 σ.1 a) =
        (Real.rpow 2 a)⁻¹ * (Real.rpow 2 a * pairing σ.1 (testHi ρ.1 σ.1 a)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    _ ≤ (Real.rpow 2 a)⁻¹ * testMass ρ.1 σ.1 a :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hc.le)

end GourResource

