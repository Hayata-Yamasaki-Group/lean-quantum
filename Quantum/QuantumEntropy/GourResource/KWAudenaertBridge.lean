/-
Obtains the Audenaert inequality for the trace norm and mixed powers for positive X,Y and α∈[0,1].
Proof construction: imports AudenaertChernoff.spectral_inequality and connects it with GourConditionalEntropy.w40_hermitian_norm_dictionary. Interior points are handled by α↦1−α, and endpoints by CFC.rpow_zero and the evaluation of the trace norm. The bridge between carriers is used for comparison, not as a type dependency.
-/
import Quantum.QuantumEntropy.GourResource.KWCarrierBridge
import Quantum.TraceInequality.AudenaertChernoff.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesDecouplingNorm.GSLCoreRetained
import Quantum.OperationalProbabilistic.Framework.TestingRegionHockeyStick.GSLCore
import Quantum.OperationalProbabilistic.OperationalFidelity.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesMinDefinitions.GSLCore
import Quantum.QuantumModel.HighInterfaces.GSLCoreRetained
import Quantum.QuantumModel.NativeFidelity.GSLCoreRetained
import Quantum.QuantumModel.SupportFaceDictionary.GSLCore


open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower ℝ ℂ (L H) :=
  RestrictScalars.isScalarTower ℝ ℂ (L H)
open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower NNReal ℂ (L H) :=
  RestrictScalars.isScalarTower NNReal ℂ (L H)

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private noncomputable def b07_conj {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) : L A ≃⋆ₐ[ℂ] L B :=
  (linearToContinuousEndStarAlgEquiv A).trans
    (U.conjStarAlgEquiv.trans (linearToContinuousEndStarAlgEquiv B).symm)

private theorem b07_map_rpow {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (X : L A) (p : ℝ) :
    b07_conj U (CFC.rpow X p) = CFC.rpow (b07_conj U X) p := by
  let φ := b07_conj U
  let f : NNReal → NNReal := fun x => x ^ p
  change φ (cfc f X) = cfc f (φ X)
  have hnn : (0 : L B) ≤ φ X ↔ (0 : L A) ≤ X := by
    conv_lhs => rw [show (0 : L B) = φ 0 from (map_zero φ).symm]
    exact OrderIsoClass.map_le_map_iff φ
  have hspec : spectrum NNReal (φ X) = spectrum NNReal X :=
    AlgEquiv.spectrum_eq (φ.restrictScalars NNReal).toAlgEquiv X
  by_cases h : (0 ≤ X) ∧ ContinuousOn f (spectrum NNReal X)
  · exact StarAlgHomClass.map_cfc (S := ℂ) φ f X h.2
      (map_continuous φ) h.1 (hnn.mpr h.1)
  · rw [cfc_apply_of_not_and X h, map_zero, cfc_apply_of_not_and]
    rwa [hnn, hspec]

-- `CFC.abs` commutes with any multiplicative, `star`-preserving map that commutes with the
-- square-root power. Stated over abstract C⋆-algebras so that the `CFC.abs` unfolding is
-- elaborated without the costly `L A` instance searches.
private theorem b07_abs_of_map {R S : Type*} [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
    [CStarAlgebra S] [PartialOrder S] [StarOrderedRing S] (φ : R → S)
    (hmul : ∀ a b : R, φ (a * b) = φ a * φ b) (hstar : ∀ a : R, φ (star a) = star (φ a))
    (hφ : ∀ a : R, φ (a ^ (1 / 2 : ℝ)) = φ a ^ (1 / 2 : ℝ)) (a : R) :
    φ (CFC.abs a) = CFC.abs (φ a) := by
  simp only [CFC.abs, CFC.sqrt_eq_rpow, hφ, hmul, hstar]

private theorem b07_map_abs {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (X : L A) :
    b07_conj U (CFC.abs X) = CFC.abs (b07_conj U X) := by
  exact b07_abs_of_map (b07_conj U) (map_mul _) (map_star _)
    (fun a => by simpa only [← CFC.rpow_eq_pow] using b07_map_rpow U a (1 / 2)) X

private theorem b07_transport {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (X Y : L A) (α : ℝ)
    (htrace : ∀ Z : L A, Tr (b07_conj U Z) = Tr Z)
    (h : (1 / 2 : ℝ) *
      ((Tr (b07_conj U X + b07_conj U Y)).re -
        (Tr (CFC.abs (b07_conj U X - b07_conj U Y))).re) ≤
      (Tr (CFC.rpow (b07_conj U X) (1 - α) *
        CFC.rpow (b07_conj U Y) (1 - (1 - α)))).re) :
    ((Tr X).re + (Tr Y).re - w40T₁ (X - Y)) / 2 ≤
      (Tr (CFC.rpow X (1 - α) * CFC.rpow Y α)).re := by
  have he : 1 - (1 - α) = α := by ring
  rw [he, ← map_add, ← map_sub, ← b07_map_abs, ← b07_map_rpow,
    ← b07_map_rpow, ← map_mul, htrace, htrace, htrace,
    map_add, Complex.add_re] at h
  change ((Tr X).re + (Tr Y).re - (Tr (CFC.abs (X - Y))).re) / 2 ≤ _
  linarith

private theorem b07_interior {A : Type u} [Qudit A] [Nontrivial A]
    (X Y : L A) (hX : X.IsPositive) (hY : Y.IsPositive)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ((Tr X).re + (Tr Y).re - w40T₁ (X - Y)) / 2 ≤
      (Tr (CFC.rpow X (1 - α) * CFC.rpow Y α)).re := by
  obtain ⟨S, _, ⟨U⟩⟩ := GourResource.gsl_b01.1 (A := A)
  have htransport := (GourResource.gsl_b01.2.1 S U).2
  have htrace (Z : L A) : Tr (b07_conj U Z) = Tr Z :=
    (htransport Z Z).2.2.1
  have hx : 0 ≤ b07_conj U X :=
    (LinearMap.nonneg_iff_isPositive _).mpr ((htransport X X).2.1.mp hX)
  have hy : 0 ≤ b07_conj U Y :=
    (LinearMap.nonneg_iff_isPositive _).mpr ((htransport Y Y).2.1.mp hY)
  apply b07_transport U X Y α htrace
  exact AudenaertChernoff.spectral_inequality
    (b07_conj U X) (b07_conj U Y) hx hy (1 - α) (by linarith) (by linarith)

private theorem b07_endpoint_bounds {A : Type u} [Qudit A] [Nontrivial A]
    (X Y : L A) (hX : X.IsPositive) (hY : Y.IsPositive) :
    ((Tr X).re + (Tr Y).re - w40T₁ (X - Y)) / 2 ≤ (Tr X).re ∧
    ((Tr X).re + (Tr Y).re - w40T₁ (X - Y)) / 2 ≤ (Tr Y).re := by
  have hM : IsSelfAdjoint (X - Y) :=
    ((LinearMap.nonneg_iff_isPositive X).mpr hX).isSelfAdjoint.sub
      ((LinearMap.nonneg_iff_isPositive Y).mpr hY).isSelfAdjoint
  have hb := (w40_hermitian_norm_dictionary (X - Y) hM).2.2.1.2
  have ho : -(1 : L A) ≤ 1 := neg_le_self (zero_le_one' (L A))
  have hp : (Tr (X - Y)).re ≤ w40T₁ (X - Y) :=
    hb ⟨1, IsSelfAdjoint.one _, ho, le_rfl, by rw [one_mul]⟩
  have hn : -(Tr (X - Y)).re ≤ w40T₁ (X - Y) :=
    hb ⟨-1, (IsSelfAdjoint.one _).neg, le_rfl, ho, by
      rw [neg_mul, one_mul, map_neg, Complex.neg_re]⟩
  simp only [map_sub, Complex.sub_re] at hp hn
  constructor <;> linarith

/-- Audenaert-type trace inequality (a foundation): for positive operators `X, Y` and
`α ∈ [0, 1]`, `(Re Tr X + Re Tr Y - ‖X - Y‖₁) / 2 ≤ Re Tr (X ^ (1 - α) * Y ^ α)`, including
the endpoints `α = 0, 1`. -/
theorem gsl_b07 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (X Y : L.{u} A) (α : ℝ), X.IsPositive → Y.IsPositive →
  α ∈ Set.Icc 0 1 →
  ((Tr.{u} X).re + (Tr.{u} Y).re - w40T₁.{u} (X-Y)) / 2 ≤
    (Tr.{u} (CFC.rpow X (1-α) * CFC.rpow Y α)).re)
:= by
  intro A _ _ X Y α hX hY hα
  have hx := (LinearMap.nonneg_iff_isPositive X).mpr hX
  have hy := (LinearMap.nonneg_iff_isPositive Y).mpr hY
  by_cases h0 : α = 0
  · subst α
    simpa [CFC.rpow_one X hx, CFC.rpow_zero Y hy]
      using (b07_endpoint_bounds X Y hX hY).1
  by_cases h1 : α = 1
  · subst α
    simpa [CFC.rpow_zero X hx, CFC.rpow_one Y hy]
      using (b07_endpoint_bounds X Y hX hY).2
  exact b07_interior X Y hX hY α
    (lt_of_le_of_ne hα.1 (Ne.symm h0)) (lt_of_le_of_ne hα.2 h1)

end GourResource

