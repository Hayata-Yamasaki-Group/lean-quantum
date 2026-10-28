/-
Transport of the trace norm and the square-root fidelity by the same isometric coordinates. The single-universe Sys and the universe-polymorphic A, and the square of the fidelity, are kept apart.
-/
import Quantum.QuantumModel.KW.Distances.SineDistanceTriangle.GSLCore
import Quantum.QuantumEntropy.GourResource.KWTestingBridge
import Quantum.QuantumEntropy.Gour.Sandwiched.CyclicTrace.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesMinDefinitions.GSLCore
import Quantum.QuantumModel.KW.Distances.HypothesisTestingCore.Basic


namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem b04_push_mul {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (X Y : L A) :
    push0 U (X * Y) = push0 U X * push0 U Y := by
  ext z
  simp [push0, Module.End.mul_apply]

private theorem b04_push_sub {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (X Y : L A) :
    push0 U (X - Y) = push0 U X - push0 U Y := by
  exact U.toLinearEquiv.conj.map_sub X Y

private theorem b04_push_star {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (X : L A) :
    push0 U (star X) = star (push0 U X) := by
  simp only [push0, LinearMap.star_eq_adjoint, LinearMap.adjoint_comp,
    LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
  rfl

-- `CFC.sqrt` commutes with a multiplicative, positivity-preserving map. Stated over abstract
-- C⋆-algebras so that `CFC.sqrt_unique` is elaborated without the costly `L A`/`L B` instance
-- searches.
private theorem b04_sqrt_of_map {R S : Type*} [CStarAlgebra R] [PartialOrder R]
    [StarOrderedRing R] [CStarAlgebra S] [PartialOrder S] [StarOrderedRing S] (φ : R → S)
    (hmul : ∀ a b : R, φ (a * b) = φ a * φ b) (hpos : ∀ a : R, 0 ≤ a → 0 ≤ φ a)
    (a : R) (ha : 0 ≤ a) : CFC.sqrt (φ a) = φ (CFC.sqrt a) := by
  apply CFC.sqrt_unique
  · rw [← hmul, CFC.sqrt_mul_sqrt_self a ha]
  · exact hpos _ (CFC.sqrt_nonneg a)

private theorem b04_push_sqrt {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (X : L A) (hX : 0 ≤ X) :
    CFC.sqrt (push0 U X) = push0 U (CFC.sqrt X) := by
  refine b04_sqrt_of_map (push0 U) (b04_push_mul U) (fun Y hY => ?_) X hX
  apply (LinearMap.nonneg_iff_isPositive _).mpr
  apply (LinearMap.isPositive_linearIsometryEquiv_conj_iff U).mpr
  exact (LinearMap.nonneg_iff_isPositive _).mp hY

private theorem b04_push_trace {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (X : L A) : Tr (push0 U X) = Tr X :=
  LinearMap.trace_conj' X U.toLinearEquiv

private theorem b04_td_push {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (X Y : L A) :
    td (push0 U X) (push0 U Y) = td X Y := by
  unfold td w40T₁
  rw [← b04_push_sub, ← b04_push_star, ← b04_push_mul,
    b04_push_sqrt U _ (star_mul_self_nonneg _), b04_push_trace]

private theorem b04_fidelity_push {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (X Y : L A) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    rootFidelity (push0 U X) (push0 U Y) = rootFidelity X Y := by
  have hM : 0 ≤ CFC.sqrt X * Y * CFC.sqrt X := by
    simpa only [(CFC.sqrt_nonneg X).isSelfAdjoint.star_eq] using
      star_left_conjugate_nonneg hY (CFC.sqrt X)
  unfold rootFidelity
  rw [b04_push_sqrt U X hX, ← b04_push_mul, ← b04_push_mul,
    b04_push_sqrt U _ hM, b04_push_trace]

open QuantumModel in
private theorem b04_norm_native (S : Sys) (X : L (Space S)) :
    w40T₁ X = NativeTraceDistance.traceNorm X := by
  rfl

open QuantumModel in
private theorem b04_td_native (S : Sys) (ρ σ : DensityMatrix S) :
    td ρ.operator σ.operator = NativeTraceDistance.traceDistance ρ σ := by
  rw [td, b04_norm_native]
  exact div_eq_inv_mul _ _

private theorem b04_fidelity_symm {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : L A) (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    rootFidelity ρ σ = rootFidelity σ ρ := by
  have h := SandwichedRenyiRelativeEntropy.gourSandwichedTraceCyclicEquivalence
    (alpha := 1 / 2) (by norm_num) ρ σ hρ hσ
  norm_num at h
  rw [CFC.rpow_one σ ((LinearMap.nonneg_iff_isPositive _).mpr hσ.1)] at h
  simpa only [rootFidelity, CFC.sqrt_eq_rpow, one_div] using congrArg Complex.re h.symm

private theorem b04_root_product {A : Type u} [Qudit A]
    (X Y : L A) (hX : 0 ≤ X) :
    w40T₁ (CFC.sqrt X * CFC.sqrt Y) = rootFidelity Y X := by
  unfold w40T₁ rootFidelity
  rw [star_mul, (CFC.sqrt_nonneg X).isSelfAdjoint.star_eq,
    (CFC.sqrt_nonneg Y).isSelfAdjoint.star_eq,
    ← mul_assoc, mul_assoc (CFC.sqrt Y), CFC.sqrt_mul_sqrt_self X hX]

open QuantumModel in
private theorem b04_fidelity_native (S : Sys) (ρ σ : DensityMatrix S) :
    rootFidelity ρ.operator σ.operator = NativeFidelity.operatorRootFidelity ρ σ := by
  have hρ : IsDensity ρ.operator :=
    ⟨(LinearMap.nonneg_iff_isPositive _).mp ρ.nonneg, ρ.trace_one⟩
  have hσ : IsDensity σ.operator :=
    ⟨(LinearMap.nonneg_iff_isPositive _).mp σ.nonneg, σ.trace_one⟩
  have h := b04_root_product (A := Space S) ρ.operator σ.operator ρ.nonneg
  exact (b04_fidelity_symm _ _ hρ hσ).trans h.symm

open QuantumModel in
private theorem b04_td_raw (S : Sys) (X Y : L (Space S)) :
    td X Y = (2 : ℝ)⁻¹ * NativeTraceDistance.traceNorm (X - Y) := by
  rw [td, b04_norm_native]
  exact div_eq_inv_mul _ _

open QuantumModel in
private theorem b04_contract {A B : Type u} [Qudit A] [Nontrivial A]
    [Qudit B] [Nontrivial B] (ρ σ : State A) (E : CPTP A B) :
    td (E.toFun ρ.1) (E.toFun σ.1) ≤ td ρ.1 σ.1 := by
  obtain ⟨S, _, ⟨U⟩⟩ := GourResource.gsl_b01.1 (A := A)
  obtain ⟨T, _, ⟨V⟩⟩ := GourResource.gsl_b01.1 (A := B)
  obtain ⟨e, he⟩ := (GourResource.gsl_b01.2.1 S U).1
  obtain ⟨Φ, hΦ, hmap⟩ := GourResource.gsl_b02.2.2.1 S T U V E
  have hc := NativeTraceDistance.traceDistance_contracts (e ρ) (e σ) Φ
    ((isChannel_iff_isCPTP Φ).mpr hΦ)
  rw [← b04_td_raw, ← b04_td_raw] at hc
  rw [he, he, hmap, hmap, b04_td_push, b04_td_push] at hc
  exact hc

private theorem b04_outer_push {A : Type u} [Qudit A] {B : Type} [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (x y : A) :
    push0 U (outer_product x y) = outer_product (U x) (U y) := by
  ext z
  simp only [push0, LinearMap.comp_apply, outer_product_eq_rankOne,
    ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply, map_smul]
  change inner ℂ x (U.symm z) • U y = inner ℂ (U x) z • U y
  rw [← U.inner_map_map x (U.symm z), U.apply_symm_apply]

open QuantumModel in
private theorem b04_pure {A : Type u} [Qudit A] [Nontrivial A]
    (x y : A) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    td (outer_product x x) (outer_product y y) =
      Real.sqrt (1 - Complex.normSq (inner ℂ x y)) := by
  obtain ⟨S, _, ⟨U⟩⟩ := GourResource.gsl_b01.1 (A := A)
  have hx' : ‖U x‖ = 1 := (U.norm_map x).trans hx
  have hy' : ‖U y‖ = 1 := (U.norm_map y).trans hy
  have h := NativeTraceDistance.traceDistance_pureOfUnitVector_eq (U x) (U y) hx' hy'
  rw [← b04_td_native] at h
  change td (outer_product (U x) (U x)) (outer_product (U y) (U y)) = _ at h
  rw [← b04_outer_push, ← b04_outer_push, b04_td_push, U.inner_map_map] at h
  simpa only [Complex.normSq_eq_norm_sq] using h

open QuantumModel in
private theorem b04_fvg {A : Type u} [Qudit A] [Nontrivial A] (ρ σ : State A) :
    td ρ.1 σ.1 ≤ Real.sqrt (1 - rootFidelity ρ.1 σ.1 ^ 2) := by
  obtain ⟨S, _, ⟨U⟩⟩ := GourResource.gsl_b01.1 (A := A)
  obtain ⟨e, he⟩ := (GourResource.gsl_b01.2.1 S U).1
  have h := NativeFidelity.fuchsVanDeGraaf_upper (e ρ) (e σ)
  rw [← b04_td_native, ← b04_fidelity_native, he, he, b04_td_push,
    b04_fidelity_push U _ _ ((LinearMap.nonneg_iff_isPositive _).mpr ρ.2.1)
      ((LinearMap.nonneg_iff_isPositive _).mpr σ.2.1)] at h
  exact h

/-- Correspondence with the finite-dimensional model for the trace distance and the
square-root fidelity (a foundation): agreement and isometric transport of both quantities,
contraction of the trace distance under quantum channels, the bound of the trace distance by
`√(1 - F²)` with `F` the square-root fidelity, and the distance formula for pure states given
by unit vectors. -/
theorem gsl_b04 :
(∀ (S : QuantumModel.Sys) (ρ σ :
  QuantumModel.DensityMatrix S),
  td ρ.operator σ.operator =
    QuantumModel.NativeTraceDistance.traceDistance ρ σ ∧
  rootFidelity ρ.operator σ.operator =
    QuantumModel.NativeFidelity.operatorRootFidelity ρ σ) ∧
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (S : QuantumModel.Sys) (U : A
  ≃ₗᵢ[ℂ] QuantumModel.Space S) (ρ σ : State.{u} A),
  td (push0.{u} U ρ.1) (push0.{u} U σ.1) = td ρ.1 σ.1 ∧
  rootFidelity (push0.{u} U ρ.1) (push0.{u} U σ.1) = rootFidelity ρ.1 σ.1) ∧
((∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] {B : Type u} [Qudit.{u} B] [Nontrivial B]
  (ρ σ : State.{u} A) (E : CPTP.{u,u} A B),
  td.{u} (E.toFun ρ.1) (E.toFun σ.1) ≤ td.{u} ρ.1 σ.1)) ∧
((∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (x y : A), ‖x‖ = 1 → ‖y‖ = 1 →
  td.{u} (QuantumChannel.outer_product x x) (QuantumChannel.outer_product y y) = Real.sqrt (1 -
    Complex.normSq (inner ℂ x y)))) ∧
((∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A),
  td.{u} ρ.1 σ.1 ≤ Real.sqrt (1 - rootFidelity.{u} ρ.1 σ.1 ^ 2)))
:= by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro S ρ σ
    exact ⟨b04_td_native S ρ σ, b04_fidelity_native S ρ σ⟩
  · intro A _ _ S U ρ σ
    exact ⟨b04_td_push U ρ.1 σ.1,
      b04_fidelity_push U ρ.1 σ.1
        ((LinearMap.nonneg_iff_isPositive _).mpr ρ.2.1)
        ((LinearMap.nonneg_iff_isPositive _).mpr σ.2.1)⟩
  · intro A _ _ B _ _ ρ σ E
    exact b04_contract ρ σ E
  · intro A _ _ x y hx hy
    exact b04_pure x y hx hy
  · intro A _ _ ρ σ
    exact b04_fvg ρ σ

end GourResource

