/-
Transports the density, positivity, trace and support inclusion by the same isometric coordinate map of a finite-dimensional Hilbert space, and obtains the compactness of states/effects.
Proof construction: finite-dimensional isometric coordinate transport that aligns the single-universe Sys with a carrier of arbitrary Type u along the Qudit dictionary.
Proof construction: imports QuantumModel.densityOperatorSet_isCompact and QuantumModel.spaceQudit of Skeleton. Sys is chosen by finrank, and state/effect/trace/support/compact are transported by the same isometry given by the standard orthonormal basis.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 3.
-/
import Quantum.QuantumEntropy.GourResource.Definitions
import Quantum.QuantumModel.FiniteStinespringMinimax.GSLCore


namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem coordinates {A : Type u} [Qudit.{u} A] [Nontrivial A] :
    ∃ S : QuantumModel.Sys,
      S.dim = Module.finrank ℂ A ∧
      Nonempty (A ≃ₗᵢ[ℂ] QuantumModel.Space S) := by
  exact ⟨⟨Module.finrank ℂ A, Module.finrank_pos⟩, rfl,
    ⟨(stdOrthonormalBasis ℂ A).repr⟩⟩

private theorem push0_positive {A : Type u} [Qudit.{u} A]
    {B : Type} [Qudit B] (U : A ≃ₗᵢ[ℂ] B) (X : L A) :
    X.IsPositive ↔ (push0 U X).IsPositive :=
  (LinearMap.isPositive_linearIsometryEquiv_conj_iff U).symm

private theorem push0_trace {A : Type u} [Qudit.{u} A]
    {B : Type} [Qudit B] (U : A ≃ₗᵢ[ℂ] B) (X : L A) :
    Tr (push0 U X) = Tr X :=
  LinearMap.trace_conj' X U.toLinearEquiv

private theorem push0_density {A : Type u} [Qudit.{u} A]
    {B : Type} [Qudit B] (U : A ≃ₗᵢ[ℂ] B) (X : L A) :
    IsDensity X ↔ IsDensity (push0 U X) := by
  rw [IsDensity, IsDensity, push0_trace, ← push0_positive]

private theorem push0_support {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (S : QuantumModel.Sys)
    (U : A ≃ₗᵢ[ℂ] QuantumModel.Space S) (X Y : L A) :
    SandwichedRenyiRelativeEntropy.suppLE X Y ↔
      SandwichedRenyiRelativeEntropy.suppLE (push0 U X) (push0 U Y) := by
  constructor
  · intro h x hx
    have hY : Y (U.symm x) = 0 := U.injective (by simpa [push0] using hx)
    change U (X (U.symm x)) = 0
    simpa using congrArg U (h hY)
  · intro h x hx
    change Y x = 0 at hx
    have hY : (push0 U Y) (U x) = 0 := by simp [push0, hx]
    have hX : U (X x) = 0 := by simpa [push0] using h hY
    exact U.injective (by simpa using hX)

private noncomputable def stateEquiv {A : Type u} [Qudit.{u} A]
    (S : QuantumModel.Sys)
    (U : A ≃ₗᵢ[ℂ] QuantumModel.Space S) :
    State A ≃ QuantumModel.DensityMatrix S :=
  (U.toLinearEquiv.conj.toEquiv.subtypeEquiv (push0_density U)).trans
    { toFun := fun ρ =>
        ⟨ρ.1, (LinearMap.nonneg_iff_isPositive _).mpr ρ.2.1, ρ.2.2⟩
      invFun := fun ρ =>
        ⟨ρ.operator, (LinearMap.nonneg_iff_isPositive _).mp ρ.nonneg, ρ.trace_one⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem density_compact {A : Type u} [Qudit.{u} A] [Nontrivial A] :
    IsCompact {X : L A | IsDensity X} := by
  obtain ⟨S, _, ⟨U⟩⟩ := coordinates (A := A)
  let c : L A ≃ₗ[ℂ] L (QuantumModel.Space S) :=
    U.toLinearEquiv.conj
  haveI : T2Space (L A) := TopologicalSpace.t2Space_of_metrizableSpace
  haveI : T2Space (L (QuantumModel.Space S)) :=
    TopologicalSpace.t2Space_of_metrizableSpace
  let e := c.toContinuousLinearEquiv.toHomeomorph
  have hset : {X : L A | IsDensity X} =
      e ⁻¹' QuantumModel.densityOperatorSet S := by
    ext X
    change IsDensity X ↔
      0 ≤ push0 U X ∧ Tr (push0 U X) = 1
    rw [LinearMap.nonneg_iff_isPositive]
    exact push0_density U X
  rw [hset, e.isCompact_preimage]
  exact QuantumModel.densityOperatorSet_isCompact S

private theorem effect_compact {A : Type u} [Qudit.{u} A] :
    IsCompact {M : L A | effect M} := by
  letI : ProperSpace (L A) := FiniteDimensional.proper ℂ (L A)
  have hset : {M : L A | effect M} = Set.Icc 0 1 := by
    ext M
    simp only [Set.mem_setOf_eq, effect, Set.mem_Icc,
      ← LinearMap.nonneg_iff_isPositive, sub_nonneg]
  rw [hset]
  apply Metric.isCompact_of_isClosed_isBounded isClosed_Icc
  apply Bornology.IsBounded.subset
    (Metric.isBounded_closedBall : Bornology.IsBounded (Metric.closedBall (0 : L A) 1))
  intro M hM
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg M hM.1).mpr hM.2

/-- Correspondence with the finite-dimensional model (a foundation without a theorem number
in the sources): a linear isometric isomorphism from `A` to the model space of the same
dimension gives a bijection of states and preserves density, positivity, trace and support
inclusion; the sets of density operators and of effect operators are compact. -/
theorem gsl_b01 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A], ∃ S : QuantumModel.Sys,
  S.dim = Module.finrank ℂ A ∧ Nonempty (A ≃ₗᵢ[ℂ] QuantumModel.Space S)) ∧
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (S : QuantumModel.Sys) (U : A
  ≃ₗᵢ[ℂ] QuantumModel.Space S),
  (∃ e : State.{u} A ≃ QuantumModel.DensityMatrix S, ∀ ρ : State.{u} A, (e
    ρ).operator = push0.{u} U ρ.1) ∧
  (∀ X Y : L.{u} A, (IsDensity X ↔ IsDensity (push0.{u} U X)) ∧
    (X.IsPositive ↔ (push0.{u} U X).IsPositive) ∧
    Tr (push0.{u} U X) = Tr X ∧
    (SandwichedRenyiRelativeEntropy.suppLE X Y ↔
      SandwichedRenyiRelativeEntropy.suppLE (push0.{u} U X) (push0.{u} U Y)))) ∧
((∀ {A : Type u} [Qudit.{u} A] [Nontrivial A], IsCompact {X : L.{u} A | IsDensity.{u} X} ∧
  IsCompact {M : L.{u} A | effect.{u} M}))
:= by
  refine ⟨?_, ?_, ?_⟩
  · intro A _ _
    exact coordinates
  · intro A _ _ S U
    refine ⟨⟨stateEquiv S U, fun _ => rfl⟩, ?_⟩
    intro X Y
    exact ⟨push0_density U X, push0_positive U X, push0_trace U X,
      push0_support S U X Y⟩
  · intro A _ _
    exact ⟨density_compact, effect_compact⟩

end GourResource

