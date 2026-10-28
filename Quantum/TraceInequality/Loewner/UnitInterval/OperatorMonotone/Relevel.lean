import Quantum.TraceInequality.Loewner.LoewnerTheorem
import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.CStarMatrixBridge

/-!
# Universe transport for normalized operator monotonicity

This module transports `OperatorMonotoneOnUnitInterval` between universe levels.
The missing `ULift` instances are deliberately private and local to the transport
implementation.
-/

namespace Quantum.TraceInequality.Loewner

universe u v

noncomputable section

namespace UnitIntervalRelevel

variable {A : Type} [NonUnitalCStarAlgebra A]

private local instance instStarULift_quantum : Star (ULift.{u} A) :=
  ⟨fun a => ⟨star a.down⟩⟩

@[simp] private lemma down_star (a : ULift.{u} A) : (star a).down = star a.down :=
  rfl

private local instance instInvolutiveStarULift_quantum : InvolutiveStar (ULift.{u} A) where
  star_involutive a := ULift.down_injective (star_star a.down)

private local instance instStarMulULift_quantum : StarMul (ULift.{u} A) where
  star_mul a b := ULift.down_injective (star_mul a.down b.down)

private local instance instStarRingULift_quantum : StarRing (ULift.{u} A) where
  star_add a b := ULift.down_injective (star_add a.down b.down)

private local instance instStarModuleComplexULift_quantum : StarModule ℂ (ULift.{u} A) where
  star_smul c a := ULift.down_injective (star_smul c a.down)

private local instance instSMulCommClassComplexULift_quantum :
    SMulCommClass ℂ (ULift.{u} A) (ULift.{u} A) where
  smul_comm c a b := ULift.down_injective (smul_comm c a.down b.down)

private local instance instCStarRingULift_quantum : CStarRing (ULift.{u} A) where
  norm_mul_self_le a := CStarRing.norm_mul_self_le a.down

private local instance instNonUnitalCStarAlgebraULift_quantum :
    NonUnitalCStarAlgebra (ULift.{u} A) where

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private local instance instStarOrderedRingULift_quantum : StarOrderedRing (ULift.{u} A) := by
  refine ⟨fun x y => ?_⟩
  have h := StarOrderedRing.le_iff x.down y.down
  constructor
  · intro hxy
    obtain ⟨p, hp, hpy⟩ := h.mp hxy
    refine ⟨ULift.up p, ?_, ULift.down_injective hpy⟩
    clear hpy
    induction hp using AddSubmonoid.closure_induction with
    | mem t ht =>
      obtain ⟨s, rfl⟩ := ht
      exact AddSubmonoid.subset_closure ⟨ULift.up s, rfl⟩
    | zero => exact (AddSubmonoid.closure _).zero_mem
    | add p q hp hq ihp ihq => exact AddSubmonoid.add_mem _ ihp ihq
  · rintro ⟨q, hq, hqy⟩
    have hmem : q.down ∈ AddSubmonoid.closure (Set.range fun s : A => star s * s) := by
      clear hqy h
      induction hq using AddSubmonoid.closure_induction with
      | mem t ht =>
        obtain ⟨s, rfl⟩ := ht
        exact AddSubmonoid.subset_closure ⟨s.down, rfl⟩
      | zero => exact (AddSubmonoid.closure _).zero_mem
      | add p q hp hq ihp ihq => exact AddSubmonoid.add_mem _ ihp ihq
    exact h.mpr ⟨q.down, hmem, congrArg ULift.down hqy⟩

variable {A : Type} [NonUnitalCStarAlgebra A]

private def upHom : A →⋆ₙₐ[ℂ] ULift.{u} A where
  toFun := ULift.up
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

private def downHom : ULift.{u} A →⋆ₙₐ[ℂ] A where
  toFun := ULift.down
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

private lemma isometry_up : Isometry (ULift.up : A → ULift.{u} A) :=
  Isometry.of_dist_eq fun _ _ => rfl

private lemma isometry_down : Isometry (ULift.down : ULift.{u} A → A) :=
  Isometry.of_dist_eq fun _ _ => rfl

private lemma continuous_upHom : Continuous (upHom : A →⋆ₙₐ[ℂ] ULift.{u} A) :=
  isometry_up.continuous

private lemma quasispectrum_up (a : A) :
    quasispectrum ℝ (ULift.up.{u} a) = quasispectrum ℝ a := by
  apply Set.Subset.antisymm
  · exact NonUnitalAlgHom.quasispectrum_apply_subset' ℂ
      (upHom : A →⋆ₙₐ[ℂ] ULift.{u} A) a
  · exact NonUnitalAlgHom.quasispectrum_apply_subset' ℂ
      (downHom : ULift.{u} A →⋆ₙₐ[ℂ] A) (ULift.up a)

private lemma isSelfAdjoint_up_iff {a : A} :
    IsSelfAdjoint (ULift.up.{u} a) ↔ IsSelfAdjoint a := by
  constructor
  · intro h
    exact ULift.up_injective h
  · intro h
    exact congrArg ULift.up h

private lemma cfcₙ_up (g : ℝ → ℝ) (hg0 : g 0 = 0) (a : A) :
    cfcₙ g (ULift.up.{u} a) = ULift.up (cfcₙ g a) := by
  by_cases ha : IsSelfAdjoint a
  · by_cases hg : ContinuousOn g (quasispectrum ℝ a)
    · exact (NonUnitalStarAlgHom.map_cfcₙ (upHom : A →⋆ₙₐ[ℂ] ULift.{u} A) g a hg hg0
        continuous_upHom ha (isSelfAdjoint_up_iff.mpr ha)).symm
    · rw [cfcₙ_apply_of_not_continuousOn (ULift.up.{u} a)
          (by rwa [quasispectrum_up]),
        cfcₙ_apply_of_not_continuousOn a hg]
      rfl
  · rw [cfcₙ_apply_of_not_predicate (ULift.up.{u} a)
        (fun h => ha (isSelfAdjoint_up_iff.mp h)),
      cfcₙ_apply_of_not_predicate a ha]
    rfl

theorem _root_.Quantum.TraceInequality.Loewner.operatorMonotoneOnUnitInterval_toZero
    {f : ℝ → ℝ}
    (h : OperatorMonotoneOnUnitInterval.{u} f) :
    OperatorMonotoneOnUnitInterval.{0} f := by
  constructor
  intro A _ _ _ a ha b hb hab
  have hg0 : (fun x : ℝ => f x - f 0) 0 = 0 := by simp
  have key : cfcₙ (fun x : ℝ => f x - f 0) (ULift.up.{u} a) ≤
      cfcₙ (fun x : ℝ => f x - f 0) (ULift.up.{u} b) :=
    h.cfc_monotone (A := ULift.{u} A)
      ⟨isSelfAdjoint_up_iff.mpr ha.1, by rw [quasispectrum_up]; exact ha.2⟩
      ⟨isSelfAdjoint_up_iff.mpr hb.1, by rw [quasispectrum_up]; exact hb.2⟩
      (ULift.up_le.mpr hab)
  have key' : ULift.up.{u} (cfcₙ (fun x : ℝ => f x - f 0) a) ≤
      ULift.up.{u} (cfcₙ (fun x : ℝ => f x - f 0) b) := by
    rw [← cfcₙ_up _ hg0 a, ← cfcₙ_up _ hg0 b]
    exact key
  exact key'

theorem _root_.Quantum.TraceInequality.Loewner.operatorMonotoneOnUnitInterval_zeroTo
    {f : ℝ → ℝ}
    (h : OperatorMonotoneOnUnitInterval.{0} f) :
    OperatorMonotoneOnUnitInterval.{u} f :=
  operatorMonotoneOnUnitInterval_of_finiteMatrixMonotone
    (unitIntervalMatrixMonotone_of_finiteMatrixMonotone
      (finiteMatrixMonotone_of_operatorMonotoneOnUnitInterval h))

theorem _root_.Quantum.TraceInequality.Loewner.operatorMonotoneOnUnitInterval_relevel
    {f : ℝ → ℝ}
    (h : OperatorMonotoneOnUnitInterval.{u} f) :
    OperatorMonotoneOnUnitInterval.{v} f :=
  operatorMonotoneOnUnitInterval_zeroTo
    (operatorMonotoneOnUnitInterval_toZero h)

end UnitIntervalRelevel

end

end Quantum.TraceInequality.Loewner
