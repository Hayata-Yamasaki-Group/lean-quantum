/-
Pinching as a mixture of k unitaries.
-/
import Quantum.QuantumEntropy.GourResource.Definitions
import Quantum.OperationalProbabilistic.OperationalFidelity.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesDecouplingNorm.GSLCoreRetained
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesMinDefinitions.GSLCore

open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower ℝ ℂ (L H) :=
  RestrictScalars.isScalarTower ℝ ℂ (L H)

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem c32_diagonal_star {A : Type u} [Qudit A]
    (S : L A) (c : spectralEigenvalue S → ℂ) :
    star (∑ μ, c μ • spectralProjector S μ) =
      ∑ μ, star (c μ) • spectralProjector S μ := by
  classical
  simp only [star_sum, star_smul]
  apply Finset.sum_congr rfl
  intro μ _
  congr 1
  exact (spectralProjector_isSymmetric S μ).adjoint_eq

private theorem c32_diagonal_unitary {A : Type u} [Qudit A]
    (S : L A) (hS : S.IsSymmetric) (c : spectralEigenvalue S → ℂ)
    (hc : ∀ μ, star (c μ) * c μ = 1) :
    star (∑ μ, c μ • spectralProjector S μ) *
        (∑ μ, c μ • spectralProjector S μ) = 1 ∧
      (∑ μ, c μ • spectralProjector S μ) *
        star (∑ μ, c μ • spectralProjector S μ) = 1 := by
  classical
  rw [c32_diagonal_star]
  constructor
  · rw [spectralProjector_weighted_sum_mul S hS]
    simp only [hc, one_smul]
    exact spectralProjector_sum_eq_one S hS
  · rw [spectralProjector_weighted_sum_mul S hS]
    simp only [mul_comm (c _), hc, one_smul]
    exact spectralProjector_sum_eq_one S hS

private theorem c32_diagonal_conjugation {A : Type u} [Qudit A]
    (S X : L A) (c : spectralEigenvalue S → ℂ) :
    (∑ μ, c μ • spectralProjector S μ) * X *
        star (∑ μ, c μ • spectralProjector S μ) =
      ∑ μ, ∑ ν, (c μ * star (c ν)) •
        (spectralProjector S μ * X * spectralProjector S ν) := by
  classical
  rw [c32_diagonal_star, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro μ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm]

private theorem c32_phase_product {n : ℕ} [NeZero n] (a b j : ZMod n) :
    ZMod.stdAddChar (j * a) * star (ZMod.stdAddChar (j * b)) =
      ZMod.stdAddChar (j * (a - b)) := by
  rw [show star (ZMod.stdAddChar (j * b)) = ZMod.stdAddChar (-(j * b)) from
    (AddChar.map_neg_eq_conj _ _).symm]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

private theorem c32_phase_sum {n : ℕ} [NeZero n] (a b : ZMod n) :
    (∑ j : ZMod n, ZMod.stdAddChar (j * a) * star (ZMod.stdAddChar (j * b))) =
      if a = b then (n : ℂ) else 0 := by
  simp_rw [c32_phase_product]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar n)]
  simp only [sub_eq_zero, ZMod.card]
  split_ifs <;> simp only [Nat.cast_zero]

private theorem c32_phase_unit {n : ℕ} [NeZero n] (a j : ZMod n) :
    star (ZMod.stdAddChar (j * a)) * ZMod.stdAddChar (j * a) = 1 := by
  rw [mul_comm, c32_phase_product]
  simp only [sub_self, mul_zero, AddChar.map_zero_eq_one]

private theorem c32_mixture_sum {A : Type u} [Qudit A]
    (S X : L A) {n : ℕ} [NeZero n]
    (e : spectralEigenvalue S → ZMod n) (he : Function.Injective e) :
    (n : ℂ) • spectralPinchingLinearMap S X =
      ∑ j : ZMod n,
        (∑ μ, ZMod.stdAddChar (j * e μ) • spectralProjector S μ) * X *
          star (∑ μ, ZMod.stdAddChar (j * e μ) • spectralProjector S μ) := by
  classical
  rw [spectralPinchingLinearMap_apply]
  simp_rw [c32_diagonal_conjugation]
  rw [Finset.smul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro μ _
  rw [Finset.sum_comm, Finset.sum_eq_single μ]
  · rw [← Finset.sum_smul, c32_phase_sum]
    simp only [ite_true]
  · intro ν _ hνμ
    rw [← Finset.sum_smul, c32_phase_sum, if_neg (he.ne hνμ.symm), zero_smul]
  · intro hμ
    exact (hμ (Finset.mem_univ μ)).elim

private theorem c32_card_ne_zero {A : Type u} [Qudit A] [Nontrivial A]
    (σ : State A) : Fintype.card (spectralEigenvalue σ.1) ≠ 0 := by
  intro h
  haveI : IsEmpty (spectralEigenvalue σ.1) := Fintype.card_eq_zero_iff.mp h
  have hs := spectralProjector_sum_eq_one σ.1 σ.2.1.isSymmetric
  simp at hs

theorem gsl_c32 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (σ : State.{u} A),
  ∃ U : Fin (Fintype.card (spectralEigenvalue.{u} σ.1)) → L.{u} A,
  (∀ j, star (U j)*U j=1 ∧ U j*star (U j)=1) ∧
  ∀ X : L.{u} A, pin.{u} σ.1 X =
    (1 / (Fintype.card (spectralEigenvalue.{u} σ.1) : ℝ)) • ∑ j, U j * X * star (U j))
:= by
  classical
  intro A _ _ σ
  let n := Fintype.card (spectralEigenvalue σ.1)
  haveI : NeZero n := ⟨c32_card_ne_zero σ⟩
  let e : spectralEigenvalue σ.1 ≃ ZMod n :=
    (Fintype.equivFin _).trans (ZMod.finEquiv n).toEquiv
  let V : ZMod n → L A := fun j =>
    ∑ μ, ZMod.stdAddChar (j * e μ) • spectralProjector σ.1 μ
  refine ⟨fun j => V (ZMod.finEquiv n j), ?_, ?_⟩
  · intro j
    exact c32_diagonal_unitary σ.1 σ.2.1.isSymmetric _
      (fun μ => c32_phase_unit (e μ) (ZMod.finEquiv n j))
  · intro X
    have hsum : (n : ℂ) • pin σ.1 X = ∑ j : ZMod n, V j * X * star (V j) :=
      c32_mixture_sum σ.1 X e e.injective
    have hfin : (∑ j : Fin n, V (ZMod.finEquiv n j) * X *
        star (V (ZMod.finEquiv n j))) = ∑ j : ZMod n, V j * X * star (V j) :=
      Fintype.sum_equiv (ZMod.finEquiv n).toEquiv _ _ (fun _ => rfl)
    change pin σ.1 X = (1 / (n : ℝ)) • _
    rw [hfin, ← hsum]
    have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    simp only [one_div, RCLike.ofReal_inv, RCLike.ofReal_natCast,
      inv_mul_cancel₀ hn, one_smul]

end GourResource

