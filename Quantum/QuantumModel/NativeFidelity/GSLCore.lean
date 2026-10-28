/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Quantum.QuantumModel.NativeTraceDistance.GSLCore
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.ENNReal.Inv
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Native quantum fidelity

The operator root fidelity of density matrices, finite POVMs with their Born distributions,
the classical root fidelity and root overlap, the measured POVM root fidelity, and channel
application to density matrices.
-/

noncomputable section

namespace QuantumModel
namespace NativeFidelity

open CategoryTheory
open QuantumState
open scoped ENNReal MonoidalCategory

/-- The positive square root of a density operator is nonnegative. -/
theorem densitySqrt_nonneg {A : Sys} (rho : DensityMatrix A) :
    0 ≤ CFC.sqrt rho.operator :=
  CFC.sqrt_nonneg rho.operator

/-- The positive square root squares to the density operator. -/
theorem densitySqrt_comp_self {A : Sys} (rho : DensityMatrix A) :
    (CFC.sqrt rho.operator).comp (CFC.sqrt rho.operator) = rho.operator :=
  CFC.sqrt_mul_sqrt_self rho.operator rho.nonneg

/-- A finite indexed POVM.  Outcome upper bounds follow from nonnegativity
and `sum_eq_id`, so they are not stored redundantly. -/
structure POVM (A : Sys) where
  ι : Type
  [fintype_ι : Fintype ι]
  effect : ι → Operator A
  nonneg : ∀ i, 0 ≤ effect i
  sum_eq_id : Finset.univ.sum effect = LinearMap.id

attribute [instance] POVM.fintype_ι

namespace POVM

/-- The one-outcome identity POVM. -/
def trivial (A : Sys) : POVM A where
  ι := PUnit
  effect := fun _ => LinearMap.id
  nonneg := fun _ =>
    (LinearMap.nonneg_iff_isPositive LinearMap.id).mpr LinearMap.isPositive_id
  sum_eq_id := by simp

private theorem re_trace_comp_nonneg {A : Sys} (P Q : Operator A)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    0 ≤ (Tr (P.comp Q)).re := by
  let S : Operator A := CFC.sqrt P
  have hSadj : LinearMap.adjoint S = S := by
    rw [← LinearMap.star_eq_adjoint]
    exact (CFC.sqrt_nonneg P).isSelfAdjoint
  have hSsq : S.comp S = P := CFC.sqrt_mul_sqrt_self P hP
  have hQpos : Q.IsPositive :=
    (LinearMap.nonneg_iff_isPositive Q).mp hQ
  have hconj :
      ((LinearMap.adjoint S).comp (Q.comp S)).IsPositive :=
    hQpos.adjoint_conj S
  have htrace :
      Tr (P.comp Q) =
        Tr ((LinearMap.adjoint S).comp (Q.comp S)) := by
    calc
      Tr (P.comp Q) = Tr (Q.comp P) :=
        (LinearMap.trace_comp_comm' P Q).symm
      _ = Tr (Q.comp (S.comp S)) := by rw [hSsq]
      _ = Tr ((Q.comp S).comp S) := by rw [LinearMap.comp_assoc]
      _ = Tr (S.comp (Q.comp S)) :=
        LinearMap.trace_comp_comm' S (Q.comp S)
      _ = Tr ((LinearMap.adjoint S).comp (Q.comp S)) := by rw [hSadj]
  rw [htrace]
  exact (Complex.nonneg_iff.mp hconj.trace_nonneg).1

/-- Every POVM outcome has a nonnegative Born probability. -/
theorem bornProbability_nonneg {A : Sys} (M : POVM A)
    (rho : DensityMatrix A) (i : M.ι) :
    0 ≤ NativeNoCloning.bornProbability (M.effect i) rho := by
  exact re_trace_comp_nonneg (M.effect i) rho.operator
    (M.nonneg i) rho.nonneg

/-- Born probabilities of a finite POVM sum to one. -/
theorem bornProbability_sum_eq_one {A : Sys} (M : POVM A)
    (rho : DensityMatrix A) :
    Finset.univ.sum
        (fun i => NativeNoCloning.bornProbability (M.effect i) rho) = 1 := by
  have hcomp :
      (Finset.univ.sum M.effect).comp rho.operator =
        Finset.univ.sum (fun i => (M.effect i).comp rho.operator) := by
    apply LinearMap.ext
    intro x
    simp
  change Finset.univ.sum
      (fun i => (Tr ((M.effect i).comp rho.operator)).re) = 1
  have htrace :
      Tr ((Finset.univ.sum M.effect).comp rho.operator) =
        Finset.univ.sum (fun i => Tr ((M.effect i).comp rho.operator)) := by
    rw [hcomp, map_sum]
  have hre :
      (Tr ((Finset.univ.sum M.effect).comp rho.operator)).re =
        Finset.univ.sum
          (fun i => (Tr ((M.effect i).comp rho.operator)).re) := by
    rw [htrace]
    change Complex.reCLM
        (Finset.univ.sum (fun i => Tr ((M.effect i).comp rho.operator))) =
      Finset.univ.sum
        (fun i => Complex.reCLM (Tr ((M.effect i).comp rho.operator)))
    exact map_sum Complex.reCLM _ _
  rw [← hre, M.sum_eq_id, LinearMap.id_comp, rho.trace_one]
  rfl

/-- Born probability mass function of a finite POVM. -/
noncomputable def bornPMF {A : Sys} (M : POVM A)
    (rho : DensityMatrix A) : PMF M.ι :=
  PMF.ofFintype
    (fun i => ENNReal.ofReal
      (NativeNoCloning.bornProbability (M.effect i) rho))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · rw [M.bornProbability_sum_eq_one rho]
        exact ENNReal.ofReal_one
      · intro i _hi
        exact M.bornProbability_nonneg rho i)

@[simp]
theorem bornPMF_apply {A : Sys} (M : POVM A)
    (rho : DensityMatrix A) (i : M.ι) :
    M.bornPMF rho i = ENNReal.ofReal
      (NativeNoCloning.bornProbability (M.effect i) rho) :=
  rfl

end POVM

/-- Classical root overlap (Bhattacharyya coefficient) of two finite PMFs. -/
noncomputable def classicalRootFidelity {ι : Type} [Fintype ι]
    (p q : PMF ι) : ℝ≥0∞ :=
  Finset.univ.sum (fun i => (p i * q i).rpow (1 / 2 : ℝ))

/-- Classical root overlap produced by one finite POVM. -/
noncomputable def POVM.rootOverlap {A : Sys} (M : POVM A)
    (rho sigma : DensityMatrix A) : ℝ≥0∞ :=
  classicalRootFidelity (M.bornPMF rho) (M.bornPMF sigma)

/-- Root fidelity obtained by minimizing over finite native POVMs. -/
noncomputable def measuredPOVMRootFidelityENNReal {A : Sys}
    (rho sigma : DensityMatrix A) : ℝ≥0∞ :=
  ⨅ M : POVM A, M.rootOverlap rho sigma

/-! ## Channel application -/

/-- Native CPTP channel action used by the fidelity facade. -/
def channelApply {A B : Sys} (rho : DensityMatrix A)
    (Phi : NativeNoCloning.Superoperator A B) (hPhi : IsCPTP Phi) :
    DensityMatrix B :=
  rho.channelApply Phi ((isChannel_iff_isCPTP Phi).mpr hPhi)

@[simp]
theorem channelApply_operator {A B : Sys} (rho : DensityMatrix A)
    (Phi : NativeNoCloning.Superoperator A B) (hPhi : IsCPTP Phi) :
    (channelApply rho Phi hPhi).operator = Phi rho.operator := by
  exact DensityMatrix.channelApply_operator rho Phi
    ((isChannel_iff_isCPTP Phi).mpr hPhi)

end NativeFidelity
end QuantumModel
