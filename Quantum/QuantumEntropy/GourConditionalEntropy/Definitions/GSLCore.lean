import Quantum.QuantumEntropy.GourSemiCausalMemory.GSLCore
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Analysis.Convex.Jensen

open QuantumState QuantumChannel GourChoi GourSemiCausal CategoryTheory
open scoped TensorProduct ComplexOrder BigOperators MonoidalCategory

universe u

/-! Defines the tensor product `productDensity` of density operators and the image `isometryDensity`
under an isometry (used in the definition of conditional entropy in Gour §7.2). -/

namespace GourConditionalEntropy

noncomputable def productDensity
    {A B : Type u} [Qudit A] [Qudit B]
    (ρ : {X : L A // IsDensity X}) (σ : {X : L B // IsDensity X}) :
    {X : L (A ⊗[ℂ] B) // IsDensity X} :=
  ⟨TensorProduct.map ρ.1 σ.1, by
    refine ⟨?_, by rw [(tensor_trace ρ.1 σ.1).2.2, ρ.2.2, σ.2.2, one_mul]⟩
    apply (LinearMap.nonneg_iff_isPositive _).mp
    have hx := (LinearMap.nonneg_iff_isPositive _).mpr ρ.2.1
    have hy := (LinearMap.nonneg_iff_isPositive _).mpr σ.2.1
    have hs : star (TensorProduct.map (CFC.sqrt ρ.1) (CFC.sqrt σ.1)) =
        TensorProduct.map (star (CFC.sqrt ρ.1)) (star (CFC.sqrt σ.1)) := by
      simp only [LinearMap.star_eq_adjoint, TensorProduct.adjoint_map]
    rw [show TensorProduct.map ρ.1 σ.1 =
        star (TensorProduct.map (CFC.sqrt ρ.1) (CFC.sqrt σ.1)) *
          TensorProduct.map (CFC.sqrt ρ.1) (CFC.sqrt σ.1) by
      rw [hs, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg ρ.1)).star_eq,
        (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg σ.1)).star_eq,
        ← TensorProduct.map_mul, CFC.sqrt_mul_sqrt_self ρ.1 hx,
        CFC.sqrt_mul_sqrt_self σ.1 hy]]
    exact star_mul_self_nonneg _⟩

noncomputable def isometryDensity
    {A A' : Type u} [Qudit A] [Qudit A'] (V : A →ₗᵢ[ℂ] A')
    (ρ : {X : L A // IsDensity X}) : {X : L A' // IsDensity X} :=
  ⟨krausTerm V.toLinearMap ρ.1, by
    obtain ⟨N, hN⟩ := gourMemory_isometry_channel V
    rw [← hN]
    refine ⟨?_, (N.trace_map ρ.1).symm.trans ρ.2.2⟩
    apply (LinearMap.nonneg_iff_isPositive _).mp
    exact completelyPositive_to_positiveMap N.toLinearMap
      ⟨N.toCompletelyPositiveMap, rfl⟩ ρ.1
      ((LinearMap.nonneg_iff_isPositive _).mpr ρ.2.1)⟩

end GourConditionalEntropy
