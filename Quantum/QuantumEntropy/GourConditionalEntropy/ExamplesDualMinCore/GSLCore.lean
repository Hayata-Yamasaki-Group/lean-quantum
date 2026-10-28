import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesMinDefinitions.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.Definitions.GSLCore
import Quantum.QuantumEntropy.GourSemiCausalMemory.GSLCore
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Fin.Tuple.Sort
import Quantum.OperationalProbabilistic.Decomposition.ConditionedStates.GSLCore
import Quantum.OperationalProbabilistic.Framework.ExactCompression.GSLCore
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Intrinsic
import Quantum.OperationalProbabilistic.Framework.NormalizedEffects.GSLCore
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Quantum.OperationalProbabilistic.DistinguishableStates.Core.GSLCore
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
import Quantum.QuantumEntropy.GourQuantumMaxRelativeEntropy.GSLCore
import Quantum.QuantumMechanics.DiagonalDensity.GSLCore
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Analysis.Convex.Function
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivDPI.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalFDivConcrete.GSLCore
import Quantum.OperationalProbabilistic.Framework.MeasuredLift.GSLCore
import Quantum.QuantumMechanics.SpectralPinching.GSLCore
import Quantum.QuantumEntropy.GourQuantumRelativeEntropyBasicProperties.GSLCore
import Quantum.OperationalProbabilistic.Framework.QuantumRelativeEntropyLaws.GSLCore
import Quantum.OperationalProbabilistic.Framework.QuantumRelativeEntropyLaws.GSLCoreRetained
import Mathlib.Topology.Order.AtTopBotIxx
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiOrder.GSLCore
import Quantum.OperationalProbabilistic.Framework.MeasurementEntropy.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiDivergence.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiRelativeEntropyLimits.GSLCore
import Quantum.OperationalProbabilistic.Framework.ClassicalRenyiPowerFDivBridge.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.FromRelativePreparation.GSLCore
import Quantum.QuantumMechanics.Channel.BasicGeneralizedStein
import Quantum.QuantumMechanics.Channel.ChoiKraus

namespace GourConditionalEntropy

section

open QuantumState QuantumChannel GourChoi GourConditionalEntropy
open scoped TensorProduct ComplexOrder BigOperators ENNReal
universe u

set_option autoImplicit false

private theorem w39c18_isometry_exists
    {H E : Type u} [Qudit H] [Qudit E]
    (hdim : Module.finrank ℂ H ≤ Module.finrank ℂ E) :
    Nonempty (H →ₗᵢ[ℂ] E) := by
  classical
  let a := stdOrthonormalBasis ℂ H
  let b := stdOrthonormalBasis ℂ E
  let f := a.toBasis.constr ℂ (fun i => b (Fin.castLE hdim i))
  refine ⟨f.isometryOfOrthonormal (v := a.toBasis) a.orthonormal ?_⟩
  have hf : f ∘ a.toBasis = b ∘ Fin.castLE hdim := by
    funext i
    simp [f]
  rw [hf]
  exact b.orthonormal.comp _ (Fin.castLE_injective hdim)

private theorem w39c18_equal_gram
    {H E : Type u} [Qudit H] [Qudit E] (A B : H →ₗ[ℂ] E)
    (hgram : ∀ x y, inner ℂ (A x) (A y) = inner ℂ (B x) (B y)) :
    ∃ U : E →ₗᵢ[ℂ] E, U.toLinearMap.comp A = B := by
  classical
  have hker : A.ker ≤ B.ker := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [← hgram x x, LinearMap.mem_ker.mp hx, inner_zero_left]
  let f : A.range →ₗ[ℂ] E :=
    (A.ker.liftQ B hker).comp A.quotKerEquivRange.symm.toLinearMap
  have hf : ∀ x (hx : A x ∈ A.range), f ⟨A x, hx⟩ = B x := by
    intro x hx
    simp [f]
  have hinner : ∀ x y : A.range, inner ℂ (f x) (f y) = inner ℂ x y := by
    rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
    simpa only [hf, Submodule.coe_inner] using (hgram x y).symm
  let W := f.isometryOfInner hinner
  refine ⟨W.extend, ?_⟩
  ext x
  change W.extend (A x) = B x
  rw [W.extend_apply ⟨A x, LinearMap.mem_range_self A x⟩]
  exact hf x _

private theorem w39c18_iso_adjoint
    {H E : Type u} [Qudit H] [Qudit E] (J : H →ₗᵢ[ℂ] E) :
    J.toLinearMap.adjoint.comp J.toLinearMap = LinearMap.id := by
  ext x
  apply ext_inner_left ℂ
  intro y
  simpa only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.adjoint_inner_right]
    using J.inner_map_map y x

private theorem w39c18_sqrt_adjoint
    {H : Type u} [Qudit H] (X : L H) :
    (CFC.sqrt X).adjoint = CFC.sqrt X :=
  ((LinearMap.nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg X)).isSymmetric.adjoint_eq

private theorem w39c18_polar
    {H : Type u} [Qudit H] (A : L H) :
    ∃ U : H →ₗᵢ[ℂ] H,
      U.toLinearMap * CFC.sqrt (A.adjoint * A) = A := by
  apply w39c18_equal_gram
  intro x y
  rw [← LinearMap.adjoint_inner_right, w39c18_sqrt_adjoint]
  change inner ℂ x ((CFC.sqrt (A.adjoint * A) * CFC.sqrt (A.adjoint * A)) y) = _
  have hA : 0 ≤ A.adjoint * A :=
    (LinearMap.nonneg_iff_isPositive _).mpr (LinearMap.isPositive_adjoint_comp_self A)
  rw [CFC.sqrt_mul_sqrt_self (A.adjoint * A) hA]
  exact LinearMap.adjoint_inner_right A x (A y)

private theorem w39c18_positive_trace_bound
    {H : Type u} [Qudit H] (P : L H) (hP : P.IsPositive)
    (U : H →ₗᵢ[ℂ] H) : ‖Tr (U.toLinearMap * P)‖ ≤ (Tr P).re := by
  classical
  let b := hP.isSymmetric.eigenvectorBasis rfl
  change ‖(LinearMap.trace ℂ H) (U.toLinearMap * P)‖ ≤
    RCLike.re ((LinearMap.trace ℂ H) P)
  rw [LinearMap.trace_eq_sum_inner _ b,
    hP.isSymmetric.re_trace_eq_sum_eigenvalues rfl]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hi : 0 ≤ hP.isSymmetric.eigenvalues rfl i :=
    hP.nonneg_eigenvalues rfl i
  change ‖inner ℂ (b i) (U (P (b i)))‖ ≤ _
  rw [hP.isSymmetric.apply_eigenvectorBasis, map_smul, inner_smul_right, norm_mul]
  change ‖(hP.isSymmetric.eigenvalues rfl i : ℂ)‖ *
    ‖inner ℂ (b i) (U (b i))‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hi]
  have hb : ‖inner ℂ (b i) (U (b i))‖ ≤ 1 := by
    simpa only [U.norm_map, b.norm_eq_one, mul_one] using
      norm_inner_le_norm (b i) (U (b i))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hb hi

private noncomputable def w39c18_push
    {H E : Type u} [Qudit H] [Qudit E] (J : H →ₗᵢ[ℂ] E) (X : L H) : L E :=
  (J.toLinearMap.comp X).comp J.toLinearMap.adjoint

private theorem w39c18_push_mul
    {H E : Type u} [Qudit H] [Qudit E] (J : H →ₗᵢ[ℂ] E) (X Y : L H) :
    w39c18_push J (X * Y) = w39c18_push J X * w39c18_push J Y := by
  change (J.toLinearMap.comp (X.comp Y)).comp J.toLinearMap.adjoint =
    ((J.toLinearMap.comp X).comp J.toLinearMap.adjoint).comp
      ((J.toLinearMap.comp Y).comp J.toLinearMap.adjoint)
  simp only [LinearMap.comp_assoc]
  rw [← LinearMap.comp_assoc _ J.toLinearMap J.toLinearMap.adjoint,
    w39c18_iso_adjoint, LinearMap.id_comp]

private theorem w39c18_push_positive
    {H E : Type u} [Qudit H] [Qudit E] (J : H →ₗᵢ[ℂ] E)
    (X : L H) (hX : X.IsPositive) : (w39c18_push J X).IsPositive :=
  hX.conj_adjoint J.toLinearMap

private theorem w39c18_push_sqrt
    {H E : Type u} [Qudit H] [Qudit E] (J : H →ₗᵢ[ℂ] E)
    (X : L H) (hX : X.IsPositive) :
    CFC.sqrt (w39c18_push J X) = w39c18_push J (CFC.sqrt X) := by
  apply CFC.sqrt_unique
  · rw [← w39c18_push_mul, CFC.sqrt_mul_sqrt_self X
      ((LinearMap.nonneg_iff_isPositive _).mpr hX)]
  · exact (LinearMap.nonneg_iff_isPositive _).mpr (w39c18_push_positive J _
      ((LinearMap.nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg X)))

private theorem w39c18_push_trace
    {H E : Type u} [Qudit H] [Qudit E] (J : H →ₗᵢ[ℂ] E) (X : L H) :
    Tr (w39c18_push J X) = Tr X := by
  rw [w39c18_push, LinearMap.trace_comp_comm', ← LinearMap.comp_assoc,
    w39c18_iso_adjoint, LinearMap.id_comp]

private theorem w39c18_push_fidelity
    {H E : Type u} [Qudit H] [Qudit E] (J : H →ₗᵢ[ℂ] E)
    (X Y : L H) (hX : X.IsPositive) (hY : Y.IsPositive) :
    rootFidelity (w39c18_push J X) (w39c18_push J Y) = rootFidelity X Y := by
  have hM : (CFC.sqrt X * Y * CFC.sqrt X).IsPositive := by
    simpa only [w39c18_sqrt_adjoint] using hY.conj_adjoint (CFC.sqrt X)
  rw [rootFidelity, w39c18_push_sqrt J X hX, ← w39c18_push_mul, ← w39c18_push_mul,
    w39c18_push_sqrt J _ hM, w39c18_push_trace]
  rfl

private theorem w39c18_trace_sqrt_swap
    {H : Type u} [Qudit H] (A : L H) :
    Tr (CFC.sqrt (A * A.adjoint)) = Tr (CFC.sqrt (A.adjoint * A)) := by
  obtain ⟨U, hU⟩ := w39c18_polar A
  have heq : A * A.adjoint = w39c18_push U (A.adjoint * A) := by
    conv_lhs => rw [← hU]
    rw [show (U.toLinearMap * CFC.sqrt (A.adjoint * A)).adjoint =
        CFC.sqrt (A.adjoint * A) * U.toLinearMap.adjoint by
      change (U.toLinearMap.comp (CFC.sqrt (A.adjoint * A))).adjoint = _
      rw [LinearMap.adjoint_comp, w39c18_sqrt_adjoint]
      rfl]
    change (U.toLinearMap * CFC.sqrt (A.adjoint * A)) *
      (CFC.sqrt (A.adjoint * A) * U.toLinearMap.adjoint) =
      U.toLinearMap * (A.adjoint * A) * U.toLinearMap.adjoint
    have hA : 0 ≤ A.adjoint * A := (LinearMap.nonneg_iff_isPositive _).mpr
      (LinearMap.isPositive_adjoint_comp_self A)
    rw [mul_assoc, ← mul_assoc (CFC.sqrt (A.adjoint * A)),
      CFC.sqrt_mul_sqrt_self (A.adjoint * A) hA]
    simp only [mul_assoc]
  rw [heq, w39c18_push_sqrt U (A.adjoint * A) (LinearMap.isPositive_adjoint_comp_self A),
    w39c18_push_trace]

private theorem w39c18_trace_bound
    {H : Type u} [Qudit H] (A : L H) :
    ‖Tr A‖ ≤ (Tr (CFC.sqrt (A * A.adjoint))).re := by
  rw [w39c18_trace_sqrt_swap]
  obtain ⟨U, hU⟩ := w39c18_polar A
  simpa only [hU] using w39c18_positive_trace_bound (CFC.sqrt (A.adjoint * A))
    ((LinearMap.nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg _)) U

private theorem w39c18_push_adjoint
    {H E : Type u} [Qudit H] [Qudit E] (J : H →ₗᵢ[ℂ] E) (X : L H) :
    (w39c18_push J X).adjoint = w39c18_push J X.adjoint := by
  simp only [w39c18_push, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
    LinearMap.comp_assoc]

private theorem w39c18_square_pair
    {H : Type u} [Qudit H] (A B : L H) :
    rootFidelity (A * A.adjoint) (B * B.adjoint) =
      (Tr (CFC.sqrt ((A.adjoint * B) * (A.adjoint * B).adjoint))).re := by
  obtain ⟨U, hU⟩ := w39c18_polar A.adjoint
  simp only [LinearMap.adjoint_adjoint] at hU
  let P := CFC.sqrt (A * A.adjoint)
  have hV : P * U.toLinearMap.adjoint = A := by
    have h := congrArg LinearMap.adjoint hU
    simpa only [Module.End.mul_eq_comp, LinearMap.adjoint_comp,
      LinearMap.adjoint_adjoint, w39c18_sqrt_adjoint] using h
  have heq : (A.adjoint * B) * (A.adjoint * B).adjoint =
      w39c18_push U (P * (B * B.adjoint) * P) := by
    calc
      _ = (A.adjoint * (B * B.adjoint)) * A := by
        simp only [Module.End.mul_eq_comp, LinearMap.adjoint_comp,
          LinearMap.adjoint_adjoint, LinearMap.comp_assoc]
      _ = ((U.toLinearMap * P) * (B * B.adjoint)) *
          (P * U.toLinearMap.adjoint) :=
        congrArg₂ (fun C D : L H => (C * (B * B.adjoint)) * D) hU.symm hV.symm
      _ = _ := by change _ = U.toLinearMap * (P * (B * B.adjoint) * P) *
                              U.toLinearMap.adjoint
                  simp only [mul_assoc]
  have hM : (P * (B * B.adjoint) * P).IsPositive := by
    simpa only [P, w39c18_sqrt_adjoint] using
      (LinearMap.isPositive_self_comp_adjoint B).conj_adjoint P
  rw [heq, w39c18_push_sqrt U _ hM, w39c18_push_trace]
  rfl

/-- The case `dim H ≤ dim E` of `w39c18_rectangular_pair`: embed `H` isometrically into `E`. -/
private theorem w39c18_rectangular_pair_of_le
    {H E : Type u} [Qudit H] [Qudit E] (A B : E →ₗ[ℂ] H)
    (hdim : Module.finrank ℂ H ≤ Module.finrank ℂ E) :
    rootFidelity (A.comp A.adjoint) (B.comp B.adjoint) =
      (Tr (CFC.sqrt ((A.adjoint.comp B) * (A.adjoint.comp B).adjoint))).re := by
  obtain ⟨J⟩ := w39c18_isometry_exists hdim
  let C := J.toLinearMap.comp A
  let D := J.toLinearMap.comp B
  have hC : C * C.adjoint = w39c18_push J (A.comp A.adjoint) := by
    simp only [C, w39c18_push, Module.End.mul_eq_comp, LinearMap.adjoint_comp,
      LinearMap.comp_assoc]
  have hD : D * D.adjoint = w39c18_push J (B.comp B.adjoint) := by
    simp only [D, w39c18_push, Module.End.mul_eq_comp, LinearMap.adjoint_comp,
      LinearMap.comp_assoc]
  have hCD : C.adjoint * D = A.adjoint.comp B := by
    simp only [C, D, Module.End.mul_eq_comp, LinearMap.adjoint_comp,
      LinearMap.comp_assoc]
    rw [← LinearMap.comp_assoc _ J.toLinearMap J.toLinearMap.adjoint,
      w39c18_iso_adjoint, LinearMap.id_comp]
  have h := w39c18_square_pair C D
  rw [hC, hD, hCD, w39c18_push_fidelity J _ _
    (LinearMap.isPositive_self_comp_adjoint A)
    (LinearMap.isPositive_self_comp_adjoint B)] at h
  exact h

/-- The case `dim E ≤ dim H` of `w39c18_rectangular_pair`: embed `E` isometrically into `H`. -/
private theorem w39c18_rectangular_pair_of_ge
    {H E : Type u} [Qudit H] [Qudit E] (A B : E →ₗ[ℂ] H)
    (hdim : Module.finrank ℂ E ≤ Module.finrank ℂ H) :
    rootFidelity (A.comp A.adjoint) (B.comp B.adjoint) =
      (Tr (CFC.sqrt ((A.adjoint.comp B) * (A.adjoint.comp B).adjoint))).re := by
  obtain ⟨J⟩ := w39c18_isometry_exists hdim
  let C := A.comp J.toLinearMap.adjoint
  let D := B.comp J.toLinearMap.adjoint
  have hC : C * C.adjoint = A.comp A.adjoint := by
    simp only [C, Module.End.mul_eq_comp, LinearMap.adjoint_comp,
      LinearMap.adjoint_adjoint, LinearMap.comp_assoc]
    rw [← LinearMap.comp_assoc _ J.toLinearMap J.toLinearMap.adjoint,
      w39c18_iso_adjoint, LinearMap.id_comp]
  have hD : D * D.adjoint = B.comp B.adjoint := by
    simp only [D, Module.End.mul_eq_comp, LinearMap.adjoint_comp,
      LinearMap.adjoint_adjoint, LinearMap.comp_assoc]
    rw [← LinearMap.comp_assoc _ J.toLinearMap J.toLinearMap.adjoint,
      w39c18_iso_adjoint, LinearMap.id_comp]
  have hCD : C.adjoint * D = w39c18_push J (A.adjoint.comp B) := by
    simp only [C, D, w39c18_push, Module.End.mul_eq_comp, LinearMap.adjoint_comp,
      LinearMap.adjoint_adjoint, LinearMap.comp_assoc]
  have h := w39c18_square_pair C D
  rw [hC, hD, hCD, w39c18_push_adjoint, ← w39c18_push_mul,
    w39c18_push_sqrt J ((A.adjoint.comp B) * (A.adjoint.comp B).adjoint)
      (LinearMap.isPositive_self_comp_adjoint _), w39c18_push_trace] at h
  exact h

private theorem w39c18_rectangular_pair
    {H E : Type u} [Qudit H] [Qudit E] (A B : E →ₗ[ℂ] H) :
    rootFidelity (A.comp A.adjoint) (B.comp B.adjoint) =
      (Tr (CFC.sqrt ((A.adjoint.comp B) * (A.adjoint.comp B).adjoint))).re := by
  rcases le_total (Module.finrank ℂ H) (Module.finrank ℂ E) with hdim | hdim
  · exact w39c18_rectangular_pair_of_le A B hdim
  · exact w39c18_rectangular_pair_of_ge A B hdim

private theorem w39c18_psd_factor
    {H E : Type u} [Qudit H] [Qudit E] (X : L H) (hX : X.IsPositive)
    (hdim : Module.finrank ℂ (LinearMap.range X) ≤ Module.finrank ℂ E) :
    ∃ A : E →ₗ[ℂ] H, A.comp A.adjoint = X := by
  let S := CFC.sqrt X
  have hS : S.adjoint = S := w39c18_sqrt_adjoint X
  have hSS : S * S = X :=
    CFC.sqrt_mul_sqrt_self X ((LinearMap.nonneg_iff_isPositive _).mpr hX)
  have hrange : S.range = X.range := by
    have h := LinearMap.range_self_comp_adjoint S
    rw [hS, ← Module.End.mul_eq_comp, hSS] at h
    exact h.symm
  letI : CompleteSpace S.range := S.range.complete_of_finiteDimensional.completeSpace_coe
  letI : Qudit S.range :=
    { (inferInstance : NormedAddCommGroup S.range),
      (inferInstance : InnerProductSpace ℂ S.range),
      (inferInstance : CompleteSpace S.range),
      (inferInstance : FiniteDimensional ℂ S.range) with }
  have hdimS : Module.finrank ℂ S.range ≤ Module.finrank ℂ E := by
    rw [hrange]
    exact hdim
  obtain ⟨J⟩ := w39c18_isometry_exists (H := S.range) (E := E) hdimS
  let F := J.toLinearMap.comp S.rangeRestrict
  refine ⟨F.adjoint, ?_⟩
  rw [LinearMap.adjoint_adjoint]
  ext x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y (F.adjoint (F x)) = inner ℂ y (X x)
  rw [LinearMap.adjoint_inner_right]
  change inner ℂ (J (S.rangeRestrict y)) (J (S.rangeRestrict x)) = _
  rw [J.inner_map_map]
  change inner ℂ (S y) (S x) = _
  rw [← LinearMap.adjoint_inner_right, hS]
  change inner ℂ y ((S * S) x) = _
  rw [hSS]

private theorem w39c18_rectangular_bound
    {H E : Type u} [Qudit H] [Qudit E] (A B : E →ₗ[ℂ] H) :
    Complex.normSq (Tr (A.adjoint.comp B)) ≤
      rootFidelity (A.comp A.adjoint) (B.comp B.adjoint) ^ 2 := by
  rw [w39c18_rectangular_pair, Complex.normSq_eq_norm_sq]
  have h := w39c18_trace_bound (A.adjoint.comp B)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

private theorem w39c18_rectangular_attainment
    {H E : Type u} [Qudit H] [Qudit E] (X Y : L H)
    (hX : X.IsPositive) (hY : Y.IsPositive)
    (hdim : max (Module.finrank ℂ (LinearMap.range X))
      (Module.finrank ℂ (LinearMap.range Y)) ≤ Module.finrank ℂ E) :
    ∃ A B : E →ₗ[ℂ] H,
      A.comp A.adjoint = X ∧ B.comp B.adjoint = Y ∧
      Complex.normSq (Tr (A.adjoint.comp B)) = rootFidelity X Y ^ 2 := by
  obtain ⟨A, hA⟩ := w39c18_psd_factor X hX ((le_max_left _ _).trans hdim)
  obtain ⟨B, hB⟩ := w39c18_psd_factor Y hY ((le_max_right _ _).trans hdim)
  let C := A.adjoint.comp B
  obtain ⟨U, hU⟩ := w39c18_polar C
  let D := B.comp U.toLinearMap.adjoint
  have hD : D.comp D.adjoint = Y := by
    simp only [D, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
      LinearMap.comp_assoc]
    rw [← LinearMap.comp_assoc _ U.toLinearMap U.toLinearMap.adjoint,
      w39c18_iso_adjoint, LinearMap.id_comp, hB]
  refine ⟨A, D, hA, hD, ?_⟩
  have ht : Tr (A.adjoint.comp D) = Tr (CFC.sqrt (C.adjoint * C)) := by
    change Tr (C * U.toLinearMap.adjoint) = _
    conv_lhs => rw [← hU]
    change Tr (w39c18_push U (CFC.sqrt (C.adjoint * C))) = _
    exact w39c18_push_trace U _
  have hf : rootFidelity X Y = (Tr (CFC.sqrt (C.adjoint * C))).re := by
    rw [← hA, ← hB, w39c18_rectangular_pair, w39c18_trace_sqrt_swap]
  have hp : 0 ≤ Tr (CFC.sqrt (C.adjoint * C)) := by
    have hs : 0 ≤ CFC.sqrt (C.adjoint * C) := CFC.sqrt_nonneg _
    exact ((LinearMap.nonneg_iff_isPositive _).mp hs).trace_nonneg
  rw [ht, hf, Complex.normSq_apply, ← (Complex.nonneg_iff.mp hp).2]
  ring

private theorem w39c18_vec_marginal
    {H E : Type u} [Qudit H] [Qudit E] (A : E →ₗ[ℂ] H) :
    TrRight (outer_product (vec (stdOrthonormalBasis ℂ E).toBasis A)
      (vec (stdOrthonormalBasis ℂ E).toBasis A)) = A.comp A.adjoint := by
  classical
  let b := stdOrthonormalBasis ℂ E
  change traceOutRight (outer_product (vec b.toBasis A) (vec b.toBasis A)) = _
  rw [vec_apply, outer_product_sum]
  simp only [OrthonormalBasis.coe_toBasis, map_sum, TrRight_outer_product_tmul_basis,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ext x
  simp only [LinearMap.sum_apply, outer_product_apply, LinearMap.comp_apply]
  conv_rhs => rw [← b.sum_repr' (A.adjoint x)]
  simp only [map_sum, map_smul, LinearMap.adjoint_inner_right]

private theorem w39c18_vec_surjective
    {H E : Type u} [Qudit H] [Qudit E] (ξ : H ⊗[ℂ] E) :
    ∃ A : E →ₗ[ℂ] H, vec (stdOrthonormalBasis ℂ E).toBasis A = ξ := by
  classical
  let b := stdOrthonormalBasis ℂ E
  let A := b.toBasis.constr ℂ (fun i => tensorRightSlice b i ξ)
  refine ⟨A, ?_⟩
  change vec b.toBasis A = ξ
  rw [vec_apply]
  simpa only [A, Module.Basis.constr_basis] using
    (tensorRightSlice_expand b ξ).symm

theorem w39_uhlmann_psd : ∀ {H E : Type u} [Qudit.{u} H] [Qudit.{u} E]
    [Nontrivial H] [Nontrivial E] (X Y : L H),
    X.IsPositive → Y.IsPositive → X ≠ 0 → Y ≠ 0 →
    max (Module.finrank ℂ (LinearMap.range X)) (Module.finrank ℂ (LinearMap.range Y)) ≤
      Module.finrank ℂ E →
    let S : Set ℝ := {r | ∃ ξ η : H ⊗[ℂ] E,
      TrRight (outer_product ξ ξ) = X ∧ TrRight (outer_product η η) = Y ∧
      r = Complex.normSq (inner ℂ ξ η)}
    IsGreatest S (rootFidelity X Y ^ 2) ∧
    (∃ ξ η : H ⊗[ℂ] E,
      TrRight (outer_product ξ ξ) = X ∧ TrRight (outer_product η η) = Y ∧
      Complex.normSq (inner ℂ ξ η) = rootFidelity X Y ^ 2) := by
  intro H E _ _ _ _ X Y hX hY _ _ hdim
  obtain ⟨A, B, hA, hB, hAB⟩ := w39c18_rectangular_attainment X Y hX hY hdim
  let b := stdOrthonormalBasis ℂ E
  have hw : ∃ ξ η : H ⊗[ℂ] E,
      TrRight (outer_product ξ ξ) = X ∧ TrRight (outer_product η η) = Y ∧
      Complex.normSq (inner ℂ ξ η) = rootFidelity X Y ^ 2 := by
    refine ⟨vec b.toBasis A, vec b.toBasis B,
      (w39c18_vec_marginal A).trans hA, (w39c18_vec_marginal B).trans hB, ?_⟩
    rw [inner_vec_eq_trace]
    exact hAB
  refine ⟨⟨?_, ?_⟩, hw⟩
  · obtain ⟨ξ, η, hξ, hη, heq⟩ := hw
    exact ⟨ξ, η, hξ, hη, heq.symm⟩
  · rintro r ⟨ξ, η, hξ, hη, rfl⟩
    obtain ⟨C, rfl⟩ := w39c18_vec_surjective ξ
    obtain ⟨D, rfl⟩ := w39c18_vec_surjective η
    rw [w39c18_vec_marginal] at hξ hη
    rw [inner_vec_eq_trace]
    simpa only [hξ, hη] using w39c18_rectangular_bound C D

end

end GourConditionalEntropy
