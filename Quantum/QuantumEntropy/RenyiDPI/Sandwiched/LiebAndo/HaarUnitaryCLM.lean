/-
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.Central.Basic
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Star.Unitary

import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.LiebAndo.TensorCFC
import Quantum.QuantumEntropy.TensorCFC
import Quantum.TraceInequality.LiebAndo.AndoConvexity.LiebTrace.Bridge
import Quantum.TraceInequality.LiebAndo.LiebTrace.Bridge
import Quantum.TraceInequality.LiebTrace.Bridge
import Quantum.QuantumMechanics.Channel.Basic
import Quantum.QuantumMechanics.Channel.Representations
import Quantum.QuantumMechanics.OperatorInstances

/-!
# Haar measure on continuous-linear unitary operators

This module is the CLM-native Haar producer.  Its carrier is written literally as
`unitary (ℋ →L[ℂ] ℋ)`.  The measurable, Borel, multiplicative, and star topologies on
continuous linear maps are Mathlib's canonical instances; this module does not transport
any topology from linear endomorphisms.
-/

open QuantumState QuantumChannel TensorCFC
open MeasureTheory MeasureTheory.Measure
open GeneralizedPerspectiveFunction
open scoped ComplexOrder TensorProduct

namespace HaarUnitaryCLM

universe u

/-! ## Compact unitary group and normalized Haar measure -/

section CompactHaar

variable {ℋ : Type u} [Qudit ℋ]

/-- Every unitary continuous endomorphism has operator norm at most one. -/
lemma norm_coe_unitary_le_one [Nontrivial ℋ] (U : unitary (B ℋ)) :
    ‖(U : B ℋ)‖ ≤ 1 := by
  rw [CStarRing.norm_coe_unitary]

/-- The unitary group of a finite-dimensional Hilbert space is bounded. -/
lemma unitary_isBounded [Nontrivial ℋ] :
    Bornology.IsBounded (unitary (B ℋ) : Set (B ℋ)) := by
  rw [Metric.isBounded_iff_subset_ball 0]
  exact ⟨2, fun x hx => by
    simp only [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (norm_coe_unitary_le_one ⟨x, hx⟩) one_lt_two⟩

/-- Compactness of the CLM-native unitary group. -/
instance compactSpace_unitary [Nontrivial ℋ] : CompactSpace (unitary (B ℋ)) := by
  have : ProperSpace (B ℋ) := FiniteDimensional.proper ℂ (B ℋ)
  exact isCompact_iff_compactSpace.mp
    (Metric.isCompact_of_isClosed_isBounded isClosed_unitary unitary_isBounded)

/-- Local compactness of the CLM-native unitary group. -/
instance locallyCompactSpace_unitary [Nontrivial ℋ] :
    LocallyCompactSpace (unitary (B ℋ)) := by
  haveI : ProperSpace (unitary (B ℋ)) := proper_of_compact
  exact locallyCompact_of_proper

/-- The positive compact normalizer used to construct normalized Haar measure. -/
noncomputable def unitaryPC (ℋ : Type u) [Qudit ℋ] [Nontrivial ℋ] :
    TopologicalSpace.PositiveCompacts (unitary (B ℋ)) :=
  ⟨⟨Set.univ, isCompact_univ⟩, by rw [interior_univ]; exact Set.univ_nonempty⟩

/-- The normalized Haar measure on `unitary (ℋ →L[ℂ] ℋ)`.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
noncomputable def haarUnitary (ℋ : Type u) [Qudit ℋ] [Nontrivial ℋ] :
    Measure (unitary (B ℋ)) :=
  haarMeasure (unitaryPC ℋ)

instance haarUnitary_isHaarMeasure [Nontrivial ℋ] :
    IsHaarMeasure (haarUnitary ℋ) := by
  unfold haarUnitary
  infer_instance

/-- The normalized Haar measure has total mass one. -/
instance haarUnitary_isProbabilityMeasure [Nontrivial ℋ] :
    IsProbabilityMeasure (haarUnitary ℋ) :=
  ⟨by
    change haarMeasure (unitaryPC ℋ) Set.univ = 1
    have hself : haarMeasure (unitaryPC ℋ) (unitaryPC ℋ : Set _) = 1 := haarMeasure_self
    simpa [unitaryPC] using hself⟩

end CompactHaar

/-! ## Continuity and integrability of conjugation -/

section Measurability

variable {ℋ : Type u} [Qudit ℋ]

/-- Unitary conjugation on continuous endomorphisms is continuous. -/
lemma continuous_unitaryConj (X : B ℋ) :
    Continuous (fun u : unitary (B ℋ) =>
      (u : B ℋ) * X * star (u : B ℋ)) := by
  exact ((continuous_subtype_val.mul continuous_const).mul
    (continuous_star.comp continuous_subtype_val))

/-- Unitary conjugation is Bochner-integrable for normalized Haar measure. -/
lemma integrable_unitaryConj [Nontrivial ℋ] (X : B ℋ) :
    Integrable (fun u : unitary (B ℋ) =>
      (u : B ℋ) * X * star (u : B ℋ))
      (haarUnitary ℋ) :=
  (continuous_unitaryConj X).integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))

end Measurability

/-! ## Twirling and Schur orthogonality -/

section Twirl

variable {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]

omit [Nontrivial ℋ] in
/-- An operator commuting with every CLM-native unitary is scalar. -/
lemma scalar_of_commutes_unitaries (M : ℋ →L[ℂ] ℋ)
    (hM : ∀ V : unitary (ℋ →L[ℂ] ℋ),
      (V : ℋ →L[ℂ] ℋ) * M = M * (V : ℋ →L[ℂ] ℋ)) :
    ∃ c : ℂ, M = c • (1 : ℋ →L[ℂ] ℋ) := by
  let commutant : Submodule ℂ (ℋ →L[ℂ] ℋ) :=
    { carrier := {A | A * M = M * A}
      zero_mem' := by simp
      add_mem' := by
        intro A B hA hB
        simp only [Set.mem_setOf_eq, add_mul, mul_add]
        rw [hA, hB]
      smul_mem' := by
        intro c A hA
        simp only [Set.mem_setOf_eq, smul_mul_assoc, mul_smul_comm]
        rw [hA] }
  have hspan : Submodule.span ℂ (unitary (ℋ →L[ℂ] ℋ) : Set (ℋ →L[ℂ] ℋ)) ≤ commutant :=
    Submodule.span_le.mpr fun A hA => hM ⟨A, hA⟩
  have hcomm : ∀ A : ℋ →L[ℂ] ℋ, A * M = M * A := by
    intro A
    exact hspan (by rw [CStarAlgebra.span_unitary]; exact Submodule.mem_top)
  have hcenter : M ∈ Subalgebra.center ℂ (ℋ →L[ℂ] ℋ) := by
    rw [Subalgebra.mem_center_iff]
    exact hcomm
  obtain ⟨c, hc⟩ := (Algebra.IsCentral.mem_center_iff ℂ).mp hcenter
  exact ⟨c, by simpa [Algebra.algebraMap_eq_smul_one] using hc⟩

private noncomputable def traceCLM (ℋ : Type u) [Qudit ℋ] :
    (ℋ →L[ℂ] ℋ) →L[ℂ] ℂ :=
  { toFun := fun A => LinearMap.trace ℂ ℋ (A : L ℋ)
    map_add' := fun A B => by simp
    map_smul' := fun (c : ℂ) A => by
      change LinearMap.trace ℂ ℋ (c • (A : L ℋ)) =
        c • LinearMap.trace ℂ ℋ (A : L ℋ)
      exact map_smul (LinearMap.trace ℂ ℋ) c (A : L ℋ)
    cont := LinearMap.continuous_of_finiteDimensional
      { toFun := fun A : ℋ →L[ℂ] ℋ => LinearMap.trace ℂ ℋ (A : L ℋ)
        map_add' := fun A B => by simp
        map_smul' := fun (c : ℂ) A => by
          change LinearMap.trace ℂ ℋ (c • (A : L ℋ)) =
            c • LinearMap.trace ℂ ℋ (A : L ℋ)
          exact map_smul (LinearMap.trace ℂ ℋ) c (A : L ℋ) } }

/-- Averaging unitary conjugation gives the scalar trace projection.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
theorem twirl_eq_smul_one (X : ℋ →L[ℂ] ℋ) :
    ∫ u : unitary (ℋ →L[ℂ] ℋ),
      (u : ℋ →L[ℂ] ℋ) * X * star (u : ℋ →L[ℂ] ℋ) ∂(haarUnitary ℋ) =
    ((Module.finrank ℂ ℋ : ℂ)⁻¹ * LinearMap.trace ℂ ℋ (X : L ℋ)) •
      (1 : ℋ →L[ℂ] ℋ) := by
  set Φ := ∫ u : unitary (ℋ →L[ℂ] ℋ),
    (u : ℋ →L[ℂ] ℋ) * X * star (u : ℋ →L[ℂ] ℋ) ∂(haarUnitary ℋ)
  have hΦ_comm : ∀ V : unitary (ℋ →L[ℂ] ℋ),
      (V : ℋ →L[ℂ] ℋ) * Φ = Φ * (V : ℋ →L[ℂ] ℋ) := by
    intro V
    suffices h_conj : (V : ℋ →L[ℂ] ℋ) * Φ * star (V : ℋ →L[ℂ] ℋ) = Φ by
      have hVV : star (V : ℋ →L[ℂ] ℋ) * (V : ℋ →L[ℂ] ℋ) = 1 :=
        (Unitary.mem_iff.mp V.property).1
      calc
        (V : ℋ →L[ℂ] ℋ) * Φ = (V : ℋ →L[ℂ] ℋ) * Φ * 1 := (mul_one _).symm
        _ = (V : ℋ →L[ℂ] ℋ) * Φ *
            (star (V : ℋ →L[ℂ] ℋ) * (V : ℋ →L[ℂ] ℋ)) := by rw [hVV]
        _ = ((V : ℋ →L[ℂ] ℋ) * Φ * star (V : ℋ →L[ℂ] ℋ)) *
            (V : ℋ →L[ℂ] ℋ) := by rw [mul_assoc ((V : ℋ →L[ℂ] ℋ) * Φ)]
        _ = Φ * (V : ℋ →L[ℂ] ℋ) := by rw [h_conj]
    let conjV : (ℋ →L[ℂ] ℋ) →L[ℂ] (ℋ →L[ℂ] ℋ) :=
      { toFun := fun A => (V : ℋ →L[ℂ] ℋ) * A * star (V : ℋ →L[ℂ] ℋ)
        map_add' := fun A B => by rw [mul_add, add_mul]
        map_smul' := fun c A => by rw [RingHom.id_apply, mul_smul_comm, smul_mul_assoc]
        cont := (continuous_const.mul continuous_id).mul continuous_const }
    have h_pull := conjV.integral_comp_comm (integrable_unitaryConj X)
    have hfVu : ∀ u : unitary (ℋ →L[ℂ] ℋ),
        conjV ((u : ℋ →L[ℂ] ℋ) * X * star (u : ℋ →L[ℂ] ℋ)) =
        ((V * u : unitary (ℋ →L[ℂ] ℋ)) : ℋ →L[ℂ] ℋ) * X *
          star ((V * u : unitary (ℋ →L[ℂ] ℋ)) : ℋ →L[ℂ] ℋ) := by
      intro u
      change (V : ℋ →L[ℂ] ℋ) *
        ((u : ℋ →L[ℂ] ℋ) * X * star (u : ℋ →L[ℂ] ℋ)) *
        star (V : ℋ →L[ℂ] ℋ) = _
      simp only [MulMemClass.coe_mul, star_mul, mul_assoc]
    simp_rw [hfVu] at h_pull
    have h_haar := integral_mul_left_eq_self (μ := haarUnitary ℋ)
      (fun u : unitary (ℋ →L[ℂ] ℋ) =>
        (u : ℋ →L[ℂ] ℋ) * X * star (u : ℋ →L[ℂ] ℋ)) V
    exact h_pull.symm.trans h_haar
  obtain ⟨c, hc⟩ := scalar_of_commutes_unitaries Φ hΦ_comm
  have hc_val : c = (Module.finrank ℂ ℋ : ℂ)⁻¹ *
      LinearMap.trace ℂ ℋ (X : L ℋ) := by
    have hd : (Module.finrank ℂ ℋ : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℂ) (M := ℋ)).ne'
    have h1 : LinearMap.trace ℂ ℋ (Φ : L ℋ) =
        c * (Module.finrank ℂ ℋ : ℂ) := by
      rw [hc]
      change LinearMap.trace ℂ ℋ (c • (1 : L ℋ)) =
        c * (Module.finrank ℂ ℋ : ℂ)
      rw [map_smul, LinearMap.trace_one, smul_eq_mul]
    have h2 : LinearMap.trace ℂ ℋ (Φ : L ℋ) =
        LinearMap.trace ℂ ℋ (X : L ℋ) := by
      have h_tr := (traceCLM ℋ).integral_comp_comm (integrable_unitaryConj X)
      have h_cycl : ∀ u : unitary (ℋ →L[ℂ] ℋ),
          traceCLM ℋ ((u : ℋ →L[ℂ] ℋ) * X * star (u : ℋ →L[ℂ] ℋ)) =
          LinearMap.trace ℂ ℋ (X : L ℋ) := by
        intro u
        simp only [traceCLM]
        change LinearMap.trace ℂ ℋ
          ((((u : ℋ →L[ℂ] ℋ) * X * star (u : ℋ →L[ℂ] ℋ) :
            QuantumState.B ℋ) : L ℋ)) = _
        rw [show (((u : ℋ →L[ℂ] ℋ) * X * star (u : ℋ →L[ℂ] ℋ) :
            QuantumState.B ℋ) : L ℋ) =
            ((u : ℋ →L[ℂ] ℋ) : L ℋ) * (X : L ℋ) *
              ((star (u : ℋ →L[ℂ] ℋ) : QuantumState.B ℋ) : L ℋ) from rfl,
          LinearMap.trace_mul_cycle,
          show ((star (u : ℋ →L[ℂ] ℋ) : QuantumState.B ℋ) : L ℋ) *
              ((u : ℋ →L[ℂ] ℋ) : L ℋ) = 1 from
            congrArg ContinuousLinearMap.toLinearMap (Unitary.mem_iff.mp u.property).1,
          one_mul]
      simp_rw [h_cycl] at h_tr
      simp only [integral_const, probReal_univ, one_smul] at h_tr
      simpa only [traceCLM, Φ] using h_tr.symm
    have h := h1.symm.trans h2
    rw [← h, mul_comm c (Module.finrank ℂ ℋ : ℂ), ← mul_assoc,
      inv_mul_cancel₀ hd, one_mul]
  rw [hc, hc_val]

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- Schur orthogonality for the fundamental CLM representation.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
theorem schur_orthogonality (b : OrthonormalBasis ι ℂ ℋ) (i j k l : ι) :
    ∫ u : unitary (ℋ →L[ℂ] ℋ),
      @inner ℂ ℋ _ (b i) ((u : ℋ →L[ℂ] ℋ) (b j)) *
      starRingEnd ℂ (@inner ℂ ℋ _ (b k) ((u : ℋ →L[ℂ] ℋ) (b l)))
    ∂(haarUnitary ℋ) =
    if i = k ∧ j = l then (Fintype.card ι : ℂ)⁻¹ else 0 := by
  set X : ℋ →L[ℂ] ℋ := InnerProductSpace.rankOne ℂ (b j) (b l) with hX
  have h_int : ∀ u : unitary (ℋ →L[ℂ] ℋ),
      @inner ℂ ℋ _ (b i) ((u : ℋ →L[ℂ] ℋ) (b j)) *
        starRingEnd ℂ (@inner ℂ ℋ _ (b k) ((u : ℋ →L[ℂ] ℋ) (b l))) =
      @inner ℂ ℋ _ (b i)
        (((u : ℋ →L[ℂ] ℋ) * X * star (u : ℋ →L[ℂ] ℋ)) (b k)) := by
    intro u
    rw [hX]
    simp [InnerProductSpace.rankOne_apply,
      ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]
    ring
  simp_rw [h_int]
  let elem : (ℋ →L[ℂ] ℋ) →L[ℂ] ℂ :=
    { toFun := fun A => @inner ℂ ℋ _ (b i) (A (b k))
      map_add' := fun A B => by simp
      map_smul' := fun (c : ℂ) A => by simp
      cont := LinearMap.continuous_of_finiteDimensional
        { toFun := fun A : ℋ →L[ℂ] ℋ => @inner ℂ ℋ _ (b i) (A (b k))
          map_add' := fun A B => by simp
          map_smul' := fun (c : ℂ) A => by simp } }
  change (∫ u : unitary (ℋ →L[ℂ] ℋ),
      elem ((u : ℋ →L[ℂ] ℋ) * X * star (u : ℋ →L[ℂ] ℋ)) ∂(haarUnitary ℋ)) = _
  rw [elem.integral_comp_comm (integrable_unitaryConj X), twirl_eq_smul_one X]
  change @inner ℂ ℋ _ (b i)
      (((Module.finrank ℂ ℋ : ℂ)⁻¹ * LinearMap.trace ℂ ℋ (X : L ℋ)) • b k) = _
  rw [inner_smul_right]
  have hTr : LinearMap.trace ℂ ℋ (X : L ℋ) = @inner ℂ ℋ _ (b l) (b j) := by
    rw [hX]
    exact InnerProductSpace.trace_rankOne (b j) (b l)
  rw [hTr, Module.finrank_eq_card_basis b.toBasis]
  have horth := orthonormal_iff_ite.mp b.orthonormal
  rw [horth l j, horth i k]
  simp only [show (l = j) = (j = l) from propext eq_comm]
  by_cases hik : i = k <;> by_cases hjl : j = l <;> simp [hik, hjl]

end Twirl

/-! ## Tensor-factor twirling -/

section TensorTwirl

variable {ℋ₁ : Type u} {ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂]
variable [Nontrivial ℋ₁] [Nontrivial ℋ₂]

/-- The canonical CLM tensor product of two continuous endomorphisms. -/
noncomputable def tensorMap (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    (ℋ₁ ⊗[ℂ] ℋ₂) →L[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂) :=
  (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂)).toContinuousLinearMap

/-- The first-factor partial trace, with CLM input and output. -/
noncomputable def traceOutLeft (X : B (ℋ₁ ⊗[ℂ] ℋ₂)) :
    B ℋ₂ :=
  (QuantumChannel.traceOutLeft (X : L (ℋ₁ ⊗[ℂ] ℋ₂))).toContinuousLinearMap

/-- The second-factor partial trace, with CLM input and output. -/
noncomputable def traceOutRight (X : B (ℋ₁ ⊗[ℂ] ℋ₂)) :
    B ℋ₁ :=
  (QuantumChannel.traceOutRight (X : L (ℋ₁ ⊗[ℂ] ℋ₂))).toContinuousLinearMap

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
@[simp] lemma tensorMap_toLinearMap (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    ((tensorMap A B : (ℋ₁ ⊗[ℂ] ℋ₂) →L[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂)) :
      L (ℋ₁ ⊗[ℂ] ℋ₂)) =
      TensorProduct.map (A : L ℋ₁) (B : L ℋ₂) := rfl

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
@[simp] lemma traceOutLeft_toLinearMap
    (X : B (ℋ₁ ⊗[ℂ] ℋ₂)) :
    ((traceOutLeft X : B ℋ₂) : L ℋ₂) =
      QuantumChannel.traceOutLeft (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) := rfl

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
@[simp] lemma traceOutRight_toLinearMap
    (X : B (ℋ₁ ⊗[ℂ] ℋ₂)) :
    ((traceOutRight X : B ℋ₁) : L ℋ₁) =
      QuantumChannel.traceOutRight (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) := rfl

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma tensorMap_eq_mul (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    tensorMap A B =
      rTensorContinuousStarAlgHom (ℋ₂ := ℋ₂) A *
        lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁) B := by
  change (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂)).toContinuousLinearMap =
    ((rTensorStarAlgHom (ℋ₂ := ℋ₂)) (A : L ℋ₁) *
      (lTensorStarAlgHom (ℋ₁ := ℋ₁)) (B : L ℋ₂)).toContinuousLinearMap
  exact congrArg LinearMap.toContinuousLinearMap
    (TensorCFC.map_eq_rTensor_mul_lTensor (A : L ℋ₁) (B : L ℋ₂))

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma tensorMap_eq_mul_comm (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    tensorMap A B =
      lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁) B *
        rTensorContinuousStarAlgHom (ℋ₂ := ℋ₂) A := by
  change (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂)).toContinuousLinearMap =
    ((lTensorStarAlgHom (ℋ₁ := ℋ₁)) (B : L ℋ₂) *
      (rTensorStarAlgHom (ℋ₂ := ℋ₂)) (A : L ℋ₁)).toContinuousLinearMap
  exact congrArg LinearMap.toContinuousLinearMap
    (TensorCFC.map_eq_lTensor_mul_rTensor (A : L ℋ₁) (B : L ℋ₂))

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma tensorMap_add_left (A₁ A₂ : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    tensorMap (A₁ + A₂) B = tensorMap A₁ B + tensorMap A₂ B := by
  change (TensorProduct.map ((A₁ : L ℋ₁) + (A₂ : L ℋ₁))
      (B : L ℋ₂)).toContinuousLinearMap =
    (TensorProduct.map (A₁ : L ℋ₁) (B : L ℋ₂) +
      TensorProduct.map (A₂ : L ℋ₁) (B : L ℋ₂)).toContinuousLinearMap
  exact congrArg LinearMap.toContinuousLinearMap
    (TensorProduct.map_add_left (A₁ : L ℋ₁) (A₂ : L ℋ₁) (B : L ℋ₂))

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma tensorMap_add_right (A : B ℋ₁) (B₁ B₂ : B ℋ₂) :
    tensorMap A (B₁ + B₂) = tensorMap A B₁ + tensorMap A B₂ := by
  change (TensorProduct.map (A : L ℋ₁)
      ((B₁ : L ℋ₂) + (B₂ : L ℋ₂))).toContinuousLinearMap =
    (TensorProduct.map (A : L ℋ₁) (B₁ : L ℋ₂) +
      TensorProduct.map (A : L ℋ₁) (B₂ : L ℋ₂)).toContinuousLinearMap
  exact congrArg LinearMap.toContinuousLinearMap
    (TensorProduct.map_add_right (A : L ℋ₁) (B₁ : L ℋ₂) (B₂ : L ℋ₂))

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma tensorMap_smul_left (c : ℂ) (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    tensorMap (c • A) B = c • tensorMap A B := by
  rw [tensorMap_eq_mul, tensorMap_eq_mul, map_smul]
  exact smul_mul_assoc c _ _

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma tensorMap_smul_right (c : ℂ) (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    tensorMap A (c • B) = c • tensorMap A B := by
  rw [tensorMap_eq_mul, tensorMap_eq_mul, map_smul]
  exact mul_smul_comm c _ _

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma tensorMap_smul_swap
    (a b : ℂ) (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    tensorMap A ((a * b) • B) = tensorMap (b • A) (a • B) := by
  simp only [tensorMap_smul_left, tensorMap_smul_right, smul_smul]

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma tensorMap_mul (A₁ A₂ : B ℋ₁) (B₁ B₂ : B ℋ₂) :
    tensorMap A₁ B₁ * tensorMap A₂ B₂ = tensorMap (A₁ * A₂) (B₁ * B₂) := by
  change (TensorProduct.map (A₁ : L ℋ₁) (B₁ : L ℋ₂) *
      TensorProduct.map (A₂ : L ℋ₁) (B₂ : L ℋ₂)).toContinuousLinearMap =
    (TensorProduct.map ((A₁ : L ℋ₁) * (A₂ : L ℋ₁))
      ((B₁ : L ℋ₂) * (B₂ : L ℋ₂))).toContinuousLinearMap
  exact congrArg LinearMap.toContinuousLinearMap
    (TensorProduct.map_mul (A₁ : L ℋ₁) (A₂ : L ℋ₁)
      (B₁ : L ℋ₂) (B₂ : L ℋ₂)).symm

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma tensorMap_star (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    star (tensorMap A B) = tensorMap (star A) (star B) := by
  rw [tensorMap_eq_mul, star_mul]
  rw [← map_star (lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)) B,
    ← map_star (rTensorContinuousStarAlgHom (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)) A]
  exact (tensorMap_eq_mul_comm (star A) (star B)).symm

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma tensorMap_one :
    tensorMap (1 : B ℋ₁) (1 : B ℋ₂) = 1 := by
  change (TensorProduct.map (1 : L ℋ₁) (1 : L ℋ₂)).toContinuousLinearMap =
    (1 : L (ℋ₁ ⊗[ℂ] ℋ₂)).toContinuousLinearMap
  exact congrArg LinearMap.toContinuousLinearMap TensorProduct.map_one

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma continuous_tensorMap_left (B : ℋ₂ →L[ℂ] ℋ₂) :
    Continuous (fun A : ℋ₁ →L[ℂ] ℋ₁ => tensorMap A B) := by
  simp_rw [tensorMap_eq_mul]
  exact (rTensorContinuousStarAlgHom (ℋ₁ := ℋ₁)
    (ℋ₂ := ℋ₂)).toLinearMap.continuous_of_finiteDimensional.mul continuous_const

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma continuous_tensorMap_right (A : ℋ₁ →L[ℂ] ℋ₁) :
    Continuous (fun B : ℋ₂ →L[ℂ] ℋ₂ => tensorMap A B) := by
  simp_rw [tensorMap_eq_mul]
  exact continuous_const.mul
    (lTensorContinuousStarAlgHom (ℋ₁ := ℋ₁)
      (ℋ₂ := ℋ₂)).toLinearMap.continuous_of_finiteDimensional

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private noncomputable def tensorMapRight (B : ℋ₂ →L[ℂ] ℋ₂) :
    (ℋ₁ →L[ℂ] ℋ₁) →L[ℂ] ((ℋ₁ ⊗[ℂ] ℋ₂) →L[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂)) :=
  { toFun := fun A => tensorMap A B
    map_add' := fun A₁ A₂ => tensorMap_add_left A₁ A₂ B
    map_smul' := fun c A => tensorMap_smul_left c A B
    cont := continuous_tensorMap_left B }

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private noncomputable def tensorMapLeft (A : ℋ₁ →L[ℂ] ℋ₁) :
    (ℋ₂ →L[ℂ] ℋ₂) →L[ℂ] ((ℋ₁ ⊗[ℂ] ℋ₂) →L[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂)) :=
  { toFun := fun B => tensorMap A B
    map_add' := tensorMap_add_right A
    map_smul' := fun c B => tensorMap_smul_right c A B
    cont := continuous_tensorMap_right A }

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma traceOutLeft_tensorMap (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    traceOutLeft (tensorMap A B) =
      LinearMap.trace ℂ ℋ₁ (A : L ℋ₁) • B := by
  change (QuantumChannel.traceOutLeft
      (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂))).toContinuousLinearMap =
    (LinearMap.trace ℂ ℋ₁ (A : L ℋ₁) • (B : L ℋ₂)).toContinuousLinearMap
  congr 1
  rw [← QuantumChannel.endomorphismTensorEquiv_symm_tmul (A : L ℋ₁) (B : L ℋ₂),
    QuantumChannel.traceOutLeft_tmul]

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma traceOutRight_tensorMap (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    traceOutRight (tensorMap A B) =
      LinearMap.trace ℂ ℋ₂ (B : L ℋ₂) • A := by
  change (QuantumChannel.traceOutRight
      (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂))).toContinuousLinearMap =
    (LinearMap.trace ℂ ℋ₂ (B : L ℋ₂) • (A : L ℋ₁)).toContinuousLinearMap
  congr 1
  unfold QuantumChannel.traceOutRight
  simp only [LinearMap.comp_apply]
  have hswap : QuantumChannel.conjugateEnd (TensorProduct.comm ℂ ℋ₁ ℋ₂)
      (TensorProduct.map (A : L ℋ₁) (B : L ℋ₂)) =
      TensorProduct.map (B : L ℋ₂) (A : L ℋ₁) := by
    apply TensorProduct.ext'
    intro y x
    simp [QuantumChannel.conjugateEnd, TensorProduct.map_tmul]
  rw [hswap, ← QuantumChannel.endomorphismTensorEquiv_symm_tmul (B : L ℋ₂) (A : L ℋ₁),
    QuantumChannel.traceOutLeft_tmul]

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma traceOutLeft_add
    (X Y : B (ℋ₁ ⊗[ℂ] ℋ₂)) :
    traceOutLeft (X + Y) = traceOutLeft X + traceOutLeft Y := by
  change (QuantumChannel.traceOutLeft
      ((X : L (ℋ₁ ⊗[ℂ] ℋ₂)) + (Y : L (ℋ₁ ⊗[ℂ] ℋ₂)))).toContinuousLinearMap =
    (QuantumChannel.traceOutLeft (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) +
      QuantumChannel.traceOutLeft (Y : L (ℋ₁ ⊗[ℂ] ℋ₂))).toContinuousLinearMap
  exact congrArg LinearMap.toContinuousLinearMap
    (QuantumChannel.traceOutLeft.map_add
      (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) (Y : L (ℋ₁ ⊗[ℂ] ℋ₂)))

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
private lemma traceOutRight_add
    (X Y : B (ℋ₁ ⊗[ℂ] ℋ₂)) :
    traceOutRight (X + Y) = traceOutRight X + traceOutRight Y := by
  change (QuantumChannel.traceOutRight
      ((X : L (ℋ₁ ⊗[ℂ] ℋ₂)) + (Y : L (ℋ₁ ⊗[ℂ] ℋ₂)))).toContinuousLinearMap =
    (QuantumChannel.traceOutRight (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) +
      QuantumChannel.traceOutRight (Y : L (ℋ₁ ⊗[ℂ] ℋ₂))).toContinuousLinearMap
  exact congrArg LinearMap.toContinuousLinearMap
    (QuantumChannel.traceOutRight.map_add
      (X : L (ℋ₁ ⊗[ℂ] ℋ₂)) (Y : L (ℋ₁ ⊗[ℂ] ℋ₂)))

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- First-factor tensor conjugation is continuous. -/
lemma continuous_unitaryConj_tensor (X : B (ℋ₁ ⊗[ℂ] ℋ₂)) :
    Continuous (fun u : unitary (B ℋ₁) =>
      tensorMap (u : B ℋ₁) (1 : B ℋ₂) * X *
        tensorMap (star (u : B ℋ₁)) (1 : B ℋ₂)) := by
  have hleft : Continuous (fun u : unitary (B ℋ₁) =>
      tensorMap (u : B ℋ₁) (1 : B ℋ₂)) :=
    (continuous_tensorMap_left (1 : B ℋ₂)).comp continuous_subtype_val
  have hright : Continuous (fun u : unitary (B ℋ₁) =>
      tensorMap (star (u : B ℋ₁)) (1 : B ℋ₂)) :=
    (continuous_tensorMap_left (1 : B ℋ₂)).comp
      (continuous_star.comp continuous_subtype_val)
  exact (hleft.mul continuous_const).mul hright

omit [Nontrivial ℋ₂] in
/-- First-factor tensor conjugation is Haar-integrable. -/
lemma integrable_unitaryConj_tensor (X : B (ℋ₁ ⊗[ℂ] ℋ₂)) :
    Integrable (fun u : unitary (B ℋ₁) =>
      tensorMap (u : B ℋ₁) (1 : B ℋ₂) * X *
        tensorMap (star (u : B ℋ₁)) (1 : B ℋ₂))
      (haarUnitary ℋ₁) :=
  (continuous_unitaryConj_tensor X).integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))

omit [Nontrivial ℋ₂] in
/-- First-factor twirl of a product operator. -/
private lemma twirl_tensorMap_left (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    ∫ u : unitary (ℋ₁ →L[ℂ] ℋ₁),
      tensorMap (u : ℋ₁ →L[ℂ] ℋ₁) (1 : ℋ₂ →L[ℂ] ℋ₂) * tensorMap A B *
        tensorMap (star (u : ℋ₁ →L[ℂ] ℋ₁)) (1 : ℋ₂ →L[ℂ] ℋ₂)
    ∂(haarUnitary ℋ₁) =
    tensorMap ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ • (1 : ℋ₁ →L[ℂ] ℋ₁))
      (traceOutLeft (tensorMap A B)) := by
  have hintegrand : ∀ u : unitary (ℋ₁ →L[ℂ] ℋ₁),
      tensorMap (u : ℋ₁ →L[ℂ] ℋ₁) (1 : ℋ₂ →L[ℂ] ℋ₂) * tensorMap A B *
        tensorMap (star (u : ℋ₁ →L[ℂ] ℋ₁)) (1 : ℋ₂ →L[ℂ] ℋ₂) =
      tensorMap ((u : ℋ₁ →L[ℂ] ℋ₁) * A * star (u : ℋ₁ →L[ℂ] ℋ₁)) B := by
    intro u
    rw [tensorMap_mul, tensorMap_mul]
    simp only [mul_one, one_mul]
  simp_rw [hintegrand]
  calc
    (∫ u : unitary (ℋ₁ →L[ℂ] ℋ₁),
        tensorMap ((u : ℋ₁ →L[ℂ] ℋ₁) * A * star (u : ℋ₁ →L[ℂ] ℋ₁)) B ∂(haarUnitary ℋ₁)) =
        tensorMapRight B
          (∫ u : unitary (ℋ₁ →L[ℂ] ℋ₁),
            (u : ℋ₁ →L[ℂ] ℋ₁) * A * star (u : ℋ₁ →L[ℂ] ℋ₁) ∂(haarUnitary ℋ₁)) :=
      (tensorMapRight B).integral_comp_comm (integrable_unitaryConj A)
    _ = tensorMap ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ • (1 : ℋ₁ →L[ℂ] ℋ₁))
          (traceOutLeft (tensorMap A B)) := by
      rw [twirl_eq_smul_one, traceOutLeft_tensorMap]
      change tensorMap
          (((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ * LinearMap.trace ℂ ℋ₁ (A : L ℋ₁)) •
            (1 : ℋ₁ →L[ℂ] ℋ₁)) B =
        tensorMap ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ • (1 : ℋ₁ →L[ℂ] ℋ₁))
          (LinearMap.trace ℂ ℋ₁ (A : L ℋ₁) • B)
      simp only [tensorMap_smul_left, tensorMap_smul_right, smul_smul, mul_comm]

omit [Nontrivial ℋ₂] in
/-- The first-factor twirl formula holds for `0`. -/
private lemma twirl_left_zero :
    ∫ u : unitary (ℋ₁ →L[ℂ] ℋ₁),
      tensorMap (u : ℋ₁ →L[ℂ] ℋ₁) (1 : ℋ₂ →L[ℂ] ℋ₂) * (0 : B (ℋ₁ ⊗[ℂ] ℋ₂)) *
        tensorMap (star (u : ℋ₁ →L[ℂ] ℋ₁)) (1 : ℋ₂ →L[ℂ] ℋ₂)
    ∂(haarUnitary ℋ₁) =
    tensorMap ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ • (1 : ℋ₁ →L[ℂ] ℋ₁))
      (traceOutLeft (0 : B (ℋ₁ ⊗[ℂ] ℋ₂))) := by
  simp [tensorMap, traceOutLeft, TensorProduct.map_zero_right]

omit [Nontrivial ℋ₂] in
/-- The first-factor twirl formula is additive. -/
private lemma twirl_left_add {X Y : B (ℋ₁ ⊗[ℂ] ℋ₂)}
    (hX : ∫ u : unitary (ℋ₁ →L[ℂ] ℋ₁),
      tensorMap (u : ℋ₁ →L[ℂ] ℋ₁) (1 : ℋ₂ →L[ℂ] ℋ₂) * X *
        tensorMap (star (u : ℋ₁ →L[ℂ] ℋ₁)) (1 : ℋ₂ →L[ℂ] ℋ₂)
      ∂(haarUnitary ℋ₁) =
      tensorMap ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ • (1 : ℋ₁ →L[ℂ] ℋ₁)) (traceOutLeft X))
    (hY : ∫ u : unitary (ℋ₁ →L[ℂ] ℋ₁),
      tensorMap (u : ℋ₁ →L[ℂ] ℋ₁) (1 : ℋ₂ →L[ℂ] ℋ₂) * Y *
        tensorMap (star (u : ℋ₁ →L[ℂ] ℋ₁)) (1 : ℋ₂ →L[ℂ] ℋ₂)
      ∂(haarUnitary ℋ₁) =
      tensorMap ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ • (1 : ℋ₁ →L[ℂ] ℋ₁)) (traceOutLeft Y)) :
    ∫ u : unitary (ℋ₁ →L[ℂ] ℋ₁),
      tensorMap (u : ℋ₁ →L[ℂ] ℋ₁) (1 : ℋ₂ →L[ℂ] ℋ₂) * (X + Y) *
        tensorMap (star (u : ℋ₁ →L[ℂ] ℋ₁)) (1 : ℋ₂ →L[ℂ] ℋ₂)
    ∂(haarUnitary ℋ₁) =
    tensorMap ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ • (1 : ℋ₁ →L[ℂ] ℋ₁)) (traceOutLeft (X + Y)) := by
  simp only [mul_add, add_mul]
  rw [integral_add
    (integrable_unitaryConj_tensor (ℋ₂ := ℋ₂) _)
    (integrable_unitaryConj_tensor (ℋ₂ := ℋ₂) _),
    hX, hY, traceOutLeft_add, tensorMap_add_right]

omit [Nontrivial ℋ₂] in
/-- First-factor twirl formula on operators written through `endomorphismTensorEquiv`. -/
private lemma twirl_left_endomorphismTensorEquiv (Y : L ℋ₁ ⊗[ℂ] L ℋ₂) :
    (∫ u : unitary (ℋ₁ →L[ℂ] ℋ₁),
      tensorMap (u : ℋ₁ →L[ℂ] ℋ₁) (1 : ℋ₂ →L[ℂ] ℋ₂) *
        Module.End.toContinuousLinearMap (𝕜 := ℂ) (ℋ₁ ⊗[ℂ] ℋ₂)
          ((QuantumChannel.endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).symm Y) *
        tensorMap (star (u : ℋ₁ →L[ℂ] ℋ₁)) (1 : ℋ₂ →L[ℂ] ℋ₂)
      ∂(haarUnitary ℋ₁)) =
    tensorMap ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ • (1 : ℋ₁ →L[ℂ] ℋ₁))
      (traceOutLeft (Module.End.toContinuousLinearMap (𝕜 := ℂ) (ℋ₁ ⊗[ℂ] ℋ₂)
        ((QuantumChannel.endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).symm Y))) := by
  let e₁ := Module.End.toContinuousLinearMap (𝕜 := ℂ) ℋ₁
  let e₂ := Module.End.toContinuousLinearMap (𝕜 := ℂ) ℋ₂
  let e₁₂ := Module.End.toContinuousLinearMap (𝕜 := ℂ) (ℋ₁ ⊗[ℂ] ℋ₂)
  induction Y using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero]
      exact twirl_left_zero
  | tmul A B =>
      rw [QuantumChannel.endomorphismTensorEquiv_symm_tmul]
      have htm : e₁₂ (TensorProduct.map A B) = tensorMap (e₁ A) (e₂ B) := by
        change e₁₂ (TensorProduct.map A B) =
          e₁₂ (TensorProduct.map (e₁.symm (e₁ A)) (e₂.symm (e₂ B)))
        rw [e₁.symm_apply_apply, e₂.symm_apply_apply]
      rw [htm]
      exact twirl_tensorMap_left (e₁ A) (e₂ B)
  | add Y₁ Y₂ hY₁ hY₂ =>
      rw [map_add, map_add]
      exact twirl_left_add hY₁ hY₂

omit [Nontrivial ℋ₂] in
/-- First-factor twirl equals the maximally mixed operator tensored with the partial trace.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
theorem twirl_eq_partialTrace_smul_id
    (X : (ℋ₁ ⊗[ℂ] ℋ₂) →L[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂)) :
    ∫ u : unitary (ℋ₁ →L[ℂ] ℋ₁),
      tensorMap (u : ℋ₁ →L[ℂ] ℋ₁) (1 : ℋ₂ →L[ℂ] ℋ₂) * X *
        tensorMap (star (u : ℋ₁ →L[ℂ] ℋ₁)) (1 : ℋ₂ →L[ℂ] ℋ₂)
    ∂(haarUnitary ℋ₁) =
    tensorMap ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ • (1 : ℋ₁ →L[ℂ] ℋ₁))
      (traceOutLeft X) := by
  simpa only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply] using
    twirl_left_endomorphismTensorEquiv (QuantumChannel.endomorphismTensorEquiv (ℋ₁ := ℋ₁)
      (ℋ₂ := ℋ₂) ((Module.End.toContinuousLinearMap (𝕜 := ℂ) (ℋ₁ ⊗[ℂ] ℋ₂)).symm X))

omit [Nontrivial ℋ₁] [Nontrivial ℋ₂] in
/-- Second-factor tensor conjugation is continuous. -/
lemma continuous_unitaryConj_tensor_right
    (X : B (ℋ₁ ⊗[ℂ] ℋ₂)) :
    Continuous (fun u : unitary (B ℋ₂) =>
      tensorMap (1 : B ℋ₁) (u : B ℋ₂) * X *
        tensorMap (1 : B ℋ₁) (star (u : B ℋ₂))) := by
  have hleft : Continuous (fun u : unitary (B ℋ₂) =>
      tensorMap (1 : B ℋ₁) (u : B ℋ₂)) :=
    (continuous_tensorMap_right (1 : B ℋ₁)).comp continuous_subtype_val
  have hright : Continuous (fun u : unitary (B ℋ₂) =>
      tensorMap (1 : B ℋ₁) (star (u : B ℋ₂))) :=
    (continuous_tensorMap_right (1 : B ℋ₁)).comp
      (continuous_star.comp continuous_subtype_val)
  exact (hleft.mul continuous_const).mul hright

omit [Nontrivial ℋ₁] in
/-- Second-factor tensor conjugation is Haar-integrable. -/
lemma integrable_unitaryConj_tensor_right
    (X : B (ℋ₁ ⊗[ℂ] ℋ₂)) :
    Integrable (fun u : unitary (B ℋ₂) =>
      tensorMap (1 : B ℋ₁) (u : B ℋ₂) * X *
        tensorMap (1 : B ℋ₁) (star (u : B ℋ₂)))
      (haarUnitary ℋ₂) :=
  (continuous_unitaryConj_tensor_right X).integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))

omit [Nontrivial ℋ₁] in
/-- Second-factor twirl of a product operator. -/
private lemma twirl_tensorMap_right (A : ℋ₁ →L[ℂ] ℋ₁) (B : ℋ₂ →L[ℂ] ℋ₂) :
    ∫ u : unitary (ℋ₂ →L[ℂ] ℋ₂),
      tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (u : ℋ₂ →L[ℂ] ℋ₂) * tensorMap A B *
        tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (star (u : ℋ₂ →L[ℂ] ℋ₂))
    ∂(haarUnitary ℋ₂) =
    tensorMap (traceOutRight (tensorMap A B))
      ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • (1 : ℋ₂ →L[ℂ] ℋ₂)) := by
  have hintegrand : ∀ u : unitary (ℋ₂ →L[ℂ] ℋ₂),
      tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (u : ℋ₂ →L[ℂ] ℋ₂) * tensorMap A B *
        tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (star (u : ℋ₂ →L[ℂ] ℋ₂)) =
      tensorMap A ((u : ℋ₂ →L[ℂ] ℋ₂) * B * star (u : ℋ₂ →L[ℂ] ℋ₂)) := by
    intro u
    rw [tensorMap_mul, tensorMap_mul]
    simp only [mul_one, one_mul]
  simp_rw [hintegrand]
  calc
    (∫ u : unitary (ℋ₂ →L[ℂ] ℋ₂),
        tensorMap A ((u : ℋ₂ →L[ℂ] ℋ₂) * B * star (u : ℋ₂ →L[ℂ] ℋ₂)) ∂(haarUnitary ℋ₂)) =
        tensorMapLeft A
          (∫ u : unitary (ℋ₂ →L[ℂ] ℋ₂),
            (u : ℋ₂ →L[ℂ] ℋ₂) * B * star (u : ℋ₂ →L[ℂ] ℋ₂) ∂(haarUnitary ℋ₂)) :=
      (tensorMapLeft A).integral_comp_comm (integrable_unitaryConj B)
    _ = tensorMap (traceOutRight (tensorMap A B))
          ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • (1 : ℋ₂ →L[ℂ] ℋ₂)) := by
      rw [twirl_eq_smul_one, traceOutRight_tensorMap]
      change tensorMap A
          (((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ * LinearMap.trace ℂ ℋ₂ (B : L ℋ₂)) •
            (1 : ℋ₂ →L[ℂ] ℋ₂)) =
        tensorMap (LinearMap.trace ℂ ℋ₂ (B : L ℋ₂) • A)
          ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • (1 : ℋ₂ →L[ℂ] ℋ₂))
      exact tensorMap_smul_swap _ _ _ _

omit [Nontrivial ℋ₁] in
/-- The second-factor twirl formula holds for `0`. -/
private lemma twirl_right_zero :
    ∫ u : unitary (ℋ₂ →L[ℂ] ℋ₂),
      tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (u : ℋ₂ →L[ℂ] ℋ₂) * (0 : B (ℋ₁ ⊗[ℂ] ℋ₂)) *
        tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (star (u : ℋ₂ →L[ℂ] ℋ₂))
    ∂(haarUnitary ℋ₂) =
    tensorMap (traceOutRight (0 : B (ℋ₁ ⊗[ℂ] ℋ₂)))
      ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • (1 : ℋ₂ →L[ℂ] ℋ₂)) := by
  simp [tensorMap, traceOutRight, TensorProduct.map_zero_left]

omit [Nontrivial ℋ₁] in
/-- The second-factor twirl formula is additive. -/
private lemma twirl_right_add {X Y : B (ℋ₁ ⊗[ℂ] ℋ₂)}
    (hX : ∫ u : unitary (ℋ₂ →L[ℂ] ℋ₂),
      tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (u : ℋ₂ →L[ℂ] ℋ₂) * X *
        tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (star (u : ℋ₂ →L[ℂ] ℋ₂))
    ∂(haarUnitary ℋ₂) =
      tensorMap (traceOutRight X)
      ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • (1 : ℋ₂ →L[ℂ] ℋ₂)))
    (hY : ∫ u : unitary (ℋ₂ →L[ℂ] ℋ₂),
      tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (u : ℋ₂ →L[ℂ] ℋ₂) * Y *
        tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (star (u : ℋ₂ →L[ℂ] ℋ₂))
    ∂(haarUnitary ℋ₂) =
      tensorMap (traceOutRight Y)
      ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • (1 : ℋ₂ →L[ℂ] ℋ₂))) :
    ∫ u : unitary (ℋ₂ →L[ℂ] ℋ₂),
      tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (u : ℋ₂ →L[ℂ] ℋ₂) * (X + Y) *
        tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (star (u : ℋ₂ →L[ℂ] ℋ₂))
    ∂(haarUnitary ℋ₂) =
    tensorMap (traceOutRight (X + Y))
      ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • (1 : ℋ₂ →L[ℂ] ℋ₂)) := by
  simp only [mul_add, add_mul]
  rw [integral_add (integrable_unitaryConj_tensor_right X)
    (integrable_unitaryConj_tensor_right Y), hX, hY, traceOutRight_add]
  exact (tensorMap_add_left (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂) _ _ _).symm

omit [Nontrivial ℋ₁] in
/-- Second-factor twirl formula on operators written through `endomorphismTensorEquiv`. -/
private lemma twirl_right_endomorphismTensorEquiv (Y : L ℋ₁ ⊗[ℂ] L ℋ₂) :
    ∫ u : unitary (ℋ₂ →L[ℂ] ℋ₂),
      tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (u : ℋ₂ →L[ℂ] ℋ₂) *
        (Module.End.toContinuousLinearMap (𝕜 := ℂ) (ℋ₁ ⊗[ℂ] ℋ₂)
          ((QuantumChannel.endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).symm Y)) *
        tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (star (u : ℋ₂ →L[ℂ] ℋ₂))
    ∂(haarUnitary ℋ₂) =
    tensorMap (traceOutRight (Module.End.toContinuousLinearMap (𝕜 := ℂ) (ℋ₁ ⊗[ℂ] ℋ₂)
          ((QuantumChannel.endomorphismTensorEquiv (ℋ₁ := ℋ₁) (ℋ₂ := ℋ₂)).symm Y)))
      ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • (1 : ℋ₂ →L[ℂ] ℋ₂)) := by
  let e₁ := Module.End.toContinuousLinearMap (𝕜 := ℂ) ℋ₁
  let e₂ := Module.End.toContinuousLinearMap (𝕜 := ℂ) ℋ₂
  let e₁₂ := Module.End.toContinuousLinearMap (𝕜 := ℂ) (ℋ₁ ⊗[ℂ] ℋ₂)
  induction Y using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero]
      exact twirl_right_zero
  | tmul A B =>
      rw [QuantumChannel.endomorphismTensorEquiv_symm_tmul]
      have htm : e₁₂ (TensorProduct.map A B) = tensorMap (e₁ A) (e₂ B) := by
        change e₁₂ (TensorProduct.map A B) =
          e₁₂ (TensorProduct.map (e₁.symm (e₁ A)) (e₂.symm (e₂ B)))
        rw [e₁.symm_apply_apply, e₂.symm_apply_apply]
      rw [htm]
      exact twirl_tensorMap_right (e₁ A) (e₂ B)
  | add Y₁ Y₂ hY₁ hY₂ =>
      rw [map_add, map_add]
      exact twirl_right_add hY₁ hY₂

omit [Nontrivial ℋ₁] in
/-- Second-factor twirl equals the partial trace tensored with the maximally mixed operator.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
theorem twirl_eq_partialTrace_right_smul_id
    (X : (ℋ₁ ⊗[ℂ] ℋ₂) →L[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂)) :
    ∫ u : unitary (ℋ₂ →L[ℂ] ℋ₂),
      tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (u : ℋ₂ →L[ℂ] ℋ₂) * X *
        tensorMap (1 : ℋ₁ →L[ℂ] ℋ₁) (star (u : ℋ₂ →L[ℂ] ℋ₂))
    ∂(haarUnitary ℋ₂) =
    tensorMap (traceOutRight X)
      ((Module.finrank ℂ ℋ₂ : ℂ)⁻¹ • (1 : ℋ₂ →L[ℂ] ℋ₂)) := by
  simpa only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply] using
    twirl_right_endomorphismTensorEquiv (QuantumChannel.endomorphismTensorEquiv (ℋ₁ := ℋ₁)
      (ℋ₂ := ℋ₂) ((Module.End.toContinuousLinearMap (𝕜 := ℂ) (ℋ₁ ⊗[ℂ] ℋ₂)).symm X))

end TensorTwirl

/-! ## Jensen inequalities for Bochner integrals of continuous endomorphisms -/

section Jensen

variable {ℋ : Type u} [Qudit ℋ]

/-- Jointly convex Jensen inequality for CLM-valued Bochner integrals.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
theorem jointly_convex_integral_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {S T : Set (B ℋ)} (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hSc : IsClosed S) (hTc : IsClosed T)
    {f : B ℋ → B ℋ → ℝ}
    (hf_conv : JointlyConvexOn S T f)
    (hf_cont : ContinuousOn (Function.uncurry f) (S ×ˢ T))
    {g₁ g₂ : α → B ℋ}
    (hg₁ : ∀ᵐ x ∂μ, g₁ x ∈ S)
    (hg₂ : ∀ᵐ x ∂μ, g₂ x ∈ T)
    (hg₁_int : Integrable g₁ μ) (hg₂_int : Integrable g₂ μ)
    (hfg_int : Integrable (fun x => f (g₁ x) (g₂ x)) μ) :
    f (∫ x, g₁ x ∂μ) (∫ x, g₂ x ∂μ) ≤ ∫ x, f (g₁ x) (g₂ x) ∂μ := by
  have hF : ConvexOn ℝ (S ×ˢ T) (Function.uncurry f) := by
    constructor
    · exact hS.prod hT
    · rintro ⟨a₁, b₁⟩ ⟨ha₁, hb₁⟩ ⟨a₂, b₂⟩ ⟨ha₂, hb₂⟩ c d hc hd hcd
      change f (c • a₁ + d • a₂) (c • b₁ + d • b₂) ≤
        c • f a₁ b₁ + d • f a₂ b₂
      have hcd' : c = 1 - d := by linarith
      rw [hcd']
      exact hf_conv ha₁ ha₂ hb₁ hb₂ hd (by linarith)
  have key := hF.map_integral_le hf_cont (hSc.prod hTc)
    (hg₁.mp (hg₂.mono fun x h₂ h₁ => ⟨h₁, h₂⟩))
    (hg₁_int.prodMk hg₂_int) hfg_int
  simp only [Function.uncurry_apply_pair, integral_pair hg₁_int hg₂_int] at key
  exact key

/-- Jointly concave Jensen inequality for CLM-valued Bochner integrals.

Source: arXiv:1306.5358v3, chapter-level reference (no numbered correspondence). -/
theorem jointly_concave_le_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {S T : Set (B ℋ)} (hS : Convex ℝ S) (hT : Convex ℝ T)
    (hSc : IsClosed S) (hTc : IsClosed T)
    {f : B ℋ → B ℋ → ℝ}
    (hf_conc : JointlyConcaveOn S T f)
    (hf_cont : ContinuousOn (Function.uncurry f) (S ×ˢ T))
    {g₁ g₂ : α → B ℋ}
    (hg₁ : ∀ᵐ x ∂μ, g₁ x ∈ S)
    (hg₂ : ∀ᵐ x ∂μ, g₂ x ∈ T)
    (hg₁_int : Integrable g₁ μ) (hg₂_int : Integrable g₂ μ)
    (hfg_int : Integrable (fun x => f (g₁ x) (g₂ x)) μ) :
    (∫ x, f (g₁ x) (g₂ x) ∂μ) ≤ f (∫ x, g₁ x ∂μ) (∫ x, g₂ x ∂μ) := by
  have hF : ConcaveOn ℝ (S ×ˢ T) (Function.uncurry f) := by
    constructor
    · exact hS.prod hT
    · rintro ⟨a₁, b₁⟩ ⟨ha₁, hb₁⟩ ⟨a₂, b₂⟩ ⟨ha₂, hb₂⟩ c d hc hd hcd
      change c • f a₁ b₁ + d • f a₂ b₂ ≤
        f (c • a₁ + d • a₂) (c • b₁ + d • b₂)
      have hcd' : c = 1 - d := by linarith
      rw [hcd']
      exact hf_conc ha₁ ha₂ hb₁ hb₂ hd (by linarith)
  have key := hF.le_map_integral hf_cont (hSc.prod hTc)
    (hg₁.mp (hg₂.mono fun x h₂ h₁ => ⟨h₁, h₂⟩))
    (hg₁_int.prodMk hg₂_int) hfg_int
  simp only [Function.uncurry_apply_pair, integral_pair hg₁_int hg₂_int] at key
  exact key

end Jensen

/-! ## Stinespring–Haar identity -/

section StinespringHaar

variable {ℋ₁ : Type u} {ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂]
variable [Nontrivial ℋ₁]

/-- Stinespring–Haar identity on the raw CLM carrier. -/
theorem stinespring_haar_eq
    (U : unitary (B (ℋ₁ ⊗[ℂ] ℋ₂)))
    (τ : B ℋ₁) (γ : B ℋ₂) :
    tensorMap ((Module.finrank ℂ ℋ₁ : ℂ)⁻¹ • (1 : B ℋ₁))
      (traceOutLeft
        ((U : B (ℋ₁ ⊗[ℂ] ℋ₂)) * tensorMap τ γ *
          star (U : B (ℋ₁ ⊗[ℂ] ℋ₂)))) =
    ∫ u : unitary (B ℋ₁),
      tensorMap (u : B ℋ₁) (1 : B ℋ₂) *
        ((U : B (ℋ₁ ⊗[ℂ] ℋ₂)) * tensorMap τ γ *
          star (U : B (ℋ₁ ⊗[ℂ] ℋ₂))) *
        tensorMap (star (u : B ℋ₁)) (1 : B ℋ₂)
    ∂(haarUnitary ℋ₁) := by
  exact (twirl_eq_partialTrace_smul_id
    ((U : B (ℋ₁ ⊗[ℂ] ℋ₂)) * tensorMap τ γ *
      star (U : B (ℋ₁ ⊗[ℂ] ℋ₂)))).symm

end StinespringHaar

end HaarUnitaryCLM
