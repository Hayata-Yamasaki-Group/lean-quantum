/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quantum.QuantumEntropy.RenyiDPI.Defs
import Quantum.QuantumEntropy.Common.OperatorCFC
import Quantum.QuantumEntropy.CFCTransport
import Quantum.QuantumEntropy.Common.TracePositiveDefinite
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

open scoped Quantum.TraceInequality.Loewner

/-! # Representation and continuity of the fixed Petz trace power

All public representation bridges state their domain explicitly. Continuity
uses positive exponents on the whole nonnegative cone, including its boundary.
-/

namespace RenyiDPI

open QuantumState QuantumEntropy SandwichedRenyiRelativeEntropy
open scoped QuantumEntropy ComplexOrder NNReal Topology

universe u
variable {H : Type u} [Qudit H] [Nontrivial H]

private local instance : ContinuousFunctionalCalculus ℂ (L H) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus
private local instance : ContinuousFunctionalCalculus ℝ (L H) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

omit [Nontrivial H] in
private lemma rpow_toCLM_of_nonneg {X : L H} (hX : 0 ≤ X) {p : ℝ} (hp : 0 < p) :
    (CFC.rpow X p).toContinuousLinearMap = CFC.rpow X.toContinuousLinearMap p := by
  -- The totalized transport lemma needs neither hypothesis; they stay in the statement.
  have _ := hX
  have _ := hp
  exact CFCTransport.cfc_rpow_toCLM X p

omit [Nontrivial H] in
/-- Transport the fixed CLM quantity to the linear-map CFC on its intended domain. -/
theorem petzTracePower_eq_trace_rpow_mul {α : ℝ} {ρ σ : L H}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    petzTracePower α ρ σ = (Tr (CFC.rpow ρ α * CFC.rpow σ (1 - α))).re := by
  unfold petzTracePower
  -- The transported powers agree with the ones in `petzTracePower` only after unfolding
  -- instances, so rewrite up to definitional unfolding.
  erw [← rpow_toCLM_of_nonneg hρ hα.1, ← rpow_toCLM_of_nonneg hσ (sub_pos.mpr hα.2)]
  rfl

omit [Nontrivial H] in
private lemma trace_sqrt_product {X Y : L H} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    Tr (star (CFC.sqrt X * CFC.sqrt Y) * (CFC.sqrt X * CFC.sqrt Y)) =
      Tr (X * Y) := by
  rw [star_mul, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg X)).star_eq,
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg Y)).star_eq]
  calc
    _ = Tr (CFC.sqrt Y * ((CFC.sqrt X * CFC.sqrt X) * CFC.sqrt Y)) := by
      simp only [mul_assoc]
    _ = Tr (CFC.sqrt Y * (X * CFC.sqrt Y)) := by rw [CFC.sqrt_mul_sqrt_self X hX]
    _ = Tr ((X * CFC.sqrt Y) * CFC.sqrt Y) := LinearMap.trace_mul_comm _ _ _
    _ = Tr (X * Y) := by rw [mul_assoc, CFC.sqrt_mul_sqrt_self Y hY]

omit [Nontrivial H] in
/-- The trace of the product of two nonnegative powers is real and nonnegative. -/
theorem trace_rpow_mul_nonneg (α : ℝ) (ρ σ : L H) :
    (0 : ℂ) ≤ Tr (CFC.rpow ρ α * CFC.rpow σ (1 - α)) := by
  rw [← trace_sqrt_product (X := CFC.rpow ρ α) (Y := CFC.rpow σ (1 - α))
    CFC.rpow_nonneg CFC.rpow_nonneg]
  exact ((LinearMap.nonneg_iff_isPositive _).mp (star_mul_self_nonneg _)).trace_nonneg

omit [Nontrivial H] in
/-- Nonnegativity of the fixed trace power, including singular inputs. -/
theorem petzTracePower_nonneg {α : ℝ} {ρ σ : L H}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    0 ≤ petzTracePower α ρ σ := by
  rw [petzTracePower_eq_trace_rpow_mul hα hρ hσ]
  exact (Complex.nonneg_iff.mp (trace_rpow_mul_nonneg α ρ σ)).1

/-- Strict positivity on positive-definite pairs. -/
theorem petzTracePower_pos_of_posDef {α : ℝ} {ρ σ : L H}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hρ : ρ ∈ pdSetLM (ℋ := H)) (hσ : σ ∈ pdSetLM (ℋ := H)) :
    0 < petzTracePower α ρ σ := by
  rw [petzTracePower_eq_trace_rpow_mul hα (nonneg_of_pdSetLM hρ) (nonneg_of_pdSetLM hσ)]
  let X := CFC.rpow ρ α
  let Y := CFC.rpow σ (1 - α)
  have hX : IsUnit X := ((pdSetLM_strictPositivity_certificate ρ).mp hρ).rpow.isUnit
  have hY : IsUnit Y := ((pdSetLM_strictPositivity_certificate σ).mp hσ).rpow.isUnit
  have hZ : CFC.sqrt X * CFC.sqrt Y ≠ 0 := by
    intro hz
    apply (hX.mul hY).ne_zero
    calc
      X * Y = (CFC.sqrt X * CFC.sqrt X) * (CFC.sqrt Y * CFC.sqrt Y) := by
        rw [CFC.sqrt_mul_sqrt_self X CFC.rpow_nonneg,
          CFC.sqrt_mul_sqrt_self Y CFC.rpow_nonneg]
      _ = CFC.sqrt X * (CFC.sqrt X * CFC.sqrt Y) * CFC.sqrt Y := by
        simp only [mul_assoc]
      _ = 0 := by rw [hz]; simp
  have hZZ := (not_congr (CStarRing.star_mul_self_eq_zero_iff _)).mpr hZ
  have ht := QuantumEntropy.trace_re_pos_of_ne_zero (star_mul_self_nonneg _) hZZ
  rwa [trace_sqrt_product (X := X) (Y := Y) CFC.rpow_nonneg CFC.rpow_nonneg] at ht

/-- The extended quantity agrees with the real divergence on positive-definite pairs. -/
theorem petzDivNN_eq_coe_of_posDef {α : ℝ} {ρ σ : L H}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hρ : ρ ∈ pdSetLM (ℋ := H)) (hσ : σ ∈ pdSetLM (ℋ := H)) :
    petzDivNN α ρ σ = (petzDiv α ρ σ : EReal) := by
  have hQ := petzTracePower_pos_of_posDef hα hρ hσ
  have hTr := trace_re_pos_of_pdSetLM hρ
  simp [petzDivNN, ne_of_gt hQ]

omit [Nontrivial H] in
private lemma rpow_continuousOn_cone {p : ℝ} (hp : 0 ≤ p) :
    ContinuousOn (fun X : L H => CFC.rpow X p) {X : L H | 0 ≤ X} := by
  exact continuousOn_id.cfc_nnreal_of_mem_nhdsSet
    (s := Set.univ) (f := (· ^ p)) Filter.univ_mem
    (ha' := fun _ hX => hX) (hf := NNReal.continuousOn_rpow_const (.inr hp))

omit [Nontrivial H] in
/-- Continuity along arbitrary nonnegative paths; both exponents are positive. -/
theorem tendsto_petzTracePower_nonneg {ι : Type*} {f : Filter ι}
    {a b : ι → L H} {ρ σ : L H} {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (ha : Filter.Tendsto a f (𝓝 ρ)) (hb : Filter.Tendsto b f (𝓝 σ))
    (ha0 : ∀ᶠ i in f, 0 ≤ a i) (hb0 : ∀ᶠ i in f, 0 ≤ b i) :
    Filter.Tendsto (fun i => petzTracePower α (a i) (b i)) f
      (𝓝 (petzTracePower α ρ σ)) := by
  have ha' := (rpow_continuousOn_cone hα.1.le ρ hρ).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨ha, ha0⟩)
  have hb' := (rpow_continuousOn_cone (sub_pos.mpr hα.2).le σ hσ).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hb, hb0⟩)
  have ht : Continuous (fun X : L H => (Tr X).re) := by fun_prop
  rw [petzTracePower_eq_trace_rpow_mul hα hρ hσ]
  refine ((ht.tendsto _).comp (ha'.mul hb')).congr' ?_
  filter_upwards [ha0, hb0] with i hai hbi
  exact (petzTracePower_eq_trace_rpow_mul hα hai hbi).symm

end RenyiDPI
