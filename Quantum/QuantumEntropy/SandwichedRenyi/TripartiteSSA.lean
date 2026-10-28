import Quantum.QuantumEntropy.SandwichedRenyi.NonNeg.Dispatcher.GSLCore
import Quantum.QuantumEntropy.VonNeumann.SSA
import Quantum.QuantumEntropy.UmegakiDPI.ViaPetz.FromRenyi.GSLCore


/-!
# Tripartite sandwiched Rényi data processing

Source: arXiv:2607.05492v1, main.tex:204–218, Eq. intro-generalized-ssa.
Original DPI: R. L. Frank and E. H. Lieb, “Monotonicity of a relative Rényi
entropy”, Journal of Mathematical Physics 54, 122201 (2013), Theorem 1.

We use the carrier A ⊗ (B ⊗ C). The reference (ρ_AB ⊗ τ_C) is transported
through the tensor associator. Here ρ_AB = Tr_C ρ, ρ_BC = Tr_A ρ, and
ρ_B = Tr_A ρ_AB. The NN theorem holds for every positive semidefinite ρ,
so in particular for every density operator. Its codomain is EReal.
-/

open QuantumState QuantumChannel VonNeumann TensorProduct
open GeneralizedPerspectiveFunction
open scoped ComplexOrder

namespace SandwichedRenyiRelativeEntropy

universe u
variable {A B C : Type u} [Qudit A] [Qudit B] [Qudit C]

/-- The reference X_AB ⊗ Y_C, represented on A ⊗ (B ⊗ C).
Source: main.tex:209; tensor associativity bookkeeping for Frank–Lieb (2013), Thm. 1. -/
noncomputable def tripartiteReference (X : L (A ⊗[ℂ] B)) (Y : L C) :
    L (A ⊗[ℂ] (B ⊗[ℂ] C)) :=
  conjugateEnd (TensorProduct.assoc ℂ A B C) (TensorProduct.map X Y)

/-- Tracing out A commutes with tensoring the reference by Y_C.
An auxiliary identity (partial trace / tensor-association bookkeeping) used in the proof
of the tripartite SSA; not itself a theorem of the paper.
Source context: main.tex:204–218. -/
theorem traceOutLeft_tripartiteReference (X : L (A ⊗[ℂ] B)) (Y : L C) :
    traceOutLeft (tripartiteReference X Y) = TensorProduct.map (traceOutLeft X) Y := by
  obtain ⟨W, rfl⟩ := (endomorphismTensorEquiv (ℋ₁ := A) (ℋ₂ := B)).symm.surjective X
  induction W using TensorProduct.induction_on with
  | zero => simp [tripartiteReference]
  | tmul P Q =>
    rw [endomorphismTensorEquiv_symm_tmul]
    have hassoc : tripartiteReference (TensorProduct.map P Q) Y =
        TensorProduct.map P (TensorProduct.map Q Y) := by
      apply TensorProduct.ext'
      intro a bc
      induction bc using TensorProduct.induction_on with
      | zero => simp
      | tmul b c => rfl
      | add b c hb hc =>
        simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hb hc
    rw [hassoc, traceOutLeft_map, traceOutLeft_map, TensorProduct.map_smul_left]
  | add U V hU hV =>
    simp only [map_add, TensorProduct.map_add_left, tripartiteReference] at hU hV ⊢
    rw [hU, hV]


/-- The two orders of tracing out A and C give the same middle marginal.
Source: main.tex:213–215; marginal bookkeeping for Frank–Lieb (2013), Thm. 1. -/
theorem tripartite_middle_marginal (Z : L (A ⊗[ℂ] (B ⊗[ℂ] C))) :
    QuantumChannel.traceOutLeft (traceOutThird Z) =
      QuantumChannel.traceOutRight (ℋ₂ := B) (ℋ₃ := C)
        (QuantumChannel.traceOutLeft Z) := by
  have conjugateEnd_assoc_symm_map (P : L A) (R : L B) (S : L C) :
      conjugateEnd (TensorProduct.assoc ℂ A B C).symm
        (TensorProduct.map P (TensorProduct.map R S)) =
        TensorProduct.map (TensorProduct.map P R) S := by
    apply TensorProduct.ext'
    intro xy z
    induction xy using TensorProduct.induction_on with
    | zero => simp [conjugateEnd]
    | tmul x y => simp [conjugateEnd]
    | add a b ha hb =>
        simp only [add_tmul, map_add] at ha hb ⊢
        rw [ha, hb]
  have traceOutThird_map (P : L A) (Q : L (B ⊗[ℂ] C)) :
      traceOutThird (TensorProduct.map P Q) =
        TensorProduct.map P
          (QuantumChannel.traceOutRight (ℋ₂ := B) (ℋ₃ := C) Q) := by
    obtain ⟨W, rfl⟩ :=
      (endomorphismTensorEquiv (ℋ₁ := B) (ℋ₂ := C)).symm.surjective Q
    induction W using TensorProduct.induction_on with
    | zero =>
        simp only [map_zero, TensorProduct.map_zero_right]
    | tmul R S =>
        rw [endomorphismTensorEquiv_symm_tmul]
        unfold QuantumChannel.traceOutThird
        rw [LinearMap.comp_apply, conjugateEnd_assoc_symm_map,
          traceOutRight_map, traceOutRight_map, TensorProduct.map_smul_right]
    | add W₁ W₂ h₁ h₂ =>
        rw [map_add, TensorProduct.map_add_right, map_add, h₁, h₂, map_add,
          TensorProduct.map_add_right]
  obtain ⟨W, rfl⟩ :=
    (endomorphismTensorEquiv (ℋ₁ := A) (ℋ₂ := B ⊗[ℂ] C)).symm.surjective Z
  induction W using TensorProduct.induction_on with
  | zero => simp
  | tmul P Q =>
      rw [endomorphismTensorEquiv_symm_tmul, traceOutThird_map, traceOutLeft_map,
        traceOutLeft_map, map_smul]
  | add W₁ W₂ h₁ h₂ =>
      simp only [map_add]
      rw [h₁, h₂]

variable [Nontrivial A] [Nontrivial B] [Nontrivial C]

/-- The SSA-type Rényi inequality for every nonnegative tripartite operator.
Source: main.tex:204–218, Eq. intro-generalized-ssa; Frank–Lieb (2013), Thm. 1.
The density condition Tr ρ = 1 is unnecessary for this stronger NN statement. -/
theorem sandwichedRenyiDivNN_tripartiteSSA {α : ℝ} (hα : (1 : ℝ) / 2 ≤ α) (hα1 : α ≠ 1)
    (ρ : L (A ⊗[ℂ] (B ⊗[ℂ] C))) (hρ : 0 ≤ ρ) :
    let τ : L C := (((Module.finrank ℂ C : ℝ)⁻¹ : ℝ) : ℂ) • 1
    sandwichedRenyiDivNN α (traceOutLeft ρ)
      (TensorProduct.map (traceOutRight (traceOutLeft ρ)) τ) ≤
      sandwichedRenyiDivNN α ρ (tripartiteReference (traceOutThird ρ) τ) := by
  intro τ
  have hτ : 0 ≤ τ := smul_nonneg (by positivity) zero_le_one
  have hAB : 0 ≤ traceOutThird ρ :=
    map_nonneg (CPTP.traceOutThird A B C).toCompletelyPositiveMap hρ
  have hXY : 0 ≤ TensorProduct.map (traceOutThird ρ) τ := by
    simpa [TensorCFC.tensorMapLeftₗ] using
      TensorCFC.tensorProduct_map_le_map_left τ hτ hAB
  have hσ : 0 ≤ tripartiteReference (traceOutThird ρ) τ := by
    have hc := isPositiveMap_conjugate (TensorProduct.assocIsometry ℂ A B C).toLinearMap
      (TensorProduct.map (traceOutThird ρ) τ) hXY
    simpa only [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm] using hc
  have h := RenyiDPI.sandwichedRenyiDivNN_monotone (CPTP.traceOutLeft A (B ⊗[ℂ] C)) hα hα1 hρ hσ
  simpa only [CPTP.traceOutLeft_toFun, traceOutLeft_tripartiteReference,
    tripartite_middle_marginal] using h

/-- The real-valued SSA-type inequality on its finite, nonzero domain.
Source: main.tex:204–218; Frank–Lieb (2013), Theorem 1, finite branch.
The trace hypotheses state the mathematical domain of the logarithmic formula;
the comparison itself needs only support inclusion and the two nonzero Q values. -/
theorem sandwichedRenyiDiv_tripartiteSSA {α : ℝ}
    (hα : (1 : ℝ) / 2 ≤ α) (hα1 : α ≠ 1)
    (ρ : L (A ⊗[ℂ] (B ⊗[ℂ] C))) (hρ : 0 ≤ ρ)
    (hσ : tripartiteReference (traceOutThird ρ)
      ((((Module.finrank ℂ C : ℝ)⁻¹ : ℝ) : ℂ) • (1 : L C)) ∈ pdSetLM)
    (hQ : (sandwichedQuasi α ρ (tripartiteReference (traceOutThird ρ)
      ((((Module.finrank ℂ C : ℝ)⁻¹ : ℝ) : ℂ) • (1 : L C)))).re ≠ 0)
    (hQBC : (sandwichedQuasi α (traceOutLeft ρ)
      (TensorProduct.map (traceOutRight (traceOutLeft ρ))
        ((((Module.finrank ℂ C : ℝ)⁻¹ : ℝ) : ℂ) • (1 : L C)))).re ≠ 0)
    (_hTr : (Tr ρ).re ≠ 0) (_hTrBC : (Tr (traceOutLeft ρ)).re ≠ 0) :
    let τ : L C := (((Module.finrank ℂ C : ℝ)⁻¹ : ℝ) : ℂ) • 1
    sandwichedRenyiDiv α (traceOutLeft ρ)
      (TensorProduct.map (traceOutRight (traceOutLeft ρ)) τ) ≤
      sandwichedRenyiDiv α ρ (tripartiteReference (traceOutThird ρ) τ) := by
  intro τ
  have hsupp := suppLE_of_pdSetLM_right ρ hσ
  have hEsupp := supportLE_map_of_cptp (CPTP.traceOutLeft A (B ⊗[ℂ] C))
    hρ (nonneg_of_pdSetLM hσ) hsupp
  simp only [CPTP.traceOutLeft_toFun, traceOutLeft_tripartiteReference,
    tripartite_middle_marginal] at hEsupp
  have h := sandwichedRenyiDivNN_tripartiteSSA hα hα1 ρ hρ
  dsimp only at h
  simpa only [sandwichedRenyiDivNN, hsupp, hEsupp, hQ, hQBC,
    not_true_eq_false, and_false, or_self, ↓reduceIte, EReal.coe_le_coe_iff] using h

end SandwichedRenyiRelativeEntropy
