import Quantum.QuantumMechanics.Channel.Representations
import Quantum.TraceInequality.LownerHeinz.Defs
import Quantum.TraceInequality.LiebAndo.LownerHeinz.Defs
import Quantum.TraceInequality.TraceFunctionMonotonicity.LownerHeinz.Defs
import Quantum.TraceInequality.LownerHeinz.DefsRetained
import Quantum.TraceInequality.LiebAndo.JensenOperatorInequalityIImpIV
import Quantum.TraceInequality.JensenOperatorInequalityIImpIVRetained
import Quantum.TraceInequality.LiebTrace.Bridge
import Quantum.TraceInequality.LiebAndo.LiebTrace.Bridge
import Quantum.TraceInequality.LiebAndo.AndoConvexity.LiebTrace.Bridge
import Quantum.QuantumEntropy.SandwichedRenyiBase.NonNeg.Defs
import Quantum.QuantumEntropy.VonNeumann.Basic
import Quantum.QuantumEntropy.VonNeumann.PartialTraceThirdCPTP
import Quantum.QuantumEntropy.UmegakiDPI.AlphaOneCore

/-!
# Paper 1 comparator challenge

The statements below freeze the main theorem surface presented in Sections 2--4
of arXiv:2607.05492v1.  Direct imports are restricted to definition/vocabulary
or pre-provider modules; the current provider modules are imported only by
`Paper1Solution.lean`.
-/

/-! Definition-only vocabulary for the tripartite statements. The reference map
and tensor instance have the same names, types, and bodies as the provider-side
vocabulary. The third-factor trace is imported from its vocabulary owner. -/

namespace VonNeumann
open QuantumState TensorProduct
universe u v

instance instNontrivialTensorProduct
    {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
    [Nontrivial ℋ₁] [Nontrivial ℋ₂] : Nontrivial (ℋ₁ ⊗[ℂ] ℋ₂) :=
  Module.nontrivial_of_finrank_pos (R := ℂ) (by
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos)

end VonNeumann

namespace SandwichedRenyiRelativeEntropy
open QuantumState QuantumChannel TensorProduct
universe u
variable {A B C : Type u} [Qudit A] [Qudit B] [Qudit C]

noncomputable def tripartiteReference (X : L (A ⊗[ℂ] B)) (Y : L C) :
    L (A ⊗[ℂ] (B ⊗[ℂ] C)) :=
  conjugateEnd (TensorProduct.assoc ℂ A B C) (TensorProduct.map X Y)

end SandwichedRenyiRelativeEntropy

namespace ComparatorChallenges.Paper1

open QuantumState
open TensorProduct
open scoped ComplexOrder MatrixOrder Topology

universe u v w

/-! ## Section 2: complete-positivity representations -/

/-- Complete positivity iff positivity of the input-space tensor amplification. -/
theorem cp_iff_tensor
    {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
    {κ : Type w}
    (_b : Module.Basis κ ℂ ℋ₁) (Φ : QuantumChannel.T ℋ₁ ℋ₂) :
    QuantumChannel.IsCompletelyPositive Φ ↔
      QuantumChannel.AmplificationPositive Φ := by
  sorry

/-- Complete positivity iff positivity of the Choi operator. -/
theorem cp_iff_choi
    {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
    {κ : Type w} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis κ ℂ ℋ₁) (Φ : QuantumChannel.T ℋ₁ ℋ₂) :
    QuantumChannel.IsCompletelyPositive Φ ↔
      QuantumChannel.ChoiPositive b Φ := by
  sorry

/-- Complete positivity iff existence of a finite Kraus representation. -/
theorem cp_iff_kraus
    {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
    {κ : Type w}
    (_b : Module.Basis κ ℂ ℋ₁) (Φ : QuantumChannel.T ℋ₁ ℋ₂) :
    QuantumChannel.IsCompletelyPositive Φ ↔ QuantumChannel.HasKraus Φ := by
  sorry

/-- Complete positivity iff existence of a Choi-rank Kraus representation. -/
theorem cp_iff_rank_kraus
    {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
    {κ : Type w} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis κ ℂ ℋ₁) (Φ : QuantumChannel.T ℋ₁ ℋ₂) :
    QuantumChannel.IsCompletelyPositive Φ ↔
      QuantumChannel.HasRankKraus b Φ := by
  sorry

/-- Complete positivity iff existence of a finite-dimensional Stinespring representation. -/
theorem cp_iff_stinespring
    {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
    {κ : Type w}
    (_b : Module.Basis κ ℂ ℋ₁) (Φ : QuantumChannel.T ℋ₁ ℋ₂) :
    QuantumChannel.IsCompletelyPositive Φ ↔
      ∃ (ℋ₃ : Type u) (_ : Qudit ℋ₃),
        ∃ A : ℋ₁ →ₗ[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃),
          ∀ X : L ℋ₁,
            Φ X =
              (@QuantumChannel.traceOutRight ℋ₂ inferInstance ℋ₃ inferInstance
                (((A.comp X).comp
                  (LinearMap.adjoint A : (ℋ₂ ⊗[ℂ] ℋ₃) →ₗ[ℂ] ℋ₁)) :
                    L (ℋ₂ ⊗[ℂ] ℋ₃)) : L ℋ₂) := by
  sorry

/-- Complete positivity iff existence of a minimal Choi-rank Stinespring representation. -/
theorem cp_iff_rank_stinespring
    {ℋ₁ : Type u} {ℋ₂ : Type v} [Qudit ℋ₁] [Qudit ℋ₂]
    {κ : Type w} [DecidableEq κ] [Fintype κ]
    (b : Module.Basis κ ℂ ℋ₁) (Φ : QuantumChannel.T ℋ₁ ℋ₂) :
    QuantumChannel.IsCompletelyPositive Φ ↔
      ∃ (ℋ₃ : Type u) (inst : Qudit ℋ₃),
        Module.finrank ℂ ℋ₃ = QuantumChannel.choiRank b Φ ∧
          ∃ A : ℋ₁ →ₗ[ℂ] (ℋ₂ ⊗[ℂ] ℋ₃),
            ∀ X : L ℋ₁,
              Φ X =
                (@QuantumChannel.traceOutRight ℋ₂ inferInstance ℋ₃ inst
                  (((A.comp X).comp
                    (LinearMap.adjoint A : (ℋ₂ ⊗[ℂ] ℋ₃) →ₗ[ℂ] ℋ₁)) :
                      L (ℋ₂ ⊗[ℂ] ℋ₃)) : L ℋ₂) := by
  sorry

/-! ## Section 3: operator powers, Jensen, perspectives, and Lieb--Ando -/

/-- Löwner--Heinz monotonicity for powers in `[0, 1]`. -/
theorem power_Icc_zero_one_operatorMonotoneOn_Ici
    {𝓐 : Type u} [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
    [NonnegSpectrumClass ℝ 𝓐] (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    LownerHeinzCore.OperatorMonotoneOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ))
      (fun x ↦ x ^ p) := by
  sorry

/-- Operator concavity for powers in `[0, 1]`. -/
theorem power_Icc_zero_one_operatorConcaveOn_Ici
    {𝓐 : Type u} [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
    [Nontrivial 𝓐] [NonnegSpectrumClass ℝ 𝓐]
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    LownerHeinzCore.OperatorConcaveOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ))
      (fun x ↦ x ^ p) := by
  sorry

/-- Operator convexity for powers in `[1, 2]`. -/
theorem power_Icc_one_two_operatorConvexOn_Ici
    {𝓐 : Type u} [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
    [Nontrivial 𝓐] [NonnegSpectrumClass ℝ 𝓐]
    (p : ℝ) (hp : p ∈ Set.Icc (1 : ℝ) 2) :
    LownerHeinzCore.OperatorConvexOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ))
      (fun x ↦ x ^ p) := by
  sorry

/-- Operator monotonicity of `x ↦ -(x^p)` for `p ∈ [-1, 0]`. -/
theorem power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi
    {𝓐 : Type u} [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
    [NonnegSpectrumClass ℝ 𝓐]
    (p : ℝ) (hp : p ∈ Set.Icc (-1 : ℝ) 0) :
    LownerHeinzCore.OperatorMonotoneOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ))
      (fun x ↦ -(x ^ p)) := by
  sorry

/-- Operator concavity of `x ↦ -(x^p)` for `p ∈ [-1, 0]`. -/
theorem power_Icc_neg_one_zero_neg_operatorConcaveOn_Ioi
    {𝓐 : Type u} [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
    [Nontrivial 𝓐] [NonnegSpectrumClass ℝ 𝓐]
    (p : ℝ) (hp : p ∈ Set.Icc (-1 : ℝ) 0) :
    LownerHeinzCore.OperatorConcaveOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ))
      (fun x ↦ -(x ^ p)) := by
  sorry

/-- Hansen--Pedersen two-operator Jensen inequality on `[0, ∞)`. -/
theorem theorem_2_5_2_i_all_imp_v_Ici
    {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] [Nontrivial ℋ] {f : ℝ → ℝ}
    (hf : JensenOperatorInequality.OperatorConvexIciAllContNonposAtZero.{u} f) :
    JensenOperatorInequality.JensenContractiveColumnCondition (ℋ := ℋ) f := by
  sorry

/-- Joint convexity of generalized perspectives on the PSD/PD domain,
with localized hypotheses on `f`. -/
theorem theorem_2_5_forward_jointlyConvexOn_psd_pd_Ici
    {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] [Nontrivial ℋ] {f h : ℝ → ℝ}
    (hf : JensenOperatorInequality.OperatorConvexIciAllContNonposAtZero.{u} f)
    (hconc : LownerHeinzTheorem.OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) h)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    GeneralizedPerspectiveFunction.JointlyConvexOn
      (GeneralizedPerspectiveFunction.psdSet (ℋ := ℋ))
      (GeneralizedPerspectiveFunction.pdSet (ℋ := ℋ))
      (fun A B => GeneralizedPerspectiveFunction.generalizedPerspective f h A B) := by
  sorry

/-- Joint concavity of generalized perspectives on the PSD/PD domain,
with localized hypotheses on `f`. -/
theorem theorem_2_6_forward_jointlyConcaveOn_psd_pd_Ici
    {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] [Nontrivial ℋ] {f h : ℝ → ℝ}
    (hfconc :
      LownerHeinzTheorem.OperatorConcaveOnAll.{u} (Set.Ici (0 : ℝ)) f)
    (hfcont : ContinuousOn f (Set.Ici (0 : ℝ)))
    (hf0 : 0 ≤ f 0)
    (hconc : LownerHeinzTheorem.OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) h)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    GeneralizedPerspectiveFunction.JointlyConcaveOn
      (GeneralizedPerspectiveFunction.psdSet (ℋ := ℋ))
      (GeneralizedPerspectiveFunction.pdSet (ℋ := ℋ))
      (fun A B => GeneralizedPerspectiveFunction.generalizedPerspective f h A B) := by
  sorry

/-- Lieb joint concavity on the positive-definite cone. -/
theorem liebTrace_jointlyConcaveOn_pdSet
    {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] [FiniteDimensional ℂ ℋ] [Nontrivial ℋ]
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (K : ℋ →L[ℂ] ℋ) :
    GeneralizedPerspectiveFunction.JointlyConcaveOn
      (GeneralizedPerspectiveFunction.pdSet (ℋ := ℋ))
      (GeneralizedPerspectiveFunction.pdSet (ℋ := ℋ))
      (LiebAndoTrace.liebTraceMap (ℋ := ℋ) s K) := by
  sorry

/-- Lieb joint convexity on the positive-definite cone. -/
theorem liebTrace_jointlyConvexOn_pdSet
    {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] [FiniteDimensional ℂ ℋ] [Nontrivial ℋ]
    {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (K : ℋ →L[ℂ] ℋ) :
    GeneralizedPerspectiveFunction.JointlyConvexOn
      (GeneralizedPerspectiveFunction.pdSet (ℋ := ℋ))
      (GeneralizedPerspectiveFunction.pdSet (ℋ := ℋ))
      (LiebAndoTrace.liebTraceMap (ℋ := ℋ) s K) := by
  sorry

/-- Ando joint convexity on the positive-definite cone. -/
theorem andoTrace_jointlyConvexOn_pdSet
    {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] [FiniteDimensional ℂ ℋ] [Nontrivial ℋ]
    {q r : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hqr : 1 ≤ q - r)
    (K : ℋ →L[ℂ] ℋ) :
    GeneralizedPerspectiveFunction.JointlyConvexOn
      (GeneralizedPerspectiveFunction.pdSet (ℋ := ℋ))
      (GeneralizedPerspectiveFunction.pdSet (ℋ := ℋ))
      (LiebAndoTrace.andoTraceMap (ℋ := ℋ) q r K) := by
  sorry

/-! ## Section 4: sandwiched Renyi data processing -/

/-- Positive-definite data processing for the sandwiched Renyi divergence. -/
theorem sandwichedRenyiDiv_monotone
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {𝒦 : Type u} [Qudit 𝒦] [Nontrivial 𝒦]
    (E : QuantumChannel.CPTP ℋ 𝒦)
    {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ}
    (hρ : ρ ∈ SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ))
    (hσ : σ ∈ SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := ℋ))
    (hEρ : E.toFun ρ ∈ SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := 𝒦))
    (hEσ : E.toFun σ ∈ SandwichedRenyiRelativeEntropy.pdSetLM (ℋ := 𝒦)) :
    SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) ≤
      SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv α ρ σ := by
  sorry

/-- Extended-real data processing for non-negative inputs. -/
theorem sandwichedRenyiDivNN_monotone
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ]
    [Qudit 𝒦] [Nontrivial 𝒦]
    (E : QuantumChannel.CPTP ℋ 𝒦) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN α (E.toFun ρ) (E.toFun σ) ≤
      SandwichedRenyiRelativeEntropy.sandwichedRenyiDivNN α ρ σ := by
  sorry

/-! ## Further paper statements and diagnostic results -/

section
open QuantumChannel VonNeumann

theorem strongSubadditivity_of_state
    {ℋA ℋB ℋC : Type u} [Qudit ℋA] [Qudit ℋB] [Qudit ℋC]
    [Nontrivial ℋA] [Nontrivial ℋB] [Nontrivial ℋC]
    (ρ : L (ℋA ⊗[ℂ] (ℋB ⊗[ℂ] ℋC)))
    (hρ : 0 ≤ ρ)
    (hTr : Tr ρ = 1) :
    vonNeumannEntropy ρ +
        vonNeumannEntropy
          (QuantumChannel.traceOutRight (QuantumChannel.traceOutLeft ρ)) ≤
      vonNeumannEntropy (QuantumChannel.traceOutThird ρ) +
        vonNeumannEntropy (QuantumChannel.traceOutLeft ρ) := by
  sorry

end

section
open QuantumChannel SandwichedRenyiRelativeEntropy

theorem sandwichedRenyiDiv_tendsto_umegaki
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {ρ σ : L ℋ} (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    Filter.Tendsto (fun α => sandwichedRenyiDiv α ρ σ) (𝓝[>] (1 : ℝ))
      (𝓝 (umegakiNorm ρ σ)) := by
  sorry

end

section
open QuantumChannel SandwichedRenyiRelativeEntropy

theorem sandwichedRenyi_tendsto_umegaki_of_pd
    {H : Type u} [Qudit H] [Nontrivial H] {ρ σ : L H} (hρ : ρ ∈ pdSetLM) (hσ : σ ∈ pdSetLM) :
    Filter.Tendsto (fun α => sandwichedRenyiDiv α ρ σ) (𝓝[≠] (1 : ℝ))
      (𝓝 (umegakiNorm ρ σ)) := by
  sorry

end

section
open QuantumChannel SandwichedRenyiRelativeEntropy

theorem sandwichedRenyiDivNN_tripartiteSSA
    {A B C : Type u} [Qudit A] [Qudit B] [Qudit C]
    [Nontrivial A] [Nontrivial B] [Nontrivial C] {α : ℝ} (hα : (1 : ℝ) / 2 ≤ α) (hα1 : α ≠ 1)
    (ρ : L (A ⊗[ℂ] (B ⊗[ℂ] C))) (hρ : 0 ≤ ρ) :
    let τ : L C := (((Module.finrank ℂ C : ℝ)⁻¹ : ℝ) : ℂ) • 1
    sandwichedRenyiDivNN α (traceOutLeft ρ)
      (TensorProduct.map (traceOutRight (traceOutLeft ρ)) τ) ≤
      sandwichedRenyiDivNN α ρ (tripartiteReference (traceOutThird ρ) τ) := by
  sorry

end

section
open QuantumChannel SandwichedRenyiRelativeEntropy

theorem sandwichedRenyiDiv_tripartiteSSA
    {A B C : Type u} [Qudit A] [Qudit B] [Qudit C]
    [Nontrivial A] [Nontrivial B] [Nontrivial C] {α : ℝ}
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
  sorry

end

section
open QuantumChannel LownerHeinzCore

theorem OperatorConvex_eq_zero_of_nontrivial
    {𝓐 : Type u} [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
    [Nontrivial 𝓐] {f : ℝ → ℝ}
    (hf : OperatorConvex (𝓐 := 𝓐) f) : ∀ x, f x = 0 := by
  sorry

end

section
open QuantumChannel LownerHeinzCore

theorem OperatorConcave_eq_zero_of_nontrivial
    {𝓐 : Type u} [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐]
    {f : ℝ → ℝ} (hf : OperatorConcave (𝓐 := 𝓐) f) : ∀ x, f x = 0 := by
  sorry

end

section
open QuantumChannel LownerHeinzTheorem

theorem OperatorConvexAll_eq_zero {f : ℝ → ℝ} (hf : OperatorConvexAll.{u} f) : f = 0 := by
  sorry

end

section
open QuantumChannel LownerHeinzTheorem

theorem OperatorConcaveAll_eq_zero {f : ℝ → ℝ} (hf : OperatorConcaveAll.{u} f) : f = 0 := by
  sorry

end

section
open QuantumChannel LownerHeinzTheorem

theorem operatorConvexOnAll_Ici_sq :
    OperatorConvexOnAll.{u} (Set.Ici 0) (fun x : ℝ ↦ x ^ (2 : ℕ)) := by
  sorry

end

section
open QuantumChannel JensenOperatorInequality LownerHeinzTheorem

theorem jensenFinite_of_opConvexIciAll
    {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] [Nontrivial ℋ] {ι : Type v} [Fintype ι]
    {f : ℝ → ℝ} (hf : OperatorConvexIciAllContNonposAtZero.{u} f)
    (A X : ι → ℋ →L[ℂ] ℋ)
    (hA : ∀ i, IsSelfAdjoint (A i))
    (hAs : ∀ i, spectrum ℝ (A i) ⊆ Set.Ici (0 : ℝ))
    (hX : ∑ i, star (X i) * X i ≤ 1) :
    cfcR f (∑ i, star (X i) * A i * X i) ≤
      ∑ i, star (X i) * cfcR f (A i) * X i := by
  sorry

end

section
open QuantumChannel SandwichedRenyiRelativeEntropy

theorem sandwichedRenyiDivNN_theorem1
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_ne1 : α ≠ 1)
    {ρ σ : L ℋ} (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (_hσpd : IsPositiveDefinite σ) :
    sandwichedRenyiDivNN α (E.toFun ρ) (E.toFun σ) ≤
      sandwichedRenyiDivNN α ρ σ := by
  sorry

end

section
open QuantumChannel SandwichedRenyiRelativeEntropy

theorem sandwichedRenyi_tendsto_umegakiNorm_of_support
    {H : Type u} [Qudit H] [Nontrivial H] {ρ σ : L H}
    (hρ : 0 ≤ ρ) (hρ0 : ρ ≠ 0) (hσ : 0 ≤ σ) (hsupp : SupportLE ρ σ) :
    Filter.Tendsto (fun α => sandwichedRenyiDiv α ρ σ) (𝓝[≠] (1 : ℝ))
      (𝓝 (umegakiNorm ρ σ)) := by
  sorry

end

section
open QuantumChannel JensenOperatorInequality LownerHeinzTheorem

theorem jensenFinite_of_opConvexOnAll_of_isOpen
    {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] [Nontrivial ℋ] {ι : Type v} [Fintype ι]
    {I : Set ℝ} (hI : I.OrdConnected) (hopen : IsOpen I) (h0 : 0 ∈ I)
    {f : ℝ → ℝ} (hf : OperatorConvexOnAll.{u} I f) (hf0 : f 0 ≤ 0)
    (A X : ι → ℋ →L[ℂ] ℋ) (hA : ∀ i, IsSelfAdjoint (A i))
    (hAs : ∀ i, spectrum ℝ (A i) ⊆ I) (hX : ∑ i, star (X i) * X i ≤ 1) :
    cfcR f (∑ i, star (X i) * A i * X i) ≤
      ∑ i, star (X i) * cfcR f (A i) * X i := by
  sorry

end

section
open QuantumChannel JensenOperatorInequality LownerHeinzTheorem

theorem jensenFinite_of_opConvexOnAll_of_endpoints
    {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] [Nontrivial ℋ] {ι : Type v} [Fintype ι]
    {I : Set ℝ} (hI : I.OrdConnected) (h0 : 0 ∈ I)
    {f : ℝ → ℝ} (hf : OperatorConvexOnAll.{u} I f) (hf0 : f 0 ≤ 0)
    (he : ∀ x ∈ I \ interior I, ContinuousWithinAt f I x)
    (A X : ι → ℋ →L[ℂ] ℋ) (hA : ∀ i, IsSelfAdjoint (A i))
    (hAs : ∀ i, spectrum ℝ (A i) ⊆ I) (hX : ∑ i, star (X i) * X i ≤ 1) :
    cfcR f (∑ i, star (X i) * A i * X i) ≤
      ∑ i, star (X i) * cfcR f (A i) * X i := by
  sorry

end

end ComparatorChallenges.Paper1
