/-
hRate converges to reg.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Theorem 4.
-/
/-
The H–Y main theorem without assuming permutation invariance. The bits rate of the composite β converges to reg.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Theorem 1; Hayashi–Yamasaki, Theorem 4.
-/
/-
Displays the common finite nonnegative limit of the composite testing rate and uRate.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Theorem 4.
-/
/-
Thm 11.4 for families satisfying the four conditions of Gour.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Theorems 1 and 4.
-/
import Quantum.QuantumEntropy.GourResource.DirectBound
import Quantum.QuantumEntropy.Gour.UmegakiDPIAdapter.GSLCore
import Quantum.QuantumEntropy.GourResource.Minimax


namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


/-- Under `hyValid ρ F`, for every `ε ∈ (0, 1)`, `hRate ρ F ε` converges to `reg ρ F`.
This combines the lower bound `gsl_y51` with the strong converse bound `gsl_y10`. -/
theorem gsl_y52 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ ε : ℝ, ε ∈ Set.Ioo 0 1 →
    Tendsto (hRate.{u} ρ F ε) atTop (𝓝 (reg.{u} ρ F))
:= by
  intro A _ _ ρ F hF ε hε
  exact tendsto_of_le_liminf_of_limsup_le
    (GourResource.gsl_y51.{u} ρ F hF ε hε)
    (GourResource.gsl_y10.{u} ρ F hF ε ⟨hε.1.le, hε.2⟩)

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


/-- Convergence of the composite testing rate (Hayashi–Yamasaki, Theorem 1). Under
`hyValid ρ F`, for every `ε ∈ (0, 1)` the rate of `dSet (pow ρ n) (F n) ε` converges to
`reg ρ F`. Permutation invariance and closedness under partial traces are not assumed. -/
theorem gsl_y53 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ ε : ℝ, ε ∈ Set.Ioo 0 1 →
    Tendsto (rate (fun n => dSet.{u} (pow.{u} ρ n) (F n) ε)) atTop (𝓝 (reg.{u} ρ F))
:= by
  intro A _ _ ρ F hF ε hε
  obtain ⟨γ, lam, _, _, hγ⟩ := GourResource.gsl_y06.{u} ρ F hF
  apply (GourResource.gsl_y52.{u} ρ F hF ε hε).congr'
  apply Filter.Eventually.of_forall
  intro n
  by_cases hn : n = 0
  · simp only [hRate, rate, if_pos hn]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hd := GourResource.gsl_y04.{u}
      ⟨pow ρ n, (w42_tensor_spectral_dictionary.1 ρ n).2.1⟩
      (F n) ε ⟨pow γ n, (hγ n hnpos).1⟩ (hF.2.1 n hnpos).1
      (hF.2.1 n hnpos).2 (hF.1 n hnpos) hε
    simp only [hRate, rate, if_neg hn]
    exact congrArg (fun x : EReal => ((1 / (n : ℝ) : ℝ) : EReal) * x) hd

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem du_nonneg {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ σ : L.{u} A) (hρ : IsDensity.{u} ρ) (hσ : IsDensity.{u} σ) :
    0 ≤ du.{u} ρ σ := by
  let D : OPT.GourMatrixStateDivergence.{u} :=
    fun ρ σ hρ hσ => OPT.petzQuantumRenyiDivergence OPT.petzRenyiOrderOne ρ σ hρ hσ
  have hP := OPT.petzOrderOneLaws_from_umegakiDPI.{u, u}
  have hD : OPT.GourMatrixRelativeEntropyLaws.{u} D :=
    ⟨hP.dataProcessing, fun {_ _} _ _ _ _ _ => hP.tensorAdditivity,
      hP.binaryNormalization⟩
  have hn := (w37_relative_diagonal_calibration D hD).1 ⟨ρ, hρ⟩ ⟨σ, hσ⟩
  simpa only [D, OPT.petzQuantumRenyiDivergence_one_eq_umegakiRelEntropyNN,
    du] using hn

private theorem reg_nonneg {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (F : Family.{u} A) (hF : hyValid.{u} ρ F) :
    0 ≤ reg.{u} ρ F := by
  obtain ⟨γ, lam, _, _, hγ⟩ := GourResource.gsl_y06.{u} ρ F hF
  unfold reg
  apply le_iInf
  intro n
  have hρn : IsDensity.{u} (pow.{u} ρ n) :=
    (w42_tensor_spectral_dictionary.{u}.1 ρ n).2.1
  obtain ⟨σ, hσ, hmin⟩ := GourResource.gsl_y57.{u} ⟨pow.{u} ρ n, hρn⟩ (F n)
    ⟨pow.{u} γ n, (hγ n n.2).1⟩ (hF.2.1 n n.2).1 (hF.1 n n.2)
  have hres : 0 ≤ res.{u} du.{u} (pow.{u} ρ n) (F n) := by
    rw [← hmin]
    exact du_nonneg _ _ hρn (hF.1 n n.2 hσ)
  simp only [uRate, rate, PNat.ne_zero, ↓reduceIte]
  exact mul_nonneg (EReal.coe_nonneg.mpr (div_nonneg zero_le_one (Nat.cast_nonneg n))) hres

/-- Common limit (Hayashi–Yamasaki, Theorem 4). Under `hyValid ρ F` and for every
`ε ∈ (0, 1)`, there is a real `r ≥ 0` with `reg ρ F = r` such that both the composite
testing rate and the relative entropy rate `uRate ρ F` converge to `r`. -/
theorem gsl_y55 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ ε : ℝ, ε ∈ Set.Ioo 0 1 →
  ∃ r : ℝ, 0 ≤ r ∧ reg.{u} ρ F = (r : EReal) ∧
    Tendsto (rate (fun n => dSet.{u} (pow.{u} ρ n) (F n) ε)) atTop (𝓝 (r : EReal)) ∧
    Tendsto (uRate.{u} ρ F) atTop (𝓝 (r : EReal))
:= by
  intro A _ _ ρ F hF ε hε
  obtain ⟨hu, r, hr⟩ := GourResource.gsl_c23.{u} ρ F hF
  have hnonneg : 0 ≤ r := EReal.coe_nonneg.mp (hr ▸ reg_nonneg ρ F hF)
  refine ⟨r, hnonneg, hr, ?_, ?_⟩
  · simpa only [hr] using GourResource.gsl_y53.{u} ρ F hF ε hε
  · simpa only [hr] using hu

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


/-- **Generalized quantum Stein's lemma** (Gour, Theorem 11.4). If the family `F` satisfies
`valid ρ F`, then for every `ε ∈ (0, 1)` the hypothesis-testing rate `hRate ρ F ε` converges
to the regularized relative entropy `reg ρ F`. The proof goes through the
Hayashi–Yamasaki version `gsl_y53` and does not use permutation invariance. -/
theorem gsl_y54 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), valid.{u} ρ F →
  ∀ ε : ℝ, ε ∈ Set.Ioo 0 1 →
    Tendsto (hRate.{u} ρ F ε) atTop (𝓝 (reg.{u} ρ F))
:= by
  intro A _ _ ρ F hF ε hε
  have hHY : hyValid ρ F := ⟨hF.1, hF.2.1, hF.2.2.2.1, hF.2.2.2.2⟩
  obtain ⟨γ, lam, _, _, hγ⟩ := GourResource.gsl_y06 ρ F hHY
  apply (GourResource.gsl_y53.{u} ρ F hHY ε hε).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hd := GourResource.gsl_y04
    ⟨pow ρ n, (w42_tensor_spectral_dictionary.1 ρ n).2.1⟩
    (F n) ε ⟨pow γ n, (hγ n hn).1⟩ (hHY.2.1 n hn).1
    (hHY.2.1 n hn).2 (hHY.1 n hn) hε
  simp only [hRate, rate, if_neg (Nat.ne_of_gt hn)]
  exact congrArg (fun x : EReal => ((1 / (n : ℝ) : ℝ) : EReal) * x) hd.symm

end GourResource

