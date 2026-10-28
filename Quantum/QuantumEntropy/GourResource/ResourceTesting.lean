/-
On a nonempty closed free set F of density operators, constructs σ attaining the inf of dh for fixed ρ and ε∈(0,1).
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 3.
-/
import Quantum.QuantumEntropy.GourResource.TestingContinuity

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem negLog_antitone : Antitone OPT.binaryNegLog2 := by
  intro a b hab
  by_cases ha : a = 0
  · rw [ha, OPT.binaryNegLog2_zero]
    exact le_top
  have ha_pos : 0 < a := lt_of_le_of_ne (zero_le a) (Ne.symm ha)
  have hb : b ≠ 0 := ne_of_gt (lt_of_lt_of_le ha_pos hab)
  simp only [OPT.binaryNegLog2, if_neg ha, if_neg hb, EReal.coe_le_coe_iff]
  exact neg_le_neg (Real.logb_le_logb_of_le (by norm_num)
    (show 0 < (a : ℝ) from ha_pos) (show (a : ℝ) ≤ (b : ℝ) from hab))

theorem gsl_c20 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Set (L.{u} A)) (ε : ℝ),
  F.Nonempty → IsClosed F → F ⊆ {X | IsDensity.{u} X} → ε ∈ Set.Ioo 0 1 →
  ∃ σ ∈ F, dh.{u} ρ.1 σ ε = res.{u} (fun X Y => dh.{u} X Y ε) ρ.1 F)
:= by
  intro A _ _ ρ F ε hne hclosed hdens hε
  have hcompact : IsCompact F := (GourResource.gsl_b01.{u}.2.2 (A := A)).1.of_isClosed_subset
    hclosed hdens
  let S : Set (State A) := {σ | σ.1 ∈ F}
  have himage : Subtype.val '' S = F := by
    ext X
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact hσ
    · intro hX
      exact ⟨⟨X, hdens hX⟩, hX, rfl⟩
  have hS : IsCompact S := Subtype.isCompact_iff.mpr (himage ▸ hcompact)
  have hSne : S.Nonempty := by
    obtain ⟨X, hX⟩ := hne
    exact ⟨⟨X, hdens hX⟩, hX⟩
  obtain ⟨σ, hσ, hmax⟩ := hS.exists_isMaxOn hSne
    (GourResource.gsl_y02.{u} ρ ε ⟨hε.1.le, hε.2⟩).continuousOn
  refine ⟨σ.1, hσ, le_antisymm ?_ ?_⟩
  · refine le_iInf fun X => le_iInf fun hX => ?_
    exact negLog_antitone (Real.toNNReal_mono
      (hmax (show (⟨X, hdens hX⟩ : State A) ∈ S from hX)))
  · exact iInf_le_of_le σ.1 (iInf_le_of_le hσ le_rfl)

end GourResource

