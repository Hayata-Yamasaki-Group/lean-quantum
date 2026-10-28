/-
Minimax equality for the trace pairing (X, Y) ↦ Re Tr(XY) on nonempty compact convex sets (gsl_y01).
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 3.
-/
/-
Minimax for the composite β.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 3.
-/
/-
Dictionary between the composite β and the resource Dmin.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 3; Hayashi–Yamasaki, Theorem 4.
-/
import Quantum.QuantumEntropy.GourResource.ResourceTesting
import Quantum.QuantumEntropy.GourResource.TestingSDP

open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower ℝ ℂ (L H) :=
  RestrictScalars.isScalarTower ℝ ℂ (L H)

namespace GourResource


open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem pairing_continuous_left {A : Type u} [Qudit.{u} A] (Y : L A) :
    Continuous (fun X : L A => pairing X Y) := by
  exact QuantumState.continuous_re_trace_lm.comp (continuous_id.mul continuous_const)

private theorem pairing_continuous_right {A : Type u} [Qudit.{u} A] (X : L A) :
    Continuous (pairing X) := by
  exact QuantumState.continuous_re_trace_lm.comp (continuous_const.mul continuous_id)

private theorem pairing_convex {A : Type u} [Qudit.{u} A]
    (S : Set (L A)) (hS : Convex ℝ S) (Y : L A) :
    ConvexOn ℝ S (fun X => pairing X Y) := by
  refine ⟨hS, ?_⟩
  intro X hX Z hZ a b ha hb hab
  simp [pairing, add_mul]

private theorem pairing_concave {A : Type u} [Qudit.{u} A]
    (T : Set (L A)) (hT : Convex ℝ T) (X : L A) :
    ConcaveOn ℝ T (pairing X) := by
  refine ⟨hT, ?_⟩
  intro Y hY Z hZ a b ha hb hab
  simp [pairing, mul_add]

theorem gsl_y01 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (S T : Set (L.{u} A)),
  S.Nonempty → T.Nonempty → IsCompact S → IsCompact T →
  Convex ℝ S → Convex ℝ T →
  sSup ((fun Y => sInf ((fun X => pairing.{u} X Y) '' S)) '' T) =
    sInf ((fun X => sSup ((fun Y => pairing.{u} X Y) '' T)) '' S)
:= by
  intro A _ _ S T hSne hTne hSc hTc hS hT
  let lo := fun Y => sInf ((fun X => pairing X Y) '' S)
  let hi := fun X => sSup ((fun Y => pairing X Y) '' T)
  have hbLo (Y : L A) : BddBelow ((fun X => pairing X Y) '' S) :=
    hSc.bddBelow_image (pairing_continuous_left Y).continuousOn
  have hbHi (X : L A) : BddAbove ((fun Y => pairing X Y) '' T) :=
    hTc.bddAbove_image (pairing_continuous_right X).continuousOn
  have hweak (X : L A) (hX : X ∈ S) (Y : L A) (hY : Y ∈ T) : lo Y ≤ hi X :=
    (csInf_le (hbLo Y) (Set.mem_image_of_mem _ hX)).trans
      (le_csSup (hbHi X) (Set.mem_image_of_mem _ hY))
  obtain ⟨X₀, hX₀⟩ := hSne
  obtain ⟨Y₀, hY₀⟩ := hTne
  have hbOuterLo : BddAbove (lo '' T) := by
    refine ⟨hi X₀, ?_⟩
    rintro _ ⟨Y, hY, rfl⟩
    exact hweak X₀ hX₀ Y hY
  have hbOuterHi : BddBelow (hi '' S) := by
    refine ⟨lo Y₀, ?_⟩
    rintro _ ⟨X, hX, rfl⟩
    exact hweak X hX Y₀ hY₀
  change sSup (lo '' T) = sInf (hi '' S)
  apply le_antisymm
  · apply csSup_le (Set.Nonempty.image _ ⟨Y₀, hY₀⟩)
    rintro _ ⟨Y, hY, rfl⟩
    apply le_csInf (Set.Nonempty.image _ ⟨X₀, hX₀⟩)
    rintro _ ⟨X, hX, rfl⟩
    exact hweak X hX Y hY
  · apply le_of_forall_lt_imp_le_of_dense
    intro r hr
    have hresponse : ∀ X ∈ S, ∃ Y ∈ T, r < pairing X Y := by
      intro X hX
      have hrX : r < hi X :=
        hr.trans_le (csInf_le hbOuterHi (Set.mem_image_of_mem _ hX))
      obtain ⟨v, ⟨Y, hY, rfl⟩, hv⟩ :=
        (lt_csSup_iff (hbHi X) (Set.Nonempty.image _ ⟨Y₀, hY₀⟩)).mp hrX
      exact ⟨Y, hY, hv⟩
    obtain ⟨Y, hY, hcommon⟩ :=
      SandwichedRenyiRelativeEntropy.compact_common_response S T
        ⟨X₀, hX₀⟩ hS ⟨Y₀, hY₀⟩ hTc hT pairing
        (fun Y _ => pairing_convex S hS Y)
        (fun X _ => pairing_concave T hT X)
        (fun X _ => (pairing_continuous_right X).continuousOn) r hresponse
    have hrLo : r ≤ lo Y := by
      apply le_csInf (Set.Nonempty.image _ ⟨X₀, hX₀⟩)
      rintro _ ⟨X, hX, rfl⟩
      exact hcommon X hX
    exact hrLo.trans (le_csSup hbOuterLo (Set.mem_image_of_mem _ hY))

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem pairing_comm {A : Type u} [Qudit A] (X Y : L A) :
    pairing X Y = pairing Y X := by
  exact congrArg Complex.re (LinearMap.trace_mul_comm ℂ X Y)

private theorem pairing_continuous {A : Type u} [Qudit A] [Nontrivial A]
    (X : L A) :
    Continuous (fun M : L A => pairing X M) := by
  have hTr : Continuous (fun M : L A => Tr M) :=
    LinearMap.continuous_of_finiteDimensional (Tr : L A →ₗ[ℂ] ℂ)
  exact Complex.continuous_re.comp (hTr.comp (continuous_const.mul continuous_id))

private theorem pairing_combo {A : Type u} [Qudit A]
    (X M N : L A) (a b : ℝ) :
    pairing X (a • M + b • N) = a * pairing X M + b * pairing X N := by
  simp [pairing, mul_add, map_add, LinearMap.map_smul_of_tower]

private theorem effect_convex {A : Type u} [Qudit A] :
    Convex ℝ {M : L A | effect M} := by
  have heq : {M : L A | effect M} = Set.Icc 0 1 := by
    ext M
    simp only [Set.mem_setOf_eq, effect, Set.mem_Icc,
      ← LinearMap.nonneg_iff_isPositive, sub_nonneg]
  rw [heq]
  exact convex_Icc 0 1

private theorem feasible_compact {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) (ε : ℝ) :
    IsCompact {M : L A | effect M ∧ 1 - ε ≤ pairing ρ.1 M} := by
  exact (GourResource.gsl_b01.{u}.2.2 (A := A)).2.inter_right
    (isClosed_le continuous_const (pairing_continuous ρ.1))

private theorem feasible_convex {A : Type u} [Qudit A]
    (ρ : State A) (ε : ℝ) :
    Convex ℝ {M : L A | effect M ∧ 1 - ε ≤ pairing ρ.1 M} := by
  intro M hM N hN a b ha hb hab
  refine ⟨effect_convex hM.1 hN.1 ha hb hab, ?_⟩
  change 1 - ε ≤ pairing ρ.1 (a • M + b • N)
  rw [pairing_combo]
  calc
    1 - ε = a * (1 - ε) + b * (1 - ε) := by rw [← add_mul, hab, one_mul]
    _ ≤ a * pairing ρ.1 M + b * pairing ρ.1 N :=
      add_le_add (mul_le_mul_of_nonneg_left hM.2 ha)
        (mul_le_mul_of_nonneg_left hN.2 hb)

private theorem beta_image {A : Type u} [Qudit A]
    (ρ σ : L A) (ε : ℝ) :
    beta ρ σ ε = sInf ((fun M => pairing M σ) ''
      {M : L A | effect M ∧ 1 - ε ≤ pairing ρ M}) := by
  unfold beta
  congr 1
  ext b
  constructor
  · rintro ⟨M, hM, hacc, rfl⟩
    exact ⟨M, ⟨hM, hacc⟩, pairing_comm M σ⟩
  · rintro ⟨M, ⟨hM, hacc⟩, rfl⟩
    exact ⟨M, hM, hacc, pairing_comm M σ⟩

private theorem betaSet_image {A : Type u} [Qudit A]
    (ρ : L A) (S : Set (L A)) (ε : ℝ) :
    betaSet ρ S ε = sInf ((fun M => sSup ((fun σ => pairing M σ) '' S)) ''
      {M : L A | effect M ∧ 1 - ε ≤ pairing ρ M}) := by
  have hc (M : L A) : (fun σ => pairing σ M) = (fun σ => pairing M σ) := by
    funext σ
    exact pairing_comm σ M
  unfold betaSet
  simp only [hc]
  congr 1
  ext b
  constructor
  · rintro ⟨M, hM, hacc, rfl⟩
    exact ⟨M, ⟨hM, hacc⟩, rfl⟩
  · rintro ⟨M, ⟨hM, hacc⟩, rfl⟩
    exact ⟨M, hM, hacc, rfl⟩

theorem gsl_y03 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (S : Set (L.{u} A)) (ε : ℝ),
  S.Nonempty → IsCompact S → Convex ℝ S →
  S ⊆ {X | IsDensity.{u} X} → ε ∈ Set.Ico 0 1 →
  betaSet.{u} ρ.1 S ε = worstBeta.{u} ρ.1 S ε
:= by
  intro A _ _ ρ S ε hS hSc hSv _ hε
  let K : Set (L A) := {M | effect M ∧ 1 - ε ≤ pairing ρ.1 M}
  have hK : K.Nonempty := by
    obtain ⟨M, hM, hacc, _⟩ := GourResource.gsl_b02.{u}.2.2.2.1 ρ ρ ε hε
    exact ⟨M, hM, hacc⟩
  rw [betaSet_image, worstBeta]
  simp only [beta_image]
  exact (GourResource.gsl_y01.{u} K S hK hS (feasible_compact ρ ε) hSc (feasible_convex ρ ε)
    hSv).symm

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem gsl_y04_negLog_strictAnti : StrictAnti OPT.binaryNegLog2 := by
  intro a b hab
  have hb : b ≠ 0 := ne_of_gt ((zero_le a).trans_lt hab)
  by_cases ha : a = 0
  · rw [ha, OPT.binaryNegLog2_zero, OPT.binaryNegLog2, if_neg hb]
    exact EReal.coe_lt_top _
  have ha_pos : 0 < a := lt_of_le_of_ne (zero_le a) (Ne.symm ha)
  simp only [OPT.binaryNegLog2, if_neg ha, if_neg hb, EReal.coe_lt_coe_iff]
  exact neg_lt_neg (Real.logb_lt_logb (by norm_num)
    (show 0 < (a : ℝ) from ha_pos) (show (a : ℝ) < (b : ℝ) from hab))

theorem gsl_y04 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (S : Set (L.{u} A)) (ε : ℝ),
  S.Nonempty → IsClosed S → Convex ℝ S →
  S ⊆ {X | IsDensity.{u} X} → ε ∈ Set.Ioo 0 1 →
  res.{u} (fun X Y => dh.{u} X Y ε) ρ.1 S = dSet.{u} ρ.1 S ε
:= by
  intro A _ _ ρ S ε hne hclosed hconv hdens hε
  have hcompact : IsCompact S :=
    (GourResource.gsl_b01.{u}.2.2 (A := A)).1.of_isClosed_subset hclosed hdens
  obtain ⟨σ, hσ, hmin⟩ := GourResource.gsl_c20.{u} ρ S ε hne hclosed hdens hε
  have hmax : ∀ X ∈ S, Real.toNNReal (beta ρ.1 X ε) ≤
      Real.toNNReal (beta ρ.1 σ ε) := by
    intro X hX
    apply gsl_y04_negLog_strictAnti.le_iff_ge.mp
    change dh ρ.1 σ ε ≤ dh ρ.1 X ε
    rw [hmin]
    exact iInf_le_of_le X (iInf_le_of_le hX le_rfl)
  have hbound : ∀ X ∈ S, beta ρ.1 X ε ≤
      (Real.toNNReal (beta ρ.1 σ ε) : ℝ) := by
    intro X hX
    exact Real.toNNReal_le_iff_le_coe.mp (hmax X hX)
  have hbdd : BddAbove ((fun X => beta ρ.1 X ε) '' S) := by
    refine ⟨(Real.toNNReal (beta ρ.1 σ ε) : ℝ), ?_⟩
    rintro b ⟨X, hX, rfl⟩
    exact hbound X hX
  have hsup : Real.toNNReal (worstBeta ρ.1 S ε) =
      Real.toNNReal (beta ρ.1 σ ε) := by
    apply le_antisymm
    · apply Real.toNNReal_le_iff_le_coe.mpr
      exact csSup_le (hne.image _) (by
        rintro b ⟨X, hX, rfl⟩
        exact hbound X hX)
    · exact Real.toNNReal_mono (le_csSup hbdd ⟨σ, hσ, rfl⟩)
  rw [dSet, GourResource.gsl_y03.{u} ρ S ε hne hcompact hconv hdens ⟨hε.1.le, hε.2⟩, hsup]
  exact hmin.symm

end GourResource

