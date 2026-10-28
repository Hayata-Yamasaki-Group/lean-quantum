/-
Freeness of the padded block.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 6.
-/
/-
Additivity of the sandwiched Rényi divergence sand (α > 1) along the padded block sequence (gsl_y08).
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 6.
-/
import Quantum.QuantumEntropy.GourResource.TensorSeed
import Quantum.QuantumEntropy.Gour.RenyiDPIAdapter.GSLCore
import Quantum.QuantumMechanics.QuantumStateGeneralizedStein


namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem gsl_y07_cast_mem {A : Type u} [Qudit A] (F : Family A)
    {n m : ℕ} (h : n = m) (X : L (Copy A n)) :
    cast (congrArg (fun j => L (Copy A j)) h) X ∈ F m ↔ X ∈ F n := by
  subst m
  rfl

private theorem gsl_y07_left_unit_mem {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) (F : Family A) (n : ℕ) (X : L (Copy A n)) (hX : X ∈ F n) :
    join ρ 0 n 1 X ∈ F (0 + n) := by
  apply (gsl_y07_cast_mem F (Nat.zero_add n) _).mp
  rwa [(gsl_y05 ρ ρ n 0).2.2.1 X |>.2]

private theorem gsl_y07_pow_mem {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) (F : Family A) (hF : hyValid ρ F)
    (γ : State A) (hγ : pow γ 1 ∈ F 1) (n : ℕ) (hn : 0 < n) :
    pow γ n ∈ F n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hz : n = 0
    · subst n
      exact hγ
    · have hn' : 0 < n := Nat.pos_of_ne_zero hz
      rw [← (gsl_y05 ρ γ n 1).1]
      exact hF.2.2.1 n 1 hn' (by decide) _ (ih hn') _ hγ

private theorem gsl_y07_block_mem {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) (F : Family A) (hF : hyValid ρ F)
    (m : ℕ) (σ : L (Copy A m)) (hm : 0 < m) (hσ : σ ∈ F m)
    (k : ℕ) (hk : 0 < k) : blockPower ρ m σ k ∈ F (m * k) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hz : k = 0
    · subst k
      simpa only [blockPower, Nat.mul_zero] using gsl_y07_left_unit_mem ρ F m σ hσ
    · have hk' : 0 < k := Nat.pos_of_ne_zero hz
      change join ρ (m * k) m (blockPower ρ m σ k) σ ∈ F (m * k + m)
      exact hF.2.2.1 (m * k) m (Nat.mul_pos hm hk') hm _ (ih hk') _ hσ

theorem gsl_y07 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∀ (γ : State.{u} A) (m : ℕ) (σ : L.{u} (Copy.{u} A m)),
    0 < m → pow.{u} γ 1 ∈ F 1 → σ ∈ F m →
    admissible.{u} F (padded.{u} ρ γ m σ)
:= by
  intro A _ _ ρ F hF γ m σ hm hγ hσ n hn
  have hfree : padded ρ γ m σ n ∈ F n := by
    unfold padded
    apply (gsl_y07_cast_mem F (Nat.div_add_mod n m) _).mpr
    generalize hk : n / m = k
    generalize hr : n % m = r
    have hpos : 0 < m * k + r := by
      rw [← hk, ← hr, Nat.div_add_mod]
      exact hn
    cases k with
    | zero =>
      have hrpos : 0 < r := by simpa only [Nat.mul_zero, Nat.zero_add] using hpos
      simpa only [Nat.mul_zero, blockPower] using
        gsl_y07_left_unit_mem ρ F r (pow γ r) (gsl_y07_pow_mem ρ F hF γ hγ r hrpos)
    | succ k =>
      have hb := gsl_y07_block_mem ρ F hF m σ hm hσ (k + 1) (Nat.succ_pos k)
      cases r with
      | zero =>
        change join ρ (m * (k + 1)) 0 (blockPower ρ m σ (k + 1)) 1 ∈ F (m * (k + 1))
        rw [(gsl_y05 ρ γ (m * (k + 1)) 0).2.2.1 (blockPower ρ m σ (k + 1)) |>.1]
        exact hb
      | succ r =>
        exact hF.2.2.1 (m * (k + 1)) (r + 1) (Nat.mul_pos hm (Nat.succ_pos k))
          (Nat.succ_pos r) _ hb _ (gsl_y07_pow_mem ρ F hF γ hγ (r + 1) (Nat.succ_pos r))
  exact ⟨hfree, hF.1 n hn hfree⟩

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem sand_density {A : Type u} [Qudit A] [Nontrivial A]
    (α : ℝ) (X Y : L A) (hX : IsDensity X) (hY : IsDensity Y) :
    sand α X Y = SandwichedRenyiRelativeEntropy.gourSandwichedRenyiBits
      (ENNReal.ofReal α) X Y hX hY := by
  simp only [sand, dif_pos hX, dif_pos hY]

private theorem pow_density {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) (n : ℕ) : IsDensity (pow ρ n) :=
  (w42_tensor_spectral_dictionary.1 ρ n).2.1

private theorem sand_tensor {A B : Type u} [Qudit A] [Qudit B]
    [Nontrivial A] [Nontrivial B] [Nontrivial (A ⊗[ℂ] B)]
    (α : ℝ) (hα : 1 < α) (X Y : L A) (Z W : L B)
    (hX : IsDensity X) (hY : IsDensity Y) (hZ : IsDensity Z) (hW : IsDensity W) :
    sand α (TensorProduct.map X Z) (TensorProduct.map Y W) =
      sand α X Y + sand α Z W := by
  rw [sand_density _ _ _ (OPT.isDensity_tensorProduct _ _ hX hZ)
    (OPT.isDensity_tensorProduct _ _ hY hW), sand_density _ _ _ hX hY,
    sand_density _ _ _ hZ hW]
  exact RenyiDPI.gourSandwichedBits_tensor_gt_one
    hα _ _ _ _ hX hY hZ hW

private theorem push_density {A B : Type u} [Qudit A] [Qudit B]
    (U : A ≃ₗᵢ[ℂ] B) (X : L A) (hX : IsDensity X) : IsDensity (push U X) := by
  have h := (isometryDensity U.toLinearIsometry ⟨X, hX⟩).2
  change IsDensity (QuantumChannel.krausTerm U.toLinearMap X) at h
  simpa only [QuantumChannel.krausTerm, LinearMap.coe_mk,
    AddHom.coe_mk, LinearIsometryEquiv.adjoint_toLinearMap_eq_symm, push] using h

private theorem sand_push_le {A B : Type u} [Qudit A] [Qudit B]
    [Nontrivial A] [Nontrivial B] (U : A ≃ₗᵢ[ℂ] B)
    (α : ℝ) (hα : 1 < α) (X Y : L A) (hX : IsDensity X) (hY : IsDensity Y) :
    sand α (push U X) (push U Y) ≤ sand α X Y := by
  have hU : (LinearMap.adjoint U.toLinearMap).comp U.toLinearMap = (1 : L A) := by
    rw [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
    ext x
    exact U.symm_apply_apply x
  have h := RenyiDPI.gourSandwichedBits_dataProcessing_gt_one
    (SandwichedRenyiRelativeEntropy.isometricConjugationChannel U.toLinearMap hU)
    hα X Y hX hY
  rw [sand_density _ _ _ (push_density U X hX) (push_density U Y hY),
    sand_density _ _ _ hX hY]
  simpa only [SandwichedRenyiRelativeEntropy.isometricConjugationChannel_apply,
    LinearIsometryEquiv.adjoint_toLinearMap_eq_symm, push, LinearMap.comp_assoc] using h

private theorem sand_push {A B : Type u} [Qudit A] [Qudit B]
    [Nontrivial A] [Nontrivial B] (U : A ≃ₗᵢ[ℂ] B)
    (α : ℝ) (hα : 1 < α) (X Y : L A) (hX : IsDensity X) (hY : IsDensity Y) :
    sand α (push U X) (push U Y) = sand α X Y := by
  apply le_antisymm (sand_push_le U α hα X Y hX hY)
  have h := sand_push_le U.symm α hα (push U X) (push U Y)
    (push_density U X hX) (push_density U Y hY)
  have hinv (Z : L A) : push U.symm (push U Z) = Z := by
    ext x
    simp [push]
  simpa only [hinv] using h

private theorem sand_self {A : Type u} [Qudit A] [Nontrivial A]
    (α : ℝ) (hα : 1 < α) (X : L A) (hX : IsDensity X) : sand α X X = 0 := by
  have hα0 : 0 ≤ α := le_trans zero_le_one hα.le
  rw [sand_density _ _ _ hX hX,
    SandwichedRenyiRelativeEntropy.gourSandwichedRenyiBits_standard_order]
  · rw [ENNReal.toReal_ofReal hα0]
    simp [SandwichedRenyiRelativeEntropy.standardSandwichedRenyiBitsFinite,
      SandwichedRenyiRelativeEntropy.suppLE, SandwichedRenyiRelativeEntropy.SupportLE,
      SandwichedRenyiRelativeEntropy.sandwichedQuasi_self_density
        (lt_trans zero_lt_one hα) X hX, hX.2]
  · exact ENNReal.ofReal_ne_zero_iff.mpr (lt_trans zero_lt_one hα)
  · intro h
    have := congrArg ENNReal.toReal h
    exact (ne_of_gt hα) (by simpa only
      [ENNReal.toReal_ofReal hα0, ENNReal.toReal_one] using this)
  · exact ENNReal.ofReal_ne_top
  · simpa only [ENNReal.toReal_ofReal hα0] using (show (1 / 2 : ℝ) ≤ α by linarith)

private theorem sand_join {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) (n m : ℕ) (α : ℝ) (hα : 1 < α)
    (X Y : L (Copy A n)) (Z W : L (Copy A m))
    (hX : IsDensity X) (hY : IsDensity Y) (hZ : IsDensity Z) (hW : IsDensity W) :
    sand α (join ρ n m X Z) (join ρ n m Y W) =
      sand α X Y + sand α Z W := by
  change sand α (push (w44TensorJoin ρ n m) (TensorProduct.map X Z))
    (push (w44TensorJoin ρ n m) (TensorProduct.map Y W)) = _
  rw [sand_push _ _ hα _ _ (OPT.isDensity_tensorProduct _ _ hX hZ)
    (OPT.isDensity_tensorProduct _ _ hY hW)]
  exact sand_tensor α hα X Y Z W hX hY hZ hW

private theorem nat_succ_mul (n : ℕ) (x : EReal) :
    ((n + 1 : ℕ) : EReal) * x = (n : EReal) * x + x := by
  rw [Nat.cast_add, Nat.cast_one,
    EReal.right_distrib_of_nonneg (by positivity) zero_le_one, one_mul]

private theorem sand_pow {A : Type u} [Qudit A] [Nontrivial A]
    (ρ γ : State A) (α : ℝ) (hα : 1 < α) (n : ℕ) :
    sand α (pow ρ n) (pow γ n) = (n : EReal) * sand α ρ.1 γ.1 := by
  induction n with
  | zero =>
    simpa only [Nat.cast_zero, zero_mul] using sand_self α hα (pow ρ 0) (pow_density ρ 0)
  | succ n ih =>
    change sand α (TensorProduct.map ρ.1 (pow ρ n))
      (TensorProduct.map γ.1 (pow γ n)) = _
    rw [sand_tensor α hα ρ.1 γ.1 _ _ ρ.2 γ.2 (pow_density ρ n) (pow_density γ n), ih,
      nat_succ_mul, add_comm]

private theorem density_cast {A : Type u} [Qudit A] {n m : ℕ}
    (h : n = m) (X : L (Copy A n)) (hX : IsDensity X) :
    IsDensity (cast (congrArg (fun j => L (Copy A j)) h) X) := by
  subst m
  exact hX

private theorem sand_cast_pow {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) (α : ℝ) {n m : ℕ} (h : n = m) (X : L (Copy A n)) :
    sand α (pow ρ m) (cast (congrArg (fun j => L (Copy A j)) h) X) =
      sand α (pow ρ n) X := by
  subst m
  rfl

private theorem block_density {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) (m : ℕ) (σ : State (Copy A m)) (k : ℕ) :
    IsDensity (blockPower ρ m σ.1 k) := by
  induction k with
  | zero => exact pow_density ρ 0
  | succ k ih =>
    exact density_cast (Nat.mul_succ m k).symm _
      ((gsl_y05 ρ ρ (m * k) m).2.1 _ _ ih σ.2)

private theorem sand_block {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) (m : ℕ) (σ : State (Copy A m)) (α : ℝ) (hα : 1 < α) (k : ℕ) :
    sand α (pow ρ (m * k)) (blockPower ρ m σ.1 k) =
      (k : EReal) * sand α (pow ρ m) σ.1 := by
  induction k with
  | zero =>
    simpa only [Nat.mul_zero, blockPower, Nat.cast_zero, zero_mul] using
      sand_self α hα (pow ρ 0) (pow_density ρ 0)
  | succ k ih =>
    change sand α (pow ρ (m * (k + 1)))
      (cast (congrArg (fun j => L (Copy A j)) (Nat.mul_succ m k).symm)
        (join ρ (m * k) m (blockPower ρ m σ.1 k) σ.1)) = _
    rw [sand_cast_pow ρ α (Nat.mul_succ m k).symm,
      ← (gsl_y05 ρ ρ (m * k) m).1,
      sand_join ρ (m * k) m α hα _ _ _ _ (pow_density ρ (m * k))
        (block_density ρ m σ k) (pow_density ρ m) σ.2,
      ih, nat_succ_mul]

theorem gsl_y08 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ γ : State.{u} A) (m : ℕ)
  (σ : State.{u} (Copy.{u} A m)) (α : ℝ), 0 < m → 1 < α →
  ∀ n : ℕ, sand.{u} α (pow.{u} ρ n) (padded.{u} ρ γ m σ.1 n) =
    ((n/m : ℕ) : EReal) * sand.{u} α (pow.{u} ρ m) σ.1 +
    ((n%m : ℕ) : EReal) * sand.{u} α ρ.1 γ.1
:= by
  intro A _ _ ρ γ m σ α _hm hα n
  have hn : m * (n / m) + n % m = n := by
    simpa [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div n m
  unfold padded
  rw [sand_cast_pow ρ α hn, ← (gsl_y05 ρ ρ (m * (n / m)) (n % m)).1,
    sand_join ρ (m * (n / m)) (n % m) α hα _ _ _ _
      (pow_density ρ (m * (n / m))) (block_density ρ m σ (n / m))
      (pow_density ρ (n % m)) (pow_density γ (n % m)),
    sand_block ρ m σ α hα, sand_pow ρ γ α hα]

end GourResource

