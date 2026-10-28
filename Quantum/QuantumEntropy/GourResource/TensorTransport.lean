/-Proof construction: canonical coherence showing, from the eigenbasis-dependent implementation, the
action on pure tensors, and that the isometry is the same for different reference states.
Proof construction: applies GourConditionalEntropy.w44_tensor_join_basis and
w42_tensor_coordinate_dictionary on generators. Induction on tensorWord makes perm/join
basis-independent, and fixes the zero-copy cast and the index bijection of blockWord simultaneously.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 5; Hayashi–Yamasaki, Lemma 6.
-/
import Quantum.QuantumEntropy.GourResource.Definitions
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesStrongTypicalityContaminationFoundation.GSLCore

set_option linter.style.longLine false

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem basis_word {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (b : OrthonormalBasis (Fin (Module.finrank ℂ A)) ℂ A)
    (n : ℕ) (x : Fin n → Fin (Module.finrank ℂ A)) :
    w42TensorBasis b n x = tensorWord n (fun i => b (x i)) := by
  induction n with
  | zero =>
    simp only [w42TensorBasis, OrthonormalBasis.reindex_apply,
      OrthonormalBasis.map_apply, OrthonormalBasis.singleton_apply, tensorWord]
    rfl
  | succ n ih =>
    change ((b.tensorProduct (w42TensorBasis b n)).reindex _) x = _
    rw [OrthonormalBasis.reindex_apply]
    rw [OrthonormalBasis.tensorProduct_apply]
    exact congrArg (fun z => b (x 0) ⊗ₜ[ℂ] z) (ih _)

private theorem word_inner {A : Type u} [Qudit.{u} A]
    (n : ℕ) (x y : Fin n → A) :
    inner ℂ (tensorWord n x) (tensorWord n y) = ∏ i, inner ℂ (x i) (y i) := by
  induction n with
  | zero =>
    change inner ℂ (1 : ℂ) 1 = _
    simp
  | succ n ih =>
    change inner ℂ (x 0 ⊗ₜ[ℂ] tensorWord n _) (y 0 ⊗ₜ[ℂ] tensorWord n _) = _
    rw [TensorProduct.inner_tmul, ih, Fin.prod_univ_succ]

private theorem word_ext {A B : Type u} [Qudit.{u} A] [Nontrivial A] [Qudit.{u} B]
    (n : ℕ) (f g : Copy A n →ₗ[ℂ] B)
    (h : ∀ x, f (tensorWord n x) = g (tensorWord n x)) : f = g := by
  apply (w42TensorBasis (stdOrthonormalBasis ℂ A) n).toBasis.ext
  intro x
  simpa only [OrthonormalBasis.coe_toBasis, basis_word] using
    h (fun i => stdOrthonormalBasis ℂ A (x i))

private theorem perm_word {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State A) (n : ℕ) (π : Equiv.Perm (Fin n)) (x : Fin n → A) :
    perm ρ n π (tensorWord n x) = tensorWord n (fun i => x (π.symm i)) := by
  let b := w42TensorBasis (w42EigenBasis ρ) n
  apply b.repr.injective
  ext y
  obtain ⟨y, rfl⟩ := (wordPerm (Module.finrank ℂ A) n π).surjective y
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
  have hb : b (wordPerm (Module.finrank ℂ A) n π y) = perm ρ n π (b y) :=
    (OrthonormalBasis.equiv_apply_basis b b _ y).symm
  nth_rw 1 [hb]
  rw [LinearIsometryEquiv.inner_map_map]
  simp only [b, basis_word, word_inner, wordPerm]
  exact (Equiv.prod_comp π.symm (fun i => inner ℂ (w42EigenBasis ρ (y i)) (x i))).symm

private theorem perm_independent {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ γ : State A) (n : ℕ) (π : Equiv.Perm (Fin n)) :
    perm ρ n π = perm γ n π := by
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  apply word_ext
  intro x
  exact (perm_word ρ n π x).trans (perm_word γ n π x).symm

private theorem join_word {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State A) (n m : ℕ) (x : Fin n → A) (y : Fin m → A) :
    w44TensorJoin ρ n m (tensorWord n x ⊗ₜ[ℂ] tensorWord m y) =
      tensorWord (n + m) (Fin.append x y) := by
  apply (w42TensorBasis (w42EigenBasis ρ) (n + m)).repr.injective
  ext z
  obtain ⟨⟨v, w⟩, rfl⟩ := (Fin.appendEquiv n m).surjective z
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
  change inner ℂ (w42TensorBasis (w42EigenBasis ρ) (n + m) (Fin.append v w)) _ =
    inner ℂ (w42TensorBasis (w42EigenBasis ρ) (n + m) (Fin.append v w)) _
  nth_rw 1 [← w44_tensor_join_basis ρ n m v w]
  rw [LinearIsometryEquiv.inner_map_map]
  rw [TensorProduct.inner_tmul]
  simp only [basis_word, word_inner, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

private theorem join_independent {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ γ : State A) (n m : ℕ) : w44TensorJoin ρ n m = w44TensorJoin γ n m := by
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  apply ((w42TensorBasis (w42EigenBasis ρ) n).tensorProduct
    (w42TensorBasis (w42EigenBasis ρ) m)).toBasis.ext
  intro z
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply', basis_word]
  exact (join_word ρ n m _ _).trans (join_word γ n m _ _).symm

private def cons_equiv (ι : Type) (n : ℕ) :
    (ι × (Fin n → ι)) ≃ (Fin (n + 1) → ι) where
  toFun x := Fin.cons x.1 x.2
  invFun x := (x 0, fun i => x i.succ)
  left_inv x := by simp
  right_inv x := by ext i; exact Fin.cases rfl (fun _ => rfl) i

private noncomputable def word_basis {A : Type u} [Qudit.{u} A] [Nontrivial A]
    {ι : Type} [Fintype ι] (b : OrthonormalBasis ι ℂ A) :
    (n : ℕ) → OrthonormalBasis (Fin n → ι) ℂ (Copy A n)
  | 0 => (w42TensorBasis (stdOrthonormalBasis ℂ A) 0).reindex (Equiv.ofUnique _ _)
  | n + 1 => (b.tensorProduct (word_basis b n)).reindex (cons_equiv ι n)

private theorem word_basis_apply {A : Type u} [Qudit.{u} A] [Nontrivial A]
    {ι : Type} [Fintype ι] (b : OrthonormalBasis ι ℂ A)
    (n : ℕ) (x : Fin n → ι) :
    word_basis b n x = tensorWord n (fun i => b (x i)) := by
  induction n with
  | zero => simp only [word_basis, OrthonormalBasis.reindex_apply, basis_word, tensorWord]
  | succ n ih =>
    change ((b.tensorProduct (word_basis b n)).reindex _) x = _
    rw [OrthonormalBasis.reindex_apply, OrthonormalBasis.tensorProduct_apply]
    exact congrArg (fun z => b (x 0) ⊗ₜ[ℂ] z) (ih _)

private def block_index (m k : ℕ) : Fin k × Fin m ≃ Fin (m * k) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm k m))

private def block_equiv (ι : Type) (m k : ℕ) :
    (Fin k → Fin m → ι) ≃ (Fin (m * k) → ι) where
  toFun := blockWord m k
  invFun y i j := y (block_index m k (i, j))
  left_inv x := by
    ext i j
    change x ((block_index m k).symm (block_index m k (i, j))).1
      ((block_index m k).symm (block_index m k (i, j))).2 = _
    rw [Equiv.symm_apply_apply]
  right_inv y := by
    ext i
    change y (block_index m k ((block_index m k).symm i)) = y i
    rw [Equiv.apply_symm_apply]

private theorem block_prod (m k : ℕ) (f : Fin k → Fin m → ℂ) :
    (∏ i, ∏ j, f i j) = ∏ l, blockWord m k f l := by
  rw [← Fintype.prod_prod_type (fun p : Fin k × Fin m => f p.1 p.2)]
  exact (Equiv.prod_comp (block_index m k).symm (fun p => f p.1 p.2)).symm

private noncomputable def block_iso {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State A) (m k : ℕ) : Copy (Copy A m) k ≃ₗᵢ[ℂ] Copy A (m * k) :=
  (word_basis (word_basis (w42EigenBasis ρ) m) k).equiv
    (word_basis (w42EigenBasis ρ) (m * k)) (block_equiv _ m k)

private theorem block_iso_word {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State A) (m k : ℕ) (x : Fin k → Fin m → A) :
    block_iso ρ m k (tensorWord k (fun i => tensorWord m (x i))) =
      tensorWord (m * k) (blockWord m k x) := by
  let b := w42EigenBasis ρ
  apply (word_basis b (m * k)).repr.injective
  ext y
  obtain ⟨y, rfl⟩ := (block_equiv (Fin (Module.finrank ℂ A)) m k).surjective y
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
  have hb : word_basis b (m * k) (block_equiv _ m k y) =
      block_iso ρ m k (word_basis (word_basis b m) k y) :=
    (OrthonormalBasis.equiv_apply_basis _ _ _ y).symm
  nth_rw 1 [hb]
  rw [LinearIsometryEquiv.inner_map_map]
  simp only [word_basis_apply, word_inner]
  exact block_prod m k (fun i j => inner ℂ (b (y i j)) (x i j))

private theorem cast_word {A : Type u} [Qudit.{u} A]
    {n m : ℕ} (h : n = m) (x : Fin n → A) :
    cast (congrArg (Copy A) h) (tensorWord n x) =
      tensorWord m (fun i => x (Fin.cast h.symm i)) := by
  subst m
  rfl

private theorem cast_operator_apply {A : Type u} [Qudit.{u} A]
    {n m : ℕ} (h : n = m) (X : L (Copy A n)) (v : Copy A n) :
    cast (congrArg (fun j => L (Copy A j)) h) X (cast (congrArg (Copy A) h) v) =
      cast (congrArg (Copy A) h) (X v) := by
  subst m
  rfl

private theorem cast_inner {A : Type u} [Qudit.{u} A]
    {n m : ℕ} (h : n = m) (x y : Copy A n) :
    inner ℂ (cast (congrArg (Copy A) h) x) (cast (congrArg (Copy A) h) y) =
      inner ℂ x y := by
  subst m
  rfl

private theorem block_snoc {A : Type u} (m k : ℕ) (x : Fin (k + 1) → Fin m → A) :
    (fun i => blockWord m (k + 1) x (Fin.cast (Nat.mul_succ m k).symm i)) =
      Fin.append (blockWord m k (fun i => x i.castSucc)) (x (Fin.last k)) := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.append_left, blockWord, finProdFinEquiv]
    rfl
  · have hm : 0 < m := Nat.zero_lt_of_lt j.isLt
    simp only [Fin.append_right, blockWord, finProdFinEquiv]
    congr 1
    · apply Fin.ext
      change (m * k + j.val) / m = k
      exact (Nat.mul_add_div hm k j.val).trans
        (by rw [Nat.div_eq_of_lt j.isLt, Nat.add_zero])
    · apply Fin.ext
      change (m * k + j.val) % m = j.val
      simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]

private theorem cast_block_word {A : Type u} [Qudit.{u} A]
    (m k : ℕ) (x : Fin (k + 1) → Fin m → A) :
    cast (congrArg (Copy A) (Nat.mul_succ m k))
      (tensorWord (m * (k + 1)) (blockWord m (k + 1) x)) =
        tensorWord (m * k + m)
          (Fin.append (blockWord m k (fun i => x i.castSucc)) (x (Fin.last k))) := by
  rw [cast_word (Nat.mul_succ m k), block_snoc]

private theorem join_inner {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State A) (n m : ℕ) (X : L (Copy A n)) (Y : L (Copy A m))
    (a c : Copy A n) (b d : Copy A m) :
    inner ℂ (w44TensorJoin ρ n m (a ⊗ₜ[ℂ] b))
      (join ρ n m X Y (w44TensorJoin ρ n m (c ⊗ₜ[ℂ] d))) =
        inner ℂ a (X c) * inner ℂ b (Y d) := by
  simp [GourResource.join, TensorProduct.inner_tmul]

private theorem block_entry {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State A) (m : ℕ) (σ : L (Copy A m)) (k : ℕ)
    (x y : Fin k → Fin m → A) :
    inner ℂ (tensorWord (m * k) (blockWord m k x))
      (blockPower ρ m σ k (tensorWord (m * k) (blockWord m k y))) =
        ∏ i, inner ℂ (tensorWord m (x i)) (σ (tensorWord m (y i))) := by
  induction k with
  | zero =>
    simp only [blockPower, Nat.mul_zero, id_eq, Module.End.one_apply,
      word_inner, Fin.prod_univ_zero]
  | succ k ih =>
    rw [← cast_inner (Nat.mul_succ m k), ← cast_operator_apply (Nat.mul_succ m k)]
    have hop : cast (congrArg (fun j => L (Copy A j)) (Nat.mul_succ m k))
        (blockPower ρ m σ (k + 1)) = join ρ (m * k) m (blockPower ρ m σ k) σ := by
      simp only [blockPower]
      simp only [cast_eq, id_eq]
    rw [hop, cast_block_word, cast_block_word]
    rw [← join_word ρ (m * k) m, ← join_word ρ (m * k) m, join_inner, ih]
    exact (Fin.prod_univ_castSucc
      (fun i => inner ℂ (tensorWord m (x i)) (σ (tensorWord m (y i))))).symm

private theorem power_word {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (X : L A) (n : ℕ) (x : Fin n → A) :
    w42OperatorPower X n (tensorWord n x) = tensorWord n (fun i => X (x i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change TensorProduct.map X (w42OperatorPower X n)
      (x 0 ⊗ₜ[ℂ] tensorWord n _) = _
    rw [TensorProduct.map_tmul, ih]
    rfl

private theorem block_iso_power {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State A) (m k : ℕ) (σ : L (Copy A m)) :
    push (block_iso ρ m k) (w42OperatorPower σ k) = blockPower ρ m σ k := by
  let b := w42EigenBasis ρ
  apply (word_basis b (m * k)).toBasis.ext
  intro y
  apply (word_basis b (m * k)).repr.injective
  ext x
  obtain ⟨x, rfl⟩ := (block_equiv (Fin (Module.finrank ℂ A)) m k).surjective x
  obtain ⟨y, rfl⟩ := (block_equiv (Fin (Module.finrank ℂ A)) m k).surjective y
  simp only [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis]
  have hb (z : Fin k → Fin m → Fin (Module.finrank ℂ A)) :
      word_basis b (m * k) (block_equiv _ m k z) =
        block_iso ρ m k (word_basis (word_basis b m) k z) :=
    (OrthonormalBasis.equiv_apply_basis _ _ _ z).symm
  calc
    _ = inner ℂ (word_basis (word_basis b m) k x)
        (w42OperatorPower σ k (word_basis (word_basis b m) k y)) := by
      rw [hb x, hb y]
      simp [push]
    _ = ∏ i, inner ℂ (tensorWord m (fun j => b (x i j)))
        (σ (tensorWord m (fun j => b (y i j)))) := by
      simp only [word_basis_apply, power_word, word_inner]
    _ = _ := by
      simp only [word_basis_apply]
      exact (block_entry ρ m σ k (fun i j => b (x i j)) (fun i j => b (y i j))).symm

private theorem join_right_unit {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State A) (n : ℕ) (v : Copy A n) :
    w44TensorJoin ρ n 0 (v ⊗ₜ[ℂ] (ULift.up 1 : Copy A 0)) = v := by
  have h : (w44TensorJoin ρ n 0).toLinearEquiv.toLinearMap.comp
      ((TensorProduct.mk ℂ (Copy A n) (Copy A 0)).flip (ULift.up 1)) =
        LinearMap.id := by
    apply word_ext
    intro x
    change w44TensorJoin ρ n 0 (tensorWord n x ⊗ₜ[ℂ] tensorWord 0 Fin.elim0) = _
    rw [join_word]
    congr 1
    ext i
    exact Fin.append_left x Fin.elim0 i
  exact LinearMap.congr_fun h v

private theorem join_right_zero {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State A) (n : ℕ) (X : L (Copy A n)) : join ρ n 0 X 1 = X := by
  ext v
  have hi : (w44TensorJoin ρ n 0).symm v = v ⊗ₜ[ℂ] (ULift.up 1 : Copy A 0) := by
    apply (w44TensorJoin ρ n 0).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (join_right_unit ρ n v).symm
  change w44TensorJoin ρ n 0 (TensorProduct.map X 1 ((w44TensorJoin ρ n 0).symm v)) = X v
  rw [hi]
  exact (congrArg (w44TensorJoin ρ n 0)
    (TensorProduct.map_tmul X (1 : L (Copy A 0)) v (ULift.up 1))).trans
      (join_right_unit ρ n (X v))

private noncomputable def cast_iso {A : Type u} [Qudit.{u} A]
    {n m : ℕ} (h : n = m) : Copy A n ≃ₗᵢ[ℂ] Copy A m := by
  subst m
  exact LinearIsometryEquiv.refl ℂ (Copy A n)

private theorem cast_iso_apply {A : Type u} [Qudit.{u} A]
    {n m : ℕ} (h : n = m) (v : Copy A n) :
    cast_iso h v = cast (congrArg (Copy A) h) v := by
  subst m
  rfl

private theorem join_left_unit {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State A) (n : ℕ) (v : Copy A n) :
    cast_iso (Nat.zero_add n) (w44TensorJoin ρ 0 n ((ULift.up 1 : Copy A 0) ⊗ₜ[ℂ] v)) = v := by
  let U := (w44TensorJoin ρ 0 n).trans (cast_iso (Nat.zero_add n))
  have h : U.toLinearEquiv.toLinearMap.comp
      (TensorProduct.mk ℂ (Copy A 0) (Copy A n) (ULift.up 1)) = LinearMap.id := by
    apply word_ext
    intro x
    change cast_iso (Nat.zero_add n)
      (w44TensorJoin ρ 0 n (tensorWord 0 Fin.elim0 ⊗ₜ[ℂ] tensorWord n x)) = _
    rw [join_word, cast_iso_apply, cast_word (Nat.zero_add n)]
    congr 1
    ext i
    have hi : Fin.cast (Nat.zero_add n).symm i = Fin.natAdd 0 i := by
      apply Fin.ext
      exact (Nat.zero_add i.val).symm
    rw [hi, Fin.append_right]
  exact LinearMap.congr_fun h v

private theorem cast_push {A B : Type u} [Qudit.{u} A] [Qudit.{u} B]
    {n m : ℕ} (h : n = m) (U : B ≃ₗᵢ[ℂ] Copy A n) (X : L B) :
    cast (congrArg (fun j => L (Copy A j)) h) (push U X) = push (U.trans (cast_iso h)) X := by
  subst m
  rfl

private theorem join_left_zero {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State A) (n : ℕ) (X : L (Copy A n)) :
    cast (congrArg (fun j => L (Copy A j)) (Nat.zero_add n)) (join ρ 0 n 1 X) = X := by
  change cast (congrArg (fun j => L (Copy A j)) (Nat.zero_add n))
    (push (w44TensorJoin ρ 0 n) (TensorProduct.map 1 X)) = X
  rw [cast_push (Nat.zero_add n) (w44TensorJoin ρ 0 n) (TensorProduct.map 1 X)]
  let U := (w44TensorJoin ρ 0 n).trans (cast_iso (Nat.zero_add n))
  ext v
  have hi : U.symm v = (ULift.up 1 : Copy A 0) ⊗ₜ[ℂ] v := by
    apply U.injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (join_left_unit ρ n v).symm
  change U (TensorProduct.map 1 X (U.symm v)) = X v
  rw [hi]
  exact (congrArg U
    (TensorProduct.map_tmul (1 : L (Copy A 0)) X (ULift.up 1) v)).trans
      (join_left_unit ρ n (X v))

private theorem join_reference {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ γ : State A) (n m : ℕ) (X : L (Copy A n)) (Y : L (Copy A m)) :
    join ρ n m X Y = join γ n m X Y := by
  unfold GourResource.join
  rw [join_independent ρ γ]

private theorem block_reference {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ γ : State A) (m : ℕ) (σ : L (Copy A m)) (k : ℕ) :
    blockPower ρ m σ k = blockPower γ m σ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [blockPower]
    rw [ih, join_reference ρ γ]

theorem gsl_t01 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ γ : State.{u} A),
  (∀ (n : ℕ) (π : Equiv.Perm (Fin n)) (x : Fin n → A),
    perm.{u} ρ n π (tensorWord.{u} n x) = tensorWord.{u} n (fun i => x (π.symm i))) ∧
  (∀ (n : ℕ) (π : Equiv.Perm (Fin n)), perm.{u} ρ n π = perm.{u} γ n π) ∧
  (∀ (n m : ℕ) (x : Fin n → A) (y : Fin m → A),
    w44TensorJoin.{u} ρ n m (tensorWord.{u} n x ⊗ₜ[ℂ] tensorWord.{u} m y) =
      tensorWord.{u} (n+m) (Fin.append x y)) ∧
  (∀ (n m : ℕ), w44TensorJoin.{u} ρ n m = w44TensorJoin.{u} γ n m) ∧
  (∀ (n : ℕ) (X : L.{u} (Copy.{u} A n)),
    join.{u} ρ n 0 X 1 = X ∧
    cast (congrArg (fun j => L.{u} (Copy.{u} A j)) (Nat.zero_add n)) (join.{u} ρ 0 n 1 X) = X) ∧
  (∀ (m k : ℕ), ∃ U : Copy.{u} (Copy.{u} A m) k ≃ₗᵢ[ℂ] Copy.{u} A (m*k),
    (∀ x : Fin k → Fin m → A,
      U (tensorWord.{u} k (fun i => tensorWord.{u} m (x i))) =
        tensorWord.{u} (m*k) (blockWord m k x)) ∧
    ∀ σ : L.{u} (Copy.{u} A m),
      push.{u} U (w42OperatorPower.{u} σ k) = blockPower.{u} ρ m σ k) ∧
  (∀ (m : ℕ) (σ : L.{u} (Copy.{u} A m)) (n : ℕ),
    padded.{u} ρ γ m σ n =
      cast (congrArg (fun j => L.{u} (Copy.{u} A j))
        (by simpa [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div n m))
        (join.{u} γ (m*(n/m)) (n%m) (blockPower.{u} γ m σ (n/m)) (pow.{u} γ (n%m))))
:= by
  intro A _ _ ρ γ
  refine ⟨perm_word ρ, perm_independent ρ γ, join_word ρ, join_independent ρ γ,
    ?_, ?_, ?_⟩
  · intro n X
    exact ⟨join_right_zero ρ n X, join_left_zero ρ n X⟩
  · intro m k
    exact ⟨block_iso ρ m k, block_iso_word ρ m k, block_iso_power ρ m k⟩
  · intro m σ n
    unfold padded
    rw [block_reference ρ γ, join_reference ρ γ]

end GourResource

