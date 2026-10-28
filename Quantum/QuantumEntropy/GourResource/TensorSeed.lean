/-
Recombination of copies and density property.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 5; Hayashi–Yamasaki, Lemma 6.
-/
/-
Full-support seed and lower bound for all copies.
Source context: Gour, Theorem 11.4; Hayashi–Yamasaki, Lemma 7; Hayashi–Yamasaki, Theorem 4.
-/
import Quantum.QuantumEntropy.GourResource.TensorTransport
import Quantum.QuantumEntropy.GourResource.KWTestingBridge

open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower ℝ ℂ (L H) :=
  RestrictScalars.isScalarTower ℝ ℂ (L H)

namespace GourResource


open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem gsl_y05_join_density {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (n m : ℕ)
    (X : L.{u} (Copy.{u} A n)) (Y : L.{u} (Copy.{u} A m))
    (hX : IsDensity.{u} X) (hY : IsDensity.{u} Y) :
    IsDensity.{u} (join.{u} ρ n m X Y) := by
  let U := w44TensorJoin ρ n m
  have hd := (isometryDensity U.toLinearIsometry
    (productDensity ⟨X, hX⟩ ⟨Y, hY⟩)).2
  change IsDensity (QuantumChannel.krausTerm U.toLinearMap (TensorProduct.map X Y)) at hd
  simpa only [QuantumChannel.krausTerm, LinearMap.coe_mk, AddHom.coe_mk,
    LinearIsometryEquiv.adjoint_toLinearMap_eq_symm] using hd

private theorem gsl_y05_join_pow {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (γ : State.{u} A) (n m : ℕ) :
    join.{u} γ n m (pow.{u} γ n) (pow.{u} γ m) = pow.{u} γ (n+m) := by
  classical
  apply (w42TensorBasis (w42EigenBasis γ) (n+m)).toBasis.ext
  intro z
  obtain ⟨⟨x, y⟩, rfl⟩ := (Fin.appendEquiv n m).surjective z
  simp only [OrthonormalBasis.coe_toBasis, Fin.appendEquiv, Equiv.coe_fn_mk]
  rw [(w42_tensor_spectral_dictionary.1 γ (n+m)).1 (Fin.append x y)]
  rw [← w44_tensor_join_basis γ n m x y]
  simp only [GourResource.join, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
    TensorProduct.map_tmul]
  rw [(w42_tensor_spectral_dictionary.1 γ n).1 x,
    (w42_tensor_spectral_dictionary.1 γ m).1 y]
  simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul, smul_smul]
  congr 1
  simp [Fin.prod_univ_add, Complex.ofReal_mul, mul_comm]

theorem gsl_y05 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ γ : State.{u} A) (n m : ℕ),
  join.{u} ρ n m (pow.{u} γ n) (pow.{u} γ m) = pow.{u} γ (n+m) ∧
  (∀ (X : L.{u} (Copy.{u} A n)) (Y : L.{u} (Copy.{u} A m)),
    IsDensity.{u} X → IsDensity.{u} Y → IsDensity.{u} (join.{u} ρ n m X Y)) ∧
  (∀ X : L.{u} (Copy.{u} A n), join.{u} ρ n 0 X 1 = X ∧
    cast (congrArg (fun j => L.{u} (Copy.{u} A j)) (Nat.zero_add n)) (join.{u} ρ 0 n 1 X) = X) ∧
  (∀ (x : Fin n → A) (y : Fin m → A),
    w44TensorJoin.{u} ρ n m (tensorWord.{u} n x ⊗ₜ[ℂ] tensorWord.{u} m y) =
      tensorWord.{u} (n+m) (Fin.append x y)) ∧
  w44TensorJoin.{u} ρ n m = w44TensorJoin.{u} γ n m
:= by
  intro A _ _ ρ γ n m
  obtain ⟨_, _, hpure, hbase, hzero, _, _⟩ := GourResource.gsl_t01.{u} ρ γ
  refine ⟨?_, gsl_y05_join_density ρ n m, hzero n, hpure n m, hbase n m⟩
  simpa only [GourResource.join, hbase n m] using gsl_y05_join_pow γ n m

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem diagonal_matrix {A : Type u} [Qudit A] {ι : Type} [Fintype ι]
    [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ A) (X : L A) (d : ι → ℝ)
    (hX : ∀ i, X (b i) = (d i : ℂ) • b i) :
    LinearMap.toMatrix b.toBasis b.toBasis X = Matrix.diagonal (fun i => (d i : ℂ)) := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply]
  change b.repr (X (b j)) i = _
  rw [b.repr_apply_apply, hX, inner_smul_right, b.inner_eq_ite]
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal]
  · simp [Matrix.diagonal, hij]

private theorem diagonal_det {A : Type u} [Qudit A] {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ A) (X : L A) (d : ι → ℝ)
    (hX : ∀ i, X (b i) = (d i : ℂ) • b i) :
    X.det = ∏ i, (d i : ℂ) := by
  classical
  rw [← LinearMap.det_toMatrix b.toBasis, diagonal_matrix b X d hX, Matrix.det_diagonal]

private theorem diagonal_lower_bound {A : Type u} [Qudit A] {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ A) (X : L A) (d : ι → ℝ)
    (hX : ∀ i, X (b i) = (d i : ℂ) • b i) (c : ℝ) (hc : ∀ i, c ≤ d i) :
    c • (1 : L A) ≤ X := by
  classical
  apply (LinearMap.posSemidef_toMatrix_iff b).mp
  have hs : ∀ i, (X - c • (1 : L A)) (b i) = ((d i - c : ℝ) : ℂ) • b i := by
    intro i
    rw [LinearMap.sub_apply, RCLike.real_smul_eq_coe_smul (K := ℂ),
      LinearMap.smul_apply, Module.End.one_apply, hX, Complex.ofReal_sub, sub_smul]
    rfl
  rw [diagonal_matrix b _ _ hs]
  exact (open scoped ComplexOrder in
    Matrix.PosSemidef.diagonal fun i =>
      Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr (hc i), rfl⟩)

private theorem seed_spectral_positive {A : Type u} [Qudit A] [Nontrivial A]
    (γ : State A) (hγ : IsPositiveDefinite γ.1) :
    ∀ i, 0 < (w42EigenPMF γ i).toReal := by
  classical
  have he : ∀ i, γ.1 (w42EigenBasis γ i) =
      ((w42EigenPMF γ i).toReal : ℂ) • w42EigenBasis γ i := by
    intro i
    rw [(w42_spectral_probability γ).2.2.1]
    exact γ.2.1.isSymmetric.apply_eigenvectorBasis rfl i
  have hd := hγ.2
  rw [diagonal_det (w42EigenBasis γ) γ.1 _ he] at hd
  intro i
  have hi := Finset.prod_ne_zero_iff.mp hd i (Finset.mem_univ i)
  exact lt_of_le_of_ne ENNReal.toReal_nonneg
    (Ne.symm (fun h => hi (by simp [h])))

private theorem seed_spectral_min {A : Type u} [Qudit A] [Nontrivial A]
    (γ : State A) (hγ : IsPositiveDefinite γ.1) :
    ∃ lam : ℝ, lam ∈ Set.Ioc 0 1 ∧ ∀ i, lam ≤ (w42EigenPMF γ i).toReal := by
  classical
  have hn : (Finset.univ : Finset (Fin (Module.finrank ℂ A))).Nonempty :=
    ⟨⟨0, Module.finrank_pos⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
    (fun i => (w42EigenPMF γ i).toReal) hn
  refine ⟨min 1 (w42EigenPMF γ i).toReal, ?_, ?_⟩
  · exact ⟨lt_min zero_lt_one (seed_spectral_positive γ hγ i), min_le_left _ _⟩
  · intro j
    exact (min_le_right _ _).trans (hi j (Finset.mem_univ j))

private theorem tensor_spectral_bound {A : Type u} [Qudit A] [Nontrivial A]
    (γ : State A) (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ i, lam ≤ (w42EigenPMF γ i).toReal) (n : ℕ) :
    (lam ^ n : ℝ) • (1 : L (Copy A n)) ≤ pow γ n ∧
      IsPositiveDefinite (pow γ n) := by
  classical
  have hb : ∀ x, lam ^ n ≤ (OPT.PMF.iid n (w42EigenPMF γ) x).toReal := by
    intro x
    rw [OPT.PMF.iid_apply_toReal]
    calc
      lam ^ n = ∏ _j : Fin n, lam := by simp
      _ ≤ ∏ j : Fin n, (w42EigenPMF γ (x j)).toReal :=
        Finset.prod_le_prod (fun _ _ => hlam.le) (fun j _ => hmin (x j))
  have he := (w42_tensor_spectral_dictionary.1 γ n).1
  refine ⟨diagonal_lower_bound (w42TensorBasis (w42EigenBasis γ) n)
    (pow γ n) _ he (lam ^ n) hb, (w42_tensor_spectral_dictionary.1 γ n).2.1.1, ?_⟩
  rw [diagonal_det (w42TensorBasis (w42EigenBasis γ) n) (pow γ n) _ he]
  apply Finset.prod_ne_zero_iff.mpr
  intro x _
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt ((pow_pos hlam n).trans_le (hb x)))

theorem gsl_y06 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), hyValid.{u} ρ F →
  ∃ (γ : State.{u} A) (lam : ℝ), IsPositiveDefinite.{u} γ.1 ∧
    lam ∈ Set.Ioc 0 1 ∧ ∀ n : ℕ, 0 < n →
    pow.{u} γ n ∈ F n ∧ IsDensity.{u} (pow.{u} γ n) ∧
    ((lam ^ n : ℝ) • (1 : L.{u} (Copy.{u} A n))) ≤ pow.{u} γ n ∧
    IsPositiveDefinite.{u} (pow.{u} γ n)
:= by
  intro A _ _ ρ F hF
  obtain ⟨γ, hγ, hseed⟩ := hF.2.2.2
  obtain ⟨lam, hlam, hmin⟩ := seed_spectral_min γ hγ
  have hfree : ∀ n : ℕ, 0 < n → pow γ n ∈ F n := by
    intro n
    induction n with
    | zero => intro hn; exact (Nat.lt_irrefl 0 hn).elim
    | succ n ih =>
      intro hn
      cases n with
      | zero => exact hseed
      | succ k =>
        rw [← (GourResource.gsl_y05.{u} ρ γ (k + 1) 1).1]
        exact hF.2.2.1 (k + 1) 1 (Nat.succ_pos k) (by decide)
          (pow γ (k + 1)) (ih (Nat.succ_pos k)) (pow γ 1) hseed
  refine ⟨γ, lam, hγ, hlam, ?_⟩
  intro n hn
  exact ⟨hfree n hn, (w42_tensor_spectral_dictionary.1 γ n).2.1,
    tensor_spectral_bound γ lam hlam.1 hmin n⟩

end GourResource

