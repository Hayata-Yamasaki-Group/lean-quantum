/-
Nests the test projections P,Q for a≤b of the same commuting density pair, and publishes together the positivity, orthogonality, idempotence and commutativity of the three regions.
Proof construction: the complementary projection of the strict-positive one contains the zero eigenspace of the difference. The thresholds are compared in the same joint eigenbasis.
Proof construction: guided by QuantumChannel.densityJointBasis_mem, spectralProjector_apply_of_mem_eigenspace and spectralProjector_apply_eq_zero_of_mem_eigenspace, evaluates the sum over the eigenspaces of posProj. Each component is proved including a=b and the common kernel, and the idempotence and commutativity conclusions are not returned to the parent.
Source context: Gour, Theorem 11.4; Gour, Example 3.63; Hayashi–Yamasaki, Lemma 7.
-/
import Quantum.QuantumEntropy.GourResource.Definitions

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem posProj_projection {A : Type u} [Qudit.{u} A] (X : L A) :
    (posProj X).IsSymmetricProjection :=
  Submodule.isSymmetricProjection_starProjection _

private theorem testHi_projection {A : Type u} [Qudit.{u} A]
    (X S : L A) (a : ℝ) : (testHi X S a).IsSymmetricProjection := by
  have h := posProj_projection ((Real.rpow 2 a : ℝ) • S - X)
  exact ⟨h.isIdempotentElem.one_sub, LinearMap.IsSymmetric.id.sub h.isSymmetric⟩

private theorem posProj_apply {A : Type u} [Qudit.{u} A]
    (X : L A) (hX : X.IsSymmetric) (r : ℝ) (x : A)
    (hx : x ∈ Module.End.eigenspace X (r : ℂ)) :
    posProj X x = if 0 < r then x else 0 := by
  classical
  unfold posProj
  split_ifs with hr
  · apply Submodule.starProjection_eq_self_iff.mpr
    exact Submodule.mem_iSup_of_mem r (Submodule.mem_iSup_of_mem hr hx)
  · apply (Submodule.starProjection_apply_eq_zero_iff (K := _)).mpr
    rw [← Submodule.iInf_orthogonal]
    apply (Submodule.mem_iInf _).mpr
    intro s
    by_cases hs : 0 < s
    · rw [iSup_pos hs]
      have hne : (r : ℂ) ≠ (s : ℂ) := by
        intro hrs
        exact hr ((Complex.ofReal_injective hrs) ▸ hs)
      exact hX.orthogonalFamily_eigenspaces.isOrtho hne hx
    · simp [iSup_neg hs]

private theorem testHi_apply {A : Type u} [Qudit.{u} A]
    (R S : L A) (hR : R.IsSymmetric) (hS : S.IsSymmetric)
    (r s a : ℝ) (x : A) (hRx : R x = (r : ℂ) • x)
    (hSx : S x = (s : ℂ) • x) :
    testHi R S a x = if 0 < Real.rpow 2 a * s - r then 0 else x := by
  classical
  have hsym : ((Real.rpow 2 a : ℝ) • S - R).IsSymmetric := by
    exact (hS.smul (by simp)).sub hR
  have hx : x ∈ Module.End.eigenspace ((Real.rpow 2 a : ℝ) • S - R)
      ((Real.rpow 2 a * s - r : ℝ) : ℂ) := by
    rw [Module.End.mem_eigenspace_iff]
    change (Real.rpow 2 a : ℂ) • S x - R x = _
    simp only [hRx, hSx, Complex.ofReal_sub, Complex.ofReal_mul, sub_smul, smul_smul]
  simp only [testHi, LinearMap.sub_apply, Module.End.one_apply,
    posProj_apply _ hsym _ x hx]
  split_ifs <;> simp

private theorem eigenvalue_real {A : Type u} [Qudit.{u} A]
    (X : L A) (hX : X.IsSymmetric) (μ : Module.End.Eigenvalues X) :
    (μ.1.re : ℂ) = μ.1 :=
  RCLike.conj_eq_iff_re.mp (hX.conj_eigenvalue_eq_self μ.2)

private theorem joint_data {A : Type u} [Qudit.{u} A]
    (ρ σ : State.{u} A) (hcomm : Commute ρ.1 σ.1) :
    ∃ (e : OrthonormalBasis (Fin (Module.finrank ℂ A)) ℂ A)
      (r s : Fin (Module.finrank ℂ A) → ℝ),
      (∀ i, 0 ≤ s i) ∧ (∀ i, ρ.1 (e i) = (r i : ℂ) • e i) ∧
      (∀ i, σ.1 (e i) = (s i : ℂ) • e i) := by
  let e := densityJointBasis ρ.1 σ.1 ρ.2 σ.2 hcomm
  let idx := densityJointIndex ρ.1 σ.1 ρ.2 σ.2 hcomm
  refine ⟨e, fun i => (idx i).1.1.re, fun i => (idx i).2.1.re, ?_, ?_, ?_⟩
  · intro i
    apply eigenvalue_nonneg_of_nonneg (T := σ.1)
    · change Module.End.HasEigenvalue σ.1 ((idx i).2.1.re : ℂ)
      rw [eigenvalue_real σ.1 σ.2.1.isSymmetric (idx i).2]
      exact (idx i).2.2
    · exact σ.2.1.re_inner_nonneg_right
  · intro i
    rw [eigenvalue_real ρ.1 ρ.2.1.isSymmetric (idx i).1]
    exact Module.End.mem_eigenspace_iff.mp
      (densityJointBasis_mem ρ.1 σ.1 ρ.2 σ.2 hcomm i).1
  · intro i
    rw [eigenvalue_real σ.1 σ.2.1.isSymmetric (idx i).2]
    exact Module.End.mem_eigenspace_iff.mp
      (densityJointBasis_mem ρ.1 σ.1 ρ.2 σ.2 hcomm i).2

private theorem diagonal_commute {A : Type u} [Qudit.{u} A]
    (e : OrthonormalBasis (Fin (Module.finrank ℂ A)) ℂ A)
    (X Y : L A) (x y : Fin (Module.finrank ℂ A) → ℂ)
    (hX : ∀ i, X (e i) = x i • e i) (hY : ∀ i, Y (e i) = y i • e i) :
    Commute X Y := by
  apply e.toBasis.ext
  intro i
  change X (Y (e i)) = Y (X (e i))
  simp only [hX, hY, map_smul, smul_smul, mul_comm]

private theorem testHi_diagonal {A : Type u} [Qudit.{u} A]
    (R S : L A) (hR : R.IsSymmetric) (hS : S.IsSymmetric)
    (r s a : ℝ) (x : A) (hRx : R x = (r : ℂ) • x)
    (hSx : S x = (s : ℂ) • x) :
    testHi R S a x = (if 0 < Real.rpow 2 a * s - r then (0 : ℂ) else 1) • x := by
  rw [testHi_apply R S hR hS r s a x hRx hSx]
  split_ifs <;> simp

private theorem testHi_nested_mul {A : Type u} [Qudit.{u} A]
    (e : OrthonormalBasis (Fin (Module.finrank ℂ A)) ℂ A)
    (R S : L A) (hR : R.IsSymmetric) (hS : S.IsSymmetric)
    (r s : Fin (Module.finrank ℂ A) → ℝ)
    (hs : ∀ i, 0 ≤ s i) (hRx : ∀ i, R (e i) = (r i : ℂ) • e i)
    (hSx : ∀ i, S (e i) = (s i : ℂ) • e i)
    (a b : ℝ) (hab : a ≤ b) : testHi R S a * testHi R S b = testHi R S b := by
  classical
  apply e.toBasis.ext
  intro i
  change testHi R S a (testHi R S b (e i)) = testHi R S b (e i)
  rw [testHi_apply R S hR hS (r i) (s i) b (e i) (hRx i) (hSx i)]
  by_cases hb : 0 < Real.rpow 2 b * s i - r i
  · simp only [if_pos hb, map_zero]
  · rw [if_neg hb, testHi_apply R S hR hS (r i) (s i) a (e i) (hRx i) (hSx i)]
    apply if_neg
    have hmono : Real.rpow 2 a * s i - r i ≤ Real.rpow 2 b * s i - r i :=
      sub_le_sub_right (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hab) (hs i)) _
    exact fun ha => hb (lt_of_lt_of_le ha hmono)

private theorem symmetric_reverse_mul {A : Type u} [Qudit.{u} A]
    (P Q : L A) (hP : P.IsSymmetric) (hQ : Q.IsSymmetric)
    (hPQ : P * Q = Q) : Q * P = Q := by
  have h := congrArg LinearMap.adjoint hPQ
  simpa only [Module.End.mul_eq_comp, LinearMap.adjoint_comp,
    hP.adjoint_eq, hQ.adjoint_eq] using h

theorem gsl_y35 :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (a b : ℝ),
  Commute ρ.1 σ.1 → a ≤ b →
  let P := testHi.{u} ρ.1 σ.1 a
  let Q := testHi.{u} ρ.1 σ.1 b
  Q ≤ P ∧ Commute P Q ∧
  (1-P).IsPositive ∧ (P-Q).IsPositive ∧ Q.IsPositive ∧
  (1-P)*(P-Q)=0 ∧ (P-Q)*Q=0 ∧ (1-P)*Q=0 ∧
  P*P=P ∧ Q*Q=Q ∧ P.IsSymmetric ∧ Q.IsSymmetric ∧
  Commute P ρ.1 ∧ Commute P σ.1 ∧ Commute Q ρ.1 ∧ Commute Q σ.1
:= by
  classical
  intro A _ _ ρ σ a b hcomm hab
  dsimp only
  obtain ⟨e, r, s, hs, hR, hS⟩ := joint_data ρ σ hcomm
  let P := testHi ρ.1 σ.1 a
  let Q := testHi ρ.1 σ.1 b
  have hP : P.IsSymmetricProjection := testHi_projection ρ.1 σ.1 a
  have hQ : Q.IsSymmetricProjection := testHi_projection ρ.1 σ.1 b
  have hPQ : P * Q = Q := testHi_nested_mul e ρ.1 σ.1
    ρ.2.1.isSymmetric σ.2.1.isSymmetric r s hs hR hS a b hab
  have hQP : Q * P = Q := symmetric_reverse_mul P Q hP.isSymmetric hQ.isSymmetric hPQ
  have hrange : LinearMap.range Q ≤ LinearMap.range P :=
    (LinearMap.IsIdempotentElem.comp_eq_right_iff hP.isIdempotentElem Q).mp hPQ
  have hle : Q ≤ P := (hQ.le_iff_range_le_range hP).mpr hrange
  have hdiff : (P - Q).IsPositive := (hQ.sub_of_range_le_range hP hrange).isPositive
  have hcompl : (1 - P).IsSymmetricProjection :=
    ⟨hP.isIdempotentElem.one_sub, LinearMap.IsSymmetric.id.sub hP.isSymmetric⟩
  have hPP : P * P = P := hP.isIdempotentElem
  have hQQ : Q * Q = Q := hQ.isIdempotentElem
  have hleft : (1 - P) * (P - Q) = 0 := by
    simp only [mul_sub, sub_mul, one_mul, hPP, hPQ, sub_self]
  have hmid : (P - Q) * Q = 0 := by
    rw [sub_mul, hPQ, hQQ, sub_self]
  have houter : (1 - P) * Q = 0 := by
    rw [sub_mul, one_mul, hPQ, sub_self]
  let t : ℝ → Fin (Module.finrank ℂ A) → ℂ :=
    fun c i => if 0 < Real.rpow 2 c * s i - r i then 0 else 1
  have hT (c : ℝ) (i : Fin (Module.finrank ℂ A)) :
      testHi ρ.1 σ.1 c (e i) = t c i • e i :=
    testHi_diagonal ρ.1 σ.1 ρ.2.1.isSymmetric σ.2.1.isSymmetric
      (r i) (s i) c (e i) (hR i) (hS i)
  exact ⟨hle, hPQ.trans hQP.symm, hcompl.isPositive, hdiff, hQ.isPositive,
    hleft, hmid, houter, hPP, hQQ, hP.isSymmetric, hQ.isSymmetric,
    diagonal_commute e P ρ.1 (t a) (fun i => (r i : ℂ)) (hT a) hR,
    diagonal_commute e P σ.1 (t a) (fun i => (s i : ℂ)) (hT a) hS,
    diagonal_commute e Q ρ.1 (t b) (fun i => (r i : ℂ)) (hT b) hR,
    diagonal_commute e Q σ.1 (t b) (fun i => (s i : ℂ)) (hT b) hS⟩

end GourResource

