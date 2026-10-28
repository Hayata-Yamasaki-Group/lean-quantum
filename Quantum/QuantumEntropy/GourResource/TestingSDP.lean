/-
Shows that the minimum of the trace over W≥0 with W≥X is Tr(X₊).
Source context: Gour, Theorem 11.4.
-/
/-
Represents continuous linear functionals on the space of reals × Hermitian operators by t and the trace pairing with a Hermitian W, and obtains the dictionary between the positive cone and the SDP constraints.
Source context: Gour, Theorem 11.4.
-/
/-
For the testing SDP with ε∈(0,1), the dual value of β is attained by a nonnegative t and a positive W.
Source context: Gour, Theorem 11.4.
-/
import Quantum.QuantumEntropy.GourResource.JordanTesting
import Quantum.QuantumEntropy.GourResource.KWTestingBridge

open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower ℝ ℂ (L H) :=
  RestrictScalars.isScalarTower ℝ ℂ (L H)

namespace GourResource


open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem trace_le_of_orthogonal_parts
    {A : Type u} [Qudit.{u} A] (P N W : L.{u} A)
    (hP : P.IsSymmetric) (hN : N.IsSymmetric) (hPN : P * N = 0)
    (hW : W.IsPositive) (hD : (W - (P - N)).IsPositive) :
    (Tr P).re ≤ (Tr W).re := by
  classical
  let b := hP.eigenvectorBasis rfl
  have hNP : N * P = 0 := by
    have h := congrArg star hPN
    simpa only [star_mul, star_zero, LinearMap.star_eq_adjoint,
      hP.adjoint_eq, hN.adjoint_eq] using h
  have hdiag : ∀ i, (inner ℂ (b i) (P (b i))).re ≤
      (inner ℂ (b i) (W (b i))).re := by
    intro i
    have heig : P (b i) = (hP.eigenvalues rfl i : ℂ) • b i :=
      hP.apply_eigenvectorBasis rfl i
    by_cases hi : hP.eigenvalues rfl i = 0
    · have hPi : P (b i) = 0 := by simp only [heig, hi, Complex.ofReal_zero, zero_smul]
      simpa only [hPi, inner_zero_right, Complex.zero_re] using
        hW.re_inner_nonneg_right (b i)
    · have hNi : N (b i) = 0 := by
        have hz : N (P (b i)) = 0 :=
          congrArg (fun T : L A => T (b i)) hNP
        rw [heig, map_smul] at hz
        exact (smul_eq_zero.mp hz).resolve_left (Complex.ofReal_ne_zero.mpr hi)
      have h := hD.re_inner_nonneg_right (b i)
      simp only [LinearMap.sub_apply, hNi, sub_zero, inner_sub_right] at h
      exact sub_nonneg.mp h
  change (LinearMap.trace ℂ A P).re ≤ (LinearMap.trace ℂ A W).re
  rw [P.trace_eq_sum_inner b, W.trace_eq_sum_inner b]
  simp only [Complex.re_sum]
  exact Finset.sum_le_sum fun i _ => hdiag i

theorem gsl_c06 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (X : L.{u} A), X.IsSymmetric →
  IsLeast {r : ℝ | ∃ W : L.{u} A, W.IsPositive ∧ (W-X).IsPositive ∧ r=(Tr.{u} W).re}
    ((Tr.{u} (positivePart.{u} X)).re))
:= by
  intro A _ _ X hX
  obtain ⟨hP, hN, hXPN, hPN⟩ := GourResource.gsl_y26.{u} X hX
  constructor
  · refine ⟨positivePart X, hP, ?_, rfl⟩
    have hdiff : positivePart X - X = positivePart (-X) := by
      calc
        positivePart X - X =
            positivePart X - (positivePart X - positivePart (-X)) :=
          congrArg (fun Y => positivePart X - Y) hXPN
        _ = positivePart (-X) := sub_sub_cancel _ _
    rw [hdiff]
    exact hN
  · rintro r ⟨W, hW, hWX, rfl⟩
    apply trace_le_of_orthogonal_parts (positivePart X) (positivePart (-X)) W
      hP.isSymmetric hN.isSymmetric hPN hW
    rwa [← hXPN]

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem c07a_pairing_nonneg {A : Type u} [Qudit A] {X Y : L A}
    (hX : X.IsPositive) (hY : Y.IsPositive) : 0 ≤ pairing X Y := by
  have hY0 := (LinearMap.nonneg_iff_isPositive _).mpr hY
  have hs : IsSelfAdjoint (CFC.sqrt Y) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg Y)
  have hp : 0 ≤ CFC.sqrt Y * X * CFC.sqrt Y := by
    simpa only [hs.star_eq] using
      star_left_conjugate_nonneg ((LinearMap.nonneg_iff_isPositive _).mpr hX) (CFC.sqrt Y)
  have ht := (Complex.nonneg_iff.mp
    ((LinearMap.nonneg_iff_isPositive _).mp hp).trace_nonneg).1
  have he : Tr (CFC.sqrt Y * X * CFC.sqrt Y) = Tr (X * Y) := by
    rw [mul_assoc, LinearMap.trace_mul_comm ℂ (CFC.sqrt Y), mul_assoc,
      CFC.sqrt_mul_sqrt_self Y hY0]
  change 0 ≤ (Tr (X * Y)).re
  rwa [he] at ht

private theorem c07a_trace_outer {A : Type u} [Qudit A] (X : L A) (v : A) :
    pairing X (outer_product v v) = (inner ℂ v (X v)).re := by
  have he : X * outer_product v v = outer_product v (X v) := by
    ext z
    simp [Module.End.mul_apply, outer_product_eq_rankOne]
  rw [pairing, he, trace_outer_product]

private theorem c07a_positive_iff {A : Type u} [Qudit A] (X : L A)
    (hX : X.IsSymmetric) :
    (∀ Y : selfAdjoint (L A), Y.1.IsPositive → 0 ≤ pairing X Y.1) ↔
      X.IsPositive := by
  constructor
  · intro h
    refine ⟨hX, ?_⟩
    intro v
    have hp := (LinearMap.nonneg_iff_isPositive _).mp (outer_product_self_nonneg v)
    have hv := h ⟨outer_product v v, hp.isSelfAdjoint⟩ hp
    rw [c07a_trace_outer] at hv
    simpa only [inner_re_symm] using hv
  · intro h Y hY
    exact c07a_pairing_nonneg h hY

private theorem c07a_pairing_add_right {A : Type u} [Qudit A] (X Y Z : selfAdjoint (L A)) :
    pairing X.1 (Y + Z).1 = pairing X.1 Y.1 + pairing X.1 Z.1 := by
  simp only [pairing, AddSubgroup.coe_add, mul_add, map_add, Complex.add_re]

private theorem c07a_pairing_smul_right {A : Type u} [Qudit A] (X : selfAdjoint (L A)) (r : ℝ)
    (Y : selfAdjoint (L A)) : pairing X.1 (r • Y).1 = r • pairing X.1 Y.1 := by
  simp only [pairing, selfAdjoint.val_smul, mul_smul_comm]
  simp

private theorem c07a_pairing_add_left {A : Type u} [Qudit A] (X Y Z : selfAdjoint (L A)) :
    pairing (X + Y).1 Z.1 = pairing X.1 Z.1 + pairing Y.1 Z.1 := by
  change (Tr ((X.1 + Y.1) * Z.1)).re = _
  simp only [add_mul, map_add, Complex.add_re]
  rfl

private theorem c07a_pairing_smul_left {A : Type u} [Qudit A] (r : ℝ) (X Y : selfAdjoint (L A)) :
    pairing (r • X).1 Y.1 = r • pairing X.1 Y.1 := by
  change (Tr ((r • X.1) * Y.1)).re = r • (Tr (X.1 * Y.1)).re
  simp only [smul_mul_assoc]
  simp

-- The linearity proofs are the four `c07a_pairing_*` lemmas above (elaborated once each).
private noncomputable def c07a_traceDual {A : Type u} [Qudit A] :
    selfAdjoint (L A) →ₗ[ℝ] Module.Dual ℝ (selfAdjoint (L A)) where
  toFun X :=
    { toFun := fun Y => pairing X.1 Y.1
      map_add' := c07a_pairing_add_right X
      map_smul' := c07a_pairing_smul_right X }
  map_add' X Y := LinearMap.ext fun Z => c07a_pairing_add_left X Y Z
  map_smul' r X := LinearMap.ext fun Y => c07a_pairing_smul_left r X Y

private theorem c07a_traceDual_injective {A : Type u} [Qudit A] [Nontrivial A] :
    Function.Injective (c07a_traceDual (A := A)) := by
  intro X Y h
  have hz : c07a_traceDual (A := A) (X - Y) = 0 := by rw [map_sub, h, sub_self]
  have hv := LinearMap.congr_fun hz (X - Y)
  let Z := X - Y
  have htrace : (Tr (Z.1 * Z.1)).re = 0 := hv
  have hstar : star Z.1 = Z.1 := Z.2
  have hpos : 0 ≤ Z.1 * Z.1 := by
    simpa only [hstar] using star_mul_self_nonneg Z.1
  have hnorm := SandwichedRenyiRelativeEntropy.norm_le_re_trace_lm hpos
  rw [htrace] at hnorm
  have hsq : star Z.1 * Z.1 = 0 := by
    rw [hstar]
    exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
  have hzero : Z = 0 := Subtype.ext ((CStarRing.star_mul_self_eq_zero_iff _).mp hsq)
  exact sub_eq_zero.mp hzero

-- Surjectivity from injectivity for `V → V*`, stated for an abstract finite-dimensional space so
-- that the finrank and `FiniteDimensional` instances are not searched on `selfAdjoint (L A)`.
private theorem c07a_surj_of_inj {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] Module.Dual ℝ V) (hT : Function.Injective T) :
    Function.Surjective T :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq).symm).mp hT

private theorem c07a_trace_representation {A : Type u} [Qudit A] [Nontrivial A]
    (f : Module.Dual ℝ (selfAdjoint (L A))) :
    ∃ W : selfAdjoint (L A), ∀ Y : selfAdjoint (L A), pairing W.1 Y.1 = f Y := by
  letI : FiniteDimensional ℝ (L A) := FiniteDimensional.trans ℝ ℂ (L A)
  letI : FiniteDimensional ℝ (selfAdjoint (L A)) := by
    change FiniteDimensional ℝ (selfAdjoint.submodule ℝ (L A))
    infer_instance
  have hsurj := c07a_surj_of_inj (c07a_traceDual (A := A)) c07a_traceDual_injective
  obtain ⟨W, hW⟩ := hsurj f
  exact ⟨W, fun Y => LinearMap.congr_fun hW Y⟩

private theorem c07a_cone_dictionary {A : Type u} [Qudit A]
    (f : (ℝ × selfAdjoint (L A)) →L[ℝ] ℝ) (t : ℝ) (W : L A)
    (hW : W.IsSymmetric)
    (hf : ∀ x : ℝ × selfAdjoint (L A), f x = t * x.1 + pairing W x.2.1) :
    (∀ x : ℝ × selfAdjoint (L A), 0 ≤ x.1 → x.2.1.IsPositive → 0 ≤ f x) ↔
      0 ≤ t ∧ W.IsPositive := by
  constructor
  · intro h
    constructor
    · have ht := h (1, 0) zero_le_one LinearMap.isPositive_zero
      simpa [hf, pairing] using ht
    · apply (c07a_positive_iff W hW).mp
      intro M hM
      have hm := h (0, M) le_rfl hM
      simpa [hf] using hm
  · rintro ⟨ht, hp⟩ x hx hM
    rw [hf]
    exact add_nonneg (mul_nonneg ht hx) (c07a_pairing_nonneg hp hM)

private theorem c07a_sdp_dictionary {A : Type u} [Qudit A]
    (f : (ℝ × selfAdjoint (L A)) →L[ℝ] ℝ) (t : ℝ) (W : L A)
    (hW : W.IsSymmetric)
    (hf : ∀ x : ℝ × selfAdjoint (L A), f x = t * x.1 + pairing W x.2.1)
    (ρ σ : State A) :
    (∀ M : selfAdjoint (L A), M.1.IsPositive →
      f (pairing ρ.1 M.1, -M) ≤ pairing σ.1 M.1) ↔
      (σ.1 + W - t • ρ.1).IsPositive := by
  have hs : (σ.1 + W - t • ρ.1).IsSymmetric := by
    apply (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr
    exact (σ.2.1.isSelfAdjoint.add
      ((LinearMap.isSymmetric_iff_isSelfAdjoint _).mp hW)).sub
      ((IsSelfAdjoint.all t).smul ρ.2.1.isSelfAdjoint)
  rw [← c07a_positive_iff _ hs]
  have he : ∀ M : selfAdjoint (L A),
      pairing (σ.1 + W - t • ρ.1) M.1 =
        pairing σ.1 M.1 - f (pairing ρ.1 M.1, -M) := by
    intro M
    rw [hf]
    simp [pairing, sub_mul, add_mul]
    ring
  simp only [he, sub_nonneg]

-- A linear functional on `ℝ × V` splits along the two factors (stated for an abstract `V`).
private theorem c07a_prod_decomp {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f : (ℝ × V) →ₗ[ℝ] ℝ) (s : ℝ) (M : V) :
    f (s, M) = f (1, 0) * s + f (0, M) := by
  calc
    f (s, M) = f (s • ((1 : ℝ), (0 : V)) + (0, M)) := by
      congr 1
      simp
    _ = _ := by rw [map_add, map_smul, smul_eq_mul, mul_comm]

private theorem c07a_trace_representation_inr {A : Type u} [Qudit A] [Nontrivial A]
    (f : (ℝ × selfAdjoint (L A)) →L[ℝ] ℝ) :
    ∃ W : selfAdjoint (L A), ∀ M : selfAdjoint (L A), pairing W.1 M.1 = f (0, M) :=
  c07a_trace_representation (f.toLinearMap.comp (LinearMap.inr ℝ ℝ (selfAdjoint (L A))))

theorem gsl_c07a :
∀ {A : Type u} [Qudit.{u} A] [Nontrivial A]
  (f : (ℝ × selfAdjoint (L.{u} A)) →L[ℝ] ℝ),
  ∃ (t : ℝ) (W : L.{u} A), W.IsSymmetric ∧
    (∀ x : ℝ × selfAdjoint (L.{u} A), f x = t*x.1 + pairing.{u} W x.2.1) ∧
    ((∀ x : ℝ × selfAdjoint (L.{u} A), 0 ≤ x.1 → x.2.1.IsPositive → 0 ≤ f x) ↔
      0 ≤ t ∧ W.IsPositive) ∧
    (∀ ρ σ : State.{u} A,
      (∀ M : selfAdjoint (L.{u} A), M.1.IsPositive →
        f (pairing.{u} ρ.1 M.1, -M) ≤ pairing.{u} σ.1 M.1) ↔
      (σ.1 + W - t • ρ.1).IsPositive)
:= by
  intro A _ _ f
  obtain ⟨W, hW⟩ := c07a_trace_representation_inr f
  let t := f (1, 0)
  have hs : W.1.IsSymmetric := (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr W.2
  have hf : ∀ x : ℝ × selfAdjoint (L A), f x = t * x.1 + pairing W.1 x.2.1 := by
    rintro ⟨s, M⟩
    rw [hW M]
    exact c07a_prod_decomp f.toLinearMap s M
  exact ⟨t, W.1, hs, hf, c07a_cone_dictionary f t W.1 hs hf,
    c07a_sdp_dictionary f t W.1 hs hf⟩

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private noncomputable def c07b_cone (A : Type u) [Qudit A] :
    PointedCone ℝ (selfAdjoint (L A)) :=
  (PointedCone.positive ℝ (L A)).comap (selfAdjoint.submodule ℝ (L A)).subtype

private theorem c07b_continuous_pairing {A : Type u} [Qudit A] (X : L A) :
    Continuous (fun M : L A => pairing X M) := by
  haveI : T2Space (L A) := TopologicalSpace.t2Space_of_metrizableSpace
  exact Complex.continuous_re.comp
    (Tr.continuous_of_finiteDimensional.comp (continuous_const.mul continuous_id))

private noncomputable def c07b_pairing {A : Type u} [Qudit A] (X : L A) :
    selfAdjoint (L A) →L[ℝ] ℝ where
  toFun M := pairing X M.1
  map_add' := by intro M N; simp [pairing, mul_add]
  map_smul' := by intro r M; simp [pairing]
  cont := (c07b_continuous_pairing X).comp continuous_subtype_val

private noncomputable def c07b_constraints {A : Type u} [Qudit A] (ρ : State A) :
    selfAdjoint (L A) →L[ℝ] ℝ × selfAdjoint (L A) :=
  (c07b_pairing ρ.1).prod (-ContinuousLinearMap.id ℝ (selfAdjoint (L A)))

private noncomputable def c07b_rhs (A : Type u) [Qudit A] (ε : ℝ) :
    ℝ × selfAdjoint (L A) := (1 - ε, -⟨1, IsSelfAdjoint.one (L A)⟩)

open scoped ComplexOrder in
private theorem c07b_interior {A : Type u} [Qudit A]
    (X : selfAdjoint (L A)) (a : ℝ) (ha : 0 < a)
    (hX : (a : ℂ) • (1 : L A) ≤ X.1) :
    X ∈ interior (c07b_cone A : Set (selfAdjoint (L A))) := by
  apply mem_interior_iff_mem_nhds.mpr
  apply Metric.mem_nhds_iff.mpr
  refine ⟨a, ha, ?_⟩
  intro Y hY
  have hnorm : ‖X - Y‖ ≤ a := by
    have hd : dist Y.1 X.1 ≤ a := (show dist Y X < a from hY).le
    rw [dist_eq_norm] at hd
    change ‖X.1 - Y.1‖ ≤ a
    rwa [norm_sub_rev]
  have hbound : X.1 - Y.1 ≤ (a : ℂ) • (1 : L A) := by
    calc
      X.1 - Y.1 ≤ (‖X - Y‖ : ℂ) • (1 : L A) := by
        simpa only [Algebra.algebraMap_eq_smul_one] using
          (show IsSelfAdjoint (X - Y).1 from (X - Y).2).le_algebraMap_norm_self
      _ ≤ (a : ℂ) • (1 : L A) :=
        smul_le_smul_of_nonneg_right (by exact_mod_cast hnorm)
          (show (0 : L A) ≤ 1 from zero_le_one)
  change 0 ≤ Y.1
  exact (sub_le_self_iff _).mp (hbound.trans hX)

private theorem c07b_smul_one_nonneg {A : Type u} [Qudit A] (c : ℝ) (hc : 0 ≤ c) :
    0 ≤ c • (1 : L A) := smul_nonneg hc zero_le_one

private theorem c07b_slater_sub {A : Type u} [Qudit A] (ε : ℝ) :
    -((1 - ε / 2) • (1 : L A)) - -(1 : L A) = (ε / 2) • (1 : L A) := by module

private theorem c07b_mem_interior_prod {A : Type u} [Qudit A] (x : ℝ × selfAdjoint (L A))
    (h1 : 0 < x.1) (h2 : x.2 ∈ interior (c07b_cone A : Set (selfAdjoint (L A)))) :
    x ∈ interior (((PointedCone.positive ℝ ℝ).prod (c07b_cone A) :
        PointedCone ℝ (ℝ × selfAdjoint (L A))) : Set (ℝ × selfAdjoint (L A))) := by
  change x ∈ interior ((Set.Ici (0 : ℝ)) ×ˢ (c07b_cone A : Set (selfAdjoint (L A))))
  rw [interior_prod_eq, interior_Ici]
  exact ⟨h1, h2⟩

private theorem c07b_slater {A : Type u} [Qudit A]
    (ρ : State A) (ε : ℝ) (hε : ε ∈ Set.Ioo 0 1) :
    ∃ M ∈ c07b_cone A, c07b_constraints ρ M - c07b_rhs A ε ∈
      interior (((PointedCone.positive ℝ ℝ).prod (c07b_cone A) :
        PointedCone ℝ (ℝ × selfAdjoint (L A))) : Set (ℝ × selfAdjoint (L A))) := by
  let M : selfAdjoint (L A) := (1 - ε / 2) • ⟨1, IsSelfAdjoint.one (L A)⟩
  refine ⟨M, ?_, c07b_mem_interior_prod _ ?_ ?_⟩
  · change 0 ≤ (1 - ε / 2) • (1 : L A)
    exact c07b_smul_one_nonneg _ (by linarith [hε.2])
  · have hpair : pairing ρ.1 M.1 = 1 - ε / 2 := by
      simp [M, pairing, ρ.2.2]
    change 0 < pairing ρ.1 M.1 - (1 - ε)
    rw [hpair]
    linarith [hε.1]
  · apply c07b_interior _ (ε / 2) (by linarith [hε.1])
    change (↑(ε / 2) : ℂ) • (1 : L A) ≤
      -((1 - ε / 2) • (1 : L A)) - -(1 : L A)
    rw [c07b_slater_sub ε]
    exact le_rfl

private theorem c07b_beta_le {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : State A) (ε : ℝ) (M : L A) (hM : effect M)
    (hacc : 1 - ε ≤ pairing ρ.1 M) : beta ρ.1 σ.1 ε ≤ pairing σ.1 M := by
  have hcont := c07b_continuous_pairing σ.1
  have hb := ((GourResource.gsl_b01.{u}.2.2 (A := A)).2.image hcont).bddBelow
  unfold beta
  apply csInf_le
  · apply hb.mono
    rintro r ⟨N, hN, _, rfl⟩
    exact ⟨N, hN, rfl⟩
  · exact ⟨M, hM, hacc, rfl⟩

private theorem c07b_feasible {A : Type u} [Qudit A] (ρ : State A) (ε : ℝ)
    (M : selfAdjoint (L A)) (hM : effect M.1) (hacc : 1 - ε ≤ pairing ρ.1 M.1) :
    c07b_constraints ρ M - c07b_rhs A ε ∈
      (PointedCone.positive ℝ ℝ).prod (c07b_cone A) := by
  change 0 ≤ pairing ρ.1 M.1 - (1 - ε) ∧ 0 ≤ -M.1 - -(1 : L A)
  constructor
  · exact sub_nonneg.mpr hacc
  · simpa only [sub_neg_eq_add, neg_add_eq_sub] using
      (LinearMap.nonneg_iff_isPositive (1 - M.1)).mpr hM.2

private theorem c07b_feasible_le {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : State A) (ε : ℝ) (N : selfAdjoint (L A)) (hN : N ∈ c07b_cone A)
    (hcon : c07b_constraints ρ N - c07b_rhs A ε ∈
      (PointedCone.positive ℝ ℝ).prod (c07b_cone A)) :
    beta ρ.1 σ.1 ε ≤ c07b_pairing σ.1 N := by
  change 0 ≤ pairing ρ.1 N.1 - (1 - ε) ∧ 0 ≤ -N.1 - -(1 : L A) at hcon
  apply c07b_beta_le ρ σ ε N.1
  · refine ⟨(LinearMap.nonneg_iff_isPositive _).mp hN, ?_⟩
    apply (LinearMap.nonneg_iff_isPositive _).mp
    simpa only [sub_neg_eq_add, neg_add_eq_sub] using hcon.2
  · exact sub_nonneg.mp hcon.1

private theorem c07b_dual_functional {A : Type u} [Qudit A] [Nontrivial A]
    (ρ σ : State A) (ε : ℝ) (hε : ε ∈ Set.Ioo 0 1) :
    ∃ f : (ℝ × selfAdjoint (L A)) →L[ℝ] ℝ,
      (∀ x : ℝ × selfAdjoint (L A), 0 ≤ x.1 → x.2.1.IsPositive → 0 ≤ f x) ∧
      (∀ M : selfAdjoint (L A), M.1.IsPositive →
        f (pairing ρ.1 M.1, -M) ≤ pairing σ.1 M.1) ∧
      f (c07b_rhs A ε) = beta ρ.1 σ.1 ε := by
  letI : NormedSpace ℝ (selfAdjoint (L A)) :=
    inferInstanceAs (NormedSpace ℝ (selfAdjoint.submodule ℝ (L A)))
  obtain ⟨M, hM, hacc, hβ⟩ :=
    GourResource.gsl_b02.{u}.2.2.2.1 ρ σ ε ⟨hε.1.le, hε.2⟩
  let Mstar : selfAdjoint (L A) :=
    ⟨M, (LinearMap.isSymmetric_iff_isSelfAdjoint M).mp hM.1.isSymmetric⟩
  have hm : Mstar ∈ c07b_cone A :=
    (LinearMap.nonneg_iff_isPositive M).mpr hM.1
  have hc := c07b_feasible ρ ε Mstar hM hacc
  have hmin (N : selfAdjoint (L A)) (hN : N ∈ c07b_cone A)
      (hcon : c07b_constraints ρ N - c07b_rhs A ε ∈
        (PointedCone.positive ℝ ℝ).prod (c07b_cone A)) :
      c07b_pairing σ.1 Mstar ≤ c07b_pairing σ.1 N := by
    change pairing σ.1 M ≤ _
    rw [hβ]
    exact c07b_feasible_le ρ σ ε N hN hcon
  obtain ⟨f, hf, hdom, heq⟩ := SandwichedRenyiRelativeEntropy.linear_conic_dual_attained
    (c07b_cone A) ((PointedCone.positive ℝ ℝ).prod (c07b_cone A))
    (c07b_constraints ρ) (c07b_pairing σ.1) (c07b_rhs A ε) Mstar hm hc hmin
    (c07b_slater ρ ε hε)
  refine ⟨f, ?_, ?_, heq.trans hβ⟩
  · intro x hx hX
    exact hf x ⟨hx, (LinearMap.nonneg_iff_isPositive _).mpr hX⟩
  · intro N hN
    exact hdom N ((LinearMap.nonneg_iff_isPositive _).mpr hN)

-- Slater and the conic duality lemma supply the dual witness.

theorem gsl_c07b :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ σ : State.{u} A) (ε : ℝ), ε ∈ Set.Ioo 0 1 →
  ∃ (t : ℝ) (W : L.{u} A), 0 ≤ t ∧ W.IsPositive ∧
    (σ.1 + W - t • ρ.1).IsPositive ∧
    beta.{u} ρ.1 σ.1 ε = (1-ε)*t - (Tr.{u} W).re)
:= by
  intro A _ _ ρ σ ε hε
  obtain ⟨f, hf, hbound, heq⟩ := c07b_dual_functional ρ σ ε hε
  obtain ⟨t, W, _, hrep, hpos, hdom⟩ := GourResource.gsl_c07a.{u} f
  obtain ⟨ht, hW⟩ := hpos.mp hf
  refine ⟨t, W, ht, hW, (hdom ρ σ).mp hbound, ?_⟩
  rw [← heq, hrep]
  simp [c07b_rhs, pairing, sub_eq_add_neg, mul_comm]

end GourResource

