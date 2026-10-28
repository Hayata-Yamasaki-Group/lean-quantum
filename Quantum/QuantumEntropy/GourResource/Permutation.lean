/-
Representation laws of permutations.
-/
/-
CPTP property of the finite average twirl.
-/
/-
Quantum channels of the permutation representation and the twirl.
-/
/-
Freeness and invariance of the twirl.
-/
/-
Dimension of the symmetric subspace.
-/
import Quantum.QuantumEntropy.GourResource.TensorTransport
import Quantum.OperationalProbabilistic.OperationalFidelity.GSLCore
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesDecouplingNorm.GSLCoreRetained
import Quantum.QuantumEntropy.GourConditionalEntropy.ExamplesMinDefinitions.GSLCore
import Quantum.QuantumEntropy.GourQuantumRelativeEntropySemicontinuity.GSLCore
import Quantum.QuantumEntropy.PSDMoorePenroseCFC.GSLCore

open QuantumState in
local instance {H : Type*} [Qudit H] : IsScalarTower ℝ ℂ (L H) :=
  RestrictScalars.isScalarTower ℝ ℂ (L H)

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem tensorWord_ext {A B : Type u} [Qudit.{u} A] [Qudit.{u} B]
    (n : ℕ) {f g : Copy.{u} A n →ₗ[ℂ] B}
    (h : ∀ x : Fin n → A, f (tensorWord n x) = g (tensorWord n x)) : f = g := by
  induction n with
  | zero =>
      apply LinearMap.ext
      intro z
      have hz : z = z.down • (ULift.up (1 : ℂ) : Copy A 0) := by
        apply ULift.ext
        simp
      calc
        f z = f (z.down • (ULift.up (1 : ℂ) : Copy A 0)) := congrArg f hz
        _ = z.down • f (ULift.up (1 : ℂ)) := f.map_smul _ _
        _ = z.down • g (ULift.up (1 : ℂ)) := congrArg (z.down • ·) (h Fin.elim0)
        _ = g (z.down • (ULift.up (1 : ℂ) : Copy A 0)) := (g.map_smul _ _).symm
        _ = g z := congrArg g hz.symm
  | succ n ih =>
      apply TensorProduct.ext'
      intro a b
      have hab := ih
        (f := f.comp (TensorProduct.mk ℂ A (Copy A n) a))
        (g := g.comp (TensorProduct.mk ℂ A (Copy A n) a))
        (by
          intro x
          simpa [tensorWord] using h (Fin.cons a x))
      exact LinearMap.congr_fun hab b

theorem gsl_c50 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (n : ℕ),
  (∀ π τ : Equiv.Perm (Fin n),
    (perm.{u} ρ n (π*τ)).toLinearEquiv.toLinearMap =
      (perm.{u} ρ n π).toLinearEquiv.toLinearMap ∘ₗ (perm.{u} ρ n τ).toLinearEquiv.toLinearMap))
:= by
  intro A _ _ ρ n π τ
  have h := (GourResource.gsl_t01.{u} ρ ρ).1
  apply tensorWord_ext
  intro x
  change perm ρ n (π * τ) (tensorWord n x) =
    perm ρ n π (perm ρ n τ (tensorWord n x))
  rw [h, h, h]
  rfl

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem c51_scaled_kraus {H : Type u} [Qudit H]
    (U : H ≃ₗᵢ[ℂ] H) (X : L H) (c : ℝ) (hc : 0 ≤ c) :
    krausTerm ((Real.sqrt c : ℂ) • U.toLinearMap) X = c • act U X := by
  change ((Real.sqrt c : ℂ) • U.toLinearMap) ∘ₗ X ∘ₗ
      LinearMap.adjoint ((Real.sqrt c : ℂ) • U.toLinearMap) =
    c • (U.toLinearMap ∘ₗ X ∘ₗ U.symm.toLinearMap)
  rw [map_smulₛₗ, LinearIsometryEquiv.adjoint_toLinearMap_eq_symm, Complex.conj_ofReal]
  simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc, Complex.coe_smul]

private theorem c51_trace_act {H : Type u} [Qudit H]
    (U : H ≃ₗᵢ[ℂ] H) (X : L H) : Tr (act U X) = Tr X := by
  exact LinearMap.trace_conj' X U.toLinearEquiv

private theorem c51_average_channel {H : Type u} [Qudit H] (n : ℕ)
    (U : Equiv.Perm (Fin n) → H ≃ₗᵢ[ℂ] H) :
    ∃ E : CPTP H H, ∀ X,
      E.toFun X = (1 / (Nat.factorial n : ℝ)) • ∑ π, act (U π) X := by
  classical
  let V (π : Equiv.Perm (Fin n)) : L H :=
    (Real.sqrt (1 / (Nat.factorial n : ℝ)) : ℂ) • (U π).toLinearMap
  let Φ : T H H := ∑ π, krausTerm (V π)
  have hΦ : IsCompletelyPositive Φ := sum_krausTerm_isCompletelyPositive V
  have happly (X : L H) :
      Φ X = (1 / (Nat.factorial n : ℝ)) • ∑ π, act (U π) X := by
    simp only [Φ, LinearMap.sum_apply, V,
      c51_scaled_kraus _ _ _ (div_nonneg zero_le_one (Nat.cast_nonneg _)), Finset.smul_sum]
  have htrace (X : L H) : Tr (Φ X) = Tr X := by
    rw [happly, LinearMap.map_smul_of_tower, map_sum]
    simp only [c51_trace_act, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    rw [one_div_mul_cancel (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_smul]
  obtain ⟨Ψ, hΨ⟩ := hΦ
  refine ⟨{ toCompletelyPositiveMap := Ψ, trace_map := ?_ }, ?_⟩
  · intro X
    change Tr X = Tr (Ψ.toLinearMap X)
    rw [hΨ, htrace]
  · intro X
    change Ψ.toLinearMap X = _
    rw [hΨ, happly]

theorem gsl_c51 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (n : ℕ),
  ∃ E : CPTP.{u,u} (Copy.{u} A n) (Copy.{u} A n), ∀ X, E.toFun X = twirl.{u} ρ n X)
:= by
  intro A _ _ ρ n
  exact c51_average_channel n (perm ρ n)

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u


theorem gsl_c28 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (n : ℕ),
  (∀ π τ : Equiv.Perm (Fin n),
    (perm.{u} ρ n (π*τ)).toLinearEquiv.toLinearMap =
      (perm.{u} ρ n π).toLinearEquiv.toLinearMap ∘ₗ (perm.{u} ρ n τ).toLinearEquiv.toLinearMap) ∧
  ∃ E : CPTP.{u,u} (Copy.{u} A n) (Copy.{u} A n), ∀ X, E.toFun X = twirl.{u} ρ n X)
:= by
  intro A _ _ ρ n
  exact And.intro (GourResource.gsl_c50.{u} ρ n) (GourResource.gsl_c51.{u} ρ n)

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private theorem act_trans {B : Type u} [Qudit B]
    (U V : B ≃ₗᵢ[ℂ] B) (X : L B) :
    act U (act V X) = act (V.trans U) X := by
  ext x
  rfl

private theorem act_average {B : Type u} [Qudit B]
    {ι : Type} [Fintype ι] (U : B ≃ₗᵢ[ℂ] B) (c : ℝ) (X : ι → L B) :
    act U (c • ∑ i, X i) = c • ∑ i, act U (X i) := by
  ext x
  simp [act, LinearMap.smul_apply, LinearMap.sum_apply, map_sum,
    ← Complex.coe_smul]

private theorem perm_pow {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) (n : ℕ) (π : Equiv.Perm (Fin n)) :
    act (perm ρ n π) (pow ρ n) = pow ρ n := by
  classical
  let b := w42TensorBasis (w42EigenBasis ρ) n
  let e := wordPerm (Module.finrank ℂ A) n π
  have hd := (w42_tensor_spectral_dictionary.1 ρ n).1
  have hw (x : Fin n → Fin (Module.finrank ℂ A)) :
      (OPT.PMF.iid n (w42EigenPMF ρ) (e.symm x)).toReal =
        (OPT.PMF.iid n (w42EigenPMF ρ) x).toReal := by
    simp only [OPT.PMF.iid_apply_toReal]
    exact Equiv.prod_comp π (fun i => OPT.PMF.realMass (w42EigenPMF ρ) (x i))
  apply b.toBasis.ext
  intro x
  change (b.equiv b e) (w42DensityPower ρ n ((b.equiv b e).symm (b x))) =
    w42DensityPower ρ n (b x)
  rw [OrthonormalBasis.equiv_symm, OrthonormalBasis.equiv_apply_basis]
  rw [hd, map_smul, OrthonormalBasis.equiv_apply_basis, Equiv.apply_symm_apply, hd, hw]

private theorem twirl_pow {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) (n : ℕ) : twirl ρ n (pow ρ n) = pow ρ n := by
  classical
  have hn : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  simp only [twirl, perm_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp [hn]

private theorem twirl_mem {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) (F : Family A) (hF : valid ρ F) (n : ℕ) (hn : 0 < n)
    (X : L (Copy A n)) (hX : X ∈ F n) : twirl ρ n X ∈ F n := by
  classical
  have hc := (hF.2.1 n hn).2
  have hcard : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hw : ∑ _π : Equiv.Perm (Fin n), (1 / (Nat.factorial n : ℝ)) = 1 := by
    simp [Fintype.card_perm, nsmul_eq_mul, hcard]
  have hm := hc.sum_mem (t := Finset.univ)
    (w := fun _π : Equiv.Perm (Fin n) => 1 / (Nat.factorial n : ℝ))
    (z := fun π => act (perm ρ n π) X)
    (fun _ _ => by positivity) hw (fun π _ => hF.2.2.1 n hn X hX π)
  simpa only [twirl, Finset.smul_sum] using hm

private theorem twirl_symmetric {A : Type u} [Qudit A] [Nontrivial A]
    (ρ : State A) (n : ℕ)
    (hrep : ∀ π τ : Equiv.Perm (Fin n),
      (perm ρ n (π * τ)).toLinearEquiv.toLinearMap =
        (perm ρ n π).toLinearEquiv.toLinearMap ∘ₗ
          (perm ρ n τ).toLinearEquiv.toLinearMap)
    (X : L (Copy A n)) : symmetric ρ n (twirl ρ n X) := by
  classical
  intro π
  have hm (τ : Equiv.Perm (Fin n)) :
      act (perm ρ n π) (act (perm ρ n τ) X) = act (perm ρ n (π * τ)) X := by
    rw [act_trans]
    have he : (perm ρ n τ).trans (perm ρ n π) = perm ρ n (π * τ) := by
      ext x
      exact LinearMap.congr_fun (hrep π τ).symm x
    rw [he]
  unfold twirl
  rw [act_average]
  simp_rw [hm]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft π) (fun τ => act (perm ρ n τ) X)

theorem gsl_c29 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (F : Family.{u} A), valid.{u} ρ F →
  ∀ n : ℕ, 0 < n →
  twirl.{u} ρ n (pow.{u} ρ n) = pow.{u} ρ n ∧
  ∀ X ∈ F n, twirl.{u} ρ n X ∈ F n ∧ symmetric.{u} ρ n (twirl.{u} ρ n X))
:= by
  intro A _ _ ρ F hF n hn
  refine ⟨twirl_pow ρ n, ?_⟩
  intro X hX
  exact ⟨twirl_mem ρ F hF n hn X hX, twirl_symmetric ρ n (GourResource.gsl_c28.{u} ρ n).1 X⟩

end GourResource

namespace GourResource

open QuantumState QuantumChannel GourConditionalEntropy GourResource Filter Topology
open scoped TensorProduct BigOperators
universe u

private def wordSym {d n : ℕ} (x : Fin n → Fin d) : Sym (Fin d) n :=
  ⟨(List.ofFn x : Multiset (Fin d)), by simp⟩

private theorem wordSym_surjective (d n : ℕ) :
    Function.Surjective (@wordSym d n) := by
  rintro ⟨⟨l⟩, hn⟩
  change l.length = n at hn
  subst n
  refine ⟨l.get, ?_⟩
  apply Subtype.ext
  simp [wordSym, List.ofFn_get]

private theorem wordSym_perm {d n : ℕ} (π : Equiv.Perm (Fin n))
    (x : Fin n → Fin d) : wordSym (wordPerm d n π x) = wordSym x := by
  apply Subtype.ext
  exact Quotient.sound (Equiv.Perm.ofFn_comp_perm π.symm x)

private theorem wordSym_eq_perm {d n : ℕ} {x y : Fin n → Fin d}
    (h : wordSym x = wordSym y) : ∃ π : Equiv.Perm (Fin n), wordPerm d n π x = y := by
  have hp : (List.ofFn x).Perm (List.ofFn y) := Quotient.exact (congrArg Subtype.val h)
  have hs : x ∘ Tuple.sort x = y ∘ Tuple.sort y :=
    List.ofFn_injective <|
      (((Tuple.sort x).ofFn_comp_perm x).trans hp).trans
        ((Tuple.sort y).ofFn_comp_perm y).symm |>.eq_of_pairwise'
          (Tuple.monotone_sort x).sortedLE_ofFn.pairwise
          (Tuple.monotone_sort y).sortedLE_ofFn.pairwise
  refine ⟨(Tuple.sort x).symm.trans (Tuple.sort y), ?_⟩
  funext i
  simpa [wordPerm] using congrFun hs ((Tuple.sort y).symm i)

private theorem card_wordSym_le (d n : ℕ) :
    Fintype.card (Sym (Fin d) n) ≤ (n + 1) ^ d := by
  let f : Sym (Fin d) n → (Fin d → Fin (n + 1)) :=
    fun s i => ⟨s.val.count i, by
      have h := Multiset.count_le_card i s.val
      rw [s.property] at h
      exact Nat.lt_succ_of_le h⟩
  have hf : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    apply Multiset.ext.mpr
    intro i
    exact congrArg Fin.val (congrFun h i)
  simpa using Fintype.card_le_of_injective f hf

private noncomputable def coordinates {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (n : ℕ) :
    Copy.{u} A n ≃ₗ[ℂ] ((Fin n → Fin (Module.finrank ℂ A)) → ℂ) :=
  (w42TensorBasis.{u} (w42EigenBasis.{u} ρ) n).toBasis.equivFun

private theorem coordinates_perm {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (n : ℕ) (π : Equiv.Perm (Fin n)) (v : Copy.{u} A n)
    (x : Fin n → Fin (Module.finrank ℂ A)) :
    coordinates ρ n (perm ρ n π v) (wordPerm (Module.finrank ℂ A) n π x) =
      coordinates ρ n v x := by
  simp [coordinates, perm, OrthonormalBasis.equiv, wordPerm, Equiv.piCongrLeft']

private theorem mem_symSpace_iff {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (n : ℕ) (v : Copy.{u} A n) :
    v ∈ symSpace ρ n ↔ ∀ π : Equiv.Perm (Fin n), perm ρ n π v = v := by
  simp [symSpace, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

private theorem coordinates_eq_of_wordSym_eq {A : Type u} [Qudit.{u} A]
    [Nontrivial A] (ρ : State.{u} A) (n : ℕ) (v : symSpace ρ n)
    {x y : Fin n → Fin (Module.finrank ℂ A)} (h : wordSym x = wordSym y) :
    coordinates ρ n v.val x = coordinates ρ n v.val y := by
  obtain ⟨π, rfl⟩ := wordSym_eq_perm h
  have hv := (mem_symSpace_iff ρ n v.val).mp v.property π
  have hc := coordinates_perm ρ n π v.val x
  rw [hv] at hc
  exact hc.symm

private noncomputable def symLift {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (n : ℕ) :
    (Sym (Fin (Module.finrank ℂ A)) n → ℂ) →ₗ[ℂ] symSpace ρ n where
  toFun f := ⟨(coordinates ρ n).symm (fun x => f (wordSym x)), by
    apply (mem_symSpace_iff ρ n _).mpr
    intro π
    apply (coordinates ρ n).injective
    funext x
    obtain ⟨y, rfl⟩ := (wordPerm (Module.finrank ℂ A) n π).surjective x
    rw [coordinates_perm, LinearEquiv.apply_symm_apply, wordSym_perm]⟩
  map_add' f g := by
    apply Subtype.ext
    exact (coordinates ρ n).symm.map_add _ _
  map_smul' c f := by
    apply Subtype.ext
    exact (coordinates ρ n).symm.map_smul c _

private theorem symLift_injective {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (n : ℕ) : Function.Injective (symLift ρ n) := by
  intro f g h
  funext s
  obtain ⟨x, rfl⟩ := wordSym_surjective (Module.finrank ℂ A) n s
  have hc := congrArg (fun v : symSpace ρ n => coordinates ρ n v.val x) h
  simpa [symLift] using hc

private theorem symLift_surjective {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (n : ℕ) : Function.Surjective (symLift ρ n) := by
  intro v
  let r := Function.surjInv (wordSym_surjective (Module.finrank ℂ A) n)
  refine ⟨fun s => coordinates ρ n v.val (r s), ?_⟩
  apply Subtype.ext
  apply (coordinates ρ n).injective
  funext x
  change coordinates ρ n
    ((coordinates ρ n).symm (fun y => coordinates ρ n v.val (r (wordSym y)))) x = _
  rw [LinearEquiv.apply_symm_apply]
  apply coordinates_eq_of_wordSym_eq
  exact Function.surjInv_eq (wordSym_surjective (Module.finrank ℂ A) n) (wordSym x)

private theorem finrank_symSpace {A : Type u} [Qudit.{u} A] [Nontrivial A]
    (ρ : State.{u} A) (n : ℕ) :
    Module.finrank ℂ (symSpace ρ n) =
      Fintype.card (Sym (Fin (Module.finrank ℂ A)) n) := by
  let e := LinearEquiv.ofBijective (symLift ρ n)
    ⟨symLift_injective ρ n, symLift_surjective ρ n⟩
  rw [← e.finrank_eq, Module.finrank_fintype_fun_eq_card]

-- The dimension formula below uses the coordinate action `perm` directly (through `symLift`),
-- not the twirling channel of `gsl_c28`.

theorem gsl_c30 :
(∀ {A : Type u} [Qudit.{u} A] [Nontrivial A] (ρ : State.{u} A) (n : ℕ),
  Module.finrank ℂ (symSpace.{u} ρ n) = Nat.choose (n + Module.finrank ℂ A - 1) n ∧
  Module.finrank ℂ (symSpace.{u} ρ n) ≤ (n+1)^(Module.finrank ℂ A))
:= by
  intro A _ _ ρ n
  rw [finrank_symSpace]
  constructor
  · simpa [Nat.add_comm] using
      (Sym.card_sym_eq_choose (α := Fin (Module.finrank ℂ A)) n)
  · exact card_wordSym_le (Module.finrank ℂ A) n

end GourResource

