import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.Common.FaithfulApproximation
import Quantum.QuantumEntropy.SandwichedRenyiBase.NonNeg.Continuity
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.SandwichedLift.FaithfulPowerLimit
import Quantum.QuantumEntropy.HaarUnitaryLM.GSLCore

open scoped Quantum.TraceInequality.Loewner

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

private lemma s15_rpow_continuousOn_nonneg
    {H : Type u} [Qudit H] [Nontrivial H] {p : ℝ} (hp : 0 ≤ p) :
    ContinuousOn (fun A : L H => CFC.rpow A p) {A : L H | 0 ≤ A} :=
  (continuousOn_id (s := {A : L H | 0 ≤ A})).cfc_nnreal_of_mem_nhdsSet
    (s := Set.univ) (f := (· ^ p)) Filter.univ_mem
    (ha' := fun _ hA => hA) (hf := (NNReal.continuous_rpow_const hp).continuousOn)

private lemma s15_faithful_eq
    {H K : Type u} [Qudit H] [Nontrivial H] [Qudit K] [Nontrivial K]
    (E : CPTP H K) {X : L H} (hX : 0 ≤ X)
    (l : {l : ℝ // 0 < l ∧ l ≤ 1}) :
    (faithfulApprox E l.val l.property.1.le l.property.2).toFun X =
      ((1 - l.val : ℝ) : ℂ) • E.toFun X +
      ((l.val * ((Tr X).re / (Module.finrank ℂ K : ℝ)) : ℝ) : ℂ) • (1 : L K) := by
  have hTr : Tr X = ((Tr X).re : ℂ) := by
    have h := ((LinearMap.nonneg_iff_isPositive X).mp hX).trace_nonneg
    change (0 : ℂ) ≤ Tr X at h
    rw [Complex.le_def] at h
    exact Complex.ext rfl h.2.symm
  change ((1 - l.val : ℝ) : ℂ) • E.toFun X +
      (l.val : ℂ) • ((Tr X / (Module.finrank ℂ K : ℂ)) • (1 : L K)) = _
  rw [smul_smul, hTr]
  push_cast
  rfl

theorem sandwichedRenyiDiv_tendsto_faithful_gt :
∀ {H K : Type u} [Qudit H] [Nontrivial H] [Qudit K] [Nontrivial K]
  (E : CPTP H K) {α : ℝ} {ρ σ : L H},
  1 < α → 0 ≤ ρ → 0 ≤ σ → σ ≠ 0 → ρ ≠ 0 →
  SupportLE (E.toFun ρ) (E.toFun σ) →
  Filter.Tendsto
    (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
      sandwichedRenyiDiv α
        ((faithfulApprox E l.val l.property.1.le l.property.2).toFun ρ)
        ((faithfulApprox E l.val l.property.1.le l.property.2).toFun σ))
    (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (𝓝[>] (0 : ℝ)))
    (𝓝 (sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ))) := by
  intro H K _ _ _ _ E α ρ σ hα hρ hσ hσ0 hρ0 hsupp
  classical
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  have hEρ : 0 ≤ E.toFun ρ := map_nonneg E.toCompletelyPositiveMap hρ
  have hEσ : 0 ≤ E.toFun σ := map_nonneg E.toCompletelyPositiveMap hσ
  have hTrρ : (Tr ρ).re ≠ 0 :=
    ne_of_gt (QuantumEntropy.trace_re_pos_of_ne_zero hρ hρ0)
  have hEρ0 : E.toFun ρ ≠ 0 := by
    intro hz
    apply hTrρ
    rw [E.trace_map ρ, hz]
    simp
  have hd : 0 < (Module.finrank ℂ K : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℂ) (M := K)
  let cσ : ℝ := (Tr σ).re / (Module.finrank ℂ K : ℝ)
  let cρ : ℝ := (Tr ρ).re / (Module.finrank ℂ K : ℝ)
  have hcσ : 0 < cσ :=
    div_pos (QuantumEntropy.trace_re_pos_of_ne_zero hσ hσ0) hd
  have hcρ : 0 ≤ cρ :=
    div_nonneg (QuantumEntropy.trace_re_pos_of_ne_zero hρ hρ0).le hd.le
  let β : ℝ := (1 - α) / (2 * α)
  let F (l : {l : ℝ // 0 < l ∧ l ≤ 1}) :=
    faithfulApprox E l.val l.property.1.le l.property.2
  let f := Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
    (𝓝[>] (0 : ℝ))
  have hM := RenyiDPI.rpow_conj_tendsto_faithful_gt hα hEσ hEρ hsupp hcσ hcρ
  have hM' : Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        CFC.rpow ((F l).toFun σ) β * (F l).toFun ρ * CFC.rpow ((F l).toFun σ) β)
      f (𝓝 (CFC.rpow (E.toFun σ) β * E.toFun ρ * CFC.rpow (E.toFun σ) β)) := by
    have ht := hM.comp (Filter.tendsto_comap (f := fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val))
    simpa only [Function.comp_def, F, s15_faithful_eq E hρ, s15_faithful_eq E hσ,
      β, cσ, cρ, f] using ht
  have hMnn : 0 ≤ CFC.rpow (E.toFun σ) β * E.toFun ρ * CFC.rpow (E.toFun σ) β :=
    conjugate_nonneg_of_nonneg hEρ CFC.rpow_nonneg
  have hMwithin : Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        CFC.rpow ((F l).toFun σ) β * (F l).toFun ρ * CFC.rpow ((F l).toFun σ) β)
      f (𝓝[{A : L K | 0 ≤ A}]
        (CFC.rpow (E.toFun σ) β * E.toFun ρ * CFC.rpow (E.toFun σ) β)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hM', Filter.Eventually.of_forall ?_⟩
    intro l
    exact conjugate_nonneg_of_nonneg
      (map_nonneg (F l).toCompletelyPositiveMap hρ) CFC.rpow_nonneg
  have htrace : Continuous (fun A : L K => (Tr A).re) := by fun_prop
  have hQ : Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        (sandwichedQuasi α ((F l).toFun ρ) ((F l).toFun σ)).re)
      f (𝓝 (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re) := by
    have hc := (htrace.comp_continuousOn
      (s15_rpow_continuousOn_nonneg hα0.le)).continuousWithinAt hMnn
    have ht := Filter.Tendsto.comp hc hMwithin
    exact ht
  have hQ0 : (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re ≠ 0 :=
    sandwichedQuasi_re_ne_zero_of_suppLE hα hEρ hEσ hsupp hEρ0
  have hT : Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => (Tr ((F l).toFun ρ)).re)
      f (𝓝 (Tr (E.toFun ρ)).re) := by
    simpa only [← CPTP.trace_map] using
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : {l : ℝ // 0 < l ∧ l ≤ 1} => (Tr ρ).re) f (𝓝 (Tr ρ).re))
  have hT0 : (Tr (E.toFun ρ)).re ≠ 0 := by
    rwa [← E.trace_map ρ]
  exact ((Real.continuousAt_log (div_ne_zero hQ0 hT0)).tendsto.comp
    (hQ.div hT hT0)).const_mul (1 / (α - 1))

end RenyiDPI
