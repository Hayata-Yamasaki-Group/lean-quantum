import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.I0
import Quantum.QuantumEntropy.RenyiDPI.Common.I0
import Quantum.QuantumEntropy.RenyiDPI.Common.Cone
import Quantum.QuantumEntropy.RenyiDPI.Common.Haar
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.QuasiContinuity
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.QuasiConvexity
import Quantum.QuantumEntropy.Common.PositiveDefiniteTensor
import Quantum.QuantumEntropy.Common.PositiveDefinitePerturbation
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.SingularImage
import Quantum.QuantumEntropy.RenyiDPI.Sandwiched.HiaiPetz.HaarUnitaryLM.GSLCore

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open GeneralizedPerspectiveFunction LiebAndoTrace
open scoped ComplexOrder Topology TensorProduct QuantumEntropy RenyiDPI.Sym
universe u

namespace RenyiDPI

private theorem s08_orbit_continuous
    {K E : Type u} [Qudit K] [Qudit E]
    [Nontrivial K] [Nontrivial E] (X : L (K ⊗[ℂ] E)) :
    Continuous (rightOrbit X) :=
  HaarUnitary.continuous_unitaryConj_tensor_right X

private theorem s08_integrand_continuous
    {K E : Type u} [Qudit K] [Qudit E]
    [Nontrivial K] [Nontrivial E] [Nontrivial (K ⊗[ℂ] E)]
    {α : ℝ} {X Y Z : L (K ⊗[ℂ] E)}
    (hα : 1 < α) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hZ : Z ∈ pdSetLM (ℋ := K ⊗[ℂ] E)) :
    Continuous
      (fun U => (quasiVar α (rightOrbit X U) (rightOrbit Y U) Z).re) := by
  have hcont : ContinuousOn
      (Function.uncurry (fun ρ σ : L (K ⊗[ℂ] E) => (quasiVar α ρ σ Z).re))
      ({A : L (K ⊗[ℂ] E) | 0 ≤ A} ×ˢ {A : L (K ⊗[ℂ] E) | 0 ≤ A}) :=
    quasiVar_continuousOn_nonneg_gt hα (nonneg_of_pdSetLM hZ)
  have hpair : Continuous
      (fun U : unitary (L E) => (rightOrbit X U, rightOrbit Y U)) :=
    (s08_orbit_continuous X).prodMk (s08_orbit_continuous Y)
  exact hcont.comp_continuous
    (f := fun U : unitary (L E) => (rightOrbit X U, rightOrbit Y U)) hpair
    (fun U => ⟨rightOrbit_nonneg hX U, rightOrbit_nonneg hY U⟩)

private theorem s08_integrable
    {K E : Type u} [Qudit K] [Qudit E]
    [Nontrivial K] [Nontrivial E] [Nontrivial (K ⊗[ℂ] E)]
    {α : ℝ} {X Y Z : L (K ⊗[ℂ] E)}
    (hα : 1 < α) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hZ : Z ∈ pdSetLM (ℋ := K ⊗[ℂ] E)) :
    MeasureTheory.Integrable
      (fun U => (quasiVar α (rightOrbit X U) (rightOrbit Y U) Z).re)
      (HaarUnitary.haarUnitary E) := by
  exact (s08_integrand_continuous hα hX hY hZ).integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _)
      (Set.subset_univ _))

private theorem s08_average_nonneg
    {K E : Type u} [Qudit K] [Qudit E]
    [Nontrivial K] [Nontrivial E] [Nontrivial (K ⊗[ℂ] E)]
    {X : L (K ⊗[ℂ] E)} (hX : 0 ≤ X) :
    (∫ U, rightOrbit X U ∂(HaarUnitary.haarUnitary E)) ∈
      {A : L (K ⊗[ℂ] E) | 0 ≤ A} := by
  exact (nonnegCone_convex (H := K ⊗[ℂ] E)).integral_mem
    nonnegCone_isClosed (Filter.Eventually.of_forall (rightOrbit_nonneg hX))
    (rightOrbit_integrable X)

theorem quasiVar_jensen_haar_hiaiPetz :
∀ {K E : Type u} [Qudit K] [Qudit E]
  [Nontrivial K] [Nontrivial E] [Nontrivial (K ⊗[ℂ] E)]
  {α : ℝ} {X Y Z : L (K ⊗[ℂ] E)},
  1 < α → 0 ≤ X → 0 ≤ Y → Z ∈ pdSetLM (ℋ := K ⊗[ℂ] E) →
  (quasiVar α
    (∫ U, rightOrbit X U ∂(HaarUnitary.haarUnitary E))
    (∫ U, rightOrbit Y U ∂(HaarUnitary.haarUnitary E)) Z).re ≤
      ∫ U, (quasiVar α (rightOrbit X U) (rightOrbit Y U) Z).re
        ∂(HaarUnitary.haarUnitary E) := by
  intro K E _ _ _ _ _ α X Y Z hα hX hY hZ
  exact HaarUnitary.jointly_convex_integral_le
    (nonnegCone_convex (H := K ⊗[ℂ] E)) nonnegCone_convex
    nonnegCone_isClosed nonnegCone_isClosed
    (RenyiDPI.quasiVar_jointlyConvex_nonneg_hiaiPetz hα hZ)
    (quasiVar_continuousOn_nonneg_gt hα (nonneg_of_pdSetLM hZ))
    (Filter.Eventually.of_forall (rightOrbit_nonneg hX))
    (Filter.Eventually.of_forall (rightOrbit_nonneg hY))
    (rightOrbit_integrable X) (rightOrbit_integrable Y)
    (s08_integrable hα hX hY hZ) (s08_average_nonneg hX) (s08_average_nonneg hY)

private theorem s10_average_pd
    {K E : Type u} [Qudit K] [Nontrivial K] [Qudit E] [Nontrivial E]
    {X : L (K ⊗[ℂ] E)} (hX : traceOutRight X ∈ pdSetLM (ℋ := K)) :
    rightAverage X ∈ pdSetLM (ℋ := K ⊗[ℂ] E) := by
  have hd : (0 : ℝ) < Module.finrank ℂ E := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := E))
  have hmax : ((Module.finrank ℂ E : ℂ)⁻¹ • (1 : L E)) ∈ pdSetLM (ℋ := E) := by
    simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using
      (pos_smul_one_pdSetLM (ℋ := E) (inv_pos.mpr hd))
  exact pdSetLM_tensorMap hX hmax

private theorem s10_rotated_isometry
    {H K E : Type u} [Qudit H] [Qudit K] [Qudit E]
    (V : H →ₗ[ℂ] (K ⊗[ℂ] E))
    (hV : (LinearMap.adjoint V).comp V = (1 : L H))
    (U : unitary (L E)) :
    (LinearMap.adjoint ((TensorProduct.map (1 : L K) (U : L E)).comp V)).comp
      ((TensorProduct.map (1 : L K) (U : L E)).comp V) = (1 : L H) := by
  let W : L (K ⊗[ℂ] E) := TensorProduct.map (1 : L K) (U : L E)
  have hW : LinearMap.adjoint W * W = 1 := by
    rw [← LinearMap.star_eq_adjoint]
    change star (TensorProduct.map (1 : L K) (U : L E)) *
      TensorProduct.map (1 : L K) (U : L E) = 1
    rw [LinearMap.star_eq_adjoint, TensorProduct.adjoint_map,
      ← LinearMap.star_eq_adjoint, ← LinearMap.star_eq_adjoint, star_one,
      ← TensorProduct.map_mul,
      one_mul, (Unitary.mem_iff.mp U.property).1, TensorProduct.map_one]
  change (LinearMap.adjoint (W.comp V)).comp (W.comp V) = 1
  rw [LinearMap.adjoint_comp]
  calc
    ((LinearMap.adjoint V).comp (LinearMap.adjoint W)).comp (W.comp V) =
        (LinearMap.adjoint V).comp ((LinearMap.adjoint W * W).comp V) := by
      simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]
    _ = (LinearMap.adjoint V).comp V := by
      rw [hW, Module.End.one_eq_id, LinearMap.id_comp]
    _ = 1 := hV

private theorem s10_orbit_image
    {H K E : Type u} [Qudit H] [Qudit K] [Qudit E]
    (V : H →ₗ[ℂ] (K ⊗[ℂ] E)) (A : L H) (U : unitary (L E)) :
    rightOrbit ((V.comp A).comp (LinearMap.adjoint V)) U =
      (((TensorProduct.map (1 : L K) (U : L E)).comp V).comp A).comp
        (LinearMap.adjoint ((TensorProduct.map (1 : L K) (U : L E)).comp V)) := by
  have hstar : LinearMap.adjoint (TensorProduct.map (1 : L K) (U : L E)) =
      TensorProduct.map (1 : L K) (star (U : L E)) := by
    rw [TensorProduct.adjoint_map, ← LinearMap.star_eq_adjoint,
      ← LinearMap.star_eq_adjoint, star_one]
  simp only [rightOrbit, LinearMap.adjoint_comp, hstar,
    Module.End.mul_eq_comp, LinearMap.comp_assoc]

private theorem s10_integrable
    {K E : Type u} [Qudit K] [Nontrivial K] [Qudit E] [Nontrivial E]
    [Nontrivial (K ⊗[ℂ] E)] {α : ℝ} {X Y Z : L (K ⊗[ℂ] E)}
    (hα : 1 < α) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) :
    MeasureTheory.Integrable
      (fun U ↦ (quasiVar α (rightOrbit X U) (rightOrbit Y U) Z).re)
      (HaarUnitary.haarUnitary E) := by
  have hXcont : Continuous (rightOrbit X) :=
    HaarUnitary.continuous_unitaryConj_tensor_right X
  have hYcont : Continuous (rightOrbit Y) :=
    HaarUnitary.continuous_unitaryConj_tensor_right Y
  have hcont := (quasiVar_continuousOn_nonneg_gt (α := α) (Z := Z) hα hZ).comp_continuous
    (hXcont.prodMk hYcont)
    (fun U ↦ ⟨rightOrbit_nonneg hX U, rightOrbit_nonneg hY U⟩)
  exact hcont.integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))

theorem sandwichedQuasi_haar_hiaiPetz :
∀ {H K E : Type u}
  [Qudit H] [Nontrivial H] [Qudit K] [Nontrivial K] [Qudit E] [Nontrivial E]
  (V : H →ₗ[ℂ] (K ⊗[ℂ] E)),
  (LinearMap.adjoint V).comp V = (1 : L H) →
  ∀ {α : ℝ} {ρ σ : L H},
  1 < α → ρ ∈ pdSetLM (ℋ := H) → σ ∈ pdSetLM (ℋ := H) →
  traceOutRight ((V.comp ρ).comp (LinearMap.adjoint V)) ∈ pdSetLM (ℋ := K) →
  traceOutRight ((V.comp σ).comp (LinearMap.adjoint V)) ∈ pdSetLM (ℋ := K) →
  (sandwichedQuasi α
    (rightAverage ((V.comp ρ).comp (LinearMap.adjoint V)))
    (rightAverage ((V.comp σ).comp (LinearMap.adjoint V)))).re ≤
      (sandwichedQuasi α ρ σ).re := by
  intro H K E _ _ _ _ _ _ V hV α ρ σ hα hρ hσ hρout hσout
  haveI : Nontrivial (K ⊗[ℂ] E) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by
      rw [Module.finrank_tensorProduct]
      exact Nat.mul_pos Module.finrank_pos Module.finrank_pos)
  let X : L (K ⊗[ℂ] E) := (V.comp ρ).comp (LinearMap.adjoint V)
  let Y : L (K ⊗[ℂ] E) := (V.comp σ).comp (LinearMap.adjoint V)
  have hρnn : 0 ≤ ρ := nonneg_of_pdSetLM hρ
  have hX : 0 ≤ X := (LinearMap.nonneg_iff_isPositive _).2
    (((LinearMap.nonneg_iff_isPositive ρ).1 hρnn).conj_adjoint V)
  have hY : 0 ≤ Y := (LinearMap.nonneg_iff_isPositive _).2
    (((LinearMap.nonneg_iff_isPositive σ).1 (nonneg_of_pdSetLM hσ)).conj_adjoint V)
  obtain ⟨Z, hZ, hopt⟩ :=
    RenyiDPI.exists_quasiVar_eq_quasi_pd_gt hα (s10_average_pd hρout) (s10_average_pd hσout)
  have hZnn : 0 ≤ Z := nonneg_of_pdSetLM hZ
  have hJ := RenyiDPI.quasiVar_jensen_haar_hiaiPetz hα hX hY hZ
  have htwirl (A : L (K ⊗[ℂ] E)) :
      (∫ U, rightOrbit A U ∂(HaarUnitary.haarUnitary E)) = rightAverage A :=
    HaarUnitary.twirl_eq_partialTrace_right_smul_id A
  rw [htwirl X, htwirl Y] at hJ
  have hpoint (U : unitary (L E)) :
      (quasiVar α (rightOrbit X U) (rightOrbit Y U) Z).re ≤
        (sandwichedQuasi α ρ σ).re := by
    dsimp only [X, Y]
    rw [s10_orbit_image V ρ U, s10_orbit_image V σ U]
    exact RenyiDPI.quasiVar_le_quasi_isometric_gt ((TensorProduct.map (1 : L K) (U : L E)).comp V)
      (s10_rotated_isometry V hV U) hα hρnn hσ hZnn
  have hint :
      (∫ U, (quasiVar α (rightOrbit X U) (rightOrbit Y U) Z).re
        ∂(HaarUnitary.haarUnitary E)) ≤ (sandwichedQuasi α ρ σ).re := by
    simpa only [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul] using
      (MeasureTheory.integral_mono (s10_integrable hα hX hY hZnn)
        (MeasureTheory.integrable_const (sandwichedQuasi α ρ σ).re) hpoint)
  rw [← hopt]
  exact hJ.trans hint

end RenyiDPI
