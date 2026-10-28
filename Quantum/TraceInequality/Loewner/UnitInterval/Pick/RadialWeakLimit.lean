import Quantum.TraceInequality.Loewner.UnitInterval.Pick.CircleHerglotz

/-!
# Chapter 3 radial boundary measures and weak limits

This module contains the weak compactness step turning radial boundary measures
from the disk Poisson argument into disk-boundary Herglotz circle data.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set
open Filter
open scoped Topology
open scoped NNReal
open scoped ENNReal

noncomputable section

/-! ### Radial boundary measures and weak limits -/

/-- The boundary circle as a compact subtype. -/
abbrev UnitDiskBoundary : Type :=
  {ξ : ℂ // ξ ∈ unitDiskBoundary}

/-- The unit circle boundary is compact as a subtype. -/
instance : CompactSpace UnitDiskBoundary :=
  isCompact_iff_compactSpace.mp
    (by simpa [UnitDiskBoundary, unitDiskBoundary] using
      (isCompact_sphere (0 : ℂ) 1))

/-- The unit circle boundary is nonempty. -/
instance : Nonempty UnitDiskBoundary :=
  ⟨⟨(1 : ℂ), by simp [unitDiskBoundary]⟩⟩

/-- The unit circle boundary is a measurable subset of `ℂ`. -/
theorem unitDiskBoundary_measurableSet :
    MeasurableSet (unitDiskBoundary : Set ℂ) := by
  have hcompact : IsCompact (unitDiskBoundary : Set ℂ) := by
    simpa [unitDiskBoundary] using (isCompact_sphere (0 : ℂ) 1)
  exact hcompact.isClosed.measurableSet

/-- Points of `UnitDiskBoundary` have norm one. -/
theorem unitDiskBoundary_norm_eq_one (ξ : UnitDiskBoundary) :
    ‖(ξ : ℂ)‖ = 1 := by
  simp [unitDiskBoundary]

/-- A boundary point of the disk cannot coincide with an interior disk point. -/
private theorem unitDiskBoundaryKernel_den_ne
    {w : ℂ} (hw : w ∈ (unitDiskDomain : Set ℂ)) (ξ : UnitDiskBoundary) :
    (ξ : ℂ) - w ≠ 0 := by
  intro h
  have hξw : (ξ : ℂ) = w := sub_eq_zero.mp h
  have hξ : ‖(ξ : ℂ)‖ = 1 := unitDiskBoundary_norm_eq_one ξ
  have hw_norm : ‖w‖ < 1 := by
    simpa [unitDiskDomain, dist_eq_norm] using hw
  have : ‖w‖ = 1 := by simpa [hξw] using hξ
  linarith

/-- The disk Herglotz kernel as a continuous function on the boundary circle. -/
def unitDiskBoundaryKernel (w : ℂ) (hw : w ∈ (unitDiskDomain : Set ℂ)) :
    C(UnitDiskBoundary, ℂ) where
  toFun ξ := unitDiskCaratheodoryKernel (ξ : ℂ) w
  continuous_toFun := by
    unfold unitDiskCaratheodoryKernel
    exact (continuous_subtype_val.add continuous_const).div
      (continuous_subtype_val.sub continuous_const)
      (unitDiskBoundaryKernel_den_ne hw)

/-- The same boundary kernel as a bounded continuous function. -/
noncomputable def unitDiskBoundaryKernelBCF
    (w : ℂ) (hw : w ∈ (unitDiskDomain : Set ℂ)) :
    BoundedContinuousFunction UnitDiskBoundary ℂ :=
  BoundedContinuousFunction.mkOfCompact (unitDiskBoundaryKernel w hw)

/-- Push a boundary-subtype finite measure forward to a finite measure on `ℂ`. -/
def unitDiskBoundaryMeasureToComplex
    (μ : FiniteMeasure UnitDiskBoundary) : FiniteMeasure ℂ :=
  μ.map ((↑) : UnitDiskBoundary → ℂ)

/-- The pushed-forward boundary measure is supported on the unit circle. -/
theorem unitDiskBoundaryMeasureToComplex_support
    (μ : FiniteMeasure UnitDiskBoundary) :
    (unitDiskBoundaryMeasureToComplex μ : Measure ℂ)
        (unitDiskBoundary : Set ℂ)ᶜ = 0 := by
  rw [unitDiskBoundaryMeasureToComplex, FiniteMeasure.toMeasure_map]
  rw [Measure.map_apply continuous_subtype_val.measurable
    unitDiskBoundary_measurableSet.compl]
  simp [UnitDiskBoundary]

/-- Pushing a boundary measure to `ℂ` preserves total mass. -/
theorem unitDiskBoundaryMeasureToComplex_mass
    (μ : FiniteMeasure UnitDiskBoundary) :
    (unitDiskBoundaryMeasureToComplex μ).mass = μ.mass := by
  rw [FiniteMeasure.mass, FiniteMeasure.mass, unitDiskBoundaryMeasureToComplex]
  rw [FiniteMeasure.map_apply μ continuous_subtype_val.measurable MeasurableSet.univ]
  simp

/-- Integrating the disk Herglotz kernel after pushforward equals boundary integration. -/
theorem unitDiskBoundaryMeasureToComplex_integral_kernel
    (μ : FiniteMeasure UnitDiskBoundary) {w : ℂ}
    (hw : w ∈ (unitDiskDomain : Set ℂ)) :
    (∫ ξ : ℂ, unitDiskCaratheodoryKernel ξ w
        ∂(unitDiskBoundaryMeasureToComplex μ : Measure ℂ)) =
      ∫ ξ : UnitDiskBoundary, unitDiskBoundaryKernel w hw ξ
        ∂(μ : Measure UnitDiskBoundary) := by
  rw [unitDiskBoundaryMeasureToComplex, FiniteMeasure.toMeasure_map]
  simpa [unitDiskBoundaryKernel] using
    ((MeasurableEmbedding.subtype_coe unitDiskBoundary_measurableSet).integral_map
      (μ := (μ : Measure UnitDiskBoundary))
      (g := fun ξ : ℂ => unitDiskCaratheodoryKernel ξ w))

/-- The canonical radial parameter used in the disk proof of book Theorem 3.2. -/
def unitDiskHerglotzRadius (n : ℕ) : ℝ :=
  1 - ((n + 2 : ℕ) : ℝ)⁻¹

/-- The canonical radial parameter is positive. -/
theorem unitDiskHerglotzRadius_pos (n : ℕ) :
    0 < unitDiskHerglotzRadius n := by
  unfold unitDiskHerglotzRadius
  have hgt : (1 : ℝ) < ((n + 2 : ℕ) : ℝ) := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    norm_num
    linarith
  have hinv : (((n + 2 : ℕ) : ℝ)⁻¹) < 1 :=
    inv_lt_one_of_one_lt₀ hgt
  linarith

/-- The canonical radial parameter is strictly inside the unit disk. -/
theorem unitDiskHerglotzRadius_lt_one (n : ℕ) :
    unitDiskHerglotzRadius n < 1 := by
  unfold unitDiskHerglotzRadius
  have hpos : 0 < (((n + 2 : ℕ) : ℝ)⁻¹) := by positivity
  linarith

/-- The canonical radial parameters tend to the boundary radius `1`. -/
theorem unitDiskHerglotzRadius_tendsto_one :
    Tendsto unitDiskHerglotzRadius atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => 1 - ((n + 2 : ℕ) : ℝ)⁻¹) atTop (𝓝 1)
  have hinv :
      Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa [Function.comp_def, one_div, Nat.cast_add, add_assoc, add_comm, add_left_comm,
      show (1 : ℝ) + 1 = 2 by norm_num] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto
        (fun n : ℕ => 1 / (((n : ℝ) + 1))) atTop (𝓝 0)).comp
          (tendsto_add_atTop_nat 1))
  simpa using
    (tendsto_const_nhds (x := (1 : ℝ))).sub hinv

/-- Radial dilates using the canonical parameters converge back to the point. -/
theorem unitDiskHerglotzRadius_mul_tendsto (w : ℂ) :
    Tendsto (fun n : ℕ => (unitDiskHerglotzRadius n : ℂ) * w)
      atTop (𝓝 w) := by
  have hr :
      Tendsto (fun n : ℕ => (unitDiskHerglotzRadius n : ℂ))
        atTop (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.tendsto 1 |>.comp unitDiskHerglotzRadius_tendsto_one
  simpa using hr.mul tendsto_const_nhds

/--
Radial boundary measures supplied by the Poisson step in the proof of book
Theorem 3.2.

These measures are constructed from Theorem 3.1 by
`unitDiskRadialHerglotzFamilyData_of_theorem31RadialFamilyData`
(`RadialFamily.lean`) and the concrete radial formula in
`ConcreteRadialMeasures.lean`.  This package records the part used by the
weak-limit argument.
-/
structure UnitDiskRadialHerglotzFamilyData (G : ℂ → ℂ) where
  radialMeasure : ℕ → FiniteMeasure UnitDiskBoundary
  radialMass : ℝ≥0
  radial_mass_eq : ∀ n : ℕ, (radialMeasure n).mass = radialMass
  mass_eq : (radialMass : ENNReal) = ENNReal.ofReal (G 0).re
  formula :
    ∀ (n : ℕ) ⦃w : ℂ⦄ (hw : w ∈ (unitDiskDomain : Set ℂ)),
      G ((unitDiskHerglotzRadius n : ℂ) * w) =
        Complex.I * ((G 0).im : ℂ) +
          ∫ ξ : UnitDiskBoundary, unitDiskBoundaryKernel w hw ξ
            ∂(radialMeasure n : Measure UnitDiskBoundary)

/-- Uniformly mass-bounded boundary measures have a weakly convergent subsequence. -/
theorem exists_subseq_tendsto_unitDiskBoundaryMeasure_of_mass_le
    (μs : ℕ → FiniteMeasure UnitDiskBoundary) (C : ℝ≥0)
    (hC : ∀ n : ℕ, (μs n).mass ≤ C) :
    ∃ (μ : FiniteMeasure UnitDiskBoundary) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) := by
  classical
  have hm_in_real : ∀ n, ((μs n).mass : ℝ) ∈ Set.Icc (0 : ℝ) (C : ℝ) := by
    intro n
    exact ⟨NNReal.coe_nonneg _, hC n⟩
  rcases (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (C : ℝ))).tendsto_subseq
      hm_in_real with
    ⟨MR, hMR, φ₁, hφ₁, hmass₁R⟩
  let M : ℝ≥0 := ⟨MR, hMR.1⟩
  let μ₁ : ℕ → FiniteMeasure UnitDiskBoundary := fun n => μs (φ₁ n)
  have hmass₁' : Tendsto (fun n => (μ₁ n).mass) atTop (𝓝 M) := by
    rw [← NNReal.tendsto_coe]
    simpa [μ₁, Function.comp, M] using hmass₁R
  by_cases hM0 : M = 0
  · refine ⟨0, φ₁, hφ₁, ?_⟩
    have hmass_zero : Tendsto (fun n => (μ₁ n).mass) atTop (𝓝 (0 : ℝ≥0)) := by
      simpa [hM0] using hmass₁'
    simpa [μ₁, Function.comp] using
      (MeasureTheory.FiniteMeasure.tendsto_zero_of_tendsto_zero_mass
        (μs := μ₁) hmass_zero)
  · rcases (CompactSpace.tendsto_subseq
        (fun n => (μ₁ n).normalize)) with
      ⟨ν, φ₂, hφ₂, hnorm₂⟩
    let φ : ℕ → ℕ := fun n => φ₁ (φ₂ n)
    have hφ : StrictMono φ := hφ₁.comp hφ₂
    let μ₂ : ℕ → FiniteMeasure UnitDiskBoundary := fun n => μs (φ n)
    have hmass₂ : Tendsto (fun n => (μ₂ n).mass) atTop (𝓝 M) := by
      have hφ₂_atTop : Tendsto φ₂ atTop atTop := hφ₂.tendsto_atTop
      simpa [μ₂, μ₁, φ] using hmass₁'.comp hφ₂_atTop
    have hnorm₂' : Tendsto (fun n => (μ₂ n).normalize) atTop (𝓝 ν) := by
      simpa [μ₂, μ₁, φ, Function.comp] using hnorm₂
    let μ : FiniteMeasure UnitDiskBoundary := M • ν.toFiniteMeasure
    have hμ_mass : μ.mass = M := by
      rw [MeasureTheory.FiniteMeasure.mass]
      change (M • ν.toFiniteMeasure) Set.univ = M
      rw [MeasureTheory.FiniteMeasure.smul_apply]
      have hνuniv : ν.toFiniteMeasure Set.univ = 1 := by
        have h : ν.toFiniteMeasure.mass = 1 :=
          ProbabilityMeasure.mass_toFiniteMeasure ν
        unfold MeasureTheory.FiniteMeasure.mass at h
        exact h
      simp [hνuniv, smul_eq_mul]
    have hμ_ne0 : μ ≠ 0 := by
      have : μ.mass ≠ 0 := by simpa [hμ_mass] using hM0
      exact (MeasureTheory.FiniteMeasure.mass_nonzero_iff μ).1 this
    have hμ_norm : μ.normalize = ν := by
      have h_toFinite :
          μ.normalize.toFiniteMeasure = ν.toFiniteMeasure := by
        have hn : μ.normalize.toFiniteMeasure = μ.mass⁻¹ • μ :=
          MeasureTheory.FiniteMeasure.normalize_eq_inv_mass_smul_of_nonzero
            (μ := μ) hμ_ne0
        calc
          μ.normalize.toFiniteMeasure
              = μ.mass⁻¹ • μ := hn
          _ = M⁻¹ • (M • ν.toFiniteMeasure) := by
                simp [μ, hμ_mass]
          _ = (M⁻¹ * M) • ν.toFiniteMeasure := by
                simp [smul_smul]
          _ = (1 : ℝ≥0) • ν.toFiniteMeasure := by
                simp [inv_mul_cancel₀ hM0]
          _ = ν.toFiniteMeasure := by simp
      exact
        (MeasureTheory.ProbabilityMeasure.toFiniteMeasure_isEmbedding
          UnitDiskBoundary).injective
        h_toFinite
    have hnorm₂'' : Tendsto (fun n => (μ₂ n).normalize) atTop (𝓝 μ.normalize) := by
      simpa [hμ_norm] using hnorm₂'
    have hmass₂' : Tendsto (fun n => (μ₂ n).mass) atTop (𝓝 μ.mass) := by
      simpa [hμ_mass] using hmass₂
    have hμ₂_tendsto :
        Tendsto μ₂ atTop (𝓝 μ) :=
      MeasureTheory.FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
        (μ := μ) (μs := μ₂) hnorm₂'' hmass₂'
    refine ⟨μ, φ, hφ, ?_⟩
    simpa [μ₂, φ, Function.comp] using hμ₂_tendsto

/-- Boundary-kernel integrals converge along weak convergence of finite measures. -/
theorem unitDiskBoundaryKernel_integral_tendsto_of_measure_tendsto
    {μs : ℕ → FiniteMeasure UnitDiskBoundary}
    {μ : FiniteMeasure UnitDiskBoundary}
    (hμ : Tendsto μs atTop (𝓝 μ)) {w : ℂ}
    (hw : w ∈ (unitDiskDomain : Set ℂ)) :
    Tendsto
      (fun n : ℕ =>
        ∫ ξ : UnitDiskBoundary, unitDiskBoundaryKernel w hw ξ
          ∂(μs n : Measure UnitDiskBoundary))
      atTop
      (𝓝 (∫ ξ : UnitDiskBoundary, unitDiskBoundaryKernel w hw ξ
        ∂(μ : Measure UnitDiskBoundary))) := by
  have h :=
    (MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto
      (Ω := UnitDiskBoundary) ℂ).1 hμ (unitDiskBoundaryKernelBCF w hw)
  simpa [unitDiskBoundaryKernelBCF] using h

/-- Extract disk-boundary Herglotz circle data from radial boundary measures. -/
noncomputable def unitDiskHerglotzCircleData_of_radialFamilyData
    {G : ℂ → ℂ} (hG : UnitDiskCaratheodoryInput G)
    (data : UnitDiskRadialHerglotzFamilyData G) :
    UnitDiskHerglotzCircleData G := by
  classical
  let hex :=
    exists_subseq_tendsto_unitDiskBoundaryMeasure_of_mass_le
      data.radialMeasure data.radialMass
      (fun n => by rw [data.radial_mass_eq n])
  let ν : FiniteMeasure UnitDiskBoundary := Classical.choose hex
  let hexν := Classical.choose_spec hex
  let φ : ℕ → ℕ := Classical.choose hexν
  have hφν : StrictMono φ ∧ Tendsto (data.radialMeasure ∘ φ) atTop (𝓝 ν) :=
    Classical.choose_spec hexν
  have hφ : StrictMono φ := hφν.1
  have hν : Tendsto (data.radialMeasure ∘ φ) atTop (𝓝 ν) := hφν.2
  have hν_mass : ν.mass = data.radialMass := by
    have hlim :
        Tendsto (fun k : ℕ => (data.radialMeasure (φ k)).mass)
          atTop (𝓝 ν.mass) :=
      (MeasureTheory.FiniteMeasure.continuous_mass.tendsto ν).comp hν
    have hconst :
        Tendsto (fun _ : ℕ => data.radialMass) atTop
          (𝓝 data.radialMass) :=
      tendsto_const_nhds
    have hconst' :
        Tendsto (fun k : ℕ => (data.radialMeasure (φ k)).mass)
          atTop (𝓝 data.radialMass) := by
      have hfun :
          (fun k : ℕ => (data.radialMeasure (φ k)).mass) =
            fun _ : ℕ => data.radialMass := by
        funext k
        exact data.radial_mass_eq (φ k)
      rw [hfun]
      exact hconst
    exact tendsto_nhds_unique hlim hconst'
  refine
    { boundaryMeasure := unitDiskBoundaryMeasureToComplex ν
      boundary_support := unitDiskBoundaryMeasureToComplex_support ν
      mass_eq := ?_
      formula := ?_ }
  · calc
      ((unitDiskBoundaryMeasureToComplex ν).mass : ENNReal) = (ν.mass : ENNReal) := by
        rw [unitDiskBoundaryMeasureToComplex_mass]
      _ = (data.radialMass : ENNReal) := by rw [hν_mass]
      _ = ENNReal.ofReal (G 0).re := data.mass_eq
  · intro w hw
    have hleft :
        Tendsto (fun k : ℕ =>
          G ((unitDiskHerglotzRadius (φ k) : ℂ) * w))
          atTop (𝓝 (G w)) := by
      have hcont : ContinuousAt G w :=
        hG.analyticOn.continuousOn.continuousAt
          (unitDiskDomain_isOpen.mem_nhds hw)
      exact hcont.tendsto.comp
        ((unitDiskHerglotzRadius_mul_tendsto w).comp hφ.tendsto_atTop)
    have hright_int :
        Tendsto
          (fun k : ℕ =>
            ∫ ξ : UnitDiskBoundary, unitDiskBoundaryKernel w hw ξ
              ∂(data.radialMeasure (φ k) : Measure UnitDiskBoundary))
          atTop
          (𝓝 (∫ ξ : UnitDiskBoundary, unitDiskBoundaryKernel w hw ξ
            ∂(ν : Measure UnitDiskBoundary))) := by
      simpa [Function.comp] using
        unitDiskBoundaryKernel_integral_tendsto_of_measure_tendsto
          (μs := data.radialMeasure ∘ φ) hν hw
    have hright :
        Tendsto
          (fun k : ℕ =>
            Complex.I * ((G 0).im : ℂ) +
              ∫ ξ : UnitDiskBoundary, unitDiskBoundaryKernel w hw ξ
                ∂(data.radialMeasure (φ k) : Measure UnitDiskBoundary))
          atTop
          (𝓝 (Complex.I * ((G 0).im : ℂ) +
            ∫ ξ : UnitDiskBoundary, unitDiskBoundaryKernel w hw ξ
              ∂(ν : Measure UnitDiskBoundary))) :=
      tendsto_const_nhds.add hright_int
    have hsubtype :
        G w =
          Complex.I * ((G 0).im : ℂ) +
            ∫ ξ : UnitDiskBoundary, unitDiskBoundaryKernel w hw ξ
              ∂(ν : Measure UnitDiskBoundary) := by
      have hright_lhs :
          Tendsto (fun k : ℕ =>
            G ((unitDiskHerglotzRadius (φ k) : ℂ) * w))
            atTop
            (𝓝 (Complex.I * ((G 0).im : ℂ) +
              ∫ ξ : UnitDiskBoundary, unitDiskBoundaryKernel w hw ξ
                ∂(ν : Measure UnitDiskBoundary))) := by
        refine Tendsto.congr' ?_ hright
        exact Eventually.of_forall fun k => (data.formula (φ k) hw).symm
      exact tendsto_nhds_unique hleft hright_lhs
    calc
      G w =
          Complex.I * ((G 0).im : ℂ) +
            ∫ ξ : UnitDiskBoundary, unitDiskBoundaryKernel w hw ξ
              ∂(ν : Measure UnitDiskBoundary) := hsubtype
      _ =
          Complex.I * ((G 0).im : ℂ) +
            ∫ ξ : ℂ, unitDiskCaratheodoryKernel ξ w
              ∂(unitDiskBoundaryMeasureToComplex ν : Measure ℂ) := by
            rw [unitDiskBoundaryMeasureToComplex_integral_kernel ν hw]

/-- Producer interface for the radial-measure output of Theorem 3.1. -/
structure UnitDiskRadialHerglotzFamilyProducerFromCaratheodoryInput where
  produce :
    ∀ {G : ℂ → ℂ}, UnitDiskCaratheodoryInput G →
      UnitDiskRadialHerglotzFamilyData G

/-- Radial boundary measures and weak compactness give the circle Herglotz producer. -/
def unitDiskHerglotzCircleProducer_of_radialFamilyProducer
    (producer : UnitDiskRadialHerglotzFamilyProducerFromCaratheodoryInput) :
    UnitDiskHerglotzCircleProducerFromCaratheodoryInput where
  produce := by
    intro G hG
    exact unitDiskHerglotzCircleData_of_radialFamilyData hG
      (producer.produce hG)

end

end Quantum.TraceInequality.Loewner
