import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
-- Projections identify normal idempotents with self-adjoint idempotents in C*-algebras.
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Algebra.Order.Star.Pi
-- Matrix-block algebra automorphisms are inner after identifying matrices with endomorphisms.
import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Artinian.Ring
-- Complete orthogonal idempotent families package the coordinate block projections.
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Topology.Order.Basic
import Quantum.TraceInequality.HiaiPetz.LownerHeinzTheorem
import Quantum.TraceInequality.LownerHeinzTheorem
import Quantum.TraceInequality.Loewner.HalfLine.Convexity
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Primitives
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Transport
import Quantum.Analysis.CStar.FiniteDimensionalStructure.EndpointOrder
import Quantum.Analysis.CStar.FiniteDimensionalStructure.QuotientTransport
import Quantum.Analysis.CStar.FiniteDimensionalStructure.BlockDecomposition
import Quantum.Analysis.CStar.FiniteDimensionalStructure.CornerAlgebras
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Implementers
import Quantum.Analysis.CStar.FiniteDimensionalStructure.TraceRepair
import Quantum.Analysis.CStar.FiniteDimensionalStructure.CornerNormalization
import Quantum.Analysis.CStar.FiniteDimensionalStructure.ProductAssembly
import Quantum.Analysis.CStar.FiniteDimensionalStructure.Classification
import Quantum.TraceInequality.Loewner.HalfLine.ClosedPositiveCFCReverse
import Quantum.TraceInequality.Loewner.HalfLine.Decreasing.Basic
import Quantum.TraceInequality.Loewner.HalfLine.Decreasing.EndpointEquivalence
import Quantum.TraceInequality.Loewner.HalfLine.Decreasing.ResolventKuboAndo

-- AH1 collects the theorem-facing matrix-order bridge statements on the positive ray.

/-!
# Positive-ray AH1 matrix-order bridge

This file contains the finite-dimensional matrix-order part of Carlen's
AH1 argument on the positive ray.  Most bridges are stated for abstract matrix
assignments `G,H`; the final wrappers name the concrete CFC realization
`G n X = g(X)` and its quadratic-form twist.
-/

namespace Quantum.TraceInequality.Loewner

universe u

open scoped MatrixOrder ComplexOrder CStarAlgebra FinMatrixCStar
open scoped Topology
open Filter
open Matrix

section PositiveRayEndpointQuotientCFC

/-- The bounded-operator algebra on `EuclideanSpace ℂ (Fin n)` has a real continuous functional
calculus for self-adjoint elements. -/
noncomputable local instance
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))] :
    ContinuousFunctionalCalculus ℝ
      ((EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- Nonnegative bounded operators on `EuclideanSpace ℂ (Fin n)` have nonnegative real spectrum. -/
noncomputable local instance
    {n : ℕ} [Nontrivial (EuclideanSpace ℂ (Fin n))] :
    NonnegSpectrumClass ℝ
      ((EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) := inferInstance

end PositiveRayEndpointQuotientCFC

/-! ### Endpoint quotient right-continuity and scalar twist control -/
/--
Closed positive-ray matrix CFC convexity and endpoint linear control give a
finite right-continuous endpoint quotient.
-/
theorem exists_endpointQuotient_rightContinuous_of_closedMatrixConvex_endpointControl
    {h : ℝ → ℝ}
    (hclosed : PositiveRayClosedMatrixOperatorConvex (positiveRayMatrixCfc h))
    (hlin : PositiveRayEndpointLinearControl (fun x : ℝ => h x - h 0)) :
    ∃ d : ℝ,
      Tendsto (positiveRayEndpointQuotient h d) (𝓝[>] (0 : ℝ)) (𝓝 d) ∧
      (∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
        h x = h 0 + x * positiveRayEndpointQuotient h d x) := by
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) h :=
    positiveRayScalarConvexOn_Ici_of_closedMatrixOperatorConvex hclosed
  rcases PositiveRayEndpointLinearControl.exists_pos_interval_bound hlin with
    ⟨C, δ, _hC, hδ, hbound⟩
  let d : ℝ := sInf ((slope h 0) '' Set.Ioo (0 : ℝ) δ)
  refine ⟨d, ?_, ?_⟩
  · have hmono_full :
        MonotoneOn (slope h 0) {x ∈ Set.Ici (0 : ℝ) | 0 < x} :=
      hconv.monotoneOn_slope_gt (by simp)
    have hmono : MonotoneOn (slope h 0) (Set.Ioo (0 : ℝ) δ) := by
      intro x hx y hy hxy
      exact hmono_full ⟨hx.1.le, hx.1⟩ ⟨hy.1.le, hy.1⟩ hxy
    have hnonempty : (Set.Ioo (0 : ℝ) δ).Nonempty :=
      Set.nonempty_Ioo.mpr hδ
    have hbdd : BddBelow ((slope h 0) '' Set.Ioo (0 : ℝ) δ) := by
      refine ⟨0, ?_⟩
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      have hnum : 0 ≤ h x - h 0 := (hbound hx).1
      rw [slope_def_field]
      exact div_nonneg hnum (sub_nonneg.mpr hx.1.le)
    have hslope :
        Tendsto (slope h 0) (𝓝[>] (0 : ℝ)) (𝓝 d) := by
      simpa [d] using
        MonotoneOn.tendsto_nhdsWithin_Ioo_right hnonempty hmono hbdd
    have hquot_eq_slope :
        positiveRayEndpointQuotient h d =ᶠ[𝓝[>] (0 : ℝ)] slope h 0 := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hxpos : 0 < x := by simpa using hx
      have hxne : x ≠ 0 := ne_of_gt hxpos
      simp [positiveRayEndpointQuotient, hxne, slope_def_field]
    exact hslope.congr' hquot_eq_slope.symm
  · intro x hx
    have hxpos : 0 < x := by simpa using hx
    have hxne : x ≠ 0 := ne_of_gt hxpos
    simp [positiveRayEndpointQuotient, hxne]
    field_simp [hxne]
    ring

/-- Scalar value extracted from a one-dimensional matrix assignment. -/
noncomputable def positiveRayScalarQFormValue
    (G : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n) (x : ℝ) : ℝ :=
  positiveRayQForm (G 1 (positiveRayScalarMatrix x)) (positiveRayScalarVector 1)

/-- For `x > 0`, evaluating the positive-ray matrix CFC of a scalar function `g` on the
one-dimensional scalar model recovers `g(x)`. [carlen2022] -/
lemma positiveRayMatrixCfc_scalarQFormValue {g : ℝ → ℝ} {x : ℝ} (hx : 0 < x) :
    g x = positiveRayScalarQFormValue (positiveRayMatrixCfc g) x := by
  symm
  unfold positiveRayScalarQFormValue
  rw [positiveRayMatrixCfc_scalarMatrix (g := g) hx]
  exact positiveRayQForm_scalarMatrix (g x)

/-- The scalar `x^2`-twist of a one-dimensional matrix assignment. -/
noncomputable def positiveRayScalarQFormTwist
    (G : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n) (x : ℝ) : ℝ :=
  x^2 * positiveRayScalarQFormValue G x

/--
The scalar `ε = x / 2` endpoint estimate extracted from Carlen's AH1 joint
convexity argument.

The conclusion is the linear control needed at the endpoint for
`x ↦ x^2 * g(x)`.  The constant is `2 * g(1)`, which is sufficient for the
endpoint argument and avoids a limiting `ε ↓ 0` step.
-/
theorem positiveRayEndpointLinearControl_scalarTwist_of_qformJointConvex
    {G : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n}
    (hjoint : PositiveRayMatrixQFormJointConvex G)
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ positiveRayScalarQFormValue G x) :
    PositiveRayEndpointLinearControl (positiveRayScalarQFormTwist G) := by
  let g1 : ℝ := positiveRayScalarQFormValue G 1
  refine ⟨2 * g1, mul_nonneg zero_le_two (hnonneg 1 zero_lt_one), ?_⟩
  have hsmall : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < 1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with x hxpos hxlt1
  have hx0 : 0 < x := by simpa using hxpos
  have hxlt2 : x < 2 := by linarith
  have hden_pos : 0 < 2 - x := by linarith
  have hden_ne : 2 - x ≠ 0 := by linarith
  let θ : ℝ := x / (2 - x)
  have hθpos : 0 < θ := by
    dsimp [θ]
    exact div_pos hx0 hden_pos
  have hθ0 : 0 ≤ θ := hθpos.le
  have hθ1 : θ ≤ 1 := by
    dsimp [θ]
    rw [div_le_one (by linarith)]
    linarith
  have hhalf_pos : 0 < x / 2 := by positivity
  have hcombo : θ * 1 + (1 - θ) * (x / 2) = x := by
    dsimp [θ]
    field_simp [hden_ne]
    ring_nf
  have hq := hjoint
    (n := 1)
    (X := positiveRayScalarMatrix 1)
    (Y := positiveRayScalarMatrix (x / 2))
    (v := positiveRayScalarVector 1)
    (w := positiveRayScalarVector 0)
    (θ := θ)
    (positiveRayScalarMatrix_posDef zero_lt_one)
    (positiveRayScalarMatrix_posDef hhalf_pos)
    hθ0 hθ1
  rw [positiveRayScalarMatrix_convexCombo, hcombo,
    positiveRayVectorConvexCombo_scalar_zero,
    positiveRayQForm_scalarVector,
    positiveRayQForm_scalarVector_zero] at hq
  have hθgx :
      θ * positiveRayScalarQFormValue G x ≤ positiveRayScalarQFormValue G 1 := by
    have hq' :
        θ * (θ * positiveRayScalarQFormValue G x) ≤
          θ * positiveRayScalarQFormValue G 1 := by
      simpa [positiveRayScalarQFormValue, pow_two, mul_assoc] using hq
    exact le_of_mul_le_mul_of_pos_left hq' hθpos
  have hxgx :
      x * positiveRayScalarQFormValue G x ≤ (2 - x) * positiveRayScalarQFormValue G 1 := by
    have hθgx' := hθgx
    dsimp [θ] at hθgx'
    have hrewrite :
        x / (2 - x) * positiveRayScalarQFormValue G x =
          (x * positiveRayScalarQFormValue G x) / (2 - x) := by
      ring
    rw [hrewrite] at hθgx'
    have hmul := (div_le_iff₀ hden_pos).mp hθgx'
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
  have hg1_nonneg : 0 ≤ positiveRayScalarQFormValue G 1 :=
    hnonneg 1 zero_lt_one
  constructor
  · unfold positiveRayScalarQFormTwist
    exact mul_nonneg (sq_nonneg x) (hnonneg x hx0)
  · unfold positiveRayScalarQFormTwist
    have hupper1 :
        x * (x * positiveRayScalarQFormValue G x) ≤
          x * ((2 - x) * positiveRayScalarQFormValue G 1) :=
      mul_le_mul_of_nonneg_left hxgx hx0.le
    have hfactor :
        (2 - x) * positiveRayScalarQFormValue G 1 ≤
          2 * positiveRayScalarQFormValue G 1 := by
      exact mul_le_mul_of_nonneg_right (by linarith) hg1_nonneg
    have hupper2 :
        x * ((2 - x) * positiveRayScalarQFormValue G 1) ≤
          x * (2 * positiveRayScalarQFormValue G 1) :=
      mul_le_mul_of_nonneg_left hfactor hx0.le
    calc
      x^2 * positiveRayScalarQFormValue G x =
          x * (x * positiveRayScalarQFormValue G x) := by ring
      _ ≤ x * ((2 - x) * positiveRayScalarQFormValue G 1) := hupper1
      _ ≤ x * (2 * positiveRayScalarQFormValue G 1) := hupper2
      _ = (2 * g1) * x := by
            simp [g1]
            ring

/--
If a positive-ray scalar function has endpoint linear control and is assigned
the value `0` at the endpoint, then it is right-continuous at the endpoint.
-/
theorem positiveRayEndpointTendsto_zero_of_linearControl
    {h : ℝ → ℝ}
    (h0 : h 0 = 0)
    (hlin : PositiveRayEndpointLinearControl h) :
    Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0)) := by
  rw [h0]
  rcases hlin with ⟨C, _hC, hbound⟩
  have hx : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hCx : Tendsto (fun x : ℝ => C * x) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hx.const_mul C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hCx ?_ ?_
  · filter_upwards [hbound] with x hx
    exact hx.1
  · filter_upwards [hbound] with x hx
    exact hx.2

/--
For the scalar `x^2`-twist extracted from a jointly convex positive-ray
matrix assignment, the endpoint value at `0` is `0` and the right limit is
also `0`.
-/
theorem positiveRayScalarQFormTwist_tendsto_zero_of_qformJointConvex
    {G : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n}
    (hjoint : PositiveRayMatrixQFormJointConvex G)
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ positiveRayScalarQFormValue G x) :
    Tendsto (positiveRayScalarQFormTwist G) (𝓝[>] (0 : ℝ))
      (𝓝 ((positiveRayScalarQFormTwist G) 0)) := by
  have h0 : positiveRayScalarQFormTwist G 0 = 0 := by
    simp [positiveRayScalarQFormTwist]
  exact positiveRayEndpointTendsto_zero_of_linearControl h0
    (positiveRayEndpointLinearControl_scalarTwist_of_qformJointConvex hjoint hnonneg)

/--
Transfer the endpoint right-continuity of the scalar `x^2`-twist to any
function that has endpoint value `0` and agrees with it on a right
neighborhood of `0`.
-/
theorem positiveRayEndpointTendsto_zero_of_scalarTwist_eventualEq
    {G : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n} {h : ℝ → ℝ}
    (hjoint : PositiveRayMatrixQFormJointConvex G)
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ positiveRayScalarQFormValue G x)
    (h0 : h 0 = 0)
    (heq : h =ᶠ[𝓝[>] (0 : ℝ)] positiveRayScalarQFormTwist G) :
    Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (h 0)) := by
  have htwist0 : positiveRayScalarQFormTwist G 0 = 0 := by
    simp [positiveRayScalarQFormTwist]
  have htwist :
      Tendsto (positiveRayScalarQFormTwist G) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa [htwist0] using
      positiveRayScalarQFormTwist_tendsto_zero_of_qformJointConvex hjoint hnonneg
  have hh : Tendsto h (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    htwist.congr' heq.symm
  simpa [h0] using hh

/-! ### Xsq endpoint extension and closed matrix CFC convexity -/
/-- Extend `x ↦ x^2 * g x` to the endpoint by the value `0`. -/
noncomputable def positiveRayXsqEndpointExtension (g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => if x = 0 then 0 else x^2 * g x

/--
The positive-ray matrix CFC convexity of `x ↦ x^2 * g x`, extended by `0` at
the endpoint, implies scalar continuity on the open positive ray.
-/
theorem positiveRayXsqEndpointExtension_continuousOn_Ioi_of_matrixConvex
    {g : ℝ → ℝ}
    (hconvex :
      PositiveRayMatrixOperatorConvex
        (positiveRayMatrixCfc (positiveRayXsqEndpointExtension g))) :
    ContinuousOn (positiveRayXsqEndpointExtension g) (Set.Ioi (0 : ℝ)) :=
  PositiveRayScalarConvex.continuousOn_Ioi
    (positiveRayScalarConvex_of_matrixOperatorConvex hconvex)

/-- On positive definite inputs, the concrete CFC twist is the CFC of `x ↦ x^2 * g x`. -/
lemma positiveRayMatrixCfcTwist_eq_xsqEndpointExtension_cfc_of_posDef
    {g : ℝ → ℝ} {n : ℕ} (X : HansenPedersen.Mₙ n) (hX : X.PosDef) :
    positiveRayMatrixCfcTwist g n X =
      positiveRayMatrixCfc (positiveRayXsqEndpointExtension g) n X := by
  dsimp [positiveRayMatrixCfcTwist, positiveRayMatrixCfc]
  rw [dif_pos hX.isHermitian, dif_pos hX.isHermitian]
  rw [← Matrix.IsHermitian.cfc_eq hX.isHermitian g]
  rw [← Matrix.IsHermitian.cfc_eq hX.isHermitian (positiveRayXsqEndpointExtension g)]
  rw [hX.isHermitian.eq]
  have hcomm : Commute X (cfc g X) := by
    simpa [cfc_id' (R := ℝ) (A := HansenPedersen.Mₙ n) X] using
      (cfc_commute_cfc (R := ℝ) (A := HansenPedersen.Mₙ n)
        (fun x : ℝ => x) g X)
  have hleft : X * cfc g X * X = X ^ 2 * cfc g X := by
    calc
      X * cfc g X * X = X * (cfc g X * X) := by rw [mul_assoc]
      _ = X * (X * cfc g X) := by rw [hcomm.eq.symm]
      _ = X ^ 2 * cfc g X := by rw [← mul_assoc, sq]
  have hEqOn : (spectrum ℝ X).EqOn (fun x : ℝ => x ^ 2 * g x)
      (positiveRayXsqEndpointExtension g) := by
    intro x hx
    have hxpos : 0 < x := by
      obtain ⟨i, rfl⟩ :=
        Set.ext_iff.mp hX.isHermitian.spectrum_real_eq_range_eigenvalues x |>.mp hx
      exact hX.eigenvalues_pos i
    have hxne : x ≠ 0 := ne_of_gt hxpos
    simp [positiveRayXsqEndpointExtension, hxne]
  have hg : ContinuousOn g (spectrum ℝ X) :=
    (Matrix.finite_real_spectrum (A := X)).continuousOn g
  calc
    X * cfc g X * X = X ^ 2 * cfc g X := hleft
    _ = cfc (fun x : ℝ => x ^ 2) X * cfc g X := by
      rw [cfc_pow_id (R := ℝ) (A := HansenPedersen.Mₙ n) X 2]
    _ = cfc (fun x : ℝ => x ^ 2 * g x) X := by
      rw [cfc_mul (R := ℝ) (A := HansenPedersen.Mₙ n) (fun x : ℝ => x ^ 2) g X
        (hg := hg)]
    _ = cfc (positiveRayXsqEndpointExtension g) X := by
      exact cfc_congr (a := X) hEqOn

/--
Matrix convexity of the concrete CFC twist can be read as matrix CFC convexity
of the endpoint extension `x ↦ x^2 * g x` on positive definite inputs.
-/
theorem positiveRayMatrixOperatorConvex_xsqEndpointExtension_of_cfcTwist
    {g : ℝ → ℝ}
    (hconvex : PositiveRayMatrixOperatorConvex (positiveRayMatrixCfcTwist g)) :
    PositiveRayMatrixOperatorConvex
      (positiveRayMatrixCfc (positiveRayXsqEndpointExtension g)) := by
  intro n X Y θ hX hY hθ0 hθ1
  have hcombo : (positiveRayMatrixConvexCombo θ X Y).PosDef :=
    positiveRayMatrixConvexCombo_posDef hX hY hθ0 hθ1
  rw [← positiveRayMatrixCfcTwist_eq_xsqEndpointExtension_cfc_of_posDef
      (g := g) X hX,
    ← positiveRayMatrixCfcTwist_eq_xsqEndpointExtension_cfc_of_posDef
      (g := g) Y hY,
    ← positiveRayMatrixCfcTwist_eq_xsqEndpointExtension_cfc_of_posDef
      (g := g) (positiveRayMatrixConvexCombo θ X Y) hcombo]
  exact hconvex hX hY hθ0 hθ1

/--
Positive-definite matrix CFC convexity extends to positive semidefinite inputs
once the endpoint scalar perturbation continuity of the CFC values is supplied.
-/
theorem positiveRayClosedMatrixOperatorConvex_xsqEndpointExtension_of_positive_endpointPerturbation
    {g : ℝ → ℝ}
    (hconvex :
      PositiveRayMatrixOperatorConvex
        (positiveRayMatrixCfc (positiveRayXsqEndpointExtension g)))
    (hpert :
      PositiveRayMatrixEndpointPerturbationContinuous
        (positiveRayXsqEndpointExtension g)) :
    PositiveRayClosedMatrixOperatorConvex
      (positiveRayMatrixCfc (positiveRayXsqEndpointExtension g)) := by
  let h : ℝ → ℝ := positiveRayXsqEndpointExtension g
  intro n X Y θ hXherm hYherm hXpsd hYpsd hθ0 hθ1
  let C : HansenPedersen.Mₙ n := positiveRayMatrixConvexCombo θ X Y
  let D : HansenPedersen.Mₙ n :=
    positiveRayMatrixConvexCombo θ (positiveRayMatrixCfc h n X)
      (positiveRayMatrixCfc h n Y) - positiveRayMatrixCfc h n C
  rw [Matrix.le_iff]
  change D.PosSemidef
  have hCherm : C.IsHermitian :=
    positiveRay_isHermitian_convexCombo θ hXherm hYherm
  have hCpsd : C.PosSemidef :=
    positiveRayMatrixConvexCombo_posSemidef hXpsd hYpsd hθ0 hθ1
  have hDherm : D.IsHermitian := by
    dsimp [D]
    exact (positiveRay_isHermitian_convexCombo θ
      (positiveRayMatrixCfc_isHermitian_of_isHermitian (g := h) X hXherm)
      (positiveRayMatrixCfc_isHermitian_of_isHermitian (g := h) Y hYherm)).sub
      (positiveRayMatrixCfc_isHermitian_of_isHermitian (g := h) C hCherm)
  let F : ℝ → HansenPedersen.Mₙ n := fun ε =>
    positiveRayMatrixConvexCombo θ
      (positiveRayMatrixCfc h n (X + ε • (1 : HansenPedersen.Mₙ n)))
      (positiveRayMatrixCfc h n (Y + ε • (1 : HansenPedersen.Mₙ n))) -
    positiveRayMatrixCfc h n
      (positiveRayMatrixConvexCombo θ (X + ε • (1 : HansenPedersen.Mₙ n))
        (Y + ε • (1 : HansenPedersen.Mₙ n)))
  have hGX :
      Tendsto
        (fun ε : ℝ => positiveRayMatrixCfc h n (X + ε • (1 : HansenPedersen.Mₙ n)))
        (𝓝[>] (0 : ℝ)) (𝓝 (positiveRayMatrixCfc h n X)) :=
    hpert X hXherm hXpsd
  have hGY :
      Tendsto
        (fun ε : ℝ => positiveRayMatrixCfc h n (Y + ε • (1 : HansenPedersen.Mₙ n)))
        (𝓝[>] (0 : ℝ)) (𝓝 (positiveRayMatrixCfc h n Y)) :=
    hpert Y hYherm hYpsd
  have hGC0 :
      Tendsto
        (fun ε : ℝ => positiveRayMatrixCfc h n (C + ε • (1 : HansenPedersen.Mₙ n)))
        (𝓝[>] (0 : ℝ)) (𝓝 (positiveRayMatrixCfc h n C)) :=
    hpert C hCherm hCpsd
  have hGC :
      Tendsto
        (fun ε : ℝ =>
          positiveRayMatrixCfc h n
            (positiveRayMatrixConvexCombo θ (X + ε • (1 : HansenPedersen.Mₙ n))
              (Y + ε • (1 : HansenPedersen.Mₙ n))))
        (𝓝[>] (0 : ℝ)) (𝓝 (positiveRayMatrixCfc h n C)) := by
    refine hGC0.congr' ?_
    filter_upwards with ε
    rw [positiveRayMatrixConvexCombo_add_scalar_one]
  have hRHS :
      Tendsto
        (fun ε : ℝ =>
          positiveRayMatrixConvexCombo θ
            (positiveRayMatrixCfc h n (X + ε • (1 : HansenPedersen.Mₙ n)))
            (positiveRayMatrixCfc h n (Y + ε • (1 : HansenPedersen.Mₙ n))))
        (𝓝[>] (0 : ℝ))
        (𝓝
          (positiveRayMatrixConvexCombo θ
            (positiveRayMatrixCfc h n X) (positiveRayMatrixCfc h n Y))) := by
    dsimp [positiveRayMatrixConvexCombo]
    exact (hGX.const_smul (θ : ℂ)).add
      (hGY.const_smul (((1 - θ : ℝ) : ℂ)))
  have hF :
      Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 D) := by
    dsimp [F, D]
    exact hRHS.sub hGC
  have hpsd : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (F ε).PosSemidef := by
    filter_upwards [self_mem_nhdsWithin] with ε hεmem
    have hε : 0 < ε := by simpa using hεmem
    have hXε : (X + ε • (1 : HansenPedersen.Mₙ n)).PosDef :=
      positiveRayMat_add_pos_scalar_one_posDef hXpsd hε
    have hYε : (Y + ε • (1 : HansenPedersen.Mₙ n)).PosDef :=
      positiveRayMat_add_pos_scalar_one_posDef hYpsd hε
    have hineq := hconvex (n := n)
      (X := X + ε • (1 : HansenPedersen.Mₙ n))
      (Y := Y + ε • (1 : HansenPedersen.Mₙ n))
      (θ := θ) hXε hYε hθ0 hθ1
    rw [Matrix.le_iff] at hineq
    simpa [F] using hineq
  exact positiveRayMat_posSemidef_of_tendsto hF hDherm hpsd

/--
If the one-dimensional scalar restriction of a jointly convex matrix assignment
agrees with `g` on the positive ray, then the endpoint extension of
`x ↦ x^2 * g x` is right-continuous at `0`.
-/
theorem positiveRayXsqEndpointExtension_tendsto_zero_of_scalarQForm
    {G : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n} {g : ℝ → ℝ}
    (hjoint : PositiveRayMatrixQFormJointConvex G)
    (hscalar : ∀ x : ℝ, 0 < x → g x = positiveRayScalarQFormValue G x)
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x) :
    Tendsto (positiveRayXsqEndpointExtension g) (𝓝[>] (0 : ℝ))
      (𝓝 ((positiveRayXsqEndpointExtension g) 0)) := by
  have hnonnegG : ∀ x : ℝ, 0 < x → 0 ≤ positiveRayScalarQFormValue G x := by
    intro x hx
    simpa [← hscalar x hx] using hnonneg x hx
  refine positiveRayEndpointTendsto_zero_of_scalarTwist_eventualEq
    hjoint hnonnegG ?_ ?_
  · simp [positiveRayXsqEndpointExtension]
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hxpos : 0 < x := by simpa using hx
    have hxne : x ≠ 0 := ne_of_gt hxpos
    simp [positiveRayXsqEndpointExtension, positiveRayScalarQFormTwist, hxne,
      hscalar x hxpos]

/--
Endpoint control for the positive-ray function `x ↦ x^2 * g x`.

It records both the linear estimate near `0` from the right and the resulting
right-continuity of the endpoint extension.
-/
structure PositiveRayXsqEndpointControl (g : ℝ → ℝ) : Prop where
  linear_control :
    PositiveRayEndpointLinearControl (positiveRayXsqEndpointExtension g)
  right_continuous_at_zero :
    Tendsto (positiveRayXsqEndpointExtension g) (𝓝[>] (0 : ℝ))
      (𝓝 ((positiveRayXsqEndpointExtension g) 0))

/--
Endpoint control and interior continuity for `x ↦ x^2 * g x`, extended by
`0` at the endpoint, imply right-continuity of its finite-dimensional CFC
values under `X ↦ X + ε I`.
-/
theorem positiveRayXsqEndpointExtension_matrixEndpointPerturbationContinuous_of_endpointControl
    {g : ℝ → ℝ}
    (hcont :
      ContinuousOn (positiveRayXsqEndpointExtension g) (Set.Ioi (0 : ℝ)))
    (hcontrol : PositiveRayXsqEndpointControl g) :
    PositiveRayMatrixEndpointPerturbationContinuous
      (positiveRayXsqEndpointExtension g) := by
  apply positiveRayMatrixEndpointPerturbationContinuous_of_continuousOn_Ici
  intro x hx
  have hxle : 0 ≤ x := by simpa using hx
  rcases lt_or_eq_of_le hxle with hxpos | rfl
  · exact (hcont.continuousAt (Ioi_mem_nhds hxpos)).continuousWithinAt
  · have hright :
        ContinuousWithinAt (positiveRayXsqEndpointExtension g)
          (Set.Ioi (0 : ℝ)) 0 :=
      hcontrol.right_continuous_at_zero
    exact continuousWithinAt_Ioi_iff_Ici.mp hright

/--
Matrix convexity of the concrete CFC twist and endpoint control extend the
CFC convexity of `x ↦ x^2 * g x`, with endpoint value `0`, from positive
definite inputs to positive semidefinite Hermitian inputs.
-/
theorem positiveRayClosedMatrixOperatorConvex_xsqEndpointExtension_of_cfcTwist_endpointControl
    {g : ℝ → ℝ}
    (hconvex : PositiveRayMatrixOperatorConvex (positiveRayMatrixCfcTwist g))
    (hcontrol : PositiveRayXsqEndpointControl g) :
    PositiveRayClosedMatrixOperatorConvex
      (positiveRayMatrixCfc (positiveRayXsqEndpointExtension g)) := by
  have hopen :
      PositiveRayMatrixOperatorConvex
        (positiveRayMatrixCfc (positiveRayXsqEndpointExtension g)) :=
    positiveRayMatrixOperatorConvex_xsqEndpointExtension_of_cfcTwist hconvex
  have hcont :
      ContinuousOn (positiveRayXsqEndpointExtension g) (Set.Ioi (0 : ℝ)) :=
    positiveRayXsqEndpointExtension_continuousOn_Ioi_of_matrixConvex hopen
  have hpert :
      PositiveRayMatrixEndpointPerturbationContinuous
        (positiveRayXsqEndpointExtension g) :=
    positiveRayXsqEndpointExtension_matrixEndpointPerturbationContinuous_of_endpointControl
      hcont hcontrol
  intro n X Y θ hXherm hYherm hXpsd hYpsd hθ0 hθ1
  exact
    (positiveRayClosedMatrixOperatorConvex_xsqEndpointExtension_of_positive_endpointPerturbation
      (g := g) hopen hpert (n := n) (X := X) (Y := Y) (θ := θ))
      hXherm hYherm hXpsd hYpsd hθ0 hθ1

/--
The scalar endpoint extension of `x ↦ x^2 * g x` has the same linear endpoint
control as the one-dimensional scalar twist, provided `g` agrees with that
scalar restriction on the positive ray.
-/
theorem positiveRayXsqEndpointExtension_linearControl_of_scalarQForm
    {G : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n} {g : ℝ → ℝ}
    (hjoint : PositiveRayMatrixQFormJointConvex G)
    (hscalar : ∀ x : ℝ, 0 < x → g x = positiveRayScalarQFormValue G x)
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x) :
    PositiveRayEndpointLinearControl (positiveRayXsqEndpointExtension g) := by
  have hnonnegG : ∀ x : ℝ, 0 < x → 0 ≤ positiveRayScalarQFormValue G x := by
    intro x hx
    simpa [← hscalar x hx] using hnonneg x hx
  rcases positiveRayEndpointLinearControl_scalarTwist_of_qformJointConvex
      hjoint hnonnegG with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, self_mem_nhdsWithin] with x hxbound hx
  have hxpos : 0 < x := by simpa using hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have heq :
      positiveRayXsqEndpointExtension g x = positiveRayScalarQFormTwist G x := by
    simp [positiveRayXsqEndpointExtension, positiveRayScalarQFormTwist, hxne,
      hscalar x hxpos]
  simpa [heq] using hxbound

/--
If the one-dimensional scalar restriction of a jointly convex matrix assignment
agrees with `g` on the positive ray and `g` is nonnegative there, then
`x ↦ x^2 * g x` has endpoint linear control and is right-continuous at `0`
after assigning endpoint value `0`.
-/
theorem positiveRayXsqEndpointControl_of_scalarQForm
    {G : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n} {g : ℝ → ℝ}
    (hjoint : PositiveRayMatrixQFormJointConvex G)
    (hscalar : ∀ x : ℝ, 0 < x → g x = positiveRayScalarQFormValue G x)
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x) :
    PositiveRayXsqEndpointControl g where
  linear_control :=
    positiveRayXsqEndpointExtension_linearControl_of_scalarQForm
      hjoint hscalar hnonneg
  right_continuous_at_zero :=
    positiveRayXsqEndpointExtension_tendsto_zero_of_scalarQForm
      hjoint hscalar hnonneg

/--
Endpoint control for `x ↦ x^2 * g x`, whose endpoint extension has value `0`,
also supplies endpoint linear control for the normalized difference
`h₀ - h₀(0)`.
-/
theorem PositiveRayXsqEndpointControl.linear_control_sub_endpoint
    {g : ℝ → ℝ} (hcontrol : PositiveRayXsqEndpointControl g) :
    PositiveRayEndpointLinearControl
      (fun x : ℝ =>
        positiveRayXsqEndpointExtension g x -
          positiveRayXsqEndpointExtension g 0) := by
  rcases hcontrol.linear_control with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with x hx
  simpa [positiveRayXsqEndpointExtension] using hx

/-! ### Finite-right-derivative and quotient representation suppliers -/
/--
If the endpoint extension of `x ↦ x^2 * g x` has the finite-right-derivative
operator-convex representation with nonnegative linear coefficient, then `g`
is operator monotone decreasing on the positive ray.
-/
theorem operatorMonotoneDecreasingOnPositive_of_xsq_finiteRightDerivativeRep
    {g : ℝ → ℝ}
    (rep : PositiveRayOperatorConvexRepFiniteRightDerivative
      (positiveRayXsqEndpointExtension g))
    (ha : 0 ≤ rep.a) :
    OperatorMonotoneDecreasingOnPositive g := by
  let h₀ : ℝ → ℝ := positiveRayXsqEndpointExtension g
  have hxsq :
      ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) → h₀ x = x ^ 2 * g x := by
    intro x hx
    have hxpos : 0 < x := by simpa using hx
    have hxne : x ≠ 0 := ne_of_gt hxpos
    simp [h₀, positiveRayXsqEndpointExtension, hxne]
  have hzero : h₀ 0 = 0 := by
    simp [h₀, positiveRayXsqEndpointExtension]
  let drep : PositiveRayOperatorMonotoneDecreasingRep g :=
    positiveRayOperatorMonotoneDecreasingRep_of_xsq_finiteRightDerivativeRep
      (g := g) (h₀ := h₀) hxsq hzero rep ha
  exact operatorMonotoneDecreasingOnPositive_of_rep drep

/--
AH1 assembly step: once the finite-right-derivative representation of
`x ↦ x^2 * g x` is supplied from the twist convexity and endpoint control,
joint convexity of the quadratic forms implies that `g` is operator monotone
decreasing on the positive ray.
-/
theorem operatorMonotoneDecreasingOnPositive_of_qformJointConvex_of_xsqRepSupplier
    {G H : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n} {g : ℝ → ℝ}
    (hHermH : ∀ {n : ℕ} (X : HansenPedersen.Mₙ n), (H n X).IsHermitian)
    (hjoint : PositiveRayMatrixQFormJointConvex G)
    (htwist : PositiveRayMatrixQFormTwist G H)
    (hscalar : ∀ x : ℝ, 0 < x → g x = positiveRayScalarQFormValue G x)
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hrepSupplier :
      PositiveRayMatrixOperatorConvex H →
        PositiveRayXsqEndpointControl g →
          ∃ rep : PositiveRayOperatorConvexRepFiniteRightDerivative
              (positiveRayXsqEndpointExtension g),
            0 ≤ rep.a) :
    OperatorMonotoneDecreasingOnPositive g := by
  have hconvexH : PositiveRayMatrixOperatorConvex H :=
    positiveRayMatrixOperatorConvex_of_qformJointConvex_twist
      hHermH hjoint htwist
  have hcontrol : PositiveRayXsqEndpointControl g :=
    positiveRayXsqEndpointControl_of_scalarQForm hjoint hscalar hnonneg
  rcases hrepSupplier hconvexH hcontrol with ⟨rep, ha⟩
  exact operatorMonotoneDecreasingOnPositive_of_xsq_finiteRightDerivativeRep rep ha

/--
Build the finite-right-derivative representation of the endpoint extension of
`x ↦ x^2 * g x` from a Kubo--Ando representation of the quotient
`q` in `h₀ x = h₀ 0 + x * q x`.
-/
theorem exists_xsq_finiteRightDerivativeRep_of_positiveRayKuboAndoQuotient
    {g q : ℝ → ℝ}
    (hquot : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
      positiveRayXsqEndpointExtension g x =
        positiveRayXsqEndpointExtension g 0 + x * q x)
    (rep : PositiveRayKuboAndoRep q)
    (ha : 0 ≤ q 0) :
    ∃ rep' : PositiveRayOperatorConvexRepFiniteRightDerivative
        (positiveRayXsqEndpointExtension g),
      0 ≤ rep'.a := by
  let rep' : PositiveRayOperatorConvexRepFiniteRightDerivative
      (positiveRayXsqEndpointExtension g) :=
    positiveRayOperatorConvexRepFiniteRightDerivative_of_positiveRayKuboAndoRep
      hquot rep
  refine ⟨rep', ?_⟩
  simpa [rep'] using ha

/--
Extract the closed-positive monotone quotient from a finite-right-derivative
representation of the endpoint extension of `x ↦ x^2 * g x`.
-/
theorem exists_closedPositiveQuotient_of_xsq_finiteRightDerivativeRep
    {g : ℝ → ℝ}
    (rep : PositiveRayOperatorConvexRepFiniteRightDerivative
      (positiveRayXsqEndpointExtension g))
    (ha : 0 ≤ rep.a) :
    ∃ q : ℝ → ℝ,
      (∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
        positiveRayXsqEndpointExtension g x =
          positiveRayXsqEndpointExtension g 0 + x * q x) ∧
      OperatorMonotoneOnClosedPositive q ∧
      0 ≤ q 0 := by
  rcases exists_kuboAndo_quotient_of_positiveRayOperatorConvexRepFiniteRightDerivative
      rep with ⟨q, hquot, ⟨qrep⟩, hq0⟩
  refine ⟨q, hquot, ?_, ?_⟩
  · exact operatorMonotoneOnClosedPositive_of_positiveRayKuboAndoRep qrep
  · simpa [hq0] using ha

/--
For the endpoint extension of `x ↦ x^2 * g x`, nonnegativity of `g` on the
positive ray forces the linear coefficient in any finite-right-derivative
representation to be nonnegative.
-/
theorem positiveRayOperatorConvexRepFiniteRightDerivative_linearCoeff_nonneg_of_xsq_nonneg
    {g : ℝ → ℝ}
    (rep : PositiveRayOperatorConvexRepFiniteRightDerivative
      (positiveRayXsqEndpointExtension g))
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x) :
    0 ≤ rep.a := by
  rcases exists_kuboAndo_quotient_of_positiveRayOperatorConvexRepFiniteRightDerivative
      rep with ⟨q, hquot, ⟨qrep⟩, hq0⟩
  have hclosed : OperatorMonotoneOnClosedPositive.{0} q :=
    operatorMonotoneOnClosedPositive_of_positiveRayKuboAndoRep qrep
  have hq_nonneg_eventually : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 ≤ q x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxpos : 0 < x := by simpa using hx
    have hxIoi : x ∈ Set.Ioi (0 : ℝ) := by simpa using hxpos
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hquotx := hquot hxIoi
    have hmul : x * q x = x ^ 2 * g x := by
      simpa [positiveRayXsqEndpointExtension, hxne] using hquotx.symm
    have hxg_nonneg : 0 ≤ x ^ 2 * g x :=
      mul_nonneg (sq_nonneg x) (hnonneg x hxpos)
    have hxq_nonneg : 0 ≤ x * q x := by
      simpa [hmul] using hxg_nonneg
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hxq_nonneg) hxpos
  have hq0_nonneg : 0 ≤ q 0 :=
    ge_of_tendsto hclosed.right_continuous_at_zero hq_nonneg_eventually
  simpa [hq0] using hq0_nonneg

/--
Build the finite-right-derivative representation of `x ↦ x^2 * g x` from a
Kubo--Ando quotient.  The nonnegativity of `g` on the positive ray supplies
the nonnegative linear coefficient of the resulting representation.
-/
theorem exists_xsq_finiteRightDerivativeRep_of_positiveRayKuboAndoQuotient_of_xsq_nonneg
    {g q : ℝ → ℝ}
    (hquot : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
      positiveRayXsqEndpointExtension g x =
        positiveRayXsqEndpointExtension g 0 + x * q x)
    (rep : PositiveRayKuboAndoRep q)
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x) :
    ∃ rep' : PositiveRayOperatorConvexRepFiniteRightDerivative
        (positiveRayXsqEndpointExtension g),
      0 ≤ rep'.a := by
  let rep' : PositiveRayOperatorConvexRepFiniteRightDerivative
      (positiveRayXsqEndpointExtension g) :=
    positiveRayOperatorConvexRepFiniteRightDerivative_of_positiveRayKuboAndoRep
      hquot rep
  exact ⟨rep',
    positiveRayOperatorConvexRepFiniteRightDerivative_linearCoeff_nonneg_of_xsq_nonneg
      rep' hnonneg⟩

/--
Build the finite-right-derivative representation of `x ↦ x^2 * g x` from a
closed-positive operator-monotone quotient.  The half-line Loewner theorem
turns the quotient into a Kubo--Ando representation, and nonnegativity of `g`
supplies the nonnegative linear coefficient.
-/
theorem exists_xsq_finiteRightDerivativeRep_of_closedPositiveQuotient_of_xsq_nonneg
    {g q : ℝ → ℝ}
    (hquot : ∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
      positiveRayXsqEndpointExtension g x =
        positiveRayXsqEndpointExtension g 0 + x * q x)
    (hclosed : OperatorMonotoneOnClosedPositive q)
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x) :
    ∃ rep' : PositiveRayOperatorConvexRepFiniteRightDerivative
        (positiveRayXsqEndpointExtension g),
      0 ≤ rep'.a := by
  exact
    exists_xsq_finiteRightDerivativeRep_of_positiveRayKuboAndoQuotient_of_xsq_nonneg
      hquot
      (positiveRayKuboAndoRep_of_operatorMonotoneOnClosedPositive hclosed)
      hnonneg

/--
Specialize the closed-positive quotient representation theorem to the endpoint
quotient of `x ↦ x^2 * g x`.
-/
theorem exists_xsq_finiteRightDerivativeRep_of_endpointQuotient_closedPositive_of_xsq_nonneg
    {g : ℝ → ℝ} {d : ℝ}
    (hclosed :
      OperatorMonotoneOnClosedPositive
        (positiveRayEndpointQuotient (positiveRayXsqEndpointExtension g) d))
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x) :
    ∃ rep' : PositiveRayOperatorConvexRepFiniteRightDerivative
        (positiveRayXsqEndpointExtension g),
      0 ≤ rep'.a := by
  refine
    exists_xsq_finiteRightDerivativeRep_of_closedPositiveQuotient_of_xsq_nonneg
      ?_ hclosed hnonneg
  intro x hx
  have hxpos : 0 < x := by simpa using hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  simp [positiveRayEndpointQuotient, hxne]
  field_simp [hxne]
  ring

/--
The normalized interval finite-matrix monotonicity of an endpoint quotient,
together with its right-continuity at `0`, gives closed-positive
operator-monotonicity of the quotient on the positive half-line.
-/
theorem operatorMonotoneOnClosedPositive_endpointQuotient_of_unitIntervalFiniteMatrixMonotone
    {h : ℝ → ℝ} {d : ℝ}
    (hfinite :
      UnitIntervalMatrixMonotone
        (positiveCayleyPullback (positiveRayEndpointQuotient h d)))
    (hright :
      Tendsto (positiveRayEndpointQuotient h d) (𝓝[>] (0 : ℝ)) (𝓝 d)) :
    OperatorMonotoneOnClosedPositive.{u}
      (positiveRayEndpointQuotient h d) := by
  refine operatorMonotoneOnClosedPositive_of_unitIntervalFiniteMatrixMonotone
    hfinite ?_
  simpa [positiveRayEndpointQuotient] using hright

/--
Specialize the finite-matrix-to-closed-positive quotient route to the endpoint
quotient of `x ↦ x^2 * g x`, then build the finite-right-derivative
representation.
-/
theorem exists_xsq_finiteRightDerivativeRep_of_endpointQuotient_finiteMatrixMonotone_of_xsq_nonneg
    {g : ℝ → ℝ} {d : ℝ}
    (hfinite :
      UnitIntervalMatrixMonotone
        (positiveCayleyPullback
          (positiveRayEndpointQuotient (positiveRayXsqEndpointExtension g) d)))
    (hright :
      Tendsto
        (positiveRayEndpointQuotient (positiveRayXsqEndpointExtension g) d)
        (𝓝[>] (0 : ℝ)) (𝓝 d))
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x) :
    ∃ rep' : PositiveRayOperatorConvexRepFiniteRightDerivative
        (positiveRayXsqEndpointExtension g),
      0 ≤ rep'.a := by
  exact
    exists_xsq_finiteRightDerivativeRep_of_endpointQuotient_closedPositive_of_xsq_nonneg.{0}
      (operatorMonotoneOnClosedPositive_endpointQuotient_of_unitIntervalFiniteMatrixMonotone.{0}
        hfinite hright)
      hnonneg

/--
Build the finite-right-derivative representation from endpoint-control data
once the closed-positive monotone quotient is supplied for the concrete CFC
twist `X ↦ X^* g(X) X`.
-/
theorem exists_xsq_finiteRightDerivativeRep_of_matrixCfcTwist_closedPositiveQuotientSupplier
    {g : ℝ → ℝ}
    (hconvexH : PositiveRayMatrixOperatorConvex (positiveRayMatrixCfcTwist g))
    (hcontrol : PositiveRayXsqEndpointControl g)
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hquotSupplier :
      PositiveRayMatrixOperatorConvex (positiveRayMatrixCfcTwist g) →
        PositiveRayXsqEndpointControl g →
          ∃ q : ℝ → ℝ,
            (∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
              positiveRayXsqEndpointExtension g x =
                positiveRayXsqEndpointExtension g 0 + x * q x) ∧
            OperatorMonotoneOnClosedPositive q) :
    ∃ rep : PositiveRayOperatorConvexRepFiniteRightDerivative
        (positiveRayXsqEndpointExtension g),
      0 ≤ rep.a := by
  rcases hquotSupplier hconvexH hcontrol with ⟨q, hquot, hclosed⟩
  exact
    exists_xsq_finiteRightDerivativeRep_of_closedPositiveQuotient_of_xsq_nonneg
      hquot hclosed hnonneg

/--
Build the finite-right-derivative representation from endpoint-control data
once the concrete matrix CFC twist has been transported to closed-positive
operator convexity and the closed-positive Bendat--Sherman quotient has been
supplied.
-/
theorem exists_xsq_finiteRightDerivativeRep_of_closedPositiveConvexQuotientSupplier
    {g : ℝ → ℝ}
    (hconvexH : PositiveRayMatrixOperatorConvex (positiveRayMatrixCfcTwist g))
    (hcontrol : PositiveRayXsqEndpointControl g)
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hclosedConvexSupplier :
      PositiveRayMatrixOperatorConvex (positiveRayMatrixCfcTwist g) →
        PositiveRayXsqEndpointControl g →
          ∀ {𝓑 : Type} [CStarAlgebra 𝓑] [PartialOrder 𝓑]
            [StarOrderedRing 𝓑] [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint]
            [Nontrivial 𝓑],
            LownerHeinzCore.OperatorConvexOn (𝓐 := 𝓑)
              (Set.Ici (0 : ℝ)) (positiveRayXsqEndpointExtension g))
    (hquotientSupplier :
      ∀ _hclosed :
          (∀ {𝓑 : Type} [CStarAlgebra 𝓑] [PartialOrder 𝓑]
            [StarOrderedRing 𝓑] [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint]
            [Nontrivial 𝓑],
            LownerHeinzCore.OperatorConvexOn (𝓐 := 𝓑)
              (Set.Ici (0 : ℝ)) (positiveRayXsqEndpointExtension g)),
        ∃ q : ℝ → ℝ,
          (∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
            positiveRayXsqEndpointExtension g x =
              positiveRayXsqEndpointExtension g 0 + x * q x) ∧
          OperatorMonotoneOnClosedPositive q) :
    ∃ rep : PositiveRayOperatorConvexRepFiniteRightDerivative
        (positiveRayXsqEndpointExtension g),
      0 ≤ rep.a := by
  refine
    exists_xsq_finiteRightDerivativeRep_of_matrixCfcTwist_closedPositiveQuotientSupplier
      hconvexH hcontrol hnonneg ?_
  intro hconvexH' hcontrol'
  have hclosed :
      ∀ {𝓑 : Type} [CStarAlgebra 𝓑] [PartialOrder 𝓑]
        [StarOrderedRing 𝓑] [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint]
        [Nontrivial 𝓑],
        LownerHeinzCore.OperatorConvexOn (𝓐 := 𝓑)
          (Set.Ici (0 : ℝ)) (positiveRayXsqEndpointExtension g) := by
    intro 𝓑 _ _ _ _ _
    exact hclosedConvexSupplier hconvexH' hcontrol'
  exact hquotientSupplier (by
    exact fun {𝓑 : Type} [CStarAlgebra 𝓑] [PartialOrder 𝓑]
        [StarOrderedRing 𝓑] [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint]
        [Nontrivial 𝓑] {A B : 𝓑} {t : ℝ} hA hB ht0 ht1 hAs hBs =>
      hclosed (𝓑 := 𝓑) (A := A) (B := B) (t := t)
        hA hB ht0 ht1 hAs hBs)

/-! ### Abstract AH1 assembly from quotient suppliers -/
/--
AH1 assembly step with a Kubo--Ando quotient supplier.  If the quotient in
`h₀ x = h₀ 0 + x * q x` has a Kubo--Ando representation with nonnegative
endpoint value whenever the twist convexity and endpoint control are available,
then the original scalar function is operator monotone decreasing on the
positive ray.
-/
theorem operatorMonotoneDecreasingOnPositive_of_qformJointConvex_of_kuboAndoQuotientSupplier
    {G H : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n} {g : ℝ → ℝ}
    (hHermH : ∀ {n : ℕ} (X : HansenPedersen.Mₙ n), (H n X).IsHermitian)
    (hjoint : PositiveRayMatrixQFormJointConvex G)
    (htwist : PositiveRayMatrixQFormTwist G H)
    (hscalar : ∀ x : ℝ, 0 < x → g x = positiveRayScalarQFormValue G x)
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hkuboSupplier :
      PositiveRayMatrixOperatorConvex H →
        PositiveRayXsqEndpointControl g →
          ∃ q : ℝ → ℝ,
            (∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
              positiveRayXsqEndpointExtension g x =
                positiveRayXsqEndpointExtension g 0 + x * q x) ∧
            Nonempty (PositiveRayKuboAndoRep q) ∧
            0 ≤ q 0) :
    OperatorMonotoneDecreasingOnPositive g := by
  refine
    operatorMonotoneDecreasingOnPositive_of_qformJointConvex_of_xsqRepSupplier
      hHermH hjoint htwist hscalar hnonneg ?_
  intro hconvexH hcontrol
  rcases hkuboSupplier hconvexH hcontrol with ⟨q, hquot, ⟨rep⟩, ha⟩
  exact exists_xsq_finiteRightDerivativeRep_of_positiveRayKuboAndoQuotient
    hquot rep ha

/--
Positive-input AH1 assembly step with a Kubo--Ando quotient supplier.  This
variant asks for self-adjointness and twist only on positive definite inputs.
-/
theorem operatorMonotoneDecreasingOnPositive_of_kuboAndoQuotientSupplierOnPositive
    {G H : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n} {g : ℝ → ℝ}
    (hHermH : ∀ {n : ℕ} (X : HansenPedersen.Mₙ n), X.PosDef → (H n X).IsHermitian)
    (hjoint : PositiveRayMatrixQFormJointConvex G)
    (htwist : PositiveRayMatrixQFormTwistOnPositive G H)
    (hscalar : ∀ x : ℝ, 0 < x → g x = positiveRayScalarQFormValue G x)
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hkuboSupplier :
      PositiveRayMatrixOperatorConvex H →
        PositiveRayXsqEndpointControl g →
          ∃ q : ℝ → ℝ,
            (∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
              positiveRayXsqEndpointExtension g x =
                positiveRayXsqEndpointExtension g 0 + x * q x) ∧
            Nonempty (PositiveRayKuboAndoRep q) ∧
            0 ≤ q 0) :
    OperatorMonotoneDecreasingOnPositive g := by
  have hconvexH : PositiveRayMatrixOperatorConvex H :=
    positiveRayMatrixOperatorConvex_of_qformJointConvex_twistOnPositive
      hHermH hjoint htwist
  have hcontrol : PositiveRayXsqEndpointControl g :=
    positiveRayXsqEndpointControl_of_scalarQForm hjoint hscalar hnonneg
  rcases hkuboSupplier hconvexH hcontrol with ⟨q, hquot, ⟨rep⟩, ha⟩
  rcases exists_xsq_finiteRightDerivativeRep_of_positiveRayKuboAndoQuotient
      hquot rep ha with ⟨rep', ha'⟩
  exact operatorMonotoneDecreasingOnPositive_of_xsq_finiteRightDerivativeRep
    rep' ha'

/--
Positive-input AH1 assembly step with a finite-right-derivative representation
supplier.  The theorem closes the self-adjointness, twist, and endpoint-control
transport, and leaves only the representation supplier as an explicit input.
-/
theorem operatorMonotoneDecreasingOnPositive_of_xsqRepSupplierOnPositive
    {G H : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n} {g : ℝ → ℝ}
    (hHermH : ∀ {n : ℕ} (X : HansenPedersen.Mₙ n), X.PosDef → (H n X).IsHermitian)
    (hjoint : PositiveRayMatrixQFormJointConvex G)
    (htwist : PositiveRayMatrixQFormTwistOnPositive G H)
    (hscalar : ∀ x : ℝ, 0 < x → g x = positiveRayScalarQFormValue G x)
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hrepSupplier :
      PositiveRayMatrixOperatorConvex H →
        PositiveRayXsqEndpointControl g →
          ∃ rep : PositiveRayOperatorConvexRepFiniteRightDerivative
              (positiveRayXsqEndpointExtension g),
            0 ≤ rep.a) :
    OperatorMonotoneDecreasingOnPositive g := by
  have hconvexH : PositiveRayMatrixOperatorConvex H :=
    positiveRayMatrixOperatorConvex_of_qformJointConvex_twistOnPositive
      hHermH hjoint htwist
  have hcontrol : PositiveRayXsqEndpointControl g :=
    positiveRayXsqEndpointControl_of_scalarQForm hjoint hscalar hnonneg
  rcases hrepSupplier hconvexH hcontrol with ⟨rep, ha⟩
  exact operatorMonotoneDecreasingOnPositive_of_xsq_finiteRightDerivativeRep
    rep ha

/-! ### Concrete CFC AH1 assembly and theorem-facing conclusion -/
/--
AH1 assembly step from a matrix functional-calculus realization supplier.
If the concrete scalar function `g` is realized by matrix assignments `G,H`
that satisfy the quadratic-form convexity, twist, scalar restriction,
nonnegativity, and Kubo--Ando quotient supplier hypotheses of the abstract
bridge, then `g` is operator monotone decreasing on the positive ray.
-/
theorem operatorMonotoneDecreasingOnPositive_of_matrixRealizationSupplier
    {g : ℝ → ℝ}
    (hsupplier :
      ∃ G H : ∀ n : ℕ, HansenPedersen.Mₙ n → HansenPedersen.Mₙ n,
        (∀ {n : ℕ} (X : HansenPedersen.Mₙ n), X.PosDef → (H n X).IsHermitian) ∧
        PositiveRayMatrixQFormJointConvex G ∧
        PositiveRayMatrixQFormTwistOnPositive G H ∧
        (∀ x : ℝ, 0 < x → g x = positiveRayScalarQFormValue G x) ∧
        (∀ x : ℝ, 0 < x → 0 ≤ g x) ∧
        (PositiveRayMatrixOperatorConvex H →
          PositiveRayXsqEndpointControl g →
            ∃ q : ℝ → ℝ,
              (∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
                positiveRayXsqEndpointExtension g x =
                  positiveRayXsqEndpointExtension g 0 + x * q x) ∧
              Nonempty (PositiveRayKuboAndoRep q) ∧
              0 ≤ q 0)) :
    OperatorMonotoneDecreasingOnPositive g := by
  rcases hsupplier with
    ⟨G, H, hHermH, hjoint, htwist, hscalar, hnonneg, hkuboSupplier⟩
  exact
    operatorMonotoneDecreasingOnPositive_of_kuboAndoQuotientSupplierOnPositive
      hHermH hjoint htwist hscalar hnonneg hkuboSupplier

/--
AH1 assembly step for the concrete finite-dimensional CFC realization
`G n X = g(X)` and twist `H n X = X^* g(X) X`.

The scalar one-dimensional restriction and the Kubo--Ando quotient supplier
are explicit hypotheses here; this theorem closes only the self-adjointness and
twist parts of the concrete CFC realization.  The theorem-facing AH1 direction,
which needs neither, is `operatorMonotoneDecreasingOnPositive_of_qformJointConvex`
below.
-/
theorem operatorMonotoneDecreasingOnPositive_of_matrixCfcRealizationSupplier
    {g : ℝ → ℝ}
    (hjoint : PositiveRayMatrixQFormJointConvex (positiveRayMatrixCfc g))
    (hscalar : ∀ x : ℝ, 0 < x →
      g x = positiveRayScalarQFormValue (positiveRayMatrixCfc g) x)
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hkuboSupplier :
      PositiveRayMatrixOperatorConvex (positiveRayMatrixCfcTwist g) →
        PositiveRayXsqEndpointControl g →
          ∃ q : ℝ → ℝ,
            (∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
              positiveRayXsqEndpointExtension g x =
                positiveRayXsqEndpointExtension g 0 + x * q x) ∧
            Nonempty (PositiveRayKuboAndoRep q) ∧
            0 ≤ q 0) :
    OperatorMonotoneDecreasingOnPositive g := by
  refine operatorMonotoneDecreasingOnPositive_of_matrixRealizationSupplier ?_
  exact ⟨positiveRayMatrixCfc g, positiveRayMatrixCfcTwist g,
    (fun X hX => positiveRayMatrixCfcTwist_isHermitian_of_posDef (g := g) X hX),
    hjoint, positiveRayMatrixCfcTwistOnPositive g, hscalar, hnonneg,
    hkuboSupplier⟩

/--
AH1 assembly step for the concrete finite-dimensional CFC realization, with
the one-dimensional scalar restriction supplied by the CFC algebra-map rule.
-/
theorem operatorMonotoneDecreasingOnPositive_of_matrixCfcRealizationScalarRestriction
    {g : ℝ → ℝ}
    (hjoint : PositiveRayMatrixQFormJointConvex (positiveRayMatrixCfc g))
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hkuboSupplier :
      PositiveRayMatrixOperatorConvex (positiveRayMatrixCfcTwist g) →
        PositiveRayXsqEndpointControl g →
          ∃ q : ℝ → ℝ,
            (∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
              positiveRayXsqEndpointExtension g x =
                positiveRayXsqEndpointExtension g 0 + x * q x) ∧
            Nonempty (PositiveRayKuboAndoRep q) ∧
            0 ≤ q 0) :
    OperatorMonotoneDecreasingOnPositive g := by
  exact operatorMonotoneDecreasingOnPositive_of_matrixCfcRealizationSupplier
    hjoint (fun _ hx => positiveRayMatrixCfc_scalarQFormValue (g := g) hx)
    hnonneg hkuboSupplier

/--
AH1 assembly step for the concrete CFC realization with the one-dimensional
scalar restriction built in, using a finite-right-derivative representation
supplier instead of a Kubo--Ando quotient supplier.
-/
theorem operatorMonotoneDecreasingOnPositive_of_matrixCfcRealizationXsqRepSupplier
    {g : ℝ → ℝ}
    (hjoint : PositiveRayMatrixQFormJointConvex (positiveRayMatrixCfc g))
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hrepSupplier :
      PositiveRayMatrixOperatorConvex (positiveRayMatrixCfcTwist g) →
        PositiveRayXsqEndpointControl g →
          ∃ rep : PositiveRayOperatorConvexRepFiniteRightDerivative
              (positiveRayXsqEndpointExtension g),
            0 ≤ rep.a) :
    OperatorMonotoneDecreasingOnPositive g := by
  exact operatorMonotoneDecreasingOnPositive_of_xsqRepSupplierOnPositive
    (fun X hX => positiveRayMatrixCfcTwist_isHermitian_of_posDef (g := g) X hX)
    hjoint (positiveRayMatrixCfcTwistOnPositive g)
    (fun _ hx => positiveRayMatrixCfc_scalarQFormValue (g := g) hx)
    hnonneg hrepSupplier

/--
AH1 assembly step for the concrete CFC realization, using a closed-positive
operator-monotone quotient supplier.  The closed-positive monotonicity of the
quotient gives its Kubo--Ando representation by the half-line Loewner theorem;
the finite-right-derivative representation supplier is then obtained from that
Kubo--Ando representation.
-/
theorem operatorMonotoneDecreasingOnPositive_of_matrixCfcRealizationClosedPositiveQuotientSupplier
    {g : ℝ → ℝ}
    (hjoint : PositiveRayMatrixQFormJointConvex (positiveRayMatrixCfc g))
    (hnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hquotSupplier :
      PositiveRayMatrixOperatorConvex (positiveRayMatrixCfcTwist g) →
        PositiveRayXsqEndpointControl g →
          ∃ q : ℝ → ℝ,
            (∀ ⦃x : ℝ⦄, x ∈ Set.Ioi (0 : ℝ) →
              positiveRayXsqEndpointExtension g x =
                positiveRayXsqEndpointExtension g 0 + x * q x) ∧
            OperatorMonotoneOnClosedPositive q ∧
            0 ≤ q 0) :
    OperatorMonotoneDecreasingOnPositive g := by
  refine
    operatorMonotoneDecreasingOnPositive_of_matrixCfcRealizationXsqRepSupplier
      hjoint hnonneg ?_
  intro hconvexH hcontrol
  rcases hquotSupplier hconvexH hcontrol with
    ⟨q, hquot, hclosed, ha⟩
  let rep : PositiveRayKuboAndoRep q :=
    positiveRayKuboAndoRep_of_operatorMonotoneOnClosedPositive hclosed
  exact exists_xsq_finiteRightDerivativeRep_of_positiveRayKuboAndoQuotient
    hquot rep ha

end Quantum.TraceInequality.Loewner
