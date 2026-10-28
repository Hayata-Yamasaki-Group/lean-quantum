import Quantum.TraceInequality.Loewner.Koranyi.RawDyadicInsideMass

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Set

noncomputable section

open scoped ComplexOrder
open scoped MatrixOrder

/-!
# Finite Koranyi inside-mass estimates

This file is the low-level 38-c analytic consumer for finite Koranyi spectral
measures.  It does not construct the Koranyi operator from `GlobalStrictPosDef`;
it only records the dyadic-family cover estimate once uniform inverse-square
control is available for the spectral measure of a fixed finite operator.
-/

/--
Finite Koranyi stage inside-mass bound from a uniform inverse-square bound on
the dyadic family covering `[-1,1]`.

This is the same measure-cover argument used for the raw dyadic branch, but it
is stated directly for the spectral measure of an arbitrary finite symmetric
operator.  The producer of the hypothesis `hK` for the canonical signed-eval
backbone is a separate theorem-38-c frontier.
-/
theorem finiteKoranyi_insideMass_le_of_uniform_sqInvDist
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (φ : E) (m : ℕ) (K : ENNReal)
    (hK :
      ∀ i : Fin (nonzeroInteriorDyadicPointCount m + 1),
        (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist (zeroAnchoredDyadicPointFamily m i) y
          ∂(_root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric
            (T := T) (hT := hT) φ)) ≤ K) :
    (_root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric
      (T := T) (hT := hT) φ) (Set.Icc (-1 : ℝ) 1) ≤
      (nonzeroInteriorDyadicPointCount m + 1) *
        ((ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ)) * K := by
  exact
    measure_Icc_le_mul_lintegral_sqInvDist_of_uniform_bound_dyadicFamily
      (μ := _root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric
        (T := T) (hT := hT) φ)
      (m := m) (K := K) hK

/--
Stand-alone finite Koranyi stagewise inverse-square bound from uniformly
bounded resolvent solutions at the dyadic family centers.

This is the theorem-38-c-pre-standalone analytic node. It does not mention the
canonical signed-eval backbone; the canonical specialization is a separate
frontier.
-/
theorem finiteKoranyi_stagewiseSqInvDistBound_standalone
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (φ : E) (m : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hsol :
      ∀ i : Fin (nonzeroInteriorDyadicPointCount m + 1),
        ∃ δ : E,
          (T - (zeroAnchoredDyadicPointFamily m i : ℂ) • (LinearMap.id : E →ₗ[ℂ] E)) δ = φ ∧
            ‖δ‖ ≤ R) :
    ∀ i : Fin (nonzeroInteriorDyadicPointCount m + 1),
      (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist (zeroAnchoredDyadicPointFamily m i) y
          ∂(_root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric
            (T := T) (hT := hT) φ)) ≤ ENNReal.ofReal (R ^ 2) := by
  intro i
  rcases hsol i with ⟨δ, hδ, hδR⟩
  have hle :
      (∫⁻ y, Quantum.TraceInequality.Loewner.sqInvDist (zeroAnchoredDyadicPointFamily m i) y
          ∂(_root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric
            (T := T) (hT := hT) φ)) ≤ ENNReal.ofReal (‖δ‖ ^ 2) := by
    simpa using
      (_root_.Quantum.TraceInequality.Loewner.lintegral_sqInvDist_diracMeasure_le_of_solution
        (T := T) (hT := hT) (φ := φ) (δ := δ) (x0 := zeroAnchoredDyadicPointFamily m i) hδ)
  have hnorm_le : ENNReal.ofReal (‖δ‖ ^ 2) ≤ ENNReal.ofReal (R ^ 2) := by
    have hsq : ‖δ‖ ^ 2 ≤ R ^ 2 := by
      have h0 : 0 ≤ ‖δ‖ := norm_nonneg _
      nlinarith [hδR, h0, hR]
    exact ENNReal.ofReal_le_ofReal hsq
  exact hle.trans hnorm_le

/--
Finite Koranyi stage inside-mass bound from uniformly bounded resolvent
solutions at the dyadic family centers.

This is the dyadic-family analogue of the Step46 bridge. It is still a
consumer: the theorem-38-c producer must supply the uniformly bounded
solutions for the actual Koranyi operator chosen by the canonical backbone.
-/
theorem finiteKoranyi_insideMass_le_of_uniform_solution_norm
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (φ : E) (m : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hsol :
      ∀ i : Fin (nonzeroInteriorDyadicPointCount m + 1),
        ∃ δ : E,
          (T - (zeroAnchoredDyadicPointFamily m i : ℂ) • (LinearMap.id : E →ₗ[ℂ] E)) δ = φ ∧
            ‖δ‖ ≤ R) :
    (_root_.Quantum.TraceInequality.Loewner.diracMeasure_of_isSymmetric
      (T := T) (hT := hT) φ) (Set.Icc (-1 : ℝ) 1) ≤
      (nonzeroInteriorDyadicPointCount m + 1) *
        ((ENNReal.ofReal (dyadicGridRadius m)) ^ (2 : ℕ)) * ENNReal.ofReal (R ^ 2) := by
  refine
    finiteKoranyi_insideMass_le_of_uniform_sqInvDist
      (T := T) (hT := hT) (φ := φ) (m := m) (K := ENNReal.ofReal (R ^ 2)) ?_
  exact finiteKoranyi_stagewiseSqInvDistBound_standalone
    (T := T) (hT := hT) (φ := φ) (m := m) (R := R) hR hsol

end

end Loewner
end TraceInequality
end Quantum
