import Quantum.TraceInequality.Loewner.Statement
import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.CanonicalStrictificationBridge
import Quantum.TraceInequality.Loewner.UnitInterval.HardDirection
import Quantum.TraceInequality.Loewner.UnitInterval.Pick.PublicCorrespondence
import Quantum.TraceInequality.Loewner.UnitInterval.IntegralToOperatorMonotone
import Quantum.TraceInequality.Loewner.UnitInterval.OperatorMonotone.HiaiRegularity


/-!
# Loewner theorem on the normalized unit interval

This module exposes the completed theorem-facing API for the normalized interval.

## Main results and API

* `integralRepOnUnitInterval_of_loewnerPosOnUnitInterval`: the broad hard direction
  from public Löwner positivity to the interval integral representation.
* `loewnerPosOnUnitInterval_of_integralRep`: the converse finite-matrix positivity
  consequence, obtained through operator monotonicity.
* `operatorMonotoneOnUnitInterval_of_loewnerPosOnUnitInterval`: the public
  operator-monotonicity consequence.
* `operatorMonotoneOnUnitInterval_of_finiteMatrixMonotone`: the finite-dimensional
  CFC monotonicity entry point.
* `unitInterval_loewnerPos_has_all_three`: the completed normalized triangle between
  `LoewnerPosOnUnitInterval`, `IntegralRepOnUnitInterval`, and
  `OperatorMonotoneOnUnitInterval`.
* `unitIntervalIntegralRep_nonempty_of_loewnerPosInteriorSmoothInput` and the
  smooth-input Pick/triangle wrappers retain the explicit Chapter 20 route as a
  theorem-facing compatibility surface.

The public predicates and representation structures are defined in `Statement`.
The Pick correspondence is exposed by `unitIntervalPickExtension_iff_integralRep`.

## Sources

Chapter numbers refer to B. Simon, *Loewner's Theorem on Monotone Matrix Functions*,
Grundlehren der mathematischen Wissenschaften 354, Springer, 2019.

* Chapter 3 supplies the Pick/integral correspondence, the integral-to-operator-monotone
  direction, and the two-by-two Hiai regularity route.
* Chapter 20 supplies the finite-order regularity ladder and canonical strictification
  used by the broad hard direction.
* Chapter 27 supplies the Korányi construction used below the theorem-facing surface:
  finite-stage approximations, their weak limit, and the inside-mass estimate.

## Design

The normalized mainline is
`LoewnerPos → IntegralRep → OperatorMonotone → LoewnerPos`.  The hard direction
passes through the Chapter 20 finite-order regularity input and canonical
strictification bridge.  The Korányi modules provide the finite construction, the weak
limit and the inside-mass estimate, while this file contains only the public assembly and
compatibility wrappers.

## Status

The Pick correspondence, integral-to-operator-monotone direction, broad hard
direction, full normalized triangle, and two-by-two Hiai regularization route
are proved.

Finite-dimensional non-unital C*-algebras are classified by finite products of
`CStarMatrix` blocks in `Quantum.TraceInequality.Loewner.exists_starAlgEquiv_pi_cstarMatrix`;
with a star-ordered structure, such an equivalence yields a `FiniteCStarMatrixBlockModel`
(`finiteCStarMatrixBlockModel_of_starAlgEquiv`).  The half-line decreasing equivalence itself
is unconditional at the theorem-facing surface.
-/

namespace Quantum.TraceInequality.Loewner

universe u

/--
The broad public hard direction on the normalized interval.

The finite-order regularity ladder is supplied by Chapter 20, then consumed by
the existing canonical strictification bridge.
-/
noncomputable def integralRepOnUnitInterval_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_loewnerPosOnUnitInterval_of_finiteOrderRegularityInput
    publicFiniteOrderRegularityInput_of_loewnerPosOnUnitInterval
    hpos

/-! ### Smooth-input hard direction -/
/--
Smooth public Löwner-positive input supplies the interval integral representation.

Lean-deviation: the source-side smooth input remains in the surface name, but
`LoewnerPosOnUnitInterval` alone suffices for this formal statement.
-/
theorem unitIntervalIntegralRep_nonempty_of_loewnerPosInteriorSmoothInput
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    Nonempty (IntegralRepOnUnitInterval f) :=
  ⟨integralRepOnUnitInterval_of_loewnerPosOnUnitInterval hpos⟩

/-! ### Integral representation consequences -/
/--
Integral representations give finite-dimensional Löwner positivity by first
passing through operator monotonicity.
-/
theorem loewnerPosOnUnitInterval_of_integralRep
    {f : ℝ → ℝ} (rep : IntegralRepOnUnitInterval f) :
    LoewnerPosOnUnitInterval f :=
  loewnerPosOnUnitInterval_of_operatorMonotone
    (operatorMonotoneOnUnitInterval_of_integralRep rep)

/-! ### Operator-monotonicity wrappers -/
/-- Public Löwner positivity implies normalized interval operator monotonicity. -/
theorem operatorMonotoneOnUnitInterval_of_loewnerPosOnUnitInterval
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    OperatorMonotoneOnUnitInterval f :=
  operatorMonotoneOnUnitInterval_of_integralRep
    (integralRepOnUnitInterval_of_loewnerPosOnUnitInterval hpos)

/--
Finite-dimensional CFC monotonicity on the normalized interval already implies
the public normalized-interval operator-monotone predicate.
-/
theorem operatorMonotoneOnUnitInterval_of_finiteMatrixMonotone
    {f : ℝ → ℝ} (hf : UnitIntervalMatrixMonotone f) :
    OperatorMonotoneOnUnitInterval f := by
  exact operatorMonotoneOnUnitInterval_of_loewnerPosOnUnitInterval
    (loewnerPosOnUnitInterval_of_finiteMatrixMonotone hf)

/--
gcongr form of the normalized-interval operator monotonicity: once `f` is
operator monotone on the normalized interval, the normalized non-unital CFC
map preserves the order of self-adjoint elements with quasispectrum in
`(-1, 1)`.
-/
@[gcongr]
theorem cfcn_sub_le_cfcn_sub_of_le_of_operatorMonotoneOnUnitInterval
    {f : ℝ → ℝ} (hf : OperatorMonotoneOnUnitInterval.{u} f)
    {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a b : A} (hab : a ≤ b)
    (ha : IsSelfAdjoint a) (hqa : quasispectrum ℝ a ⊆ Set.Ioo (-1 : ℝ) 1)
    (hb : IsSelfAdjoint b) (hqb : quasispectrum ℝ b ⊆ Set.Ioo (-1 : ℝ) 1) :
    cfcₙ (fun x : ℝ => f x - f 0) a ≤ cfcₙ (fun x : ℝ => f x - f 0) b :=
  hf.cfc_monotone ⟨ha, hqa⟩ ⟨hb, hqb⟩ hab

/-! ### Pick-extension wrappers -/
/--
Smooth public Löwner-positive input supplies the Pick-type extension.

Lean-deviation: the source-side smooth input remains in the surface name, but
`LoewnerPosOnUnitInterval` alone suffices for this formal statement.
-/
theorem unitIntervalPickExtension_nonempty_of_loewnerPosInteriorSmoothInput
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    Nonempty (PickExtensionOnUnitInterval f) :=
  (unitIntervalPickExtension_iff_integralRep f).2
    (unitIntervalIntegralRep_nonempty_of_loewnerPosInteriorSmoothInput hpos)

/--
Smooth public Löwner-positive input supplies both endpoints of the Chapter 3
Pick/integral correspondence.

Lean-deviation: the source-side smooth input remains in the surface name, but
`LoewnerPosOnUnitInterval` alone suffices for this formal statement.
-/
theorem unitInterval_smoothLoewnerPos_has_integral_and_pick
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    Nonempty (IntegralRepOnUnitInterval f) ∧
      Nonempty (PickExtensionOnUnitInterval f) :=
  ⟨unitIntervalIntegralRep_nonempty_of_loewnerPosInteriorSmoothInput hpos,
    unitIntervalPickExtension_nonempty_of_loewnerPosInteriorSmoothInput hpos⟩

/-! ### Public normalized interval triangles -/
/--
The full normalized interval triangle from broad public Löwner positivity.
-/
theorem unitInterval_loewnerPos_has_all_three
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    LoewnerPosOnUnitInterval f ∧
      Nonempty (IntegralRepOnUnitInterval f) ∧
        OperatorMonotoneOnUnitInterval f := by
  let rep : IntegralRepOnUnitInterval f :=
    integralRepOnUnitInterval_of_loewnerPosOnUnitInterval hpos
  exact ⟨hpos, ⟨rep⟩, operatorMonotoneOnUnitInterval_of_integralRep rep⟩

/--
Smooth public Löwner-positive input supplies the three normalized interval
conditions: Löwner positivity, integral representation, and operator monotonicity.

Lean-deviation: the source-side smooth input remains in the surface name, but
`LoewnerPosOnUnitInterval` alone suffices for this formal statement.
-/
theorem unitInterval_smoothLoewnerPos_has_all_three
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f) :
    LoewnerPosOnUnitInterval f ∧
      Nonempty (IntegralRepOnUnitInterval f) ∧
        OperatorMonotoneOnUnitInterval f :=
  unitInterval_loewnerPos_has_all_three hpos

end Loewner
end TraceInequality
end Quantum
