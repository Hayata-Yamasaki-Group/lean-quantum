import Quantum.TraceInequality.Loewner.Statement
import Quantum.TraceInequality.Loewner.UnitInterval.HardDirectionBridge

/-!
# Strict hard direction on the normalized interval

This module packages the strict and smooth-input forms of the book-route hard
direction from normalized Löwner positivity to the interval representation.
-/

namespace Quantum.TraceInequality.Loewner

open Set MeasureTheory Filter

open scoped ComplexOrder
open scoped MatrixOrder
open scoped Topology
open scoped UpperHalfPlane

noncomputable section

/--
Book-route strict hard direction on the normalized interval, under the explicit
interior smooth input used by the Chapter 20 approximation argument.
-/
noncomputable def strict_hard_direction_unitInterval_bookRoute_of_interiorSmooth
    {f : ℝ → ℝ} (h : GlobalStrictPosDef f)
    (hfSmooth : ContDiffOn ℝ loewnerBookSmoothOrder f (Set.Ioo (-1 : ℝ) 1)) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_globalStrictPosDef_of_interiorSmooth h hfSmooth

/--
Packaged book-route strict hard direction on the normalized interval.

This is the public-facing book-route target for the strengthened input; the
old `GlobalStrictPosDef`-only dyadic-recovery placeholder is not part of the
current public route.
-/
noncomputable def strict_hard_direction_unitInterval_bookRoute
    {f : ℝ → ℝ} (h : GlobalStrictInteriorSmoothInput f) :
    IntegralRepOnUnitInterval f :=
  strict_hard_direction_unitInterval_bookRoute_of_interiorSmooth
    h.strict h.interiorSmooth

/--
Book-route strict hard direction for the smooth strict input used in
Chapter 20's `\widetilde M_\infty(-1,1)` reduction.
-/
noncomputable def strict_hard_direction_unitInterval_bookRoute_of_smoothNeighborhood
    {f : ℝ → ℝ} (h : GlobalStrictSmoothNeighborhoodInput f) :
    IntegralRepOnUnitInterval f :=
  strict_hard_direction_unitInterval_bookRoute
    (globalStrictInteriorSmoothInput_of_globalStrictSmoothNeighborhoodInput h)

end

end Loewner
end TraceInequality
end Quantum
