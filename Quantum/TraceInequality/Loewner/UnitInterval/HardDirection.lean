import Quantum.TraceInequality.Loewner.UnitInterval.FiniteOrder.CanonicalStrictificationBridge

/-!
# Chapter 20 book-route public hard direction

This file records the public-facing smooth hard-direction wrapper obtained from
the Chapter 20 strictification pipeline.
The broad non-smooth public hard direction is supplied downstream by
the finite-order regularity ladder and theorem-facing public wrappers.
-/

namespace Quantum.TraceInequality.Loewner

open MeasureTheory Filter

open scoped Topology
open scoped ComplexOrder
open scoped MatrixOrder

noncomputable section

/--
Book-route hard direction for public Löwner-positive inputs with explicit
interior smoothness.
-/
noncomputable def general_hard_direction_unitInterval_bookRoute_of_interiorSmooth
    {f : ℝ → ℝ} (hpos : LoewnerPosOnUnitInterval f)
    (hfSmooth : ContDiffOn ℝ loewnerBookSmoothOrder f (Set.Ioo (-1 : ℝ) 1)) :
    IntegralRepOnUnitInterval f :=
  integralRepOnUnitInterval_of_loewnerPosOnUnitInterval_of_interiorSmooth
    hpos hfSmooth

/--
Packaged public-facing book-route hard direction for the smooth public input.
-/
noncomputable def general_hard_direction_unitInterval_bookRoute
    {f : ℝ → ℝ} (h : LoewnerPosInteriorSmoothInput f) :
    IntegralRepOnUnitInterval f :=
  general_hard_direction_unitInterval_bookRoute_of_interiorSmooth
    h.pos h.interiorSmooth

end

end Quantum.TraceInequality.Loewner
