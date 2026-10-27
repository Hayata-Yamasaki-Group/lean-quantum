import Quantum.TraceInequality.Basic
/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hayata Yamasaki
-/

import Quantum.TraceInequality.CompressionInequality.RotatedBlockCompression
import Quantum.TraceInequality.CompressionInequality.JuliaUnitary

/-! Scoped instance caches for compression proofs.
Here, `ScopedCTC` denotes a scoped cache of algebraic type-class instances.
Importing this module alone does not activate them. -/

namespace HansenPedersen.ConvexityCharacterization

open scoped ComplexOrder

universe u

/- Instance caches: the Julia-block algebra below multiplies operators on
`L (WithLp 2 (H × H))`, and each `*`/`•`/`star` elaboration re-runs deep
`Monoid`/`SMul`/`Algebra` derivations on that product space (profiler: `Monoid`
~90ms x20, `HSMul` ~125ms x4; previously behind a `maxHeartbeats 800000`
budget). Scoped reducible instances turn each search into a head-match. -/

-- One-time search for the cache itself; every later use is a head-match.
/-- Scoped reducible cache for the monoid structure on the two-by-two Hilbert
product operator algebra used by Julia-block products. -/
@[reducible] noncomputable def instMonoidLPairScopedCTC
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    Monoid (L (WithLp 2 (H × H))) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Scoped reducible cache for star multiplication on the two-by-two Hilbert
product operator algebra used by Julia-block conjugations. -/
@[reducible] noncomputable def instStarMulLPairScopedCTC
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    StarMul (L (WithLp 2 (H × H))) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Scoped reducible cache for real scalar multiplication on the two-by-two
Hilbert product operator algebra used in block midpoint averages. -/
@[reducible] noncomputable def instSMulRealLPairScopedCTC
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    SMul ℝ (L (WithLp 2 (H × H))) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Scoped reducible cache for the real algebra structure on the two-by-two
Hilbert product operator algebra used in block CFC calculations. -/
@[reducible] noncomputable def instAlgebraRealLPairScopedCTC
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    Algebra ℝ (L (WithLp 2 (H × H))) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Scoped reducible cache for the monoid structure on `L H` used by the block
entries in the contraction proof. -/
@[reducible] noncomputable def instMonoidLHScopedCTC
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    Monoid (L H) :=
  inferInstance

-- One-time search for the cache itself; every later use is a head-match.
/-- Scoped reducible cache for real scalar multiplication on `L H` used in the
fixed-space contraction proof. -/
@[reducible] noncomputable def instSMulRealLHScopedCTC
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    SMul ℝ (L H) :=
  inferInstance

namespace ContractionInstances

attribute [scoped instance]
  instMonoidLPairScopedCTC
  instStarMulLPairScopedCTC
  instSMulRealLPairScopedCTC
  instAlgebraRealLPairScopedCTC
  instMonoidLHScopedCTC
  instSMulRealLHScopedCTC

end ContractionInstances

end HansenPedersen.ConvexityCharacterization
