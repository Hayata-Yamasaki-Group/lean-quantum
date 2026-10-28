/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Quantum.OperationalProbabilistic.Framework.Core.GSLCore
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open CategoryTheory
open scoped MonoidalCategory ENNReal

/-!
# Classical relative entropy of finite PMFs

`classicalRelEntropyPMF` is Mathlib's Kullback--Leibler divergence `InformationTheory.klDiv` of
the measures of two finite PMFs, valued in `ℝ≥0∞` with the natural logarithm: a positive
probability measured against zero gives `∞`, while zero-mass points make no contribution.
-/

namespace OPT

noncomputable section

universe u v

variable {Sys : Type u} [Category.{v} Sys] [MonoidalCategory Sys]
  [Preadditive Sys] [CategoryTheory.Linear ℝ Sys]
  [MonoidalPreadditive Sys] [MonoidalLinear ℝ Sys]
  [CausalOperationalProbabilisticTheory Sys]

/-- Classical relative entropy of two finite probability mass functions.

The discrete outcome type carries its full measurable space, and the PMFs are
viewed as probability measures before applying Mathlib's KL divergence. -/
noncomputable def classicalRelEntropyPMF {iota : Type} [Fintype iota]
    (p q : PMF iota) : ℝ≥0∞ :=
  letI : MeasurableSpace iota := ⊤
  InformationTheory.klDiv p.toMeasure q.toMeasure

end

end OPT
